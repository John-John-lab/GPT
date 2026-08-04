# Chart Development Roadmap

> **AI and maintainer note:** Read the optimization decision record below
> before proposing chart performance work. It records optimizations already
> shipped, experiments that were rejected, and the small set of remaining
> candidates. Do not reintroduce a rejected approach without new measurements
> and an explicit reason.

## Purpose

This document describes the next safe development steps for the chart in
`gpt_22_07.py`. It is intended to preserve the existing task analysis,
strategy calculations, indicator formulas, JSON data, and parquet data model
while making the chart easier to extend with new sources, oscillators,
trade annotations, measurement behavior, and responsive controls.

The chart should be treated as a small application with explicit inputs and
state, rather than as a collection of independently wired buttons.

---

## Chart Optimization Decision Record

This section is the durable handoff for future maintainers and coding agents.
The chart has already received substantial server, transport, and browser
optimization. Read this section and inspect `git log -- gpt_22_07.py` before
starting another performance refactor. Update this record whenever an
experiment is accepted or rejected.

### Measured baseline after the current optimization work

Measurements supplied during development used 1,861 candles and up to 20
traces. They show that same-schema navigation now spends roughly 0.30-0.64
seconds building the compact server payload. Compressed responses are commonly
about 235-255 KB, down from approximately 625-634 KB raw. The remaining visible
delay is usually browser scheduling and Plotly application (roughly 0.8-3.4
seconds), rather than indicator calculation (normally about 0.10-0.15 seconds).

An authoritative chart opened from a source table intentionally still builds
a complete figure. That path commonly takes about 2.8-3.4 seconds on the
measured workload because it establishes the schema and trusted baseline that
later navigation patches validate against.

These figures are diagnostic baselines, not performance promises. Compare new
work on the same machine, source, candle count, pane count, and warm/cold cache
state.

### Implemented and retained

- Bounded task-window and indicator caching with source-file version
  invalidation.
- Lazy computation of visible indicators; strategy and indicator formulas are
  unchanged.
- Per-indicator WebGL switches with SVG fallbacks, so each renderer can be
  rolled back independently.
- A compact epoch-based time axis and removal of unnecessary dense helper
  traces where the same visual result can be represented by layout objects.
- A schema-tagged compact navigation payload with exact task/event checks,
  source-context validation, gzip transport, and a full-render fallback.
- One type-correct `Plotly.react` application for fast navigation, followed by
  integrity validation of trace samples, signal levels, and source entry/exit
  events.
- Direct local navigation state updates and browser-only toolbar actions that
  do not request a new figure.
- Timestamp-based oscillator synchronization using binary search rather than
  assuming that hover point indices are interchangeable across panes.

### Tried and rejected: do not repeat without new evidence

- **Dash `Patch` replacing complete trace objects:** the patch was frequently
  larger and more CPU-intensive than the compact response. The old incremental
  route remains disabled; replacing every trace is not incremental rendering.
- **Separate candlestick restyle plus oscillator update:** reliable, but it
  caused two expensive Plotly render passes and was slower than one react.
- **One heterogeneous `Plotly.update` call with undefined OHLC slots:** caused
  Plotly/ScatterGL `_inputDomain` failures. Use type-correct trace objects.
- **Deep-copying cached Plotly figures:** copying cost roughly 1.2-2.3 seconds
  and removed most of the expected benefit. Cache compact data/models instead.
- **Broad or eager parquet prefetch:** reads normally cost only tens of
  milliseconds and background work competed with foreground browser paint.
  Any future prefetch must be bounded, idle-only, and measured end to end.
- **Forcing oscillator defaults during every source open:** changed user UI
  state and increased the payload. Source defaults may initialize a new
  session, but must not overwrite explicit choices.
- **Carrying zoom/range state between different tasks:** produced displaced or
  apparently missing chart content. Task navigation resets data-dependent
  ranges unless the user explicitly opts into persistence.
- **Reading private/native hover data for the “Osc All” field:** pane hover data
  can be stale or refer to a different trace. Resolve the shared timestamp from
  axis geometry and look up each oscillator independently.
- **Sending no-op toolbar callbacks:** even tiny 28-byte responses can queue
  ahead of navigation. Pure presentation/measurement toggles remain local.

### Remaining compact, maintainable opportunities

1. **Dedicated compact navigation endpoint with cancellation.** Avoid Dash
   callback scheduling for Next/Previous and cancel superseded requests with
   `AbortController`. This is the strongest remaining candidate, but it must
   retain source authorization, schema checks, and full-render fallback.
2. **Small serialized-payload cache for revisits.** Key it by task, source-file
   version, event identity, pane state, and render schema; bound it by count and
   bytes. This can remove the remaining 0.15-0.35 second payload-build cost on
   back/forward navigation.
3. **Adjacent-task prefetch after idle.** Prefetch at most the previous and next
   compact payload after `plotly_afterplot`; abort it immediately on user work.
   Do not restore broad parquet or figure prefetch.
4. **Explicit display-detail control.** A user-selected shorter visible window
   or reduced detail can lower Plotly cost. Never silently downsample analysis
   data or alter indicator/strategy calculations.

The first two options are localized additions. They do not require another
chart architecture rewrite. Beyond them, Plotly rendering of thousands of
points across many panes is the dominant cost, so gains become smaller or
require an explicit product tradeoff.

### Guardrails for future optimization work

- Preserve authoritative full rendering for a new source open.
- Preserve schema mismatch, exception, and integrity-check fallbacks.
- Do not change task analysis, strategy math, indicator formulas, trade-event
  alignment, or signal levels as a performance shortcut.
- Avoid private Plotly internals, unbounded caches, implicit downsampling,
  binary protocols, and another broad refactor unless measured evidence shows
  that the compact endpoint is insufficient.
- Measure click-to-request, server build, serialization, response-to-plot, long
  tasks, trace count, payload bytes, and integrity on the same workload.
- Ship one optimization per commit behind an independent rollback switch.
- Add the outcome and measurements to this record so future agents do not
  repeat the same experiment.

---

## Current Architecture

The current chart foundation has four layers.

### 1. Chart request and source context

A chart request identifies which task is open, where it was opened from, and
which source event is selected. Source profiles describe source-specific
behavior without modifying strategy math.

Current source profiles:

- `main_table`: normal task navigation, signal focus, no trade-detail overlay
  by default.
- `dynamic_oscillator_summary`: event-group navigation, event-interval focus,
  RSI/Stochastic defaults, and source trade details.
- `strategy_summary`: reserved profile for future strategy-summary links. It
  supports event-group navigation, event focus, and source trade details.

The canonical payload concept is:

```python
{
    "task_id": "...",
    "source": "main_table | dynamic_oscillator_summary | strategy_summary",
    "profile": {...},
    "context": {
        "events": [...],
        "index": 0,
        "overlay": True,
    },
    "selected_event": {...},
}
```

### 2. Chart UI state

The grouped `chart-ui-state-store` provides a stable contract for chart UI
state. Existing individual Stores remain the compatibility writers while the
migration is in progress.

The grouped state contains:

```python
{
    "panes": {"rsi": False, "stochastic": False, ...},
    "overlays": {"strategy": False, "impulses": False, "events": False},
    "measurement": {
        "enabled": False,
        "snap_to_candle": False,
        "show_hover": True,
        "shade_oscillator_range": False,
    },
    "information": {"candle": False, "oscillator": True, ...},
    "viewport": {"extend_x": False, "focus_entry": False},
}
```

### 3. Data, model, and rendering boundaries

- `load_chart_task_window(...)` loads and slices the candle window.
- `build_chart_render_model(...)` makes UI-only rendering decisions.
- `CHART_INDICATOR_REGISTRY` defines pane order and availability.
- `CHART_OVERLAY_REGISTRY` documents overlays and source awareness.
- source-trade helpers normalize selected events, trade timing, labels,
  reasons, and P&L before Plotly rendering.

### 4. Performance instrumentation

Chart rendering has optional checkpoints controlled by `PERF_TRACE_ENABLED`.
It can report task-window loading, indicator preparation, rendering/model
work, layout/view-state work, source, pane count, trace count, and a render
budget warning. This must guide optimization; do not apply speculative cache
or event-listener changes first.

---

## Development Principles

1. **Do not change existing task, strategy, or indicator math unless the
   feature explicitly requires a formula change.** UI refactors should operate
   on existing outputs.
2. **Use the request/context model for every new entry point.** Do not add a
   new direct chart-opening path with a custom Store or raw JavaScript event.
3. **Use grouped UI state for every new control.** Existing individual Stores
   are compatibility infrastructure, not the preferred pattern for new work.
4. **Keep foreground chart opening responsive.** Optional prefetch must stay
   background-only and must never delay the selected chart.
5. **Use source profiles, not scattered `if source == ...` branches.**
6. **Use indicator/overlay registries for additions.** This makes adding a
   pane or mark predictable and testable.
7. **Keep transient pointer and drag state in the browser.** Persist only
   meaningful preferences/settings or saved measurements.
8. **Measure before optimizing.** Use Phase 6 trace output to find the actual
   slow stage.

---

## Required Input From the Product Owner

The following details are required before implementing a strategy-summary
chart link or a new oscillator. They prevent accidental changes to trading
semantics.

### A. Strategy-summary links

Please identify the exact summary/table that should receive the first chart
link. Examples:

- Dynamic Oscillator Summary;
- Toward-Level Next-Candle Strategy Summary;
- Signal Performance Summary;
- a new dedicated strategy-result table.

For each chartable row/event, provide or confirm this payload:

```python
{
    "task_id": "required task id",
    "entry_time": 1710000000000,
    "entry_price": 123.45,
    "exit_time": 1710003600000,       # optional for open trades
    "exit_price": 125.00,             # optional for open trades
    "direction": "buy | sell",
    "label": "human-readable strategy/event name",
    "entry_conditions": "why the position opened",
    "entry_condition_window": 1,
    "entry_execution": "how entry was executed",
    "entry_level_distance_pct": 0.25,
    "exit_reason": "stop | oscillator_close | tp | open | custom_value",
    "exit_conditions": "why the position exited",
    "return_pct": 1.25,
}
```

Decisions needed:

- Should open positions show an entry marker and an "Open" status only?
- Should a TP checkpoint be treated as an exit or as an intermediate marker?
- Should this source open focused on signal, entry, or entry-to-exit interval?
- Which indicator panes should open automatically for this source?
- Which toolbar controls should be visible or emphasized for this source?

### B. New oscillator specification

For every requested oscillator, provide:

1. **Name and label** (for example `CCI`, `Williams %R`, `MFI`).
2. **Formula or exact TradingView-compatible parameter set**.
3. **Input series** (`close`, `hl2`, `ohlc4`, volume, etc.).
4. **Pane layout**: own pane, shared pane, or main-candle overlay.
5. **Visual style**: lines/bars, colors, widths, reference levels.
6. **Default visibility**: on or off.
7. **Source availability**: all sources or selected profiles only.
8. **Trade-mark behavior**: should source entry/exit time guides appear in the
   pane?
9. **Expected range**: fixed such as 0-100, or dynamic such as MACD.
10. **Performance expectation**: simple rolling calculation, or a costly
    multi-series/volume-derived calculation.

Example request:

```text
Oscillator: CCI
Parameters: 20 periods, typical price = (high + low + close) / 3
Pane: separate pane
Levels: +100, 0, -100
Style: blue line, grey dashed levels
Default: off
Sources: main_table and strategy_summary
Synchronized entry/exit guides: yes
```

### C. Measurement behavior

Please decide whether measurements are:

- temporary and cleared when the chart closes;
- retained while navigating next/previous tasks;
- saved per task and restored when reopening;
- exportable or copyable;
- allowed to span all oscillator panes or only the main candle pane.

The current safe default is temporary browser-local drawing with persistent
preferences only (snap, hover, oscillator shading).

---

## Next Feature Plan

### Feature 1: First `strategy_summary` chart link

1. Add a chart control to the agreed strategy summary.
2. Build the source event payload from the summary row.
3. Publish a canonical chart request using the `strategy_summary` profile.
4. Reuse `add_source_trade_overlay(...)` for main-pane entry/exit details.
5. Reuse synchronized oscillator guides automatically.
6. Add source-specific default panes only after the source payload is verified.

**Improvement:** strategy research becomes navigable visually without copying
chart logic or losing entry/exit explanations.

### Feature 2: First new oscillator

1. Add a registry entry in `CHART_INDICATOR_REGISTRY`.
2. Add the calculation lazily, using the existing cache/window model.
3. Add a trace renderer with the requested levels and axis rules.
4. Add one grouped UI-state control.
5. Add the pane to source profiles where applicable.
6. Verify with source-trade guides and measurement shading enabled.

**Improvement:** a new oscillator is a contained extension instead of a change
to many independent Stores, JavaScript mappings, callbacks, and figure
branches.

### Feature 3: Finish grouped UI-state writer migration

Migrate writers in this order:

1. new controls first;
2. indicator-pane buttons;
3. strategy/impulse/event overlay buttons;
4. information and viewport buttons;
5. measurement controls last.

For each group, retain legacy Stores as fallback until browser verification is
complete. Do not migrate all buttons in one commit.

**Improvement:** fewer event paths, less dependence on document listeners,
and lower risk when Dash/React re-renders components.

### Feature 4: Measurement persistence (only after product decision)

1. Keep drag geometry temporary and browser-local.
2. Store user preferences in grouped UI state.
3. If saved measurements are requested, introduce a task-keyed data model:

```python
{
    "task_id": "...",
    "shapes": [
        {"x0": ..., "x1": ..., "y0": ..., "y1": ..., "label": ...}
    ],
}
```

4. Restore saved shapes after a figure rebuild.
5. Never let temporary shape updates trigger a parquet read or full figure
   rebuild.

**Improvement:** measurement becomes reliable while preserving responsive drag
interaction.

---

## Phase 6 Operational Guide

Phase 6 is active as instrumentation. Before optimizing, run a representative
local measurement session.

### Enable tracing temporarily

Set:

```python
PERF_TRACE_ENABLED = True
```

Then restart the app and collect output for:

1. uncached candle-only chart;
2. cached candle-only chart;
3. chart with one oscillator;
4. chart with all existing oscillators;
5. Dynamic Oscillator Summary event chart;
6. next/previous navigation;
7. short versus long task windows.

### What to record

For each chart, record:

- task/symbol/timeframe;
- source profile;
- number of panes;
- trace count;
- load-task-window time;
- lazy-indicator-preparation time;
- figure-trace/overlay time;
- layout/view-state time;
- total render time.

### How to act on results

| Slow stage | Preferred next action |
|---|---|
| Task-window loading | inspect parquet predicate pushdown, window size, storage latency, and cache hit rate. |
| Indicator preparation | cache derived arrays by task window, indicator, parameters, and source file version. |
| Trace/overlay construction | reduce unnecessary traces, avoid duplicate overlays, and build only visible panes. |
| Layout/browser rendering | reduce point count only after confirming visual requirements; avoid full figure rebuilds for local UI interactions. |
| Navigation | ensure foreground read wins over prefetch and keep prefetch bounded/background-only. |

Do not change cache sizes, event handlers, or Plotly behavior until the trace
shows a repeatable bottleneck.

---

## Definition of Done for Future Chart Features

A new chart feature is complete only when it:

- has a declared source profile or uses an existing profile;
- uses canonical request/context data;
- uses grouped UI state for new controls;
- preserves existing task and strategy calculations;
- works from every intended source;
- handles absent/malformed event data gracefully;
- does not block foreground chart opening;
- includes an isolated Python/static test where practical;
- is checked with JavaScript syntax validation;
- is measured with Phase 6 tracing if it changes loading, indicators, traces,
  or figure rebuild frequency.
