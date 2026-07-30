# Chart Development Roadmap

## Purpose

This document describes the next safe development steps for the chart in
`gpt_22_07.py`. It is intended to preserve the existing task analysis,
strategy calculations, indicator formulas, JSON data, and parquet data model
while making the chart easier to extend with new sources, oscillators,
trade annotations, measurement behavior, and responsive controls.

The chart should be treated as a small application with explicit inputs and
state, rather than as a collection of independently wired buttons.

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

