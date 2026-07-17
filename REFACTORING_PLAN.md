# Main Application Reliability and Refactoring Plan

## Purpose and status

This document records the current architectural analysis and ideas for future
discussion. It is deliberately a **planning document, not an instruction to
perform every item immediately**. The application contains valuable, mature
calculation and market-data behavior. Reliability and future flexibility are
more important than reducing line count or making superficially similar code
share one implementation.

The plan assumes that `gpt_16_07.py` remains the main application file for now,
and that most early improvements happen as clearly separated sections and
helpers inside that file. Moving code into additional modules should happen only
after boundaries are stable, tested, and useful in practice.

---

## Guiding position: do not over-unify

The concern that unifying similar-looking code can prevent flexible development
is correct. Two blocks may look alike today while representing different domain
policies that will diverge tomorrow. Prematurely forcing them through one helper
can create hidden switches, optional arguments, and coupling that are harder to
maintain than the original duplication.

The objective is therefore **clear ownership and explicit contracts**, not the
smallest possible number of lines.

### Good candidates for shared infrastructure

These are mechanisms whose meaning should remain consistent across features:

- Timestamp normalization and inclusive range filtering.
- Read-only Parquet access, cache invalidation, and column projection.
- Atomic JSON and Parquet writing.
- Market-data validation and preservation checks.
- Background-job status, cancellation, and bounded logging.
- Task lookup and immutable task snapshots.
- Common UI formatting that has no business meaning.
- Cache keys based on file version and calculation inputs.

### Poor candidates for forced unification

These may look similar but can have different research or trading semantics:

- Event, strategy, and impulse warm-up periods.
- Chart display history versus calculation history.
- Grid-search windows versus production strategy windows.
- Strategy-specific entry, exit, confirmation, and indicator rules.
- Summary-table fields that happen to have similar formatting.
- Different event types with superficially similar candle tests.
- Download ranges versus analysis ranges.

### Rule for deciding whether to unify

Share code only when all of the following are true:

1. The duplicated blocks express the same domain rule, not merely similar
   syntax.
2. They should change together when the rule changes.
3. The shared function has a small, clear contract without feature flags.
4. Tests can prove that every caller retains its previous behavior.
5. A future caller can opt into a distinct policy without modifying unrelated
   callers.

If any answer is uncertain, keep separate orchestration functions and share only
the low-level mechanism. A useful pattern is:

```text
feature-specific policy -> shared read/validation mechanism -> feature-specific calculation
```

Explicit policy parameters are acceptable when they are named and visible at the
call site. A helper with many booleans such as `special_mode=True` is a warning
that unrelated policies have been combined.

---

## Non-negotiable invariants

Structural work must not silently change:

- Event definitions, ordering, or tie-breaking.
- `searchsorted` sides and inclusive/exclusive candle boundaries.
- Indicator formulas, periods, smoothing, or `min_periods` behavior.
- Strategy entry, exit, stop-loss, take-profit, or confirmation rules.
- Signal parsing and timestamp interpretation.
- The meaning of `start_date`, `end_date`, and `pre_buffer_minutes`.
- Bybit pagination, timeframe alignment, or closed-candle handling.
- Duplicate resolution and existing-row preservation.
- JSON compatibility and runtime-only field exclusion.
- Parquet backup, reread, and atomic replacement requirements.

Formula changes should be separate, explicitly named changes with before/after
examples. A maintenance refactor should produce identical derived task fields for
the same input candles and settings.

---

## Current architectural pressure points

The main file has useful numbered sections, but several sections still contain
multiple responsibilities:

1. `DownloadTask.analyze_signal()` combines data preparation, event detection,
   metrics, task mutation, and logging.
2. `update_task_chart()` combines data loading, indicators, subplot planning,
   traces, overlays, measurement, and view-state restoration.
3. `build_tasks_tab_layout()` and `build_root_layout()` are large component
   declarations that are difficult to scan.
4. Callbacks often perform validation, I/O, calculations, mutation, and Dash
   response construction in one function.
5. Runtime state is distributed across module globals, dictionaries, task
   objects, stores, locks, and background workers.
6. Periodic intervals can wake callbacks while the user is interacting with a
   chart, which matters on a slow, single-process machine.
7. Some analytical paths still read more Parquet data than their calculation
   needs.
8. `database.py` has clear sections but one callback-registration function owns
   many unrelated callbacks.

These are navigation and ownership problems. They do not imply that every large
function should immediately be rewritten.

---

## Risk levels and timing

### Safe to do now

- Add characterization and compatibility tests.
- Add a source navigation index and stronger section contracts.
- Split layout-only builders while preserving every component ID.
- Move repeated presentation formatting into pure helpers.
- Add performance measurements around reads, calculations, and rendering.
- Disable idle polling where callback contracts permit it.
- Add bounded status/log containers.
- Separate pure boundary calculation from Parquet reading and DataFrame slicing.
- Add explicit cache-key builders containing every input that affects results.
- Add column projection to read-only Parquet readers after compatibility tests.

### Reasonable after tests exist

- Decompose `analyze_signal()` one metric family at a time.
- Decompose chart construction into data, indicators, traces, overlays, and
  view-state stages.
- Introduce result objects for calculations before applying values to tasks.
- Group callback registration by feature inside the same file.
- Replace related global flags with small state containers.
- Introduce a shared background-job status mechanism.
- Add registries for strategy definitions, derived fields, chart overlays, and
  table columns.

### Too ambitious or early now

- Splitting the main application into many modules before hidden dependencies
  are characterized.
- Rewriting `analyze_signal()` as one large change.
- Replacing all task attributes with a new schema or generic dictionary.
- Building a universal strategy framework before several strategies demonstrate
  the required extension points.
- Combining every event and strategy into one generic detector.
- Replacing Dash callback architecture wholesale.
- Introducing a database server or distributed job queue solely to organize the
  code.
- Increasing thread counts or cache sizes without measurements on the old Mac.

---

## Phase 0: establish a behavioral safety net

This is the prerequisite for ambitious structural work.

### Characterization fixtures

Create deterministic candle fixtures for:

- Resistance and support signals.
- Signal exactly on a candle and between candles.
- Body, shadow, pin, bounce, and breakthrough events.
- No-event and insufficient-history cases.
- Duplicate, missing, and unaligned timestamps.
- Different pre-signal values.
- `analyze_beyond` enabled and disabled.
- Closed and open ending boundaries.
- Strategy and impulse paths with and without signals.

For each fixture, record all relevant derived fields, event order, timestamps,
strategy signals, and chart markers. These tests describe current behavior even
if a behavior later appears unusual.

### Real-task snapshots

Use a small, anonymized set of real tasks and candle ranges. Save a normalized
snapshot of derived fields before a refactor and require exact equality after it.
Where floating-point tolerance is necessary, document the specific field and
reason.

### Persistence tests

Test old JSON load, current save/reload, runtime-field exclusion, temporary
pre-signal override behavior, persistent pre-signal behavior, and unknown-field
reporting.

### Callback contract tests

Check that callback output IDs exist in the relevant layout, return arity is
correct, property types are valid, and dynamic-tab callbacks do not target absent
components unexpectedly.

### Market-data safety tests

Use temporary directories and mocked API responses to test:

- No modification on validation failure.
- Existing-row preservation.
- Overlap rejection.
- Gap and alignment rejection.
- Temporary-file reread failure.
- Backup creation.
- Atomic replacement.
- Unavailable or delisted symbols.
- Partial batch completion without damage to existing data.

---

## Phase 1: improve navigation without changing behavior

Add a concise maintenance index near the top of `gpt_16_07.py`, linking the
numbered sections and identifying their allowed dependencies.

Use stable naming:

- `fmt_*`: presentation only.
- `parse_*`: input to structured values.
- `calculate_*`: formula or metric calculation.
- `build_*`: construct data, figures, or UI.
- `read_*`: read-only I/O.
- `write_*`: durable mutation.
- `validate_*`: no mutation.
- `start_*`: launch work.
- `poll_*`: report work.
- `render_*`: present already-calculated state.
- `_run_*`: worker implementation.

Every large section should state what it may and may not access. In particular,
formula code should not import Dash, render UI, or write files.

---

## Phase 2: decompose analysis conservatively

Do not begin by designing a generic analysis engine. First extract stable stages
from `analyze_signal()` while preserving statement order and numerical behavior.

Suggested progression:

1. Input validation and frame preparation.
2. Signal index and calculation-window selection.
3. Event candidate creation.
4. Event classification and ordering.
5. Target-hit metrics.
6. Adverse and expected movement metrics.
7. Return-to-level metrics.
8. Toward-level strategy metrics.
9. Application of results to the task.
10. Logging and publication.

A calculation result object can eventually hold outputs before they are applied
to a task. This enables atomic updates and tests without locks or Dash. However,
introduce it only after extracted helpers are proven equivalent.

Centralize reset and apply behavior so future fields cannot be recalculated while
stale values remain from an older formula version.

---

## Phase 3: establish strategy extension points without forcing sameness

New strategies should have independent policy objects or definitions containing:

- A unique name and version.
- Required candle columns.
- Required warm-up policy.
- Eligibility test.
- Calculation function.
- Output fields.
- Reset function.
- Optional chart overlay builder.
- Optional table summary formatter.

The registry should orchestrate independent strategies; it should not force them
to share entry/exit mathematics.

For example, a production strategy, grid search, and walk-forward test may share
a Parquet range reader but retain separate window-policy functions. If they are
expected to diverge, that distinction should be visible in names and call sites.

---

## Phase 4: decompose the chart pipeline

Keep the Dash chart callback as a coordinator. Separate:

1. Chart request and task resolution.
2. File-version and time-range resolution.
3. Parquet range read.
4. Required-column and indicator planning.
5. Lazy indicator calculation.
6. Subplot layout.
7. Price and volume traces.
8. Indicator traces.
9. Event, strategy, and impulse overlays.
10. Measurement overlays.
11. View-state restoration.

New formulas should register optional overlays rather than adding unrelated
branches throughout the central chart function.

Client-only controls should continue using small stores and Plotly relayout or
restyle calls. A full server figure rebuild should occur only when candle data,
indicator data, or task context changes.

---

## Phase 5: split layout builders inside the same file

Extract layout-only functions such as:

- `build_active_download_monitor()`
- `build_signal_input_panel()`
- `build_task_creation_options()`
- `build_strategy_control_panel()`
- `build_json_persistence_panel()`
- `build_task_table_controls()`
- `build_chart_panel()`
- `build_application_intervals()`

These functions must preserve existing IDs and must not access task state, files,
or formulas. This is low risk and makes the main layout much easier to navigate.

---

## Phase 6: thin callback orchestration

Use three conceptual layers:

```text
Dash input normalization -> feature operation -> Dash response translation
```

The feature operation should be callable without Dash. This makes it testable and
allows a future CLI or batch workflow without duplicating business logic.

Group callback registration by feature inside the same file before moving any
callbacks to modules:

- task creation;
- summary and table;
- chart;
- strategy and impulse;
- persistence;
- recalculation and background work.

Callback count alone is not a defect. A small callback with one responsibility is
often safer and faster than one universal callback with many inputs and outputs.

---

## Phase 7: runtime state and concurrency

Gradually replace related groups of globals with focused state containers:

- Display snapshot state.
- Recalculation state.
- Chart cache state.
- JSON preparation state.
- Background job state.

Do not create one global application-state object containing everything; that
would preserve the monolith under a new name.

Concurrency rules:

- Never sleep, perform network I/O, or read Parquet while holding a shared lock.
- Calculate locally, validate, then hold a lock only for identity check and
  atomic state application.
- Use cancellation events for long jobs.
- Bound logs and completed-job history.
- Avoid parallel CPU-heavy jobs on the old Mac.
- Publish one Golden Store update after a completed operation rather than
  exposing partially updated tasks.

---

## Phase 8: old Mac and old SSD performance

Performance work should reduce total work, not merely hide it behind threads.

### Polling

- Disable verification and recalculation intervals while idle.
- Prefer explicit version/store triggers over periodic full-table checks.
- Ensure status polling returns small text/progress payloads.
- Do not let general-purpose intervals trigger unrelated chart or optimizer work.

### Parquet reads

- Read timestamp-bounded ranges.
- Request only required columns.
- Include path, mtime, size, range, and column set in cache keys.
- Never mutate cached frames in place.
- Use defensive slicing after predicate reads.
- Keep caches bounded and measure hit rates.

### RAM versus SSD

The correct cache size is machine-dependent. Excessive caching can force macOS
swap onto the old SSD and become slower than a small reread. Record:

- read duration;
- rows and columns materialized;
- cache hits and misses;
- indicator time;
- figure construction time;
- serialized response size;
- callback queue delay.

Tune from these measurements rather than continually increasing cache limits.

### Browser payloads

- Keep logs bounded.
- Avoid returning full figures for toolbar-like changes.
- Render only the visible task page.
- Refresh heavy summaries only when analysis data changes.

---

## Phase 9: `database.py` maintenance

Keep metadata scanning, verification, extension, UI, and callbacks as explicitly
separated sections. Within the same file, split callback registration into:

- extension callbacks;
- verification callbacks;
- database-chart callbacks;
- cleanup callbacks.

Inject a narrow task service if database UI needs task-manager operations. Do not
import the main application from `database.py`, because that creates circular
dependencies.

Remove or clearly disable placeholder callbacks that cannot perform their stated
operation.

Market-data writes must remain behind the canonical validation, preservation,
backup, reread, and atomic-replace path.

---

## Phase 10: eventual file split

Only after same-file boundaries are proven should code move to modules. A
possible eventual layout is:

```text
gpt_16_07.py          app creation and registration
task_model.py         task state and execution
analysis.py           event and metric calculations
strategy_runtime.py   strategy orchestration and registry
charting.py            chart requests, indicators, and figures
task_persistence.py   JSON schema, load, and save
task_services.py      task manager and background jobs
task_ui.py            layouts and renderers
task_callbacks.py     callback registration
database.py           market-data facade
```

This is not a current requirement. Splitting files before reducing hidden global
dependencies would create a multi-file monolith and make debugging harder.

---

## Decision checklist for each future refactor

Before starting:

- What exact responsibility is moving?
- Is this structure, performance, bug-fix, UI, or formula work?
- Which outputs prove behavior is unchanged?
- Which global state and locks does it currently touch?
- Does it read or write market data?
- Could it alter a cache key or stale-value behavior?
- Does it preserve JSON compatibility?
- How will it affect old-Mac CPU, RAM, SSD, and browser payloads?

Before merging:

- Characterization results match.
- Formula changes are absent or explicitly documented.
- Callback IDs and output types are unchanged.
- No new full-file reads were introduced.
- No unbounded cache, queue, or log was introduced.
- No lock is held during sleep, disk, network, or heavy calculation.
- Market-data failure paths leave originals untouched.
- The new boundary is easier to explain than the old code.
- A future distinct strategy can remain distinct without adding flags to a
  universal helper.

---

## Recommended next discussion

The next step should be selecting **one small milestone**, not approving this
entire plan. Recommended options are:

1. Add characterization tests around task-window and selected event behavior.
2. Add a source navigation index and section contracts only.
3. Split the Tasks layout into layout-only builders.
4. Profile interval callbacks and disable idle polling.
5. Extract only the input-preparation stage from `analyze_signal()` after tests.

The safest default is option 1 followed by option 4. Tests protect future formula
development, while reducing idle polling offers a practical speed improvement
without touching mathematical logic.

