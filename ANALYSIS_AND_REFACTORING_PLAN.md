# Task Data Flow Analysis and Refactoring Plan

## Purpose

This document records the current understanding of the application's intended data flow, how the existing code matches that concept, the remaining architectural risks, and a low-risk plan for making the codebase clearer and more modular.

The goal is to preserve the current business logic while making future changes safer, especially changes involving new task-table columns, new event calculations, formula changes, JSON reloads, recalculation, chart interaction, and page rendering performance.

---

## 1. Intended Concept

The key concept is correct and should remain the guiding architecture:

```text
Parsed signals
    ↓
Tasks with static/core fields
    ↓
Candle download and validation
    ↓
Derived calculations
    ↓
Saved/loaded JSON snapshots when needed
    ↓
Final in-memory display storage, currently called Golden Store
    ↓
UI slices 300 tasks per page
    ↓
Task table renders only the selected page
```

### 1.1 Source of Truth

The original source of data is parsed signal input. A parsed signal contains the basic information needed to create a task, such as:

- Symbol
- Signal time
- Signal price / level
- Direction, such as support or resistance
- File timeframe / selected timeframe

### 1.2 Task Static Fields

After parsing, signals become tasks. Each task should have static fields that should generally survive recalculation:

- `task_id`
- `symbols`
- `timeframe`
- `mode`
- `start_date`
- `end_date`
- `signal_time`
- `signal_price`
- `signal_symbol`
- `signal_direction`
- `pre_buffer_minutes`
- `analyze_beyond`
- Strategy/impulse enable flags

These static fields define what the task is.

### 1.3 Task Derived Fields

After candles are downloaded and validated, formulas populate derived fields such as:

- First event time/type/close
- Whether the level was reached
- Whether price reversed direction
- Hit 1%, 1.5%, 2%
- First hit timing in expected/opposite direction
- Max adverse and expected moves
- Signal-based adverse/expected moves
- Drawdown before level and before percentage targets
- Return-to-signal metrics
- Strategy signals
- Impulse signals
- Event lists for charting

These fields are calculated outputs. If formulas change, these fields should be cleared or recomputed while static fields are preserved.

### 1.4 JSON Snapshots

JSON files are snapshots of completed task data. They are important because they avoid unnecessary repeated downloads and calculations.

A loaded JSON file should be treated as a task snapshot set. It should restore static fields and previously calculated derived fields, then publish the loaded tasks into the final display storage so the UI can render immediately.

### 1.5 Recalculation

When a new event, new column, or formula change requires recomputation, the correct flow is:

```text
Load existing JSON/task snapshot
    ↓
Preserve static fields
    ↓
Clear or overwrite selected derived fields
    ↓
Run recalculation formulas
    ↓
Publish finished tasks into Golden Store
    ↓
UI reads Golden Store
    ↓
User can save new JSON snapshot
```

### 1.6 Formula and JSON Evolution Requirement

The application must remain flexible because its purpose is to test new trading approaches. New events, new task-table columns, and changed formulas are expected to appear over time. Therefore, refactoring must support schema evolution instead of assuming that one JSON format or one formula set is final.

Required behavior for future formula/event changes:

1. Old saved JSON files must still open in the app.
2. Missing fields from older JSON files should be treated as normal, not as load errors.
3. Existing static task fields should remain the stable identity of each task.
4. New derived fields should be filled by recalculation when they cannot be read from the old JSON.
5. Formula changes should overwrite or recompute only the affected derived fields while preserving static fields.
6. After recalculation, the updated task snapshot should be publishable to Golden Store and saveable as a new JSON file.
7. The field catalog should be updated whenever a new formula, event, or table column introduces a new task attribute.

This means the field catalog is not meant to freeze the model. It is a safety map. It should make future additions explicit: decide whether each new field is static, derived, UI/state, internal snapshot, or runtime-only.

Recommended safe workflow for adding a new formula or event:

```text
Add or change formula/event logic
    ↓
Add the new task attribute to the field catalog
    ↓
Open an older JSON file
    ↓
Recalculate completed tasks
    ↓
Verify old static fields are preserved
    ↓
Verify the new derived field is populated
    ↓
Publish to Golden Store
    ↓
Save a new JSON snapshot
```

---

## 2. How the Current Code Matches the Concept

The current code mostly matches this concept, although it is still too monolithic.

### 2.1 Parsed Signals

The signal parser creates normalized dictionaries containing fields like symbol, time, price, direction, and file timeframe. This matches the intended source-input concept.

### 2.2 Task Model

`DownloadTask` currently holds both static task fields and derived calculation fields.

Static fields include task identity, symbols, timeframe, mode, period, signal time, signal price, signal symbol, and signal direction.

Derived fields include first event fields, reached/reversed flags, hit flags, max adverse/expected metrics, drawdowns, strategy signals, events, and return-to-signal metrics.

This means the core data model exists, but it currently combines too many responsibilities.

### 2.3 Derived Calculations

`analyze_signal()` populates calculated fields such as first event, level reached, reversal state, hit percentages, drawdowns, adverse/expected moves, and strategy-related data.

This is aligned with the concept that calculated table fields should be derived from candles and task static fields.

### 2.4 Golden Store

The app currently uses global variables similar to a Golden Store:

- `golden_task_store_data`
- `golden_store_version`

The task table callback prefers `golden_task_store_data` and only falls back to `tm.tasks` when Golden Store is empty.

This is good and should be preserved. The UI should continue to read from Golden Store, not directly from mutable working state whenever possible.

### 2.5 Paginated Table Rendering

The task table callback slices the task list into pages of 300 tasks. It then renders only the visible page and caches page output by Golden Store version.

This is the correct performance model for an older machine.

### 2.6 JSON Loading

The JSON loader reconstructs `DownloadTask` objects, restores fields from JSON, updates `tm.tasks`, updates Golden Store, increments `golden_store_version`, and clears table/stat caches.

That is aligned with the intended flow: loaded JSON snapshots become the final display source.

### 2.7 Recalculation

The recalculation flow reconstructs task objects, runs `analyze_signal()` again for completed tasks, and then republishes tasks into Golden Store after recalculation completes.

That generally matches the intended concept.

---

## 3. Current Architectural Problems

### 3.1 `DownloadTask` Has Too Many Responsibilities

`DownloadTask` currently acts as:

- Static task model
- Runtime download job
- Candle download buffer
- Analysis result container
- UI table data source
- Log container
- Chart cache container
- Thread/event state holder

This makes it difficult to safely change calculations or UI fields.

### 3.2 Golden Store Is Global State, Not an Abstraction

Golden Store currently exists as global variables. Many callbacks can read or mutate those globals directly.

That works, but it is fragile. A future callback can easily update `tm.tasks` and forget to publish to Golden Store, or forget to increment the version, or forget to clear caches.

### 3.3 Static vs. Derived Fields Are Not Explicit

The code does not yet have a formal list of:

- Static fields
- Derived fields
- Runtime-only fields
- UI-only fields
- Serialized fields

Because of this, JSON save/load and recalculation rely on broad attribute restoration. That is flexible, but it is risky when adding new calculated columns.

### 3.4 UI Layout, Callbacks, Calculation, Storage, and Rendering Are Mixed

The file is monolithic. It contains:

- Parsing
- Task model
- Downloading
- Analysis
- JSON persistence
- Dash layout
- JavaScript
- Table rendering
- Chart rendering
- Chart measurement
- Callback wiring
- Recalculation
- Storage/cache logic

This makes maintenance difficult and increases the chance that a UI change affects calculation or data-flow behavior.

### 3.5 Table Rendering Still Does Too Much

The table callback is mostly optimized, but it still owns some summary/stat behavior. Ideally, it should only do:

```text
Read Golden Store page
    ↓
Render task table page
    ↓
Return UI
```

Summary statistics should remain separate.

---

## 4. Recommended Target Architecture

A cleaner long-term architecture would be:

```text
models.py
    ParsedSignal
    TaskSpec / StaticTaskFields
    TaskAnalysisResult / DerivedTaskFields
    TaskSnapshot

analysis.py
    analyze_signal(...)
    calculate_hit_metrics(...)
    calculate_drawdowns(...)
    calculate_adverse_expected_moves(...)

storage.py
    save_tasks_json(...)
    load_tasks_json(...)
    GoldenTaskStore

ui/layout.py
    build_root_layout(...)
    build_chart_modal(...)
    build_task_tab_layout(...)

ui/task_table.py
    render_task_table_row(...)
    render_task_table_html(...)
    render_pagination_nav(...)

callbacks/
    task_callbacks.py
    chart_callbacks.py
    storage_callbacks.py
    recalc_callbacks.py
```

This should not be done all at once. The first step should be much smaller and safer.

---

## 5. Recommended First Refactoring Step

### Step 1: Prepare UI Layout Builders Inside the Same File

Do not move callbacks yet. Do not move business logic yet. Do not change Dash IDs.

First, move layout construction into pure functions near the bottom of the current file.

Suggested functions:

```python
def build_index_string():
    ...

def build_global_stores():
    ...

def build_root_layout():
    ...

def build_task_tab_layout():
    ...

def build_chart_modal():
    ...

def build_chart_modal_button_row():
    ...

def build_strategy_details_modal():
    ...

def build_impulse_panel():
    ...

def build_task_table_container():
    ...
```

Then replace:

```python
app.layout = html.Div([...])
```

with:

```python
app.layout = build_root_layout()
```

And replace:

```python
app.index_string = '''...'''
```

with:

```python
app.index_string = build_index_string()
```

### Why this is safe

This mostly moves presentation construction. It should not change:

- Calculation logic
- JSON load/save
- Recalculation
- Golden Store publishing
- Table slicing
- Callback inputs/outputs
- Dash component IDs

### What must not change in Step 1

- Do not rename component IDs.
- Do not change callback decorators.
- Do not change the Golden Store flow.
- Do not change task calculation formulas.
- Do not change JSON serialization behavior.
- Do not change table row output unless strictly required.

---

## 6. Recommended Second Refactoring Step

### Step 2: Extract Table Rendering Helpers

After layout builders are stable, group table rendering into a dedicated section or future module.

Candidates:

```python
TASK_TABLE_HEADERS = [...]

def render_task_table_row(task):
    ...

def render_task_table_html(visible_tasks):
    ...

def render_pagination_nav(current_page, total_pages):
    ...
```

Rules:

- Table rendering should not calculate new business metrics.
- It should only format fields already present on tasks.
- It should remain fast and use raw HTML strings where needed.
- It should preserve the 300-row page slicing behavior.

---

## 7. Recommended Third Refactoring Step

### Step 3: Wrap Golden Store in a Small API

Current global variables should eventually be replaced with a small wrapper.

Example:

```python
class GoldenTaskStore:
    def __init__(self):
        self._tasks = []
        self._version = 0
        self._lock = threading.Lock()

    def publish(self, tasks, reason=""):
        ...

    def clear(self):
        ...

    def get_all(self):
        ...

    def get_page(self, page, page_size):
        ...

    def version(self):
        ...
```

Benefits:

- One place controls version increments.
- One place clears caches.
- One place publishes final task snapshots.
- Fewer callbacks touch global variables directly.
- Easier to reason about UI refresh behavior.

---

## 8. Recommended Fourth Refactoring Step

### Step 4: Define Static, Derived, Runtime, and Serialized Fields

Create explicit field groups:

```python
STATIC_TASK_FIELDS = {
    "task_id",
    "symbols",
    "timeframe",
    "mode",
    "start_date",
    "end_date",
    "signal_time",
    "signal_price",
    "signal_symbol",
    "signal_direction",
    "pre_buffer_minutes",
    "analyze_beyond",
}

DERIVED_TASK_FIELDS = {
    "first_event_time",
    "first_event_type",
    "first_event_is_pin",
    "first_event_close",
    "reached_level",
    "reversed_direction",
    "hit_1",
    "hit_1_5",
    "hit_2",
    "max_adverse_move_pct",
    "max_expected_move_pct",
    "drawdown_before_level",
    "strategy_signals",
    "events",
}

RUNTIME_TASK_FIELDS = {
    "stop_event",
    "pause_event",
    "raw_batches",
    "state_lock",
    "_chart_cache",
}
```

Then JSON save/load and recalculation can become safer:

- Save static + derived fields.
- Do not save runtime fields.
- Recalculation preserves static fields.
- Recalculation clears or overwrites derived fields.

---

## 9. Recommended Fifth Refactoring Step

### Step 5: Move Calculation Logic After UI and Storage Are Cleaner

Only after layout, table rendering, and Golden Store are cleaner should calculation be separated.

Move calculation in small chunks:

1. Hit percentage calculations
2. First event detection
3. Max adverse/expected calculations
4. Drawdown calculations
5. Strategy/impulse calculations

Each move should include comparison checks to ensure existing output does not change.

---

## 10. Practical Safety Rules for Future Work

To avoid breaking current behavior:

1. Do not change Dash component IDs during refactors.
2. Do not mix UI refactor with formula changes.
3. Do not mix Golden Store refactor with chart or measurement UI changes.
4. Keep page size at 300 unless explicitly changing performance behavior.
5. Keep raw HTML table rendering unless replacing it with a measured faster alternative.
6. Keep JSON backward compatibility.
7. Add explicit logs when Golden Store is published:

```text
Golden Store published: N tasks, version=X, reason=load/recalc/parse
```

8. For formula changes, compare old vs. new outputs on a known JSON file before replacing logic.

---

## 11. Summary

The concept is correct:

```text
Parsed signals are converted into tasks.
Tasks hold static source fields and calculated fields.
Heavy calculations can be saved to JSON snapshots.
JSON snapshots can be loaded later without recalculating.
Recalculation should preserve static fields and recompute derived fields.
Finished tasks should be published to Golden Store.
The UI task table should read Golden Store, slice 300 tasks, and render only the active page.
```

The code mostly follows this concept today, but it is too monolithic. The safest first refactoring step is to extract UI layout construction into pure builder functions within the same file, preparing for a future move to a separate UI module without changing business logic.
