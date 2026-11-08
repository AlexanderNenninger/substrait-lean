---
name: add-function
description: Add a Substrait function, a black-box DuckDB function or a coverage case to sverify: where each piece goes (Functions.lean rows and anchors, Parse.lean, the Python function table, SQL writer, SQL lift, Ibis producer, tests, engine support, reference docs). Use when adding or extending a function, a coverage case, a lift rule or a writer case, or when closing a coverage target.
---

# Adding functions and coverage cases

Parallel PRs used to conflict in shared lists and dispatch tables; these are
now split by area. The areas are the same everywhere: `core` (logic,
comparisons, NULLs, arithmetic, math, bitwise), `strings` (with LIKE, regex,
digests), `temporal`, `nested` (lists, structs, lambdas, UNNEST),
`aggregates`, `windows`, `relations` and `casts`. A feature edits its area's
file; touch the shared `_base.py` only for what the area files say lives there.

- **Substrait function** (`core/Sverify/Core/Functions.lean`): add a row at the
  end of its area's table (`core`, `strings`, `temporal`, `nested`,
  `aggregates`, `windows`), one per constructor it is modelled by, with the
  next free anchor in that area's range (100s core, 200s strings, 300s
  temporal, 400s nested, 500s aggregates, 600s windows), its group from
  `docs/core-semantics.md`, its constructor and how the parser reads it.
  `Write.lean`'s anchors (`UnFn`/`BinFn`/`AggFn.anchor`, `fn "name"`) and
  `Pretty.lean` read the row. `lake build` rejects duplicate anchors or
  names, out-of-range anchors, a constructor with two rows and a group the
  design does not list. `substrait-check --functions` prints the tables as
  JSON for the Python mirror.
- **Coverage case** (`python/tools/sverify_dev/coverage_cases/<area>.py`): append to
  that module's `CASES`, and put its refusals in the same module's `REFUSED`,
  `TIE_FREE`, … (`coverage.py` documents them). A new area is a new module
  listed in `coverage_cases.AREAS`.
- **Parse** (`SubstraitLean/Parse.lean`): a row marked `reads := .plain`
  (`.float` for doubles) is read as its constructor with nothing more.
  Otherwise the function's arm in its area's `mkCoreCall?`, `mkStringCall?`,
  `mkTemporalCall?` or `mkNestedCall?`, before its last arm, which reads the
  table. Doubles go in `mkFloatCall`, decimals in `decimalCall`, constant folding in
  `foldCoreCall`/`foldTemporalCall`, aggregates in `parseMeasure`'s
  `match name, k`, windows in `parseWindow`'s `match baseName name, args`. A
  string function's integer arguments go in `stringFns`; an option's functions
  in that option's arm of `optionAccepts`.
- **Function table** (`python/src/sverify/_functions.py`, #544): a scalar
  function of strings, math or bitwise operations is a row: its anchor, area
  and group (`docs/core-semantics.md`), its kinds, the writer's operation, the
  SQL of each dialect, and the SQLGlot nodes and Ibis operations that read as
  it. A row whose `call`, `expr`, `lift` or `ibis` covers the function needs
  no case in the places below; `tests/test_functions.py` checks the rows
  against `Functions.lean` (`substrait-check --functions`).
- **SQL writer** (`python/src/sverify/sql/core/<area>.py`, `strings`,
  `temporal`, `nested`): the function's case in the area's `call` (`mkCall`),
  its SQL in the area's `expr`, and its result kind in the area's `UN_KINDS` or
  `BIN_KINDS`. In `_base.py`, add the op to the area's `<Area>UnOp`/`<Area>BinOp`
  Literal and the `Dialect` hook under the area's comment. Core functions,
  aggregates, windows, casts and relations are still in `_base.py`.
- **SQL lift** (`python/src/sverify/sql_lift/<area>.py`): the rule function and
  its entry in the area's `register({...})`, keyed by SQLGlot node type.
  Aggregates (`_AGGREGATES`), windows (`_RANKING`), joins, set operations and
  UNNEST are still in `_base.py`'s `_Lift`.
- **Ibis producer** (`python/src/sverify/ibis_substrait/<area>.py`): the rule
  and its entry in the area's `register({...})` (expressions),
  `register_rels({...})` (relations) or `register_refusals({...})`. Aggregates
  are a branch of `aggregates.measure`, window functions of `windows.window`;
  decimal typing (`_exact`) is in `_base.py`.
- **Tests of the lift**: `python/tests/test_sql_lift_<area>.py`, with the
  shared tables in `python/tests/_sql_lift.py`.
- **Black box** (#325), a DuckDB function the checker treats as opaque: add a
  row to `BlackBox.scalars` or `BlackBox.aggregates`
  (`core/Sverify/Core/BlackBox.lean`) with its types, NULL handling, whether it
  raises, its laws and a `sample` the laws allow (`scalars_wf` checks it by
  `decide`), and the same row, at the same index, to `TABLE` in
  `python/src/sverify/black_box.py` with DuckDB's SQL. Its anchor is 700 plus
  its index, under the black boxes' URN; the parser, the lift
  (`sql_lift/blackbox.py`), the writers and the refusals of other engines
  read the table, and `tests/test_black_box.py` checks the two tables agree.
  Add a lift rule only where SQLGlot reads the call as a node of its own
  (`to_base64`), and a Lean evaluator in `BlackBox.evalScalar` where Lean can
  compute it exactly. Test it in `tests/test_black_box.py`: oracle C, the
  laws on random data, a contract they prove. A new law kind needs its case
  in `BlackBox.Law.holds` and `Law.bound` (`Contracts.lean`).
- **Engine support** (`python/src/sverify/_support.py`): a function that not
  every engine runs (a new one runs on DuckDB only, #271) gets a row in
  `SUPPORT` with the engines that run it. `to_sql` and `run_plan` refuse it
  on the others before they dispatch, with "see #271". Refusals that depend
  on types or arguments stay in the engine.
- **Reference semantics** (`docs/reference-semantics.md`): the area's section.
