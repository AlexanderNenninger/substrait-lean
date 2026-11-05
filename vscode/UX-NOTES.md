# UX notes from the editor prototype

Notes from building the VS Code extension on sverify 0.5's public API,
against the tour's examples ([demo](demo)). The extension's Python side
([check.py](python/sverify_vscode/check.py)) uses only what `sverify`
exports and documents, as an outside tool would. Where that was not enough,
the gap is under [Public API gaps](#public-api-gaps): closed in this PR
with a small public addition, or described with the signature I'd want.
Times are from the laptop under a load of 3 to 20 from other sessions, so
read them as orders of magnitude.

## What felt good

- The report carries enough structure for an editor. `Report.needed`,
  `Report.inferred_from` (each needed precondition with the `Issue` it rules
  out), `Report.suggestions`, `CheckedCondition.nullable`, `.reads`,
  `Report.facts`, `Report.ties` and `Route.suggested` became diagnostics and
  quick fixes without parsing prose.
- Inferred preconditions come back as code. `(_.qty != 0)` goes into
  `requires=` as it is, and the fix's edit is one insertion
  ([check.py](python/sverify_vscode/check.py), `_issues`).
- `on_inferred="error"` as the default suits the editor. A needed
  precondition is an error at the operation that needs it, with three fixes
  side by side: state it, filter first, or guard the operation. Each one
  re-checks to the result its title promises
  ([test_check.py](python/tests/test_check.py)).
- `report.ensures` keeps the order of `ensures`, so each verdict lands on
  the condition that was written, also when the list is a module constant
  shared by several transforms (`REQUIRES`, `ENSURES` in the tour).
- `Issue.shown` (#655) is the operation in the user's terms. `total // qty`
  and `sum(x)` are enough to find the Ibis expression in the source with an
  AST match, and the same text, as a regex, finds it inside a SQL string.
- With `ContractedTransform.check` (added here), checking a transform is one
  call on unbound tables: no patching, no data read, no exception to catch.
- Latency is fine for check-on-save. Importing sverify and Ibis takes about
  1 s once per editor session; the first check in a process 1.5 to 2 s (the
  first transform pays about 1 s); later checks of the demo files take 0.1
  to 0.2 s for six to eight transforms at a counterexample budget of 0.
- sverify's own error for a misspelled `requires` key is good: "requires:
  unknown parameter 'order'; the inputs are: orders; did you mean
  'orders'?". The prototype's static check of contract columns copies that
  style.

## What was awkward

### Running a file to check it

1. A transform has no input schema until it is called. The extension
   checks it on module-level unbound tables named like its parameters, or
   reads its `last_report` where the file called it. A transform in a file
   without either shows "not checked".
2. A module-level call of a transform whose contract is not proved raises
   `VerificationError` and stops the file there; so does a decorator that
   raises (an unknown `requires` key). Nothing after that line is checked.
   The extension says "sverify stopped here" on the line.
3. Calling a transform on bound tables checks `requires` on the data
   (`check_requires=True`), which an editor check should not pay for.
   `check` reads no data.
4. An `sv.verify` report is found only where the file assigns it to a name
   (`report = sv.verify(...)`). A bare `sv.verify(...)` call, or one inside
   a function, leaves no report the extension can reach.
5. The counterexample budget of the file's own `sv.verify` calls is the
   file's: `sensors.py` took 8.3 s at the default 200, almost all of it in
   searches that found nothing: 5.8 s for the two postconditions of
   `unkeyed`, undetermined because rows tie, and 2.6 s for
   `~_.temperature.isnan()`. At a budget of 0 it takes 80 ms.
6. Marimo notebooks, the tour's format, run their cells only under
   `app.run()`, so a check of the file sees no transforms.

### Placing findings in the source

7. Nothing in a report points at source. `Issue.shown` is text, so an
   expression written twice gets the first match; `CheckedCondition` has no
   index into `ensures`, only its order.
8. Issues of a SQL plan often have no `shown`: the demo's SQL model reports
   `DATE_TRUNC_day($3)`, `(DOUBLE($3) /. DOUBLE($4))` and "SUM of $2" in
   Lean's notation, so they sit on the `sv.verify` call
   ([mart.py](demo/mart.py)). The same operations in Ibis have `shown`.
9. `Report.ties` is empty for a SQL window with ties (`deterministic` is
   False), so the SQL version gets no "add `sv.unique(...)`" fix. The Ibis
   version of the same window gets one ([sensors.py](demo/sensors.py)).

### Messages

10. Labels come in three formats. `requires` labels print
    `datetime.datetime(2000, 1, 1, 0, 0)`, needed labels `datetime(1, 1, 1)`
    (valid only after `from datetime import datetime`), and keys
    `unique(a, b)` (no Python). The extension rewrites each label into code
    for the file (`source.label_code`: `sv.unique("a", "b")`,
    `dt.datetime(1, 1, 1)` where the file has `import datetime as dt`).
11. The hint for a `SUM` that may overflow (bounds on the column and a row
    cap) and for a truncated timestamp are prose only (`Report.hints`). The
    extension shows them in the diagnostic and offers no fix. "add
    sv.unique('id') on the input it comes from", for an unproved key, names
    no table.
12. One cause, several diagnostics. Rows that tie in a window make each
    postcondition "Lean only knows it is undetermined: rows may tie…", and
    the report adds its own note: three diagnostics on `unkeyed` for one
    missing key.
13. A refused route's `reason` for an unproved plan repeats the whole
    report (every unproved condition, every needed precondition). The
    extension shortens it to "not verified (see the diagnostics)".
14. `Report.errors` includes the assumed issues (a `SUM` that may overflow
    is both an error and assumed), which the client subtracts with
    `issue in report.assumed`.
15. Numbers are hard to read in a hover: "an integer in [22, 1999999998]",
    `price * 2.000000`, `-9 * 10**18`, and a requires label
    `(_.amount < 1000000000)` for `_.amount < 1_000_000_000`.
16. Some routes have no class: `by_id` with its key stated routes to DuckDB
    as `"reference"` with `cls=None`, which the hover shows as "?".
17. `Report.epsilon` gives `{"m": {"abs": None}}` for a mean of unbounded
    doubles: None reads as "unbounded" by convention only.

### Writing contracts

18. `_` gives no help while typing: nothing completes or checks `_.amout`
    until the transform runs, and then Ibis raises "'Table' object has no
    attribute 'amout'" without naming the condition or the table. The
    extension's completion and live check close that gap with the schemas of
    the last check (`Report.inputs`, `Report.output`), which only exist
    after one successful save.
19. The default `on_inferred="error"` is noisy for overflow. The tour's
    `plus_one` (`amount + 1` on int64) reports a needed
    `_.amount < 9 * 10**18` next to its real finding, "total > 5 is not
    proved". Most int64 columns are far from 2⁶³; a division by zero is a
    real bug class.
20. A quick fix that edits a shared `REQUIRES` constant changes every
    transform and `sv.verify` call that reads it. The extension edits the
    constant, which is what the tour's style asks for, and the preview
    shows where.
21. Fixes interact. In `unit_price` the needed `qty != 0` and the unproved
    `unit >= 0` (NULL where `qty` is NULL) need two preconditions; one at a
    time each leaves the transform unproved. The "add all" fix helps where
    sverify suggests both, but `Report.suggestions` has nothing for this
    NULL case.
22. Two vocabularies. Conditions are Ibis expressions or SQL snippets, and
    a fix for a SQL transform inserts the Ibis form (`_.qty != 0`) into a
    list of SQL strings.

## Public API gaps

What the extension needed and the public API did not have. The first group
is closed in this PR, with tests in
[test_check_api.py](../python/tests/test_check_api.py), the guide's
["Checking without running"](../docs/guide.md#checking-without-running)
and a changelog fragment. Each addition is general: dbt, CI and tests need
the same.

### Closed in this PR

- `ContractedTransform.check(*tables, counterexamples=None, **tables) -> Report`:
  a transform's proof for input schemas (Ibis tables, `ibis.Schema`s or
  mappings), without raising and without reading data. Before, the only way
  was to call the transform, catch `VerificationError` and read its
  `report`, which also checks `requires` on bound data. (1, 3)
- `sv.ContractedTransform`, exported: the type `@sv.transform` returns, so
  a tool finds transforms in a module with `isinstance`.
- `Report.route(engine, route="auto", *, reproducible=None) -> Route`: the
  route and class a run would take, without running. `routes.choose` did
  this, undocumented; `Report.routes` is filled only by a run.
- `Report.inputs: dict[str, ibis.Schema]`: the input tables' schemas, the
  columns `requires` may name, next to `Report.output`. Before, a tool had
  to find the tables in the expression or the `tables=` argument. (18)
- `CheckedCondition.message`, `Issue.message`, `Issue.assumption` and
  `Report.notes: list[str]`: the lines `str(report)` prints for each
  finding. Before, they were built by private helpers
  (`contracts._assumption`, `_cause`, `_observation.why`, `TIES_HINT`).
- `Issue.suggested: dict[str, tuple[str, ...]]`: the preconditions that rule
  an issue out, per table, as labels; `Issue.hint` says the same in words
  ("state `(_.b != 0)` in the requires of 't'"), which a client would
  otherwise parse. (11)
- `SVERIFY_COUNTEREXAMPLES`: the default counterexample budget of
  `sv.verify`, transform calls and `check`. A tool that runs a user's file
  sets it to 0 for the verdicts only. Before, the decorator's 200 was fixed.
  (5)

### Open (to file)

1. Source spans. `Issue.span` and `CheckedCondition.span:
   tuple[str, int, int, int, int] | None` (file, line, col, end line, end
   col), from the Ibis expression's creation site (a frame recorded per
   operation, or the decorator's function and an op path) and for SQL from
   SQLGlot's token positions; `CheckedCondition.index: int` into `ensures`.
   Large: Ibis records no creation sites. (7)
2. `Issue.shown` for every issue of a SQL plan, in SQL's terms (8), and
   `Report.ties` for SQL windows (9).
3. A checking mode for running user code: `with sv.checking():` (or
   `SVERIFY_CHECK=1`), in which transform calls record their report on
   `last_report` and return the unchecked expression instead of raising,
   `requires` is not checked on data, and `Report.run` and `refresh` do
   nothing. `sv.verify` would keep a list of the reports it made, with the
   caller's line: `sv.checking().reports: list[tuple[str, int, Report]]`.
   (2, 4)
4. Input schemas on the decorator: `@sv.transform(inputs={"orders":
   schema})`, so `doubled.check()` needs no arguments and a static tool
   needs no tables in the module. (1)
5. One code format: `Condition.code: str`, the Python a user would write
   (`sv.unique("a", "b")`, `_.ts >= datetime.datetime(1, 1, 1)`), next to
   `label`, with `label` the same format in `requires`, `needed` and
   suggestions; `Condition.sql` for a SQL contract. (10, 22)
6. Structured fixes for what is prose now: `Report.hints` as
   `Hint(issue: Issue, table: str, add: list[str])` (the `SUM` bounds and
   row cap, the truncated column's bounds), and the table on an unproved
   key's suggestion (`CheckedCondition.suggested` filled for keys). (11,
   21)
7. A cause on each unproved condition, `CheckedCondition.cause: Literal["ties",
   "null", "false", "observation", "key"]`, so that clients group one cause
   into one finding; `Route.cause` likewise, with `reason` one sentence.
   (12, 13)
8. `Issue.assumed: bool`, or `errors` without the assumed issues. (14)
9. Facts as data: `Report.ranges: dict[str, tuple[lo, hi, nullable]]`
   next to `facts`, readable numbers in `facts` (`1_999_999_998`), and the
   shortest form of a double (`2.0`). (15)
10. A class on every route, and `epsilon`'s unbounded written as
    `float("inf")`. (16, 17)
11. Contract validation before Ibis builds the conditions:
    `ContractError: requires of orders, condition 1: no column 'amout'; did
    you mean 'amount'?`, from `sv.verify`, a transform's call and `check`.
    (18)
12. `on_inferred` per kind: `on_inferred={"overflow": "warn", "division by
    zero": "error"}`, or a default that errors on divisions, casts and
    domain errors and warns on integer overflow. (19)
13. Skip the counterexample search for a postcondition that is
    undetermined because rows tie: the search found none in 5.8 s on the
    demo, most of a check's time (5).

## Open questions

- Should an editor run the file at all? Running catches what the file
  computes (shared constants, helper functions, schemas from Arrow), and
  executes whatever the module does at import. With `inputs=` on the
  decorator (open gap 4) and literal contracts, a static mode would need no
  execution.
- Hover or code lens for routes: the lens line ("duckdb: exact · polars:
  shim") was the quickest way to see where a plan runs; the hover's table
  says why.
- Quick fixes in the refactor preview cost a click each. For an insertion
  into `requires` the inline diff may be enough; the setting
  `sverify.previewFixes` turns the preview off.
