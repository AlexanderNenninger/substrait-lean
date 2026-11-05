# UX notes from the editor prototype

Notes from building the VS Code extension on sverify 0.5's API, against the
tour's examples ([demo](demo)). Each awkward point has the place in the
API it comes from and, at the end, a change that would remove it. Times are
from the laptop under a load of 4 to 20 from other sessions, so read them
as orders of magnitude.

## What felt good

- The report carries enough structure for an editor. `Report.needed`,
  `Report.inferred_from` (each needed precondition with the `Issue` it rules
  out), `CheckedCondition.suggested`, `.nullable`, `.reads`, `Report.facts`,
  `Report.ties` and `Route.suggested` became diagnostics and quick fixes
  without parsing prose, except for the hints below.
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
- `routes.choose(report, engine)` gives the route and class per engine
  without running anything, which is what a hover needs.
- Latency is fine for check-on-save. Importing sverify and Ibis takes about
  1 s once per editor session; the first check in a process about 1.5 s
  (the first transform pays about 1 s); later checks of the demo files take
  0.1 to 0.2 s for six to eight transforms. The counterexample search added
  little on the demo: 0 against 200 inputs changed a check by under 50 ms.
- sverify's own error for a misspelled `requires` key is good: "requires:
  unknown parameter 'order'; the inputs are: orders; did you mean
  'orders'?". The prototype's static check of contract columns copies that
  style.

## What was awkward

### Running a file to check it

1. A transform has no input schema until it is called. The editor has to
   find tables to call it on: the prototype calls it on module-level
   unbound tables named like its parameters, or reads the report of a call
   the file makes. A transform in a file without them shows "not checked".
2. Calling a transform raises `VerificationError` when its contract is not
   proved, and stops the file there. The prototype patches
   `ContractedTransform.__call__` to record the report and return the
   unchecked body, so the rest of the file is checked too.
3. Calling a transform on bound tables checks `requires` on the data
   (`check_requires=True`), which an editor check should not pay for.
4. A decorator that raises (an unknown `requires` key) raises at import,
   so nothing after it in the file is checked.
5. The decorator's `counterexamples` is fixed at 200
   (`ContractedTransform._verify`). The prototype patches
   `contracts.infer_bounds` to set it.
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
    (valid only after `from datetime import datetime`), keys `unique(a, b)`
    (no Python), and the conditions in `Report.inferred` print as SQL
    (`"qty" IS NULL OR "qty" <> 0`). The prototype rewrites each into code
    for the file (`source.label_code`: `sv.unique("a", "b")`,
    `dt.datetime(1, 1, 1)` where the file has `import datetime as dt`).
11. Hints are prose. The fix for a `SUM` that may overflow comes from
    regexes over the backticks of `Report.hints` and its "requires` of
    orders" for the table (`_hint_fixes`). The "add sv.unique('id') on the
    input it comes from" of an unproved key names no table.
12. One cause, several diagnostics. Rows that tie in a window make each
    postcondition "Lean only knows it is undetermined: rows may tie…", and
    the report adds its own note: three diagnostics on `unkeyed` for one
    missing key.
13. A refused route's `reason` for an unproved plan repeats the whole
    report (every unproved condition, every needed precondition). The
    prototype shortens it to "not verified (see the diagnostics)".
14. Rendering lives in private helpers. Messages in the report's own words
    need `Report._assumed()`, `contracts._assumption`, `contracts._cause`
    and `contracts._observation.why`; `Report.errors` includes the assumed
    issues, which the client subtracts.
15. Numbers are hard to read in a hover: "an integer in [22, 1999999998]",
    `price * 2.000000`, `-9 * 10**18`.
16. Some routes have no class: `by_id` with its key stated routes to DuckDB
    as `"reference"` with `cls=None`, which the hover shows as "?".
17. `Report.epsilon` gives `{"m": {"abs": None}}` for a mean of unbounded
    doubles: None reads as "unbounded" by convention only.

### Writing contracts

18. `_` gives no help while typing: nothing completes or checks `_.amout`
    until the transform runs, and then Ibis raises "'Table' object has no
    attribute 'amout'" without naming the condition or the table. The
    editor's completion and live check close that gap with the schemas of
    the last check, which only exist after one successful save.
19. The default `on_inferred="error"` is noisy for overflow. The tour's
    `plus_one` (`amount + 1` on int64) reports a needed
    `_.amount < 9 * 10**18` next to its real finding, "total > 5 is not
    proved". Most int64 columns are far from 2⁶³; a division by zero is a
    real bug class.
20. A quick fix that edits a shared `REQUIRES` constant changes every
    transform and `sv.verify` call that reads it. The prototype edits the
    constant, which is what the tour's style asks for, and the preview
    shows where.
21. Fixes interact. In `unit_price` the needed `qty != 0` and the unproved
    `unit >= 0` (NULL where `qty` is NULL) need two preconditions; one at a
    time each leaves the transform unproved. The "add all" fix helps where
    sverify suggests both, but `suggested` is empty for this NULL case.
22. Two vocabularies. Conditions are Ibis expressions or SQL snippets, and
    a fix for a SQL transform inserts the Ibis form (`_.qty != 0`) into a
    list of SQL strings.

## API changes I'd propose

1. Input schemas on the decorator, and a check that returns a report:
   `@sv.transform(inputs={"orders": schema}, ...)` (or parameter
   annotations `orders: sv.Input[schema]`), and
   `doubled.check(**tables) -> Report`, which raises nothing and reads no
   data. An editor, a test and CI then share one entry point. (1–3)
2. A checking mode: `with sv.checking():` (or `SVERIFY_CHECK=1`) in which
   transforms record and return instead of raising, `requires` is not
   checked on data, runs and refreshes are skipped, and the counterexample
   budget comes from the context. (2, 3, 5)
3. Source spans: `Issue.span` and `CheckedCondition.span` as
   `(file, line, col, end_line, end_col)`, from the Ibis expression's
   creation site (a frame recorded per operation, or the decorator's
   function and an op path), and for SQL from SQLGlot's token positions.
   `CheckedCondition.index` into `ensures`. (7, 8)
4. `shown` for every issue of a SQL plan, in SQL's terms. (8)
5. One code format: `Condition.code`, the Python a user would write
   (`sv.unique("a", "b")`, `_.ts >= datetime(1, 1, 1)`), next to `label`,
   and `label` the same format everywhere. (10, 22: and `Condition.sql`
   for a SQL contract.)
6. Structured fixes: `Issue.fixes` and `CheckedCondition.fixes` as
   `Fix(table, add=[Condition], rewrite=None | "filter" | "case")`, so a
   client never parses `hints` or `why`. A key that is not shown names the
   input it would come from. (11, 21)
7. A cause on each unproved condition (`"ties"`, `"null"`, `"false"`,
   `"observation"`), so that clients group one cause into one finding;
   `Route.cause` likewise, with `reason` one sentence. (12, 13)
8. Public messages: `Issue.message`, `CheckedCondition.message` and
   `Report.assumed_messages`, the strings `str(report)` prints; `errors`
   without the assumed issues, or a flag on each. (14)
9. Readable numbers in facts (`1_999_999_998`, or bounds as data:
   `Report.ranges[col] = (lo, hi, nullable)`), shortest doubles (`2.0`).
   (15)
10. Every route gets a class; `epsilon` writes "unbounded" as
    `float("inf")`. (16, 17)
11. Validate contracts against the schema before Ibis builds them:
    `ContractError: requires of orders: _.amout: no column 'amout'; did
    you mean 'amount'?`, raised from `sv.verify` and the transform's call
    with the condition's index. (18)
12. `on_inferred` per kind: `on_inferred={"overflow": "warn",
    "division by zero": "error"}`, or a default that errors on divisions,
    casts and domain errors and warns on integer overflow. (19)
13. `sv.verify(..., on_inferred=...)` for SQL contracts could suggest SQL
    snippets: `Report.needed_sql`, from the same conditions. (22)

## Open questions

- Should an editor run the file at all? Running catches what the file
  computes (shared constants, helper functions, schemas from Arrow), and
  executes whatever the module does at import. A static mode (proposal 1's
  `inputs=` and literal contracts) would need no execution.
- Hover or code lens for routes: the lens line ("duckdb: exact · polars:
  shim") was the quickest way to see where a plan runs; the hover's table
  says why.
- Quick fixes in the refactor preview cost a click each. For an insertion
  into `requires` the inline diff may be enough; the setting
  `sverify.previewFixes` turns the preview off.
