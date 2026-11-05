# Notes on sverify's API, from building sverify-dbt

Sverify-dbt uses only what `sverify` exports, as an outside user would: in
practice `sv.verify` on a SQL string with `tables=`, `requires=`, `ensures=`,
`semantics="duckdb"` and `on_inferred="error"`, then the `Report`. Each note
says what happened, what sverify-dbt did about it, and a proposed change.
They were written against `main` at the 0.5.0 release (b87a8963). The
VS Code extension keeps its own notes in `vscode/UX-NOTES.md`.

The repros run in `dbt/` with `uv run python`, after `import ibis, sverify as sv,
sverify.engines`; they show the behaviour before this PR.

## Public API gaps

Gaps in what sverify exports, with the signature sverify-dbt wanted. The
first group is closed in the PR that adds sverify-dbt (#177), each a small
documented addition with tests (`python/tests/test_report_data.py`,
`test_sql_lift_core.py`) and sverify-dbt now uses it. The second group is
larger, for an issue each.

Closed in this PR:

| Note | Addition |
|---|---|
| 1 | `sverify.errors.Unsupported(ValueError)`, the base of every refusal (the lift's, the producer's, the SQL writer's, the Polars translator's); `sverify.engines.Unsupported` is the same class |
| 4 | `CheckedCondition.reason -> Literal["observation", "not_a_key", "ties", "always_false", "may_be_false", "may_be_null", "not_proved_kind", "unknown"] \| None` |
| 5 | `Report.needs -> list[Needed]`, `Needed(table, column, op, value, sql, label, code, issue)`, `code` being the Python for `requires` (`_.qty != 0`) for an editor's quick fix (`sverify.contracts.Needed`) |
| 13 | `verify(tables={"t": {"id": "BIGINT", "s": "VARCHAR NOT NULL"}})`: DuckDB's type names beside Ibis's (`sverify.contracts.input_schema`) |
| 16 | The SQL lift reads `x IS [NOT] TRUE` and `x IS [NOT] FALSE` |
| 19 | `CheckedCondition.condition`: the condition as given in `ensures` |
| 22 | The checker's pipes close when it stops |

To file (larger than this PR):

| Note | Wanted |
|---|---|
| 2 | `class ConditionError(Unsupported)` with `.condition` and `.reason`, raised before the proof; or `CheckedCondition.status == "unreadable"` and the rest proved |
| 3 | `Unsupported.construct: str \| None` (`"function md5"`, `"WITH RECURSIVE"`) and `Unsupported.sql: str \| None`, set at each refusal site of the lift and the producer |
| 6 | `CheckedCondition.needs: tuple[str, ...]`, the needed preconditions its proof used, and `proved` False when it is not empty; needs the checker to report which conditions used which inferred bound |
| 7, 8, 9 | `Issue.shown` from the user's SQL only; no domain error and no assumed `SUM` under `semantics="duckdb"` where DuckDB completes the operation or widens the type |
| 10, 11 | `Report.output` with DuckDB's types under `semantics="duckdb"`, `nullable=False` where proved; `Report.column_facts: dict[str, ColumnFacts]` (nullability, bounds, value set) |
| 12 | `Report.ensured -> dict[str, list[Condition]]` (keys, NOT NULL, bounds of the result), in the form `requires` takes, to chain `verify` calls |
| 14 | `tables` keys qualified as DuckDB resolves names (`"shop.main.orders"`) |
| 15 | `sv.unique(*cols, nulls="distinct")`, a key that lets NULLs repeat (needs a key kind in Lean's `Rel.keys`) |
| 17 | A finite value set per string column in the range analysis (Lean) |
| 18 | Exact signs through double products, quotients and sums of non-negatives (Lean's float bounds) |
| 20 | `sverify.sql_schema(query, tables, semantics="reference") -> ibis.Schema`, the lift's output schema without a proof (a new top-level name) |
| 21 | `Report.engine_version`, and a warning from `run` when the installed engine is another |
| — | `CheckedCondition.suggested` as `Needed`-like records too: sverify-dbt still parses their SQL to write a dbt test (`mapping.as_dbt_test`) |

## Errors

### 1. `sverify.engines.Unsupported` is not what `verify` raises

`sv.verify` raises `sverify.plan_json.Unsupported` for SQL the lift cannot
read. The public `sverify.engines.Unsupported` is `sverify.sql.Unsupported`,
another class, so `except sverify.engines.Unsupported` lets every refusal
through.

```python
t = ibis.schema({"x": "int64"})
try:
    sv.verify("with recursive c as (select 1 as x) select * from c", tables={"t": t})
except sverify.engines.Unsupported:
    print("caught")  # never: sverify.plan_json.Unsupported escapes
```

Sverify-dbt catches `ValueError`, the base of both
([check.py](src/sverify_dbt/check.py), `_verify`).

Proposed: one `Unsupported`, exported from `sverify.errors`, that every
refusal raises (the lift, the producer, the checker), with the others as
aliases of it.

Closed in this PR: `sverify.errors.Unsupported`. Sverify-dbt still catches `ValueError`, since a bad condition raises one too (note 2).

### 2. A bad condition and an unreadable query raise the same error

A condition on a column the result does not have (`ensures=["zz > 1"]`)
raises `Unsupported("cannot resolve the SQL's names: Column 'zz' could not
be resolved")`, as an unreadable query does, and a condition sverify cannot
read (`IS NOT FALSE`) refuses the whole call. A caller with twenty
conditions cannot tell which one failed, or whether the query did.

Sverify-dbt checks test columns against the result's columns first, then, on
an error, verifies the query with no conditions, then each condition on its
own, to find the culprits: up to one checker call per condition
(`_verify`).

Proposed: `verify` reads every condition before it proves anything, and
raises `ConditionError` (a subclass of `ValueError`) with the condition and
the reason; or it reports an unreadable condition in the report
(`CheckedCondition.status = "unreadable"`) and proves the rest.

### 3. Refusals name the construct only as truncated SQL

`dbt_utils.generate_surrogate_key` compiles to `md5(...)`, which the SQL
lift refuses with `MD5(CAST(order_items.order_id AS TEXT) || '-' ||
COALESCE... is not supported yet`. The function is the first word of a
70-character prefix of the expression; a tool that wants to say "md5 is not
supported" has to parse the message.

Sverify-dbt rephrases the message with a regex (`_refusal`).

Proposed: `Unsupported` carries structured fields: `construct`
(`"function md5"`, `"WITH RECURSIVE"`), `sql` (the fragment) and, where
there is one, an issue link. `str(e)` stays as it is.

## Reports and their wording

### 4. `CheckedCondition.why` speaks to a Python user

An unproved key says "the preconditions do not make it a key: add
sv.unique('order_id') on the input it comes from to requires". A dbt user
writes tests, and has no `requires` or `sv.unique`. The reason exists only
as this sentence and as `value` (`"not shown to be a key"`,
`"TRUE, FALSE or NULL"`).

Sverify-dbt rewrites the reason from `value`, matching its strings
(`_why`), which breaks when the wording changes.

Proposed: `CheckedCondition.reason`, an enum (`not_a_key`, `may_be_false`,
`may_be_null`, `ties`, `observation`, `needs_precondition`), with `why` the
current text built from it, so that a frontend phrases it in its own terms.

Closed in this PR: `CheckedCondition.reason`; sverify-dbt words each reason from it (`_WHY`).

### 5. `Report.needed` gives Ibis code; the SQL and the column are hidden

With `on_inferred="error"`, `report.needed` is `{"subscriptions":
["(_.mrr < 7 * 10**17)"]}`: Ibis code, which a SQL or dbt user cannot
paste. The SQL is in `report.inferred`, as an `Inferred`, a `str` subclass
sverify does not export, whose `text` attribute matches the label. The
column, the operator and the bound are in neither. `needs_lines()` writes
advice for the Python API ("declare it in requires", "`subscriptions.filter(...)`
first", "on_inferred='warn' or 'silent' assumes it").

Sverify-dbt pairs `needed` with `inferred` through `Inferred.text`, parses
the SQL with SQLGlot to get the column and bound, and writes a
`dbt_utils.accepted_range` from them ([mapping.py](src/sverify_dbt/mapping.py),
`bound`, `as_dbt_test`).

Proposed: `Report.needed` (or a new `Report.needs`) as a list of
`Needed(table, column, op, bound, sql, label, issue)`, with `issue` the
`Issue` it rules out (today `inferred_from[label]`).

Closed in this PR: `Report.needs`; sverify-dbt writes the dbt test from its column, `op` and `value` (`mapping.dbt_test`).

### 6. A condition proved with a needed precondition reads as proved

Under `on_inferred="error"`, `Report.proved` is False when `needed` is not
empty, but each `CheckedCondition.proved` stays True for a condition whose
proof used the inferred bound. A tool that reads the conditions one by one
reports them as proved.

Sverify-dbt marks every test unproved when `report.needed` is not empty
(`_read`), which also marks the tests that did not need the bound.

Proposed: `CheckedCondition.needs`, the needed preconditions its proof used
(empty when none), and `proved` False when it is not empty under
`on_inferred="error"`.

### 7. `Issue.shown` leaks the plan's internals

A query `select o.customer_id, sum(i.qty * i.price) ...` reports

```
may fail: domain error: IF ((qty = 0) AND ((price = infd) OR (price = -infd))) THEN NaNd ELSE ...
hint: `sum(qty)` is inside an AND or OR (`&`, `|`), and DuckDB and Polars evaluate both operands ...
```

`infd`, `NaNd` and the `IF` come from the plan, and `Issue.expr` has `$6`.
The query has no AND or OR; the hint follows `under_and_or=True` on the
`SUM`, which the guard sverify adds for NaN sets.

Proposed: `Issue.shown` written from the user's SQL (the `qty * price` of
the first issue), the guard's internal expression left out, and
`under_and_or` set only for an AND or OR of the user's.

### 8. Under `semantics="duckdb"`, double arithmetic "may fail"

```python
t = ibis.schema({"r": "float64", "p": "float64"})
sv.verify("select r * p as y from t", tables={"t": t}, semantics="duckdb").errors
# [Issue(kind='domain error', shown='r * p', ...)]
```

DuckDB gives NaN for `0 * inf` and `inf` for `1.0 / 0.0`, without an error,
and `semantics="duckdb"` is documented as "NaN and ±inf included". Either
the issue is a false positive under this profile, or the docs should say
which operations still raise. To confirm.

Sverify-dbt lists these as "may fail at run time".

Proposed: under `semantics="duckdb"`, no domain error for an operation
DuckDB completes; or a field on `Issue` that says under which profile it
raises.

### 9. `Report.assumed` assumes a job that dbt does not run

`select x, sum(y) as s from t group by x` assumes "SUM of sum(y) fits 64
bits in every group (inferred; checked on the data while the job runs,
which raises if it does not)". Under dbt, DuckDB runs the SQL itself, and
DuckDB's `SUM` of a `BIGINT` is a `HUGEINT`, so it cannot overflow 64 bits
(see 10).

Sverify-dbt prints the assumption as it is.

Proposed: under `semantics="duckdb"`, a `SUM` follows DuckDB's widening and
assumes nothing; elsewhere, `Issue` says who checks the assumption (the
sverify job, or the engine).

## Schemas and types

### 10. `Report.output` has the plan's types, not DuckDB's

Under `semantics="duckdb"`, `report.output` for `sum(cents)`, with `cents`
an `INTEGER`, is `Int64`; DuckDB gives `HUGEINT`. A dbt contract that
declares `bigint` passes against `report.output` and fails at `dbt build`
(`tests/test_check.py`, `test_contract_mismatch_and_inputs_without_types`).

Sverify-dbt asks DuckDB for the result's types (`DESCRIBE` of the
compiled SQL over empty tables) and checks contracts against those, noting
where sverify's type differs (`_contract`).

Proposed: under `semantics="duckdb"`, `Report.output` has DuckDB's types (or
a `Report.engine_output`), and `sverify` documents where its plan's type
and the engine's differ.

### 11. Proved NOT NULL columns are nullable in `Report.output`

Every column of `report.output` is `nullable=True`, `count(*)` included,
though `report.facts["c"]` is "an integer ≥ 1". The proved facts are
strings only.

Sverify-dbt proves `c IS NOT NULL` as a condition instead of reading it.

Proposed: `Report.output` types with `nullable=False` where the checker
proves the column never NULL, and the facts as data (`Report.column_facts`:
nullability, integer bounds, the set of a string's values).

### 12. Facts proved of one model do not reach the next

`verify` checks one query. What it proves of the result beyond the
`ensures` (a key, a bound, NOT NULL) is in `facts` as text, so a caller
cannot pass it on as `requires` to the query that reads the result.
Sverify's own answer is fusion (`Node.pipe`), which sverify-dbt cannot use:
dbt builds and tests each model on its own, and an upstream test that
`dbt build` runs (a precondition downstream) has no place in the middle of a
fused pipeline.

Sverify-dbt carries only tests: a key that sverify proves of a model but
that no test states is unknown downstream (see the README).

Proposed: `Report.ensured`, the conditions the checker proves of the result
(keys, NOT NULL, bounds, value sets), in the form `requires` takes, so a
caller can chain `verify` calls; or `requires` in the middle of a fused
pipeline, for a node whose output is checked at run time.

### 13. `tables=` takes Ibis types, and `verify` reads DuckDB's SQL

`ibis.schema({"a": "bigint"})` fails (`integer`, `hugeint` and `text`
too), so a SQL user who knows the table as DuckDB declares it has to
translate each type to Ibis's names.

Sverify-dbt creates each input as an empty DuckDB table and reads its
schema through Ibis's DuckDB backend (`ibis.duckdb.from_connection(...)`).

Proposed: `tables=` accepts DuckDB type names (`{"orders": {"id": "BIGINT"}}`,
or a `CREATE TABLE` column list), parsed with the query's `dialect`.

Closed in this PR: `tables=` takes DuckDB's type names; sverify-dbt passes DuckDB's `DESCRIBE` of each input.

### 14. Inputs must be bare names

dbt's compiled SQL reads `"shop"."main"."orders"`; `verify` refuses it
("only the inputs' tables can be read") and `tables` keys are bare names.
The refusal is safe, but every caller with schemas has to rewrite the SQL.

Sverify-dbt rewrites each relation with SQLGlot to a name of its own,
keeping the alias (`_rewrite`).

Proposed: `tables` keys may be qualified (`"shop.main.orders"`), matched as
DuckDB resolves names (catalog, schema, table, with the defaults).

## Conditions

### 15. No key that lets NULLs repeat

dbt's `unique` test, and a SQL `UNIQUE` constraint, let several rows have
NULL; `sv.unique` counts NULLs as one value (`_weighted.duplicate_keys`:
"NULLs equal"). Proving `sv.unique` implies dbt's test, but assuming it
from dbt's test is unsound for a nullable column.

Sverify-dbt assumes a `unique` test only where a `not_null` test covers the
column ([mapping.py](src/sverify_dbt/mapping.py), `_unique`).

Proposed: `sv.unique(*cols, nulls="distinct")`, a key over the rows with no
NULL in `cols`, which `Rel.keys_sound` can use for joins on those columns.

### 16. `IS [NOT] TRUE` and `IS [NOT] FALSE` are not read

dbt's tests let NULL pass, and the natural condition is `expr IS NOT
FALSE`. Sverify refuses it ("IS FALSE is not supported; only IS [NOT] NULL
is").

Sverify-dbt writes `coalesce((expr), TRUE)`.

Proposed: read `IS [NOT] TRUE/FALSE` (it is `coalesce` with a constant).

Closed in this PR: the lift reads `IS [NOT] TRUE/FALSE`.

### 17. Strings are known only by the exact condition

On a string column, sverify proves a condition only from the same condition:

```python
t = ibis.schema({"s": "string"})
v = lambda q, req, ens: (
    sv.verify(q, tables={"t": t}, semantics="duckdb", requires={"t": req}, ensures=ens)
    .ensures[0]
    .proved
)
v("select 'a' as s from t", [], ["s = 'a'"])  # False
v("select s from t where s <> 'c'", ["s IN ('a', 'b', 'c')"], ["s IN ('a', 'b')"])  # False
v("select s from t", ["s IN ('a', 'b')"], ["s IS NULL OR s IN ('a', 'b')"])  # False
v("select s from t", ["s IN ('a', 'b')"], ["s IN ('a', 'b')"])  # True
```

`accepted_values` is dbt's most common test after `not_null` and `unique`,
and four of the seven unproved tests of the sample project are this case:
a status filtered from a wider set, a tag that is a constant in each branch
of a `UNION ALL`, a quarter named by a constant.

Proposed: a finite set of values in the range analysis for strings (and
other types compared only by equality), through constants, `IN`, `=`, `<>`,
`COALESCE`, `CASE` and `UNION ALL`. A key over a `UNION ALL` whose
branches differ in a constant column follows from it too (the sample's
`unique_combination_of_columns(region, quarter)`).

### 18. The sign of a product of doubles is lost

```python
t = ibis.schema({"q": "int64", "x": "float64"})
sv.verify(
    "select q * x as y from t",
    tables={"t": t},
    semantics="duckdb",
    requires={"t": ["q >= 1 AND q <= 10", "x >= 0 AND x <= 10"]},
    ensures=["y >= 0"],
).facts["y"]
# 'a double > -8.881784197001252e-14 and < 100.00000000000009'
```

A product of two non-negative doubles is non-negative in IEEE 754, but the
rounding error widens the bound below 0, so `y >= 0` and the sample's
`accepted_range(books, min 0)` over `sum(qty * price)` stay unproved.

Proposed: keep a bound exact where rounding cannot cross it (the sign of a
product or quotient, 0 as a bound of a sum of non-negatives).

## Smaller points

### 19. `CheckedCondition` holds the label, not the condition

To pair a result with the condition passed, sverify-dbt matches
`CheckedCondition.label` against the SQL string or `Unique.label`. Proposed:
`CheckedCondition.condition`, the object as given.

Closed in this PR: `CheckedCondition.condition`; sverify-dbt pairs results with its conditions by it.

### 20. No schema of a query without a proof

Sverify-dbt needs a model's result columns before it builds the `ensures`
(to leave out a test on a missing column, see 2), and gets them from
DuckDB. Proposed: `sverify.sql_schema(query, tables, semantics=...)`, the
lift's output schema (the internal `sql_model_schema`).

### 21. Which DuckDB the profile describes

`semantics="duckdb"` models DuckDB at the versions of the engine facts; dbt
runs whatever DuckDB is installed. Proposed: `Report.engine_version` (the
version the profile was characterized at) and a warning from `run` and
`check_inputs` when the installed DuckDB is another.

### 22. The checker's pipes leak at exit

A script that calls `verify` and exits with warnings on prints
`ResourceWarning: unclosed file <_io.BufferedWriter name=4>` from
`sverify/engine.py:522`: the `substrait-check --serve` process's pipes are
not closed. Proposed: close them in the `atexit` handler.

Closed in this PR: `_Checker.close` closes the pipes.

