# Engines, SQL and routes

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
customers = StaticSource(pa.table({"name": ["ada"], "city": ["Paris"]}), name="customers")


@sv.transform()
def cities(orders, customers):
    return orders.join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    )


c = orders.pipe(cities, customers=customers)
c.refresh()
customers.apply(Changes(inserts=[("cy", "Rome")]))
c.refresh()
```

## Engines and SQL

```python
from sverify.engines import run

c.refresh(engine="polars")                     # or "duckdb" (the default), "spark"
snowflake_sql = c.to_sql("snowflake")          # or "duckdb", "spark"; UnsupportedError says why
con = sv.connect()                             # or run a plan on tables of your own
con.create("orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
           [(2, "bob", 5), (3, "cy", 50)])
con.create("customers", ibis.schema({"name": "string", "city": "string"}),
           [("ada", "Paris"), ("cy", "Rome")])
run(con, c.internal_plan, "polars")
```

`Node.to_sql` and `Report.to_sql` write the plan a proof checked as DuckDB,
Snowflake or Spark SQL, with its run-time checks, and refuse a plan that is
not proved, as `refresh` and `run` refuse it.

`refresh(engine=...)` picks where a node's plans run; `sv.connect(engine=...)`
and `engine=` on a transform pick where checks on data run.
`run(con, plan, "spark")` runs the Spark SQL on a local session, and
`run(con, plan, session)` on one you pass (the `spark` extra). The generated SQL assumes
the following about the warehouse:

* Snowflake: time columns are `TIMESTAMP_NTZ`, strings have no
  collation, and tables and columns have quoted lower-case names.
* Spark and Databricks: the session uses the settings of
  `sverify_spark.dialect.SPARK_CONF` (ANSI mode, a pinned time zone, NTZ
  timestamps, case-sensitive names), and strings use the default
  `UTF8_BINARY` collation.
* Both have no row order. `to_sql` writes sorts, `LIMIT` and windows with ties
  and a `LIMIT`'s rows open, as the reference allows (`rows="multiset"`, the
  default for these engines), and refuses `rows="sequence"`, Lean's list order,
  unless the report is `deterministic` (a key on the order columns in the
  contract, which `to_sql` reads from the report). A `SUM` or `AVG` of
  doubles runs natively, within the plan's bound of the reference's correctly
  rounded sum. Snowflake has no interval type, so interval-valued
  expressions are refused there.

How the engine translations relate to the reference semantics is in [docs/engine-profiles.md](engine-profiles.md).

## Integer division in Ibis and SQL

Ibis's `//` is `FloorDivide` and rounds toward minus infinity. Ibis's `%`
and SQL's `//` and `%` truncate toward zero, so the pair `x // d` and
`x % d` splits a negative `x` into a quotient and remainder that do not add
back up under the reference. Sverify follows each operator as its front end
defines it. On `x = -7`, with `d = 2`:

| Input | `x // 2` | `x % 2` | `q * 2 + r == x` |
|---|---|---|---|
| Ibis, `semantics="reference"` or `"duckdb"` | -4 (floor) | -1 (truncated) | no |
| SQL through `sv.sql` or `sv.verify`, reference | -3 (truncated) | -1 | yes |

A plan that splits milliseconds into seconds and a remainder with `t.ms // 1000`
and `t.ms % 1000` gets the identity only for non-negative `ms`. State
`_.ms >= 0` in `requires`, or write the plan in SQL, where both operators
truncate. When one plan uses Ibis `//` and `%` on the same operands under the
reference or DuckDB's semantics, its report carries a hint that names the pair.
[`t7b_div_mod.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/f89f83d2b3fc71848f9d5de8547475b99523b9b5/api-critique/tasks/t7b_div_mod.py)
reproduces the table.

## Routes, classes and profiles

A proof is about the plan under one semantics, a profile: sverify's
reference by default, `semantics="duckdb"` for what DuckDB does,
`semantics="substrait"` for Substrait's extension YAMLs, open wherever they
say nothing. Each profile refines one core that does a superset of
operations ([core, profiles and engines](core-and-profiles.md)). An engine computes its own semantics, so running a proved
plan raises a question: does the proof hold for what the engine computes?
A route answers it. `report.run(con, engine, route="auto")` and
`node.refresh(engine=..., route="auto")` pick one of four, and run the plan
only if one applies:

| Route | When |
|---|---|
| `native` | the plan was proved under the engine's own profile (`semantics="duckdb"` on DuckDB; `"polars"` and `"spark"` are pending) |
| `translated` | the plan was proved under the reference, and sverify's translation to the engine writes the reference's choices (proved for DuckDB; shims proved for Polars and Spark). Before 0.6 this route was `reference`, which `route=` still takes, with a `DeprecationWarning` |
| `transfer` | the plan was proved under another profile, and at every option the plan reads, the engine's choices are within that profile's (the checker's transfer check) |
| `recheck` | the checker proves the plan again under the engine's profile |

`report.routes[engine]` records the route, with its class, which says what
you can rely on. A route prints its class first, then
the evidence, and the route where it is not `translated`:
`shim (integer division rewritten to truncate); evidence proved by Rel.polars_sound, Polars.int_div_trunc`, or
`exact; transfer: verified under semantics="duckdb"; …`.

| Class (`route.cls`) | What it means for you |
|---|---|
| `exact` | every result the engine gives is one the proof covers |
| `observed` | the result equals one the proof covers up to the report's observation: doubles within the plan's bound (`floats="plan"`, the default; computed from the bounds `float-bounds/` proves over the reals, [what is trusted](trusted-base.md)), or what `ensures` states with `sv.equivalent(...)`, such as rows as a multiset, one zero, or a tolerance `floats=sv.within(...)` the plan's bound meets |
| `shim` | either of the above after the translation adds a small fix (a truncating division, a NULL placement); it costs an expression per row or a sort |
| `refused` | none of the above: the run raises `sverify.errors.RouteError` and nothing runs; for a plan that is not proved, `sverify.errors.UnverifiedRunError`, a `VerificationError` |

`route.evidence` says whether each step rests on a Lean proof (`proved`)
or on anything else, tests and probes among them (`tested`). `route.theorems`
names the proofs, and `route.facts` and `route.version` the engine facts and
the engine version they were probed at. `print(report.details())` shows the same before
any run, one `evidence:` line per engine:
`evidence: polars shim, proved by Rel.polars_sound, Polars.int_div_trunc on polars's model (facts …)` or
`evidence: spark exact, tested at 4.3.0 (facts spark-int-arith, …; #…)`. A proof
"on the engine's model" proves the model the engine's facts describe; those facts
say the engine is that model. Before the plan runs, its preconditions,
the inferred bounds and the assumed `SUM`s are checked on the data, and a
batch that breaks one raises `PreconditionError`.

A refusal names its reason: the options where the engine's choices differ,
with the facts that record them (the [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)
list every fact). What to do about one:

- Verify under the reference (the default), whose translation shims most
  differences, in place of an engine's profile.
- State the observation the difference hides: `rows="multiset"` for row
  order, `zeros="canon"` for the sign of a zero. A sum in another order is
  within the plan's bound, which a run accepts by default.
- Add the precondition the reference raises on, such as a bound on a
  column, so the plan never meets the difference.
- Run on the other engine, or pass `route="translated"` (or another) to see
  why that one fails.

`report.run(..., reproducible=sv.equivalent())`, like a sink's
`reproducible=`, asks for a determined result, which fixes the order of
ties
([tie order](reference-semantics.md#tie-order-and-determinism)):
it refuses a plan whose result is not determined up to row order, and the
reason names each window, ordered aggregate or `LIMIT` where ties stay open
(`str(report)`), with the `sv.unique(...)` that would close them
(`report.ties`).
Without it the plan runs with the engine's own order of the ties, which every
proof covers. [Example 7](getting-started.md#7-a-plan-checked-under-duckdbs-profile)
shows a transfer and a refusal, and
[how a route is chosen](verifying.md) gives the
rules behind them.

A postcondition can name what the result's consumer observes:

```python
readings = sv.connect()
readings.put("t", pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}))
t = readings.table("t")
means = sv.verify(
    t.group_by("k").aggregate(mean_x=t.x.mean()).order_by("k"),
    requires={"t": [_.x.between(-1e6, 1e6), sv.max_rows(1_000_000)]},
    ensures=[sv.equivalent(rows="sequence", floats=sv.within(abs=1e-3)), sv.unique("k")],
)
duckdb_result = means.run(readings, "duckdb", route="auto")
polars_result = means.run(readings, "polars", route="auto")
means.lenses.equal(duckdb_result, polars_result)  # True
```

Polars sums doubles in its own order, so its mean is within the plan's
bound of the reference's: here about `2.2e-4`, from the bounds on `x` and the
row cap (`--contract`'s `epsilon`, `SubstraitLean/Epsilon.lean`). The
values may cancel, so only an absolute bound holds, and the tolerance is
absolute.

Doubles follow one model. Without `sv.equivalent` in `ensures`, rows and
list elements are multisets, one zero and one NaN are read, doubles are within
the plan's bound and other values are exact: the default observation
([the table](core-semantics.md#the-default-observation)), which
`report.lenses` prints with its bound,
`equivalent(elements='multiset', floats=plan, ≤ 2.2e-04, zeros='canon')` here. `sv.equivalent(...)` states each component, and one you
leave out is exact. `floats=sv.within(abs=..., rel=..., ulps=...)` states a
tolerance, and `floats="exact"` asks for the same bits. `verify` checks
either against the plan's bound on each engine; where
no engine meets it, the plan is not proved, and the report's `lenses:`
line gives the plan's bound, the reason per engine and a tolerance that
would do ([example 5](getting-started.md#5-doubles-within-the-plans-bound)).

`sv.equivalent` also takes `elements="multiset"`, `zeros="canon"`,
`timestamps="ms"`, `strings="nfc"` (or `"casefold"`, `"ascii"`), `decimals="value"` and
`errors="kind"`; `Observation.refines` orders observations component by
component. A postcondition that reads what the observation ignores, such as
`_.mean_x <= 100` under a float tolerance, is reported with
`CheckedCondition.ignores`; `sv.approx(_.mean_x <= 100)` allows for the
tolerance. The checker names the components each condition's value depends
on, from the columns it reads, and a condition that depends on none the
observation ignores holds on every result equal to a proved one up to the
observation. A comparison with a constant
narrowed by the tolerance, `x ≤ c - ε` for `x ≤ c`, keeps the original on
every such result. A postcondition is proved on every
result the reference allows, and
`CheckedCondition.allowed` says so. A double `SUM` or `AVG` is one
value, the exact sum rounded once, so this covers postconditions that read
it; one that reads a statistical aggregate, whose value is still a choice of
the reference, is proved of the plan's own value, and `sv.approx` allows for
the bound.

The bound grows with the row cap and the values: for a `SUM` of `n` values
of at most `M` in absolute value, about `2.2e-16 · n² · M`, and for an
`AVG` that divided by `n` (`2.2e-4` above, with `n = M = 10⁶`). Tighter
`requires` give a tighter bound ([float-bounds.md](float-bounds.md)).

## SQL models

A transform's body can be SQL over its inputs by name. Sverify proves,
composes and refreshes it like any other:

```python
@sv.transform(
    requires={"orders": ["amount >= 0", "amount IS NOT NULL"]},
    ensures=["total >= 0", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, coalesce(sum(amount), 0) AS total FROM orders GROUP BY customer",
        orders=orders,
    )


totals = orders.pipe(per_customer)  # proved here, like an Ibis transform
totals.refresh()
assert sorted(totals.to_arrow().to_pylist(), key=str) == [
    {"customer": "bob", "total": 5},
    {"customer": "cy", "total": 50},
]
```

`sverify check` reads a Python file or a dbt project; a bare `.sql` file is not checked yet, so put the query in `sv.sql` in a `.py` file, or use [sverify-dbt](../dbt/README.md).
Several inputs are several keywords (`sv.sql(query, orders=orders,
customers=customers)`). The SQL is DuckDB's, and sverify plans it itself,
through SQLGlot, with sverify's reference semantics (`semantics="reference"`,
the default) or DuckDB's (`semantics="duckdb"`), for a subset of
SQL so far ([what the SQL lift reads](reference-semantics.md)).
