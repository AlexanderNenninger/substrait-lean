# Reproducible sinks, engine settings, sharding and pytest

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
gcon = sv.connect()
gcon.put("lines", pa.table({"id": [1, 2, 3], "n": [4, 0, 2], "total": [100, 250, 30]}))
lines = gcon.table("lines")
kept = lines.filter(lines.n != 0)
per_line = sv.verify(kept.select(kept.id, per=kept.total // kept.n), requires={"lines": [_.total >= 0]})
```

## Reproducible sinks

A stored node's sink commits each epoch once, so a rerun must give the same
result. The sink states what "the same" means (`reproducible=`,
[two lenses per output](how-to-production.md#reproducible-sinks)): `sv.equivalent()` asks for exact
bits, and `sv.equivalent(floats=sv.within(...))` accepts doubles within a
tolerance. A refresh whose engine may give another result on a rerun is
refused with a `RouteError`; so is a plan whose ties stay open, since the
sink then needs a determined result, and the error names the
place. Polars's streaming `SUM` of doubles may add in
another order each run, so a double sum on Polars states both: the transform's
`ensures=[sv.equivalent(floats=sv.within(abs=...))]` for the route, and the
sink's `reproducible=sv.equivalent(floats=sv.within(abs=...))` for the
rerun. The transform's tolerance must be at least the plan's bound, each
run's distance to the reference. Two runs may differ by twice that, so the
sink's absolute tolerance must be at least twice the plan's absolute bound,
or its relative tolerance at least the plan's relative bound. With `x` within
±1000 and `max_rows(1000)` that bound is about `2.2e-7`, so `abs=1e-6` passes
both. Exact doubles on a rerun need doubles that are exact on the engine, so
`sv.equivalent()` over a double `SUM` or `AVG` is refused; the default
(`floats="plan"`) or a tolerance with a row cap is met:

```python
from sverify.io import DeltaSink

samples = StaticSource(pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}), name="samples")


@sv.transform(
    requires={"samples": [_.x.between(-1000, 1000), sv.max_rows(1000)]},
    ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
)
def sample_sums(samples):
    return samples.group_by("k").aggregate(total=samples.x.sum())


sums = samples.pipe(sample_sums).write(
    DeltaSink("sample_sums", reproducible=sv.equivalent(floats=sv.within(abs=1e-6)))
)
print(sums.refresh(engine="polars", route="auto").nodes[0].route.taken)
# translated
```

A relative tolerance (`rel=`) fails where the values may cancel, since
only an absolute bound holds there. A result not determined up to row
order, such as a `LIMIT` over ties, is refused by every sink.

## Engine settings and versions

A profile's facts were probed under the engine's default settings, at a
pinned version (DuckDB 2.0.0, Polars 2.1.0). Before a routed run, sverify
reads the settings the plan will run under and compares them:

- DuckDB: `default_null_order`, `default_order`, `integer_division`,
  `error_on_division_by_zero`, `ieee_floating_point_ops`,
  `default_collation`, `scalar_subquery_error_on_multiple_rows`,
  `enable_optimizer` and `disabled_optimizers` refuse the run with the
  setting named (`sverify.errors.EngineSettingsError`), since a choice the
  route relies on depends on each; `preserve_insertion_order` warns
  (`EngineSettingsWarning`). `TimeZone` and `Calendar` are not checked:
  the SQL sverify writes never reads them.
- Polars: an engine affinity that forces another engine than streaming
  (`pl.Config.set_engine_affinity("in-memory")`) refuses the run, since
  sverify runs Polars's streaming engine.
- Spark: a session of yours whose settings differ from
  `sverify_spark.dialect.SPARK_CONF` (ANSI mode, `TIMESTAMP_NTZ`, the UTC
  session time zone, …) refuses the run where the plan relies on them. The
  session sverify starts sets `SPARK_CONF` and reads it back before it runs
  anything.
- The settings read are recorded on the route (`Route.settings`, the
  report JSON's `settings`), so a run's record says what it ran under.
- An unprobed patch of the probed minor warns (`EngineVersionWarning`) and
  is recorded on the route (`Route.unprobed_version`); another minor or
  major is refused (`EngineVersionError`) until the probes are re-run, and
  runs with `run(..., unverified=True)`
  ([D70](decisions.md#d70-engine-versions-probed-in-range-out-of-range)). To
  refuse every unprobed version, turn the warning into an error:
  `warnings.simplefilter("error", sverify.errors.EngineVersionWarning)`.

`lines.get_backend()`, the backend of a table of the connection, is its Ibis
DuckDB backend, for SQL of your own, such as
`lines.get_backend().raw_sql("SELECT current_setting('threads')")`. Sverify
runs plans on a cursor of its own, so a plain `SET` there leaves sverify's
runs alone, and a `SET GLOBAL` reaches them, which the check sees:

```python
from sverify.errors import EngineSettingsError

lines.get_backend().raw_sql("SET GLOBAL integer_division = true")
try:
    per_line.run(gcon, "duckdb", route="auto")
except EngineSettingsError as e:
    print(e)
# duckdb's integer_division is True, and the facts of semantics="duckdb" hold under False (duckdb-F1): ...
lines.get_backend().raw_sql("SET GLOBAL integer_division = false")
```

## Sharding and other optimizations

`sverify.engines.run_sharded(plan, shards, sharded=[...], broadcast=...)`
runs a plan on each shard of its data and combines the results, with a Lean
proof that this equals the result on all the data. Filters, projections and
joins with a broadcast table are concatenated; `COUNT`, integer `SUM`, `MIN`
and `MAX` combine in two phases; with split keys (`keys={"orders":
["region"]}`, as a partition column guarantees), aggregates grouped by the
key, co-partitioned joins and tie-free windows run per shard. `SUM` and
`AVG` of doubles split where `reproducible=` accepts doubles within a
tolerance, as a sink's `reproducible=` states it:
`sv.equivalent(floats="plan")` accepts the bound `Shard.lean` proves over the
reals (`sharded_near`), and
`sv.equivalent(floats=sv.within(abs=...))` raises where a row's bound exceeds
the tolerance. `tolerance=True` returns that bound per row on how far
each is from the one-pass sum
([Sharded `SUM` and `AVG`](float-bounds.md#sharded-sum-and-avg)).
Anything else raises `NotShardable` with the reason. The checker also proves
where the per-row overflow checks can go, and rewrites the transformation
with what the preconditions establish (a `DISTINCT` over a key goes, a filter
the preconditions imply goes, a left join on a NOT NULL foreign key becomes an
inner join, an unread join to a dimension goes); the report keeps both
internally, and [docs/optimizations.md](optimizations.md) describes them and
compares them with what the engines already do.

## Testing with pytest

Installing sverify registers a pytest plugin, so your suite can test its
transforms without a conftest. `sverify.testing.assert_contract(node)`
asserts that a node's contract is proved; with `data=` and `expected=` it
also runs the node on those rows, checks the preconditions and
postconditions on them, and diffs the output against the expected rows.
`assert_engines_agree(node, data)` runs it on every installed engine and
diffs their results. `cases(node)` is a Hypothesis strategy of inputs that
meet the preconditions (`pip install 'sverify[testing]'`, beside an engine's
extra such as `sverify[testing,duckdb]`, since it checks them on an engine). The fixtures are
`sv_source(rows, schema, name=...)`, an in-memory source, and `sv_engine`,
which runs a test once per installed engine (`--sv-engines=duckdb,polars`
picks them). [`python/tests/test_plugin_example.py`](../python/tests/test_plugin_example.py)
is an example test file, and [`python/tests/test_tour.py`](../python/tests/test_tour.py)
tests the tour's transforms the same way.

A test of a transform, in one file:

```python
from sverify.testing import assert_contract, assert_engines_agree, source


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 22, sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


def test_big_orders():
    orders = source([], {"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    node = orders.pipe(big_orders)
    assert_contract(node)  # the contract is proved
    data = {"orders": [(1, "ada", 30), (2, "bob", 5)]}
    assert_contract(node, data=data, expected=[(1, 60)])  # and holds on these rows
    assert_engines_agree(node, data)  # every installed engine agrees


test_big_orders()
```

A failure lists the offending rows: those that break a precondition, or the
expected rows that are missing or unexpected.
