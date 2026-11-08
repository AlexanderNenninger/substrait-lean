# Examples

Ten short examples, each a step up from the one before: a contract proved
and run, SQL, the preconditions Sverify infers, routes to Polars, tolerances
for doubles, reproducible sinks, engine profiles, Substrait's own semantics,
a plan checked under Polars's, and the export of a verified plan to any
Substrait consumer. The inputs are a few rows in memory. Every block runs as written,
in order: `python/tests/test_readme.py` runs them and checks each printed
line against the comment under it.

```bash
pip install 'sverify[polars,delta]'
```

## 1. A contract, proved and run

A transform states what it assumes (`requires`) and what it promises
(`ensures`). Sverify proves the promise for every input that meets the
assumptions when the transform is applied, before any data runs, and
`refresh` computes the result on DuckDB.

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2, 3], "qty": [4, 5, 2], "total": [100, 250, 30]}), name="orders"
)


@sv.transform(
    requires={"orders": [_.qty > 0, _.total >= 0, sv.unique("id")]},
    ensures=[_.unit >= 0, sv.unique("id")],
)
def unit_prices(orders):
    return orders.filter(orders.total > 50).select(orders.id, unit=orders.total // orders.qty)


prices = orders.pipe(unit_prices)  # proved here
prices.refresh()  # run on DuckDB
print(sorted(prices.to_arrow().to_pylist(), key=lambda r: r["id"]))
# [{'id': 1, 'unit': 25}, {'id': 2, 'unit': 50}]
print(unit_prices.report)
# requires orders: (_.qty > 0)
# requires orders: (_.total >= 0)
# requires orders: unique(id)
# ensures (_.unit >= 0): proved
# ensures unique(id): proved
```

The [guide](guide.md#contracts) has the rest of the report and what
happens when a postcondition doesn't follow.

## 2. SQL through `sv.verify`

`sv.verify` checks a query in SQL or Ibis over the tables of a connection
and returns the report; `report.run` runs the plan it checked.

```python
con = sv.connect()
con.put("orders", pa.table({"id": [1, 2, 3], "qty": [4, 5, 2], "total": [100, 250, 30]}))
report = sv.verify(
    "SELECT id, total // qty AS unit FROM orders WHERE total > 50",
    tables={"orders": con.table("orders")},
    requires={"orders": ["qty > 0", "total >= 0"]},
    ensures=["unit >= 0"],
)
print(report.proved)
# True
print(report.run(con).to_pylist())
# [{'id': 1, 'unit': 25}, {'id': 2, 'unit': 50}]
```

`report.run` refuses a report that did not prove (`report.proved` is False)
with a `RouteError`; `report.run(con, unverified=True)` runs it anyway.

The SQL is DuckDB's dialect, read with sverify's reference semantics
(`semantics="duckdb"` reads it as DuckDB computes it). `//` is integer
division, and `/` would give a double.

## 3. The preconditions a plan needs, declared and checked before the run

Leave out `requires`, and Sverify works out the preconditions under which
the plan cannot fail: here that `qty` is never zero, and that `total` stays
far enough from the smallest integer for the division not to overflow. It
reports the plan as not proved and asks you to declare them
([D23](core-semantics.md#d23-inferred-preconditions-are-errors-by-default)):

```python
from sverify.errors import PreconditionError

t = con.table("orders")
undeclared = sv.verify(t.select(t.id, unit=t.total // t.qty))
print(undeclared.proved)
# False
print(undeclared)
# needs: (_.total >= -9 * 10**18) and (_.qty != 0) on orders, inferred from `total // qty` (overflow or division by zero otherwise): declare them in requires ...
# ...
```

Declare them, here as `qty != 0` and `total >= 0`, and the plan is proved.
`report.run` checks the declared preconditions on the data first, and
refuses a batch that breaks one before anything runs
([#604](https://github.com/AlexanderNenninger/substrait-lean/issues/604)):

```python
declared = sv.verify(
    t.select(t.id, unit=t.total // t.qty),
    requires={"orders": [_.qty != 0, _.total >= 0]},
)
print(declared.proved)
# True
con.put("orders", pa.table({"id": [4], "qty": [0], "total": [10]}))
try:
    declared.run(con)
except PreconditionError as e:
    print(e)
# 1 row(s) of orders violate (_.qty != 0): refused before the run
```

The other fix is a rewrite that no row needs the precondition for:
`t.filter(t.qty != 0)` before the division, or a `CASE`.
`on_inferred="warn"` or `"ignore"` assumes the inferred preconditions and
checks them on the data as declared ones are.

An `AND` or `OR` evaluates both operands, as DuckDB and Polars do (D19 in
[core-semantics.md](core-semantics.md)), so `(qty != 0) & (total // qty > 1)`
still needs the precondition. Guarding the division itself,
`ibis.cases((_.qty != 0, _.total // _.qty)) > 1`, is proved without it.

## 4. The same plan on Polars, by a route

`route="auto"` chooses how the proof reaches the engine and refuses the plan
where none applies. The route names the plan's class on that engine:
`exact` (every result the engine gives, the reference allows), `observed`
(equal under an observation the postcondition states, a float tolerance
included), `shim` (after a proved translation) or `refused`
([D13](core-semantics.md#d13-choosing-the-route),
[D22](core-semantics.md#d22-four-route-classes-and-tolerances-are-observations)).

```python
con.put("orders", pa.table({"id": [1, 2, 3], "qty": [4, 5, 2], "total": [100, 250, 30]}))
print(declared.run(con, "polars", route="auto").to_pylist())
# [{'id': 1, 'unit': 25}, {'id': 2, 'unit': 50}, {'id': 3, 'unit': 15}]
print(declared.routes["polars"])
# shim (integer division rewritten to truncate); evidence proved by Rel.polars_sound, Polars.int_div_trunc on polars's model ...
```

SQL's `//` truncates under the reference and Polars's integer division floors,
so the translation writes a shim, proved in Lean
(`SubstraitLean/PolarsShims.lean`). Ibis's `//` is `FloorDivide` and floors under
every semantics, and its `%` truncates under the reference
([the table](guide.md#integer-division-in-ibis-and-sql)).
The [realizability table](realizability.md) lists every option's class on
each engine.

## 5. Doubles within the plan's bound

DuckDB and Polars add doubles in different orders, so a mean's last bits may
differ. The checker proves how far: a bound on each double the plan computes
([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)). With
no observation in `ensures`, a run accepts doubles within that bound, the
same as `sv.equivalent(floats="plan")`, and the report prints the bound.

```python
con.put("readings", pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}))
r = con.table("readings")
mean_x = r.group_by("k").aggregate(mean_x=r.x.mean())
bounded = {"readings": [_.x.between(-1000, 1000), sv.max_rows(1000)]}
means = sv.verify(mean_x, requires=bounded)
print(means.observation)
# equivalent(floats=plan, ≤ 1.1e-10)
on_duckdb = means.run(con, "duckdb", route="auto")
on_polars = means.run(con, "polars", route="auto")
print(means.equivalence.equal(on_duckdb, on_polars))
# True
```

Both routes are `observed`: equal to a result the reference allows, up to
the plan's bound on doubles. A column a postcondition reads keeps its exact
value; `sv.approx(...)` allows for the bound.

A tolerance of your own goes in `ensures`:
`sv.equivalent(floats=sv.within(abs=..., rel=..., ulps=...))`. `verify`
checks it against the plan's bound on each engine, and one that no engine
meets leaves the plan unproved, with the reason and a tolerance that would
do.

```python
tight = sv.verify(
    mean_x, requires=bounded, ensures=[sv.equivalent(floats=sv.within(abs=1e-12))]
)
print(tight.proved)
# False
print(tight)
# observes: equivalent(floats=within(abs=1e-12)); the plan's bound on its doubles is 1.1e-10; NOT met: no engine meets the tolerance
#   on duckdb: agg.fsum's sum_order: mean_x is within abs=1.11577e-10 of the reference, and the postcondition asks within(abs=1e-12): state sv.equivalent(floats=sv.within(abs=2e-10)) or looser in ensures, ...
```

`floats="exact"` asks for the same bits, and the report lists the engines
that give them on its `observes:` line: for this mean, none.

## 6. A reproducible sink, kept up to date

A sink commits each epoch once, so a rerun must give the same result. The
sink says what "the same" means (`reproducible=`, D20), and a refresh is
refused where the engine's run-to-run variation does not refine it. Polars's
streaming `SUM` of doubles may add in another order each run, so a sink that
asks for exact bits, `reproducible=sv.equivalent()`, is refused there, and
one that accepts the plan's float bound is not:

```python
from sverify.io import Changes, DeltaSink
from sverify.errors import RouteError

readings = StaticSource(pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}), name="readings")


@sv.transform(
    requires={"readings": [_.x.between(-1000, 1000), sv.max_rows(1000)]},
    ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
)
def sums(readings):
    return readings.group_by("k").aggregate(total=readings.x.sum())


try:
    exact = DeltaSink("sums_exact", reproducible=sv.equivalent())  # exact bits
    readings.pipe(sums).write(exact).refresh(engine="polars", route="auto")
except RouteError as e:
    print(e)
# refused on polars: sums (stored as sums_exact): a rerun must give the same result: agg.fsum's sum_order: ... a rerun must reproduce exact doubles: pass reproducible=...

totals = readings.pipe(sums).write(
    DeltaSink("sums", reproducible=sv.equivalent(floats=sv.within(abs=1e-6)))
)
totals.refresh(engine="polars", route="auto")
readings.apply(Changes(inserts=[(1, 0.5)]))
print(totals.refresh(engine="polars", route="auto"))
# sums:
#   route on polars: ...
# ...
#   view sums: readings@v1
#   wrote sums from readings@v1: merge v2, 1 row(s) written, 1 deleted
```

The second refresh adds the insert to its group's exact sum and rounds it
once, without reading the input
([`LinearAgg.fsum_no_drift`](../SubstraitLean/IncrementalFloat.lean)). A result
not determined up to row order, such as a `LIMIT` over ties, is refused by
every sink.

## 7. A plan checked under DuckDB's profile

`semantics="duckdb"` checks a plan under what DuckDB does, from its
[characterization](https://alexandernenninger.github.io/substrait-lean/ledgers/duckdb-facts.html). A route to Polars then takes the proof
across only where Polars's choices are within DuckDB's on every option the
plan reads (the checker's transfer check, `Rel.transfer_of_transferB`), and
names the options and facts where they are not:

```python
t = con.table("orders")
filtered = sv.verify(t.filter(t.total > 50).select("id", "total"), semantics="duckdb")
filtered.run(con, "polars", route="auto")
print(filtered.routes["polars"])
# exact; transfer: verified under semantics="duckdb"; polars's choices are within its choices on every option the plan reads

divided = sv.verify(
    t.select(t.id, unit=t.total // t.qty),
    requires={"orders": [_.qty != 0, _.total >= 0]},
    semantics="duckdb",
)
try:
    divided.run(con, "polars", route="transfer")
except RouteError as e:
    print(e)
# refused on polars: the transfer check fails on int.arith's overflow: duckdb gives ERROR, polars gives SILENT ...
divided.run(con, "polars", route="auto")
print(divided.routes["polars"])
# exact; recheck: proved again under semantics="polars"
```

The transfer check fails on the division's options, so `route="auto"` goes on to the
re-check: the checker proves the plan again under `semantics="polars"`, and
Polars runs it with the shim of example 4. [engine-profiles.md](engine-profiles.md) describes the
profiles, and `substrait-check --dependencies` lists a plan's options with
each profile's choice.

## 8. Substrait's own semantics

`semantics="substrait"` checks a plan under Substrait's semantics as its
extension YAMLs state them, open wherever they say nothing. The reference's
proof carries over where Substrait allows nothing more than the reference
at every option the plan meets; `str(report)` names the options where it
allows more:

```python
print(sv.verify(t.select("id", "total"), semantics="substrait").proved)
# True
plus_one = sv.verify(
    t.select(t.id, more=t.total + 1),
    requires={"orders": [_.total.between(0, 10**6)]},
    semantics="substrait",
)
print(plus_one.proved)
# False
print(str(plus_one).splitlines()[3])
#   not proved under semantics="substrait": int.arith's overflow allows ERROR, SILENT, SATURATE, the reference only ERROR
```

Substrait leaves integer overflow to the consumer (raise, wrap or
saturate), and the check compares the profiles option by option, so the
proof does not carry over even where the bound on `total` rules overflow
out. `substrait-check --profile-diff` lists every option
where the two profiles differ, published in
[core-semantics.md](core-semantics.md#the-substrait-profile). Gaps like this
one, which Substrait could close with an option, are on the
[upstream ledger](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html) as `ST` entries.

## 9. A plan checked under Polars's profile

`semantics="polars"` checks a plan under what Polars does: its integer `//`
and `%` floor, so `-7 % 2` is `1`. The plan states `division_type: FLOOR`,
which the checker reads as Polars's remainder (`Profile.polars_imod` in
[PolarsProfile.lean](../SubstraitLean/PolarsProfile.lean)), and Polars runs
its own `%` with no shim (route `native`). A postcondition that holds only
of the floored remainder is proved:

```python
con.put("signed", pa.table({"x": [-7, -2, 3, 8]}))
s = con.table("signed")
notnull = {"signed": [_.x.notnull()]}
parity = sv.verify(
    s.select(s.x, odd=s.x % 2), requires=notnull, ensures=[_.odd >= 0], semantics="polars"
)
print(parity.proved)
# True
print(parity.run(con, "polars", route="auto").column("odd").to_pylist())
# [1, 0, 1, 0]
print(parity.routes["polars"])
# exact...; native: verified under semantics="polars"
print(sv.verify(s.select(s.x, odd=s.x % 2), requires=notnull, ensures=[_.odd >= 0]).proved)
# False
try:
    parity.run(con, "duckdb", route="auto")
except RouteError as e:
    print(e)
# refused on duckdb: integer // and % with division_type FLOOR (Polars's, semantics='polars') run on polars only; duckdb truncates: verify with semantics='reference' to run on duckdb
```

Under the reference `-7 % 2` is `-1`, as on DuckDB, so the postcondition
does not hold there, and DuckDB refuses the plan. A zero divisor and integer
overflow raise under `Profile.polars` as under the reference, so `verify`
infers the same preconditions. [engine-profiles.md](engine-profiles.md#polars-as-a-profile)
says which choices the profile takes from Polars.

## 10. A verified plan for any Substrait consumer

`report.to_substrait()` returns the plan the checker verified, written for
any conforming consumer of Substrait 0.106: each call names its YAML's URN,
its compound name and its output type, and each option the proof depends on
is pinned at the reference's behaviour. The contract travels with it, and
`sv.Report.from_substrait` proves it again:

```python
from sverify.errors import ExportError

unit = sv.verify(
    t.select(t.id, unit=t.total // t.qty),
    requires={"orders": [_.qty > 0, _.total >= 0]},
    ensures=[_.unit >= 0],
)
exported = unit.to_substrait()  # protobuf JSON; "binary" for bytes
manifest = unit.substrait_contract()["manifest"]
print([(p["group"], p["option"], p["values"]) for p in manifest["pinned"]])
# [('int.arith', 'overflow', ['ERROR']), ('int.div', 'overflow', ['ERROR']), ('int.div', 'on_division_by_zero', ['ERROR']), ('int.div', 'on_domain_error', ['ERROR', 'NULL'])]
print(sv.Report.from_substrait(exported).proved)
# True
```

Where Substrait has no option for a choice the proof uses, a spec gap,
`shims` decides. A standard deviation of one value is NULL in the
reference, and Substrait leaves it open
([ST-3](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html)):

```python
spread = sv.verify(t.group_by("qty").aggregate(spread=t.total.std()))
print([s["shim"] for s in spread.substrait_contract()["manifest"]["shims"]])
# ['variance and std_dev: if count(x) < 2 (1 for POPULATION) then NULL']
print([a["text"] for a in spread.substrait_contract(shims="annotate")["manifest"]["assumptions"]])
# ["the consumer gives NULL at agg.var's stat_degenerate"]
try:
    spread.to_substrait(shims="refuse")
except ExportError as e:
    print(e)
# refused for Substrait: agg.var's stat_degenerate: Substrait allows NULL, NAN, ERROR where the proof uses NULL (ST-3, upstream/bugs/ST-3.json); export with shims='apply' or 'annotate'
```

`"apply"`, the default, rewrites the plan so that every conforming consumer
gives the reference's result; `"annotate"` leaves the plan as written and
ships the choice as an assumption; `"refuse"` refuses. The
[guide](guide.md#exporting-to-substrait) lists what the export carries.

## Where next

The [guide](guide.md) covers each feature in depth, the
[tour](../README.md#the-tour) works through three complete jobs, and the
[ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/) list what Sverify knows about each engine and the
upstream bugs it works around.
