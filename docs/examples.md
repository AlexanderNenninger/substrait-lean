# Examples

Nine short examples, each a step up from the one before: a contract proved
and run, SQL, the preconditions Sverify infers, routes to Polars, tolerances
for doubles, reproducible sinks, engine profiles, Substrait's own semantics,
and a plan checked under Polars's. The inputs are a few rows in memory. Every block runs as written,
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
print(unit_prices.last_report)
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
`on_inferred="warn"` or `"silent"` assumes the inferred preconditions and
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
# reference: verified under the reference; the translation to polars is ... [shim, proved]
```

Polars's integer division floors, and the reference's truncates, so the
translation writes a shim, proved in Lean (`SubstraitLean/PolarsShims.lean`).
The [realizability table](realizability.md) lists every option's class on
each engine.

## 5. Doubles within a tolerance

DuckDB and Polars add doubles in different orders, so a mean's last bits may
differ. `sv.equivalent(floats=sv.within(...))` in `ensures` states what the
result's consumer observes, and the route checks that the engine's sum is
within the plan's proved bound
([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)).

```python
con.put("readings", pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}))
r = con.table("readings")
means = sv.verify(
    r.group_by("k").aggregate(mean_x=r.x.mean()),
    requires={"readings": [_.x.between(-1000, 1000), sv.max_rows(1000)]},
    ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
)
on_duckdb = means.run(con, "duckdb", route="auto")
on_polars = means.run(con, "polars", route="auto")
print(means.observation.equal(on_duckdb, on_polars))
# True
```

The route to Polars is `observed`: equal under the observation, here a
tolerance of `1e-6` on doubles.

Without the observation, the run accepts doubles within the plan's proved
bound, except in a column a postcondition reads, which keeps its exact value.

## 6. A reproducible sink, kept up to date

A sink commits each epoch once, so a rerun must give the same result. The
sink says what "the same" means (`reproducible=`, D20), and a refresh is
refused where the engine's run-to-run variation does not refine it. Polars's
streaming `SUM` of doubles may add in another order each run, so a sink that
asks for exact bits, `reproducible=sv.equivalent()`, is refused there, and
one that accepts the plan's float bound is not:

```python
from sverify.io import DeltaSink
from sverify.routes import RouteError

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
readings.apply(sv.Changes(inserts=[(1, 0.5)]))
print(totals.refresh(engine="polars", route="auto"))
# sums:
#   route on polars: reference: ...
# ...
#   view sums: 1 touched group(s) recomputed
#   wrote sums from readings@v1: merge v2, 1 row(s) written, 1 deleted
```

The second refresh recomputes only the group the insert touched. A result
not determined up to row order, such as a `LIMIT` over ties, is refused by
every sink.

## 7. A plan checked under DuckDB's profile

`semantics="duckdb"` checks a plan under what DuckDB does, from its
[characterization](https://alexandernenninger.github.io/substrait-lean/ledgers/duckdb-facts.html). A route to Polars then takes the proof
across only where Polars's choices are within DuckDB's on every option the
proof depends on, and names the options and facts where they are not:

```python
t = con.table("orders")
filtered = sv.verify(t.filter(t.total > 50).select("id", "total"), semantics="duckdb")
filtered.run(con, "polars", route="auto")
print(filtered.routes["polars"])
# transfer: verified under Profile.duckdb; polars's choices are within its choices on every option the proof depends on ...

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
# recheck: proved again under Profile.polars [exact]
```

The transfer check fails on the division's options, so `route="auto"` goes on to the
re-check: the checker proves the plan again under `Profile.polars`, and
Polars runs it with the shim of example 4. [engine-profiles.md](engine-profiles.md) describes the
profiles, and `substrait-check --dependencies` lists a plan's options with
each profile's choice.

## 8. Substrait's own semantics

`semantics="substrait"` checks a plan under Substrait's semantics as its
extension YAMLs state them, open wherever they say nothing. The reference's
proof carries over where Substrait allows nothing more than the reference
at every option the plan meets; `report.transfer` names the options where it
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
print([(d["group"], d["option"], d["substrait"]) for d in plus_one.transfer])
# [('int.arith', 'overflow', ['ERROR', 'SILENT', 'SATURATE'])]
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
# native: verified under Profile.polars [exact]
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
infers the same preconditions. [core-semantics.md](core-semantics.md#polars-as-a-profile)
says which choices the profile takes from Polars.

## Where next

The [guide](guide.md) covers each feature in depth, the
[tour](../README.md#the-tour) works through three complete jobs, and the
[ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/) list what Sverify knows about each engine and the
upstream bugs it works around.
