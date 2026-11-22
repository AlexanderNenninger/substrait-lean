# `Rel.AllowedP_mono`

A profile whose choices are within another's allows no more results.

Lean: `Substrait.Rel.AllowedP_mono`, in
[`core/Sverify/Core/AllowedP.lean`](../../core/Sverify/Core/AllowedP.lean).
Layer: `AllowedP`, the results a profile allows, option by option. Axioms: not yet listed;
`#print axioms Substrait.Rel.AllowedP_mono` is the check ([trusted-base.md](../trusted-base.md)).

## What it says

A profile narrows the core's options, each to the behaviours it allows. If
profile `t` allows, at every option, only behaviours that profile `u` allows
too, then every result `t` allows for a plan is a result `u` allows. A proof
under `u` then covers an engine whose profile is `t`. This is the step under
the `transfer` route: Sverify proves a plan under one profile, checks at
each option the plan reads that the engine's choices are within it, and runs
the plan on the engine.

## The statement, line by line

```lean
theorem Rel.AllowedP_mono {t u : ProfileTable} (h : t.Le u) {cat : Catalog} {r : Rel}
    {out : Relation} : r.AllowedP t cat out → r.AllowedP u cat out
```

- `t`, `u`, `h`: two profile tables, and the assumption `ProfileTable.Le`
  that at every option each of `t`'s choices is among `u`'s.
- `cat`, `r`, `out`: the data, a plan, and a relation.
- The premise: `out` is a result `t` allows for `r`.
- The conclusion: `out` is a result `u` allows for `r`.

## What it rules out

- A transfer across profiles that differ at an option the plan reads: the
  premise `h` fails there, and the transfer check names the option and the
  facts that record the difference.

## What it does not cover

- Which choices an engine makes. The profile's table states them from the
  engine's facts ([`engines/*/facts/`](../../engines/)); that the engine
  matches its facts rests on tests ([trusted-base.md](../trusted-base.md)).
- Whether a plan reads an option. The checker's transfer check
  (`Rel.AllowedP_transfer`) computes the options a plan reads and applies this
  theorem at them.

## Its side conditions

The hypothesis that `t`'s choices are within `u`'s is decided option by
option by the checker's transfer check, from the two profiles' tables.

## Example

A plan proved under DuckDB's profile reads no option on which DuckDB and Polars
differ when it only selects columns, so the proof carries over to Polars and
to Spark:

```python
import ibis
import sverify as sv
from sverify import routes

orders = ibis.table({"id": "int64", "amount": "float64"}, name="orders")
report = sv.verify(orders.select("id", "amount"), semantics="duckdb")
for engine in ("polars", "spark"):
    route = routes.choose(report, engine)
    print(engine, route.kind, route.cls)
# polars transfer exact
# spark transfer exact
```

A comparison of doubles reads `zero_sign`, where DuckDB has one zero and
Polars IEEE's two. DuckDB's choices are not within Polars's there, so the
transfer is refused:

```python
filtered = sv.verify(orders.filter(orders.amount > 50).select("id", "amount"), semantics="duckdb")
print(routes.choose(filtered, "polars").refused)
# True
```
