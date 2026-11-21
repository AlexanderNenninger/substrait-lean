# `Rel.duckdb_sound`

A plan Sverify has proved returns the reference's rows when it runs on DuckDB as the printer writes it, under DuckDB's default settings.

Lean: `Substrait.Rel.duckdb_sound`, in
[`engines/duckdb/Sverify/DuckDB/Profile.lean`](../../engines/duckdb/Sverify/DuckDB/Profile.lean).
Layer: `eval`, the reference's result for the plan. Axioms: not yet listed;
`#print axioms Substrait.Rel.duckdb_sound` is the check ([trusted-base.md](../trusted-base.md)).

## What it says

DuckDB is the engine Sverify runs by default. This theorem says that for a
proved plan, DuckDB's functions as the SQL printer writes them (`MIN % -1`
and `<<` written out, decimals as the profile states them) give the
reference's rows, under DuckDB's IEEE operations. It carries a size
hypothesis, and it trusts that DuckDB's aggregates are Lean's: a double `SUM`
or `AVG` is within the reference's error bound of the model, and
[`float-bounds`](../float-bounds.md) proves the bound.

## The statement, line by line

```lean
theorem Rel.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat (Profile.duckdbWritten s).impl = r.eval cat
```

- `cat`, `hcat`: the data, a catalog of tables, and the assumption that it
  is well formed.
- `A`, `hA`: what the checker knows of the values of each table's columns,
  as a set per column, and the assumption that every row of the data lies in
  those sets.
- `F`, `hF`: the facts between columns or about a whole row that follow from
  the preconditions, and the assumption that every row satisfies them.
- `T`, `hT`: what the analysis assumes about the order of tied window rows
  (the keys that close the ties).
- `r`, `hwf`: the plan, and the assumption that it is well formed.
- `hsmall`: the size hypothesis (`Rel.Small`): a window reads fewer than
  2⁶² rows and an aggregate fewer than 2⁶³. An engine's memory guarantees it.
- `hs`: the plan keeps all rows where it must: no left join's right side
  loses a filter (`Rel.looseSub`).
- `hm`: the checker's list of issues the plan may raise (`Rel.mayIssues`)
  holds nothing but issues assumed on the data, which the run checks first.
- `s`, `hieee`: DuckDB's settings, and the assumption that its operations on doubles are IEEE's, which is the default.
- The conclusion: evaluating the plan with DuckDB's functions as the printer writes them gives the same rows as the reference's `Rel.eval`.

## What it rules out

- A DuckDB result that differs from the reference's on data that meets the
  preconditions, for a plan Sverify proved.
- A plan that may raise unchecked: `hm` allows only the issues the run
  checks first.

## What it does not cover

- That the profile is DuckDB's. `Profile.duckdb` is probed, and the facts
  are in [`engines/duckdb/facts/`](../../engines/duckdb/facts/); that the
  SQL printer is faithful, and that DuckDB's aggregates are Lean's, are
  trusted ([trusted-base.md](../trusted-base.md)).
- The exact digits of a double `SUM` or `AVG`: they are within a bound of the
  model, not equal to it.
- Settings other than the defaults. `hieee` and the settings the run checks
  decide where it holds ([how-to-engines-and-sql.md](../how-to-engines-and-sql.md)).

## Its side conditions

`hcat` is a fact about the data, which the run's schema check covers.
`hwf`, `hsmall`, `hs` and `hm` are the checker's own computations on the
plan. `hA`, `hF` and `hT` are the contract's schemas, preconditions and the
tie keys, checked on the data on each run.

## Example

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import routes

lines = ibis.table({"id": "int64", "n": "int64", "total": "int64"}, name="lines")
per_line = lines.select(lines.id, per=lines.total // lines.n)
report = sv.verify(
    per_line,
    requires={"lines": [_.n != 0, _.total > -1000, _.total < 1000]},
)
print(report.verdict)
# proved
```

Verified under DuckDB's own profile, the route runs the plan natively:

```python
duck = sv.verify(
    per_line,
    requires={"lines": [_.n != 0, _.total > -1000, _.total < 1000]},
    semantics="duckdb",
)
route = routes.choose(duck, "duckdb")
print(route.kind, route.cls)
# native exact
con = sv.connect()
con.put("lines", pa.table({"id": [1, 2], "n": [4, -4], "total": [100, 250]}))
print(duck.run(con, "duckdb").to_pylist())
# [{'id': 1, 'per': 25}, {'id': 2, 'per': -63}]
```

With no `n != 0` the report is `unproved` and nothing runs:

```python
unguarded = sv.verify(per_line, requires={"lines": [_.total > -1000, _.total < 1000]}, on_inferred="off", semantics="duckdb")
print(unguarded.verdict)
# unproved
```
