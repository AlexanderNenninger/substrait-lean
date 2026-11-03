### The reference is a relation: an engine returns an allowed result or raises

`docs/reference-semantics.md` now defines correctness through the set of
results the reference allows for each input (`Rel.Allowed`,
`SubstraitLean/Allowed.lean`). The set holds more than one result where the
reference leaves a choice to the engine: the order of rows and of ties,
`FIRST`/`LAST` and `distinct(on=)` without an order, the order in which a double
`SUM` or `AVG` adds (#85), and the statistical aggregates. `Rel.eval` is one
allowed result (`Rel.eval_allowed`); a plan without choices allows only its
rows (`Rel.allowed_perm_eval`); rewrites are refinements (`Rel.Refines`); and
the DuckDB shim and guard elimination return allowed results. The page also
lists where the reference overrides Substrait (one zero, one NaN, the size
hypothesis), states principle 3 as "Every engine can follow it with reasonable
effort", and notes that `fp32` arithmetic is refused until #417.
