### Rewrites refine up to an observation

`Rel.Refines` was inclusion up to the order of rows, which let an unsorted
plan refine its `ORDER BY` twin. Refinement now names its observation,
`Rel.RefinesUpTo` (#897): `Rel.Refines` is exact and keeps the order an
`ORDER BY` fixes, and `Rel.RefinesBag` is the old relation. `optimize`'s
rewrites refine the plan up to the order of rows (`Rel.optimize_refines`).
