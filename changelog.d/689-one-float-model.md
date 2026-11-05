### One model for doubles; every route has a class

Stating no observation, `sv.equivalent(floats="plan")` and the plan's own
bound are one observation (#689). `report.observation` prints it with the
bound, `equivalent(floats=plan, ≤ 2.2e-10)`, and `report.observation.equal`
compares doubles within it. A postcondition that reads a double keeps its
exact value under a stated `floats="plan"` as it does without one.

`verify` checks a stated tolerance (`abs`, `rel` or `ulps`) and
`floats="exact"` against the plan's bound on each engine
(`report.floats_on`). The report's `observes:` line shows the plan's bound
beside the tolerance and the engines that meet it; where none does, the plan
is not proved and the line gives the reason and a tolerance that would do.
A run used to refuse a too-tight `rel` or `ulps` only at run time.

A route prints `rows='multiset'` for a plan with no `ORDER BY`, and the
Substrait manifest's `class` is `observed` for a plan with a bound on its
doubles, as its routes are. `Observation`'s repr is its `equivalent(...)`
form.

Every verified run records one of the four classes in `Route.cls`: a plan
whose options have no row in the engine's tables, such as a `LAG` over a
unique key, is `exact` on tested evidence (#696).
