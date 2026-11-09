# Verifying: the two paths

Will a plan give the same answer on every engine? Sverify asks that in one
of two ways. Under the reference, the default, it proves the plan once and
carries the proof to each engine through a proved translation. Under an
engine's own profile, it proves what that one engine computes. The
`semantics` argument of `verify` picks the path, and the report says which
one a run took.

## Under the reference

`sv.verify(plan)`, `@sv.transform(...)` and `semantics="reference"` prove
the plan under the reference profile
([The core and the profiles](core-and-profiles.md)):

- The proof is strict. Where engines disagree on an edge case (overflow,
  division by zero, a NaN or `±∞` an operation creates), the reference
  raises, and the plan is proved only where its preconditions rule that
  case out ([Errors](reference-semantics.md#errors)).
- One proof carries to every engine. A run on DuckDB, Polars or Spark takes
  the route `translated`: sverify writes the plan for the engine with every
  choice spelled out, and a shim wherever the engine's value differs from
  the reference's (a truncating division, a NULL placement). Lean proves
  the translation to DuckDB correct, and the Polars and Spark shims sound
  ([the proofs](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proofs.md);
  what they rest on: [trusted-base.md](trusted-base.md)).
- Where the reference leaves a choice open (the order of tied rows, the
  order of a sum of doubles), each engine's pick is one the proof covers,
  or within the plan's bound on doubles.

Use this path for a plan that must run on more than one engine, or that
may move between engines later.

## Under an engine

`semantics="duckdb"`, `"polars"` or `"spark"` proves the plan under that
engine's profile, and `semantics="substrait"` under Substrait's:

- The proof is about what that engine computes. A plan whose meaning
  depends on the engine can be proved here and not under the reference:
  under `semantics="polars"` integer `%` floors, so `-7 % 2` is `1` and
  `_.odd >= 0` holds, which the reference does not prove.
- The run takes the route `native`: the engine runs its own operations, with
  no shim.
- The proof holds for that engine. A run on another engine goes through
  `transfer`, where the other engine's choices are within this profile's
  at every option the plan reads, which the checker decides and Lean
  proves sufficient, or
  `recheck`, which proves the plan again under the other engine's profile.
  Where neither applies, the run is refused.
- `semantics="substrait"` proves a plan under Substrait's extension YAMLs,
  open wherever they say nothing; the report names the options where
  Substrait allows more than the reference.

Spark's profile evaluates as the reference does, so under
`semantics="spark"` the proof is the reference's; the route to Spark is
`native`.

`sv.sql` is DuckDB-dialect SQL, verified under the reference like
everything else; `semantics="duckdb"` on a `sv.sql` reads that node as
DuckDB computes it.

## Choosing a path

| You want | `semantics=` | Route on the engine |
|---|---|---|
| One proof for every engine | `"reference"` (the default) | `translated` |
| What DuckDB, Polars or Spark computes, on that engine | `"duckdb"`, `"polars"`, `"spark"` | `native` |
| The same plan on a second engine | either | `transfer` or `recheck`, else refused |
| What any Substrait consumer may compute | `"substrait"` | no engine route: the plan is certified against the spec, exported like any plan |

`report.run(con, engine)` and `node.refresh(engine=...)` choose the route
(`route="auto"`, the default) and run the plan only if one applies.
`route="translated"`, `"native"`, `"transfer"` or `"recheck"` asks for one
and says why it fails.

## What the report says

- `report.semantics` names the profile the proof is under.
- `report.routes[engine]` records the route a run took, with its class:
  `exact` (every result the engine gives is one the proof covers),
  `observed` (equal to one up to the report's observation, such as doubles
  within the plan's bound), `shim` (either, after a proved fix) or
  `refused`.
- `route.evidence` says whether each step rests on a Lean proof (`proved`)
  or on tests and probes (`tested`); `route.theorems` names the proofs and
  `route.facts` the engine facts behind them.
- A refusal raises `sverify.errors.RouteError` and names its reason: the
  options where the engine's choices differ, with the facts that record
  them. A plan verified under one engine and run on another says which
  `semantics` would carry over:
  `verify with semantics='reference' to run on duckdb`.

[How to, Routes, classes and profiles](tasks.md#routes-classes-and-profiles)
has the details and what to do about a refusal;
[reference-semantics.md](reference-semantics.md) states what each option
does under the reference.

