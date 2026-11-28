# What sverify proves

In sverify you write a data transformation as usual, in
[Ibis](https://ibis-project.org) or SQL, and state what it assumes about its
inputs (`requires`) and what it guarantees about its output (`ensures`). A
checker written in [Lean](https://lean-lang.org) proves the guarantees for
every possible input, or says why it can't ([what is proved](proved-theorems.md)). Then:

* Contracts are proved before the job runs. `not_null`, `unique`, ranges and
  relations between columns hold on every input that meets the
  preconditions, and division by zero, overflow and bad casts are ruled out
  before the job runs. The preconditions you state, and those Sverify
  infers, are checked on each batch before the run, or proved from Delta
  and Iceberg metadata, and a batch that breaks one is refused before
  anything runs. The [runtime-error theorems](proved-theorems.md#runtime-errors) list what is ruled out.
* A route takes the proof to the engine. `route="auto"` runs the plan on
  DuckDB, Polars or Spark natively, through the reference's translation, or by a check that the engine's choices are within the proof's, and names
  the plan's class there: exact, equal under lenses the
  postcondition states (a float tolerance is one), or exact or observed
  after a shim. The proofs speak of a model of each engine's scalar
  functions. DuckDB's lowering and the shims are proved against that model;
  the writers' SQL and the Polars translation are tested against the lowered
  plan ([what is trusted](trusted-base.md)). Where no route
  applies, the plan is refused with the reason
  ([routes and classes](how-to-engines-and-sql.md#routes-classes-and-profiles)). DuckDB,
  Polars and Spark are characterized fact by fact, with the evidence for each
  ([the ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)).
* Postconditions say what the result's consumer observes. By default,
  doubles within the plan's bound (`floats="plan"`, which the report
  prints; [`float-bounds/`](float-bounds.md)
  proves the bounds over the reals, and [what is trusted](trusted-base.md) lists the
  step from them to the report's bound and how far the models are tested); `sv.equivalent(floats=sv.within(abs=1e-6))` states a tolerance,
  which `verify` checks against that bound, and also rows as a sequence or
  a multiset, one zero. A sink states what a
  rerun must reproduce (`reproducible=`), and a refresh whose engine can't
  promise it is refused.
* Results are kept up to date from the changes, by delta plans proved
  equal to a full recompute ([the theorem](proved-theorems.md#incremental-view-maintenance)), read from Delta's Change Data Feed or Iceberg's
  appends, and written to sinks exactly once, with the contract attached.

## Reference semantics and engines

Sverify checks every plan against a reference semantics, written in Lean,
whose four principles and choices are in
[reference-semantics.md](reference-semantics.md#principles).
The reference raises where engines disagree on an answer, so a proved plan
runs alike on each: an operation on finite doubles that overflows to `±∞`,
`power(-inf, 0.5)`, a `MEDIAN` between `-inf` and `+inf`, a constant
subexpression that raises. `AND` and `OR` evaluate both operands, as DuckDB
and Polars do. A plan proved under the reference creates no NaN and no
`±∞` its inputs did not hold. `semantics="duckdb"`, `"polars"` and
`"spark"` check a plan under what that engine does, and
`semantics="substrait"` under Substrait's extension YAMLs, open wherever
they say nothing
([the Substrait profile](core-semantics.md#the-substrait-profile)).

Sverify runs plans on DuckDB, Polars and Spark, and writes DuckDB, Spark
and Snowflake SQL. [Engines](stability.md#engines)
says which are in the 1.x promise, with their profiles and translations.

Polars refuses what only DuckDB runs so far, with a message that links
[the issue that tracks it](https://github.com/AlexanderNenninger/substrait-lean/issues/2540): the functions
that [`SUPPORT` and `WINDOW_SUPPORT`](../python/src/sverify/_support.py)
list without `polars` (`md5`, `sha256`, `first`, `last`,
`string_agg`, `median`, the quantiles, `mode`, `arg_min`, `arg_max`, the covariances,
`corr`, and variances over a window), the black boxes, and `MIN` and `MAX` of doubles.
