### Observations in postconditions, and routes to engines (#444)

- `sv.equivalent(rows=…, floats=sv.within(abs=…, rel=…, ulps=…), zeros=…, timestamps=…, strings=…, decimals=…, errors=…)`
  in `ensures` names what the result's consumer observes: rows as a multiset
  (the default) or a sequence, doubles exact or within a tolerance, one zero
  and one NaN, timestamps to a precision, strings up to NFC. Observations are
  ordered by refinement, component by component (`Observation.refines`), and
  `Observation.equal` compares two results up to one. Each other postcondition
  that depends on what the observation ignores says so
  (`CheckedCondition.ignores`), and the report is then not proved.
  Without `equivalent`, nothing changes.
- `Report.run(con, engine, route="auto")` chooses how the proof reaches the
  engine: natively where the plan was verified under the engine's profile,
  through the reference's translation, by the option-wise transfer check,
  or by a re-check under the engine's profile, and refuses the plan with the
  reason otherwise (`sverify.routes`, decision D13 of
  [core-semantics.md](docs/core-semantics.md)). The route goes into
  `Report.routes`; `route="native"` and the others take that route or refuse.
  `deterministic=True` refuses a plan whose result is not determined up to
  row order (D10). Each route carries the plan's class on the engine
  (`Route.cls`: refines, refines up to an observation, approx, shim or
  refused), and an engine that agrees with the reference only up to an
  observation the postcondition does not state is refused, or shimmed. A
  function the engine does not run refuses the plan with the reason. Before
  it runs, a routed run checks the preconditions, the inferred bounds and
  the assumed `SUM`s on the data (`Report.check_inputs`) and refuses a
  batch that breaks one, naming it (`PreconditionError`). Without `route`,
  `run` behaves as before.
- `semantics="polars"` checks an Ibis transformation under Polars's
  profile, once the checker has one.
- `sv.equivalent(elements="multiset")` ignores the order of a list's
  elements. A postcondition the checker does not prove, and that reads the
  value of `first` or `last` without an order or a list's element order,
  says it depends on that open choice.
- Engine profiles record the versions their facts were probed at (DuckDB
  2.0.0, Polars 2.1.0). A routed run on another version warns
  (`EngineVersionWarning`), and one on another major version is refused
  (`EngineVersionError`) until the probes are re-run (D14).
