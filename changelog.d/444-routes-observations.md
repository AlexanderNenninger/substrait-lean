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
  row order (D10). Without `route`, `run` behaves as before.
- Engine profiles record the versions their facts were probed at (DuckDB
  2.0.0, Polars 2.1.0). A routed run on another version warns
  (`EngineVersionWarning`), and one on another major version is refused
  (`EngineVersionError`) until the probes are re-run (D14).
