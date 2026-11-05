### Breaking: fewer knobs for "not proved", one name per concept (#690, #695)

From the API critique (#686). Every renamed or removed keyword below still
works in 0.6 with a `DeprecationWarning` that names its replacement, and goes
in 0.7. The names deprecated before 0.5 are gone.

Not proved (#690):

- `on_inferred="off"` replaces `infer=False` on `sv.verify` and
  `@sv.transform`: nothing is inferred or assumed, so a `SUM` that may leave
  64 bits, or a double operation that may overflow to ±inf, is an error.
  `on_inferred` takes `"error"` (the default), `"warn"`, `"silent"` and
  `"off"`. `infer=` warns.
- `@sv.transform(on_unproved="warn")` now lets the node's refreshes run
  unverified, each with an `UnverifiedRunWarning`, where it used to need
  `refresh(unverified=True)` as well.
- A run or refresh of a plan that is not proved raises
  `sverify.errors.UnverifiedRunError`, a `VerificationError`, so
  `except VerificationError` catches every "not proved". It is also a
  `RouteError`, so `except RouteError` still catches it. A refresh's message
  names `refresh(unverified=True)`.
- An assumed `SUM` reads `fits 64 bits in every group (checked at run time:
  the job raises if it does not; on_inferred="off" makes it an error)`, and
  an assumed finite double operation `stays finite on finite inputs (checked
  at run time …)`. Neither says "inferred" any more.
- Removed: `@sv.transform(strict=...)` (deprecated since 0.4),
  `sv.references(col, table, other)` (write `to=`), and
  `sverify.testing.Connection.datafusion` (deprecated since 0.4).
- `node.plan` is `node.internal_plan`: sverify's own form of the plan, with
  its private extension URNs. `Report.to_substrait()` is the portable one.
  `node.plan` warns.

Names (#695):

- The route `"reference"` is `"translated"`: a plan verified under
  `semantics="reference"` runs through the translation to the engine.
  `route="reference"` warns and takes `"translated"`; `Route.kind` is
  `"translated"`.
- A route prints its class first: `shim, proved (translated): verified under
  the reference; …`.
- Printed output says `semantics="duckdb"` where it said `Profile.duckdb`.
- `@sv.transform(engine=)` is `check_engine=`: where checks on data run.
  `refresh(engine=)` and `run(con, engine)` keep `engine` for where the plan
  runs.
- `Report.run(check_inputs=)` is `check_requires=`, as on `@sv.transform`.
- `sverify.engines.to_sql(tie_free=)` is `deterministic=`, as on
  `Report.run`; `run_spark` too. `to_sql` also takes the plan as a JSON
  string, so `to_sql(node.internal_plan, SNOWFLAKE)` needs no `json.loads`.
- `Node.refresh(engine=None)` and `Group.refresh` default to `None`, DuckDB,
  as `Report.run(engine=None)` defaults to its connection's engine.
- `sv.verify`'s first parameter is `query`, positional-only.
- `report.equivalence` is the equivalence the result is proved up to, by the
  name of `sv.equivalent`; `report.observation` stays.
- `report.needed_text` is a property; `Report.needs_text()` and
  `needs_lines()` warn.
- A refresh report of a stored node is headed by the transform and the sink,
  `daily_revenue → daily:`, where the names differ.
- `summary()` reads `changes from orders v1→v2 (change feed)` where it read
  `orders@v1→v2, Δ trusted (change feed)`.
