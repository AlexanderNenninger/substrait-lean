### `Report.run` checks the preconditions first (#604)

`report.run(con, engine)` checks the report's preconditions on the tables
before the run, with or without `route=`: `requires` and the bounds `verify`
inferred. A batch that breaks one is refused with a `PreconditionError`
that names it, and nothing runs, as the reference's first guarantee promises.
Before, a plan proved under an inferred precondition (such as `x != 0` for
`filter((x != 0) & (10 // x > 1))`) ran on the batch and raised on the engine.
`check_inputs=False` skips the check for a caller that has made it already,
and gives up the guarantee on data that breaks a precondition.
`Node.refresh` already checked them on each batch.
