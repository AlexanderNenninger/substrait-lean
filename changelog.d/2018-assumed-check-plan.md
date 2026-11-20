### Assumed issues are checked by a plan whose result is the verdict

A report's assumed issues (an integer `SUM` that must fit 64 bits, an
operation on finite doubles that must not give `±∞`) were checked by guards
inside the plan an engine runs. DuckDB and Spark skip an expression the result
does not need: a column nothing reads, one under a filter or a limit pushed
below it, one joined to an empty input, one under a `count(*)`. There a run
returned rows where the reference raises
([#2018](https://github.com/AlexanderNenninger/substrait-lean/issues/2018)).
`Report.run` now first runs a check plan the checker writes from the plan as
written (`assumed_check` in the report's JSON), on the run's own engine: one
row, one column per place where an issue may occur, aggregates every engine
computes. A batch on which an issue occurs is refused with a
`PreconditionError` before the run. The guards inside the plan stay. The
DuckDB run of the whole plan before another engine's run is gone, and so is
`ProfilePlugin.checks_assumed` and `check_inputs`'s `assumed_checked`.
