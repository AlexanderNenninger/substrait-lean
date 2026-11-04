### `Report.run` refuses an overflow to `±∞` before the run (#575)

`report.run(con, engine)` now checks the assumption that no operation on
finite doubles gives `±∞` on the data before the run, as it already did for
an assumed `SUM`: it runs the proved DuckDB translation first and refuses the
batch with a `PreconditionError` that names the operation, so nothing runs on
the engine. A refresh of several nodes stays atomic per node: the node whose
batch overflows writes nothing, while the stored nodes upstream of it, whose
results it reads, keep the epoch they committed.
