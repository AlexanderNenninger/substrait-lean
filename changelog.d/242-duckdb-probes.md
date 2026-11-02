### DuckDB's functions probed for the options they implement

`substrait-check --outcomes` evaluates each row of a projection over `VALUES`
under the reference and prints the value or the error raised. The maintainer
tool `python -m sverify_dev.probe` uses it to run DuckDB's arithmetic and
elementary functions on edge cases under every combination of
`error_on_division_by_zero` and `ieee_floating_point_ops`, and to keep the
Substrait options whose outcomes match
(`characterization/duckdb/probes.json`, FACTS R15). It corrected two facts:
double division by zero is IEEE under DuckDB's defaults, and `MIN % -1`
raises (#242).
