### A bounded double `SUM` runs without its overflow checks

A double `SUM` or `AVG` whose column is bounded, over an input with a `max_rows` cap, can't overflow to `±∞` in any order an engine adds it (#1787). A verified run on DuckDB now writes it as a plain sum, without the second pass that checked for `±∞`. As with the other run-time checks, this happens only on a run that checked the preconditions on its tables. Sverify's bound for engine sums now also reads `-0.0` as zero (D35, amended).
