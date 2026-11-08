### CORR's missing bound says what would give one

`Report.epsilon` gives a `CORR` column no bound, as before; its reason now
states D30's decision: a bound needs a lower bound on both sides'
variances, stated by the user and checked by the run, and without one only
`[-1, 1]` holds and a tolerance on it is tested (#918). Polars's `VAR_*`
row cites a fuzzed bound of `1.03 · n·u·√(Q'S)` (`polars-var-bound`).
