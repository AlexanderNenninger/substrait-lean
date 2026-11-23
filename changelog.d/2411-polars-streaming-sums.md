### Polars's double sums are proved, as the streaming engine adds them

Polars's profile states its double `SUM` and `AVG` as the streaming engine
computes them, sequential per group and pairwise per morsel
(`polars-sum-float-streaming`). Kahan's compensated sum is the in-memory
engine's, which sverify refuses, and it left the profile
([#2411](https://github.com/AlexanderNenninger/substrait-lean/issues/2411)).
A postcondition that holds on the reference's sum and keeps its sign is now
proved on Polars, as on DuckDB and Spark, where it was tested: five catalogue
queries (clickbench q09, q13, q37 and q42, and h2o-groupby q1) run on Polars
with proved evidence.
