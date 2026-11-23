### Polars refuses a variance beside a list in one grouping

On Polars, a grouping that holds a list-computed measure (`ARRAY_AGG` and the
like) runs on the in-memory engine. Its `VAR_*` and `STDDEV_*` then use the
in-memory algorithm, not the one the Polars profile states and proves the
bound for. The translation to Polars now refuses such a grouping, as it does
for a double `SUM` or `AVG`
([#2507](https://github.com/AlexanderNenninger/substrait-lean/issues/2507)).
The plan still runs on the other engines. On Polars, compute the list and
the statistic in separate groupings.
