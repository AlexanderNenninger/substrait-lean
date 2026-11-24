### A Polars window SUM or AVG over only `-0.0` gives `0.0`

On Polars, a window `SUM` or `AVG` whose frame holds only `-0.0` returned
`-0.0`, where the reference's correctly rounded sum of an exact zero is `0.0`.
The zero compared equal at the output, but a sign-reading function downstream
(`1 / x`, `atan2`) saw the other sign. The translation now reads the window's
result with one zero, as it already read a grouped one. DuckDB and Spark give
`0.0` natively
([#2587](https://github.com/AlexanderNenninger/substrait-lean/issues/2587)).
