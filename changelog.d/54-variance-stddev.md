### Variance and standard deviation

`var()` and `std()` of doubles and integers, of a sample or a population
(`how="pop"`), are verified (#54). sverify fixes how they are computed: the
mean first, then the squared deviations added in row order, so DuckDB,
Polars and Spark give the same result to the last bit. DataFusion and
Snowflake, which add in their own order, are refused, and so are variances
over windows. A sample of one value gives NULL, and an infinite value raises,
since its deviation would be NaN.
