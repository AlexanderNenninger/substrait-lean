### The statistical aggregates' model says what it knows outside `Stat.fits`

`StatProps` (the model of Welford's and the generic algorithms) asked for the reference's own value for finite values past 2³² rows or 2³⁹⁸ in magnitude, which DuckDB and Polars do not give (`var_pop([1e150, 3e150])` differs in the last digits). Those inputs are now open, any double; NaN and infinities keep the reference's value. No verdict changes: the route already reports such columns unproved ([#1486](https://github.com/AlexanderNenninger/substrait-lean/issues/1486), D30).
