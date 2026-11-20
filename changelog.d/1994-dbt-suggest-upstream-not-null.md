### sverify-dbt suggest names the input test that proves a model test

`sverify-dbt suggest` tries `not_null` on the seed and source columns no test covers when a model test fails because a row may fail it, and names the minimal set that proves the test, such as `not_null` on `raw_orders.ordered_at` for `fct_daily_revenue.not_null(order_day)`. It used to print that nothing more was provable ([#1994](https://github.com/AlexanderNenninger/substrait-lean/issues/1994)).
