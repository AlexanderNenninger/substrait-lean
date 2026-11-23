### `sverify-dbt` reads past a column list that names no columns

A `unique_combination_of_columns` test whose `combination_of_columns` holds a null, or is a bare string, made `sverify-dbt check` fail with a `TypeError` for the whole project. Such a test is now not checked, with the reason "its columns are no list of column names", and the project's other tests are checked as before. dbt itself fails such a test ([#2414](https://github.com/AlexanderNenninger/substrait-lean/issues/2414)).
