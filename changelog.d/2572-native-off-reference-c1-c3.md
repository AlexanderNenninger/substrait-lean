### Concatenation is proved on DuckDB, Polars and Spark

String concatenation (`||`, `concat`, `lpad`'s padding, dbt's surrogate keys) now
has proved evidence on every engine where it was tested: each engine's table
states the NULL-propagating form its writer emits (`ACCEPT_NULLS`), from its
facts, and the generated lowering's proof covers it
([#2572](https://github.com/AlexanderNenninger/substrait-lean/issues/2572), ruling 282).
