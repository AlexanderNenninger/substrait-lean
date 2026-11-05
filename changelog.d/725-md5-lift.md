### The SQL lift reads md5 and sha256

DuckDB SQL with `md5(s)` or `sha256(s)` is lifted as the digests the Ibis
producer already wrote for `hexdigest`, where it used to be refused. A
dbt surrogate key from `dbt_utils.generate_surrogate_key` now verifies, and
its `not_null` test is proved
([#725](https://github.com/AlexanderNenninger/substrait-lean/issues/725)).
