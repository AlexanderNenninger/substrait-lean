### Errors name the missing extra

A call that names an engine sverify installs as an extra, when that engine is
not installed, raises `ImportError` with the install command:
`sv.connect("polars")`, `sv.verify(..., semantics="polars")`,
`report.run(con, "polars")` and `sverify.sql.dialect_of("spark")` say
`engine 'polars' is not installed: pip install 'sverify[polars]'`, where they
said "unknown engine"
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)). A
test checks every entry point of an extra on a bare install.
