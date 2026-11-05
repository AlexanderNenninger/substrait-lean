### Plans checked under Polars's semantics run natively on Polars

`verify(semantics="polars")` now checks an Ibis transformation under
`Profile.polars`, an evaluable profile in Lean
(`SubstraitLean/PolarsProfile.lean`): integer `//` and `%` floor, as Polars's
do, so a postcondition such as `x % 2 >= 0` is proved. The plan states
`division_type: FLOOR`, the checker reads it as Polars's remainder (proved on
64-bit integers), and `report.run(con, "polars", route="auto")` takes the
`native` route, with no shim. DuckDB and the other engines refuse such a plan
with the reason. `substrait-check --contract` answers `"profile": "polars"`,
so the re-check route can target Polars, and inferred preconditions work
under `semantics="polars"`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
