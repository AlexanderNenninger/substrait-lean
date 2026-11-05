# shop: a sample dbt project for sverify-dbt

A small DuckDB project over the catalogue's `app` data
([`catalogue/schemas.toml`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/catalogue/schemas.toml)), with models
written from its dbt queries ([`catalogue/queries/modelling.toml`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/catalogue/queries/modelling.toml)):
a conditional pivot (`dbt-pivot-conditional`), a pivot of counts
(`dbt-pivot-wider`), an unpivot by `UNION ALL` (`dbt-unpivot-union`), a
type-2 history and the point-in-time join to it (`dbt-scd2-from-updates`,
`dbt-scd2-point-in-time`), a surrogate key (`dbt-surrogate-key`), a union of
sources (`dbt-union-sources`) and a recursive hierarchy
(`dbt-org-hierarchy`). The raw tables are seeds, which the models read as
the `app` source.

```bash
uv run dbt deps
uv run dbt compile
uv run sverify-dbt check . --selectors
uv run dbt seed
uv run dbt build --exclude selector:sverify_proved
```

Run these here, in `examples/shop`; `profiles.yml` is beside
`dbt_project.yml`, and the database is `shop.duckdb`. The models cover each
outcome: tests proved from the source tests, tests not proved, an enforced
contract with a primary key, a model that needs a source test it lacks
(`subscription_arr`), and two models sverify refuses (`stg_order_items`
for `md5`, `org_depth` for `WITH RECURSIVE`).
