# Examples

The ten examples are now the steps of [Getting started](getting-started.md),
with the install and what sverify does around them:

1. [A contract, proved and run](getting-started.md#1-a-contract-proved-and-run)
2. [SQL through `sv.verify`](getting-started.md#2-sql-through-svverify)
3. [The preconditions a plan needs](getting-started.md#3-the-preconditions-a-plan-needs-declared-and-checked-before-the-run)
4. [The same plan on Polars, by a route](getting-started.md#4-the-same-plan-on-polars-by-a-route)
5. [Doubles within the plan's bound](getting-started.md#5-doubles-within-the-plans-bound)
6. [A reproducible sink, kept up to date](getting-started.md#6-a-reproducible-sink-kept-up-to-date)
7. [A plan checked under DuckDB's profile](getting-started.md#7-a-plan-checked-under-duckdbs-profile)
8. [Substrait's own semantics](getting-started.md#8-substraits-own-semantics)
9. [Polars's profile, still pending](getting-started.md#9-polarss-profile-still-pending)
10. [A proved plan for any Substrait consumer](getting-started.md#10-a-proved-plan-for-any-substrait-consumer)

## One example per audience

Each audience has an example that CI runs from a checkout to a proved result:

| Audience | Example | CI job |
| --- | --- | --- |
| Data engineer | The tour, `notebooks/01_duplicate_payments.py` to `05_pipelines_and_engines.py` | `notebooks`; on a release, `notebooks-wheels` |
| Analytics engineer | The `shop` dbt project, checked by `sverify-dbt` | `dbt`; on a release, the `dbt` combination of `packages` |
| Platform team | `templates/pipelines`: `scripts/lake.py check --plans` proves every pipeline, exports each node with `Node.to_substrait` and proves the export again with `Report.from_substrait` | `template`; on a release, `template-wheel` |
