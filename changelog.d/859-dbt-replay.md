### sverify-dbt checked against dbt packages' own projects

`python -m sverify_dbt.replay` builds the integration projects of dbt-utils
1.4.1 and dbt-expectations 0.10.10 with dbt on DuckDB and checks them with
sverify-dbt, test by test, beside dbt's own result. No proved test fails in
dbt's run. The ledgers in `dbt/replay/` name an issue or a design reason for
every test sverify-dbt does not check; CI's `dbt` job replays them and warns
on a change ([#859](https://github.com/AlexanderNenninger/substrait-lean/issues/859)).
