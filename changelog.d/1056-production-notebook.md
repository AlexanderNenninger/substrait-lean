### A sixth tour notebook: running it in production

- [`notebooks/06_running_in_production.py`](notebooks/06_running_in_production.py)
  covers the work around a proved pipeline: `sverify check --diff` and
  `--fix` on a pipeline's file, a test with `sverify.testing.assert_contract`,
  a credential by name (`Secret`), OpenLineage events whose contract the
  next team proves again, and an hourly rollup whose state
  `sv.arrives_within` bounds, with a late batch refused before it lands
  ([#1056](https://github.com/AlexanderNenninger/substrait-lean/issues/1056)).
