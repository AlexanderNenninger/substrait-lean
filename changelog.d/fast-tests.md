### A fast default test suite

`poe test` runs the fast Python tests on 2 workers: it leaves out the tests
marked `slow` (engine agreement on many queries, long streams, replays, and the
Spark tests) and runs a tenth of each Hypothesis test's examples (the `dev`
profile, `SVERIFY_PROFILE`). `poe test-all` and `poe qa` run every test with
the full counts, as CI does; CI splits the `core` tests into three shards
(`SVERIFY_SHARD`, `python/tests/conftest.py`).
