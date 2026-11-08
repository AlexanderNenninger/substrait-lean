### DataFusion is an optional engine, never a reference

DataFusion stays available (`pip install 'sverify[datafusion]'`,
`engine="datafusion"`) as an optional engine outside the 1.x promise. No test
takes its results as the expected side any more: the tests that did now
compare with Lean's reference or with DuckDB, the default oracle, and outside
DataFusion's own tests sverify behaves as if it were not installed
(`python/tests/conftest.py`). Its CI job, `test (datafusion)`, runs weekly
on main, and pull requests no longer wait on it. The docs call it an optional engine
throughout ([#868](https://github.com/AlexanderNenninger/substrait-lean/issues/868),
[#1102](https://github.com/AlexanderNenninger/substrait-lean/issues/1102)).
