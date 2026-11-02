"""Maintainer tooling for sverify, kept out of the wheel.

The coverage harness, the query catalogue, the fuzzers, DuckDB's
sqllogictest replay and the example pipelines the tests share. The tests,
CI, `python/scripts/` and `characterization/` use them; users of sverify do
not. An editable install (`uv sync` in `python/`) puts `python/tools` on
`sys.path` (`dev-mode-dirs` in `pyproject.toml`), so run them as
`uv run python -m sverify_dev.<module>`.
"""
