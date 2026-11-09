"""sverify's own engines, each registered under the entry-point group
`sverify.profiles` in sverify's metadata (`pyproject.toml`), as a package
from outside registers one (#1189). Each module states one engine's
`ProfilePlugin` and imports nothing heavy: the engine's code loads when a
plan runs on it. An engine that is a package of its own registers from its
own metadata instead (`engines/duckdb/`, `engines/polars/`, `engines/spark/`).

Internal: not part of sverify's public API.
"""
