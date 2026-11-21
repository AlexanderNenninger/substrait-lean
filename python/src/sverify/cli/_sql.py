"""A bare `.sql` file as a `check` target (#1362): one query, the schemas of
the tables it reads from a file, and the verdict `verify` gives with no
contract (it reports what the query computes and what it can raise)."""

from __future__ import annotations

import inspect
import json
from pathlib import Path
from typing import Any

from sverify.cli._common import UsageError
from sverify.cli._discover import Checked, Discovery
from sverify.errors import UnsupportedError


def read_schemas(path: Path) -> dict[str, dict[str, str]]:
    """`{table: {column: type}}` from a YAML or JSON file. The types are the
    strings `sverify.verify(tables=)` reads (`"BIGINT"`, `"VARCHAR NOT NULL"`)."""
    if not path.is_file():
        raise UsageError(f"{path}: no such schema file")
    text = path.read_text(encoding="utf-8")
    try:
        if path.suffix == ".json":
            raw = json.loads(text)
        else:
            try:
                import yaml
            except ImportError:
                raise UsageError(
                    f"{path}: reading YAML needs pyyaml (pip install 'sverify[odcs]'); "
                    "a .json schema file needs nothing"
                ) from None
            raw = yaml.safe_load(text)
    except (ValueError, OSError) as e:
        raise UsageError(f"{path}: cannot read the schemas: {e}") from e
    ok = isinstance(raw, dict) and all(
        isinstance(cols, dict) and all(isinstance(t, str) for t in cols.values())
        for cols in raw.values()
    )
    if not ok:
        raise UsageError(f"{path}: the schemas are `{{table: {{column: type}}}}`, types as strings")
    return {str(t): {str(c): ty for c, ty in cols.items()} for t, cols in raw.items()}


def read_query(path: Path, dialect: str) -> str:
    """The one statement of the file."""
    import sqlglot

    text = path.read_text(encoding="utf-8")
    try:
        statements = [s for s in sqlglot.parse(text, read=dialect) if s is not None]
    except ValueError as e:  # an unknown dialect name
        raise UsageError(f"dialect {dialect!r}: {e}") from None
    except sqlglot.errors.SqlglotError as e:
        raise UsageError(f"{path}: cannot parse the SQL: {str(e).splitlines()[0]}") from e
    if len(statements) != 1:
        raise UsageError(f"{path}: one query per file, found {len(statements)} statements")
    return text


def load_sql(
    path: Path,
    out: Discovery,
    schema: str | None,
    dialect: str | None,
    semantics: str | None,
) -> Discovery:
    """Prove the query of `path` over the schemas of `schema`, into `out`.
    `dialect` and `semantics` are `sverify.sql`'s, with its defaults."""
    import sverify as sv

    # `sverify.sql`'s own defaults, and its own check of both names.
    defaults = inspect.signature(sv.sql).parameters
    dialect = dialect or defaults["dialect"].default
    semantics = semantics or defaults["semantics"].default
    if schema is None:
        raise UsageError(f"{path}: a .sql file needs --schema FILE, the types of its tables")
    query = read_query(path, dialect)
    try:
        step: Any = sv.sql(query, dialect=dialect, semantics=semantics)  # type: ignore[arg-type]
    except UnsupportedError:
        raise
    except ValueError as e:  # an unknown dialect or semantics
        raise UsageError(str(e)) from None
    schemas = read_schemas(Path(schema))
    from sverify.sql_model import query_tables

    missing = [t for t in query_tables(query, dialect) if t not in schemas]
    if missing:
        raise UsageError(f"{Path(schema)} has no schema for: {', '.join(missing)}")
    report = sv.verify(
        query,
        tables=schemas,
        counterexamples=0,
        semantics=semantics,  # type: ignore[arg-type]
    )
    out.checked.append(Checked(path.stem, [], report, [], {}, step))
    return out
