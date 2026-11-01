"""Replay DuckDB's sqllogictests through sverify (epic #185).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

DuckDB's `test/sql/` holds about 4,800 `.test` files: queries with the
results, or the errors, DuckDB's developers expect. They are the first
evidence for a DuckDB engine profile. For each query in them this module
compares three results with the expected one:

* `duckdb`: DuckDB running the test's own SQL, a control. If it differs from
  the expected result, the test was written for another DuckDB version or
  the harness misreads it, and the query is `skipped`.
* `lean`: `Rel.eval` (via `substrait-check`) on the plan DataFusion's SQL
  producer writes for the query, with the tables the test created inlined.
* `engine`: DuckDB running the plan Lean writes back out
  (`sverify.engines.run`).

and classifies the query:

* `agree`: Lean and the engine give the expected result (an expected error
  counts when they raise, or Lean's verifier says the plan may raise);
* `disagree`: Lean or the engine does not (`side` says which);
* `refused`: sverify does not plan the query (the SQL translation, the
  producer or the checker refuses it);
* `skipped`: the test needs something the replay does not have (an
  extension, a setting, a second connection, a loop too long, …).

Tests are in DuckDB's dialect and the producer reads DataFusion's, so each
query is translated with sqlglot first (`translate`): DuckDB's `/` is float
division, `//` integer division, `x::T` a cast. A `SELECT` without `FROM`
reads a one-row table, as DataFusion's producer refuses an empty relation.
The translated SQL is in the ledger.

`fetch` checks out `test/sql` at the DuckDB version `python/uv.lock` pins
(sparse and shallow, into `~/.cache/sverify/duckdb-slt`); `parse` reads the
`.test` format; `replay_file` runs one file; `python -m sverify.slt` replays
areas and writes a ledger per area (`characterization/duckdb/<area>.json`)
and a summary table (`characterization/duckdb/README.md`).
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import functools
import hashlib
import json
import math
import os
import re
import subprocess
import threading
import tomllib
from collections import Counter
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import duckdb
import pyarrow as pa

REPO = Path(__file__).resolve().parents[3]
CACHE = Path(os.environ.get("SVERIFY_SLT_CACHE", Path.home() / ".cache" / "sverify" / "duckdb-slt"))
LEDGER = REPO / "characterization" / "duckdb"

#: The one-row table a `SELECT` without `FROM` reads.
ONE = "__sverify_one"

#: Rows past which a table is not inlined into a plan for Lean.
MAX_ROWS = 5000
#: Iterations past which a file's loops are not expanded.
MAX_ITERATIONS = 2000
#: Seconds DuckDB may spend on one statement.
TIMEOUT = 10.0


# --- fetching ----------------------------------------------------------------


def duckdb_version(lock: Path = REPO / "python" / "uv.lock") -> str:
    """The DuckDB version `uv.lock` pins (the installed one without a lock)."""
    if lock.exists():
        for pkg in tomllib.loads(lock.read_text())["package"]:
            if pkg["name"] == "duckdb":
                return pkg["version"]
    return duckdb.__version__


def fetch(version: str | None = None, cache: Path = CACHE) -> Path:
    """DuckDB's `test/sql` at `version` (default: `duckdb_version`), checked
    out sparse and shallow into `cache` on first use. Returns the directory
    holding `test/sql`."""
    version = version or duckdb_version()
    root = cache / f"v{version}"
    if not (root / "test" / "sql").is_dir():
        root.parent.mkdir(parents=True, exist_ok=True)
        url = "https://github.com/duckdb/duckdb"
        git = ["git", "-c", "advice.detachedHead=false"]
        clone = ["clone", "-q", "--depth", "1", "--filter=blob:none", "--sparse"]
        subprocess.run([*git, *clone, "--branch", f"v{version}", url, str(root)], check=True)
        subprocess.run([*git, "-C", str(root), "sparse-checkout", "set", "test/sql"], check=True)
    return root


def area_of(rel: str) -> str:
    """A test file's area: its directory under `test/sql`, one level deep, or
    two for the large `function` and `types`."""
    parts = Path(rel).parts
    depth = 2 if parts[0] in ("function", "types") and len(parts) > 2 else 1
    return "/".join(parts[:depth]) if len(parts) > 1 else "(root)"


# --- parsing -----------------------------------------------------------------


@dataclass
class Record:
    """One `statement` or `query` of a test file, with loops expanded."""

    kind: str
    """`statement` or `query`."""
    line: int
    sql: str
    expect: str
    """`ok`, `error`, `maybe` (statements) or `rows` (queries)."""
    types: str = ""
    """A query's column types, one letter each (`I`, `R`, `T`, …)."""
    sort: str = "nosort"
    """`nosort`, `rowsort` or `valuesort`."""
    expected: list[str] = field(default_factory=list)
    """A query's expected lines; a statement's expected error message."""
    connection: str | None = None
    skip: str | None = None
    """Why the replay does not run the record, if it does not."""


@dataclass
class TestFile:
    records: list[Record]
    skip: str | None = None
    """Why the whole file is skipped (an extension it requires, …)."""


#: `require` arguments the in-memory Python DuckDB meets.
REQUIRE_OK = {"skip_reload", "no_alternative_verify", "noforcestorage", "no_vector_verification"}

#: `foreach` tokens and the types they stand for.
SIGNED = ["tinyint", "smallint", "integer", "bigint", "hugeint"]
UNSIGNED = ["utinyint", "usmallint", "uinteger", "ubigint", "uhugeint"]
TOKENS = {
    "<signed>": SIGNED,
    "<unsigned>": UNSIGNED,
    "<integral>": SIGNED + UNSIGNED,
    "<numeric>": SIGNED + UNSIGNED + ["float", "double"],
}


def _blocks(lines: list[str]) -> Iterator[tuple[int, list[str]]]:
    """Blank-line separated blocks, with the 1-based line of their first line.
    Comment lines outside a block are dropped."""
    block: list[str] = []
    start = 0
    for i, raw in enumerate(lines, 1):
        line = raw.rstrip("\n").rstrip("\r")
        if not line.strip():
            if block:
                yield start, block
            block = []
            continue
        if not block and line.lstrip().startswith("#"):
            continue
        if not block:
            start = i
        block.append(line)
    if block:
        yield start, block


def _expand(items: list[tuple[int, list[str]]]) -> tuple[list[tuple[int, list[str]]], str | None]:
    """Unroll `loop`/`foreach`/`endloop` (and their concurrent variants,
    sequentially), substituting `${var}` and `{var}`."""
    out: list[tuple[int, list[str]]] = []
    budget = [MAX_ITERATIONS]

    def values(header: list[str]) -> list[list[str]]:
        if header[0] in ("loop", "concurrentloop"):
            var, lo, hi = header[1], int(header[2]), int(header[3])
            return [[var, str(k)] for k in range(lo, hi)]
        var = header[1]
        vals: list[str] = []
        for tok in header[2:]:
            vals += TOKENS.get(tok.lower(), [tok])
        return [[var, v] for v in vals]

    def subst(block: list[str], var: str, val: str) -> list[str]:
        names = var.split(",")
        vals = val.split(",") if "," in var else [val]
        res = []
        for line in block:
            for n, v in zip(names, vals, strict=False):
                line = line.replace("${" + n + "}", v).replace("{" + n + "}", v)
            res.append(line)
        return res

    def walk(i: int, env: list[tuple[str, str]]) -> int:
        while i < len(items):
            start, block = items[i]
            head = block[0].split()
            if head[0] in ("loop", "foreach", "concurrentloop", "concurrentforeach"):
                body_end = None
                for val in values(head):
                    budget[0] -= 1
                    if budget[0] < 0:
                        raise OverflowError("loops too long")
                    body_end = walk(i + 1, [*env, (val[0], val[1])])
                if body_end is None:  # an empty loop: find its end
                    body_end = walk_skip(i + 1)
                i = body_end + 1
                continue
            if head[0] == "endloop":
                return i
            for var, val in env:
                block = subst(block, var, val)
            out.append((start, block))
            i += 1
        return i

    def walk_skip(i: int) -> int:
        depth = 0
        while i < len(items):
            head = items[i][1][0].split()[0]
            if head in ("loop", "foreach", "concurrentloop", "concurrentforeach"):
                depth += 1
            elif head == "endloop":
                if depth == 0:
                    return i
                depth -= 1
            i += 1
        return i

    # `endloop` and the loop headers can share a block with nothing else, but
    # a block may also start with `endloop` followed by a record: split them.
    flat: list[tuple[int, list[str]]] = []
    for start, block in items:
        while block and block[0].split()[0] in (
            "loop",
            "foreach",
            "concurrentloop",
            "concurrentforeach",
            "endloop",
        ):
            flat.append((start, [block[0]]))
            block, start = block[1:], start + 1
        if block:
            flat.append((start, block))
    items[:] = flat
    try:
        walk(0, [])
    except OverflowError as e:
        return out, str(e)
    return out, None


def parse(text: str) -> TestFile:
    """The records of a `.test` file."""
    expanded, problem = _expand(list(_blocks(text.splitlines())))
    if problem:
        return TestFile([], skip=problem)
    records: list[Record] = []
    file_skip: str | None = None
    skipping = False
    for start, block in expanded:
        head = block[0].split()
        word = head[0]
        conditions: list[str] = []
        while word in ("onlyif", "skipif"):
            conditions.append(block[0])
            block, start = block[1:], start + 1
            if not block:
                break
            head = block[0].split()
            word = head[0]
        if not block:
            continue
        skip = None
        for cond in conditions:
            c = cond.split()
            if (c[0] == "onlyif") != (c[1] == "duckdb"):
                skip = cond
        if word == "require":
            if head[1] not in REQUIRE_OK and file_skip is None:
                file_skip = f"require {' '.join(head[1:])}"
            continue
        if word in ("require-env", "include", "unzip"):
            file_skip = file_skip or " ".join(head)
            continue
        if word == "mode":
            if head[1] == "skip":
                skipping = True
            elif head[1] == "unskip":
                skipping = False
            continue
        if word == "halt":
            break
        if word not in ("statement", "query"):
            # load, restart, reconnect, set, reset, sleep, tags, hash-threshold:
            # the replay runs in memory on one connection.
            continue
        body = block[1:]
        if "----" in body:
            k = body.index("----")
            sql_lines, expected = body[:k], body[k + 1 :]
        else:
            sql_lines, expected = body, []
        sql = "\n".join(sql_lines)
        if skipping:
            skip = skip or "mode skip"
        if word == "statement":
            expect = head[1] if len(head) > 1 else "ok"
            conn = head[2] if len(head) > 2 else None
            records.append(
                Record(
                    "statement", start, sql, expect, expected=expected, connection=conn, skip=skip
                )
            )
        else:
            types = head[1] if len(head) > 1 else ""
            sort = "nosort"
            conn = None
            for tok in head[2:]:
                if tok in ("nosort", "rowsort", "valuesort", "sort"):
                    sort = "rowsort" if tok == "sort" else tok
                elif tok.startswith("con"):
                    conn = tok
            records.append(Record("query", start, sql, "rows", types, sort, expected, conn, skip))
    return TestFile(records, file_skip)


# --- translating ---------------------------------------------------------------


@functools.cache
def _dialects() -> dict[str, Any]:
    """sqlglot's DuckDB dialect under each implicit NULL ordering (to tell
    the ORDER BY items that name theirs from those that do not), and the
    DataFusion dialect to write."""
    import logging

    from ibis.backends.sql.dialects import DataFusion
    from sqlglot import exp
    from sqlglot.dialects.duckdb import DuckDB

    logging.getLogger("sqlglot").setLevel(logging.ERROR)

    class Target(DataFusion):
        class Generator(DataFusion.Generator):
            TYPE_MAPPING = {
                **DataFusion.Generator.TYPE_MAPPING,
                exp.DataType.Type.TINYINT: "TINYINT",
                exp.DataType.Type.DOUBLE: "DOUBLE",
            }
            TRANSFORMS = {
                **DataFusion.Generator.TRANSFORMS,
                # DuckDB's `//` on integers truncates, as DataFusion's `/` does.
                exp.IntDiv: lambda self, e: (
                    f"({self.sql(e, 'this')} / {self.sql(e, 'expression')})"
                ),
            }

    readers: dict[str, Any] = {"duckdb": DuckDB}
    for order in ("nulls_are_small", "nulls_are_large"):
        readers[order] = type(f"DuckDB_{order}", (DuckDB,), {"NULL_ORDERING": order})
    readers["target"] = Target
    return readers


def _parse(sql: str, dialect: Any) -> Any:
    import sqlglot

    try:
        trees = [t for t in sqlglot.parse(sql, read=dialect) if t is not None]
    except Exception as e:  # noqa: BLE001 - sqlglot's errors vary
        raise ValueError(f"sqlglot: {str(e).splitlines()[0][:200]}") from e
    if len(trees) != 1:
        raise ValueError("not one statement")
    return trees[0]


def translate(sql: str, null_order: str = "nulls_last") -> tuple[str, str, list[str], bool]:
    """DuckDB SQL as DataFusion SQL, the same query as sqlglot read it
    written back as DuckDB SQL (to check the reading), the tables it reads,
    and whether the outermost query orders its rows.

    `null_order` is DuckDB's `default_null_order` (`nulls_last`, its
    default, or `nulls_first`): the place of NULLs for an ORDER BY item that
    does not name it, written out explicitly.

    Raises:
        ValueError: sqlglot cannot read or write the query, or would drop
            part of it (a function it does not know how to write).
    """
    from sqlglot import exp
    from sqlglot.errors import ErrorLevel

    d = _dialects()
    tree = _parse(sql, d["duckdb"])
    if not isinstance(tree, exp.Query):
        raise ValueError(f"not a query: {type(tree).__name__}")
    # An item names its NULL order if every implicit ordering reads it alike.
    small, large = (_parse(sql, d[o]) for o in ("nulls_are_small", "nulls_are_large"))
    trios = zip(
        tree.find_all(exp.Ordered),
        small.find_all(exp.Ordered),
        large.find_all(exp.Ordered),
        strict=False,
    )
    for o, s, g in trios:
        explicit = (
            o.args.get("nulls_first") == s.args.get("nulls_first") == g.args.get("nulls_first")
        )
        if not explicit:
            o.set("nulls_first", null_order == "nulls_first")
    try:
        back = tree.sql(dialect=d["duckdb"], unsupported_level=ErrorLevel.RAISE)
    except Exception as e:  # noqa: BLE001
        raise ValueError(f"sqlglot: {str(e).splitlines()[0][:200]}") from e
    ctes = {c.alias_or_name for c in tree.find_all(exp.CTE)}
    for sel in list(tree.find_all(exp.Select)):
        if not sel.args.get("from_"):
            sel.set("from_", exp.From(this=exp.to_table(ONE)))
    tables = []
    for t in tree.find_all(exp.Table):
        if isinstance(t.this, exp.Identifier) and t.name not in ctes and t.name not in tables:
            tables.append(t.name)
    ordered = bool(tree.args.get("order"))
    try:
        out = tree.sql(dialect=d["target"], unsupported_level=ErrorLevel.RAISE)
    except Exception as e:  # noqa: BLE001
        raise ValueError(f"sqlglot: {str(e).splitlines()[0][:200]}") from e
    return out, back, tables, ordered


# --- comparing -------------------------------------------------------------------


def _expected_values(rec: Record) -> list[str] | str:
    """The expected values in row order, or a hash line."""
    lines = rec.expected
    if len(lines) == 1 and re.fullmatch(r"\d+ values hashing to [0-9a-f]{32}", lines[0]):
        return lines[0]
    ncols = len(rec.types) or 1
    cells = [line.split("\t") for line in lines]
    if ncols > 1 and all(len(c) == 1 for c in cells) and len(cells) % ncols == 0:
        return [c[0] for c in cells]  # one value per line
    return [v for c in cells for v in c]


def _sorted(values: list[str], ncols: int, sort: str) -> list[str]:
    if sort == "valuesort":
        return sorted(values)
    if sort == "rowsort":
        rows = [values[i : i + ncols] for i in range(0, len(values), ncols)]
        return [v for r in sorted(rows) for v in r]
    return values


def _same_value(a: str, b: str) -> bool:
    if a == b:
        return True
    bools = {"true": "1", "false": "0"}
    if bools.get(a.lower(), a) == bools.get(b.lower(), b):
        return True
    try:
        x, y = float(a), float(b)
    except ValueError:
        return False
    if math.isnan(x) or math.isnan(y):
        return math.isnan(x) and math.isnan(y)
    # Lean prints doubles with six decimals.
    return x == y or math.isclose(x, y, rel_tol=1e-9, abs_tol=1e-6)


def _same_bag(a: list[list[str]], b: list[list[str]], ordered: bool) -> bool:
    if not ordered:
        a, b = sorted(a), sorted(b)
    return len(a) == len(b) and all(
        len(x) == len(y) and all(map(_same_value, x, y)) for x, y in zip(a, b, strict=True)
    )


def matches(rec: Record, got: list[list[str]], ordered: bool) -> bool:
    """Whether rows (as DuckDB's runner prints values) are the expected
    ones. Without an `ORDER BY`, rows compare as a bag even under `nosort`:
    the expected order is DuckDB's, which no plan promises."""
    ncols = len(rec.types) or 1
    sort = rec.sort if rec.sort != "nosort" or ordered else "rowsort"
    if any(len(r) != ncols for r in got):
        return False
    values = _sorted([v for r in got for v in r], ncols, sort)
    expected = _expected_values(rec)
    if isinstance(expected, str):
        digest = hashlib.md5("".join(v + "\n" for v in values).encode()).hexdigest()
        return expected == f"{len(values)} values hashing to {digest}"
    expected = _sorted(expected, ncols, sort)
    return len(values) == len(expected) and all(map(_same_value, values, expected))


class Formatter:
    """Values as DuckDB's sqllogictest runner prints them: cast to VARCHAR,
    NULL as `NULL`, the empty string as `(empty)`."""

    def __init__(self) -> None:
        self.con = duckdb.connect()

    def rows(self, table: pa.Table) -> list[list[str]]:
        names = [f"c{i}" for i in range(table.num_columns)]
        table = table.rename_columns(names)
        if not names:
            return [[] for _ in range(table.num_rows)]
        self.con.register("__r", table)
        try:
            cols = ", ".join(f"CAST({n} AS VARCHAR)" for n in names)
            out = self.con.sql(f"SELECT {cols} FROM __r").fetchall()
        finally:
            self.con.unregister("__r")
        return [
            ["NULL" if v is None else (v or "(empty)").replace("\0", "\\0") for v in r] for r in out
        ]


# --- replaying ---------------------------------------------------------------------


@dataclass
class Result:
    file: str
    line: int
    sql: str
    expected: str
    duckdb: str
    lean: str
    engine: str
    cls: str
    side: str | None = None
    """For `disagree`: `lean`, `engine` or `both`."""
    reason: str | None = None
    translated: str | None = None


def _clip(s: str, n: int = 300) -> str:
    s = s.replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"


def _show(rows: list[list[str]]) -> str:
    return _clip(json.dumps(rows))


def _error(e: BaseException) -> str:
    return "error: " + _clip(str(e).strip().splitlines()[0] if str(e).strip() else repr(e), 200)


#: DuckDB settings that change what a query means: queries run while one is
#: set are skipped. `default_null_order` is followed instead (`translate`).
SEMANTIC = {
    "binary_as_string", "calendar", "current_dialect", "default_collation", "default_order",
    "dialect_compatibility_mode", "disable_timestamptz_casts", "error_on_division_by_zero",
    "ieee_floating_point_ops", "integer_division", "legacy_disable_null_type", "null_order",
    "old_implicit_casting", "order_by_non_integer_literal", "preserve_identifier_case",
    "regex_match_operator_semantics", "scalar_subquery_error_on_multiple_rows", "schema",
    "search_path", "sqlite_all_varchar", "timezone", "variable",
}  # fmt: skip

_SETTING = re.compile(
    r"^\s*(SET|PRAGMA|RESET)\s+(?:(?:GLOBAL|SESSION|LOCAL)\s+)?(\w+)\s*(?:(?:=|TO)\s*(.*?))?\s*;?\s*$",
    re.I | re.S,
)

_PROBE = re.compile(r"^\s*(\(\s*)*(SELECT|WITH|VALUES|FROM|TABLE)\b", re.I)


class Replay:
    """One test file's replay: a DuckDB database holding the test's state,
    and a sverify connection that mirrors the tables a query reads."""

    def __init__(self, rel: str) -> None:
        from sverify.engine import connect

        self.rel = rel
        self.db = duckdb.connect()
        self.fmt = Formatter()
        self.con = connect()
        self.con.put(ONE, pa.table({"__x": pa.array([0], pa.int64())}))
        self.version = 0
        self.synced: dict[str, int] = {}
        self.null_order = "nulls_last"
        self.settings: set[str] = set()

    def run(self, sql: str) -> duckdb.DuckDBPyRelation | None:
        timer = threading.Timer(TIMEOUT, self.db.interrupt)
        timer.start()
        try:
            return self.db.sql(sql)
        finally:
            timer.cancel()

    def arrow(self, sql: str) -> pa.Table:
        timer = threading.Timer(TIMEOUT, self.db.interrupt)
        timer.start()
        try:
            rel = self.db.sql(sql)
            return rel.to_arrow_table() if rel is not None else pa.table({})
        finally:
            timer.cancel()

    def sync(self, tables: Iterable[str]) -> dict[str, list[tuple]]:
        """Mirror the DuckDB tables (and views, as tables) a query reads.
        Returns their rows, for inlining."""
        from sverify.engine import table_rows

        known = {
            r[0]
            for r in self.db.sql(
                "SELECT table_name FROM duckdb_tables() WHERE schema_name = 'main' "
                "UNION SELECT view_name FROM duckdb_views() "
                "WHERE schema_name = 'main' AND NOT internal"
            ).fetchall()
        }
        rows: dict[str, list[tuple]] = {}
        for name in tables:
            if name == ONE or name not in known:
                continue
            if self.synced.get(name) != self.version:
                table = self.arrow(f'SELECT * FROM "{name}"')
                if table.num_rows > MAX_ROWS:
                    raise OverflowError(f"table {name} has {table.num_rows} rows")
                self.con.put(name, table)
                self.synced[name] = self.version
            rows[name] = table_rows(self.con, name)
        rows[ONE] = [(0,)]
        return rows

    def statement(self, rec: Record) -> None:
        try:
            self.run(rec.sql)
            ok = True
        except duckdb.Error:
            ok = False
        self.version += 1
        if ok and (m := _SETTING.match(rec.sql)):
            verb, name, value = m.group(1).upper(), m.group(2).lower(), (m.group(3) or "")
            value = value.strip().strip("'\"").lower()
            if name == "default_null_order":
                if verb == "RESET" or value in ("nulls_last", "nulls_first"):
                    self.null_order = "nulls_last" if verb == "RESET" else value
                    self.settings.discard(name)
                else:
                    self.settings.add(name)
            elif name in SEMANTIC:
                (self.settings.discard if verb == "RESET" else self.settings.add)(name)

    def probe(self, rec: Record) -> Result:
        """Run a query (or a statement that is one) all three ways."""
        res = Result(self.rel, rec.line, _clip(rec.sql, 1000), "", "", "", "", "skipped")
        is_query = rec.kind == "query"
        if is_query:
            exp_vals = _expected_values(rec)
            res.expected = exp_vals if isinstance(exp_vals, str) else _clip(json.dumps(exp_vals))
        else:
            msg = " ".join(rec.expected)
            res.expected = rec.expect + (f": {_clip(msg, 200)}" if msg else "")
        expect_error = rec.expect == "error"

        def outcome(rows: list[list[str]] | None, err: str | None, ordered: bool) -> bool:
            if rec.expect == "maybe":
                return True
            if err is not None:
                return expect_error
            if expect_error:
                return False
            return matches(rec, rows or [], ordered) if is_query else True

        # DuckDB on the test's SQL, the control.
        try:
            table = self.arrow(rec.sql)
            ddb_rows, ddb_err = self.fmt.rows(table), None
            res.duckdb = _show(ddb_rows)
        except Exception as e:  # noqa: BLE001 - DuckDB's error is a result
            ddb_rows, ddb_err = None, _error(e)
            res.duckdb = ddb_err
        self.version += 1  # a query can have side effects (nextval, …)

        if self.settings:
            res.reason = "setting " + ", ".join(sorted(self.settings))
            return res
        try:
            sql, back, tables, ordered = translate(rec.sql, self.null_order)
        except ValueError as e:
            res.cls, res.reason = "refused", f"translate: {e}"
            return res
        res.translated = _clip(sql, 1000)
        # sqlglot must read the query as DuckDB does: its reading, written
        # back as DuckDB SQL, gives DuckDB's result.
        try:
            back_rows, back_err = self.fmt.rows(self.arrow(back)), None
        except Exception as e:  # noqa: BLE001
            back_rows, back_err = None, _error(e)
        self.version += 1
        same = (back_err is None) == (ddb_err is None) and (
            back_rows is None or _same_bag(back_rows, ddb_rows or [], ordered)
        )
        if not same:
            res.cls, res.reason = "refused", "translate: sqlglot reads the query differently"
            return res
        if not outcome(ddb_rows, ddb_err, ordered):
            res.reason = "DuckDB's own result differs from the expected one"
            return res
        try:
            rows = self.sync(tables)
        except OverflowError as e:
            res.reason = str(e)
            return res
        except Exception as e:  # noqa: BLE001 - a type Arrow or sverify cannot hold
            res.cls, res.reason = "refused", f"tables: {_clip(str(e), 200)}"
            return res

        from sverify.engine import run_checker, run_plan, substrait_json, written_plan
        from sverify.testing import lean_values

        try:
            plan = substrait_json(self.con, sql)
            schema = self.con.datafusion.sql(sql).schema()
        except Exception as e:  # noqa: BLE001 - the producer refusing
            res.cls, res.reason = "refused", f"producer: {_datafusion_message(e)}"
            return res
        if '"virtualTable": {}' in plan:
            # DataFusion 51 writes `VALUES (…)` as an empty virtual table.
            res.cls, res.reason = "refused", "producer: VALUES written as an empty virtual table"
            return res
        code, out, err = run_checker((), plan)
        if code != 0 or "well-formed: yes" not in out:
            res.cls, res.reason = "refused", f"checker: {_clip((err or out).strip()[-200:], 200)}"
            return res

        # Lean on the plan with the tables inlined.
        lean_err = None
        lean_rows: list[list[str]] = []
        try:
            inlined = _typed_inline(json.loads(plan), rows, self.con)
            values = lean_values(json.dumps(inlined))
            lean_rows = self.fmt.rows(_as_table(values, schema))
            res.lean = _show(lean_rows)
        except subprocess.CalledProcessError as e:
            lean_err = "error: " + _clip(((e.stderr or "") + (e.output or "")).strip()[-200:], 200)
        except Exception as e:  # noqa: BLE001 - recorded
            lean_err = _error(e)
        if lean_err is not None:
            res.lean = lean_err
        lean_ok = outcome(lean_rows, lean_err, ordered)
        if expect_error and not lean_ok and (issues := _issues(sql, self.con)):
            # Not an agreement (`Rel.eval` gives rows), but the verifier warns.
            res.reason = "verify: " + _clip("; ".join(issues), 200)

        # DuckDB on the plan Lean writes.
        from sverify import polars_engine
        from sverify.sql import core as sql_core

        refusals = (polars_engine.Unsupported, sql_core.Unsupported)

        engine_ok: bool | None
        try:
            got = run_plan(self.con, written_plan(plan), "duckdb")
            eng_rows = self.fmt.rows(got)
            res.engine = _show(eng_rows)
            engine_ok = outcome(eng_rows, None, ordered)
        except refusals as e:
            res.engine, engine_ok = f"refused: {_clip(str(e), 200)}", None
        except Exception as e:  # noqa: BLE001
            res.engine = _error(e)
            engine_ok = outcome(None, res.engine, ordered)

        if lean_ok and engine_ok is not False:
            res.cls = "agree"
        else:
            res.cls = "disagree"
            res.side = (
                "both"
                if not lean_ok and engine_ok is False
                else "lean"
                if not lean_ok
                else "engine"
            )
        return res


def _issues(sql: str, con: Any) -> list[str]:
    """The runtime errors and wrap-arounds `verify` cannot rule out."""
    from sverify.contracts import verify

    try:
        report = verify(sql, tables={n: con.table(n).schema() for n in con.arrow})
    except Exception:  # noqa: BLE001
        return []
    return [str(i) for i in report.issues]


def _datafusion_message(e: BaseException) -> str:
    """The message of a DataFusion error, without its diagnostic wrapping."""
    text = str(e)
    if m := re.search(r'message: "((?:[^"\\]|\\.)*)"', text):
        text = m.group(1)
    return _clip(text.removeprefix("DataFusion error: "), 200)


def _typed_inline(plan: dict, rows: dict[str, list[tuple]], con: Any) -> dict:
    """`inline_tables`, with each NULL typed as its column (not `i64`)."""
    from sverify.testing import inline_tables

    plan = inline_tables(plan, rows)

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "virtualTable" in node and "baseSchema" in node:
                types = node["baseSchema"].get("struct", {}).get("types", [])
                for row in node["virtualTable"].get("expressions", []):
                    for i, f in enumerate(row["fields"]):
                        lit = f.get("literal", {})
                        if "null" in lit and i < len(types):
                            lit["null"] = types[i]
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return plan


def _as_table(values: list[tuple], schema: pa.Schema) -> pa.Table:
    """Lean's values as a table of DataFusion's output schema: timestamps
    and dates come back as integer codes."""
    from sverify.testing import EPOCH

    cols = []
    for i, f in enumerate(schema):
        col = [r[i] for r in values]
        t = f.type
        if pa.types.is_timestamp(t):
            col = [None if v is None else EPOCH + dt.timedelta(microseconds=v) for v in col]
            t = pa.timestamp("us", t.tz)
        elif pa.types.is_date(t):
            col = [None if v is None else EPOCH.date() + dt.timedelta(days=v) for v in col]
            t = pa.date32()
        elif pa.types.is_string(t) or pa.types.is_large_string(t) or pa.types.is_string_view(t):
            t = pa.string()
        try:
            cols.append(pa.array(col, t))
        except (pa.ArrowInvalid, pa.ArrowTypeError, OverflowError, TypeError):
            # A value outside the type (an unbounded integer, …): as text.
            cols.append(pa.array([None if v is None else str(v) for v in col], pa.string()))
    return pa.table(cols, names=[f"c{i}" for i in range(len(cols))])


def replay_file(path: Path, rel: str) -> tuple[list[Result], str | None]:
    """The results of one test file, and why it was skipped (if it was)."""
    tf = parse(path.read_text(errors="replace"))
    if tf.skip:
        return [], tf.skip
    rp = Replay(rel)
    results: list[Result] = []
    for rec in tf.records:
        probe = _PROBE.match(rec.sql) is not None
        if rec.skip or rec.connection:
            if probe:
                why = rec.skip or f"connection {rec.connection}"
                results.append(
                    Result(
                        rel, rec.line, _clip(rec.sql, 1000), "", "", "", "", "skipped", reason=why
                    )
                )
            continue
        if not probe:
            rp.statement(rec)
            continue
        try:
            results.append(rp.probe(rec))
        except Exception as e:  # noqa: BLE001 - the harness must go on
            results.append(
                Result(
                    rel,
                    rec.line,
                    _clip(rec.sql, 1000),
                    "",
                    "",
                    "",
                    "",
                    "skipped",
                    reason=f"harness: {_error(e)}",
                )
            )
    return results, None


def _replay_one(args: tuple[str, str]) -> tuple[str, list[dict], str | None]:
    path, rel = args
    try:
        results, skip = replay_file(Path(path), rel)
    except Exception as e:  # noqa: BLE001
        return rel, [], f"harness: {_error(e)}"
    return rel, [asdict(r) for r in results], skip


# --- ledger --------------------------------------------------------------------------

CLASSES = ("agree", "disagree", "refused", "skipped")


def write_ledger(
    area: str,
    version: str,
    results: list[dict],
    skipped_files: dict[str, str],
    out: Path = LEDGER,
    head: dict | None = None,
) -> Path:
    """`<out>/<area>.json`: one result per line, sorted by file and line.
    `head` adds to (or replaces) the keys before the results."""
    out.mkdir(parents=True, exist_ok=True)
    results = sorted(results, key=lambda r: (r["file"], r["line"]))
    counts = Counter(r["cls"] for r in results)
    sides = Counter(r["side"] for r in results if r["cls"] == "disagree")
    head = {
        **{
            "duckdb": version,
            "area": area,
            "summary": {c: counts.get(c, 0) for c in CLASSES},
            "disagree_sides": dict(sorted(sides.items())),
            "skipped_files": dict(sorted(skipped_files.items())),
        },
        **(head or {}),
    }
    path = out / f"{area.replace('/', '__')}.json"
    lines = ["{"]
    for k, v in head.items():
        lines.append(f"  {json.dumps(k)}: {json.dumps(v, sort_keys=True)},")
    lines.append('  "results": [')
    body = [
        "    " + json.dumps({k: v for k, v in r.items() if v not in (None, "")}, ensure_ascii=False)
        for r in results
    ]
    lines.append(",\n".join(body))
    lines.append("  ]")
    lines.append("}")
    path.write_text("\n".join(lines) + "\n")
    return path


def write_summary(out: Path = LEDGER) -> Path:
    """`<out>/README.md`'s table, from every ledger in `out`."""
    rows = []
    for p in sorted(out.glob("*.json")):
        led = json.loads(p.read_text())
        s = led["summary"]
        reasons = Counter(
            (r.get("reason") or "").split(":")[0] for r in led["results"] if r["cls"] == "refused"
        )
        top = ", ".join(f"{k} {n}" for k, n in reasons.most_common(2))
        d = led.get("disagree_sides", {})
        sides = ", ".join(f"{k} {n}" for k, n in sorted(d.items()))
        rows.append(
            f"| [{led['area']}]({p.name}) | {s['agree']} | {s['disagree']} | {sides} "
            f"| {s['refused']} | {s['skipped']} | {len(led['skipped_files'])} | {top} |"
        )
    path = out / "README.md"
    text = path.read_text() if path.exists() else ""
    table = "\n".join(
        [
            "<!-- slt:start -->",
            "| Area | Agree | Disagree | Disagree side | Refused | Skipped | Files skipped "
            "| Refused by |",
            "|---|---:|---:|---|---:|---:|---:|---|",
            *rows,
            "<!-- slt:end -->",
        ]
    )
    if "<!-- slt:start -->" in text:
        text = re.sub(r"<!-- slt:start -->.*<!-- slt:end -->", lambda _: table, text, flags=re.S)
    else:
        text = text + ("\n" if text else "") + table + "\n"
    path.write_text(text)
    return path


def test_files(root: Path, areas: Sequence[str]) -> dict[str, list[tuple[str, str]]]:
    """`.test` files under `root/test/sql` by area, for the areas named (all
    if none): an area matches itself and its subareas."""
    base = root / "test" / "sql"
    found: dict[str, list[tuple[str, str]]] = {}
    for p in sorted(base.rglob("*.test")):
        rel = p.relative_to(base).as_posix()
        area = area_of(rel)
        if areas and not any(
            area == a or area.startswith(a + "/") or rel.startswith(a) for a in areas
        ):
            continue
        found.setdefault(area, []).append((str(p), rel))
    return found


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("areas", nargs="*", help="areas under test/sql (default: all)")
    parser.add_argument("--version", help="DuckDB version (default: uv.lock's)")
    parser.add_argument("--out", type=Path, default=LEDGER)
    parser.add_argument("--jobs", type=int, default=2, help="processes (default 2)")
    args = parser.parse_args(argv)
    version = args.version or duckdb_version()
    root = fetch(version)
    for area, files in test_files(root, args.areas).items():
        results: list[dict] = []
        skipped: dict[str, str] = {}
        with concurrent.futures.ProcessPoolExecutor(args.jobs) as pool:
            for rel, res, skip in pool.map(_replay_one, files, chunksize=4):
                results += res
                if skip:
                    skipped[rel] = skip
        path = write_ledger(area, version, results, skipped, args.out)
        counts = Counter(r["cls"] for r in results)
        print(f"{area}: {dict(counts)} ({len(skipped)} files skipped) -> {path}", flush=True)
    write_summary(args.out)


if __name__ == "__main__":
    main()
