"""Replay DuckDB's sqllogictests through sverify (epic #185).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

DuckDB's `test/sql/` holds about 4,800 `.test` files: queries with the
results, or the errors, DuckDB's developers expect. They are the first
evidence for a DuckDB engine profile. For each query in them this module
compares three results with the expected one:

* `duckdb`: DuckDB running the test's own SQL, a control. If it differs from
  the expected result, the test was written for another DuckDB version or
  the harness misreads it, and the query is `skipped`.
* `lean`: `Rel.eval` (via `substrait-check`) on the plan sverify's lift
  (`sverify.sql_lift`) writes for the query, DuckDB's SQL as it is with
  DuckDB's semantics, with the tables the test created inlined.
* `engine`: DuckDB running the plan Lean writes back out
  (`sverify.engines.run`).

and classifies the query:

* `agree`: Lean and the engine give the expected result (an expected error
  counts when they raise, or Lean's verifier says the plan may raise);
* `disagree`: Lean or the engine does not (`side` says which);
* `refused`: sverify does not plan the query (the lift or the checker
  refuses it);
* `skipped`: the test needs something the replay does not have (an
  extension, a setting, a second connection, a loop too long, …).

The lift reads DuckDB's default NULL order only: queries run under
`SET default_null_order` are skipped.

`fetch` checks out `test/sql` at the DuckDB version `python/uv.lock` pins
(sparse and shallow, into `~/.cache/sverify/duckdb-slt`); `parse` reads the
`.test` format; `replay_file` runs one file; `python -m sverify_dev.slt` replays
areas and writes a ledger per area (`characterization/duckdb/<area>.json`)
and a summary table (`characterization/duckdb/README.md`).
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import functools
import hashlib
import json
import math
import multiprocessing
import os
import re
import signal
import subprocess
import tempfile
import threading
import time
import tomllib
from collections import Counter
from collections.abc import Callable, Iterable, Iterator, Sequence
from dataclasses import asdict, dataclass, field
from multiprocessing import connection as mp_connection
from multiprocessing.connection import Connection
from pathlib import Path
from typing import Any, cast

import duckdb
import pyarrow as pa

REPO = Path(__file__).resolve().parents[3]
CACHE = Path(os.environ.get("SVERIFY_SLT_CACHE", Path.home() / ".cache" / "sverify" / "duckdb-slt"))
REPLAY_DIR = REPO / "characterization" / "duckdb"

#: The one-row table a `SELECT` without `FROM` reads.
ONE = "__sverify_one"

#: Rows past which a query's tables, together, are not inlined into a plan
#: for Lean: data this size covers the semantics as well as more would, and
#: hundreds of thousands of rows make plans of tens of megabytes of JSON,
#: which take longer to parse than to evaluate (#357).
MAX_ROWS = 1000
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


def source(version: str, cache: Path = CACHE) -> str:
    """Where the tests come from: the repository, tag and commit."""
    root = cache / f"v{version}"
    try:
        commit = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True
        ).stdout.strip()
    except OSError:
        commit = ""
    return f"duckdb/duckdb@v{version}" + (f" ({commit})" if commit else "")


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


def _clip(s: str, n: int = 300) -> str:
    s = s.replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"


def _show(rows: list[list[str]]) -> str:
    return _clip(json.dumps(rows))


def _error(e: BaseException) -> str:
    return "error: " + _clip(str(e).strip().splitlines()[0] if str(e).strip() else repr(e), 200)


#: DuckDB settings that change what a query means: queries run while one is
#: set are skipped, and so are those under `default_null_order` (`Replay.probe_lift`).
SEMANTIC = {
    "binary_as_string", "calendar", "current_dialect", "default_collation", "default_order",
    "dialect_compatibility_mode", "disable_timestamptz_casts", "error_on_division_by_zero",
    "ieee_floating_point_ops", "integer_division", "legacy_disable_null_type", "null_order",
    "old_implicit_casting", "order_by_non_integer_literal", "preserve_identifier_case",
    "regex_match_operator_semantics", "scalar_subquery_error_on_multiple_rows", "schema",
    "search_path", "sqlite_all_varchar", "timezone", "variable",
}  # fmt: skip

#: Statements after which a name no longer means what the lift takes it to:
#: a collation, a macro or function named like a builtin, a user type.
_REDEFINES = re.compile(
    r"\bCOLLATE\b|\bCREATE\s+(OR\s+REPLACE\s+)?(TEMP\w*\s+)?(MACRO|FUNCTION|TYPE)\b", re.I
)

_SETTING = re.compile(
    r"^\s*(SET|PRAGMA|RESET)\s+(?:(?:GLOBAL|SESSION|LOCAL)\s+)?(\w+)\s*(?:(?:=|TO)\s*(.*?))?\s*;?\s*$",
    re.I | re.S,
)

#: DuckDB errors from reading the query, not from running it.
_FRONTEND = tuple(
    f"error: {k} Error"
    for k in ("Binder", "Parser", "Catalog", "Not implemented", "Dependency", "Syntax")
)

_PROBE = re.compile(r"^\s*(\(\s*)*(SELECT|WITH|VALUES|FROM|TABLE)\b", re.I)


_DML = re.compile(r"\b(INSERT|UPDATE|DELETE|MERGE)\b", re.I)


def _modifies(sql: str) -> str | None:
    """The statement that modifies data inside a query, such as an INSERT in
    a CTE (#318), or None."""
    import sqlglot as sg

    if not _DML.search(sql):
        return None  # most queries: no need to parse
    try:
        tree = sg.parse_one(sql, read="duckdb")
    except (sg.errors.SqlglotError, RecursionError):
        return None  # the lift says why, as for any query
    found = tree.find(sg.exp.Insert, sg.exp.Update, sg.exp.Delete, sg.exp.Merge)
    return None if found is None else found.key.upper()


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

    def sync(self, tables: Iterable[str], cap: int | None = MAX_ROWS) -> dict[str, list[tuple]]:
        """Mirror the DuckDB tables (and views, as tables) a query reads.
        Returns their rows, for inlining. Raises `OverflowError` past `cap`
        rows in all."""
        from sverify.engine import table_rows

        known = {
            r[0]
            for r in self.db.sql(
                "SELECT table_name FROM duckdb_tables() WHERE schema_name = 'main' "
                "UNION SELECT view_name FROM duckdb_views() "
                "WHERE schema_name = 'main' AND NOT internal"
            ).fetchall()
        }
        # DuckDB's identifiers are case-insensitive; the lift lowercases
        # unquoted ones.
        lower = {k.lower(): k for k in known}
        for name in list(self.con.arrow):
            if name != ONE and name.lower() not in lower:
                self.con.drop(name)  # dropped or renamed in DuckDB
                self.synced.pop(name, None)
        rows: dict[str, list[tuple]] = {}
        for ref in tables:
            name = lower.get(ref.lower())
            if ref == ONE or name is None:
                continue
            if self.synced.get(name) != self.version:
                table = self.arrow(f'SELECT * FROM "{name}"')
                if cap is not None and table.num_rows > cap:
                    n = table.num_rows
                    raise OverflowError(f"table {name} has {n} rows, more than {cap}")
                for alias in {name, name.lower()}:
                    self.con.put(alias, table)
                self.synced[name] = self.version
            for alias in {name, name.lower()}:
                rows[alias] = table_rows(self.con, name)
        total = sum(len(rows[n]) for n in {lower[r.lower()] for r in tables if r.lower() in lower})
        if cap is not None and total > cap:
            raise OverflowError(f"the query reads {total} rows, more than {cap}")
        rows[ONE] = [(0,)]
        return rows

    def condense(
        self, rec: Record, tables: list[str]
    ) -> tuple[dict[str, list[tuple]], Callable[[Any, Any, bool], bool]]:
        """For a query reading more than `MAX_ROWS` rows: the first rows of
        each table, `MAX_ROWS` in all, mirrored in place of the full ones,
        and an outcome that compares with DuckDB's result on them (oracle A on
        less data) rather than with the test's, which was for the full ones."""
        from sverify.engine import table_rows

        full = self.sync(tables, cap=None)
        names = sorted({n for n in self.con.arrow if n != ONE and n in full})
        distinct = sorted({n.lower() for n in names})
        keep = max(1, MAX_ROWS // max(1, len(distinct)))
        con = duckdb.connect()
        for name in names:
            small = self.con.arrow[name].slice(0, keep)
            self.con.put(name, small)
            self.synced.pop(name, None)  # the next query mirrors the full table again
            con.register(name, small)
        rows = {name: table_rows(self.con, name) for name in names}
        rows[ONE] = [(0,)]
        try:
            rel = con.sql(rec.sql)
            want, want_err = self.fmt.rows(rel.to_arrow_table() if rel else pa.table({})), None
        except Exception as e:  # noqa: BLE001 - DuckDB's error is a result
            want, want_err = None, _error(e)

        def outcome(got: Any, err: Any, ordered: bool) -> bool:
            if want_err is not None:
                return err is not None
            return err is None and _same_bag(got or [], want or [], ordered)

        return rows, outcome

    def statement(self, rec: Record) -> None:
        try:
            self.run(rec.sql)
            ok = True
        except duckdb.Error:
            ok = False
        self.version += 1
        if ok and _REDEFINES.search(rec.sql):
            self.settings.add("collation or macro")
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

        if (dml := _modifies(rec.sql)) is not None:
            # DuckDB ran it above, so the state stays the test's.
            res.reason = f"modifies data ({dml} in a query), outside sverify's scope"
            return res
        if self.settings or _REDEFINES.search(rec.sql):
            res.reason = "setting " + ", ".join(sorted(self.settings or {"collation"}))
            return res
        if expect_error and ddb_err and ddb_err.startswith(_FRONTEND):
            # DuckDB's binder or parser, not what the query computes.
            res.reason = "DuckDB frontend error"
            return res
        return self.probe_lift(rec, res, outcome, ddb_rows, ddb_err)

    def probe_lift(
        self,
        rec: Record,
        res: Result,
        outcome: Any,
        ddb_rows: list[list[str]] | None,
        ddb_err: str | None,
    ) -> Result:
        """The rest of `probe`: the query through the SQLGlot lift
        (`sverify.sql_lift`), DuckDB's SQL as it is, with DuckDB's semantics."""
        import ibis
        import sqlglot as sg

        from sverify.sql_lift import expand_table_shorthand, lift

        if self.null_order != "nulls_last":
            res.reason = "setting default_null_order"
            return res
        try:
            tree = sg.parse_one(expand_table_shorthand(rec.sql), read="duckdb")
        except sg.errors.ParseError as e:
            res.cls, res.reason = "refused", f"lift: cannot parse ({_clip(str(e), 100)})"
            return res
        tables = sorted({t.name for t in tree.find_all(sg.exp.Table) if t.name})
        ordered = (
            isinstance(tree, sg.exp.Select | sg.exp.SetOperation)
            and tree.args.get("order") is not None
        )
        if not outcome(ddb_rows, ddb_err, ordered):
            res.reason = "DuckDB's own result differs from the expected one"
            return res
        try:
            rows = self.sync(tables)
        except OverflowError:
            # Too much data to inline (#357): the query on the tables'
            # first rows, against DuckDB's result on those.
            rows, outcome = self.condense(rec, tables)
            res.reason = f"condensed to {MAX_ROWS} rows"
        except Exception as e:  # noqa: BLE001 - a type Arrow or sverify cannot hold
            res.cls, res.reason = "refused", f"tables: {_clip(str(e), 200)}"
            return res
        lower = {n.lower(): n for n in self.con.arrow}
        schemas = {
            t: ibis.Schema.from_pyarrow(self.con.arrow[lower[t.lower()]].schema)
            for t in tables
            if t.lower() in lower
        }
        try:
            lifted = lift(rec.sql, schemas, "duckdb")
        except Exception as e:  # noqa: BLE001 - the lift refusing (or failing: recorded)
            kind = "" if type(e).__name__ == "Unsupported" else f"{type(e).__name__}: "
            res.cls, res.reason = "refused", f"lift: {kind}{_clip(str(e), 200)}"
            return res
        plan = json.dumps(lifted.plan)
        schema = lifted.schema.to_pyarrow()
        return self.judge(
            rec,
            res,
            plan,
            schema,
            rows,
            ordered,
            outcome,
            functools.partial(_lift_issues, rec.sql, schemas),
        )

    def judge(
        self,
        rec: Record,
        res: Result,
        plan: str,
        schema: pa.Schema,
        rows: dict[str, list[tuple]],
        ordered: bool,
        outcome: Any,
        issues: Any,
    ) -> Result:
        """Check `plan` and compare Lean's and the engine's results with the
        expected ones."""
        from sverify.engine import run_checker, run_plan, written_plan
        from sverify.testing import lean_values

        expect_error = rec.expect == "error"
        code, out, err = run_checker((), plan)
        if code != 0 or "well-formed: yes" not in out:
            res.cls, res.reason = "refused", f"checker: {_clip((err or out).strip()[-200:], 200)}"
            return res

        # Lean on the plan with the tables inlined.
        lean_err = None
        lean_rows: list[list[str]] = []
        try:
            inlined = _typed_inline(json.loads(plan), rows, self.con)
        except TypeError as e:
            # A struct, decimal, blob, …: `sverify.testing.literal` has none.
            res.cls, res.reason = (
                "refused",
                f"tables: no Lean literal for a value ({_clip(str(e), 60)})",
            )
            return res
        try:
            values = lean_values(json.dumps(inlined))
            lean_rows = self.fmt.rows(_as_table(values, schema))
            res.lean = _show(lean_rows)
        except subprocess.CalledProcessError as e:
            lean_err = "error: " + _clip(((e.stderr or "") + (e.output or "")).strip()[-200:], 200)
        except Exception as e:  # noqa: BLE001 - recorded
            lean_err = _error(e)
        if lean_err is not None:
            res.lean = lean_err
            if "not evaluated" in lean_err:
                # A black box (`Main.check`): Lean knows no rows to compare.
                res.cls, res.reason = "refused", "checker: rows not evaluated (a black box)"
                return res
        lean_ok = outcome(lean_rows, lean_err, ordered)
        if expect_error and not lean_ok and (found := issues()):
            # Not an agreement (`Rel.eval` gives rows), but the verifier warns.
            res.reason = "verify: " + _clip("; ".join(found), 200)

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
        elif lean_ok and "overflow to infinity" in (res.engine or ""):
            # DuckDB gives `±inf`, which `Rel.eval` keeps; the reference raises
            # there and the written plan checks it on the data (#575).
            res.cls, res.side = "disagree", "engine"
            res.reason = "reference: an overflow to ±inf raises (#575)"
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


def _lift_issues(sql: str, schemas: dict[str, Any]) -> list[str]:
    """The runtime errors and wrap-arounds `verify` cannot rule out, the
    `SUM`s it assumes fit among them (#316). The SQL text goes to `verify` as
    it is: `sverify.sql` refuses a query that reads no table, which hid
    `SELECT 7 // 0`'s division by zero (#333)."""
    from sverify.contracts import verify

    try:
        report = verify(sql, tables=schemas)
    except Exception:  # noqa: BLE001
        return []
    return [str(i) for i in report.issues + report.assumed]


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


def _nested(v: Any, t: pa.DataType) -> Any:
    """Lean's value of a nested type for Arrow: a struct is the list of its
    fields in the model (`docs/nested-values.md`), a dict by name in Arrow."""
    if v is None:
        return None
    if pa.types.is_struct(t) and isinstance(v, list):
        return {t.field(k).name: _nested(x, t.field(k).type) for k, x in enumerate(v)}
    if (pa.types.is_list(t) or pa.types.is_large_list(t)) and isinstance(v, list):
        return [_nested(x, t.value_type) for x in v]
    return v


def _as_table(values: list[tuple], schema: pa.Schema) -> pa.Table:
    """Lean's values as a table of the lifted plan's output schema: timestamps
    and dates come back as integer codes."""
    from sverify.testing import EPOCH

    cols = []
    for i, f in enumerate(schema):
        col = [r[i] for r in values]
        t = f.type
        try:
            if pa.types.is_timestamp(t):
                col = [None if v is None else EPOCH + dt.timedelta(microseconds=v) for v in col]
                t = pa.timestamp("us", t.tz)
            elif pa.types.is_date(t):
                col = [None if v is None else EPOCH.date() + dt.timedelta(days=v) for v in col]
                t = pa.date32()
            elif pa.types.is_time(t):
                # Microseconds since midnight.
                col = [
                    None if v is None else (dt.datetime.min + dt.timedelta(microseconds=v)).time()
                    for v in col
                ]
                t = pa.time64("us")
            elif pa.types.is_duration(t):
                col = [None if v is None else dt.timedelta(microseconds=v) for v in col]
                t = pa.duration("us")
            elif pa.types.is_interval(t):
                # The model's intervals are microseconds.
                col = [
                    None
                    if v is None
                    else pa.scalar((0, 0, v * 1000), pa.month_day_nano_interval()).as_py()
                    for v in col
                ]
            elif pa.types.is_string(t) or pa.types.is_large_string(t) or pa.types.is_string_view(t):
                t = pa.string()
            elif pa.types.is_struct(t) or pa.types.is_list(t) or pa.types.is_large_list(t):
                col = [_nested(v, t) for v in col]
            arr = pa.array(col, t)
            if pa.types.is_integer(t) and any(isinstance(v, float) for v in col):
                raise TypeError("a double in an integer column")
            cols.append(arr)
        except (pa.ArrowInvalid, pa.ArrowTypeError, OverflowError, TypeError):
            # A value outside the type (an unbounded integer, …): as text.
            cols.append(pa.array([None if v is None else str(v) for v in col], pa.string()))
    return pa.table(cols, names=[f"c{i}" for i in range(len(cols))])


def replay_file(path: Path, rel: str) -> tuple[list[Result], str | None]:
    """The results of one test file, and why it was skipped (if it was)."""
    tf = parse(path.read_text(errors="replace"))
    if tf.skip:
        return [], tf.skip
    if os.environ.get("SVERIFY_SLT_PROGRESS"):
        # Which file a worker is on: a replay that hangs names it.
        print(f"replaying: {rel}", flush=True)
    # A new process database for each file: a DuckDB `FATAL` error
    # invalidates a database for good, and every file a worker replayed
    # after it would fail, which ones depending on scheduling (#407).
    from sverify import _duckdb

    _duckdb.reset()
    with tempfile.TemporaryDirectory(prefix="sverify-slt-") as tmp:
        return _replay(tf, rel, tmp), None


#: How long one query may keep the checker busy, in seconds. Past it the replay
#: kills the checker (Lean evaluating a plan that does not finish on a test's
#: few rows), records the query as skipped with the reason, and goes on.
CHECK_TIMEOUT = 120
#: A query slower than this (seconds) is logged as slow (not in the ledger,
#: whose contents stay the same from run to run): leads on checker performance.
SLOW = 10


@contextlib.contextmanager
def _watchdog(seconds: float) -> Iterator[list[bool]]:
    """Kill the checker if the block runs longer than `seconds`; yields a flag
    that says whether it did."""
    from sverify import engine

    fired = [False]

    def kill() -> None:
        fired[0] = True
        if (proc := engine._CHECKER.proc) is not None:
            proc.kill()

    timer = threading.Timer(seconds, kill)
    timer.daemon = True
    timer.start()
    try:
        yield fired
    finally:
        timer.cancel()


def _replay(tf: TestFile, rel: str, tmp: str) -> list[Result]:
    rp = Replay(rel)
    results: list[Result] = []
    for rec in tf.records:
        # Files a test writes go to a temporary directory.
        for key in ("__TEST_DIR__", "{TEST_DIR}", "{TEMP_DIR}"):
            rec.sql = rec.sql.replace(key, tmp)
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
            start = time.monotonic()
            with _watchdog(CHECK_TIMEOUT) as fired:
                res = rp.probe(rec)
            if (took := time.monotonic() - start) > SLOW:
                print(f"slow: {rel}:{rec.line} {took:.0f} s {_clip(rec.sql, 150)!r}", flush=True)
            if fired[0]:
                res.cls, res.side = "skipped", None
                res.reason = f"harness: the checker took over {CHECK_TIMEOUT} s"
            results.append(res)
        except (KeyboardInterrupt, SystemExit):
            raise
        except BaseException as e:  # noqa: BLE001 - the harness goes on (a crash in a native library, …)
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
    return results


def _replay_one(args: tuple[str, str]) -> tuple[str, list[dict], str | None]:
    path, rel = args
    try:
        results, skip = replay_file(Path(path), rel)
    except (KeyboardInterrupt, SystemExit):
        raise
    except BaseException as e:  # noqa: BLE001
        return rel, [], f"harness: {_error(e)}"
    return rel, [asdict(r) for r in results], skip


# --- ledger --------------------------------------------------------------------------

CLASSES = ("agree", "disagree", "refused", "skipped")


#: The fields a ledger keeps of a refused or skipped query: what and why.
_BRIEF = ("file", "line", "sql", "cls", "reason")


def _compact(r: dict) -> dict:
    """A result as the ledger keeps it: all three results of a query that
    ran, the reason alone of one that did not; long values clipped."""
    keep = r if r["cls"] in ("agree", "disagree") else {k: r.get(k) for k in _BRIEF}
    n = 300 if r["cls"] == "disagree" else 120
    return {
        k: _clip(v, n) if isinstance(v, str) and k != "file" else v
        for k, v in keep.items()
        if v not in (None, "")
    }


def write_ledger(
    area: str,
    version: str,
    results: list[dict],
    skipped_files: dict[str, str],
    out: Path = REPLAY_DIR,
    head: dict | None = None,
) -> Path:
    """`<out>/<area>.json`: one result per line, sorted by file and line.
    `head` adds to (or replaces) the keys before the results."""
    out.mkdir(parents=True, exist_ok=True)
    results = sorted(results, key=lambda r: (r["file"], r["line"]))
    counts = Counter(r["cls"] for r in results)
    sides = Counter(r["side"] for r in results if r["cls"] == "disagree")
    # Agreements where the written plan was refused: Lean's rows matched
    # DuckDB's (oracle A), but no engine ran the plan back (oracle C).
    oracle_a = _oracle_a_only(results)
    head = {
        **{
            "duckdb": version,
            "source": source(version),
            "license": "test/sql © Stichting DuckDB Foundation, MIT (LICENSE-duckdb)",
            "area": area,
            "summary": {c: counts.get(c, 0) for c in CLASSES},
            "agree_oracle_a_only": oracle_a,
            "disagree_sides": dict(sorted(sides.items())),
            "skipped_files": dict(sorted(skipped_files.items())),
        },
        **(head or {}),
    }
    path = out / f"{area.replace('/', '__')}.json"
    lines = ["{"]
    for k, v in head.items():
        if v is None:
            continue
        lines.append(f"  {json.dumps(k)}: {json.dumps(v, sort_keys=True)},")
    lines.append('  "results": [')
    body = ["    " + json.dumps(_compact(r), ensure_ascii=False) for r in results]
    lines.append(",\n".join(body))
    lines.append("  ]")
    lines.append("}")
    path.write_text("\n".join(lines) + "\n")
    return path


def _oracle_a_only(results: list[dict]) -> int:
    """The agreements no engine ran back: the writer refused the plan."""
    return sum(
        1
        for r in results
        if r["cls"] == "agree" and str(r.get("engine") or "").startswith("refused")
    )


def write_summary(out: Path = REPLAY_DIR) -> Path:
    """`<out>/README.md`'s table, from every ledger in `out`."""
    rows = []
    for p in sorted(out.glob("*.json")):
        led = json.loads(p.read_text())
        if "summary" not in led:
            continue  # not a ledger (`probes.json`)
        s = led["summary"]
        reasons = Counter(
            (r.get("reason") or "").split(":")[0] for r in led["results"] if r["cls"] == "refused"
        )
        top = ", ".join(f"{k} {n}" for k, n in reasons.most_common(2))
        d = led.get("disagree_sides", {})
        sides = ", ".join(f"{k} {n}" for k, n in sorted(d.items()))
        rows.append(
            f"| [{led['area']}]({p.name}) | {s['agree']} | {_oracle_a_only(led['results'])} "
            f"| {s['disagree']} | {sides} "
            f"| {s['refused']} | {s['skipped']} | {len(led['skipped_files'])} | {top} |"
        )
    path = out / "README.md"
    text = path.read_text() if path.exists() else ""
    table = "\n".join(
        [
            "<!-- slt:start -->",
            "| Area | Agree | Oracle A only | Disagree | Disagree side | Refused | Skipped "
            "| Files skipped | Refused by |",
            "|---|---:|---:|---:|---|---:|---:|---:|---|",
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


#: How long one test file may take, in seconds. Past it the replay stops the
#: file's worker and records the file as skipped (`timeout: …`): a hang, or a
#: test slow by design, then shows by name instead of stalling the run.
FILE_TIMEOUT = 300


def _worker(conn: Connection) -> None:
    """Replay the files `conn` sends until it sends None. The worker leads a
    process group of its own, so that stopping it stops its checker too."""
    os.setsid()
    while (task := conn.recv()) is not None:
        conn.send(_replay_one(task))


def _start_worker(ctx: Any) -> tuple[Connection, Any]:
    here, there = ctx.Pipe()
    proc = ctx.Process(target=_worker, args=(there,), daemon=True)
    proc.start()
    there.close()
    return here, proc


def _stop_worker(conn: Connection, proc: Any) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(proc.pid, signal.SIGKILL)
    proc.join()
    conn.close()


def replay_files(
    files: list[tuple[str, str]], jobs: int, timeout: float = FILE_TIMEOUT
) -> Iterator[tuple[str, list[dict], str | None]]:
    """`_replay_one` on each file, in `jobs` worker processes, one file at a
    time each. A file whose worker dies (a crash in a native library) or that
    takes over `timeout` seconds is skipped, with the reason, and its worker
    replaced; the others go on."""
    ctx = multiprocessing.get_context("spawn")
    todo = list(reversed(files))
    idle = [_start_worker(ctx) for _ in range(min(jobs, len(files)))]
    busy: dict[Connection, tuple[Any, tuple[str, str], float]] = {}
    try:
        while todo or busy:
            while idle and todo:
                conn, proc = idle.pop()
                task = todo.pop()
                conn.send(task)
                busy[conn] = (proc, task, time.monotonic())
            due = min(start + timeout for _, _, start in busy.values())
            ready = mp_connection.wait(list(busy), max(0.0, due - time.monotonic()))
            for conn in cast(list[Connection], ready):
                proc, task, _ = busy.pop(conn)
                try:
                    out = conn.recv()
                except EOFError:
                    _stop_worker(conn, proc)
                    idle.append(_start_worker(ctx))
                    yield task[1], [], "harness: the replay process crashed"
                    continue
                idle.append((conn, proc))
                yield out
            now = time.monotonic()
            for conn, (proc, task, start) in list(busy.items()):
                if now - start >= timeout:
                    del busy[conn]
                    _stop_worker(conn, proc)
                    idle.append(_start_worker(ctx))
                    yield task[1], [], f"timeout: the file took over {timeout:.0f} s"
    finally:
        for conn, _ in idle:
            with contextlib.suppress(OSError):
                conn.send(None)
        for conn, (proc, _, _) in busy.items():
            _stop_worker(conn, proc)
        for conn, proc in idle:
            proc.join(timeout=5)
            if proc.is_alive():
                _stop_worker(conn, proc)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("areas", nargs="*", help="areas under test/sql (default: all)")
    parser.add_argument("--version", help="DuckDB version (default: uv.lock's)")
    parser.add_argument("--out", type=Path, default=REPLAY_DIR)
    parser.add_argument("--jobs", type=int, default=2, help="processes (default 2)")
    parser.add_argument("--resume", action="store_true", help="skip areas with a ledger")
    args = parser.parse_args(argv)
    version = args.version or duckdb_version()
    root = fetch(version)
    for area, files in test_files(root, args.areas).items():
        path = args.out / f"{area.replace('/', '__')}.json"
        if args.resume and path.exists():
            continue
        results: list[dict] = []
        skipped: dict[str, str] = {}
        for rel, res, skip in replay_files(files, args.jobs):
            results += res
            if skip:
                skipped[rel] = skip
        path = write_ledger(area, version, results, skipped, args.out)
        counts = Counter(r["cls"] for r in results)
        print(f"{area}: {dict(counts)} ({len(skipped)} files skipped) -> {path}", flush=True)
    write_summary(args.out)


if __name__ == "__main__":
    main()
