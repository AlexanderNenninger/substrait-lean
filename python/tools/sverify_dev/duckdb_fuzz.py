"""Fuzz DuckDB's own SQL against Lean's semantics, for DuckDB's engine
profile (epic #185).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

`sverify_dev.fuzz` checks the engines on the plans Lean writes, guards
included. Characterizing DuckDB needs DuckDB's semantics instead: here each
random query of `sverify_dev.fuzz` (DuckDB's SQL) runs on DuckDB, natively,
and its rows (or its error) are compared with `Rel.eval`'s on the plan
sverify's lift (`sverify.sql_lift`) writes for it, with DuckDB's semantics.

A `Target` aims the fuzzer at one area of the replay's disagreements: the
integer values the tables hold (boundaries, zero), the integer literals,
and the expression kinds drawn. `python -m sverify_dev.duckdb_fuzz <target>`
runs one target for a budget and writes its findings as a ledger in the
format of `sverify_dev.slt` (`characterization/duckdb/fuzz__<target>.json`).

This module needs Hypothesis, which only the `dev` group installs.
"""

from __future__ import annotations

import argparse
import contextlib
import json
import math
import random
import re
import subprocess
import sys
import time
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import duckdb
import ibis
from hypothesis import HealthCheck, find, settings
from hypothesis import strategies as st
from hypothesis.errors import NoSuchExample

from sverify_dev import fuzz, slt
from sverify_dev.fuzz import BOOL, DOUBLE, INT

I64 = 2**63


@dataclass(frozen=True)
class Target:
    ints: list[int | None]
    """Integer values the tables hold."""
    literals: list[str]
    """Integer literals in expressions."""
    kinds: dict[str, list[str]] = field(default_factory=dict)
    """Expression kinds by type (`sverify_dev.fuzz._KINDS`), replacing the defaults."""
    doubles: list[float | None] | None = None
    """Double values the tables hold; `sverify_dev.fuzz`'s when `None`."""
    double_literals: list[str] | None = None
    """Double literals in expressions; `sverify_dev.fuzz`'s when `None`."""


_BOUNDS = [I64 - 1, -I64, 2**31 - 1, -(2**31), 2**31, 2**32, 3037000500]
TARGETS = {
    # 64-bit overflow of + - * and negation, and abs(minimum).
    "int_overflow": Target(
        ints=[None, 0, 1, -1, 2, *_BOUNDS],
        literals=["1", "-1", "2", str(I64 - 1), str(-I64 + 1), "3037000500"],
        kinds={INT: ["arith", "neg", "abs"], BOOL: ["cmp", "isnull"]},
    ),
    # Integer division and modulus: by zero, truncation, minimum / -1.
    "int_division": Target(
        ints=[None, 0, 0, 1, -1, 2, -2, 7, -7, I64 - 1, -I64],
        literals=["0", "1", "-1", "2", "-2", "7", "CAST(NULL AS BIGINT)"],
        kinds={INT: ["arith", "coalesce", "nullif"], BOOL: ["cmp", "isnull"]},
    ),
    # Double arithmetic over NaN, ±∞ and zero, with integers cast to doubles.
    "float_arith": Target(
        ints=[None, 0, 1, -1, 2, 2**53 + 1],
        literals=["0", "1", "-1", "2"],
        kinds={DOUBLE: ["arith", "neg", "abs", "cast_int"], BOOL: ["cmp", "isnull"]},
    ),
    # Evaluation order (`execution.evaluation_order`, #604): integer division
    # and overflow that raise inside CASE, AND, OR, COALESCE and NULLIF, on
    # rows a branch or the other operand excludes.
    "eval_order": Target(
        ints=[None, 0, 0, 1, -1, 2, 7, I64 - 1, -I64],
        literals=["0", "1", "-1", "2", str(I64 - 1)],
        kinds={
            INT: ["arith", "case", "coalesce", "nullif"],
            BOOL: ["cmp", "logic", "logic", "not", "isnull", "case"],
        },
    ),
    # Double specials (`zero_sign`, `nan_kind`, `nan_creation`, `nan_order`,
    # rounding near the limits): ±0, NaN, ±∞, the largest and a subnormal.
    "float_special": Target(
        ints=[None, 0, 1, -1],
        literals=["0", "1"],
        kinds={
            DOUBLE: ["arith", "neg", "abs", "case", "coalesce"],
            BOOL: ["cmp", "isnull", "logic"],
        },
        doubles=[None, 0.0, -0.0, 1.0, -1.0, 0.1, math.inf, -math.inf, math.nan, 1.7e308, 5e-324],
        double_literals=[
            "0.0::DOUBLE",
            "-0.0::DOUBLE",
            "'nan'::DOUBLE",
            "'inf'::DOUBLE",
            "1e308::DOUBLE",
            "0.1::DOUBLE",
            "CAST(NULL AS DOUBLE)",
        ],
    ),
}


@contextlib.contextmanager
def aimed(target: Target) -> Iterator[Any]:
    """`sverify_dev.fuzz`'s strategies drawing `target`'s values, for the block:
    yields the strategy of (query, tables) cases."""
    saved = (
        fuzz.VALUES[INT], fuzz.LITERALS[INT], fuzz.VALUES[DOUBLE], fuzz.LITERALS[DOUBLE],
        dict(fuzz._KINDS),
    )  # fmt: skip
    fuzz.VALUES[INT] = st.sampled_from(target.ints)
    fuzz.LITERALS[INT] = st.sampled_from(target.literals)
    if target.doubles is not None:
        fuzz.VALUES[DOUBLE] = st.sampled_from(target.doubles)
    if target.double_literals is not None:
        fuzz.LITERALS[DOUBLE] = st.sampled_from(target.double_literals)
    fuzz._KINDS.update(target.kinds)
    try:
        tables = st.fixed_dictionaries({name: fuzz.rows_of(name) for name in fuzz.TABLES})
        yield st.tuples(fuzz.queries(), tables)
    finally:
        fuzz.VALUES[INT], fuzz.LITERALS[INT], fuzz.VALUES[DOUBLE], fuzz.LITERALS[DOUBLE] = saved[:4]
        fuzz._KINDS.clear()
        fuzz._KINDS.update(saved[4])


#: The DuckDB settings that change what the fuzzed queries compute, recorded
#: in each ledger (#619): a ledger of 2026-11-01 ran with `integer_division`
#: on, which made `d / d` of doubles a `//`.
SETTINGS = (
    "integer_division",
    "ieee_floating_point_ops",
    "error_on_division_by_zero",
    "default_null_order",
    "default_order",
)


def settings_of(db: duckdb.DuckDBPyConnection) -> dict[str, Any]:
    """`SETTINGS` on the connection `check` runs DuckDB on."""
    return {name: db.sql(f"SELECT current_setting('{name}')").fetchall()[0][0] for name in SETTINGS}


def connect() -> duckdb.DuckDBPyConnection:
    """The connection `check` runs each query on: DuckDB's defaults."""
    return duckdb.connect()


@dataclass
class Outcome:
    sql: str
    tables: dict[str, list[tuple]]
    lean: str
    duckdb: str
    agree: bool
    issues: list[str]


def _rows(rows: list[tuple]) -> str:
    return slt._clip(json.dumps([list(map(_text, r)) for r in rows]))


def _text(v: object) -> str:
    return "NULL" if v is None else str(v)


def _same_rows(a: list[tuple], b: list[tuple], ordered: bool) -> bool:
    """`sverify_dev.fuzz.same_rows`, which cannot sort integers past a double's
    range (Lean's unbounded ones): those compare exactly."""
    try:
        return fuzz.same_rows(a, b, ordered)
    except OverflowError:
        x, y = list(map(repr, a)), list(map(repr, b))
        return x == y if ordered else sorted(x) == sorted(y)


def kind(o: Outcome) -> str:
    """The behaviour a disagreement shows, for keeping one finding of each:
    DuckDB's error without its operands, or that the rows differ."""
    if o.duckdb.startswith("error: "):
        return re.sub(r"[\s(]*\(.*|\d+", "", o.duckdb)[:80]
    return "Lean errs" if o.lean.startswith("error: ") else "rows differ"


def check(query: fuzz.Query, tables: dict[str, list[tuple]]) -> Outcome:
    """Lean against DuckDB on one query and input.

    Raises `sverify_dev.fuzz.Refused` when the query is outside the model or
    DuckDB cannot read it."""
    s = fuzz.Session(tables)
    plan = s.plan(query.sql)
    lean_rows: list[tuple] | None = None
    try:
        lean_rows = s.lean(plan)
        lean = _rows(lean_rows)
    except subprocess.CalledProcessError as e:
        lean = "error: " + slt._clip(((e.stderr or "") + (e.output or "")).strip()[-200:], 200)
    db = connect()
    for name, table in s.con.arrow.items():
        db.register(name, table)
    duck_rows: list[tuple] | None = None
    try:
        duck_rows = db.sql(query.sql).fetchall()
        duck = _rows(duck_rows)
    except duckdb.ParserException as e:
        raise fuzz.Refused(f"duckdb: {e}") from e
    except duckdb.BinderException as e:
        raise fuzz.Refused(f"duckdb: {e}") from e
    except duckdb.Error as e:
        duck = slt._error(e)
    if lean_rows is None or duck_rows is None:
        agree = lean_rows is None and duck_rows is None
    else:
        agree = _same_rows(lean_rows, duck_rows, query.ordered)
    schemas = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in s.con.arrow.items()}
    issues = [] if agree else slt._lift_issues(query.sql, schemas)
    return Outcome(query.sql, s.tables, lean, duck, agree, issues)


def search(target: str, budget: float, seed: int = 0) -> tuple[list[Outcome], int]:
    """Distinct, shrunk disagreements within `budget` seconds, and the
    number of cases checked."""
    rng = random.Random(seed)
    deadline = time.monotonic() + budget
    found: dict[str, Outcome] = {}
    checked = [0]
    cfg = settings(
        max_examples=200, database=None, deadline=None, suppress_health_check=list(HealthCheck)
    )

    def outcome(case: tuple) -> Outcome | None:
        try:
            out = check(*case)
        except fuzz.Refused:
            return None
        except Exception as e:  # noqa: BLE001 - a harness error is not a finding
            print(f"harness: {e!r}", file=sys.stderr)
            return None
        checked[0] += 1
        return out

    def new(case: tuple) -> bool:
        out = outcome(case)
        return out is not None and not out.agree and kind(out) not in found

    with aimed(TARGETS[target]) as cases:
        while time.monotonic() < deadline:
            try:
                case = find(cases, new, settings=cfg, random=random.Random(rng.random()))
            except NoSuchExample:
                continue
            out = outcome(case)
            if out is not None and not out.agree:
                found.setdefault(kind(out), out)
                print(
                    f"{out.sql}\n  {out.tables}\n  lean:   {out.lean}\n  duckdb: {out.duckdb}\n",
                    flush=True,
                )
    return list(found.values()), checked[0]


def write(target: str, version: str, found: list[Outcome], checked: int, out: Path) -> Path:
    """The findings as a ledger in `sverify_dev.slt`'s format: each finding a
    `disagree` result whose `file` is `fuzz:<target>`."""
    results = [
        {
            "file": f"fuzz:{target}",
            "line": i,
            "sql": o.sql,
            "tables": {k: [list(map(_text, r)) for r in v] for k, v in o.tables.items() if v},
            "expected": "",
            "duckdb": o.duckdb,
            "lean": o.lean,
            "engine": "",
            "cls": "disagree",
            "side": "lean",
            "reason": "verify: " + "; ".join(o.issues) if o.issues else None,
        }
        for i, o in enumerate(sorted(found, key=lambda o: (len(o.sql), o.sql)))
    ]
    summary = {"agree": checked - len(found), "disagree": len(found), "refused": 0, "skipped": 0}
    source = "sverify_dev.duckdb_fuzz (generated queries, no DuckDB tests)"
    head = {
        "source": source,
        "license": None,
        "summary": summary,
        "checked": checked,
        "settings": settings_of(connect()),
    }
    path = slt.write_ledger(f"fuzz/{target}", version, results, {}, out, head)
    return path


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("target", choices=sorted(TARGETS))
    parser.add_argument("--budget", type=float, default=60.0, help="seconds (default 60)")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--out", type=Path, default=slt.REPLAY_DIR)
    args = parser.parse_args(argv)
    found, checked = search(args.target, args.budget, args.seed)
    path = write(args.target, duckdb.__version__, found, checked, args.out)
    print(f"{len(found)} distinct finding(s) in {checked} cases -> {path}")


if __name__ == "__main__":
    main()
