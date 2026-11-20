"""Replay Ibis's own backend tests through sverify (#860).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Ibis's backend test suite (`ibis/backends/tests`, Apache-2.0) runs Ibis
expressions on each backend and compares the results with what Ibis's
developers expect. This module runs the suite on Ibis's DuckDB backend at
the Ibis release `python/uv.lock` pins (`IBIS_TAG`), with Ibis's test data
(`DATA_COMMIT`), and loads itself as a pytest plugin (`-p
sverify_dev.ibis_replay`). Every expression a test executes
(`Backend.execute`, `to_pyarrow`) is also verified by sverify and run on
DuckDB through sverify, and the rows are compared with Ibis's own. A test
that passes on DuckDB holds Ibis's expected result, so Ibis's rows are the
oracle. Each test is

* `agree`: every expression it executes is proved and gives Ibis's rows;
* `disagree`: an expression is proved and gives other rows (`side:
  "rows"`), or its run fails with an error that is no refusal (`side:
  "run"`); each is a soundness question: a fix, an issue or an engine fact;
* `refused`: sverify refuses an expression, in `verify` or, for a proved
  plan, on the way to DuckDB (`run:`); `construct` names it as the refusal
  does;
* `unproved`: sverify reads the expression but does not prove it, after
  verifying again with the preconditions it suggests
  (`Report.suggested_requires`), as a user would; `reason` says why;
* `skipped`: the test does not pass on DuckDB itself (Ibis's own xfails
  and errors), or it executes nothing the replay reads (a parameter, a
  limit).

A run that refuses Ibis's data for its preconditions is `unproved`, with the
precondition as its reason.

`python -m sverify_dev.ibis_replay` fetches the suite and the data (into
`~/.cache/sverify/ibis-replay`), replays the modules (`MODULES`, or those
named), prints the totals and with `--write` rewrites the ledgers
`python/tests/ibis_replay/<module>.json`, keeping each disagreement's and
each refusal's `issue`. `--check` fails on a new disagreement and on a
test that agreed and no longer does; other changes only print.
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import datetime as dt
import decimal
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import warnings
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[3]
LEDGERS = ROOT / "python" / "tests" / "ibis_replay"
IBIS_REPO = "https://github.com/ibis-project/ibis"
#: The release `python/uv.lock` resolves `ibis-framework` to.
IBIS_TAG = "12.0.0"
DATA_REPO = "https://github.com/ibis-project/testing-data"
#: `ibis-project/testing-data`'s master, which Ibis's CI downloads.
DATA_COMMIT = "b26bd40cf29004372319df620c4bbe41420bb6f8"
CACHE = Path(os.environ.get("SVERIFY_IBIS_REPLAY", Path.home() / ".cache/sverify/ibis-replay"))
#: The test modules of `ibis/backends/tests` the replay runs: those whose
#: tests execute relational expressions. The rest test Ibis's client,
#: its IO, UDFs and types sverify does not read (maps, JSON, structs,
#: geospatial, UUIDs).
MODULES = (
    "test_aggregation",
    "test_array",
    "test_binary",
    "test_column",
    "test_conditionals",
    "test_generic",
    "test_join",
    "test_numeric",
    "test_set_ops",
    "test_string",
    "test_temporal",
    "test_window",
)
OUTCOMES = ("agree", "disagree", "refused", "unproved", "skipped")


# -- the sources -------------------------------------------------------------


def fetch() -> Path:
    """Ibis at `IBIS_TAG` and its test data at `DATA_COMMIT`, in `CACHE`."""
    ibis_dir = CACHE / f"ibis-{IBIS_TAG}"
    if not (ibis_dir / "pyproject.toml").exists():
        ibis_dir.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "clone", "-q", "--depth", "1", "--branch", IBIS_TAG, IBIS_REPO, str(ibis_dir)],
            check=True,
        )
    data = ibis_dir / "ci" / "ibis-testing-data"
    if not (data / "parquet").exists():
        data.mkdir(parents=True, exist_ok=True)
        git = ["git", "-C", str(data)]
        subprocess.run([*git, "init", "-q"], check=True)
        subprocess.run([*git, "sparse-checkout", "set", "parquet", "tpch"], check=True)
        subprocess.run(
            [*git, "fetch", "-q", "--depth", "1", "--filter=blob:none", DATA_REPO, DATA_COMMIT],
            check=True,
        )
        subprocess.run([*git, "checkout", "-q", "FETCH_HEAD"], check=True)
    return ibis_dir


def replay(modules: list[str], workers: int = 2) -> list[dict[str, Any]]:
    """Run Ibis's tests of `modules` on DuckDB with this module as a plugin;
    one record per test."""
    ibis_dir = fetch()
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "replay.jsonl"
        env = {
            **os.environ,
            # Ibis's "sandboxed" mode: no extensions from the network, no
            # geospatial tables.
            "NIX_SVERIFY_REPLAY": "1",
            "SVERIFY_IBIS_REPLAY_OUT": str(out),
            "PYTHONPATH": os.pathsep.join([str(ROOT / "python" / "tools"), str(ibis_dir)]),
        }
        cmd = [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "no:sverify",
            "-p",
            "no:cacheprovider",
            "-p",
            "sverify_dev.ibis_replay",
            # Ibis's own options need pytest-benchmark; its warnings filter
            # turns DuckDB 2's deprecations into errors.
            "-o",
            "addopts=",
            "-o",
            "filterwarnings=ignore",
            "-o",
            "xfail_strict=false",
            "-m",
            "duckdb",
            "-n",
            str(workers),
            *[f"ibis/backends/tests/{m}.py" for m in modules],
        ]
        subprocess.run(cmd, cwd=ibis_dir, env=env, check=False, stdout=subprocess.DEVNULL)
        if not out.exists():
            raise SystemExit("the replay wrote nothing: run pytest by hand to see why")
        return [json.loads(line) for line in out.read_text().splitlines() if line.strip()]


# -- the plugin ----------------------------------------------------------------

_current: dict[str, Any] = {"test": None, "replays": []}
_tables: dict[tuple[int, str], Any] = {}
_busy = [False]


def normalize(text: str, limit: int = 160) -> str:
    """A reason without the expression's own names and numbers."""
    text = (text.strip().splitlines() or [""])[0]
    text = re.sub(r"'[^']*'|\"[^\"]*\"|`[^`]*`", "…", text)
    text = re.sub(r"https?://\S+", "", text)
    # Numbers go, but not the issues a refusal names (`#173`).
    text = re.sub(r"(?<!#)\b\d+(\.\d+)?\b", "N", text)
    return text[:limit]


def _value(v: Any) -> Any:
    """A value in a form two equal results share: doubles to 12 significant
    digits (sverify's plan may sum in another order), NaN as a string, the
    two zeros as one, dates and decimals as text, lists element-wise."""
    if isinstance(v, float):
        if math.isnan(v):
            return "nan"
        if math.isinf(v):
            return str(v)
        return float(f"{v:.12g}") + 0.0
    if isinstance(v, dict):
        return tuple(sorted((k, _value(x)) for k, x in v.items()))
    if isinstance(v, list | tuple):
        return tuple(_value(x) for x in v)
    if isinstance(v, decimal.Decimal | dt.date | dt.time | dt.timedelta):
        return str(v)
    return v


def _rows(table: Any) -> list[tuple]:
    cols = [table.column(i).to_pylist() for i in range(table.num_columns)]
    return [tuple(_value(c[r]) for c in cols) for r in range(table.num_rows)]


def _key(row: tuple) -> tuple:
    return tuple((x is None, str(type(x)), str(x)) for x in row)


def same(ours: Any, theirs: Any) -> str | None:
    """None if two results hold the same rows (as multisets: the replay does
    not know which order the test reads), else why not."""
    if ours.num_rows != theirs.num_rows:
        return f"{ours.num_rows} rows, Ibis {theirs.num_rows}"
    if ours.num_columns != theirs.num_columns:
        return f"{ours.num_columns} columns, Ibis {theirs.num_columns}"
    a, b = sorted(_rows(ours), key=_key), sorted(_rows(theirs), key=_key)
    for x, y in zip(a, b, strict=True):
        if x != y:
            return f"row {x} where Ibis has {y}"
    return None


def _replay_expr(backend: Any, expr: Any, original_to_pyarrow: Any) -> dict[str, Any]:
    """Verify `expr` with sverify, run it on DuckDB and compare with Ibis."""
    import ibis.expr.operations as ops
    import ibis.expr.types as ir

    import sverify as sv
    from sverify.engine import connect, put_table

    if isinstance(expr, ir.Scalar | ir.Column):
        expr = expr.as_table()
    if not isinstance(expr, ir.Table):
        return {"outcome": "skipped", "reason": f"a {type(expr).__name__}"}
    con = connect()
    for t in cast(Any, expr.op()).find(ops.DatabaseTable):
        key = (id(backend), t.name)
        if key not in _tables:
            _tables[key] = original_to_pyarrow(backend, t.to_expr())
        put_table(con, t.name, _tables[key])
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        try:
            report = sv.verify(expr, on_inferred="warn")
            if report.verdict == sv.Verdict.UNPROVED and report.suggested_requires:
                report = sv.verify(expr, requires=report.suggested_requires, on_inferred="warn")
        except Exception as e:  # noqa: BLE001 - a construct sverify refuses
            return {"outcome": "refused", "construct": normalize(f"{type(e).__name__}: {e}")}
        if report.verdict == sv.Verdict.UNPROVED:
            why = report.issues[0].shown if report.issues else str(report.verdict)
            kind = report.issues[0].kind if report.issues else ""
            return {"outcome": "unproved", "reason": normalize(f"{kind}: {why}")}
        try:
            ours = report.run(con, "duckdb")
        except Exception as e:  # noqa: BLE001 - a run that fails
            from sverify.errors import PreconditionError, UnsupportedError

            if os.environ.get("SVERIFY_IBIS_REPLAY_DEBUG"):
                import traceback

                traceback.print_exc()
            if isinstance(e, PreconditionError):
                return {"outcome": "unproved", "reason": normalize(f"data: {e}")}
            if isinstance(e, UnsupportedError):
                # Proved, but no route or writer takes the plan to DuckDB.
                construct = normalize(f"run: {type(e).__name__}: {e}")
                return {"outcome": "refused", "construct": construct}
            reason = normalize(f"{type(e).__name__}: {e}")
            return {"outcome": "disagree", "side": "run", "reason": reason}
    theirs = original_to_pyarrow(backend, expr)
    if not report.deterministic and ours.num_rows == theirs.num_rows:
        # Rows that tie (a LIMIT without an order, a window's ties): every
        # pick the reference allows is right, and Ibis's is one of them.
        return {"outcome": "agree"}
    if (diff := same(ours, theirs)) is not None:
        return {"outcome": "disagree", "side": "rows", "reason": diff[:300]}
    return {"outcome": "agree"}


def _wrap(name: str, original: Any, original_to_pyarrow: Any) -> Any:
    def wrapper(self: Any, expr: Any, *args: Any, **kwargs: Any) -> Any:
        result = original(self, expr, *args, **kwargs)
        if _busy[0] or _current["test"] is None:
            return result
        _busy[0] = True
        try:
            if kwargs.get("params") or kwargs.get("limit") not in (None, "default"):
                rec = {"outcome": "skipped", "reason": "a parameter or a limit"}
            else:
                rec = _replay_expr(self, expr, original_to_pyarrow)
        except Exception as e:  # noqa: BLE001 - the harness itself
            rec = {"outcome": "skipped", "reason": normalize(f"harness: {type(e).__name__}: {e}")}
        finally:
            _busy[0] = False
        _current["replays"].append(rec)
        return result

    wrapper.__name__ = name
    return wrapper


def pytest_configure(config: Any) -> None:
    from ibis.backends.duckdb import Backend

    to_pyarrow = Backend.to_pyarrow
    Backend.execute = _wrap("execute", Backend.execute, to_pyarrow)
    Backend.to_pyarrow = _wrap("to_pyarrow", to_pyarrow, to_pyarrow)


def pytest_collection_modifyitems(session: Any, config: Any, items: list) -> None:
    # Ibis's TPC-DS data is 112 MB; the replay loads TPC-H's only.
    from ibis.backends.duckdb.tests.conftest import TestConf

    TestConf.supports_tpcds = False


def pytest_runtest_setup(item: Any) -> None:
    _current["test"], _current["replays"] = item.nodeid, []


def pytest_runtest_logreport(report: Any) -> None:
    # Under xdist the controller sees the workers' reports too: only the
    # process that ran the test writes it.
    if _current["test"] != report.nodeid:
        return
    if report.when == "call" or (report.when == "setup" and report.outcome != "passed"):
        passed = report.outcome == "passed" and not hasattr(report, "wasxfail")
        rec = {"test": report.nodeid, "passed": passed, "replays": list(_current["replays"])}
        with open(os.environ["SVERIFY_IBIS_REPLAY_OUT"], "a") as f:
            f.write(json.dumps(rec) + "\n")
        _current["test"] = None


# -- the ledgers -----------------------------------------------------------------

_RANK = {"disagree": 0, "refused": 1, "unproved": 2, "agree": 3, "skipped": 4}


def classify(rec: dict[str, Any]) -> dict[str, Any]:
    """A test's outcome: its worst replay's, or `skipped`."""
    if not rec["passed"]:
        return {"outcome": "skipped", "reason": "fails or is xfailed on DuckDB in Ibis's own run"}
    replays = [r for r in rec["replays"] if r["outcome"] != "skipped"]
    if not replays:
        reasons = sorted({r.get("reason", "") for r in rec["replays"]})
        return {"outcome": "skipped", "reason": reasons[0] if reasons else "executes nothing"}
    return dict(min(replays, key=lambda r: _RANK[r["outcome"]]))


CONSTRUCTS = LEDGERS / "constructs.json"


def waits_on(construct: str) -> dict[str, Any]:
    """What a refused construct waits on: the issue it names (`#n`), the
    issue or design reason `constructs.json` gives, or nothing."""
    if m := re.search(r"#(\d+)", construct):
        return {"issue": int(m[1])}
    for c in json.loads(CONSTRUCTS.read_text())["constructs"]:
        if c["match"] in construct:
            return {k: c[k] for k in ("issue", "design") if k in c}
    return {}


def ledgers(records: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    """One ledger per module, keeping the stored `issue` of each entry."""
    out: dict[str, dict[str, Any]] = {}
    for rec in records:
        module = rec["test"].split("::")[0].rsplit("/", 1)[-1].removesuffix(".py")
        test = rec["test"].split("::", 1)[1]
        out.setdefault(module, {})[test] = classify(rec)
    result = {}
    for module, results in sorted(out.items()):
        path = LEDGERS / f"{module}.json"
        old = json.loads(path.read_text())["results"] if path.exists() else {}
        for test, r in results.items():
            if r["outcome"] == "refused":
                r.update(waits_on(r["construct"]))
            elif (issue := old.get(test, {}).get("issue")) and old[test]["outcome"] == r["outcome"]:
                r["issue"] = issue
        counts = collections.Counter(r["outcome"] for r in results.values())
        result[module] = {
            "ibis": IBIS_TAG,
            "source": f"{IBIS_REPO}/tree/{IBIS_TAG}/ibis/backends/tests/{module}.py",
            "license": "Apache-2.0",
            "data": f"{DATA_REPO}/tree/{DATA_COMMIT}",
            "module": module,
            "summary": {k: counts.get(k, 0) for k in OUTCOMES},
            "results": dict(sorted(results.items())),
        }
    return result


def summary(ledger_set: dict[str, dict[str, Any]]) -> dict[str, int]:
    total: collections.Counter[str] = collections.Counter()
    for led in ledger_set.values():
        total.update(led["summary"])
    return {k: total.get(k, 0) for k in OUTCOMES}


def changes(fresh: dict[str, dict[str, Any]]) -> tuple[list[str], list[str]]:
    """How a fresh replay differs from the stored ledgers: what fails the gate
    (a new disagreement, a test that agreed and no longer does), and what only
    drifted (a refusal lifted or changed), which the ledgers take when next
    written."""
    fails, notes = [], []
    for module, led in fresh.items():
        path = LEDGERS / f"{module}.json"
        old = json.loads(path.read_text())["results"] if path.exists() else {}
        for test, r in led["results"].items():
            was, now = old.get(test, {}).get("outcome"), r["outcome"]
            if was == now:
                continue
            why = r.get("reason") or r.get("construct", "")
            line = f"{module}::{test}: {was} -> {now} ({why})"
            (fails if now == "disagree" or was == "agree" else notes).append(line)
    return fails, notes


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("modules", nargs="*", default=list(MODULES))
    ap.add_argument("--write", action="store_true", help="rewrite the ledgers")
    ap.add_argument("--check", action="store_true", help="compare with the ledgers")
    ap.add_argument("--summary", action="store_true", help="the stored ledgers' totals")
    ap.add_argument("-n", "--workers", type=int, default=2)
    args = ap.parse_args(argv)
    if args.summary:
        stored = {p.stem: json.loads(p.read_text()) for p in sorted(LEDGERS.glob("test_*.json"))}
        print(json.dumps(summary(stored)))
        return 0
    fresh = ledgers(replay(args.modules, args.workers))
    print(json.dumps(summary(fresh)))
    for module, led in fresh.items():
        print(f"{module}: {json.dumps(led['summary'])}")
    fails, notes = changes(fresh)
    if args.write:
        LEDGERS.mkdir(parents=True, exist_ok=True)
        for module, led in fresh.items():
            text = json.dumps(led, indent=2, ensure_ascii=False) + "\n"
            (LEDGERS / f"{module}.json").write_text(text)
    if notes:
        print(f"{len(notes)} change(s) the ledgers take when rewritten:")
        print("\n".join(f"  {n}" for n in notes[:20]))
    if args.check and fails:
        print("\n".join(fails), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    with contextlib.suppress(KeyboardInterrupt):
        raise SystemExit(main())
