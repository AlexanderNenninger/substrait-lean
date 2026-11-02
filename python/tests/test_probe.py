"""The probing harness (`sverify_dev.probe`, #242): DuckDB's functions on edge
cases against Lean's outcomes under each candidate option, and the verdicts
recorded in `characterization/duckdb/probes.json`."""

import json
import math

import duckdb
import pytest

from sverify.contracts import decode_double
from sverify_dev import probe, slt

pytestmark = pytest.mark.backend("duckdb")


@pytest.mark.parametrize("x", [0.0, 0.5, -2.5, 1e308, 5e-324, math.inf, -math.inf])
def test_double_codes_round_trip(x):
    assert decode_double(probe.encode_double(x)) == x


def test_nan_code():
    assert math.isnan(decode_double(probe.encode_double(math.nan)))


def _verdict(construct: str, args: tuple[str, ...]) -> dict:
    p = next(p for p in probe.PROBES if p.construct == construct and p.args == args)
    return probe.run_probe(duckdb.connect(), p)


def test_integer_addition_raises_on_overflow():
    assert _verdict("{0} + {1}", ("int64", "int64"))["matching"] == ["ERROR"]


def test_double_division_is_ieee_but_for_nan():
    # Under DuckDB's defaults, `/` by zero is IEEE; only `±inf / ±inf`, NaN
    # in DuckDB and a domain error in the reference, differs.
    r = _verdict("{0} / {1}", ("float64", "float64"))
    assert r["matching"] == []
    ieee = r["candidates"]["IEEE"]
    assert ieee["differ"] == 4
    assert all("inf" in e["row"] and "nan" in e["duckdb"] for e in ieee["examples"])


# The Wheels workflow runs these tests from `python/tests` alone: there the
# repository's files are not here.
@pytest.mark.skipif(
    not (slt.LEDGER / "probes.json").is_file(),
    reason="characterization/ of the repository is not here",
)
def test_probes_json_is_current():
    """`probes.json` is what the harness finds now (rerun
    `python -m sverify_dev.probe --write` after a model or DuckDB change)."""
    recorded = json.loads((slt.LEDGER / "probes.json").read_text())
    assert recorded["duckdb"] == duckdb.__version__
    now = probe.probe_all(log=lambda _: None)

    def verdicts(found: list[dict]) -> list[tuple]:
        return [
            (
                json.dumps(r["settings"], sort_keys=True),
                r["construct"],
                tuple(r["matching"]),
                tuple((c, t["differ"]) for c, t in r["candidates"].items()),
            )
            for r in found
        ]

    assert verdicts(now) == verdicts(recorded["probes"])
