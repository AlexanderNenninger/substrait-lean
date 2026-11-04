"""The Polars probing harness (`sverify_dev.probe_polars`): Polars's
expressions on edge cases against Lean's outcomes under each candidate option,
the observations, and what `characterization/polars/probes.json` records."""

import json

import polars as pl
import pytest

from sverify_dev import probe_polars

pytestmark = pytest.mark.backend("polars")


def _verdict(construct: str, args: tuple[str, ...], option: str | None = None) -> dict:
    p = next(
        p
        for p in probe_polars.PROBES
        if p.construct == construct and p.args == args and (option is None or p.option == option)
    )
    return probe_polars.run_probe(p)


@pytest.mark.parametrize("w", probe_polars.WIDTHS)
def test_integer_addition_wraps(w):
    assert _verdict("{0} + {1}", (w, w))["matching"] == ["SILENT"]


def test_double_division_is_ieee_but_for_nan():
    # As DuckDB: `/` by zero is IEEE; only `±inf / ±inf`, NaN in Polars and a
    # domain error in the reference, differs.
    r = _verdict("{0} / {1}", ("float64", "float64"))
    assert r["matching"] == []
    ieee = r["candidates"]["IEEE"]
    assert ieee["differ"] == 4
    assert all("inf" in e["row"] and "nan" in e["polars"] for e in ieee["examples"])


def test_observation_reports_errors():
    o = probe_polars.Observation("t", "integers", "df(x=[2]).select(pl.col('x') ** -1).item()")
    assert probe_polars.observe(o)["observed"].startswith("error InvalidOperationError")


def test_streaming_engine_collects_lazily_on_streaming(monkeypatch):
    engines: list[object] = []
    collect = pl.LazyFrame.collect

    def spy(self, *args, **kwargs):
        engines.append(kwargs.get("engine"))
        return collect(self, *args, **kwargs)

    monkeypatch.setattr(pl.LazyFrame, "collect", spy)
    monkeypatch.setattr(probe_polars, "ENGINE", "streaming")
    o = probe_polars.Observation(
        "t", "integers",
        "df(g=[1, 1, 2], x=[1, 2, 3]).filter(pl.col('x') > 1).group_by('g')"
        ".agg(pl.col('x').sum()).sort('g').rows()",
    )  # fmt: skip
    assert probe_polars.observe(o)["observed"] == "[(1, 2), (2, 3)]"
    assert engines == ["streaming"] * 3
    p = next(p for p in probe_polars.PROBES if p.function == "add")
    assert probe_polars.polars_outcome(p, (1, 2)) == ("ok", 3)
    assert engines[-1] == "streaming"


@pytest.mark.slow
@pytest.mark.skipif(
    not probe_polars.OUT.is_file(), reason="characterization/ of the repository is not here"
)
def test_probes_json_is_current():
    """`probes.json` is what the harness finds now (rerun
    `python -m sverify_dev.probe_polars --write` after a model or Polars change)."""
    recorded = json.loads(probe_polars.OUT.read_text())
    assert recorded["polars"] == pl.__version__
    now = probe_polars.probe_all(log=lambda _: None)

    def verdicts(found: list[dict]) -> list[tuple]:
        return [
            (
                r["construct"],
                tuple(r.get("matching", ())),
                tuple((c, t["differ"]) for c, t in r.get("candidates", {}).items()),
                r.get("observed"),
            )
            for r in found
        ]

    assert verdicts(now) == verdicts(recorded["probes"])


def test_engine_diff_compares_streaming_with_in_memory():
    p = next(p for p in probe_polars.PROBES if p.function == "add")
    o = probe_polars.Observation("t", "integers", "df(x=[1, 2]).select(pl.col('x').sum()).item()")
    found = probe_polars.engine_diff([p], [o], log=lambda _: None)
    assert found[0]["differ"] == 0 and found[0]["rows"] > 1
    assert found[1] == {
        "construct": "t", "area": "integers", "code": o.code, "differ": 0,
        "in-memory": "3", "streaming": "3",
    }  # fmt: skip
    assert probe_polars.ENGINE == "in-memory"
