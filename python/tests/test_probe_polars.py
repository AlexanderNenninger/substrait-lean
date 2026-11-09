"""The Polars probing harness (`sverify_dev.probe_polars`): Polars's
expressions on edge cases against Lean's outcomes under each candidate option,
the observations, and what `characterization/polars/probes.json` records."""

import ast
import json
import re
from collections.abc import Callable

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
    # As DuckDB: `/` by zero is IEEE; only the NaNs it creates, `±inf / ±inf`
    # and `0 / 0`, NaN in Polars and a domain error in the reference (D39
    # under D37), differ.
    r = _verdict("{0} / {1}", ("float64", "float64"))
    assert r["matching"] == []
    ieee = r["candidates"]["IEEE"]
    assert ieee["differ"] == 5
    assert all(
        ("inf" in e["row"] or e["row"] == "[0.0, 0.0]") and "nan" in e["polars"]
        for e in ieee["examples"]
    )


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


def _runs(mem: str, stream: str) -> bool:
    """A float aggregate's distinct results over five runs: at least one each."""
    return all(isinstance(v := ast.literal_eval(x), list) and len(v) >= 1 for x in (mem, stream))


def _rows(observed: str) -> list[list[str]]:
    """The rows of each list of an observation's lists of rows, sorted."""
    return [sorted(re.findall(r"\([^()]*\)", x)) for x in re.findall(r"\[\(.*?\)\]", observed)]


def _one_of(mem: str, *stream: str) -> Callable[[str, str], bool]:
    return lambda m, s: m == mem and s in stream


#: Observations whose result varies from run to run, and the property each
#: keeps (of the in-memory and the streaming result). Scheduling decides the
#: order of a float sum's partials (on a few rows, each row may be a morsel of
#: its own), of a sort's ties and of the groups.
VARYING: dict[str, Callable[[str, str], bool]] = {
    "s-fsum-runs": _runs,
    "s-group-fsum-runs": _runs,
    "s-var-runs": _runs,
    "s-sort-ties-large": lambda m, s: m in ("True", "False") and s in ("True", "False"),
    "s-group-order": lambda m, s: len(ast.literal_eval(m)) == len(ast.literal_eval(s)) == 8,
    # Ties of the sort key `y` (0.0 and -0.0) in either order.
    "join-nan-zero-null": lambda m, s: _rows(m) == _rows(s) and len(_rows(m)) == 2,
    "s-group-fsum-cancel": _one_of("2.0", "0.0", "1.0", "2.0"),
    "s-group-fsum-f32": _one_of("16777218.0", "16777216.0", "16777218.0"),
    "s-group-mean-cancel": _one_of("0.5", "0.0", "0.25", "0.5"),
    "s-group-var": lambda m, s: m == "1.6666666666666667" and abs(float(s) - float(m)) < 1e-8,
    # Which tied row `arg_min` picks on streaming depends on the morsels.
    "arg-min-max-ties": lambda m, s: (
        m == "[(1, 0)]" and re.fullmatch(r"\[\(1, \d+\)\]", s) is not None
    ),
}


def _counts(observed: str) -> str:
    """An error's row counts, which follow the morsel size on streaming
    (`… for 300 out of 600 values` on 10 cores, 750 out of 1500 on CI)."""
    return re.sub(r"for \d+ out of \d+ values", "for N out of M values", observed)


#: Observations over frames of 30,000 rows or more, left out to keep the test
#: small; `python -m sverify_dev.probe_polars --diff` runs them.
LARGE = {
    "s-first-last-grouped", "s-implode-order", "s-group-order", "s-quantile-median",
    "s-window-order", "s-zero-key-first",
}  # fmt: skip


@pytest.mark.slow
@pytest.mark.skipif(
    not probe_polars.OUT_STREAMING.is_file(),
    reason="characterization/ of the repository is not here",
)
def test_probes_streaming_json_is_current():
    """`probes-streaming.json` is what `engine_diff` finds now (rerun
    `python -m sverify_dev.probe_polars --diff --write` after a Polars
    change), but for the `LARGE` observations; the `VARYING` ones keep their
    property."""
    recorded = json.loads(probe_polars.OUT_STREAMING.read_text())
    assert recorded["polars"] == pl.__version__
    observations = [
        o
        for o in (*probe_polars.OBSERVATIONS, *probe_polars.STREAMING_OBSERVATIONS)
        if o.construct not in LARGE
    ]
    now = probe_polars.engine_diff(observations=observations, log=lambda _: None)
    then = [r for r in recorded["probes"] if r["construct"] not in LARGE]

    def verdicts(found: list[dict]) -> list[tuple]:
        return [
            (r["construct"], r["differ"])
            if "code" not in r
            else (r["construct"],)
            if r["construct"] in VARYING
            else (r["construct"], r["differ"], _counts(r["in-memory"]), _counts(r["streaming"]))
            for r in found
        ]

    assert verdicts(now) == verdicts(then)
    for r in (*now, *then):
        if keeps := VARYING.get(r["construct"]):
            assert keeps(r["in-memory"], r["streaming"]), r
