"""The workflows' steps on the recorded Eurostat response: check, refresh,
refresh again, the catalog, and a refresh that the data refuses.

    pip install pytest && pytest

No network: `EUROSTAT_FIXTURES` points the sources at tests/fixtures/.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "tests" / "fixtures" / "eurostat"


def lake(*args: str, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "lake.py"), *args],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


@pytest.fixture
def env(tmp_path: Path) -> dict[str, str]:
    out = {k: v for k, v in os.environ.items() if not k.startswith("GITHUB_")}
    out |= {
        "EUROSTAT_FIXTURES": str(FIXTURES),
        "SVERIFY_LAKE": str(tmp_path / "lake"),
        "SVERIFY_STORE": "repository",
    }
    return out


def test_check_proves_every_pipeline(env, tmp_path):
    done = lake(
        "check",
        "--out",
        str(tmp_path / "check.json"),
        "--comment",
        str(tmp_path / "comment.md"),
        env=env,
    )
    assert done.returncode == 0, done.stdout + done.stderr
    doc = json.loads((tmp_path / "check.json").read_text())
    items = {i["name"]: i for f in doc["files"] for i in f["items"]}
    assert {"gdp", "trade_openness"} <= set(items)
    assert all(i["status"] == "proved" for i in items.values())
    comment = (tmp_path / "comment.md").read_text()
    assert comment.startswith("<!-- sverify-check -->")
    assert "no two rows share (geo, unit, na_item, time)" in comment


def test_refresh_then_catalog(env, tmp_path):
    # The check first, in the same process, as the workflows run it.
    done = lake(
        "refresh",
        "--check",
        str(tmp_path / "check.json"),
        "--out",
        str(tmp_path / "refresh.json"),
        env=env,
    )
    assert done.returncode == 0, done.stdout + done.stderr
    doc = json.loads((tmp_path / "refresh.json").read_text())
    writes = {n["node"]: n["write"] for r in doc["runs"] for n in r["result"]["nodes"]}
    assert writes["gdp"]["inserted"] == 1100
    assert writes["trade_openness"]["inserted"] == 110

    # A second refresh of the same data changes no row downstream.
    again = lake("refresh", "--out", str(tmp_path / "again.json"), env=env)
    assert again.returncode == 0, again.stdout + again.stderr
    doc = json.loads((tmp_path / "again.json").read_text())
    writes = {n["node"]: n["write"] for r in doc["runs"] for n in r["result"]["nodes"]}
    assert (writes["trade_openness"]["inserted"], writes["trade_openness"]["deleted"]) == (0, 0)

    assert json.loads((tmp_path / "check.json").read_text())["exit"] == 0
    site = tmp_path / "site"
    done = lake(
        "catalog",
        "--out",
        str(site),
        "--check",
        str(tmp_path / "check.json"),
        "--refresh",
        str(tmp_path / "refresh.json"),
        "--stage",
        "production",
        env=env,
    )
    assert done.returncode == 0, done.stdout + done.stderr
    assert {"index.html", "gdp.html", "trade_openness.html", "style.css", "query.js"} <= {
        p.name for p in site.iterdir()
    }
    page = (site / "gdp.html").read_text()
    assert "no two rows share (geo, unit, na_item, time)" in page  # proved facts
    assert "<svg" in page  # the chart
    assert 'href="gdp.html"' in (site / "trade_openness.html").read_text()  # lineage
    meta = json.loads((site / "gdp.json").read_text())
    assert meta["rows"] == 1100
    assert meta["files"] == ["data/gdp.parquet"]
    assert (site / "data" / "gdp.parquet").exists()

    # A public repository's pages read the data branch's files.
    env = env | {"GITHUB_REPOSITORY": "you/pipelines", "REPOSITORY_PUBLIC": "true"}
    done = lake("catalog", "--out", str(tmp_path / "linked"), "--stage", "production", env=env)
    assert done.returncode == 0, done.stdout + done.stderr
    files = json.loads((tmp_path / "linked" / "gdp.json").read_text())["files"]
    assert files and all(
        f.startswith("https://raw.githubusercontent.com/you/pipelines/data/production/gdp/")
        for f in files
    )

    done = lake("drop", env=env)
    assert done.returncode == 0
    assert not Path(env["SVERIFY_LAKE"]).exists()


def test_data_that_breaks_the_contract_fails_the_refresh(env, tmp_path):
    """A duplicated key in the source fails the precondition the proof
    rests on: the refresh exits 1 and writes the alert."""
    bad = tmp_path / "fixtures"
    bad.mkdir()
    lines = (FIXTURES / "nama_10_gdp.csv").read_text().splitlines(keepends=True)
    (bad / "nama_10_gdp.csv").write_text("".join([*lines, lines[1]]))
    env = env | {"EUROSTAT_FIXTURES": str(bad)}
    done = lake(
        "refresh",
        "--out",
        str(tmp_path / "refresh.json"),
        "--alert",
        str(tmp_path / "alert.md"),
        env=env,
    )
    assert done.returncode != 0, done.stdout + done.stderr
    alert = (tmp_path / "alert.md").read_text()
    assert alert.startswith("<!-- sverify-alert -->")
    assert "pipelines/gdp.py:trade_openness_table" in alert
    assert "PreconditionError" in alert
    assert not (Path(env["SVERIFY_LAKE"]) / "gdp").exists()  # nothing written


def test_stored_keys_reach_only_the_store_that_needs_them():
    """The cloud stores log in through OIDC (#776): a stored key or the
    Tailscale client's secret reaches a job only for the store that needs
    it, and every other secret line in lake.yml is a commented example."""
    text = (ROOT / ".github" / "workflows" / "lake.yml").read_text()
    lines = [
        line.strip()
        for line in text.splitlines()
        if "secrets." in line and not line.strip().startswith("#")
    ]
    assert lines
    for line in lines:
        assert "vars.SVERIFY_STORE == 'r2'" in line or "vars.SVERIFY_STORE == 'minio'" in line, line
