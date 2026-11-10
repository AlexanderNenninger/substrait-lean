# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "deltalake",
#     "ibis-framework==12.0.0",
#     "marimo",
#     "pyarrow==26.0.1",
#     "sverify[delta]==0.8.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="6. Running it in production")


@app.cell(hide_code=True)
def _():
    import json
    import os
    import subprocess
    import sys
    import tempfile
    import textwrap
    from datetime import datetime, timedelta
    from pathlib import Path

    import marimo as mo
    import pyarrow as pa
    import sverify as sv

    return (
        Path,
        datetime,
        json,
        mo,
        os,
        pa,
        subprocess,
        sv,
        sys,
        tempfile,
        textwrap,
        timedelta,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 5. [Pipelines and engines](?file=05_pipelines_and_engines.py)
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 6. Running it in production

    Say your payments rollup now runs every hour from a scheduler, while
    you sleep. Whatever breaks, breaks at 3 a.m.: a change merged on Friday
    divides by a quantity that can be zero, a batch arrives two hours late
    and rewrites an hour finance has already closed, or a credential ends up
    in a log. The rule itself is proved. What's left is the work around it.

    We'll check the pipeline's file before it merges, test it in CI, name
    its credentials without holding them, tell the next team what it
    guarantees through OpenLineage, and bound the state an hourly rollup
    keeps, with a late batch refused before it lands.

    ## 1. Check the file before it merges

    A pipeline lives in a file. The `sverify` command proves every
    transform and node in it without running anything, so a CI job or a
    pre-commit hook can stop a change before it merges. Here is a file that
    computes each payment's price per unit:
    """)
    return


@app.cell
def _(Path, tempfile, textwrap):
    project = Path(tempfile.mkdtemp())
    (project / "payments.py").write_text(
        textwrap.dedent("""
            import pyarrow as pa
            import sverify as sv
            from ibis import _
            from sverify.io import StaticSource

            payments = StaticSource(
                pa.table({"id": [1, 2, 3], "cents": [250, 250, 900], "qty": [1, 2, 3]}),
                name="payments",
            )

            @sv.transform(
                requires={"payments": [_.cents >= 0, sv.key("id")]},
                ensures=[sv.key("id")],
            )
            def unit_prices(payments):
                return payments.select(payments.id, unit_cents=payments.cents // payments.qty)

            unit = payments.pipe(unit_prices)
        """)
    )
    return (project,)


@app.cell
def _(project, subprocess, sys):
    def sverify(*args):
        """Run the `sverify` command in the project, and print what it prints."""
        _run = subprocess.run(
            [sys.executable, "-m", "sverify.cli", *args],
            cwd=project,
            capture_output=True,
            text=True,
        )
        print(f"$ sverify {' '.join(args)}\n{_run.stdout}{_run.stderr}exit code {_run.returncode}")
        return _run.returncode

    assert sverify("check", "payments.py", "--diff") == 1
    return (sverify,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The key is proved, and the check found what the author missed: a
    payment with `qty = 0` raises a division by zero, at 3 a.m., on the
    first such row. `--diff` shows the precondition that rules it out as a
    change to the decorator, and `--fix` writes it. The exit code is 1 while
    something is not proved, so the job fails until it is:
    """)
    return


@app.cell
def _(sverify):
    assert sverify("check", "payments.py", "--fix") == 0
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Now every refresh checks `qty ≠ 0` on the data before it runs. The
    command has an exit code per outcome (3 for a refusal, 4 for a time
    budget, which `SVERIFY_TIMEOUT` sets), `--format github` annotates the
    pull request's lines, and `--format sarif` feeds code scanning
    ([the command line](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#the-command-line)).

    ## 2. A test for CI

    A proof says the output meets the contract for every input that meets
    the preconditions. A test says the output is the one you meant on a few
    rows you chose. `sverify.testing.assert_contract` does both: it asserts
    the node's contract is proved, runs the node on your rows, checks both
    sides of the contract on them, and compares the output. Installing
    sverify registers it as a pytest plugin, so a test file in your suite
    needs only this:
    """)
    return


@app.cell
def _(project, sys):
    import importlib.util

    from sverify.testing import assert_contract

    _spec = importlib.util.spec_from_file_location("payments", project / "payments.py")
    pipeline = importlib.util.module_from_spec(_spec)
    sys.modules["payments"] = pipeline
    _spec.loader.exec_module(pipeline)

    def test_unit_prices():
        assert_contract(
            pipeline.unit,
            data={"payments": [{"id": 1, "cents": 900, "qty": 4}]},
            expected=[{"id": 1, "unit_cents": 225}],
        )

    test_unit_prices()
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `assert_engines_agree(node, data)` runs the same rows on every installed
    engine, and `cases(node)` draws inputs that meet the preconditions for
    Hypothesis
    ([testing with pytest](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#testing-with-pytest)).

    ## 3. Credentials by name

    A pipeline reads its lake with a token. The file names where the token
    lives, and sverify reads the value only when it opens a table:
    `env:NAME` for a variable, `file:` for a mounted secret, `bao:` for
    OpenBao, and each cloud's secret manager. A name in the project's
    `pyproject.toml` maps to one of those, so the file says `"lake"` and
    the deployment decides where it comes from. Reports, logs, errors and
    exports print the name:
    """)
    return


@app.cell
def _(os):
    from sverify.io import Secret

    os.environ["LAKE_TOKEN"] = "a-value-no-report-shows"
    lake_token = Secret("env:LAKE_TOKEN")
    assert lake_token.value() == os.environ["LAKE_TOKEN"]
    lake_token
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `node.credentials()` lists the names a node uses before it runs, and
    `sverify check` warns when a sink lies outside what its credential may
    write
    ([credentials](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#credentials)).

    ## 4. Tell the next team what it gets

    Finance's job reads your totals. It needs to know which version it read
    and what holds of it. OpenLineage is the standard for that: Airflow,
    Spark and dbt emit its events, and Marquez, DataHub and the cloud
    catalogs read them. A refresh with `lineage=` emits a run per node, with
    the columns each output column comes from and the node's contract.

    The payments are a Delta table with its change feed, and the node totals
    each merchant's payments:
    """)
    return


@app.cell
def _(datetime, pa, tempfile, timedelta):
    from deltalake import write_deltalake

    lake = tempfile.mkdtemp()
    START = datetime(2026, 11, 3)

    def payments_at(rows):
        """A batch of payments: (merchant, minutes after START, cents)."""
        return pa.table(
            {
                "merchant": [m for m, _, _ in rows],
                "ts": [START + timedelta(minutes=t) for _, t, _ in rows],
                "cents": [c for _, _, c in rows],
            }
        )

    write_deltalake(
        f"{lake}/payments",
        payments_at([("m1", 20 * k, 100 * k) for k in range(12)]),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    return lake, payments_at, write_deltalake


@app.cell
def _(lake, sv):
    from ibis import _
    from sverify import openlineage
    from sverify.io import DeltaSink, DeltaSource

    @sv.transform(
        requires={"payments": [_.cents >= 0, _.cents < 10**9, sv.max_rows(10**9)]},
        ensures=[_.total >= 0, sv.unique("merchant")],
    )
    def merchant_totals(payments):
        return payments.group_by("merchant").aggregate(total=payments.cents.sum())

    totals = DeltaSource(f"{lake}/payments").pipe(merchant_totals)
    totals = totals.write(DeltaSink(f"{lake}/totals"))
    events = f"{lake}/events.jsonl"
    print(totals.refresh(lineage=openlineage.Lineage(events, namespace="payments")))
    return DeltaSink, DeltaSource, events, openlineage


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The events went to a file here; a URL sends them to Marquez or DataHub.
    The run's output carries the `sverify_contract` facet: each
    postcondition with its status, and the proved plan, exported to
    Substrait. Finance's pipeline reads the events and takes the
    postconditions as its `requires`, and sverify proves them again from
    the plan before it trusts them:
    """)
    return


@app.cell
def _(DeltaSource, Path, events, json, lake, openlineage):
    _complete = json.loads(Path(events).read_text().splitlines()[-1])
    _facet = _complete["outputs"][0]["facets"]["sverify_contract"]
    # Finance's pipeline, which reads the totals' table.
    upstream = openlineage.read(events).dataset(DeltaSource(f"{lake}/totals"))
    assert upstream.verified
    {
        "event": _complete["eventType"],
        "postconditions": {c["label"]: c["status"] for c in _facet["ensures"]},
        "finance's requires": [str(c) for c in upstream.requires],
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 5. Late rows and bounded state

    Finance also wants totals per hour. An hourly rollup keeps a row per
    merchant and hour, so its state grows with every hour it has seen.
    `sv.arrives_within("ts", "PT1H")` in `requires` says that no row arrives
    more than an hour behind the latest one. The refresh's `retention` line
    shows what it buys: the hours before the watermark are final, and the
    node drops them from its state, keeping them in the sink
    (`Retention.expiry_sound`):
    """)
    return


@app.cell
def _(DeltaSink, DeltaSource, datetime, lake, sv):
    from ibis import _ as _c

    @sv.transform(
        requires={
            "payments": [
                sv.arrives_within("ts", "PT1H"),
                _c.ts >= datetime(2000, 1, 1),
                _c.ts < datetime(2100, 1, 1),
                _c.cents >= 0,
                _c.cents < 10**9,
            ]
        },
        ensures=[_c.total >= 0, sv.unique("merchant", "hour")],
    )
    def hourly(payments):
        _hour = payments.ts.truncate("h").name("hour")
        return payments.group_by(["merchant", _hour]).aggregate(total=payments.cents.sum())

    rollup = DeltaSource(f"{lake}/payments").pipe(hourly).write(DeltaSink(f"{lake}/hourly"))
    print(rollup.refresh())
    return (rollup,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The promise is checked on every batch. We'll append a payment from
    00:05, which comes in after 03:40:
    """)
    return


@app.cell
def _(lake, mo, payments_at, rollup, sv, write_deltalake):
    write_deltalake(f"{lake}/payments", payments_at([("m1", 5, 700)]), mode="append")
    try:
        rollup.refresh()
    except sv.errors.PreconditionError as _e:
        _late = _e
    mo.callout(mo.md(f"PreconditionError: {_late}"), kind="danger")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Nothing was applied: the closed hour finance reported on stays as it
    was, and the alert names the row, the watermark and the promise it
    broke. Whoever is on call decides whether the source or the promise is
    wrong, in the morning.

    ## What you got

    You can now check a pipeline's file in CI and let `--fix` write the
    preconditions a proof needs, test a node on rows you chose, keep
    credentials out of every file and log, hand the next team a contract it
    proves again, and bound a rollup's state with a promise every batch is
    checked against. That is the end of the tour. The
    [guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md)
    covers every feature in more detail, and
    [how it works](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-it-works.md)
    goes under the hood: the checker, the producers and engines, and what
    is proved and what is trusted.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 5. [Pipelines and engines](?file=05_pipelines_and_engines.py)
    """)
    return


if __name__ == "__main__":
    app.run()
