# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify==0.3.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="sverify: a guided tour")


@app.cell(hide_code=True)
def _():
    import marimo as mo

    return (mo,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # sverify: a guided tour

    Somewhere downstream of every pipeline you write, someone is relying on
    it: the customer waiting for a refund, whoever gets paged at 3 a.m., the
    analyst whose dashboard has to add up. `sverify` checks the pipeline for
    them **before it runs**. You write the
    transformation in [Ibis](https://ibis-project.org) or SQL, as usual,
    and say what it may assume about its inputs and what it guarantees
    about its output. A checker written in [Lean](https://lean-lang.org)
    proves the guarantees for every possible input, or tells you why it
    can't. Then you get:

    1. **Contracts proved, not tested.** "No NULL city", "one row per
       device and minute", "no amount below zero" hold on every input that
       meets the preconditions, not just on yesterday's data: the checks you
       would write as dbt tests or expectations, done once, at definition
       time. Division by zero, integer overflow and bad casts are ruled out
       the same way.
    2. **One plan, the same answer on every engine.** The checked plan runs
       on DuckDB, Polars or DataFusion, or is written as Snowflake or Spark
       SQL, and means the same thing on each: NULLs, integer division, NaN,
       ties and overflow are spelled out, or the plan is refused where an
       engine can't match.
    3. **Results kept up to date from the changes.** Read the change feed
       of a Delta or Iceberg table, and update the result with plans proved
       to equal a full recompute, instead of a hand-written watermark job.
       Sinks write each state exactly once and carry the contract to the
       next job.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Start with a workflow

    The first three chapters are complete jobs, condensed from the
    [query catalogue](https://github.com/AlexanderNenninger/substrait-lean/blob/v0.3.0/catalogue/INDEX.md) of 139 real analytical queries.
    Each starts from source tables, states and proves a contract, runs on
    every engine, keeps up with new data and writes a sink, and each shows
    what goes wrong without the checker:

    | | workflow | sources and sinks | what it catches |
    |---:|:---|:---|:---|
    | 1 | [Duplicate card payments](?file=01_duplicate_payments.py) | Delta, Change Data Feed | a self-join matching rows with themselves; a watermark job missing a late duplicate and keeping a reversed one |
    | 2 | [Sensor alerts](?file=02_sensor_alerts.py) | Iceberg | `LAG` over ties; a NaN reading raising an alert; Snowflake and Spark tables without row order |
    | 3 | [An orders mart](?file=03_orders_mart.py) | Delta, a type-2 dimension | `not_null(city)` failing after a left join; `/` meaning three things on three engines |
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Thirty seconds of it

    A transformation with a contract: the input has no negative amounts
    (`requires`), so the output has no negative and no NULL `doubled`
    (`ensures`). Calling the function asks Lean for a proof before the
    expression is handed back:
    """)
    return


@app.cell
def _():
    import ibis
    import sverify as sv
    from ibis import _

    orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")

    @sv.transform(
        requires={"orders": [_.amount >= 0]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(orders):
        return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

    doubled(orders)
    doubled.last_report
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Both postconditions are ✅ **proved**, and the bottom table is what Lean
    worked out about every output column on its own: `doubled` is at least
    22, because the filter keeps amounts of at least 11.
    [Contracts](?file=04_contracts.py) explains how.

    ## The rest of the tour

    **Features**, one per chapter, with examples to change and break:

    | | chapter | what it covers |
    |---:|:---|:---|
    | 4 | [Contracts](?file=04_contracts.py) | `requires`/`ensures`, what Lean tracks, `on_unproved`, contracts on real data |
    | 5 | [Keys and relations](?file=05_keys_and_relations.py) | `sv.unique`, facts between columns, joins |
    | 6 | [Runtime errors](?file=06_runtime_errors.py) | division by zero, overflow, casts; proving they can't happen |
    | 7 | [Windows and ASOF joins](?file=07_windows_and_asof.py) | LAG, LEAD, ROW_NUMBER, ties; aligning two sensors |
    | 8 | [Composing contracts](?file=08_composition.py) | proving one step's preconditions from the previous step |
    | 9 | [Incremental views](?file=09_incremental_views.py) | a transform on a source becomes a node that `refresh` keeps up to date from changes alone; what is refused, and how the update rules work |
    | 10 | [Pipelines](?file=10_pipelines.py) | nodes over nodes, `.write` to store them, fallbacks, contracts that hold in every state |
    | 11 | [Engines and SQL](?file=11_engines.py) | DuckDB, Polars, DataFusion; SQL for DuckDB, Snowflake and Spark |
    | 12 | [Doubles, time and text](?file=12_values.py) | NaN and −0.0, timestamps and intervals, calendar functions, strings |

    **Under the hood**, for when you want to know why the ✅ can be trusted:

    | | chapter | what it covers |
    |---:|:---|:---|
    | 13 | [Plans, meaning and proofs](?file=13_plans_and_proofs.py) | Substrait plans, Lean's interpreter, theorems, NULL |
    | 14 | [The checker](?file=14_the_checker.py) | `substrait-check`: well-formedness, Lean as a reference engine, Ibis coverage |
    | 15 | [What is proved, what is trusted](?file=15_trust.py) | the trusted boundary, a glossary and a map of the code |
    | 16 | [DataFusion's surprising semantics](?file=16_datafusion_semantics.py) | appendix: every DataFusion quirk, checked against the Lean model |
    | 17 | [One expression, many engines](?file=17_backend_semantics.py) | appendix: DataFusion, DuckDB, Polars, Snowflake and Ibis, question by question |

    No knowledge of formal verification is needed for any of it.

    ## Opening the tour

    Open the whole folder, so the links between chapters work:

    ```bash
    uvx marimo edit --sandbox notebooks      # from the project root
    ```

    `--sandbox` gives each notebook its own environment with `sverify`
    installed from `python/` (the first start takes a minute). The Lean
    checker must be built once with `lake build` (see the README's
    Development section). `uvx marimo run --sandbox --include-code
    notebooks` shows the same chapters as read-only apps.

    ## Is everything set up?
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    import subprocess

    from sverify.engine import checker_path

    try:
        _path = checker_path()
        _ok = (
            _path.exists()
            and subprocess.run([str(_path)], capture_output=True, check=False).returncode == 1
        )
    except FileNotFoundError:
        _ok = False
    mo.callout(
        mo.md(
            "The Lean checker `substrait-check` is installed. You're ready to go: "
            "start with the first workflow."
            if _ok
            else "The Lean checker `substrait-check` is missing. Run `lake build` in the "
            "project root, then restart this notebook."
        ),
        kind="success" if _ok else "warn",
    )
    return


if __name__ == "__main__":
    app.run()
