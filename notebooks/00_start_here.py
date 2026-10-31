# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="sverify: a guided tour")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # Verified data pipelines: a guided tour

    This project lets you **prove things about data pipelines** instead of
    only testing them. You write a pipeline in [Ibis](https://ibis-project.org)
    or SQL, as usual. Then you can:

    * state what the pipeline **guarantees** about its output ("no NULL
      prices", "one row per user and day", "every reading is from the past")
      and have it **proved** for every possible input, not just your test data;
    * keep its result **up to date from the changes alone** (inserts and
      deletes), with update rules that are proved to give the same answer as
      recomputing from scratch.

    The proofs are written in [Lean](https://lean-lang.org), a *proof
    assistant*: a program that checks every step of a mathematical proof, so
    nobody has to take the maths on trust. The Python package `sverify` puts
    them behind a small API.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.callout(
        mo.md(
            "**Tests vs. proofs, in one sentence.** A test checks that your "
            "pipeline is right *on the data you tried*. A proof checks that it is "
            "right *on every possible dataset*, including ones with NULLs, "
            "duplicates, empty tables and values you never thought of."
        ),
        kind="info",
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Thirty seconds of it

    A pipeline that keeps orders above 10 and doubles their amount, with a
    contract: the input has no negative amounts (`requires`), so the output
    has no negative and no NULL `doubled` (`ensures`). Calling the function
    asks Lean for a proof before the result is handed back:
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
    22, because the filter keeps amounts of at least 11. Chapter 3 explains
    how.

    ## How to use the tour

    Each chapter covers one feature, with runnable examples and sliders or
    switches to break things and watch the proofs react. They build on each
    other, so read them in order the first time. Open the whole folder, so
    the links between chapters work:

    ```bash
    uvx marimo edit --sandbox notebooks      # from the project root
    ```

    `--sandbox` gives each notebook its own environment with `sverify`
    installed from `python/` (the first start takes a minute). The Lean
    checker must be built once with `lake build` (see the README's Setup).
    `uvx marimo run --sandbox --include-code notebooks` shows the same
    chapters as read-only apps, with the code one click away.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    | | chapter | what it covers |
    |---:|:---|:---|
    | 1 | [Plans, meaning and proofs](?file=01_plans_and_proofs.py) | Substrait plans, Lean's interpreter, theorems, NULL |
    | 2 | [The checker](?file=02_the_checker.py) | `substrait-check`: well-formedness, Lean as a reference engine, Ibis coverage |
    | 3 | [Contracts](?file=03_contracts.py) | `requires`/`ensures`, abstract interpretation, `on_unproved` |
    | 4 | [Keys and relations](?file=04_keys_and_relations.py) | `sv.unique`, facts between columns, joins |
    | 5 | [Doubles, time and text](?file=05_values.py) | NaN and −0.0, timestamps and intervals, calendar functions, strings |
    | 6 | [Runtime errors](?file=06_runtime_errors.py) | division by zero, overflow, casts; proving they can't happen |
    | 7 | [Windows and ASOF joins](?file=07_windows_and_asof.py) | LAG, LEAD, ROW_NUMBER, ties; aligning two sensors |
    | 8 | [Composing contracts](?file=08_composition.py) | proving one step's preconditions from the previous step |
    | 9 | [Incremental views](?file=09_incremental_views.py) | Z-sets, delta rules, `IncrementalView` |
    | 10 | [Pipelines](?file=10_pipelines.py) | views over views, fallbacks, contracts that hold in every state |
    | 11 | [Engines and SQL](?file=11_engines.py) | DataFusion, Polars, DuckDB; SQL for DuckDB and Snowflake |
    | 12 | [A complete pipeline](?file=12_fitness.py) | heart rate during workouts, end to end |
    | 13 | [What is proved, what is trusted](?file=13_trust.py) | the trusted boundary, a glossary and a map of the code |
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    **Short on time?** Chapters 3, 9 and 12 give the gist: contracts,
    incremental views, and one realistic pipeline with both.
    **Curious about the formal side?** Chapters 1, 2 and 13 are about the
    Lean model, the checker, and exactly what is proved.

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
            "start with chapter 1."
            if _ok
            else "The Lean checker `substrait-check` is missing. Run `lake build` in the "
            "project root, then restart this notebook."
        ),
        kind="success" if _ok else "warn",
    )
    return


if __name__ == "__main__":
    app.run()
