# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "dbt-duckdb",
#     "marimo",
#     "sverify[duckdb]==0.9.0",
#     "sverify-dbt==0.9.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="8. Your dbt project")


@app.cell(hide_code=True)
def _():
    import tempfile
    import textwrap
    from pathlib import Path

    import marimo as mo
    import sverify_dbt
    from dbt.cli.main import dbtRunner

    return Path, dbtRunner, mo, sverify_dbt, tempfile, textwrap


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 7. [Engines](?file=07_engines.py)
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 8. Your dbt project

    Say your analytics team runs `dbt build` every hour, and the project has
    grown to hundreds of tests. Each one is a query against the warehouse,
    on every build, and most of them have never failed. A few of them will
    fail the day an upstream table changes, and the dashboard will show
    the gap before anyone reads the log.

    We'll write a small dbt project, compile it, and have sverify-dbt prove
    which tests hold on every run before the models run. Then we'll read
    what it can't prove, fix the model, and list the tests `dbt build` can
    skip.

    ## 1. A project with tests

    The project reads a source table, `orders`, and its tests say what we
    know of the data: the keys are never NULL, the order id is unique, a
    status is one of three. A model, `orders_by_customer`, totals each
    customer's orders, and tests its own result:
    """)
    return


@app.cell
def _(Path, dbtRunner, tempfile, textwrap):
    project = Path(tempfile.mkdtemp()) / "shop"
    MODEL = textwrap.dedent("""\
        select customer_id, count(*) as orders, sum(amount) as revenue
        from {{ source('app', 'orders') }}
        where status <> 'returned'
        group by customer_id
        """)
    SOURCES = textwrap.dedent("""\
        version: 2
        sources:
          - name: app
            schema: main
            tables:
              - name: orders
                columns:
                  - name: order_id
                    data_type: bigint
                    data_tests: [not_null, unique]
                  - name: customer_id
                    data_type: bigint
                    data_tests: [not_null]
                  - name: status
                    data_type: varchar
                    data_tests:
                      - accepted_values:
                          arguments: {values: [placed, shipped, returned]}
                  - name: amount
                    data_type: bigint
        """)
    MODELS = textwrap.dedent("""\
        version: 2
        models:
          - name: orders_by_customer
            columns:
              - name: customer_id
                data_tests: [not_null, unique]
              - name: orders
                data_tests: [not_null]
              - name: revenue
                data_tests: [not_null]
        """)
    FILES = {
        "dbt_project.yml": "name: shop\nversion: '1.0'\nconfig-version: 2\nprofile: shop\n",
        "profiles.yml": (
            f"shop:\n  target: dev\n  outputs:\n"
            f"    dev: {{type: duckdb, path: '{project}/shop.duckdb', threads: 1}}\n"
        ),
        "models/sources.yml": SOURCES,
        "models/orders_by_customer.yml": MODELS,
        "models/orders_by_customer.sql": MODEL,
    }

    def compile_project(files):
        """Write the project's files, and `dbt compile` them."""
        for _name, _text in files.items():
            (project / _name).parent.mkdir(parents=True, exist_ok=True)
            (project / _name).write_text(_text)
        _res = dbtRunner().invoke(
            ["compile", "--project-dir", str(project), "--profiles-dir", str(project), "--quiet"]
        )
        assert _res.success, _res.exception

    return FILES, MODEL, compile_project, project


@app.cell(hide_code=True)
def _(FILES, mo):
    mo.md(f"""
    The model's tests, `models/orders_by_customer.yml`:

    ```yaml
    {FILES["models/orders_by_customer.yml"].replace(chr(10), chr(10) + "    ")}
    ```

    The source's, `models/sources.yml`, say what we know of `orders`. Its
    columns carry `data_type`s, which sverify-dbt reads where `dbt docs generate`
    has written no catalogue.

    ## 2. Check it before the models run

    `dbt compile` writes each model's SQL. `sverify_dbt.check(project)`
    reads it, and proves each model's SQL against the tests on what it
    reads:
    """)
    return


@app.cell
def _(FILES, compile_project, project, sverify_dbt):
    compile_project(FILES)
    result = sverify_dbt.check(project)
    print(result)
    return (result,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Three of the model's tests are proved. `customer_id` is the grouping
    key, so `unique` holds whatever the data is, and `not_null` follows from the
    source's test. `orders` is a count, never NULL. A proved test holds on
    every run whose inputs pass their tests, so `dbt build` may leave it out.

    `not_null(revenue)` is not proved, and the report says why with a
    counterexample: a customer whose only order has no amount. A `SUM` of
    NULLs is NULL, and the source never promised an amount.

    ## 3. Fix the model, and prove it again

    We have two ways out: a `not_null` test on the source's `amount`, or a model
    that never returns NULL. We take the second:
    """)
    return


@app.cell
def _(FILES, MODEL, compile_project, project, sverify_dbt):
    FIXED = {
        **FILES,
        "models/orders_by_customer.sql": MODEL.replace("sum(amount)", "coalesce(sum(amount), 0)"),
    }
    compile_project(FIXED)
    fixed = sverify_dbt.check(project)
    print(fixed)
    return FIXED, fixed


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    All four tests hold on every run now. The report keeps one line of
    caution: `sum(amount)` can overflow a 64-bit integer, and DuckDB raises
    where it does, so a run needs amounts that stay small.

    ## 4. Leave the proved tests out of the build

    `write_selectors` adds a dbt selector, `sverify_proved`, to the project's
    `selectors.yml`. The command line does the same with
    `sverify-dbt check . --selectors`:
    """)
    return


@app.cell
def _(fixed, project):
    fixed.write_selectors(project / "selectors.yml")
    print((project / "selectors.yml").read_text())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `dbt build --exclude selector:sverify_proved` runs the models and the tests
    sverify-dbt couldn't prove. The tests it left out can't fail while
    the tests upstream pass, because `dbt build` skips the models downstream
    of a failing test.

    ## 5. What it refuses

    Sverify-dbt refuses a model it can't read, with the reason and what to do.
    We add two: one reads a table by its name, and one is a recursive query:
    """)
    return


@app.cell
def _(FIXED, compile_project, project, sverify_dbt):
    compile_project(
        {
            **FIXED,
            "models/stale_orders.sql": "select * from raw_orders where status = 'placed'\n",
            "models/chain.sql": (
                "with recursive n(i) as (select 1 union all select i + 1 from n where i < 3)\n"
                "select i from n\n"
            ),
        }
    )
    print(sverify_dbt.check(project, select=["stale_orders", "chain"]))
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The first refusal names its exit: read the table with `{{ ref() }}` or
    `{{ source() }}`, so that sverify-dbt knows which tests describe it. The
    second names the construct, `WITH RECURSIVE`, and the issue that tracks
    it. A refused model proves nothing, so `dbt build` still runs every test on
    it, and the project's other models are checked as before.

    You can now prove a dbt project's tests before its models run, read
    what it couldn't prove and why, fix a model until it holds, and let
    `dbt build` skip the tests that can't fail. That is the end of the tour.
    The [sverify-dbt
    README](https://github.com/AlexanderNenninger/substrait-lean/blob/v0.9.0/dbt/README.md)
    lists the tests it reads, and the
    [guide](https://github.com/AlexanderNenninger/substrait-lean/blob/v0.9.0/docs/tasks.md)
    covers every feature in more detail.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 7. [Engines](?file=07_engines.py)
    """)
    return


if __name__ == "__main__":
    app.run()
