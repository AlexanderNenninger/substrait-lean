# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[datafusion,polars]==0.3.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="14. The checker")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 13. [Plans, meaning and proofs](?file=13_plans_and_proofs.py) · [Contents](?file=00_start_here.py) · 15. [What is proved, what is trusted](?file=15_trust.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 14. The checker

    Say a reviewer asks what actually happens when you call
    `@sv.transform`. The answer is a small command-line program that does
    the work. The Lean project compiles to it,
    `substrait-check`. It is the bridge between the proofs and real queries:
    it reads a Substrait plan (as JSON), translates it into the Lean model
    `Rel`, and runs checks that are **proved** to answer the mathematical
    questions they claim to answer. `sverify` calls it behind the scenes for
    everything in the rest of the tour, and you can run it yourself.

    | Mode | What it does | Used by |
    |:---|:---|:---|
    | `substrait-check plan.json` | show the plan, check it is well-formed, evaluate it | this chapter |
    | `--write plan.json` | write the plan back out from Lean's model | the engines (chapter 11) |
    | `--contract contract.json` | prove postconditions from preconditions | contracts (chapters 4–8) |
    | `--delta plan.json` | the proved update plans for incremental views | chapters 9–10 |

    Exit codes: 0 fine, 1 unsupported or unparseable, 2 ill-formed, 3 not
    incrementally maintainable, 4 a postcondition not proved.

    ## A real plan

    Let's start with some tables, registered in DataFusion, which compiles
    the SQL here:
    """)
    return


@app.cell
def _():
    import json
    import subprocess

    import sverify as sv
    from sverify.engine import checker_path
    from sverify.engines import substrait_json, written_plan
    from sverify.examples import create_tables

    con = sv.connect()  # plans run on DuckDB by default
    create_tables(
        con,
        orders_rows=[(1, "ada", 30), (2, "bob", 5), (3, "ada", None)],
        customers_rows=[("ada", "Paris"), ("bob", "Oslo")],
    )

    def substrait_check(plan_json, *flags):
        """Run the Lean checker on a plan; returns (exit code, output)."""
        proc = subprocess.run(
            [str(checker_path()), *flags, "/dev/stdin"],
            input=plan_json,
            capture_output=True,
            text=True,
            check=False,
        )
        return proc.returncode, (proc.stdout + proc.stderr).strip()

    return con, json, substrait_check, substrait_json, written_plan


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `sverify.engines.substrait_json` asks DataFusion for the Substrait plan of a query.
    Edit the SQL and the checker re-runs. Try a join (`select o.id, c.city
    from orders o join customers c on o.customer = c.name`), a `limit 2`, or
    a `group by` (which the model doesn't cover yet).
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    sql = mo.ui.text_area(
        value="select id, amount * 2 as doubled from orders where amount > 10",
        label="SQL over orders(id, customer, amount) and customers(name, city)",
        full_width=True,
        rows=2,
    )
    sql
    return (sql,)


@app.cell(hide_code=True)
def _(con, mo, sql, substrait_check, substrait_json):
    try:
        plan = substrait_json(con, sql.value)
        _code, _out = substrait_check(plan)
        _shown = mo.md(f"```text\n$ substrait-check plan.json\n{_out}\n```")
        _note = {
            0: None,
            1: (
                "warn",
                "Outside the Lean model: the checker refuses the plan instead of guessing.",
            ),
            2: ("danger", "Ill-formed: a column reference points nowhere."),
        }.get(_code)
        _out_cell = mo.vstack(
            [_shown, mo.callout(mo.md(_note[1]), kind=_note[0])] if _note else [_shown]
        )
    except Exception as _e:
        plan = None
        _out_cell = mo.callout(
            mo.md(f"DataFusion could not plan this query: `{_e}`"), kind="danger"
        )
    _out_cell
    return (plan,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What each line means, for the default query:

    * **The tree** is the plan, printed from Lean's model, root first.
      `$2` is column 2 of the operator's input, here `amount`. The Project
      appends two columns, a copy of `id` (`$0`) and `amount * 2`, as columns
      3 and 4, and the Emit keeps just those two.
    * **`tables`**: the tables the plan reads, with their number of columns.
    * **`arity`**: how many columns the result has.
    * **`well-formed: yes`**: every column reference exists. This is decided
      by `Rel.checkWF`, which is *proved* to agree with the mathematical
      definition `Rel.WF` (theorem `checkWF_iff`). So the type-safety theorem
      `Rel.eval_arity` applies: every output row has exactly `arity` columns.
    * **`incremental: yes`**: the plan can be maintained from changes alone
      (chapter 9). Also a decision procedure with a proof (`isIncremental_iff`).
    * **`roundtrip: ok`**: writing the `Rel` back to JSON and reading it again
      gives the same `Rel`. That guards the parser, which is *trusted* code
      (chapter 15).
    * **`rows (0)`**: named tables carry only their schema here, no data.

    ## Ruling out column bugs

    Since columns are numbered, a classic bug is a reference to a column that
    doesn't exist. Move the slider to change which column the filter reads,
    by editing the plan's JSON directly:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    field_index = mo.ui.slider(0, 5, value=2, label="the filter reads column $", show_value=True)
    field_index
    return (field_index,)


@app.cell(hide_code=True)
def _(con, field_index, json, mo, substrait_check, substrait_json):
    def _set_filter_field(node, k):
        """Point the first field reference in the first filter's condition at column k."""
        if isinstance(node, dict):
            if "filter" in node and "condition" in node["filter"]:
                _stack = [node["filter"]["condition"]]
                while _stack:
                    _n = _stack.pop()
                    if isinstance(_n, dict) and "structField" in _n:
                        _n["structField"]["field"] = k
                        return True
                    if isinstance(_n, dict):
                        _stack.extend(_n.values())
                    elif isinstance(_n, list):
                        _stack.extend(_n)
            return any(_set_filter_field(v, k) for v in node.values())
        if isinstance(node, list):
            return any(_set_filter_field(v, k) for v in node)
        return False

    _plan = json.loads(
        substrait_json(con, "select id, amount * 2 as doubled from orders where amount > 10")
    )
    _set_filter_field(_plan, field_index.value)
    _code, _out = substrait_check(json.dumps(_plan))
    _out = "\n".join(l for l in _out.splitlines() if not l.startswith("rows"))
    mo.vstack(
        [
            mo.md(f"```text\n{_out}\n```"),
            mo.callout(
                mo.md(
                    "Well-formed: the filter reads `orders`, whose 3 columns are `$0` to `$2`."
                    if _code == 0
                    else f"Rejected (exit code {_code}): `orders` has 3 columns (`$0` to `$2`), "
                    f"so `${field_index.value}` doesn't exist."
                ),
                kind="success" if _code == 0 else "danger",
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    (`$0` is well-formed but compares `id` instead of `amount` with 10:
    well-formedness rules out references to nothing, not references to the
    wrong thing.
    Catching *that* is what contracts are for, from chapter 4 on.)

    ## Lean as a reference engine

    `Rel.eval` is executable, so the checker can also *run* a plan, as long
    as the data is inside the plan. `sverify.testing.inline_tables` replaces
    each table read by a Substrait `VALUES` list, and `lean_rows` runs that
    plan through `Rel.eval`. This is how the test suite compares the engines
    against the Lean semantics, the definition of correct.

    Here is your query from above, run by Lean and by DataFusion on the same
    rows:
    """)
    return


@app.cell(hide_code=True)
def _(con, display, json, mo, plan, sql):
    from sverify.engine import run_sql
    from sverify.engines import table_rows
    from sverify.testing import canonical, inline_tables, lean_rows

    if plan is None:
        _out = mo.md("*Fix the SQL above first.*")
    else:
        _cols = json.loads(plan)["relations"][0]["root"]["names"]
        _data = {t: table_rows(con, t) for t in ("orders", "customers")}
        try:
            _lean = lean_rows(json.dumps(inline_tables(json.loads(plan), _data)))
            _df = [tuple(r.values()) for r in run_sql(con, sql.value).to_pylist()]
            _out = mo.vstack(
                [
                    display.side_by_side(
                        display.table(_lean, _cols, title="Lean's Rel.eval"),
                        display.table(_df, _cols, title="DataFusion"),
                    ),
                    display.verdict(
                        canonical(_lean) == canonical(_df),
                        "Same rows ✓ (as bags: order aside)",
                        "Different rows ✗: that would be a bug in the parser or the engine",
                    ),
                ]
            )
        except Exception as _e:
            _out = mo.callout(mo.md(f"Lean can't run this plan: `{_e}`"), kind="warn")
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Writing plans back out

    `--write` prints the plan as Lean understood it, as Substrait JSON
    produced from the `Rel` (`sverify.engines.written_plan` in Python). That is the plan
    the other engines run (chapter 11), so whatever runs is exactly what was
    checked, not DataFusion's original JSON. Here are the first few hundred
    characters for your query:
    """)
    return


@app.cell(hide_code=True)
def _(mo, plan, written_plan):
    try:
        _written = written_plan(plan) if plan else ""
        _out = mo.md(f"```json\n{_written[:600]}…\n```") if _written else mo.md("")
    except ValueError as _e:
        _out = mo.callout(mo.md(f"`{_e}`"), kind="warn")
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## How much of Ibis gets through

    Not every query fits the Lean model yet. `sverify.coverage` compiles a
    list of Ibis operations and hands each to the checker: ✓ means it is
    verified (so contracts apply), ✗ that the checker refuses it, – that Ibis
    or DataFusion fails before there is a plan, and *inc.* that it can also
    be maintained incrementally. Refusing is the safe default: a plan outside
    the model is never checked against the wrong semantics.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    from sverify import coverage

    mo.md(coverage.table(coverage.results()))
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 13. [Plans, meaning and proofs](?file=13_plans_and_proofs.py) · [Contents](?file=00_start_here.py) · 15. [What is proved, what is trusted](?file=15_trust.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
