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
app = marimo.App(width="medium", app_title="3. Contracts")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 2. [The checker](?file=02_the_checker.py) · [Contents](?file=00_start_here.py) · 4. [Keys and relations](?file=04_keys_and_relations.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 3. Contracts

    In verified programming you state what a function **requires** of its
    inputs (preconditions) and what it **ensures** about its output
    (postconditions), and the machine proves the second follows from the
    first. `sverify` brings that to data transformations: a function from
    Ibis tables to an Ibis table, with a decorator that states the contract.

    ## A first contract
    """)
    return


@app.cell
def _():
    import warnings

    import ibis
    import sverify as sv
    from ibis import _

    # An unbound table: just a name and a schema, no data.
    orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.id.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
    )
    def doubled(orders):
        return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

    doubled(orders)  # proves the postconditions, or raises VerificationError
    doubled.last_report
    return doubled, ibis, orders, sv, warnings


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * `requires` maps each **parameter** of the function to conditions on
      that input. `ensures` lists conditions on the output.
    * Conditions are Ibis expressions over the table's columns (`_.amount >= 0`,
      using Ibis's `_` placeholder, or a function of the table) or SQL
      snippets (`"id IS NOT NULL"`).
    * Calling `doubled(orders)` builds the Ibis expression as usual. Before
      returning it, `sverify` sends the plan and the conditions to the Lean
      checker (`substrait-check --contract`), which tries to **prove** every
      postcondition. The verdicts are in `.last_report`.
    * The first table of the report has the verdicts. The second is
      everything Lean established about each output column, whether you
      asked or not: a free, proved data dictionary.
    * The ⚠️ row says `amount * 2` may leave the 64-bit range and wrap around,
      since nothing bounds `amount` from above. Chapter 6 is about these.

    `sv.verify(expr, requires=..., ensures=...)` does the same for an
    expression without a decorator; it returns the report instead of raising.

    ## How does Lean know `doubled ≥ 22`?

    It runs the plan on *descriptions* of values instead of values: for each
    column, whether it can be NULL and which values it can hold. This is
    called *abstract interpretation*. Each operator updates the descriptions:

    * the precondition says `amount >= 0` is TRUE on every input row, so
      `amount` is a non-NULL integer ≥ 0 (`NULL >= 0` is NULL, not TRUE);
    * the filter `amount > 10` keeps only rows where that is TRUE, so `amount`
      is a non-NULL integer ≥ 11 afterwards (NULL > 10 is not TRUE);
    * `amount * 2` is then an integer ≥ 22, and never NULL.

    A postcondition is proved when its description says it can only be TRUE.
    Change the transformation and the conditions below and watch what Lean
    can establish:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    threshold = mo.ui.slider(
        -10, 50, value=10, label="filter: keep orders with amount >", show_value=True
    )
    factor = mo.ui.slider(-3, 5, value=2, label="new column: doubled = amount ×", show_value=True)
    pre_nonneg = mo.ui.checkbox(value=True, label="requires amount ≥ 0")
    pre_upper = mo.ui.checkbox(value=False, label="requires amount ≤ 100")
    post = mo.ui.text(value="doubled >= 20", label="ensures (SQL)", full_width=True)
    mo.vstack([threshold, factor, mo.hstack([pre_nonneg, pre_upper], justify="start"), post])
    return factor, post, pre_nonneg, pre_upper, threshold


@app.cell(hide_code=True)
def _(display, factor, mo, orders, post, pre_nonneg, pre_upper, sv, threshold):
    from ibis import _

    _o = orders
    _pre = [
        c for c, on in [(_.amount >= 0, pre_nonneg.value), (_.amount <= 100, pre_upper.value)] if on
    ]
    _filtered = _o.filter(_o.amount > threshold.value)
    _result = _filtered.select(_o.id, doubled=_o.amount * factor.value)
    _req = {"orders": _pre}

    def _facts(expr, col):
        return sv.verify(expr, requires=_req).facts[col]

    _stages = [
        ["orders (input)", _facts(_o.select("amount"), "amount"), ""],
        [
            f"after filter amount > {threshold.value}",
            _facts(_filtered.select("amount"), "amount"),
            "",
        ],
        [f"doubled = amount × {factor.value}", "", _facts(_result, "doubled")],
    ]
    try:
        _check = sv.verify(_result, requires=_req, ensures=[post.value]).ensures[0]
        _verdict = mo.callout(
            mo.md(
                f"`{post.value}` is **proved** ✓"
                if _check.proved
                else f"`{post.value}` is **not proved**: Lean can only show it is {_check.value}."
            ),
            kind="success" if _check.proved else "warn",
        )
    except Exception as _e:
        _verdict = mo.callout(mo.md(f"Could not check `{post.value}`: {_e}"), kind="danger")
    mo.vstack(
        [
            display.table(_stages, ["step", "what Lean knows about amount", "… about doubled"]),
            _verdict,
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Things to try: untick *amount ≥ 0* and pick a negative factor; set the
    threshold below 0; untick it again, ask for `doubled IS NOT NULL` and think
    about why it holds even though `amount` can now be NULL in the input; tick *amount ≤ 100*
    and ask for `doubled <= 200`.

    ## When a proof fails

    A postcondition that doesn't follow is refused, with what Lean *could*
    establish. Here the precondition allows `amount = 0`, so `total` can be 1:
    """)
    return


@app.cell
def _(mo, orders, sv):
    from ibis import _

    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    try:
        plus_one(orders)
    except sv.VerificationError as _e:
        _err = _e
    mo.md(f"```text\nVerificationError: {_err}\n```")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    "It is TRUE or FALSE" is Lean's honest answer: for some allowed inputs
    `total > 5` holds, for others it doesn't. Lean never guesses. A refusal
    can also mean the truth is out of reach of the analysis (the end of this
    chapter lists what it tracks), so a ❌ is "not proved", not "false".

    ## Contracts on real data

    So far the table had no data: the proof is about *every* possible
    `orders`. Bind it to real tables and two more things happen:

    1. **Preconditions are checked on the data** at call time, because they
       are assumptions about the outside world, and the outside world lies.
       A violation raises `PreconditionError`.
    2. **Unproved postconditions** can be checked on the output instead of
       refusing the call, with `on_unproved`:

    | `on_unproved=` | what happens when a postcondition isn't proved |
    |:---|:---|
    | `"error"` (default) | raise `VerificationError`; nothing runs |
    | `"runtime"` | run the pipeline and check that condition on the actual output; raise `PostconditionError` on a violation |
    | `"warn"` | issue a warning and carry on |

    Some data, with a sneaky NULL:
    """)
    return


@app.cell
def _(display, ibis, sv):
    con = sv.connect()  # plans run on DuckDB by default
    _schema = ibis.schema({"id": "int64", "customer": "string", "amount": "int64"})
    sv.create_table(con, "orders", _schema, [(1, "ada", 30), (2, "bob", 5), (3, "cy", None)])
    display.table(sv.table_rows(con, "orders"), ["id", "customer", "amount"], title="orders")
    return (con,)


@app.cell(hide_code=True)
def _(mo):
    mode = mo.ui.radio(
        ["error", "runtime", "warn"], value="runtime", label="on_unproved", inline=True
    )
    with_pre = mo.ui.switch(value=False, label="requires amount ≥ 0")
    mo.hstack([mode, with_pre], justify="start", gap=2)
    return mode, with_pre


@app.cell
def _(con, display, mo, mode, sv, warnings, with_pre):
    from ibis import _

    @sv.transform(
        requires={"orders": [_.amount >= 0]} if with_pre.value else {},
        ensures=[_.amount < 100],
        on_unproved=mode.value,
    )
    def passthrough(orders):
        return orders.select("id", "amount")

    with warnings.catch_warnings(record=True) as _caught:
        warnings.simplefilter("always")
        try:
            _rows = passthrough(con.table("orders")).to_pyarrow()
            _out = display.arrow(_rows, title="the result")
            if _caught:
                _out = mo.vstack(
                    [mo.callout(mo.md(f"**Warning:** {_caught[0].message}"), kind="warn"), _out]
                )
        except (sv.PreconditionError, sv.PostconditionError, sv.VerificationError) as _e:
            _out = mo.callout(
                mo.md(f"**{type(_e).__name__}**: {str(_e).splitlines()[0]}"), kind="danger"
            )
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With the default settings, `amount < 100` can't be proved (nothing bounds
    `amount`), so `"runtime"` checks it on the output. It fails for one row:
    **NULL < 100 is not TRUE**, so the NULL row counts as a violation. A
    contract condition must be TRUE, not just "not FALSE".

    Switch on *requires amount ≥ 0*: now the precondition check fails first,
    for the same NULL. Pass `check_requires=False` to `sv.transform` to trust
    the inputs instead (the proofs then rest on that trust).

    ### Schemas count too

    A column declared non-nullable (`"!int64"` in Ibis) is never NULL, and
    Lean knows it, so `amount IS NOT NULL` needs no precondition:
    """)
    return


@app.cell
def _(ibis, sv):
    strict = ibis.table({"id": "!int64", "amount": "!int64"}, name="strict")
    sv.verify(strict.select("id", "amount"), ensures=["amount IS NOT NULL"])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## The theorem behind the ✅

    Every ✅ in this tour is an instance of `contract_sound` in
    `SubstraitLean/Contracts.lean`:

    ```lean
    theorem contract_sound (hcat : cat.WF)
        (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)               -- rows match the schema
        (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue)  -- preconditions hold
        (hQ : Q.WF cat)
        (hproved : (Q.aeval cat fun t => tableEnv (S t) (pre t)).all AVal.certainlyTrue) :
        ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true                   -- postconditions hold
    ```

    Read: *if every input row matches its schema and satisfies the
    preconditions, and the abstract interpretation (`aeval`) says every
    postcondition is certainly TRUE, then every postcondition is TRUE on
    every output row.* `hproved` is what the checker computes for your plan;
    the rest are assumptions about the data, which `sverify` checks when the
    data is there.

    ## What Lean tracks

    Per column: whether it can be NULL, an integer or double range, which
    booleans it can be, timestamps, and whether it can be a string. Filters
    such as `amount > 10`, `x = 3`, `x IN (1, 2, 3)` and `x IS NOT NULL`
    refine those facts; arithmetic, comparisons, `AND`/`OR`/`NOT` with SQL's
    NULL semantics, `CASE`, `COALESCE`, joins and `UNION ALL` propagate them.
    The next chapters add **keys** and **relations between columns** (4),
    doubles, time and text (5), runtime errors (6) and window functions (7).

    Not tracked yet: relations that need more than "column plus constant"
    (`a < 2 * b`), string contents, DECIMAL columns, and counts across rows.
    Postconditions like those are refused rather than guessed; use
    `on_unproved="runtime"` to check them on the data instead.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 2. [The checker](?file=02_the_checker.py) · [Contents](?file=00_start_here.py) · 4. [Keys and relations](?file=04_keys_and_relations.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
