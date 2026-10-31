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
app = marimo.App(width="medium", app_title="5. Keys and relations")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 4. [Contracts](?file=04_contracts.py) · [Contents](?file=00_start_here.py) · 6. [Runtime errors](?file=06_runtime_errors.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 5. Keys and relations

    Say you add each customer's city to the orders table so finance can sum
    revenue by city. If one customer appears twice in `customers`, their
    orders are counted twice, and the totals stop matching the ledger
    without anyone being told why.

    The facts in chapter 4 were about one value at a time: "this column is
    never NULL", "this one is at least 22". Facts like "one row per order"
    are of another kind, and two such kinds matter as much in practice:

    * **keys**: "no two rows have the same `id`", a fact about pairs of rows;
    * **relations between columns**: "`end` is after `start`", "`t1` is
      exactly one minute after `t0`", a fact about two values in one row.

    ## Keys with `sv.unique`

    `sv.unique("id")` says the listed columns identify a row. In `requires`
    it is a promise about an input (checked on the data when the input is
    bound, like any precondition). In `ensures` it is **proved**: keys
    survive filters and projections, and joins whose condition pins down at
    most one partner on the other side.

    Joining orders with customers keeps one row per order only if each
    customer name appears once. We'll try it both ways with the switch:
    """)
    return


@app.cell
def _():
    import ibis
    import sverify as sv

    orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    customers = ibis.table({"name": "string", "city": "string"}, name="customers")

    def with_city(orders, customers):
        return orders.join(customers, orders.customer == customers.name).select(
            orders.id, orders.customer, customers.city
        )

    return customers, ibis, orders, sv, with_city


@app.cell(hide_code=True)
def _(mo):
    names_unique = mo.ui.switch(value=False, label="requires customers: unique(name)")
    names_unique
    return (names_unique,)


@app.cell
def _(customers, names_unique, orders, sv, with_city):
    _requires = {"orders": [sv.unique("id")]}
    if names_unique.value:
        _requires["customers"] = [sv.unique("name")]
    sv.verify(with_city(orders, customers), requires=_requires, ensures=[sv.unique("id")])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Without the key on `name`, Lean refuses, and rightly so: here is the
    counterexample it could not rule out, run on DataFusion. `bob` moved and
    was entered twice, once per city, so his one order shows up twice and
    finance's totals are off by his 5.
    """)
    return


@app.cell(hide_code=True)
def _(display, ibis, sv, with_city):
    con = sv.connect()
    sv.create_table(
        con,
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 5)],
    )
    sv.create_table(
        con,
        "customers",
        ibis.schema({"name": "string", "city": "string"}),
        [("ada", "Paris"), ("bob", "Oslo"), ("bob", "Rome")],
    )
    display.side_by_side(
        display.table(sv.table_rows(con, "customers"), ["name", "city"], title="customers"),
        display.arrow(
            with_city(con.table("orders"), con.table("customers")), title="with_city: id 2 twice"
        ),
    )
    return (con,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With the key in `requires`, calling a contracted function on these
    tables stops at the precondition check instead, before finance sees a
    number:
    """)
    return


@app.cell
def _(con, mo, sv, with_city):
    contracted = sv.transform(
        requires={"orders": [sv.unique("id")], "customers": [sv.unique("name")]},
        ensures=[sv.unique("id")],
    )(with_city)
    try:
        contracted(con.table("orders"), con.table("customers"))
    except sv.PreconditionError as _e:
        _err = _e
    mo.callout(mo.md(f"**PreconditionError**: {_err}"), kind="danger")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Other ways to get a key, all proved in `SubstraitLean/Keys.lean`
    (`Rel.keys_sound`):

    * `DISTINCT` rows are a key: all their columns together;
    * semi and anti joins keep the left side's keys (they only drop rows);
    * a filter `x = 3` drops `x` from a key: `unique(id, customer)` and
      `customer = 'ada'` give `unique(id)`;
    * `ROW_NUMBER()` with the partition columns is a key (chapter 7).
    """)
    return


@app.cell
def _(orders, sv):
    sv.verify(
        orders.filter(orders.customer == "ada").select("id", "amount"),
        requires={"orders": [sv.unique("id", "customer")]},
        ensures=[sv.unique("id")],
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Relations between columns

    Filter and join conditions such as `a.t = b.t + 1`, `start < end` or
    `value != -9999` become **facts about the row**, and they survive
    projections, joins and unions. Postconditions such as `t1 - t0 == 1` or
    `t1 > t0` then follow.

    Say you prepare training data for a forecasting model. Readings arrive
    once a minute, `-9999` marks a sensor error, and the model needs pairs
    of *consecutive* clean readings. Whoever trains it will assume each pair
    is exactly one minute apart and that no `-9999` slipped through, so
    we'll prove both. The pipeline joins the clean readings with
    themselves, one minute apart:
    """)
    return


@app.cell
def _(ibis):
    readings = ibis.table(
        {"sensor": "string", "minute": "int64", "value": "int64"}, name="readings"
    )

    def consecutive(readings, one_sensor=True):
        clean = readings.filter(readings.value != -9999)
        if one_sensor:
            clean = clean.filter(clean.sensor == "a")
        w0, w1 = clean.view(), clean.view()
        return w0.join(w1, w1.minute == w0.minute + 1).select(
            t0=w0.minute, t1=w1.minute, v0=w0.value, v1=w1.value
        )

    return consecutive, readings


@app.cell(hide_code=True)
def _(mo):
    req_notnull = mo.ui.switch(value=True, label="requires minute IS NOT NULL")
    req_key = mo.ui.switch(value=True, label="requires unique(sensor, minute)")
    one_sensor = mo.ui.switch(value=True, label="pipeline keeps only sensor 'a'")
    mo.vstack([req_notnull, req_key, one_sensor])
    return one_sensor, req_key, req_notnull


@app.cell
def _(consecutive, one_sensor, readings, req_key, req_notnull, sv):
    from ibis import _

    _requires = [
        c
        for c, on in [
            (_.minute.notnull(), req_notnull.value),
            (sv.unique("sensor", "minute"), req_key.value),
        ]
        if on
    ]
    sv.verify(
        consecutive(readings, one_sensor.value),
        requires={"readings": _requires},
        ensures=[_.t1 - _.t0 == 1, _.t1 > _.t0, _.v0 != -9999, _.v1 != -9999, sv.unique("t0")],
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What each switch does:

    * **`minute IS NOT NULL`**: without it, `t1 - t0 == 1` is "TRUE or NULL".
      The join condition `w1.minute = w0.minute + 1` is TRUE only for
      non-NULL values, but Lean only derives that for plain column
      comparisons, not through the `+ 1`. Lean is conservative: when it
      can't see a reason, it says so.
    * **`unique(sensor, minute)`**: one reading per sensor and minute. Within
      sensor `a` that makes `minute` a key, and the join finds at most one
      `t1` per `t0`, so `unique(t0)` holds.
    * **only sensor `a`**: with several sensors the join pairs readings of
      *different* sensors too (there's no `sensor` in the join condition), so
      `t0` repeats. The relations still hold: they're about each row.

    The facts behind these proofs are `Expr.factsOf_sound` and
    `Rel.facts_sound` in `SubstraitLean/Contracts.lean`: a fact `x − y ∈ [lo,
    hi]` or `x ≠ k` taken from a condition holds on every row that passes
    it, and is kept by every operator above.

    Relations that need more than "a column plus a constant" (`a < 2 * b`)
    and relations between strings are not tracked yet.

    You can now prove that a result has one row per key, and that its
    columns keep the relations the filters and joins set up. Finance's
    join stays one row per order, and whoever trains the model gets pairs
    exactly one minute apart, as they assume. **Next up:**
    [Runtime errors](?file=06_runtime_errors.py), where a plan that is
    correct can still crash, or quietly give a wrong number.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 4. [Contracts](?file=04_contracts.py) · [Contents](?file=00_start_here.py) · 6. [Runtime errors](?file=06_runtime_errors.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
