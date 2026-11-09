# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "sverify[datafusion]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="compact", app_title="4. Contracts")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 3. [An orders mart](?file=03_orders_mart.py) · 5. [Pipelines and engines](?file=05_pipelines_and_engines.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 4. Contracts

    Say a colleague's transformation feeds the billing job you own. Its
    docstring promises that the new column is never negative and never NULL,
    and customers are invoiced on that promise. You would like it proved.

    In verified programming a function states what it requires of its inputs
    (preconditions) and what it ensures about its output (postconditions),
    and a machine proves the second follows from the first. Sverify does this
    for a data transformation: a function from Ibis tables to an Ibis table,
    with a decorator that states the contract. This chapter covers the
    contract itself, keys and relations between columns, runtime errors,
    windows and composing contracts. The proofs are described in
    [how it works](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-it-works.md).

    ## A first contract

    We'll write one.
    """)
    return


@app.cell
def _():
    import warnings

    import ibis
    import sverify as sv
    from ibis import _
    from sverify.errors import (
        CompositionError,
        PostconditionError,
        PreconditionError,
        VerificationError,
    )

    # An unbound table has a name and a schema and no data.
    orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, _.id.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
    )
    def doubled(orders):
        return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

    doubled(orders)  # proves the postconditions, or raises VerificationError
    doubled.report
    return (
        CompositionError,
        PostconditionError,
        PreconditionError,
        VerificationError,
        doubled,
        ibis,
        orders,
        sv,
        warnings,
    )


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * `requires` maps each parameter of the function to conditions on that
      input. `ensures` lists conditions on the output.
    * Conditions are Ibis expressions over the table's columns
      (`_.amount >= 0`, using Ibis's `_` placeholder) or SQL snippets
      (`"id IS NOT NULL"`).
    * Calling `doubled(orders)` builds the Ibis expression as usual. Before
      returning it, sverify sends the plan and the conditions to the Lean
      checker (`substrait-check --contract`), which tries to prove every
      postcondition. The verdicts are in `.report`.
    * The first table of the report holds the verdicts. The second holds
      everything Lean established about each output column, asked for or not.
    * `amount < 1_000_000_000` is there for `amount * 2`. Doubling the
      largest 64-bit integer overflows and the reference raises, so the
      plan needs an upper bound on `amount`. Without one, Sverify works out
      the weakest, `amount < 2**62`, and reports the plan as not proved
      until you declare a bound. Like every precondition, it is
      checked on your data, or proved from table metadata.

    `sv.verify(expr, requires=..., ensures=...)` does the same for an
    expression without a decorator and returns the report.

    ## How Lean knows `doubled ≥ 22`

    Lean runs the plan on descriptions of values: for each column, whether it
    can be NULL and which values it can hold. This is abstract interpretation,
    and each operator updates the descriptions.

    * The preconditions make `amount >= 0` and `amount < 1_000_000_000`
      TRUE on every input row, so `amount` is a non-NULL integer in
      `[0, 10⁹ - 1]`. (`NULL >= 0` is NULL, which is not TRUE.)
    * The filter `amount > 10` keeps the rows where that is TRUE, so `amount`
      is a non-NULL integer ≥ 11 afterwards.
    * `amount * 2` is then an integer in `[22, 2·10⁹ - 2]`, which fits in
      64 bits and is never NULL.

    A postcondition is proved when its description allows only TRUE.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## When a proof fails

    A promise that does not follow is refused, together with what Lean could
    establish. Here the precondition allows `amount = 0`, so `total` can be 1:
    """)
    return


@app.cell
def _(VerificationError, mo, orders, sv):
    from ibis import _

    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    try:
        plus_one(orders)
    except VerificationError as _e:
        _err = _e
    mo.md(f"```text\nVerificationError: {_err}\n```")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    "It may be FALSE on some rows" is Lean's answer when `total > 5` holds for
    some allowed inputs and fails for others. A refusal can also mean the truth is
    out of reach of the analysis (the list at the end of this section says
    what it tracks), so a refusal means "not proved".

    ## Contracts on real data

    So far the table had no data, and the proof covered every possible
    `orders`. Real tables come from upstream systems, and binding the
    function to one adds two things.

    1. Preconditions are checked on the data at call time, because they are
       assumptions about the outside world. A violation raises
       `PreconditionError`.
    2. An unproved postcondition can be checked on the output instead of
       refusing the call, with `on_unproved`.

    | `on_unproved=` | what happens when a postcondition is not proved |
    |:---|:---|
    | `"error"` (default) | `VerificationError`; nothing runs |
    | `"check"` | the pipeline runs and the condition is checked on the output; a violation raises `PostconditionError` |
    | `"warn"` | a warning, and the pipeline runs |

    Take a table with a NULL in it and the condition `amount < 100`, which
    nothing bounds, so it is not proved. With `"check"` the pipeline runs
    and the condition is checked on the output.
    """)
    return


@app.cell
def _(display, ibis, sv):
    con = sv.connect()  # plans run on DuckDB
    _schema = ibis.schema({"id": "int64", "customer": "string", "amount": "int64"})
    con.create("orders", _schema, [(1, "ada", 30), (2, "bob", 5), (3, "cy", None)])
    display.table(con.rows("orders"), ["id", "customer", "amount"], title="orders")
    return (con,)


@app.cell
def _(PostconditionError, con, mo, sv):
    from ibis import _

    @sv.transform(ensures=[_.amount < 100], on_unproved="check")
    def passthrough(orders):
        return orders.select("id", "amount")

    try:
        passthrough(con.table("orders")).to_pyarrow()
    except PostconditionError as _e:
        _err = _e
    mo.callout(mo.md(f"PostconditionError: {str(_err).splitlines()[0]}"), kind="danger")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The check fails for cy's row: `NULL < 100` is not TRUE, so the NULL counts
    as a violation. A contract condition must be TRUE. A precondition
    `amount >= 0` would fail first, for the same NULL, and
    `check_requires=False` on `sv.transform` trusts the inputs, so that the
    proofs rest on that trust.

    A column declared non-nullable (`"!int64"` in Ibis) is never NULL, and
    Lean knows it, so `amount IS NOT NULL` needs no precondition.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### What backs a proof

    Theorem `contract_sound` in `analysis/Sverify/Analysis/Contracts.lean` says: if every
    input row matches its schema and satisfies the preconditions, and the
    abstract interpretation says every postcondition is certainly TRUE, then
    every postcondition is TRUE on every output row. Sverify checks the
    hypotheses about the data when the data is there.

    ### What Lean tracks

    Per column: whether it can be NULL, integer and double ranges, timestamps,
    which booleans it can be, and which strings it can be while they are few.
    Filters such as `amount > 10`, `x = 3`, `x IN (1, 2, 3)`,
    `status <> 'cancelled'` and `x IS NOT NULL` refine those facts. Arithmetic, comparisons, `AND`/`OR`/`NOT` with SQL's NULL
    semantics, `CASE`, `COALESCE`, joins and `UNION ALL` carry them through.
    Keys and relations between columns come next. Not tracked yet: relations
    that need more than a column plus a constant (`a < 2 * b`), what is
    inside a string and counts across rows. For those,
    `on_unproved="check"` checks the condition on the data.

    ## Keys

    Say you add each customer's city to the orders so finance can sum revenue
    by city. If a customer appears twice in `customers`, their orders are
    counted twice, and the totals stop matching the ledger.

    `sv.unique("id")` says the listed columns identify a row. In `requires`
    it is an assumption about an input, checked on the data when the input is
    bound. In `ensures` it is proved: keys survive filters and projections,
    and joins whose condition pins down at most one partner on the other
    side. We'll join orders with customers, with and without a key on the
    customer names.
    """)
    return


@app.cell
def _(ibis):
    customers = ibis.table({"name": "string", "city": "string"}, name="customers")

    def with_city(orders, customers):
        return orders.join(customers, orders.customer == customers.name).select(
            orders.id, orders.customer, customers.city
        )

    return customers, with_city


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
    Without the key on `name`, Lean refuses. Say Bob moved and was entered
    twice, once per city: his one order then appears twice and finance's
    totals are off by his 5. With the key in `requires`, a contracted
    function stops at the precondition check before finance sees a number.
    """)
    return


@app.cell
def _(PreconditionError, ibis, mo, sv, with_city):
    con_keys = sv.connect()
    con_keys.create(
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 5)],
    )
    con_keys.create(
        "customers",
        ibis.schema({"name": "string", "city": "string"}),
        [("ada", "Paris"), ("bob", "Oslo"), ("bob", "Rome")],
    )
    contracted = sv.transform(
        requires={"orders": [sv.unique("id")], "customers": [sv.unique("name")]},
        ensures=[sv.unique("id")],
    )(with_city)
    try:
        contracted(con_keys.table("orders"), con_keys.table("customers"))
    except PreconditionError as _e:
        _err = _e
    mo.callout(mo.md(f"PreconditionError: {_err}"), kind="danger")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Keys come from other places too, all proved in `analysis/Sverify/Analysis/Keys.lean`
    (`Rel.keys_sound`).

    * `DISTINCT` rows are a key: all their columns together.
    * Semi and anti joins keep the left side's keys.
    * A filter `x = 3` drops `x` from a key: `unique(id, customer)` and
      `customer = 'ada'` give `unique(id)`.
    * `ROW_NUMBER()` with the partition columns is a key (see Windows below).
    * `sv.references("cust", to=("customers", "id"))` in `requires` says every
      non-NULL `cust` occurs in `customers.id`. It is an assumption, checked
      on the data, and nothing proves it in `ensures`.
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
    ### Foreign keys and row caps

    An order for a customer who isn't in `customers` drops out of the join,
    and its revenue with it. `sv.references` states that every customer an
    order names exists, and `sv.key` is a key whose columns are never NULL.
    We'll add an order for Cy, whom `customers` doesn't know:
    """)
    return


@app.cell
def _(PreconditionError, ibis, mo, sv, with_city):
    con_refs = sv.connect()
    con_refs.create(
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 5), (3, "cy", 12)],
    )
    con_refs.create(
        "customers",
        ibis.schema({"name": "string", "city": "string"}),
        [("ada", "Paris"), ("bob", "Oslo")],
    )
    _with_city = sv.transform(
        requires={
            "orders": [sv.key("id"), sv.references("customer", to=("customers", "name"))],
            "customers": [sv.key("name")],
        },
        ensures=[sv.key("id")],
    )(with_city)
    try:
        _with_city(con_refs.table("orders"), con_refs.table("customers"))
    except PreconditionError as _e:
        _err = _e
    mo.callout(mo.md(f"PreconditionError: {_err}"), kind="danger")
    return (con_refs,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Cy's order is caught before the join drops it. Nothing proves a foreign
    key in `ensures`: it stays a precondition, checked on the data.

    A row cap works the other way round. `sv.max_rows(n)` in `requires` is
    checked on the data, and Lean carries it through the plan
    (`Rel.maxRows_sound`). With it, a sum of amounts per customer is proved
    to fit 64 bits, and the cap on the output is proved too. Without it, the
    report assumes the sum fits and checks it as the job runs:
    """)
    return


@app.cell
def _(con_refs, sv):
    from ibis import _

    _orders = con_refs.table("orders")
    _totals = _orders.group_by("customer").aggregate(total=_orders.amount.sum())
    _amounts = [_.amount >= 0, _.amount <= 1_000_000]
    capped = sv.verify(
        _totals,
        requires={"orders": [*_amounts, sv.max_rows(1_000_000)]},
        ensures=[_.total >= 0, sv.max_rows(1_000_000)],
    )
    uncapped = sv.verify(_totals, requires={"orders": _amounts}, ensures=[_.total >= 0])
    assert capped.proved and not capped.assumed
    {"with sv.max_rows": capped.rows, "assumed without it": [str(a) for a in uncapped.assumed]}
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Relations between columns

    Filter and join conditions such as `a.t = b.t + 1`, `start < end` or
    `value != -9999` become facts about each row. The facts survive
    projections, joins and unions, and postconditions such as `t1 - t0 == 1`
    or `t1 > t0` follow from them.

    Say you prepare training data for a forecasting model. Readings arrive
    once a minute and `-9999` marks a sensor error. Whoever trains the model
    assumes each pair is exactly one minute apart and that no `-9999` slipped
    through. We'll prove both for a pipeline that joins the clean readings
    with themselves, one minute apart.
    """)
    return


@app.cell
def _(ibis):
    sensor_minutes = ibis.table(
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

    return consecutive, sensor_minutes


@app.cell(hide_code=True)
def _(mo):
    req_notnull = mo.ui.switch(value=True, label="requires minute IS NOT NULL")
    req_key = mo.ui.switch(value=True, label="requires unique(sensor, minute)")
    one_sensor = mo.ui.switch(value=True, label="pipeline keeps only sensor 'a'")
    mo.vstack([req_notnull, req_key, one_sensor])
    return one_sensor, req_key, req_notnull


@app.cell
def _(consecutive, one_sensor, req_key, req_notnull, sensor_minutes, sv):
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
        consecutive(sensor_minutes, one_sensor.value),
        requires={"readings": _requires},
        ensures=[_.t1 - _.t0 == 1, _.t1 > _.t0, _.v0 != -9999, _.v1 != -9999, sv.unique("t0")],
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What each switch does:

    * `minute IS NOT NULL`: without it, `t1 - t0 == 1` is "TRUE or NULL". The
      join condition `w1.minute = w0.minute + 1` is TRUE only for non-NULL
      values, but Lean derives that for plain column comparisons and not
      through the `+ 1`. When Lean sees no reason, it says so.
    * `unique(sensor, minute)`: one reading per sensor and minute. Within
      sensor `a` that makes `minute` a key, and the join finds at most one
      `t1` per `t0`, so `unique(t0)` holds.
    * Only sensor `a`: with several sensors the join also pairs readings of
      different sensors, because `sensor` is not in the join condition, and
      `t0` repeats. The relations still hold, since they are about each row.

    The facts are `Expr.factsOf_sound` and `Rel.facts_sound` in
    `analysis/Sverify/Analysis/Contracts.lean`: a fact `x − y ∈ [lo, hi]` or `x ≠ k`
    taken from a condition holds on every row that passes it, and every
    operator above keeps it.

    ## Runtime errors

    Say you are on call this week. At 3 a.m. a pipeline that was correct
    crashes on a row nobody expected, and it pages you. A pipeline that
    quietly writes a wrong number is worse, because nobody gets paged.

    Some operations can fail. The reference raises on each of these, and
    the report lists every one a plan may hit
    ([Runtime errors](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#runtime-errors)).

    * Integer `/` or `%` by zero, and `-9223372036854775808 / -1`, which
      does not fit in 64 bits.
    * `CAST(x AS BIGINT)` of NaN, ±∞ or a huge double, also after `ROUND`.
    * Integer `POWER` with a negative exponent or a huge result.
    * A regular expression that does not compile.
    * Truncating a timestamp near the ends of its range to a month or year.
      DataFusion, an optional engine outside the
      [1.x promise](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines), panics or returns garbage there.
    * `+`, `-`, `*` leaving the declared width (64 bits for `BIGINT`). The
      reference raises, and so do the DuckDB and Polars translations.
      DataFusion wraps around (`2⁶² + 2⁶²` gives `-2⁶³`), which an error
      allows.
    * An integer `SUM` leaving 64 bits. Sverify rules it out where the plan
      bounds a group's rows (a `FETCH` count) and `requires` bounds the
      column. Elsewhere it assumes each sum fits, and the job checks it on
      the data before the run (`Report.assumed`).

    Lean's model computes with exact integers, and `analysis/Sverify/Analysis/Safety.lean`
    lists, for every operation of a plan, which of these can happen. Theorem
    `Rel.mayIssues_sound` proves the list complete: if the report lists no
    error, no input can trigger one. `@sv.transform` refuses a transformation
    that may fail, even with no postconditions.

    ### Guards

    The usual fix is a guard that keeps the divisor away from zero. Whether a
    guard works depends on when the engine evaluates each part. The variants
    below cover a zero divisor, `MIN` divided by `-1` and doubles a `BIGINT`
    cannot hold. Pick one, and we'll read Lean's report.
    """)
    return


@app.cell
def _(ibis, sv):
    runtime_table = ibis.table({"qty": "int64", "n": "int64", "amount": "float64"}, name="t")
    _t = runtime_table
    VARIANTS = {
        "qty // n (no guard)": _t.select(x=_t.qty // _t.n),
        "filter n != 0, then select qty // n": _t.filter(_t.n != 0).select(x=_t.qty // _t.n),
        "filter n > 0, then select qty // n": _t.filter(_t.n > 0).select(x=_t.qty // _t.n),
        "select qty % nullif(n, 0)": _t.select(x=_t.qty % _t.n.nullif(0)),
        "select CASE WHEN n != 0 THEN qty % n ELSE 0 END": _t.select(
            x=ibis.cases((_t.n != 0, _t.qty % _t.n), else_=0)
        ),
        "filter (n != 0) AND (qty % n > 1)": _t.filter((_t.n != 0) & ((_t.qty % _t.n) > 1)),
        "filter n != 0, then filter qty % n > 1": _t.filter(_t.n != 0).filter((_t.qty % _t.n) > 1),
        "select round(amount) (a cast to BIGINT)": _t.select(x=_t.amount.round()),
        "filter 0 <= amount <= 100, then round(amount)": _t.filter(
            (_t.amount >= 0) & (_t.amount <= 100)
        ).select(x=_t.amount.round()),
        "select qty + 1": _t.select(x=_t.qty + 1),
    }
    return (VARIANTS,)


@app.cell(hide_code=True)
def _(VARIANTS, mo):
    variant = mo.ui.dropdown(list(VARIANTS), value="qty // n (no guard)", label="pipeline")
    variant
    return (variant,)


@app.cell(hide_code=True)
def _(VARIANTS, mo, sv, variant):
    _report = sv.verify(VARIANTS[variant.value])
    if _report.errors:
        _summary = mo.callout(mo.md("Lean cannot rule out a runtime error."), kind="warn")
    elif _report.needs:
        _needs = ", ".join(f"`{n.label}`" for n in _report.needs)
        _summary = mo.callout(
            mo.md(f"Lean proves this cannot fail once you declare {_needs} in `requires`."),
            kind="warn",
        )
    else:
        _summary = mo.callout(mo.md("Lean proves this cannot fail, on any data."), kind="success")
    mo.vstack([_summary, mo.md(_report._repr_markdown_())])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    What the variants show:

    * `nullif(n, 0)` and `CASE` are guards. The engines evaluate a `CASE`
      branch only when its condition holds, `NULLIF` is a `CASE` underneath,
      and Lean evaluates each branch knowing its condition.
    * A filter below a projection guards too, because the projection only
      sees rows that passed. `n != 0` leaves `MIN / -1` open, and `n > 0`
      closes it.
    * The same `AND` is no guard: DuckDB and Polars evaluate both operands,
      so `qty % n` runs on the `n = 0` row
      ([eager AND and OR](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#guards)). The report flags the error inside the
      `AND` and suggests guarding the operation itself with the `CASE` above.
    * An earlier filter is no guard either. An optimizer may merge the two
      filters into one `AND`, as DataFusion's does. Lean models that (`Rel.loose`) and reports
      the error.
    * `round(amount)` becomes a cast to `BIGINT`, which fails on `1e30` and
      NaN. Bounding `amount` first makes it safe, because `ROUND` is exact
      and monotone in the model (`FloatCode.round_mono`).
    * `qty + 1` may fail on `MAX`, where the result does not fit in 64 bits
      and the reference raises. A precondition such as `qty < 1000` rules it
      out.

    A contracted transformation has to be proved free of runtime errors, and
    correctness on the inputs that happen to arrive does not count. We pass
    `on_inferred="off"` to `ratio` to see the error itself: by default Sverify
    works out the precondition `(_.n != 0)` and reports the plan as not
    proved until you declare it in `requires`. Declared, it is checked on
    each batch before the run, so `report.run` and `refresh` refuse a batch
    with `n = 0` with a `PreconditionError` and nothing runs.
    A `SUM` that may overflow, or an operation on doubles that may overflow
    to ±∞, does not block the proof: the assumption is listed in
    `Report.assumed` and checked at run time, on the data before the run.
    """)
    return


@app.cell
def _(VerificationError, ibis, mo, sv):
    @sv.transform(on_inferred="off")
    def ratio(t):
        return t.select(x=t.qty // t.n)

    @sv.transform()
    def safe_ratio(t):
        positive = t.filter(t.n > 0)
        return positive.select(x=positive.qty // positive.n)

    _t = ibis.table({"qty": "int64", "n": "int64"}, name="t")
    try:
        ratio(_t)
    except VerificationError as _e:
        # The first line counts what is missing; the next names it.
        _err = (str(_e).splitlines()[1:] or [str(_e)])[0].strip()
    safe_ratio(_t)
    mo.vstack(
        [
            mo.callout(mo.md(f"`ratio`: VerificationError: {_err}"), kind="danger"),
            mo.callout(mo.md("`safe_ratio`: proved free of runtime errors ✓"), kind="success"),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    `Report.errors` lists the issues a proof has to rule out. `Report.proved`
    is true when every postcondition is proved and there are no errors.

    The timing of evaluation is trusted: when an engine evaluates an
    expression (lazy `CASE`, eager `AND`/`OR`, merged filters, and the
    constant conditions DuckDB evaluates while it plans the query). A
    constant that raises, such as `1 // 0 = 1` in a later `WHEN`, makes
    Sverify report the whole plan as raising, on any data. The test suite
    runs plans on random data, extreme values included,
    and checks that they fail only where Lean reported an error.

    ## Windows and ASOF joins

    Say the maintenance team asks how long each sensor went quiet between
    readings, because a long silence marks a unit to replace before it fails.
    Each reading needs the one before it. SQL looks at neighbouring rows with
    window functions:

    ```sql
    LAG(ts) OVER (PARTITION BY sensor ORDER BY ts)
    ```

    This reads: for each row, the `ts` of the previous row of the same
    sensor, in `ts` order, and NULL for the first one. The model supports
    `LAG`, `LEAD` and `ROW_NUMBER` with any sort direction, NULLs first or
    last, offsets and defaults (`core/Sverify/Core/Window.lean`).
    """)
    return


@app.cell
def _(ibis, sv):
    import datetime as dt

    def at(m, s=0):
        return dt.datetime(2024, 5, 1, 7, m, s)

    con_w = sv.connect()
    con_w.create(
        "readings",
        ibis.schema({"sensor": "string", "ts": "timestamp", "v": "float64"}),
        [
            ("a", at(0), 1.0),
            ("a", at(5), 1.5),
            ("a", at(7), 1.2),
            ("b", at(1), 9.0),
            ("b", at(4), 8.5),
        ],
    )

    def with_neighbours(readings):
        w = ibis.window(group_by=readings.sensor, order_by=readings.ts)
        return readings.select(
            "sensor",
            "ts",
            "v",
            prev_ts=readings.ts.lag().over(w),
            next_v=readings.v.lead().over(w),
            rn=ibis.row_number().over(w),
        )

    return con_w, dt, with_neighbours


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Ibis numbers rows from 0. Lean knows that `LAG(ts)` comes from an earlier
    row of the same partition, so `prev_ts <= ts`, that a lagged partition
    column equals the row's own, and that `ROW_NUMBER()` is never negative.
    The first row's NULL is guarded with `isnull() | …` in the contract below.

    ### Ties

    Sensors sometimes report twice in the same instant. If two readings of a
    sensor share a `ts`, SQL does not say which is previous. The engine
    picks, and may pick differently on the next run, so Lean proves only
    what holds for every pick. Unless `requires` gives a key on the
    partition and order columns, `report.deterministic` is `False` and
    `report.ties` names the key that would close the ties. With the key, earlier means
    strictly earlier: `prev_ts < ts`.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    keyed = mo.ui.switch(value=True, label="requires unique(sensor, ts)")
    keyed
    return (keyed,)


@app.cell
def _(ibis, keyed, mo, sv, with_neighbours):
    from ibis import _

    ts_readings = ibis.table(
        {"sensor": "string", "ts": "timestamp", "v": "float64"}, name="readings"
    )
    _requires = [_.sensor.notnull(), _.ts.notnull()] + (
        [sv.unique("sensor", "ts")] if keyed.value else []
    )
    _report = sv.verify(
        with_neighbours(ts_readings),
        requires={"readings": _requires},
        ensures=[_.prev_ts.isnull() | (_.prev_ts < _.ts), _.rn >= 0],
    )
    mo.vstack([mo.md(f"`report.deterministic` is {_report.deterministic}"), _report])
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Theorem `window_tiebreak` (`analysis/Sverify/Analysis/Keys.lean`) makes the keyed
    case trustworthy: when a window's partition and sort columns contain a
    key of its input, every way of sorting the input by the window's keys
    gives the same rows. The proof therefore describes what the engine
    computes, however it breaks ties.

    A run can ask for more: `report.run(con, engine,
    reproducible=sv.equivalent())` refuses a plan whose result a rerun may
    change, and names the key that would fix it. We'll take the largest
    order, where two orders tie on the amount:
    """)
    return


@app.cell
def _(ibis, sv):
    from sverify.errors import RouteError as _RouteError

    con_ties = sv.connect()
    con_ties.create(
        "orders",
        ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 30), (2, "bob", 30), (3, "cy", 5)],
    )
    _orders = con_ties.table("orders")
    _largest = sv.verify(_orders.order_by(ibis.desc("amount")).limit(1))
    try:
        _largest.run(con_ties, "duckdb", reproducible=sv.equivalent())
    except _RouteError as _e:
        print(f"RouteError: {_e}")
    return (con_ties,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The fix is the one the refusal names: a key in the order. With `id` as
    the tiebreak and `sv.key("id")` in `requires`, the result is
    determined, and the run goes ahead:
    """)
    return


@app.cell
def _(con_ties, ibis, sv):
    _orders = con_ties.table("orders")
    _largest = sv.verify(
        _orders.order_by([ibis.desc("amount"), "id"]).limit(1),
        requires={"orders": [sv.key("id")]},
    )
    assert _largest.deterministic
    _largest.run(con_ties, "duckdb", reproducible=sv.equivalent()).to_pylist()
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### ASOF joins

    An accelerometer samples at 100 Hz and a gyroscope at 130 Hz, so their
    timestamps rarely line up. To train a model on both, each accelerometer
    sample needs the latest gyroscope sample at or before it, and only if
    that one is recent enough. This is an ASOF join. Not every engine has one
    (DataFusion has none), and Ibis's `asof_join` compiles to DuckDB syntax, so `sv.asof_join` builds it
    from parts Lean understands: a range join, then `ROW_NUMBER` to keep the
    latest match.

    A gyroscope reading from the future would leak information the model
    cannot have in production. The contract states what an ASOF join
    promises: one output row per accelerometer sample, no gyroscope sample
    from the future, and none older than the tolerance.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    tolerance_ms = mo.ui.slider(1, 20, value=10, label="tolerance (ms)", show_value=True)
    how = mo.ui.radio(["left", "inner"], value="left", label="how", inline=True)
    gyr_keyed = mo.ui.switch(value=True, label="requires gyr: unique(device, ts)")
    mo.hstack([tolerance_ms, how, gyr_keyed], justify="start", gap=2)
    return gyr_keyed, how, tolerance_ms


@app.cell
def _(con_w, dt, gyr_keyed, how, ibis, sv, tolerance_ms):
    from ibis import _

    _t0 = dt.datetime(2024, 5, 1, 7, 0)
    _acc = [(1, _t0 + dt.timedelta(microseconds=10_000 * i), float(i)) for i in range(100)]
    _gyr = [
        (1, _t0 + dt.timedelta(microseconds=round(1e6 * i / 130)), float(i)) for i in range(130)
    ]
    con_w.create("acc", ibis.schema({"device": "int64", "ts": "timestamp", "a": "float64"}), _acc)
    con_w.create("gyr", ibis.schema({"device": "int64", "ts": "timestamp", "g": "float64"}), _gyr)

    tol = ibis.interval(milliseconds=tolerance_ms.value)

    @sv.transform(
        requires={
            "acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
            "gyr": [sv.unique("device", "ts")] if gyr_keyed.value else [],
        },
        ensures=[
            sv.unique("device", "ts"),  # one row per accelerometer sample
            _.ts_right.isnull() | (_.ts_right <= _.ts),  # never from the future
            # never too old (a condition can be SQL, too)
            f"ts_right IS NULL OR ts_right >= ts - INTERVAL '{tolerance_ms.value} milliseconds'",
        ],
        on_unproved="warn",
    )
    def aligned(acc, gyr):
        return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=tol, how=how.value)

    aligned(con_w.table("acc"), con_w.table("gyr")).order_by("ts").to_pyarrow()
    aligned.report
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Two things to try.

    * Lower the tolerance below 8 ms. The gyroscope samples every 7.7 ms, so
      some accelerometer samples find no partner. With `how="left"` they stay
      with NULLs, with `"inner"` they disappear, and the proofs hold either
      way.
    * Drop the key on `gyr`. Two gyroscope readings at the same instant tie
      for "latest". The guarantees hold for either one, and the result is
      not deterministic: a rerun may pair the sample with the other reading.

    One row per sample comes from the key analysis: `ROW_NUMBER()` over a
    partition is a key together with the partition columns, and the filter
    `rank = 0` drops the rank from that key. Framed window aggregates
    (`AVG(v) OVER (ROWS 5 PRECEDING)`), `RANK` and running sums verify too
    ([Ibis coverage](https://github.com/AlexanderNenninger/substrait-lean/blob/main/README.md#ibis-coverage)).

    ## Composing contracts

    Say the billing team owns a step that cleans up `orders`, and you own the
    step after it, which doubles the amounts for a promotion. You have never
    read their code and you should not have to. If a negative amount slips
    past them, your step doubles it and your name is on the incident.

    What you rely on is their contract. When the input of a contracted
    function is the result of another contracted function, sverify proves the
    downstream preconditions from the upstream contract, so the intermediate
    data is never checked. It also proves the downstream postconditions from
    what the upstream step guarantees, whatever its code happens to do.
    """)
    return


@app.cell
def _(ibis, sv):
    from ibis import _

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        """Orders with a known amount."""
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled_paid(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    _orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    doubled_paid(paid(_orders))
    doubled_paid.report
    return doubled_paid, paid


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The `requires paid: …` rows show what `doubled_paid` was allowed to
    assume: the guarantees of `paid`. Each link is a Hoare triple, the
    notation of program verification: `{P} f {Q}` means that if `P` holds
    before `f`, then `Q` holds after. The rule

    > `{P} g {Q}` and `{Q} f {S}` give `{P} f ∘ g {S}`

    is theorem `Triple.compose` in `SubstraitLean/Compose.lean`.

    ### When the link breaks

    We'll swap the upstream step for one that promises less. Pick what feeds
    `doubled_paid`.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    upstream = mo.ui.radio(
        {
            "paid (guarantees amount ≥ 0 and not NULL)": "paid",
            "not_null (guarantees only that amount is not NULL)": "not_null",
            "a plain Ibis filter: amount > 0": "plain",
            "a plain Ibis filter: amount IS NOT NULL": "plain_notnull",
        },
        value="not_null (guarantees only that amount is not NULL)",
        label="upstream step",
    )
    upstream
    return (upstream,)


@app.cell
def _(CompositionError, VerificationError, doubled_paid, ibis, mo, paid, sv, upstream):
    from ibis import _

    _orders = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")

    @sv.transform(ensures=[_.amount.notnull()])
    def not_null(orders):
        return orders.filter(orders.amount.notnull())

    _inputs = {
        "paid": lambda: paid(_orders),
        "not_null": lambda: not_null(_orders),
        "plain": lambda: _orders.filter(_orders.amount > 0),
        "plain_notnull": lambda: _orders.filter(_orders.amount.notnull()),
    }
    try:
        doubled_paid(_inputs[upstream.value]())
        _out = mo.vstack(
            [mo.callout(mo.md("Every link holds ✓"), kind="success"), doubled_paid.report]
        )
    except CompositionError as _e:
        _out = mo.callout(mo.md(f"CompositionError: {str(_e).splitlines()[0]}"), kind="danger")
    except VerificationError as _e:
        _first = (str(_e).splitlines()[1:] or [str(_e)])[0].strip()
        _out = mo.callout(mo.md(f"VerificationError: {_first}"), kind="danger")
    _out
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    * `not_null` guarantees too little: `doubled_paid` needs `amount ≥ 0` and
      nothing upstream promises it. The error names both sides of the broken
      link. Only the contract counts, even though `not_null`'s code would
      happen to keep negative amounts.
    * A plain Ibis step carries no contract, and what follows from its
      operations is still proved: `amount > 0` implies both preconditions of
      `doubled_paid`. With only `amount IS NOT NULL`, the missing
      `amount ≥ 0` is treated like a precondition on a base table: checked on
      the data if there is data, assumed otherwise.
    * A precondition can follow from more than the upstream `ensures`. It is
      then proved as an extra postcondition of the upstream function, from
      that function's own preconditions. Keys (`sv.unique`) propagate the same
      way.

    On bound tables only the base tables are checked: `paid`'s preconditions
    on `orders`. The intermediate result is never inspected, because
    `doubled_paid`'s preconditions were proved.

    ### Handing the contract to another team

    The billing team may run its steps on an engine sverify doesn't drive.
    `to_substrait()` writes the proved plan as Substrait, which any
    conforming consumer runs, with the contract inside it: the
    preconditions the consumer must meet, the postconditions it may rely
    on, and a manifest of how the proof reaches Substrait. We'll export
    `paid` and read it back, which proves its contract again:
    """)
    return


@app.cell
def _(paid, sv):
    exported = paid.to_substrait()
    _manifest = paid.report.substrait_contract()["manifest"]
    _back = sv.Report.from_substrait(exported)
    assert _back.proved
    {
        "class": _manifest["class"],
        "evidence": _manifest["evidence"],
        "proved again": [c.label for c in _back.ensures],
    }
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The class `exact` says a consumer that follows Substrait's spec gives
    the reference's rows. Where the spec leaves a choice open that the proof
    needs, the export says so and refuses: Substrait doesn't say how
    `upper` treats non-ASCII text (ST-10 on the
    [upstream ledger](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html)),
    and the refusal names the way out:
    """)
    return


@app.cell
def _(ibis, sv):
    @sv.transform()
    def shouty(orders):
        return orders.select(orders.id, name=orders.customer.upper())

    shouty(ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders"))
    try:
        shouty.to_substrait()
    except sv.errors.ExportError as _e:
        print(f"ExportError: {_e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    A team that keeps its contracts in a data catalog rather than beside the
    plan reads them as ODCS, the Open Data Contract Standard. `sverify.odcs`
    writes a node's contract as an ODCS document, with the proved
    guarantees as its schema and quality rules, and reads one back as
    conditions for the next team's `requires`. We'll run `paid` over a
    small source, export the node's contract, and read it back:
    """)
    return


@app.cell
def _(paid):
    import pyarrow as _pa
    from sverify import odcs
    from sverify.io import StaticSource as _StaticSource

    _source = _StaticSource(
        _pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, None]}),
        name="orders",
    )
    paid_odcs = odcs.export(_source.pipe(paid), descriptions={"amount": "in cents"})
    odcs.read(paid_odcs).conditions()
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    You can now put a contract on a transformation and read what Lean proved
    about every column. You can prove keys and relations between columns,
    rule out the runtime errors that page people at night, pin down windows
    and ASOF joins, and chain steps from different teams with every link
    proved. The billing job gets a column whose promises were proved before
    any data ran, and the assumptions about upstream data are checked when
    the data arrives.

    Orders keep arriving, though. Next up is
    [Pipelines and engines](?file=05_pipelines_and_engines.py), where a
    contracted result is kept up to date from its changes, stored in Delta
    and Iceberg, and run on other engines.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 3. [An orders mart](?file=03_orders_mart.py) · 5. [Pipelines and engines](?file=05_pipelines_and_engines.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
