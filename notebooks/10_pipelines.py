# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "ibis-framework==12.0.0",
#     "marimo",
#     "pyarrow==26.0.0",
#     "sverify[delta]==0.3.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="10. Pipelines")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 9. [Incremental views](?file=09_incremental_views.py) · [Contents](?file=00_start_here.py) · 11. [Engines and SQL](?file=11_engines.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 10. Pipelines

    Say you own the Monday report the sales team presents. It reads orders
    by city, which read the cleaned orders, which read the raw `orders`
    feed, and a bad row anywhere below ends up on their slides.

    Real pipelines are layered like that: cleaned tables feed joined tables
    feed reports. In `sverify` the layers are transforms composed directly,
    each piped from the one below, so the code reads in the order the data
    flows: `orders.pipe(paid).pipe(doubled)` is the same node as the call
    form `doubled(paid(orders))`. The other inputs of a layer come by
    keyword, as `base.pipe(cities, customers=customers)`. Without a `.write` in between they
    **fuse** into one plan, maintained as one incremental view (chapter 9).
    `.write(sink)` **stores** a layer, as a cache in the middle of a job or
    as its output; the layers above read the stored table as a versioned
    source, through its change feed. So an intermediate result is computed
    once and shared, and only changes flow through the layers.

    This chapter brings chapters 8 and 9 together: the base layer is the
    contracted `orders.pipe(paid).pipe(doubled)`, and its guarantees keep holding in
    **every** state of the pipeline, not only the first.

    ## Three layers
    """)
    return


@app.cell
def _():
    import tempfile
    from pathlib import Path

    import pyarrow as pa
    import sverify as sv
    from ibis import _
    from sverify.io import DeltaSink, StaticSource

    lake = Path(tempfile.mkdtemp())  # a local "lake"; any Delta URI works, with storage_options

    @sv.transform(
        requires={"orders": [_.amount >= 0, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    @sv.transform(requires={"base": [_.doubled.notnull()]}, ensures=[_.doubled.notnull()])
    def cities(base, customers):
        return base.join(customers, base.customer == customers.name).select("id", "city", "doubled")

    @sv.transform()
    def located(base, customers):
        return base.left_join(customers, base.customer == customers.name).select("id", "city")

    def arrow_table(schema, rows):
        return pa.Table.from_pylist([dict(zip(schema.names, r)) for r in rows], schema=schema)

    orders = StaticSource(
        arrow_table(
            pa.schema({"id": pa.int64(), "customer": pa.string(), "amount": pa.int64()}),
            [(1, "ada", 30), (2, "bob", 5), (3, "cy", 0)],
        ),
        name="orders",
    )
    customers = StaticSource(
        arrow_table(
            pa.schema({"name": pa.string(), "city": pa.string()}),
            [("ada", "Paris"), ("cy", "Lima")],
        ),
        name="customers",
    )

    base = orders.pipe(paid).pipe(doubled).write(DeltaSink(str(lake / "base")))
    by_city = base.pipe(cities, customers=customers)
    by_location = base.pipe(located, customers=customers)
    monday = sv.group(by_city, by_location)
    print(monday.refresh())
    return base, by_city, by_location, cities, customers, lake, monday, orders, pa, sv


@app.cell(hide_code=True)
def _(mo):
    mo.mermaid(
        """
        graph BT
          O["orders"] --> B["base (Delta table)<br/>orders.pipe(paid).pipe(doubled), one fused plan"]
          B --> C["cities<br/>inner join customers"]
          B --> L["located<br/>left join customers<br/>(recomputed)"]
          K["customers"] --> C
          K --> L
          style B fill:#d4f4dd,stroke:#2e8b57
        """
    )
    return


@app.cell(hide_code=True)
def _(base, mo, monday):
    mo.md(
        "* `paid` and `doubled` have no `.write` between them, so they fuse into "
        "one plan; `.write(DeltaSink(...))` stores the result as `base`. `cities` and "
        "`located` read `base`'s Delta table, not `orders`.\n"
        "* A contracted transform piped from a stored node builds on what that node's "
        "plan proved, as in a direct composition: `cities` requires "
        "`_.doubled.notnull()` of `base`, which `doubled` guarantees, so it is "
        "checked once, when the node is built, and never on the data. A precondition "
        "`base` doesn't guarantee raises `CompositionError` right there.\n"
        "* `sv.group(by_city, by_location)` refreshes both reports against the same source versions; "
        "`base` is refreshed and written once for the two of them, upstream first. "
        "Its first refresh checked `paid`'s preconditions on all of `orders` "
        "(the `requires … (checked on data)` lines above).\n"
        "* `located` is a left join, so it is **recomputed and diffed** on each "
        "refresh (chapter 9). Its change would still flow to any node reading it. "
        f"`status()` says so:\n\n```text\n{monday.status()}\n{base.status()}\n```"
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Changes, layer by layer

    We'll feed the pipeline. Each button changes `orders` and `customers`
    and refreshes both reports. The first is valid; the other two each
    insert an order that breaks a precondition of `paid`. We refresh with
    `audit=True`, so every batch is also compared with recomputation
    before it is applied (`AuditError` otherwise).
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    good = mo.ui.button(
        value=0, on_click=lambda n: n + 1, label="New orders and a new customer", kind="success"
    )
    dup = mo.ui.button(
        value=0,
        on_click=lambda n: n + 1,
        label="Insert an order with an existing id",
        kind="danger",
    )
    neg = mo.ui.button(
        value=0,
        on_click=lambda n: n + 1,
        label="Insert an order with a negative amount",
        kind="danger",
    )
    mo.hstack([good, dup, neg], justify="start")
    return dup, good, neg


@app.cell(hide_code=True)
def _():
    # Button presses applied so far, and what the last one did.
    presses = {"good": 0, "dup": 0, "neg": 0, "last": None}
    return (presses,)


@app.cell(hide_code=True)
def _(customers, dup, good, monday, neg, orders, presses, sv):
    from sverify.errors import PreconditionError

    _cities = ["Oslo", "Rome", "Lima", "Paris"]

    def _try(kind, changes):
        orders.apply(changes["orders"])
        if "customers" in changes:
            customers.apply(changes["customers"])
        try:
            presses["last"] = (kind, str(monday.refresh(audit=True)))
        except PreconditionError as e:
            presses["last"] = (kind, e)
            # The demo takes the bad order out of the feed again, so the
            # next batch can go through.
            orders.apply(sv.Changes(deletes=changes["orders"].inserts))

    while presses["good"] < good.value:
        _i = presses["good"]
        _try(
            "good",
            {
                "orders": sv.Changes(inserts=[(10 + _i, "bob", 3 * _i), (20 + _i, f"new{_i}", 7)]),
                "customers": sv.Changes(inserts=[(f"new{_i}", _cities[_i % 4])]),
            },
        )
        presses["good"] += 1
    while presses["dup"] < dup.value:
        _try("dup", {"orders": sv.Changes(inserts=[(1, "dee", 4)])})
        presses["dup"] += 1
    while presses["neg"] < neg.value:
        _try("neg", {"orders": sv.Changes(inserts=[(99, "eve", -5)])})
        presses["neg"] += 1
    state = (presses["good"], presses["dup"], presses["neg"])
    return (state,)


@app.cell(hide_code=True)
def _(base, by_city, by_location, display, mo, presses, state):
    _ = state
    _last = presses["last"]
    if _last is None:
        _msg = mo.md("*Press a button.*")
    elif isinstance(_last[1], str):
        _msg = mo.vstack(
            [
                mo.callout(
                    mo.md("Batch applied to every layer; the audit found no difference."),
                    kind="success",
                ),
                mo.md(f"`refresh(audit=True)` reports:\n\n```text\n{_last[1]}\n```"),
            ]
        )
    else:
        _msg = mo.callout(
            mo.md(
                f"**PreconditionError**: {_last[1]}. The refresh was refused; no layer "
                "changed and nothing was written."
            ),
            kind="danger",
        )

    def _rows(node):
        return sorted((tuple(r.values()) for r in node.to_arrow().to_pylist()), key=repr)

    mo.vstack(
        [
            _msg,
            display.side_by_side(
                *[
                    display.table(_rows(n), list(n.schema), title=n.name)
                    for n in [base, by_city, by_location]
                ]
            ),
        ],
        gap=1,
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Why the guarantees survive every batch

    Whoever reads `base` relies on its guarantees on the hundredth batch as
    much as on the first. `paid`'s preconditions were checked on all of
    `orders` once, on the first refresh. After that, only **the batch** is
    checked:

    * row conditions (`amount >= 0`) on the inserted rows;
    * keys (`unique(id)`) among the inserted rows and against the keys of
      the rows the batch keeps.

    That is enough, by theorem `Spec.update` in `SubstraitLean/Compose.lean`:
    a table's contract survives a batch if the inserted rows satisfy the row
    conditions and their keys clash with neither each other nor the kept
    rows. `Triple.maintained` then says a contracted view's guarantees hold
    in the new state. So `base` satisfies `doubled ≥ 0` and is non-NULL
    after every batch, without ever re-checking the whole table, and the
    Delta table it is written to records those guarantees with every
    version, for the layers that read it.

    The layering itself is `Rel.chain_sound` (DBSP's *chain rule*): when a
    view reads another view's stored result, and gets that view's change as
    its change table (here, through the Delta change feed), its own update
    plan is still correct. For a recomputed view, `ZSet.diff_correct` shows
    `new − old` is a valid change to pass on.

    Each refresh brings the layers up to date upstream first and writes
    every stored node exactly once per state. If the job stops and
    restarts, building the same nodes again is enough: the first refresh
    resumes each stored node from its table when the plan and the source
    versions match, rather than computing it again.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## Your own source and sink

    Say the customers don't live in the lake at all. The CRM team gives you
    an API that returns the customers who signed up after a given time, and
    finance wants the city report as a Parquet file on their share, not as
    a Delta table. Neither needs a table format.

    A source you write is one method, `read(since)`: it returns the rows
    that are new since the last read and a cursor to start from next time,
    as a `Batch`. A sink you write is one method too, `write(change)`: it
    stores what a refresh hands it. sverify does the rest: it numbers the
    reads as versions, works out what changed, checks the preconditions,
    and decides when a state needs writing at all.

    We'll read the CRM with `from_query`, which builds a source from a
    function and the column to keep a high-water mark on, and write the
    report with a sink of our own that keeps the contract next to the file,
    so a restarted job knows what it already wrote.
    """)
    return


@app.cell
def _(base, cities, lake, pa, sv):
    import pyarrow.parquet as pq
    from sverify.io import Contract, Sink, from_query

    crm_signups = [
        {"name": "ada", "city": "Paris", "signed_up": 1},
        {"name": "cy", "city": "Lima", "signed_up": 2},
    ]

    def signed_up_after(since):
        """The CRM's API: customers who signed up after `since`."""
        return pa.Table.from_pylist(
            [c for c in crm_signups if since is None or c["signed_up"] > since]
        )

    class ParquetFile(Sink):
        """The report as a Parquet file, with its contract next to it."""

        def __init__(self, path):
            super().__init__(path.stem, location=str(path))
            self.path, self.record = path, path.with_suffix(".contract.json")

        def committed(self):
            if not self.record.exists():
                return None
            return Contract.from_json(self.record.read_text())

        def write(self, change):
            pq.write_table(change.table, self.path)
            self.record.write_text(change.contract.to_json())

    crm = from_query(signed_up_after, cursor_on="signed_up", name="crm")
    report = base.pipe(cities, customers=crm).write(ParquetFile(lake / "city_report.parquet"))
    print(report.refresh())

    crm_signups.append({"name": "bob", "city": "Oslo", "signed_up": 3})
    print(report.refresh())
    return crm_signups, report


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The first refresh read the CRM in full as version 1 and wrote the
    file; the second read only bob, as version 2. The report line says
    what that rests on: the rows were *appended*, assuming customers only
    arrive with a greater `signed_up`. That is the watermark job's
    assumption from chapter 1, and it can break: a sign-up the CRM records
    late, with an earlier time, falls below the cursor and is never read.

    We'll record one and refresh with `audit=True`, which reads the source
    again in full, up to the cursor, and compares it with what the batches
    built.
    """)
    return


@app.cell
def _(crm_signups, report):
    from sverify.errors import AuditError

    crm_signups.append({"name": "dee", "city": "Rome", "signed_up": 2})  # late
    print(report.refresh())  # nothing new above the cursor: dee is missed
    try:
        report.refresh(audit=True)
    except AuditError as e:
        print(f"AuditError: {e}")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The plain refresh saw nothing new; the audit caught the row the cursor
    skipped, and applied nothing. A source you write can't promise more than
    its reads do, so be plain about it: give an `assumes=` that says what
    your batches rely on, and audit now and then.

    The rest of the toolkit, in `sverify.io`:

    * `from_frame(fn)` reads the whole table on every refresh and diffs it
      against the last read, so the change is exact and nothing is assumed;
      `from_files(path)` reads the files that are new in a directory.
      Subclass `Source` for anything else; a batch can also be a whole
      table (`kind="snapshot"`) or rows added and removed
      (`kind="changes"`).
    * A sink's `write` gets a `SinkChange`: the rows added and removed
      since its last write, or the whole table on the first, with the
      contract to record. `committed()` reads that contract back, so each
      state is written once even across restarts; leave it out and sverify
      remembers for the life of the process. `sink_from(fn)` hands the
      whole table to a function.
    * These sources have no metadata, so preconditions on them are checked
      on the rows, and they keep the table in memory. A restarted job reads
      them in full again, and numbers its versions above the ones its
      sinks recorded, so nothing is skipped by mistake. A table format with
      statistics and a change feed implements the full `VersionedSource`
      protocol instead, as Delta and Iceberg do.
    * Credentials stay out of your code: `Storage` holds object store
      options, or a function that fetches fresh ones, and is shared by
      every table that needs it.

    You can now stack transforms into layers that pass only their changes
    along, store the ones others read, and rely on every contract's
    guarantees in every state while only the batch is checked, whether the
    data comes from a lake, an API or a folder of files. Next up,
    [Engines and SQL](?file=11_engines.py) runs the same checked plans on
    Polars and DataFusion, and as SQL for Snowflake and Spark.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ← 9. [Incremental views](?file=09_incremental_views.py) · [Contents](?file=00_start_here.py) · 11. [Engines and SQL](?file=11_engines.py) →
    """)
    return


if __name__ == "__main__":
    app.run()
