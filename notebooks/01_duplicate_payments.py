# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "deltalake",
#     "ibis-framework[duckdb]==12.0.0",
#     "marimo",
#     "pyarrow==26.0.0",
#     "sqlglot",
#     "sverify[datafusion,polars,delta]==0.2.0",
# ]
# ///

import marimo

__generated_with = "0.25.2"
app = marimo.App(width="medium", app_title="1. Duplicate card payments")


@app.cell(hide_code=True)
def _():
    import marimo as mo
    from sverify import display

    return display, mo


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    [Contents](?file=00_start_here.py) · 2. [Sensor alerts](?file=02_sensor_alerts.py) →
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    # 1. Duplicate card payments, from a Delta table

    Say you're on the payments team. A customer was charged twice for the
    same coffee, and by the time support hears about it, they've already
    tweeted. You want to catch these **double charges**, the same card
    paying the same amount at the same merchant twice within five minutes,
    and refund them first.

    The rule comes from the [query catalogue](https://github.com/AlexanderNenninger/substrait-lean/blob/v0.2.0/catalogue/INDEX.md)
    (`fin-duplicate-payments`); stream processors write it as an interval
    join, and here it is a self-join on a Delta Lake table of card
    transactions. The refund queue trusts what you hand it, so it has to be
    right: no pair twice, no charge matched with itself, and nothing left
    over when a charge is reversed.

    We'll go through the whole job:

    1. read the transactions from a Delta table, with its Change Data Feed;
    2. write the rule in Ibis and state its **contract**: what it assumes
       about the input, and what the refund queue may rely on;
    3. have the contract **proved** before any data runs;
    4. run the same checked plan on DuckDB, Polars and DataFusion, and write
       it as Snowflake and Spark SQL;
    5. **maintain the result from the change feed** when new transactions
       arrive and old ones are reversed, and see what the usual "process
       the new rows" job gets wrong;
    6. write it to a Delta table that carries the contract, so the next job
       can build on it.
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 1. The source: a Delta table of transactions

    Amounts are integer cents: money as DOUBLE does not compare exactly, and
    an equality of amounts is the whole rule. The table has the Change Data
    Feed on (so later runs can read what changed) and a CHECK constraint
    that amounts are not negative. The data has one real double charge, a
    near miss on card 11 half an hour apart, and card 12, whose two payments
    arrived without a merchant at all.
    """)
    return


@app.cell
def _():
    import datetime as dt
    import tempfile
    from pathlib import Path

    import ibis
    import pyarrow as pa
    import sverify as sv
    from deltalake import DeltaTable, write_deltalake
    from sverify.engines import DUCKDB, ENGINES, SNOWFLAKE, SPARK, to_sql
    from sverify.io import DeltaSink, DeltaSource

    lake = Path(tempfile.mkdtemp())  # a local "lake"; any Delta URI works, with storage_options

    TXN_SCHEMA = pa.schema(
        [
            pa.field("txn_id", pa.int64(), nullable=False),
            pa.field("card_id", pa.int64(), nullable=False),
            pa.field("merchant", pa.string()),
            pa.field("amount_cents", pa.int64(), nullable=False),
            pa.field("ts", pa.timestamp("us"), nullable=False),
        ]
    )

    def at(h, m):
        return dt.datetime(2026, 3, 2, h, m)

    def txns(*rows):
        return pa.Table.from_pylist(
            [dict(zip(TXN_SCHEMA.names, r, strict=True)) for r in rows], schema=TXN_SCHEMA
        )

    first_load = txns(
        (1, 10, "coffee", 450, at(8, 0)),
        (2, 10, "coffee", 450, at(8, 2)),  # charged twice, two minutes apart
        (3, 11, "books", 2599, at(9, 0)),
        (4, 11, "books", 2599, at(9, 30)),  # same amount, but half an hour later
        (5, 12, None, 999, at(10, 0)),
        (6, 12, None, 999, at(10, 1)),  # no merchant: not a duplicate
    )
    write_deltalake(
        lake / "transactions",
        first_load,
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    DeltaTable(lake / "transactions").alter.add_constraint({"non_negative": "amount_cents >= 0"})
    return (
        DUCKDB,
        DeltaSink,
        DeltaSource,
        DeltaTable,
        ENGINES,
        SNOWFLAKE,
        SPARK,
        at,
        dt,
        first_load,
        ibis,
        lake,
        sv,
        to_sql,
        txns,
        write_deltalake,
    )


@app.cell(hide_code=True)
def _(display, first_load):
    display.arrow(first_load, title="transactions (Delta, version 0 + constraint = v1)")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 2. The rule and its contract

    We'll write the rule in Ibis, state what it assumes and what it
    promises, and have the checker prove it before any data runs. The rule
    is plain Ibis; the decorator writes down what everyone involved is
    counting on:

    * **`requires`**: what the job assumes about its input. Transaction ids
      are unique, amounts are not negative, and timestamps are before 2100
      (so adding five minutes can't overflow).
    * **`ensures`**: what the refund queue relies on. One row per pair,
      the first transaction before its duplicate, a merchant on every row, a
      non-negative amount, and the duplicate no earlier than the first.

    The checks in `ensures` are the ones you would otherwise write as dbt
    tests (`unique`, `not_null`, `accepted_range`, an expression test) and
    run on yesterday's data, hoping yesterday contained the bad case. Here
    they are proved for **every** input that meets `requires`, before the
    job runs.
    """)
    return


@app.cell
def _(dt, ibis, sv):
    from ibis import _

    def find_duplicates(transactions):
        a, b = transactions, transactions.view()
        return a.join(
            b,
            (a.card_id == b.card_id)
            & (a.merchant == b.merchant)
            & (a.amount_cents == b.amount_cents)
            & (a.txn_id < b.txn_id)
            & (b.ts >= a.ts)
            & (b.ts <= a.ts + ibis.interval(minutes=5)),
        ).select(
            first_txn=a.txn_id,
            duplicate_txn=b.txn_id,
            card_id=a.card_id,
            merchant=a.merchant,
            amount_cents=a.amount_cents,
            first_ts=a.ts,
            duplicate_ts=b.ts,
        )

    REQUIRES = {
        "transactions": [
            sv.unique("txn_id"),
            _.amount_cents >= 0,
            _.ts < dt.datetime(2100, 1, 1),
        ]
    }
    ENSURES = [
        sv.unique("first_txn", "duplicate_txn"),
        _.first_txn < _.duplicate_txn,
        _.merchant.notnull(),
        _.amount_cents >= 0,
        _.first_ts <= _.duplicate_ts,
    ]

    @sv.transform(requires=REQUIRES, ensures=ENSURES)
    def duplicate_payments(transactions):
        return find_duplicates(transactions)

    return ENSURES, REQUIRES, duplicate_payments, find_duplicates


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Now we build it. The Delta table is a source, and calling the rule on
    it builds a node. Building the node proves the contract (a
    `VerificationError` would stop here), and its first refresh loads the
    current snapshot:
    """)
    return


@app.cell
def _(DeltaSource, duplicate_payments, lake):
    transactions = DeltaSource(str(lake / "transactions"))
    dups = duplicate_payments(transactions)
    report = duplicate_payments.last_report
    assert report.proved and not report.issues
    first_refresh = dups.refresh()
    return dups, first_refresh, report, transactions


@app.cell(hide_code=True)
def _(mo, report):
    mo.md(report._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Every postcondition is ✅ proved, and no runtime error is possible. How
    each one follows:

    * **`unique(first_txn, duplicate_txn)`**: `txn_id` is a key of the
      input, so a pair of ids identifies a pair of rows.
    * **`merchant` is never NULL**, although the column is nullable: rows
      only join when `a.merchant = b.merchant` is TRUE, and `NULL = NULL` is
      not. Card 12's payments never match. (pandas' `merge` *does* match
      NaN with NaN, and a Polars join does with `nulls_equal=True`: a port
      of this rule to a dataframe library can change its result.)
    * **`first_ts <= duplicate_ts`** comes from the join condition, which
      holds on every output row.

    Each precondition was established without trusting anyone's word for
    it, and the first refresh says how:
    """)
    return


@app.cell
def _(dups, first_refresh):
    [str(p) for p in first_refresh[dups.name].preconditions]
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The amount bound comes from the table's **Delta CHECK constraint**, the
    timestamp bound from the **file statistics** (the maximum `ts` of each
    file), and the key is checked on the data, since Delta doesn't enforce
    keys. A later batch only checks the files it added.

    The node holds the one double charge in the data, and neither the near
    miss nor card 12's merchant-less pair:
    """)
    return


@app.cell(hide_code=True)
def _(display, dups):
    display.arrow(dups.to_arrow(), title="duplicate_payments")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### Break the rule

    The easiest bug in a self-join is forgetting that a row matches itself,
    and the customer would find out first: every payment refunded as its own
    duplicate. Switch off `a.txn_id < b.txn_id` (or loosen it to `<=`) and
    the contract is re-checked:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    order = mo.ui.radio(
        {"a.txn_id < b.txn_id": "<", "a.txn_id <= b.txn_id": "<=", "no condition": "none"},
        value="a.txn_id < b.txn_id",
        label="pair condition",
        inline=True,
    )
    order
    return (order,)


@app.cell(hide_code=True)
def _(ENSURES, REQUIRES, ibis, mo, order, sv):
    _t = ibis.table(
        {
            "txn_id": "!int64",
            "card_id": "!int64",
            "merchant": "string",
            "amount_cents": "!int64",
            "ts": "!timestamp",
        },
        name="transactions",
    )
    _a, _b = _t, _t.view()
    _pair = {
        "<": _a.txn_id < _b.txn_id,
        "<=": _a.txn_id <= _b.txn_id,
        "none": ibis.literal(True),
    }[order.value]
    _expr = _a.join(
        _b,
        (_a.card_id == _b.card_id)
        & (_a.merchant == _b.merchant)
        & (_a.amount_cents == _b.amount_cents)
        & _pair
        & (_b.ts >= _a.ts)
        & (_b.ts <= _a.ts + ibis.interval(minutes=5)),
    ).select(
        first_txn=_a.txn_id,
        duplicate_txn=_b.txn_id,
        card_id=_a.card_id,
        merchant=_a.merchant,
        amount_cents=_a.amount_cents,
        first_ts=_a.ts,
        duplicate_ts=_b.ts,
    )
    mo.md(sv.verify(_expr, requires=REQUIRES, ensures=ENSURES)._repr_markdown_())
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    With `<=`, every transaction is its own duplicate, and
    `first_txn < duplicate_txn` is refused: the checker can't prove it,
    because it is false. With no condition at all, each pair also appears
    in both orders, and each double charge would be refunded twice. In
    neither case did anything have to run, and no test data had to contain
    the bad case.

    ## 3. One plan, every engine

    Maybe you develop on DuckDB on a laptop and the job runs somewhere else
    in production. The node's plan is the one Lean checked. sverify runs it
    on each engine through its own translation, which keeps Lean's
    semantics (NULL keys never match, integers don't wrap around, ties
    break one way) or refuses the plan. So a node refreshed with
    `engine=` has the same rows everywhere:
    """)
    return


@app.cell
def _(ENGINES, duplicate_payments, dups, transactions):
    on_each = {}
    for _engine in ENGINES:
        _node = duplicate_payments(transactions)
        _node.refresh(engine=_engine)
        on_each[_engine] = _node.to_arrow().to_pylist()
    assert all(rows == dups.to_arrow().to_pylist() for rows in on_each.values())
    {e: len(rows) for e, rows in on_each.items()}
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    For a warehouse, sverify writes the plan as SQL. The SQL is long because
    it spells out every choice an engine would otherwise make for you:
    """)
    return


@app.cell(hide_code=True)
def _(mo):
    dialect = mo.ui.radio(["snowflake", "spark", "duckdb"], value="snowflake", inline=True)
    dialect
    return (dialect,)


@app.cell(hide_code=True)
def _(DUCKDB, SNOWFLAKE, SPARK, dialect, dups, mo, to_sql):
    import json

    import sqlglot

    _sql = to_sql(
        json.loads(dups.plan),
        {"snowflake": SNOWFLAKE, "spark": SPARK, "duckdb": DUCKDB}[dialect.value],
    )
    mo.md(f"```sql\n{sqlglot.transpile(_sql, read=dialect.value, pretty=True)[0]}\n```")
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## 4. New transactions: keeping the result up to date

    An hour later, two things have happened to the source table:

    * transaction 7 arrived late: card 11 paid 25.99 for books at 09:03, a
      duplicate of transaction **3**, which was loaded in the first run;
    * transaction 2 was **reversed** and deleted, so the coffee pair is no
      longer a double charge.
    """)
    return


@app.cell
def _(DeltaTable, at, lake, txns, write_deltalake):
    _dt = DeltaTable(lake / "transactions")
    late = txns((7, 11, "books", 2599, at(9, 3)))
    write_deltalake(_dt, late, mode="append")
    _dt.delete("txn_id = 2")
    return (late,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ### The usual incremental job

    The common way to avoid recomputing the self-join is a watermark: find
    the duplicates among the rows that arrived since the last run, and
    append them to the output. It runs fast, and it is wrong twice, once
    for each of the two changes:
    """)
    return


@app.cell
def _(find_duplicates, ibis, late):
    naive_new = find_duplicates(ibis.memtable(late)).to_pyarrow().to_pylist()
    naive = [(1, 2)] + [(r["first_txn"], r["duplicate_txn"]) for r in naive_new]
    naive  # last run's (1, 2) plus whatever the new rows contain
    return (naive,)


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    It **misses (3, 7)**, because transaction 3 is not among the new rows,
    and it **keeps (1, 2)**, because an append-only job never sees the
    reversal, so that customer gets a refund for a charge that no longer
    exists. Fixing that by hand means joining the new rows with the old
    ones both ways, and handling deletes and updates: that is the delta rule
    of a join, `Δ(A ⋈ B) = ΔA ⋈ (B + ΔB) + A ⋈ ΔB`, and it is easy to get
    subtly wrong.

    ### The node's refresh

    `dups.refresh()` reads the Change Data Feed from the version the node
    was computed at, checks the preconditions on the new rows only, and
    runs the delta plans Lean derived and **proved** to give the same result
    as a full recompute:
    """)
    return


@app.cell
def _(DeltaSource, duplicate_payments, dups, lake):
    _refresh = dups.refresh()
    _from_scratch = duplicate_payments(DeltaSource(str(lake / "transactions")))
    _from_scratch.refresh()
    assert dups.to_arrow().to_pylist() == _from_scratch.to_arrow().to_pylist()
    print(_refresh)
    return


@app.cell(hide_code=True)
def _(display, dups, mo, naive):
    _pairs = [(r["first_txn"], r["duplicate_txn"]) for r in dups.to_arrow().to_pylist()]
    assert _pairs == [(3, 7)] and sorted(naive) != _pairs
    mo.vstack(
        [
            display.arrow(dups.to_arrow(), title="duplicate_payments after the refresh"),
            mo.md(
                "The late duplicate is found and the reversed pair is gone, and the node "
                "holds the same rows as a new one computed from scratch."
            ),
        ]
    )
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    The report names the one thing the proof takes on trust: that the
    change feed really turns the old snapshot into the new one ("Δ trusted
    as coming from Delta CDF"). Where the feed is gone (CDF off, files
    vacuumed), the refresh diffs the two snapshots instead, and says so.
    `dups.refresh(audit=True)` also compares every batch with a recompute
    before it is applied.

    ## 5. The sink carries the contract

    `dups.write(DeltaSink(...))` stores the node in a Delta table, and every
    refresh writes it **exactly once per state**: the commit is keyed by the
    source versions, so a retried job can't write a batch twice. The first
    write creates the table; the proved guarantees become NOT NULL columns
    and CHECK constraints, and the commit metadata records the plan and the
    contract. Later writes MERGE only the change.
    """)
    return


@app.cell
def _(DeltaSink, dups, lake):
    stored = dups.write(DeltaSink(str(lake / "duplicate_payments")))
    print(stored.refresh())
    print(stored.refresh())  # the same state again: already committed, nothing written
    return


@app.cell
def _(DeltaSource, lake):
    contract = DeltaSource(str(lake / "duplicate_payments")).contract()
    contract
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    Now the refund queue's own job reads that table. Whoever maintains it
    doesn't have to trust your word, or re-check your data: its
    preconditions are discharged from the table's schema and constraints,
    which the contract put there:
    """)
    return


@app.cell
def _(DeltaSource, lake, sv):
    from ibis import _

    @sv.transform(
        requires={"dups": [_.amount_cents >= 0, _.merchant.notnull()]},
        ensures=[_.refund_cents >= 0, _.merchant.notnull()],
    )
    def refunds(dups):
        return dups.select(dups.duplicate_txn, dups.merchant, refund_cents=dups.amount_cents)

    refund_queue = refunds(DeltaSource(str(lake / "duplicate_payments"), name="dups"))
    [str(p) for p in refund_queue.refresh()[refund_queue.name].preconditions]
    return


@app.cell(hide_code=True)
def _(mo):
    mo.md(r"""
    ## What you got

    You now have a refund queue you can trust. Its assumptions were proved
    before a single row ran, and a bug that would have broken one was caught
    at definition time, not by a customer. The preconditions came from
    Delta's own constraints and file statistics where it has them, and from
    the data where it doesn't. The same plan gives the same rows on DuckDB,
    Polars and DataFusion and is written as Snowflake or Spark SQL. It stays
    right as charges arrive and get reversed, where the watermark job got
    two rows wrong, and the next job can build on its table without checking
    again.

    **Next up:** [Sensor alerts from an Iceberg table](?file=02_sensor_alerts.py),
    where ties and NaN get involved. The features used here are explained
    in [Contracts](?file=04_contracts.py),
    [Incremental views](?file=09_incremental_views.py),
    [Pipelines](?file=10_pipelines.py) and [Engines and SQL](?file=11_engines.py).
    """)
    return


if __name__ == "__main__":
    app.run()
