"""Row caps (#219): `sv.max_rows(n)` in `requires` bounds the rows of every
relation (`Rel.maxRows_sound`, through keyed joins `Rel.capJoins_eval`), so an
integer SUM over few enough bounded values is proved not to overflow
(`Rel.issuesCapped_sound`)."""

import ibis
import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
from _pipelines import discharged, make_orders, orders_table
from sverify.contracts import ON_DATA
from sverify.errors import PreconditionError
from sverify.io import Changes, StaticSource

ORDERS = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
ITEMS = ibis.table({"order_id": "int64", "qty": "int64"}, name="items")

SUM_OVERFLOW = "SUM overflow"


def sum_risks(report: sv.Report) -> list[str]:
    """The SUMs that may overflow: assumed to fit (`Report.assumed`), or errors."""
    return [i.expr for i in [*report.issues, *report.assumed] if i.kind == SUM_OVERFLOW]


def per_customer(orders):
    return orders.group_by("customer").aggregate(total=orders.amount.sum())


def test_a_row_bound_proves_a_sum_fits():
    bounded = [_.amount >= 0, _.amount <= 1_000_000]
    report = sv.verify(per_customer(ORDERS), requires={"orders": bounded})
    assert sum_risks(report)
    report = sv.verify(per_customer(ORDERS), requires={"orders": [*bounded, sv.max_rows(10**12)]})
    # 10¹² rows of at most 10⁶ each: below 2⁶³.
    assert not sum_risks(report)
    assert report.proved
    assert report.rows == 10**12
    assert "requires orders: max_rows(1000000000000)" in str(report)
    assert "  rows: at most 1,000,000,000,000" in str(report)


def test_too_many_rows_leave_the_sum_checked():
    requires = {"orders": [_.amount >= 0, _.amount <= 1_000_000, sv.max_rows(10**13)]}
    report = sv.verify(per_customer(ORDERS), requires=requires)
    assert sum_risks(report)


def test_unbounded_values_leave_the_sum_checked():
    report = sv.verify(per_customer(ORDERS), requires={"orders": [sv.max_rows(10)]})
    assert sum_risks(report)


def test_the_readme_sql_model():
    """The README's `per_customer`, in SQL, with a row bound."""
    query = "SELECT customer, coalesce(sum(amount), 0) AS total FROM orders GROUP BY customer"
    requires: dict[str, list] = {
        "orders": ["amount >= 0", "amount <= 1000000", "amount IS NOT NULL"]
    }
    tables = {"orders": ORDERS.schema()}
    assert sum_risks(sv.verify(query, requires=requires, tables=tables))
    requires["orders"].append(sv.max_rows(10**9))
    report = sv.verify(query, requires=requires, ensures=["total >= 0"], tables=tables)
    assert report.proved and not sum_risks(report)


def test_row_bounds_propagate():
    rows = {"orders": [sv.max_rows(100)]}
    assert sv.verify(ORDERS.filter(_.amount > 0), requires=rows).rows == 100
    assert sv.verify(ORDERS.limit(3), requires=rows).rows == 3
    assert sv.verify(ORDERS.union(ORDERS), requires=rows).rows == 200
    assert sv.verify(ORDERS.distinct(), requires=rows).rows == 100
    assert sv.verify(ORDERS.aggregate(n=ORDERS.count()), requires=rows).rows == 1
    assert sv.verify(per_customer(ORDERS), requires=rows).rows == 100
    rows["items"] = [sv.max_rows(7)]
    assert sv.verify(ORDERS.cross_join(ITEMS), requires=rows).rows == 700
    # Without a row bound on every input, nothing bounds the rows.
    assert sv.verify(ORDERS.cross_join(ITEMS), requires={"orders": rows["orders"]}).rows is None


def fan_out(orders, items):
    j = items.join(orders, items.order_id == orders.id)
    return j.group_by("customer").aggregate(total=j.amount.sum())


def test_a_join_fans_out_unless_on_a_key():
    """Each item meets every order with its id: up to 1000 · 1000 rows, whose
    sum of amounts up to 10¹³ may overflow. On a key of the orders, each item
    meets one order, and the sum fits."""
    amounts = [_.amount >= 0, _.amount <= 10**13, sv.max_rows(1000)]
    requires: dict[str, list] = {"orders": amounts, "items": [sv.max_rows(1000)]}
    report = sv.verify(fan_out(ORDERS, ITEMS), requires=requires)
    assert sum_risks(report)
    requires["orders"] = [*amounts, sv.unique("id")]
    report = sv.verify(fan_out(ORDERS, ITEMS), requires=requires)
    assert not sum_risks(report)
    keyed = ITEMS.join(ORDERS, ITEMS.order_id == ORDERS.id)
    assert sv.verify(keyed, requires=requires).rows == 1000


def test_ensures_rows_is_proved_from_the_inputs():
    requires = {"orders": [sv.max_rows(50)]}
    report = sv.verify(ORDERS.filter(_.amount > 0), requires=requires, ensures=[sv.max_rows(50)])
    assert report.proved
    report = sv.verify(ORDERS.filter(_.amount > 0), requires=requires, ensures=[sv.max_rows(49)])
    [c] = report.unproved
    assert (c.label, c.value) == ("max_rows(49)", "at most 50 rows")


# -- The catalogue's benchmark queries, at scale -------------------------------


@pytest.fixture(scope="module")
def catalogue():
    cat = pytest.importorskip("sverify_dev.catalogue")
    if not cat.ROOT.is_dir():
        pytest.skip("the catalogue lives in the repository, not in the wheel")
    return cat, {q.id: q for q in cat.load_queries()}, cat.load_schemas()


# Row counts of TPC-H and SSB at scale factor 1000.
SCALE = {
    "ssb-q1.1": {"lineorder": 6_000_000_000, "dwdate": 2556},
    "ssb-q2.1": {
        "lineorder": 6_000_000_000,
        "dwdate": 2556,
        "part": 2_000_000,
        "supplier": 2_000_000,
    },
    "ssb-q3.1": {
        "lineorder": 6_000_000_000,
        "customer": 30_000_000,
        "supplier": 2_000_000,
        "dwdate": 2556,
    },
    "ssb-q4.1": {
        "lineorder": 6_000_000_000,
        "dwdate": 2556,
        "customer": 30_000_000,
        "supplier": 2_000_000,
        "part": 2_000_000,
    },
}


@pytest.mark.parametrize("qid", sorted(SCALE))
def test_benchmark_sums_are_proved_with_row_bounds(catalogue, qid):
    cat, queries, schemas = catalogue
    q = queries[qid]
    query = cat.build(q, schemas, "native")
    requires, ensures = cat.contract(q, schemas, "native")
    before = sv.verify(query, requires=requires, ensures=ensures, counterexamples=0)
    assert sum_risks(before)
    for t, n in SCALE[qid].items():
        requires[t] = [*requires.get(t, []), sv.max_rows(n)]
    report = sv.verify(query, requires=requires, ensures=ensures, counterexamples=0)
    assert not sum_risks(report), str(report)
    assert report.proved and report.guard_free
    assert report.rows is not None


def test_benchmark_sums_of_flags_are_proved_without_row_bounds(catalogue):
    # TPC-H Q12 counts lines with `SUM(CASE WHEN … THEN 1 ELSE 0 END)`: a group
    # has fewer than 2^63 rows (`Rel.sumRows`), so the sums fit 64 bits with no
    # `max_rows` (#437).
    cat, queries, schemas = catalogue
    q = queries["tpch-q12"]
    query = cat.build(q, schemas, "native")
    requires, ensures = cat.contract(q, schemas, "native")
    report = sv.verify(query, requires=requires, ensures=ensures, counterexamples=0)
    assert not sum_risks(report), str(report)
    assert report.proved and report.guard_free


# -- Delta metadata ------------------------------------------------------------


def amounts(orders):
    return orders.group_by("customer").aggregate(total=orders.amount.sum())


def test_delta_file_counts_prove_a_row_bound(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    [fact] = [f for f in src.snapshot().facts if f.rows is not None]
    assert (fact.rows, fact.condition, fact.source) == (3, "TRUE", "file stats @v2")

    contracted = sv.transform(
        requires={"orders": [_.amount >= 0, _.amount <= 100, sv.max_rows(10)]},
        ensures=[],
    )(amounts)
    node = src.pipe(contracted)
    report = contracted.report
    assert report is not None and not sum_risks(report)
    first = discharged(node.refresh()[node.name].preconditions)
    assert first[("orders", "max_rows(10)")] == "file stats @v2"


def test_a_row_bound_the_metadata_misses_is_checked_on_data(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7), (3, "cy", 1)])
    contracted = sv.transform(requires={"orders": [sv.max_rows(2)]}, ensures=[])(amounts)
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of orders violate max_rows\(2\)"):
        src.pipe(contracted).refresh()


def test_a_batch_beyond_the_bound_is_rejected():
    src = StaticSource(pa.table({"id": [1], "customer": ["ada"], "amount": [5]}), name="orders")
    contracted = sv.transform(requires={"orders": [sv.max_rows(2)]}, ensures=[])(amounts)
    node = src.pipe(contracted)
    first = discharged(node.refresh()[node.name].preconditions)
    assert first[("orders", "max_rows(2)")] == ON_DATA
    src.apply(Changes(inserts=[(2, "bob", 7)]))
    node.refresh()
    src.apply(Changes(inserts=[(3, "cy", 1)]))
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of orders violate max_rows\(2\)"):
        node.refresh()
