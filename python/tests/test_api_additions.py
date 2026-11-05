"""The public API additions of #691: `__version__`, `dir(sverify)`,
`to_substrait` on nodes and transforms, `PreconditionError`'s attributes,
`sv.key`, proved NOT NULL columns in a sink, and `isin` read as a range."""

import json

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.errors import ExportError, PreconditionError
from sverify.io import DeltaSink, DeltaSource, StaticSource

# -- the namespace --------------------------------------------------------------


def test_version():
    assert isinstance(sv.__version__, str) and sv.__version__


def test_dir_is_all():
    assert dir(sv) == sorted([*sv.__all__, "__version__"])
    # The documented submodules still import, and read as attributes.
    import sverify.engines
    import sverify.errors
    import sverify.io

    assert sv.io is sverify.io and sv.errors is sverify.errors and sv.engines is sverify.engines


# -- to_substrait ------------------------------------------------------------------


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000, sv.unique("id")]},
    ensures=[_.amount > 10, sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount > 10)


def _orders(**kw) -> StaticSource:
    rows = {"id": [1, 2, 3], "amount": [30, 5, 50]}
    rows.update(kw)
    return StaticSource(pa.table(rows), name="orders")


def test_node_to_substrait():
    node = _orders().pipe(paid)
    plan = json.loads(node.to_substrait())
    assert node.report is not None
    assert plan == json.loads(node.report.to_substrait())
    assert isinstance(node.to_substrait("binary"), bytes)


def test_transform_to_substrait():
    @sv.transform(requires={"t": [_.x >= 0, _.x < 100]}, ensures=[_.y >= 0])
    def double(t):
        return t.select(y=t.x * 2)

    with pytest.raises(ExportError, match="not been called"):
        double.to_substrait()
    double(ibis.table({"x": "int64"}, name="t"))
    assert double.last_report is not None
    assert json.loads(double.to_substrait()) == json.loads(double.last_report.to_substrait())


def test_plain_step_exports():
    # A plain function is a transform with an empty contract.
    node = _orders().pipe(lambda t: t.filter(t.amount > 1))
    assert node.report is not None and node.report.ensures == []
    assert json.loads(node.to_substrait())["relations"]


# -- PreconditionError ------------------------------------------------------------


def test_precondition_error_attributes():
    node = _orders(amount=[30, -5, -7]).pipe(paid)
    with pytest.raises(PreconditionError) as e:
        node.refresh()
    err = e.value
    assert err.source == "orders"
    assert err.condition is not None
    assert sv.contracts.label(err.condition) == "(_.amount >= 0)"
    assert err.rows is not None
    assert sorted(err.rows.column("amount").to_pylist()) == [-7, -5]


def test_precondition_error_unique_rows():
    node = _orders(id=[1, 1, 3]).pipe(paid)
    with pytest.raises(PreconditionError) as e:
        node.refresh()
    assert e.value.condition == sv.unique("id")
    assert e.value.rows is not None
    assert e.value.rows.column("id").to_pylist() == [1, 1]


def test_precondition_error_on_a_bound_table():
    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2], "amount": [3, -4]}))
    with pytest.raises(PreconditionError) as e:
        paid(con.table("orders"))
    assert e.value.source == "orders"
    assert e.value.rows is not None
    assert e.value.rows.to_pylist() == [{"id": 2, "amount": -4}]


def test_precondition_error_on_a_batch():
    orders = _orders()
    node = orders.pipe(paid)
    node.refresh()
    orders.apply(sv.Changes(inserts=[(4, -1), (5, 20)]))
    with pytest.raises(PreconditionError) as e:
        node.refresh()
    assert e.value.source == "orders"
    assert e.value.rows is not None
    assert e.value.rows.to_pylist() == [{"id": 4, "amount": -1}]


# -- sv.key -------------------------------------------------------------------------


def test_key_is_unique_and_not_null():
    t = ibis.table({"id": "int64", "x": "int64"}, name="t")
    r = sv.verify(t.filter(t.x > 0), requires={"t": [sv.key("id")]}, ensures=[sv.key("id")])
    assert r.proved
    assert r.requires["t"] == ["unique(id)", '"id" IS NOT NULL']
    assert [c.label for c in r.ensures] == ["unique(id)", '"id" IS NOT NULL']
    # Without the key, neither part is proved.
    r = sv.verify(t, ensures=[sv.key("id")])
    assert [c.proved for c in r.ensures] == [False, False]


def test_key_is_checked_on_data():
    @sv.transform(requires={"orders": [sv.key("id")]})
    def same(orders):
        return orders

    rows = pa.table({"id": pa.array([1, None], pa.int64()), "amount": [1, 2]})
    with pytest.raises(PreconditionError, match="IS NOT NULL"):
        StaticSource(rows, name="orders").pipe(same).refresh()


def test_key_needs_a_column():
    with pytest.raises(ValueError):
        sv.key()


# -- proved NOT NULL in the sink --------------------------------------------------


def test_proved_not_null_reaches_the_sink(tmp_path):
    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000, _.region.notnull()]},
        ensures=[_.total >= 0],
    )
    def totals(orders):
        return orders.group_by("region").aggregate(total=orders.amount.sum(), n=orders.count())

    rows = pa.table({"region": ["eu", "us", "eu"], "amount": [1, 2, 3]})
    node = StaticSource(rows, name="orders").pipe(totals)
    assert node.report is not None
    assert set(node.report.not_null) >= {"region", "total", "n"}
    stored = node.write(DeltaSink(str(tmp_path / "totals")))
    stored.refresh()
    from deltalake import DeltaTable

    schema = DeltaTable(str(tmp_path / "totals")).schema().to_arrow()
    nullable = {f.name: f.nullable for f in schema}
    assert nullable == {"region": False, "total": False, "n": False}
    contract = DeltaSource(str(tmp_path / "totals")).contract()
    assert contract is not None
    assert set(contract.not_null) == {"region", "total", "n"}


def test_maybe_null_column_stays_nullable():
    t = ibis.table({"k": "int64", "v": "int64"}, name="t")
    r = sv.verify(t.group_by("k").aggregate(m=t.v.max()))
    assert "m" not in r.not_null and "k" not in r.not_null


# -- isin as a range ------------------------------------------------------------------


def test_isin_of_integers_is_a_range():
    t = ibis.table({"x": "int64"}, name="t")
    expr = t.select(flag=(t.x > 5).ifelse(1, 0))
    assert sv.verify(expr, ensures=[_.flag.isin([0, 1])]).proved
    assert sv.verify(expr, ensures=[_.flag.isin([1, 0, 2])]).proved
    # A gap is not a range: [0, 2] says nothing about 1.
    expr2 = t.select(flag=(t.x > 5).ifelse(2, 1))
    assert not sv.verify(expr2, ensures=[_.flag.isin([0, 2])]).proved


def test_isin_of_integers_in_sql():
    r = sv.verify(
        "SELECT CASE WHEN x > 5 THEN 1 ELSE 0 END AS flag FROM t",
        tables={"t": ibis.schema({"x": "int64"})},
        ensures=["flag IN (0, 1)"],
    )
    assert r.proved


@pytest.mark.parametrize(
    ("values", "expected"),
    [([0, 1], (0, 1)), ([3, 1, 2], (1, 3)), ([0, 2], None), ([1], None), ([0, 1.0], None)],
)
def test_int_range(values, expected):
    from sverify.plan_json import int_range

    assert int_range(values) == expected


def test_isin_keeps_its_results():
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array([0, 1, 2, None], pa.int64())}))
    t = ibis.table({"x": "int64"}, name="t")
    r = sv.verify(t.select(hit=t.x.isin([0, 1])))
    assert r.plan is not None and "lte" in r.plan
    for engine in ("duckdb", "polars"):
        out = r.run(con, engine).column("hit").to_pylist()
        assert out == [True, True, False, None]


def test_precondition_error_rows_of_a_sql_condition():
    @sv.transform(requires={"orders": ["amount >= 0"]})
    def same(orders):
        return orders

    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2], "amount": [3, -4]}))
    with pytest.raises(PreconditionError) as e:
        same(con.table("orders"))
    assert e.value.condition == "amount >= 0"
    assert e.value.rows is not None
    assert e.value.rows.to_pylist() == [{"id": 2, "amount": -4}]
    # The connection is free for the next query.
    assert con.table("orders").count().to_pyarrow().as_py() == 2


# -- needed_conditions ----------------------------------------------------------------


def test_needed_conditions_prove_the_transform():
    t = ibis.table({"qty": "int64", "total": "int64", "k": "!int64"}, name="orders")
    expr = t.select(u=t.total // t.qty, v=t.k * 2)
    r = sv.verify(expr)
    assert not r.proved
    conds = r.needed_conditions
    assert set(conds) == {"orders"}
    assert all(not isinstance(c, str) for c in conds["orders"])
    # `qty` may be NULL: the bound lets NULL pass, as the inferred one does.
    assert any("isnull" in repr(c) and "qty" in repr(c) for c in conds["orders"])
    assert sv.verify(expr, requires=conds).proved


def test_needed_conditions_of_sql_are_sql():
    sql = "SELECT total // qty AS u FROM orders"
    tables = {"orders": ibis.schema({"qty": "int64", "total": "int64"})}
    r = sv.verify(sql, tables=tables)
    assert r.dialect == "sql"
    conds = r.needed_conditions
    assert set(conds) == {"orders"} and all(isinstance(c, str) for c in conds["orders"])
    assert '"qty" IS NULL OR "qty" <> 0' in conds["orders"]
    assert sv.verify(sql, tables=tables, requires=conds).proved


def test_needed_conditions_empty_when_assumed():
    t = ibis.table({"qty": "int64", "total": "int64"}, name="orders")
    r = sv.verify(t.select(u=t.total // t.qty), on_inferred="ignore")
    assert r.needed_conditions == {}


# -- SverifyError --------------------------------------------------------------------


def test_every_error_is_a_sverify_error():
    import sverify.errors as errors

    raised = [
        getattr(errors, n)
        for n in errors.__all__
        if isinstance(getattr(errors, n), type)
        and issubclass(getattr(errors, n), Exception)
        and not issubclass(getattr(errors, n), Warning)
    ]
    assert errors.SverifyError in raised
    for cls in raised:
        assert issubclass(cls, errors.SverifyError), cls


def test_errors_keep_their_builtin_bases_and_old_names():
    import sverify.engines
    import sverify.routes
    from sverify.errors import ExportError, RouteError, SverifyError, UnsupportedError

    assert issubclass(UnsupportedError, ValueError) and issubclass(RouteError, ValueError)
    assert issubclass(ExportError, ValueError)
    assert sverify.routes.RouteError is RouteError
    assert sverify.engines.UnsupportedError is UnsupportedError
    with pytest.raises(SverifyError):
        sv.verify("SELECT nope(x) FROM t", tables={"t": ibis.schema({"x": "int64"})})
