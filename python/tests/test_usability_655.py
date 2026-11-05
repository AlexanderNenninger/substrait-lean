"""The fresh-eyes review's findings (#655), one test each: unproved plans
refused, doubles into a sink within the plan's bound by default, and
reports and refusals in the user's terms."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import make_orders
from sverify import routes
from sverify.errors import PreconditionError, RouteError, UnverifiedRunWarning
from sverify.io import DeltaSink
from sverify.plan_json import Unsupported


@pytest.fixture
def con():
    c = sv.connect()
    c.put(
        "t",
        pa.table(
            {
                "k": ["a", "a", "b"],
                "x": [1.0, 2.0, 3.0],
                "qty": [1, 2, 0],
                "total": [10, 20, 30],
                "s": ["x1", "y2", "z3"],
            }
        ),
    )
    return c


# -- unproved runs ------------------------------------------------------------


def test_an_unproved_run_is_refused_in_user_terms(con) -> None:
    t = con.table("t")
    report = sv.verify(t.group_by("k").aggregate(s=t.x.sum()))
    assert not report.proved
    with pytest.raises(
        RouteError,
        match=r"refused on duckdb: not verified: may fail: domain error: sum\(x\) "
        r"\(see report.errors\); run\(\.\.\., unverified=True\) runs it anyway",
    ):
        report.run(con)


@sv.transform(ensures=[_.big > 100], on_unproved="warn")
def sums(orders):
    return orders.select("id", big=orders.amount.clip(0, 10))


def test_a_refresh_refuses_an_unproved_node_unless_asked(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    with pytest.warns(UserWarning):
        node = sums(orders)
    with pytest.raises(
        RouteError, match=r"sums: not verified: ensures \(_.big > 100\) is not proved"
    ):
        node.refresh()
    with pytest.warns(UnverifiedRunWarning, match="refreshing sums on duckdb unverified"):
        out = node.refresh(unverified=True)
    assert out["sums"].route is not None and out["sums"].route.kind == "unverified"
    assert "route on duckdb: unverified: not verified" in str(out)


# -- doubles into a sink ------------------------------------------------------


@sv.transform(requires={"orders": [_.amount >= 0, _.amount <= 1000, sv.max_rows(1000)]})
def mean(orders):
    return orders.group_by("customer").aggregate(m=orders.amount.cast("float64").mean())


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_mean_into_a_sink_needs_no_settings(tmp_path, engine) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7)])
    node = mean(orders).write(DeltaSink(str(tmp_path / "m")))
    out = node.refresh(engine=engine)
    route = out["m"].route
    assert route is not None and route.kind == "reference"
    assert node.to_arrow().to_pylist() == [{"customer": "ada", "m": 6.0}]


def test_exact_doubles_into_a_sink_are_asked_for(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = mean(orders).write(DeltaSink(str(tmp_path / "m"), reproducible=sv.equivalent()))
    with pytest.raises(
        RouteError,
        match=r"mean \(stored as m\): a rerun must give the same result: .*"
        r"pass reproducible=sv.equivalent\(floats=sv.within\(rel=",
    ):
        node.refresh(engine="polars")


def test_a_postcondition_on_a_double_keeps_it_exact() -> None:
    """`_.m >= 0` is proved of the reference's mean; DuckDB's is only near
    it, so the run asks for `sv.approx` or a stated tolerance."""
    c = sv.connect()
    c.put("orders", pa.table({"id": [1], "customer": ["ada"], "amount": [5]}))
    o = c.table("orders")
    report = sv.verify(
        o.group_by("customer").aggregate(m=o.amount.cast("float64").mean()),
        requires={"orders": [_.amount >= 0, _.amount <= 1000, sv.max_rows(1000)]},
        ensures=[_.m >= 0],
    )
    assert report.proved
    with pytest.raises(RouteError, match=r"reads m.*sv.approx\(\(_.m >= 0\)\)"):
        report.run(c, "polars")


def test_the_plan_bound_level() -> None:
    plan = sv.equivalent(floats="plan")
    assert sv.equivalent().refines(plan)
    assert not plan.refines(sv.equivalent())
    assert not plan.refines(sv.equivalent(floats=sv.within(rel=1e-9)))
    resolved = routes._resolve(plan, {"m": {"abs": 1e-10, "rel": 1e-13}, "k": {}})
    assert resolved.floats == sv.within(abs=1e-10, rel=1e-13)
    assert routes._resolve(plan, {"m": {"abs": None}}).floats == "plan"


# -- inferred preconditions ---------------------------------------------------


def test_an_inferred_precondition_says_where_it_came_from(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(t.k, per=t.total // t.qty), on_inferred="silent")
    assert "requires t: (_.qty != 0) (inferred from total // qty)" in str(report)
    with pytest.raises(
        PreconditionError,
        match=r"1 row\(s\) of t violate \(_.qty != 0\): refused before the run\. The "
        r"precondition was inferred from `total // qty` \(division by zero otherwise\): "
        r"drop those rows before the transform, `t.filter\(\(_.qty != 0\)\)`",
    ):
        report.run(con)


# -- reports in the user's terms ----------------------------------------------


def test_issues_name_columns_and_operators(con) -> None:
    t = con.table("t")
    report = sv.verify(t.select(t.k, y=t.x / 0))
    text = str(report)
    assert "may fail: division by zero: x / 0" in text
    assert "it divides by the constant 0" in text
    # The error and the assumption about the same operation no longer both show.
    assert "assumes: x / 0" not in text
    sql = sv.verify("SELECT k, total * total AS y FROM t", tables={"t": t}, infer=False)
    assert "overflow: total * total" in str(sql)


def test_the_and_or_hint_writes_out_the_guard(con) -> None:
    t = con.table("t")
    report = sv.verify(t.filter((t.qty != 0) & (t.total // t.qty > 1)))
    (hint,) = [h for h in report.hints if "AND or OR" in h]
    assert hint.startswith("`total // qty` is inside an AND or OR")
    assert "`ibis.cases((_.qty != 0, _.total // _.qty))`" in hint
    assert "D19" not in hint


def test_a_double_sum_names_its_cause(con) -> None:
    t = con.table("t")
    report = sv.verify(t.group_by("k").aggregate(s=t.x.sum()))
    assert "may fail: domain error: sum(x) (NaN where x holds both +inf and -inf" in str(report)


def test_null_and_key_hints(con) -> None:
    t = con.table("t")
    report = sv.verify(
        "SELECT k, qty FROM t WHERE qty IS NOT NULL",
        tables={"t": t},
        ensures=["qty > 3", sv.unique("k")],
    )
    text = str(report)
    assert "declare" not in text.split("ensures qty > 3")[1].split("\n")[0]
    assert "add sv.unique('k') on the input it comes from to requires" in text
    # FALSE is possible too, so NOT NULL alone would not prove it (#655).
    nullable = sv.verify(t.select("k", "qty"), ensures=[_.qty > 3])
    assert "where qty is NULL" not in str(nullable)


# -- refusals that name functions ---------------------------------------------


def test_an_engine_refusal_names_the_users_function(con) -> None:
    t = con.table("t")
    report = sv.verify(
        t.group_by("k").aggregate(m=t.x.median()), requires={"t": [_.x.between(0, 10)]}
    )
    with pytest.raises(
        RouteError,
        match=r"median\(\) or quantile\(\) .*runs on duckdb only: run it with engine='duckdb' "
        r".*https://github.com/AlexanderNenninger/substrait-lean/issues/271",
    ):
        report.run(con, "polars")


def test_the_lift_quotes_the_sql(con) -> None:
    t = con.table("t")
    with pytest.raises(Unsupported, match=r"^REGEXP_MATCHES\(t.s, 'x'\) is not supported yet"):
        sv.verify("SELECT regexp_matches(s, 'x') AS m FROM t", tables={"t": t})


@pytest.mark.parametrize("call", ["now()", "current_timestamp", "random()"])
def test_non_deterministic_sql_is_refused_as_such(con, call) -> None:
    t = con.table("t")
    with pytest.raises(Unsupported, match="gives another value on every run"):
        sv.verify(f"SELECT {call} AS v FROM t", tables={"t": t})
    with pytest.raises(Unsupported, match=r"ibis.now\(\) is not supported: the time differs"):
        sv.verify(t.select(n=ibis.now()))


# -- route classes and observations -------------------------------------------


def test_a_route_names_its_class_and_observation(tmp_path) -> None:
    """Four classes (exact, observed, shim, refused); an observed route keeps
    the observation, the tolerance its plan's bound gives, and whether that
    bound is proved."""
    assert routes.CLASSES == ("exact", "observed", "shim", "refused")
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 7)])
    node = mean(orders)
    route = node.refresh(engine="polars")["mean"].route
    assert route is not None and route.cls == "observed"
    assert route.observation is not None
    assert isinstance(route.observation.floats, sv.observation.Within)
    assert route.bound_proved in (True, False)
    assert f"[observed {route.observation}" in str(route)


def test_rows_are_read_by_the_old_and_new_keys() -> None:
    old = {"class": "approx", "q": {"floats": {"bound": "plan"}}, "rerun": {}}
    new = {
        "class": "observed",
        "observation": {"floats": {"bound": "plan"}},
        "rerun_observation": {},
    }
    for r in (old, new):
        assert routes.row_class(r) == "observed"
        assert routes.row_observation(r) == {"floats": {"bound": "plan"}}
        assert routes.row_rerun(r) == {}
    assert routes.row_class({"class": "refines"}) == "exact"
    assert routes.row_class({"class": "refines_up_to"}) == "observed"
