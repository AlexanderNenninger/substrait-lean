"""Tie order (D24, #679): the reference leaves `tie_order` and `tie_pick`
open, and a rerun that must reproduce the result needs them closed.

Under the reference a plan whose ties stay open is proved for every order
and runs natively; under a rerun requirement (`reproducible=sv.equivalent()`, a
sink's `reproducible=`) it is refused, and the refusal names each place.
`lean_choices` lists the values every order allows, and `allows_rows`
accepts an engine's rows when they are one of them."""

from __future__ import annotations

import json

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.engine import connect, run_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.routes import RouteError
from sverify.testing import allows_rows, inline_tables, lean_choices

T = ibis.table({"k": "int64", "x": "int64", "s": "string", "o": "int64"}, name="t")
#: Two rows of group 1 tie at o = 2, the largest.
ROWS = [(1, 10, "a", 1), (1, 20, "b", 2), (1, 30, "c", 2), (2, 40, "d", 5)]


def choices(expr: ibis.Table) -> list[list[tuple]] | None:
    plan = json.loads(to_substrait_json(expr))
    return lean_choices(json.dumps(inline_tables(plan, {"t": ROWS})))


def test_a_pick_over_ties_allows_each_tied_row() -> None:
    expr = T.group_by("k").aggregate(last=T.x.argmax(T.o))
    got = choices(expr)
    assert got is not None
    assert sorted(got, key=lambda r: r[0][1]) == [
        [("v", 1), ("any", [20, 30])],
        [("v", 2), ("v", 40)],
    ]
    assert allows_rows([(1, 20), (2, 40)], got)
    assert allows_rows([(2, 40), (1, 30)], got)
    assert not allows_rows([(1, 10), (2, 40)], got)
    assert not allows_rows([(1, 20)], got)


def test_a_near_tie_matches_as_relation_near_does() -> None:
    """#929 step 6: two rows tie on the exact column `s` order, and their
    doubles swap order under a perturbation within the tolerance. Sorting
    both results and comparing row by row pairs "a" with "b"; the matching,
    `Relation.Near`'s (the near-tie example in `Lipschitz.lean`), pairs each
    row with its own."""
    want = [[("v", 1.0 + 2e-9), ("v", "a")], [("v", 1.0), ("v", "b")]]
    got = [(1.0, "a"), (1.0 + 2e-9, "b")]

    def near(a: object, b: object) -> bool:
        if isinstance(a, float) and isinstance(b, float):
            return abs(a - b) <= 4e-9
        return a == b

    assert allows_rows(got, want, near)
    pairs = zip(sorted(got), sorted((r[0][1], r[1][1]) for r in want), strict=True)
    assert not all(near(a, b) and s == t for (a, s), (b, t) in pairs)
    assert not allows_rows(got, want)  # exactly, the doubles differ
    assert not allows_rows([(1.0, "a"), (1.0, "a")], want, near)


def test_the_index_on_fixed_columns_keeps_every_answer() -> None:
    """`allows_rows` looks only at the choice rows that agree on the columns
    every choice row fixes: the same answers as trying every pair."""
    import itertools

    want = [[("v", 1), ("any", [10, 20])], [("v", 1), ("v", 30)], [("v", 2), ("v", None)]]
    values = [(1, 10), (1, 20), (1, 30), (2, None), (2, 10), (1, None)]
    for got in itertools.permutations(values, 3):
        slow = allows_rows(got, want, lambda a, b: a == b)
        assert allows_rows(got, want) == slow
    assert allows_rows([(1, [1]), (2, [2])], [[("v", 1), ("v", [1])], [("v", 2), ("v", [2])]])


def test_an_unordered_string_agg_allows_every_order() -> None:
    expr = T.group_by("k").aggregate(s=T.s.group_concat(","))
    got = choices(expr)
    assert got is not None
    for joined in ("a,b,c", "c,a,b", "b,c,a"):
        assert allows_rows([(1, joined), (2, "d")], got)
    assert not allows_rows([(1, "a,b"), (2, "d")], got)
    assert not allows_rows([(1, "a,a,c"), (2, "d")], got)


def test_an_ordered_string_agg_allows_the_ties_in_any_order() -> None:
    expr = T.group_by("k").aggregate(s=T.s.group_concat(",", order_by=T.o))
    got = choices(expr)
    assert got is not None
    assert allows_rows([(1, "a,b,c"), (2, "d")], got)
    assert allows_rows([(1, "a,c,b"), (2, "d")], got)
    assert not allows_rows([(1, "b,a,c"), (2, "d")], got)


def test_no_ties_leave_one_result() -> None:
    expr = T.group_by("k").aggregate(first=T.x.argmin(T.x))
    got = choices(expr)
    assert got is not None and all(c[0] == "v" for row in got for c in row)


def test_ties_in_a_window_are_not_listed() -> None:
    w = ibis.window(group_by="k", order_by="o")
    assert choices(T.mutate(rn=ibis.row_number().over(w))) is None


def test_duckdbs_own_pick_is_allowed() -> None:
    """DuckDB's own `arg_max` over the ties is one the reference allows."""
    expr = T.group_by("k").aggregate(last=T.x.argmax(T.o))
    got = choices(expr)
    assert got is not None
    con = connect()
    con.create("t", T.schema(), ROWS)
    native = con._ibis.con.sql(ibis.to_sql(expr, dialect="duckdb")).to_arrow_table()
    assert allows_rows([tuple(r.values()) for r in native.to_pylist()], got)
    written = run_plan(con, to_substrait_json(expr), "duckdb")
    assert allows_rows([tuple(r.values()) for r in written.to_pylist()], got)


# -- Both profiles -----------------------------------------------------------

W = ibis.window(group_by="k", order_by="o")
RANKED = T.mutate(rn=ibis.row_number().over(W))


def test_the_reference_proves_every_order_and_runs_natively() -> None:
    report = sv.verify(RANKED, ensures=[_.rn >= 0])
    assert report.verdict == sv.Verdict.PROVED and not report.deterministic
    r = routes.choose(report, "duckdb")
    assert not r.refused
    assert any("ties stay open:" in w for w in r.warnings)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_rerun_requirement_refuses_open_ties_and_names_the_place(engine) -> None:
    report = sv.verify(RANKED, ensures=[_.rn >= 0])
    r = routes.choose(report, engine, reproducible=sv.equivalent())
    assert r.refused
    assert "the window at relation" in r.reason
    assert "ROW_NUMBER() over rows that tie in PARTITION BY [$0] ORDER BY [$3]" in r.reason
    assert "sv.unique('k', 'o')" in r.reason


def test_a_rerun_requirement_takes_a_total_order() -> None:
    report = sv.verify(RANKED, requires={"t": [sv.unique("k", "o")]}, ensures=[_.rn >= 0])
    assert report.deterministic and report._tie_places == []
    assert not routes.choose(report, "duckdb", reproducible=sv.equivalent()).refused


def test_an_ordered_aggregate_is_named_too() -> None:
    report = sv.verify(T.group_by("k").aggregate(last=T.x.argmax(T.o)))
    assert [p.op for p in report._tie_places] == ["aggregate"]
    r = routes.choose(report, "duckdb", reproducible=sv.equivalent())
    assert r.refused and "the aggregate at relation" in r.reason


def test_a_sink_that_must_reproduce_refuses_open_ties() -> None:
    con = connect()
    con.create("t", T.schema(), ROWS)
    report = sv.verify(RANKED, ensures=[_.rn >= 0])
    with pytest.raises(RouteError, match="the plan leaves open the window"):
        report.run(con, "duckdb", reproducible=sv.equivalent())
    assert report.run(con, "duckdb").num_rows == len(ROWS)


# -- Tie-free ranks and keys through joins (the API critique, #686) ----------


@pytest.mark.parametrize(
    "fn", [ibis.rank, ibis.dense_rank, ibis.percent_rank, ibis.cume_dist], ids=lambda f: f.__name__
)
def test_ranks_over_the_window_order_are_tie_free(fn) -> None:
    """Tied rows get the same rank whatever their arrangement (`window_tieFree`),
    so the result is determined without a key; `ROW_NUMBER` is not."""
    ranked = T.mutate(r=fn().over(ibis.window(group_by="k", order_by="o")))
    report = sv.verify(ranked)
    assert report.deterministic and report._tie_places == []
    assert not routes.choose(report, "duckdb", reproducible=sv.equivalent()).refused
    numbered = T.mutate(r=ibis.row_number().over(ibis.window(group_by="k", order_by="o")))
    assert not sv.verify(numbered).deterministic


SQL_TABLES = {
    "orders": ibis.table({"customer_id": "int64", "amount": "float64"}, name="orders"),
    "customers": ibis.table({"customer_id": "int64", "name": "string"}, name="customers"),
}
SQL_REQUIRES = {
    "orders": ["customer_id IS NOT NULL"],
    "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")],
}


@pytest.mark.parametrize("side", ["p", "c"])
def test_a_key_is_seen_through_the_columns_a_join_equates(side) -> None:
    """`p.customer_id = c.customer_id`: a key on either column is a key on the
    other (`KeyOn.eqVariants`)."""
    q = (
        f"SELECT {side}.customer_id, c.name FROM (SELECT customer_id, count(*) n FROM orders "
        "GROUP BY customer_id) p JOIN customers c ON c.customer_id = p.customer_id"
    )
    report = sv.verify(
        q, tables=SQL_TABLES, requires=SQL_REQUIRES, ensures=[sv.unique("customer_id")]
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)


def test_a_key_through_a_join_breaks_the_ties_of_a_window() -> None:
    """The critique's mart: ROW_NUMBER over revenue, ties broken by the
    dimension's customer_id, is determined once the key is seen through the
    join."""
    q = """
    SELECT c.customer_id, p.revenue,
           row_number() OVER (ORDER BY p.revenue DESC, c.customer_id) AS rn
    FROM (SELECT customer_id, sum(amount) AS revenue FROM orders GROUP BY customer_id) p
    JOIN customers c ON c.customer_id = p.customer_id
    """
    report = sv.verify(q, tables=SQL_TABLES, requires=SQL_REQUIRES, ensures=["rn >= 1"])
    assert report.deterministic and report._tie_places == []


def _checker_reports(monkeypatch):
    """The checker's raw `--contract` reports while `sv.verify` runs."""
    import sverify.contracts as contracts

    seen: list[dict] = []
    run = contracts.run_checker

    def spy(flags, stdin):
        code, out, err = run(flags, stdin)
        if flags == ("--contract",) and code == 0:
            seen.append(json.loads(out))
        return code, out, err

    monkeypatch.setattr(contracts, "run_checker", spy)
    return seen


_T = ibis.table({"k": "int64", "x": "float64", "n": "int64"}, name="t")


@pytest.mark.parametrize(
    "expr",
    [_T.group_by("k").aggregate(m=_T.x.max()), _T.group_by("x").aggregate(c=_T.k.count())],
    ids=["max of doubles", "group by a double"],
)
def test_a_class_pick_is_determined_up_to_the_class(monkeypatch, expr):
    """D48: a place that only picks a member of a class (`-0.0` or `0.0`, a
    NaN) leaves the result determined up to the class, though not exactly."""
    seen = _checker_reports(monkeypatch)
    sv.verify(expr)
    (out,) = seen
    assert not out["deterministic"]
    assert out["class_determined"]
    assert [p["kind"] for p in out["tie_places"]] == ["class"]
    assert out["class_places"] == []


def test_atan2_of_a_picked_double_is_not_determined_up_to_the_class(monkeypatch):
    """`atan2(-0.0, -1)` is `-π` and `atan2(0.0, -1)` is `π`: an expression
    that tells the members apart drops the class level, and the report names
    it."""
    seen = _checker_reports(monkeypatch)
    mins = _T.group_by("k").aggregate(m=_T.x.min())
    sv.verify(mins.mutate(a=mins.m.atan2(-1.0)))
    (out,) = seen
    assert not out["class_determined"]
    (place,) = out["class_places"]
    assert "ATAN2" in place["what"] and "picked from a class" in place["what"]


def test_a_cast_of_a_picked_double_to_a_string_is_refused():
    """D48 §2.5's second counterexample, `CAST(MIN(x) AS VARCHAR)`, tells
    `-0.0` from `0.0` with a string result. The reference refuses every cast
    of a double to a string, so no plan reaches the class level with one;
    were the cast admitted, its expression is not a bare column, and
    `Expr.classCongr` would name it as `atan2`'s is named above."""
    from sverify.errors import UnsupportedError

    mins = _T.group_by("k").aggregate(m=_T.x.min())
    with pytest.raises(UnsupportedError, match="unsupported cast from .*float to .*str"):
        sv.verify(mins.mutate(s=mins.m.cast("string")))


def test_an_open_tie_is_open_at_both_levels(monkeypatch):
    seen = _checker_reports(monkeypatch)
    sv.verify(_T.group_by("k").aggregate(f=_T.x.first()))
    (out,) = seen
    assert not out["deterministic"] and not out["class_determined"]
    assert [p["kind"] for p in out["tie_places"]] == ["tie"]


# -- D48 in Python: `Report.deterministic` is the class level -----------------


def test_the_report_reads_the_class_level():
    """`Report.deterministic` is the class level; the exact level stays the
    writers' (`_exact`)."""
    picks = sv.verify(_T.group_by("k").aggregate(m=_T.x.max()))
    assert picks.deterministic and not picks._exact
    assert [p.kind for p in picks._tie_places] == ["class"] and picks._class_places == []
    mins = _T.group_by("k").aggregate(m=_T.x.min())
    reads = sv.verify(mins.mutate(a=mins.m.atan2(-1.0)))
    assert not reads.deterministic
    assert any("picked from a class" in p.what for p in reads._class_places)
    tie = sv.verify(_T.group_by("k").aggregate(f=_T.x.first()))
    assert not tie.deterministic and not tie._exact


def test_a_report_read_back_keeps_both_levels():
    report = sv.verify(_T.group_by("x").aggregate(c=_T.k.count()))
    again = sv.Report.from_json(report.to_json())
    assert (again.deterministic, again._exact) == (True, False)
    assert again._tie_places == report._tie_places


@pytest.mark.parametrize(
    "expr",
    [_T.group_by("k").aggregate(m=_T.x.max()), _T.group_by("x").aggregate(c=_T.k.count())],
    ids=["max of doubles", "group by a double"],
)
def test_a_class_pick_reruns_under_the_default_and_not_under_exact_zeros(expr):
    """D48: the default observation reads one zero and one NaN, so a rerun
    that picks another member reproduces the result; an observation that
    reads the members refuses the pick, names it and gives the two ways out."""
    report = sv.verify(expr)
    for q in (sv.equivalent(floats="plan"), sv.equivalent(zeros="canon")):
        assert not routes.choose(report, "duckdb", reproducible=q).refused
    # The engines' rerun rows are compared component by component, and the
    # default keeps `zeros` as one: no row may refuse the default on its zeros
    # (Fable's ruling on #1642, item 3).
    for engine in ("duckdb", "polars", "spark"):
        problems, _ = routes.reproducibility(report, engine, sv.equivalent(floats="plan"))
        assert not [p for p in problems if "zeros" in p or "class of doubles" in p], engine
    r = routes.choose(report, "duckdb", reproducible=sv.equivalent())
    assert r.refused and "reads the members of a class of doubles" in r.reason
    assert "picks one at the aggregate" in r.reason and routes.CLASS_PICKS in r.reason
    assert "unique(" not in r.reason


def test_a_refresh_of_a_max_of_doubles(tmp_path):
    """`SELECT region, MAX(price) … GROUP BY region` with a double price
    refreshes under the sink's default (D48); exact zeros refuse it."""
    from deltalake import DeltaTable, write_deltalake

    from sverify.errors import RouteError as Refused
    from sverify.io import DeltaSink, DeltaSource

    write_deltalake(
        str(tmp_path / "prices"),
        pa.table({"region": ["n", "n", "s", "s"], "price": [1.5, 2.5, -0.0, 0.0]}),
    )

    @sv.transform()
    def top(prices):
        return prices.group_by("region").aggregate(top=prices.price.max())

    node = top(DeltaSource(str(tmp_path / "prices"))).write(DeltaSink(str(tmp_path / "out")))
    node.refresh(engine="duckdb")
    out = DeltaTable(str(tmp_path / "out")).to_pyarrow_table().sort_by("region")
    assert out.column("top").to_pylist() == [2.5, 0.0]
    exact = top(DeltaSource(str(tmp_path / "prices"))).write(
        DeltaSink(str(tmp_path / "exact"), reproducible=sv.equivalent())
    )
    with pytest.raises(Refused, match="reads the members of a class") as err:
        exact.refresh(engine="duckdb")
    assert routes.CLASS_PICKS in str(err.value) and "unique(" not in str(err.value)


def test_keys_are_groups_up_to_canonical_codes() -> None:
    """`-0.0` and `0.0` are one key (D31): `lean_choices` lists one group and one
    `DISTINCT` row, as `Rel.eval` does, where it listed one per spelling and
    `allows_rows` then rejected the single row an engine returns."""
    t = ibis.table({"k": "float64", "x": "int64", "o": "int64"}, name="t")
    rows = [(-0.0, 1, 1), (0.0, 2, 2)]

    def listed(expr: ibis.Table) -> list[list[tuple]] | None:
        plan = json.loads(to_substrait_json(expr))
        return lean_choices(json.dumps(inline_tables(plan, {"t": rows})))

    grouped = listed(t.group_by("k").aggregate(last=t.x.argmax(t.o)))
    assert grouped is not None and len(grouped) == 1
    assert allows_rows([(0.0, 2)], grouped)
    distinct = listed(t.select("k").distinct())
    assert distinct is not None and len(distinct) == 1
    assert allows_rows([(0.0,)], distinct)
