"""`sverify.testing` and the pytest plugin (`sverify.pytest_plugin`): the
fixtures, the assertions and their messages, and `cases`.

The plugin's tests run pytest inside pytest (pytester), on
`test_plugin_example.py` and on small test files written here.
"""

import warnings
from importlib.metadata import entry_points
from pathlib import Path

import pyarrow as pa
import pytest
from hypothesis import given, settings
from ibis import _

import sverify as sv
from sverify import testing
from sverify.testing import (
    assert_contract,
    assert_engines_agree,
    cases,
    installed_engines,
    source,
)

pytest_plugins = ["pytester"]

ORDERS = {"id": "!int64", "customer": "string", "amount": "!int64"}
CUSTOMERS = {"name": "!string", "city": "string"}


@sv.transform(
    requires={"orders": [sv.unique("id"), _.amount >= 0, "amount < 1000"]},
    ensures=[sv.unique("id"), _.doubled >= 0],
)
def doubled(orders):
    return orders.select(orders.id, orders.customer, doubled=orders.amount * 2)


def orders_source():
    return source([], ORDERS, name="orders")


# -- the plugin -----------------------------------------------------------------


def test_the_plugin_is_registered():
    [ep] = [ep for ep in entry_points(group="pytest11") if ep.name == "sverify"]
    assert ep.value == "sverify.pytest_plugin"


def test_the_example_test_file_passes(pytester):
    example = Path(__file__).with_name("test_plugin_example.py").read_text()
    pytester.makepyfile(test_example=example)
    result = pytester.runpytest_subprocess("-p", "no:cacheprovider")
    engines = len(installed_engines())
    result.assert_outcomes(passed=3 + engines)
    result.stdout.no_fnmatch_line("*warning*")


def test_sv_engine_runs_once_per_engine(pytester):
    pytester.makepyfile(
        """
        def test_engine(sv_engine):
            assert sv_engine in ("duckdb", "polars", "datafusion")
        """
    )
    result = pytester.runpytest_subprocess("-v")
    for engine in installed_engines():
        result.stdout.fnmatch_lines([f"*test_engine?{engine}? PASSED*"])
    result.assert_outcomes(passed=len(installed_engines()))
    result = pytester.runpytest_subprocess("-v", "--sv-engines=duckdb")
    result.stdout.fnmatch_lines(["*test_engine?duckdb? PASSED*"])
    result.assert_outcomes(passed=1)


def test_the_plugin_can_be_turned_off(pytester):
    pytester.makepyfile("def test_source(sv_source):\n    pass\n")
    result = pytester.runpytest_subprocess("-p", "no:sverify")
    result.stdout.fnmatch_lines(["*fixture 'sv_source' not found*"])
    result.assert_outcomes(errors=1)


def test_a_failing_assertion_reads_well(pytester):
    pytester.makepyfile(
        """
        from ibis import _
        import sverify as sv
        from sverify.testing import assert_contract

        @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.doubled >= 0])
        def doubled(orders):
            return orders.select(orders.id, doubled=orders.amount * 2)

        def test_doubled(sv_source):
            orders = sv_source([], {"id": "int64", "amount": "int64"}, name="orders")
            assert_contract(
                doubled(orders),
                data={"orders": [(1, 30), (2, 4)]},
                expected=[(1, 60), (2, 9)],
            )
        """
    )
    result = pytester.runpytest_subprocess()
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [
            "*AssertionError: doubled on duckdb does not give the expected rows:",
            "*missing (1 expected row(s) not produced):",
            "*{'id': 2, 'doubled': 9}",
            "*unexpected (1 row(s) not expected):",
            "*{'id': 2, 'doubled': 8}",
        ]
    )
    # The traceback stops at the test, not inside sverify.testing.
    result.stdout.no_fnmatch_line("*sverify/testing.py*")


# -- source --------------------------------------------------------------------


def test_source_takes_tuples_dicts_or_arrow():
    a = source([(1, "ada", 3)], ORDERS, name="orders")
    b = source([{"id": 1, "customer": "ada", "amount": 3}], ORDERS, name="orders")
    c = source(a.table, name="orders")
    assert a.table == b.table == c.table
    assert not a.table.schema.field("id").nullable
    assert a.name == "orders" and a.version == 0
    with pytest.raises(TypeError, match="needs a schema"):
        source([(1,)])


# -- assert_contract -------------------------------------------------------------


def test_assert_contract_returns_the_output():
    out = assert_contract(
        doubled(orders_source()),
        data={"orders": [{"id": 1, "customer": "ada", "amount": 3}]},
        expected=[{"id": 1, "customer": "ada", "doubled": 6}],
    )
    assert out.to_pylist() == [{"id": 1, "customer": "ada", "doubled": 6}]
    assert assert_contract(doubled(orders_source())) is None


def test_expected_rows_are_a_bag():
    node = doubled(orders_source())
    data = {"orders": [(1, "a", 1), (2, "a", 1), (3, None, 0)]}
    assert_contract(node, data=data, expected=[(3, None, 0), (2, "a", 2), (1, "a", 2)])
    with pytest.raises(AssertionError) as e:  # a row twice: once is missing
        assert_contract(node, data=data, expected=[(3, None, 0), (2, "a", 2), (2, "a", 2)])
    assert str(e.value).splitlines()[1:] == [
        "  missing (1 expected row(s) not produced):",
        "    {'id': 2, 'customer': 'a', 'doubled': 2}",
        "  unexpected (1 row(s) not expected):",
        "    {'id': 1, 'customer': 'a', 'doubled': 2}",
    ]


def test_bad_test_data_is_named_with_its_rows():
    data = {"orders": [(1, "a", -1), (1, "b", 5), (2, "c", 1000)]}
    with pytest.raises(AssertionError) as e:
        assert_contract(doubled(orders_source()), data=data)
    assert str(e.value).splitlines() == [
        "the test data does not meet what doubled requires:",
        "  2 row(s) of orders violate unique(id):",
        "    {'id': 1, 'customer': 'a', 'amount': -1}",
        "    {'id': 1, 'customer': 'b', 'amount': 5}",
        "  1 row(s) of orders violate (_.amount >= 0):",
        "    {'id': 1, 'customer': 'a', 'amount': -1}",
        "  1 row(s) of orders violate amount < 1000:",
        "    {'id': 2, 'customer': 'c', 'amount': 1000}",
    ]


def test_data_must_name_the_tables_read():
    node = doubled(orders_source())
    with pytest.raises(ValueError, match=r"needs the tables \['orders'\]; missing \['orders'\]"):
        assert_contract(node, data={})
    with pytest.raises(ValueError, match=r"not read: \['other'\]"):
        assert_contract(node, data={"orders": [], "other": []})
    with pytest.raises(TypeError, match="needs data="):
        assert_contract(node, expected=[])  # type: ignore[no-matching-overload]
    with pytest.raises(TypeError, match="expected a sverify.Node"):
        assert_contract(doubled)  # type: ignore[arg-type]


def test_an_unproved_contract_fails():
    @sv.transform(ensures=[_.doubled >= 0], on_unproved="warn")
    def loose(orders):
        return orders.select(orders.id, doubled=orders.amount * 2)

    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        node = loose(orders_source())
    with pytest.raises(AssertionError) as e:
        assert_contract(node)
    lines = str(e.value).splitlines()
    assert lines[:3] == [
        "the contract of loose is not proved:",
        "  loose:",
        "    ensures (_.doubled >= 0): NOT proved (it is TRUE or FALSE)",
    ]


def test_an_unproved_link_fails():
    @sv.transform(requires={"t": [_.doubled >= 10]}, on_unproved="warn")
    def needs_ten(t):
        return t

    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        node = needs_ten(doubled(orders_source()))
    with pytest.raises(AssertionError, match=r"not proved: needs_ten: \(_.doubled >= 10\) on t"):
        assert_contract(node)


def test_a_stored_node_is_data_with_its_guarantees(tmp_path):
    from sverify.io import DeltaSink

    @sv.transform(requires={"t": [_.doubled >= 0]}, ensures=[_.plus >= 1])
    def plus_one(t):
        return t.select(t.id, plus=t.doubled + 1)

    stored = doubled(orders_source()).write(DeltaSink(str(tmp_path / "doubled")))
    node = plus_one(stored)
    assert_contract(node, data={"doubled": [(1, "a", 4)]}, expected=[(1, 5)])
    with pytest.raises(AssertionError, match=r"2 row\(s\) of doubled violate unique\(id\)"):
        assert_contract(node, data={"doubled": [(1, "a", 4), (1, "b", 2)]})


def test_a_postcondition_violated_on_an_engine_is_reported(monkeypatch):
    node = doubled(orders_source())
    monkeypatch.setattr(
        testing,
        "run_plan",
        lambda *_: pa.table({"id": [1, 1], "customer": ["a", "b"], "doubled": [2, -2]}),
    )
    with pytest.raises(AssertionError) as e:
        assert_contract(node, data={"orders": [(1, "a", 1)]})
    message = str(e.value)
    assert "violates its proved postconditions (please report this as a sverify bug)" in message
    assert "2 output row(s) violate unique(id)" in message
    assert "1 output row(s) violate (_.doubled >= 0)" in message


# -- assert_engines_agree --------------------------------------------------------


def test_engines_agree_on_a_join():
    @sv.transform(requires={"customers": [sv.unique("name")]})
    def cities(orders, customers):
        joined = orders.left_join(customers, orders.customer == customers.name)
        return joined.select(joined.id, joined.city)

    node = cities(orders_source(), source([], CUSTOMERS, name="customers"))
    data = {
        "orders": [(1, "ada", 3), (2, "bob", 4), (3, None, 5)],
        "customers": [("ada", "Paris"), ("cy", None)],
    }
    out = assert_engines_agree(node, data)
    assert sorted(out.to_pylist(), key=lambda r: r["id"]) == [
        {"id": 1, "city": "Paris"},
        {"id": 2, "city": None},
        {"id": 3, "city": None},
    ]


def test_engines_that_disagree_are_diffed(monkeypatch):
    node = doubled(orders_source())
    run_plan = testing.run_plan

    def skewed(con, plan, engine):
        out = run_plan(con, plan, engine)
        return out.slice(0, 1) if engine == "polars" else out

    monkeypatch.setattr(testing, "run_plan", skewed)
    data = {"orders": [(1, "a", 1), (2, "b", 2)]}
    with pytest.raises(AssertionError) as e:
        assert_engines_agree(node, data, engines=["duckdb", "polars"])
    assert str(e.value).splitlines() == [
        "the engines disagree on doubled (duckdb, polars):",
        "  polars differs from duckdb:",
        "  missing (1 expected row(s) not produced):",
        "    {'id': 2, 'customer': 'b', 'doubled': 4}",
    ]
    with pytest.raises(ValueError, match="at least two"):
        assert_engines_agree(node, data, engines=["duckdb"])


def test_an_engine_that_fails_is_reported(monkeypatch):
    node = doubled(orders_source())
    run_plan = testing.run_plan

    def broken(con, plan, engine):
        if engine == "polars":
            raise RuntimeError("boom")
        return run_plan(con, plan, engine)

    monkeypatch.setattr(testing, "run_plan", broken)
    with pytest.raises(AssertionError, match="polars failed: RuntimeError: boom"):
        assert_engines_agree(node, {"orders": [(1, "a", 1)]}, engines=["duckdb", "polars"])


# -- cases ---------------------------------------------------------------------


def test_cases_meet_the_preconditions():
    @sv.transform(
        requires={
            "orders": [
                sv.unique("id"),
                _.amount > 3,
                sv.references("customer", "customers", "name"),
            ],
            "customers": [sv.unique("name"), "city <> 'x'"],
        }
    )
    def cities(orders, customers):
        joined = orders.join(customers, orders.customer == customers.name)
        return joined.select(joined.id, joined.city)

    node = cities(orders_source(), source([], CUSTOMERS, name="customers"))
    seen = {"orders": 0, "customers": 0, "output": 0}

    @settings(max_examples=40, deadline=None, derandomize=True)
    @given(cases(node, max_rows=4))
    def check(data):
        assert set(data) == {"orders", "customers"}
        assert all(t.num_rows <= 4 for t in data.values())
        out = assert_contract(node, data=data)  # raises on data that violates `requires`
        for name in ("orders", "customers"):
            seen[name] += data[name].num_rows
        seen["output"] += out.num_rows

    check()
    # The repair keeps rows: the examples are not all empty.
    assert all(n > 0 for n in seen.values()), seen


def test_cases_refuses_types_it_cannot_generate():
    @sv.transform()
    def same(t):
        return t

    node = same(source([], {"xs": "array<int64>"}, name="t"))
    with pytest.raises(TypeError, match=r"cannot generate values of t.xs"):
        cases(node)
