"""Rough edges of the public API found in a review (#408, #409, #412, #413)
and the wording of unproved conditions."""

import ibis
import ibis.expr.datatypes as dt
import pytest
from ibis import _

import sverify as sv
from sverify.contracts import CheckedCondition, References, requires_by_input

S = ibis.table({"a": "!int64"}, name="s")
CUSTOMERS = ibis.table({"id": "!int64"}, name="customers")


# #408: requires keys


def test_an_unknown_requires_table_names_the_key_the_inputs_and_a_match():
    with pytest.raises(ValueError, match=r"unknown table 'S'; the inputs are: s; did you mean 's'"):
        sv.verify(S.mutate(c=_.a + 1), requires={"S": [_.a >= 0]}, ensures=[_.c > 0])


def test_an_unknown_requires_table_without_a_close_match():
    with pytest.raises(ValueError, match=r"unknown table 'orders'; the inputs are: s$"):
        requires_by_input({"orders": []}, ["s"])


def test_a_list_of_requires_is_on_the_only_input():
    report = sv.verify(S.mutate(c=_.a + 1), requires=[_.a >= 0, _.a < 1000], ensures=[_.c > 0])
    assert report.proved
    assert report.requires["s"][0] == "(_.a >= 0)"


def test_a_list_of_requires_needs_exactly_one_input():
    with pytest.raises(ValueError, match="needs exactly one input table, and there are 2"):
        requires_by_input([_.a >= 0], ["s", "t"])


def test_transform_requires_an_unknown_parameter():
    with pytest.raises(TypeError, match=r"unknown parameter 'order'.*did you mean 'orders'"):

        @sv.transform(requires={"order": [_.a >= 0]})
        def f(orders):
            return orders


def test_transform_takes_a_list_of_requires_for_one_parameter():
    @sv.transform(requires=[_.a >= 0, _.a < 1000], ensures=[_.c > 0])
    def plus(t):
        return t.mutate(c=t.a + 1)

    assert set(plus.requires) == {"t"}
    plus(S)
    assert plus.report is not None and plus.report.proved


# #412: references


def test_references_takes_an_ibis_column():
    assert sv.references("cust", to=CUSTOMERS.id) == References("cust", "customers", "id")


def test_references_takes_a_pair_of_names():
    assert sv.references("cust", to=("customers", "id")) == References("cust", "customers", "id")


def test_references_needs_the_referenced_column():
    with pytest.raises(TypeError, match="needs the referenced column"):
        sv.references("cust")
    with pytest.raises(TypeError, match="a column of a named table"):
        sv.references("cust", to=CUSTOMERS.id + 1)


# #413: Connection's engine handles


def test_connection_public_attributes_are_generic():
    con = sv.connect()
    public = {n for n in vars(con) if not n.startswith("_")}
    assert public == {"engine", "arrow", "ibis"}


# The wording of an unproved condition


@pytest.mark.parametrize(
    ("value", "why"),
    [
        ("TRUE or FALSE", "it may be FALSE on some rows"),
        ("FALSE", "it is FALSE on every row"),
        ("TRUE or NULL", "it may be NULL on some rows, where a column it reads is NULL"),
        # NULL is not the only way to fail: no NOT NULL advice (#655).
        ("TRUE, FALSE or NULL", "it may be FALSE or NULL on some rows"),
    ],
)
def test_why_a_condition_is_unproved(value, why):
    assert CheckedCondition("c", False, value).why.startswith(why)


def test_a_nullable_column_suggests_not_null_only_where_null_alone_fails():
    t = ibis.table({"a": "int64", "s": "string"}, name="t")
    report = sv.verify(t.select(b=t.a), ensures=[_.b >= 0], counterexamples=0)
    assert "NOT proved: it may be FALSE or NULL on some rows" in str(report)
    assert ".notnull()" not in str(report)
    only_null = sv.verify(t.select(n=t.s.length()), ensures=[_.n >= 0], counterexamples=0)
    assert only_null.needed == {"t": ["_.s.notnull()"]}


# #440: ibis.param in a transformation


def test_a_transformation_with_an_unbound_param_says_how_to_bind_it():
    limit = ibis.param(dt.int64)

    @sv.transform(ensures=[_.big.notnull()])
    def flag(s):
        return s.select("a", big=s.a > limit)

    with pytest.raises(TypeError, match=r"flag uses ibis.param\(int64\).*#354.*params="):
        flag(S)
    # verify binds it.
    assert sv.verify(
        S.select("a", big=S.a > limit), params={limit: 3}, ensures=[_.big.notnull()]
    ).proved
