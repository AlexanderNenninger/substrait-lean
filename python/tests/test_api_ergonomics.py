"""Rough edges of the public API found in a review (#408, #409, #412, #413)
and the wording of unproved conditions."""

import ibis
import ibis.expr.datatypes as dt
import pytest
from ibis import _

import sverify as sv
from sverify.contracts import CheckedCondition, References, requires_by_input


def _needed(report):
    """The labels of `report.needs` per input table."""
    out: dict[str, list[str]] = {}
    for n in report.needs:
        out.setdefault(n.table, []).append(n.label)
    return out


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
    assert report.verdict == sv.Verdict.PROVED
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
    assert plus.report is not None and plus.report.verdict == sv.Verdict.PROVED


# #412: references


def test_references_takes_an_ibis_column():
    assert sv.references("cust", to=CUSTOMERS.id) == References(("cust",), "customers", ("id",))


def test_references_takes_a_pair_of_names():
    assert sv.references("cust", to=("customers", "id")) == References(
        ("cust",), "customers", ("id",)
    )
    assert sv.references("cust", to=("customers", "id")).label == "references(cust, customers.id)"


# #2223: composite foreign keys

ADDRESSES = ibis.table({"street": "string", "zip": "string", "n": "int64"}, name="addresses")


def test_references_takes_several_columns_of_one_table():
    want = References(("street", "zip"), "addresses", ("street", "zip"))
    assert sv.references("street", "zip", to=[ADDRESSES.street, ADDRESSES.zip]) == want
    assert sv.references("street", "zip", to=("addresses", ["street", "zip"])) == want
    assert want.label == "references((street, zip), addresses.(street, zip))"


@pytest.mark.parametrize(
    ("cols", "to", "error", "match"),
    [
        ((), ("addresses", ["street"]), ValueError, "at least one column"),
        (("street",), ("addresses", ["street", "zip"]), ValueError, "1 column.* and 2 referenced"),
        (("a", "a"), ("addresses", ["street", "zip"]), ValueError, r"column\(s\) \['a'\]"),
        (("a", "b"), ("addresses", ["zip", "zip"]), ValueError, "repeats"),
        (("a", "b"), [ADDRESSES.street, CUSTOMERS.id], TypeError, "columns of one table"),
        (("a", "b"), [ADDRESSES.street, ADDRESSES.n + 1], TypeError, "a column of a named table"),
    ],
)
def test_references_refuses_a_malformed_key(cols, to, error, match):
    with pytest.raises(error, match=match):
        sv.references(*cols, to=to)


def test_a_pair_of_columns_that_do_not_compare_is_refused_at_verify():
    o = ibis.table({"street": "string", "zip": "int64"}, name="o")
    with pytest.raises(TypeError, match=r"o.zip is int64 and addresses.street is string"):
        sv.verify(
            o.join(ADDRESSES, o.street == ADDRESSES.zip).select(o.zip),
            requires={"o": [sv.references("street", "zip", to=("addresses", ["zip", "street"]))]},
        )


def test_the_rows_violating_a_composite_foreign_key_are_those_of_no_pair():
    """MATCH SIMPLE: a row with a NULL part is exempt; (1, 'b') breaks the key
    though 1 and 'b' each occur in `p` (the counts: test_table_conditions_as_plans)."""
    p = [{"a": 1, "b": "a"}, {"a": 2, "b": "b"}]
    rows = [{"x": x, "y": y} for x, y in [(1, "a"), (2, "b"), (1, "b"), (None, "z")]]
    fk = sv.references("x", "y", to=("p", ["a", "b"]))
    assert fk.violating(rows, lambda v: v, lambda t: p) == [{"x": 1, "y": "b"}]


def test_references_needs_the_referenced_column():
    with pytest.raises(TypeError, match="needs the referenced column"):
        sv.references("cust")
    with pytest.raises(TypeError, match="a column of a named table"):
        sv.references("cust", to=CUSTOMERS.id + 1)


# #413: Connection's engine handles


def test_connection_public_attributes_are_generic():
    con = sv.connect()
    public = {n for n in vars(con) if not n.startswith("_")}
    assert public == {"engine"}


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
    assert "NOT proved: it may be FALSE or NULL on some rows" in report.details()
    assert ".notnull()" not in report.details()
    only_null = sv.verify(t.select(n=t.s.length()), ensures=[_.n >= 0], counterexamples=0)
    assert _needed(only_null) == {"t": ["_.s.notnull()"]}


# #440: ibis.param in a transformation


def test_a_transformation_with_an_unbound_param_says_how_to_bind_it():
    limit = ibis.param(dt.int64)

    @sv.transform(ensures=[_.big.notnull()])
    def flag(s):
        return s.select("a", big=s.a > limit)

    with pytest.raises(TypeError, match=r"flag uses ibis.param\(int64\).*#354.*params="):
        flag(S)
    # verify binds it.
    assert (
        sv.verify(
            S.select("a", big=S.a > limit), params={limit: 3}, ensures=[_.big.notnull()]
        ).verdict
        == sv.Verdict.PROVED
    )
