"""Contracts on list columns (#925).

The abstract domain describes a list column by its length and by one
abstract value for its elements, so bounds and NOT NULL pass through
`cardinality`, `transform` (Ibis `map`), `filter`, list elements and
`UNNEST` (`docs/nested-values.md`, "Abstract values"). Relations between the
elements of one list are out of scope.
"""

import ibis
from ibis import _

import sverify as sv

T = ibis.table({"id": "int64", "tags": "array<string>", "xs": "array<int64>"}, name="t")


def test_a_filtered_list_keeps_its_length_bound():
    # `filter` keeps some of the elements, so a list of at most 5 tags stays one.
    expr = T.select(T.id, tags=T.tags.filter(lambda s: s != ""))
    report = sv.verify(
        expr,
        requires={"t": [_.tags.notnull(), _.tags.length() <= 5]},
        ensures=[_.tags.length() <= 5, _.tags.length() >= 0],
    )
    assert report.proved, report.unproved
    assert report.facts["tags"] == "a list (length ≤ 5; of a string or NULL)"


def test_elements_are_not_null_after_fill_null():
    # `fill_null` on every element, then one row per element: none is NULL.
    expr = T.select(T.id, xs=T.xs.map(lambda x: x.fill_null(0))).unnest("xs")
    report = sv.verify(expr, ensures=[_.xs.notnull()])
    assert report.proved, report.unproved
    # Without it, an element may be NULL.
    report = sv.verify(T.select(T.id, T.xs).unnest("xs"), ensures=[_.xs.notnull()])
    assert not report.proved


def test_unnest_keeps_an_element_bound():
    # Elements clipped into [0, 9] stay there once unnested (`clip` keeps NULL).
    clipped = T.xs.map(lambda x: x.fill_null(0).clip(lower=0, upper=9))
    expr = T.select(T.id, xs=clipped).unnest("xs")
    report = sv.verify(expr, ensures=[_.xs >= 0, _.xs <= 9])
    assert report.proved, report.unproved


def test_an_element_in_range_is_not_null():
    # A list of at least one non-NULL element has a first element.
    expr = T.select(first=T.xs.map(lambda x: x.fill_null(0))[0])
    report = sv.verify(
        expr, requires={"t": [_.xs.notnull(), _.xs.length() >= 1]}, ensures=[_.first.notnull()]
    )
    assert report.proved, report.unproved
    # Without the length, the list may be empty.
    report = sv.verify(expr, requires={"t": [_.xs.notnull()]}, ensures=[_.first.notnull()])
    assert not report.proved
