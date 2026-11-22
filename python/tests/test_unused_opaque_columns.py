"""#1996: a pipeline reads a table with an unused map, struct or binary column,
as `verify` does (`ibis_substrait.prune`): refresh and a transform with
`requires` need not model a column no step mentions."""

import ibis
import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
from _pipelines import rows
from sverify._unsupported import Unsupported
from sverify.io import DeltaSource, StaticSource

#: Ibis types of the opaque columns `verify` reads (D67).
OPAQUE_DTYPES = {"map": "map<string, string>", "binary": "binary"}

OPAQUE = {
    "map": pa.array([[("a", "b")], []], pa.map_(pa.string(), pa.string())),
    "struct": pa.array([{"x": 1}, {"x": 2}]),
    "binary": pa.array([b"a", b"b"], pa.binary()),
}


def table(kind: str) -> pa.Table:
    return pa.table(
        {
            "id": pa.array([1, 2], pa.int64()),
            "amt": pa.array([3, 4], pa.int64()),
            "extra": OPAQUE[kind],
        }
    )


def static(kind: str, _path) -> StaticSource:
    return StaticSource(table(kind), name="t")


def delta(kind: str, path) -> DeltaSource:
    write_deltalake(
        str(path / "t"), table(kind), configuration={"delta.enableChangeDataFeed": "true"}
    )
    return DeltaSource(str(path / "t"))


SOURCES = [pytest.param(static, id="static"), pytest.param(delta, id="delta")]
KINDS = list(OPAQUE)


def totals(t):
    return t.group_by("id").aggregate(total=_.amt.sum())


@sv.transform(requires={"t": [_.amt >= 0, _.amt < 1_000_000]})
def bounded(t):
    return t.group_by("id").aggregate(total=_.amt.sum())


@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("make", SOURCES)
def test_refresh_ignores_an_unused_opaque_column(make, kind, tmp_path):
    node = make(kind, tmp_path).pipe(totals)
    node.refresh()
    assert rows(node) == [(1, 3), (2, 4)]


@pytest.mark.parametrize("kind", KINDS)
@pytest.mark.parametrize("make", SOURCES)
def test_a_transform_with_requires_ignores_an_unused_opaque_column(make, kind, tmp_path):
    node = bounded(make(kind, tmp_path))
    node.refresh()
    assert rows(node) == [(1, 3), (2, 4)]


@pytest.mark.parametrize("kind", ["map", "binary"])
def test_a_carried_opaque_column_refreshes(kind):
    """A map or binary column the view carries passes through unchanged (D67)."""
    node = StaticSource(table(kind), name="t").pipe(lambda t: t.select("id", "extra"))
    node.refresh()
    assert [r[1] for r in rows(node)] == [
        list(v.items()) if isinstance(v, dict) else v for v in table(kind)["extra"].to_pylist()
    ]


def test_a_read_opaque_column_is_still_refused():
    with pytest.raises(Unsupported, match="ORDER BY it"):
        StaticSource(table("map"), name="t").pipe(lambda t: t.order_by("extra")).refresh()


@pytest.mark.parametrize("kind", list(OPAQUE_DTYPES))
def test_a_sql_condition_ignores_an_opaque_column_it_does_not_read(kind):
    """#1958: a SQL `requires` or `ensures` is lifted over the whole table, and
    proves over one with a map or binary column it does not read."""
    t = ibis.table({"id": "int64", "amt": "int64", "extra": OPAQUE_DTYPES[kind]}, name="t")
    report = sv.verify(
        t.select("id", "amt", "extra"),
        requires={"t": ['"id" IS NOT NULL', '"amt" >= 0']},
        ensures=['"id" IS NOT NULL', '"amt" >= 0'],
    )
    assert report.verdict == sv.Verdict.PROVED
