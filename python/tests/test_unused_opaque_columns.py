"""#1996: a pipeline reads a table with an unused map, struct or binary column,
as `verify` does (`ibis_substrait.prune`): refresh and a transform with
`requires` need not model a column no step mentions."""

import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
from _pipelines import rows
from sverify.io import DeltaSource, StaticSource
from sverify.plan_json import Unsupported

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


def test_a_used_opaque_column_is_still_refused():
    with pytest.raises(Unsupported, match="not supported"):
        StaticSource(table("map"), name="t").pipe(lambda t: t.select("id", "extra")).refresh()
