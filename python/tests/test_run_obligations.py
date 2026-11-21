"""The runtime obligations that tie a run to the engine theorem's hypotheses
(#1130; `docs/proofs.md`, "What is trusted"), on each of DuckDB, Polars and
Spark:

2. The session's settings are read back before the run, and a setting the
   plan relies on that differs from the profile's refuses it, so the sink is
   not written.
4. An engine that raises leaves the sink untouched: no commit, the epoch of
   the last refresh kept.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from typing import Any

import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from _pipelines import make_orders, orders_table
from sverify import _duckdb
from sverify.errors import EngineSettingsError

ENGINES = [
    "duckdb",
    "polars",
    pytest.param("spark", marks=pytest.mark.backend("spark")),
]


def _session(engine: str) -> Any:
    """The engine's session, for `engine` as a refresh argument (a name)."""
    if engine == "spark":
        pytest.importorskip("sverify_spark")
    return engine


@pytest.fixture
def drift(monkeypatch: pytest.MonkeyPatch) -> Iterator[Callable[[str], None]]:
    """Move one setting of an engine's session off its profile's value, which
    a plan that relies on it refuses; undone after the test."""
    undo: list[Callable[[], None]] = []

    def set_up(engine: str) -> None:
        if engine == "duckdb":
            other = _duckdb.cursor()
            other.execute("SET GLOBAL integer_division = true").fetchall()

            def reset() -> None:
                other.execute("RESET GLOBAL integer_division").fetchall()

            undo.append(reset)
        elif engine == "polars":
            monkeypatch.setenv("POLARS_ENGINE_AFFINITY", "in-memory")
        else:
            from sverify_spark import engine as spark_engine

            spark = spark_engine.session()
            spark.conf.set("spark.sql.ansi.enabled", "false")
            undo.append(lambda: spark.conf.set("spark.sql.ansi.enabled", "true"))

    yield set_up
    for f in undo:
        f()


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000]})
def halves(orders):
    """Relies on integer division (DuckDB), on the sum's overflow (Spark)."""
    return orders.group_by("customer").aggregate(half=(orders.amount // 2).sum())


@pytest.mark.parametrize("engine", ENGINES)
def test_a_session_off_the_profile_refuses_a_refresh_and_writes_nothing(
    engine: str, drift: Callable[[str], None], tmp_path: Any
) -> None:
    """Obligation 2: the refresh reads the session's settings back first."""
    engine = _session(engine)
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = halves(orders).write(sv.io.DeltaSink(str(tmp_path / "halves")))
    drift(engine)
    with pytest.raises(EngineSettingsError):
        node.refresh(engine=engine)
    with pytest.raises(Exception):  # noqa: B017 - the sink was never created
        DeltaTable(str(tmp_path / "halves"))


@sv.transform(on_unproved="warn")
def numbers(orders):
    """The square: each engine raises on an overflow of 64 bits, as the
    reference does."""
    return orders.select(orders.id, n=orders.amount * orders.amount)


@pytest.mark.filterwarnings("ignore::sverify._unsupported.SverifyWarning")
@pytest.mark.parametrize("engine", ENGINES)
def test_an_engine_that_raises_leaves_the_sink_untouched(engine: str, tmp_path: Any) -> None:
    """Obligation 4: the first refresh commits, the second meets a row
    the engine raises on (a square past 64 bits), and the sink keeps the version and the rows of the
    first."""
    engine = _session(engine)
    orders = make_orders(tmp_path / "orders", [(1, "a", 10), (2, "b", 7)])
    sink = str(tmp_path / "numbers")
    node = numbers(orders).write(sv.io.DeltaSink(sink))
    node.refresh(engine=engine, unverified=True)
    kept = DeltaTable(sink)
    version, rows = (
        kept.version(),
        sorted(kept.to_pyarrow_table().to_pylist(), key=lambda r: r["id"]),
    )
    assert [r["n"] for r in rows] == [100, 49]

    write_deltalake(str(tmp_path / "orders"), orders_table([(3, "c", 2**62)]), mode="append")
    with pytest.raises(Exception, match=r"(?i)overflow|leaves 64 bits"):  # the engine's own
        node.refresh(engine=engine, unverified=True)
    after = DeltaTable(sink)
    assert after.version() == version
    assert sorted(after.to_pyarrow_table().to_pylist(), key=lambda r: r["id"]) == rows
