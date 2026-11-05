"""A `DeltaSink`'s commits read the same in the Delta history whatever the
storage (#453): a local sink commits the files DuckDB wrote
(`_write_native`), an S3 one MERGEs through delta-rs (here: the Polars
engine, which MERGEs locally too). Both log what the commit changed."""

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake

import sverify as sv
from sverify.io import DeltaSink, DeltaSource


def rows(n: int, start: int) -> pa.Table:
    return pa.table({"k": list(range(start, start + n)), "x": [1] * n})


@sv.transform(ensures=[sv.unique("k")], requires={"s": [sv.unique("k")]})
def same(s):
    return s.select("k", "x")


@sv.transform()
def ones(s):
    return s.filter(s.x == 1)


def last(uri: str) -> dict:
    return DeltaTable(uri).history(1)[0]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_change_logs_merge_metrics(tmp_path, engine):
    """The issue's repro: the second refresh's commit names the rows it
    inserted, on both paths."""
    src, out = str(tmp_path / "s"), str(tmp_path / "o")
    write_deltalake(src, rows(10, 0), configuration={"delta.enableChangeDataFeed": "true"})
    node = same(DeltaSource(src)).write(DeltaSink(out))
    node.refresh(engine=engine)
    write_deltalake(src, rows(5, 10), mode="append")
    assert node.refresh(engine=engine).writes[0].mode == "merge"
    metrics = last(out)["operationMetrics"]
    assert metrics["num_target_rows_inserted"] == 5
    assert metrics["num_target_rows_deleted"] == 0
    assert metrics["num_target_files_added"] >= 1  # delta-rs's MERGE may write two
    assert metrics["num_target_files_removed"] == 0


def test_a_native_change_logs_what_it_rewrote(tmp_path):
    src, out = str(tmp_path / "s"), str(tmp_path / "o")
    write_deltalake(src, rows(10, 0), configuration={"delta.enableChangeDataFeed": "true"})
    node = ones(DeltaSource(src)).write(DeltaSink(out))
    node.refresh()
    dt = DeltaTable(src)
    dt.update(updates={"x": "2"}, predicate="k < 3")  # three rows leave the view
    write_deltalake(src, rows(2, 10), mode="append")
    node.refresh()
    entry = last(out)
    assert entry["operation"] == "WRITE"
    assert entry["operationParameters"]["sverify"] == "merge"
    assert "sverify.contract" in entry  # the contract
    m = entry["operationMetrics"]
    assert (m["num_target_rows_inserted"], m["num_target_rows_deleted"]) == (2, 3)
    assert m["num_target_rows_copied"] == 7
    assert m["num_output_rows"] == m["num_added_rows"] == 9
    assert (m["num_target_files_added"], m["num_target_files_removed"]) == (2, 1)
    assert m["num_added_files"] == 2 and m["num_removed_files"] == 1
    assert sorted(r["k"] for r in DeltaTable(out).to_pyarrow_table().to_pylist()) == [
        *range(3, 10),
        10,
        11,
    ]


def test_the_first_write_logs_write_metrics(tmp_path):
    src, out = str(tmp_path / "s"), str(tmp_path / "o")
    write_deltalake(src, rows(4, 0), configuration={"delta.enableChangeDataFeed": "true"})
    assert same(DeltaSource(src)).write(DeltaSink(out)).refresh().writes[0].mode == "created"
    entry = last(out)
    assert entry["operationParameters"]["sverify"] == "created"
    m = entry["operationMetrics"]
    assert (m["num_added_rows"], m["num_added_files"], m["num_removed_files"]) == (4, 1, 0)
    assert "num_target_rows_inserted" not in m
