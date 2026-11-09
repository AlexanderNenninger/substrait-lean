"""CI's shards, balanced by recorded durations (`sverify_dev.shard_durations`)."""

import json

import pytest

shard_durations = pytest.importorskip("sverify_dev.shard_durations")
oracle = pytest.importorskip("sverify_dev.oracle")


def test_balance_puts_the_longest_first_on_the_least_loaded_shard():
    table = shard_durations.balance({"a": 5.0, "b": 4.0, "c": 3.0, "d": 3.0}, 2)
    assert table["shard"] == {"a": 1, "b": 2, "c": 2, "d": 1}
    assert table["loads"] == [8.0, 7.0]


def test_balance_counts_the_benchmarks_in_shard_one():
    table = shard_durations.balance({"x": 2.0, "y": 2.0}, 2, {1: 3.0})
    assert table["shard"] == {"x": 2, "y": 2}


def test_oracle_shards_follow_the_table_and_round_robin_the_rest(tmp_path, monkeypatch):
    path = tmp_path / "oracle_shards.json"
    path.write_text(json.dumps({"n": 2, "shard": {"a": 2, "b": 2}}))
    monkeypatch.setattr(oracle, "SHARDS", path)
    files = ["a", "b", "c", "d", "e"]
    one, two = oracle.shard(files, "1/2"), oracle.shard(files, "2/2")
    assert sorted(one + two) == files
    assert one == ["c", "e"] and two == ["a", "b", "d"]


def test_oracle_shards_ignore_a_table_for_another_split(tmp_path, monkeypatch):
    path = tmp_path / "oracle_shards.json"
    path.write_text(json.dumps({"n": 3, "shard": {"a": 3}}))
    monkeypatch.setattr(oracle, "SHARDS", path)
    assert oracle.shard(["a", "b", "c", "d"], "1/2") == ["a", "c"]


def test_the_committed_tables_split_the_way_ci_does():
    tests = json.loads((shard_durations.TESTS).read_text())
    files = json.loads((shard_durations.ORACLE).read_text())
    assert tests["n"] == 3 and set(tests["shard"].values()) == {1, 2, 3}
    assert files["n"] == 4 and set(files["shard"].values()) == {1, 2, 3, 4}
