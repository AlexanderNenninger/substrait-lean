"""Oracle A's gate (`sverify_dev.oracle`, #242): which changes against the
ledgers fail it."""

from sverify_dev import oracle


def test_regressions_and_new_disagreements_fail():
    before = {"a": "agree", "b": "refused", "c": "disagree", "d": "skipped", "e": "agree"}
    after = {"a": "disagree", "b": "disagree", "c": "agree", "d": "agree", "e": "agree"}
    worse, better = oracle.compare(before, after, sorted(after))
    assert worse == ["a: agree -> disagree", "b: refused -> disagree"]
    assert better == ["c: disagree -> agree", "d: skipped -> agree"]


def test_an_agreement_that_becomes_a_refusal_fails():
    worse, _ = oracle.compare({"q": "agree"}, {"q": "refused"}, ["q"])
    assert worse == ["q: agree -> refused"]


def test_benchmark_mismatches_fail():
    # The benchmarks' stages: a query that newly stops at oracle A disagrees.
    worse, better = oracle.compare(
        {"q1": "lift", "q2": "oracle A"}, {"q1": "oracle A", "q2": "agree"}, ["q1", "q2"]
    )
    assert worse == ["q1: lift -> oracle A"]
    assert better == ["q2: oracle A -> agree"]


def test_the_sample_is_stable():
    known = {
        ("x.test", 1, "s"): "agree",
        ("y.test", 1, "s"): "refused",
        ("z.test", 2, "t"): "disagree",
    }
    assert oracle.sample(known, 0) == oracle.sample(known, 0)
    assert set(oracle.sample(known, 0)) == {"x.test", "z.test"}
    assert len(oracle.sample(known, 1)) == 1


def test_a_file_the_ledger_compared_and_this_run_skipped_fails():
    skips = {"a.test": "harness: the replay process crashed", "b.test": "require: tpch"}
    assert oracle.newly_skipped(skips, {"b.test": "require: tpch"}) == [
        "a.test: compared -> skipped (harness: the replay process crashed)"
    ]


def test_the_shards_cover_the_files_once():
    files = [f"{i}.test" for i in range(10)]
    shards = [oracle.shard(files, f"{i}/3") for i in (1, 2, 3)]
    assert sorted(sum(shards, [])) == sorted(files)
    assert oracle.shard(files, None) == files
