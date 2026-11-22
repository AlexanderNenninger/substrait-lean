"""`repeat('', n)` is `''` at once for every `n`, however large (#2278): the
checker used to loop `n` times, so `n = 2^63 - 1` never returned."""

import json

import ibis

from sverify.counterexample import evaluate
from sverify.engine import plan_json_over


def test_repeating_the_empty_string_a_huge_number_of_times_returns_at_once() -> None:
    t = ibis.table({"name": "string", "qty": "int64"}, name="t")
    schemas = {"t": t.schema()}
    plan = json.loads(plan_json_over(schemas, t.select(x=t.name.repeat(t.qty))))
    rows = [("", 2**63 - 1), ("", 2**32), ("a_b", 3)]
    out = evaluate(plan, {"t": rows})
    assert [r[0] for r in out] == ["", "", "a_ba_ba_b"]
