"""Reports and exceptions in the user's terms (#687), and hints that carry
code a proof has checked (#688): one test per message the API critique
quotes (`api-critique/REPORT.md` §1, #686,
https://github.com/AlexanderNenninger/substrait-lean/blob/f89f83d2b3fc71848f9d5de8547475b99523b9b5/api-critique/REPORT.md),
and a test that pastes each hint's code back and verifies again."""

import datetime as dt
import os
import re
import time

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import _checker, engine, routes
from sverify.errors import CheckerVersionError, VerificationError


def _needed(report):
    """The labels of `report.needs` per input table."""
    out: dict[str, list[str]] = {}
    for n in report.needs:
        out.setdefault(n.table, []).append(n.label)
    return out


ITEMS = ibis.table(
    {"sku": "int64", "price": "int64", "cost": "int64", "qty": "int64"}, name="items"
)
CLICKS = ibis.table(
    {"user_id": "int64", "ts": "timestamp", "page": "string", "seq": "int64"}, name="clicks"
)
PAYMENTS = ibis.table(
    {"txn_id": "int64", "card": "string", "amount": "int64", "ts": "timestamp"}, name="payments"
)
ORDERS = ibis.table(
    {"order_id": "int64", "customer_id": "int64", "amount": "float64"}, name="orders"
)
CUSTOMERS = ibis.table({"customer_id": "int64", "name": "string"}, name="customers")
READINGS = ibis.table({"sensor": "string", "temp_c": "float64"}, name="readings")


def margins(items: ibis.Table) -> ibis.Table:
    return items.select(
        items.sku,
        margin_pct=(items.price - items.cost) * 100 // items.price,
        revenue=items.price * items.qty,
    )


def sessionize(t: ibis.Table) -> ibis.Table:
    # A BIGINT step: a timestamp lies in 0001 to 9999 by its type (D32), so
    # `ts - lag(ts)` cannot overflow, and `seq - lag(seq)` can.
    prev = t.seq.lag().over(ibis.window(group_by=t.user_id, order_by=t.ts))
    return t.mutate(gap=t.seq - prev)


def double_charges(p: ibis.Table) -> ibis.Table:
    b = p.view()
    j = p.join(b, (p.card == b.card) & (p.ts < b.ts) & (b.ts <= p.ts + ibis.interval(minutes=5)))
    return j.select(first_txn=p.txn_id, dup_txn=b.txn_id, first_ts=p.ts, dup_ts=b.ts)


# -- 1.1: expressions the user wrote -------------------------------------------


def test_a_floor_division_is_one_issue_as_written() -> None:
    """Ibis's `//` is the reference's floor division, `(a + 1) // b - 1` and
    so on: its branches and sub-expressions fold into the expression."""
    report = sv.verify(margins(ITEMS), requires={"items": [_.price > 0]}, on_inferred="off")
    shown = [str(i) for i in report.errors]
    assert shown == [
        "overflow: (price - cost) * 100 // price",
        "overflow: price * qty",
    ], shown
    assert "+ 1" not in report.details() and "- 1)" not in report.details()


def test_a_window_value_is_named_not_numbered() -> None:
    report = sv.verify(sessionize(CLICKS), on_inferred="off")
    assert [str(i) for i in report.errors] == ["overflow: seq - lag(seq)"]
    assert "$" not in report.details()


def test_a_sum_in_sql_is_named_by_its_measure() -> None:
    sql = """
    WITH per AS (SELECT customer_id, sum(amount) AS revenue FROM orders GROUP BY customer_id)
    SELECT customer_id, revenue, rank() OVER (ORDER BY revenue DESC) AS r FROM per
    """
    report = sv.verify(sql, tables={"orders": ORDERS}, requires={"orders": ["amount >= 0"]})
    assert "assumes: sum(amount) stays finite on finite inputs" in report.details()
    assert "$" not in report.details()


def test_aggregates_over_one_column_are_named_together() -> None:
    expr = READINGS.group_by("sensor").aggregate(
        m=READINGS.temp_c.mean(), s=READINGS.temp_c.std(), lo=READINGS.temp_c.min()
    )
    report = sv.verify(expr, requires={"readings": [_.temp_c.between(-90, 60)]})
    assert "assumes: mean(temp_c) or std(temp_c) stays finite on finite inputs" in report.details()


def test_a_large_double_constant_reads_as_python_writes_it() -> None:
    """#885 finding 1d: `1e302` reads as `1e+302`, not its 303 digits."""
    t = ibis.table({"value": "float64"}, name="s")
    text = sv.verify(t.select(scaled=t.value * 1e302)).details()
    assert "value * 1e+302 stays finite on finite inputs" in text
    assert "000000000" not in text
    # #1997: every double constant, not only the long ones.
    text = sv.verify(t.select(scaled=t.value * 3 + 1)).details()
    assert "value * 3.0 + 1.0 stays finite" in text and ".000000" not in text
    # The plan's literals read exactly, also where `%f` rounds them.
    text = sv.verify(t.select(scaled=t.value * 1e-7 + 0.1234567)).details()
    assert "value * 1e-07 + 0.1234567 stays finite" in text
    text = sv.verify(t.select(scaled=t.value * 3.0000001)).details()
    assert "value * 3.0000001 stays finite" in text
    # Two literals that `%f` prints alike stay as Lean rounded them: `3.0`
    # would read as exact.
    text = sv.verify(t.select(scaled=t.value * 3.0000001 + 3.0)).details()
    assert "value * 3.000000 + 3.000000 stays finite" in text
    from sverify._user_text import pretty

    # Without the plan's literal, `.000000` proves integral only from 2^33 on.
    assert pretty("(y *. 3.000000d)") == "y * 3.000000"
    assert pretty("(y *. 8589934592.000000d)") == "y * 8589934592.0"
    # A decimal literal keeps its digits, which are its scale.
    assert (
        pretty(
            "(x < 0.000000) or (y *. 2.000000d)", doubles={"0.000000": "1e-07", "2.000000": "2.0"}
        )
        == "(x < 0.000000) or (y * 2.0)"
    )


def test_a_decimal_cast_reads_as_the_cast() -> None:
    report = sv.verify(
        "SELECT order_id, amount::DECIMAL(10,2) AS amt FROM orders", tables={"orders": ORDERS}
    )
    assert [str(i) for i in report.errors] == [
        "cast out of range: CAST(amount AS DECIMAL(10, 2))",
        "overflow: CAST(amount AS DECIMAL(10, 2))",
    ]
    assert "TO_DECIMAL" not in report.details()


def test_an_interval_reads_as_written() -> None:
    # A computed timestamp may leave 0001 to 9999 (D32), which its truncation
    # needs a bound for.
    later = PAYMENTS.ts + ibis.interval(minutes=5)
    report = sv.verify(PAYMENTS.select(m=later.truncate("M")))
    assert "inferred from `DATE_TRUNC_month((ts + ibis.interval(minutes=5)))`" in report.details()
    assert "300000000" not in report.details()


def test_conditions_keep_their_short_values() -> None:
    report = sv.verify(
        double_charges(PAYMENTS),
        requires={"payments": [_.ts.notnull(), _.ts < dt.datetime(9999, 1, 1)]},
        ensures=[(_.dup_ts - _.first_ts) <= ibis.interval(seconds=300)],
    )
    text = report.details()
    assert "requires payments: (_.ts < datetime(9999, 1, 1))" in text
    assert "ensures ((_.dup_ts - _.first_ts) <= ibis.interval(seconds=300)): proved" in text
    assert "datetime.datetime" not in text and "<scalar" not in text


# -- 1.3, 1.4: the verdict first, the exception short ---------------------------


def test_a_report_starts_with_its_verdict(monkeypatch: pytest.MonkeyPatch) -> None:
    # CI's checker builds without `check_generated`, for speed; a released one checks.
    monkeypatch.setattr(_checker, "_generated_proofs", lambda path: True)
    proved = sv.verify(ITEMS.select(x=ITEMS.price), ensures=[_.x.isnull() | _.x.notnull()])
    assert str(proved).splitlines()[0] == "proved"
    report = sv.verify(margins(ITEMS), ensures=[_.revenue >= 0], counterexamples=0)
    assert report.details().splitlines()[0] == (
        "NOT proved: 1 of 1 postcondition not proved, 2 possible runtime errors, "
        "1 precondition needed"
    )
    assert report._repr_markdown_().startswith(f"**{report._summary}**")


def test_the_exception_counts_then_lists_one_line_per_finding() -> None:
    t = sv.transform(ensures=[_.revenue >= 0])(margins)
    with pytest.raises(VerificationError) as e:
        t(ITEMS)
    lines = str(e.value).splitlines()
    assert lines[0] == (
        "1 of 1 postcondition not proved, 2 possible runtime errors, 1 precondition needed "
        "(e.report has the details)"
    )
    assert [line.split(":")[0].strip() for line in lines[1:] if not line.startswith("    ")] == [
        "needs",
        "not proved",
        "may fail",
        "may fail",
    ]
    assert "known about the output" not in str(e.value)
    assert "known about the output" in e.value.report.details()
    assert all(len(line) < 400 for line in lines)


def test_the_needs_line_alone_names_on_inferred() -> None:
    t = sv.transform(ensures=[_.revenue >= 0])(margins)
    with pytest.raises(VerificationError) as e:
        t(ITEMS)
    named = [line for line in str(e.value).splitlines() if "on_inferred" in line]
    assert len(named) == 1 and named[0].lstrip().startswith("needs:")
    assert "on_inferred='warn' assumes it instead" in named[0]


def test_the_and_or_hint_appears_once_and_only_for_the_users_and() -> None:
    """The producer writes `//` with an AND; that AND is not the user's."""
    report = sv.verify(margins(ITEMS), counterexamples=0)
    assert "AND or OR" not in report.details()
    t = ibis.table({"qty": "int64", "total": "int64"}, name="t")
    report = sv.verify(t.filter((t.qty != 0) & (t.total // t.qty > 1)))
    assert [h for h in report._hints if "AND or OR" in h] == [
        "`total // qty` is inside an AND or OR you wrote (`&` or `|`), and DuckDB and Polars "
        "evaluate both operands on every row, so a guard in the other operand does not keep it "
        "from raising. Guard the operation itself with `ibis.cases((_.qty != 0, _.total // "
        "_.qty))` (a boolean CASE is evaluated whole, as AND and OR are), or state the guard "
        "as a precondition"
    ]


# -- 1.5: route lines ------------------------------------------------------------


def test_route_lines_lead_with_the_class_in_plain_words() -> None:
    con = sv.connect()
    con.put("t", pa.table({"x": [-7, 7]}))
    t = con.table("t")
    report = sv.verify(t.select(q=t.x // 2), requires={"t": [_.x.between(-100, 100)]})
    report.run(con, "polars")
    report.run(con, "duckdb")
    text = report.details()
    assert "route on polars: shim (integer division rewritten to truncate); evidence" in text
    assert "route on duckdb: exact; evidence" in text
    for internal in ("Lowering", "lower_correct", "polars_engine", "Rel.eval", "Lean"):
        assert internal not in text
    assert "DuckDB lowering" in report.routes["duckdb"].reason


def test_an_observed_route_rounds_its_bound() -> None:
    obs = sv.observation.Observation(floats=sv.within(abs=1.998402245904532e-07))
    assert routes.observed_text(obs) == "doubles within abs=2e-07"


# -- 1.6, 1.7: one spelling, no Lean as the subject ---------------------------


def test_the_ties_note_names_functions_in_the_users_language() -> None:
    sql = "SELECT customer_id, row_number() OVER (ORDER BY amount DESC) AS r FROM orders"
    report = sv.verify(sql, tables={"orders": ORDERS})
    note = next(line for line in report.details().splitlines() if line.startswith("note:"))
    assert "FIRST, LAST, STRING_AGG, MODE, ARG_MIN or ARG_MAX" in note
    assert "group_concat()" not in note and "D24" not in note
    w = ibis.window(order_by=ORDERS.amount)
    report = sv.verify(ORDERS.mutate(r=ibis.row_number().over(w)))
    note = next(line for line in report.details().splitlines() if line.startswith("note:"))
    assert "first(), last(), group_concat()" in note and "STRING_AGG" not in note


def test_no_message_makes_lean_its_subject() -> None:
    report = sv.verify(
        ORDERS.select(x=ORDERS.amount), ensures=[_.x.isnull() | (_.x == _.x)], counterexamples=0
    )
    for c in report.ensures:
        assert not c.why.startswith("Lean")
    c = sv.contracts.CheckedCondition("(_.x > 1)", False, "TRUE or UNKNOWN")
    assert c.why == "the checker only knows it is TRUE or UNKNOWN"


# -- 1.8: raw exceptions ----------------------------------------------------------


def test_approx_checks_its_condition_when_called() -> None:
    with pytest.raises(TypeError, match=r"sv.approx\(\(_.lo <= _.mean_t\)\): it compares two"):
        sv.approx(_.lo <= _.mean_t)
    assert sv.approx(_.mean_t >= -90).rel == 1e-6


def test_an_ibis_condition_that_does_not_type_check_is_named_in_the_error() -> None:
    expr = double_charges(PAYMENTS)
    cond = _.dup_ts - _.first_ts <= ibis.interval(minutes=5)
    with pytest.raises(sv.errors.ConditionError) as e:
        sv.verify(expr, ensures=[_.first_ts.notnull(), cond])
    (label,) = e.value.errors
    assert label == "((_.dup_ts - _.first_ts) <= ibis.interval(minutes=5))"
    assert "does not type-check: " in str(e.value.errors[label])


def test_an_ibis_condition_on_a_missing_column_is_named_in_the_error() -> None:
    expr = double_charges(PAYMENTS)
    with pytest.raises(sv.errors.ConditionError) as e:
        sv.verify(expr, ensures=[_.zz > 1])
    assert list(e.value.errors) == ["(_.zz > 1)"]
    assert "no column 'zz'" in str(e.value.errors["(_.zz > 1)"])


def test_the_keys_of_condition_error_are_spelt_as_checked_condition_label() -> None:
    expr = double_charges(PAYMENTS)
    r = sv.verify(expr, ensures=[_.first_ts.notnull()])
    assert r.ensures[0].label == "_.first_ts.notnull()"
    with pytest.raises(sv.errors.ConditionError) as e:
        sv.verify(expr, ensures=[_.first_ts.notnull(), _.zz.notnull()])
    assert list(e.value.errors) == ["_.zz.notnull()"]


@pytest.mark.parametrize(
    ("kwargs", "condition", "reason"),
    [
        ({"ensures": ["x > 0", "zz > 1"]}, "zz > 1", "Column 'zz' could not be resolved"),
        ({"ensures": ["x >"]}, "x >", "cannot parse the SQL"),
        ({"requires": {"t": ["zz > 1"]}, "ensures": ["x > 0"]}, "zz > 1", "zz"),
        ({"ensures": ["md5(x) > 1"]}, "md5(x) > 1", "not supported"),
    ],
)
def test_a_condition_verify_cannot_read_names_itself(kwargs, condition, reason) -> None:
    """#699: an unknown column, SQL that does not parse and a construct the lift
    does not read each raise `ConditionError`, keyed by the condition; the
    query itself reads fine."""
    tables = {"t": {"x": "BIGINT"}}
    assert sv.verify("select x from t", tables=tables).verdict is sv.Verdict.PROVED
    with pytest.raises(sv.errors.ConditionError) as e:
        sv.verify("select x from t", tables=tables, **kwargs)
    assert list(e.value.errors) == [condition]
    assert reason in str(e.value.errors[condition])
    assert isinstance(e.value, sv.errors.UnsupportedError)
    assert "the query is not refused" in str(e.value)


def test_every_unreadable_condition_is_named_at_once() -> None:
    with pytest.raises(sv.errors.ConditionError) as e:
        sv.verify(
            "select x from t",
            tables={"t": {"x": "BIGINT"}},
            requires={"t": ["qq > 0"]},
            ensures=["x > 0", "zz > 1", "md5(x) > 1"],
        )
    assert list(e.value.errors) == ["qq > 0", "zz > 1", "md5(x) > 1"]


def test_a_stale_checker_build_says_so(tmp_path, monkeypatch) -> None:
    binary = tmp_path / ".lake" / "build" / "bin" / "substrait-check"
    binary.parent.mkdir(parents=True)
    binary.write_text("")
    src = tmp_path / "SubstraitLean" / "Parse.lean"
    src.parent.mkdir()
    src.write_text("")
    old = time.time() - 3600
    os.utime(binary, (old, old))
    assert "older than this sverify" in (engine.stale_checker(binary) or "")
    monkeypatch.setattr(engine, "checker_path", lambda: binary)
    err = engine.checker_failed("--contract", "error: division_type = [FLOOR] is not supported")
    assert isinstance(err, CheckerVersionError)
    assert "lake build substrait-check" in str(err) and "FLOOR" in str(err)
    os.utime(binary, None)
    assert engine.stale_checker(binary) is None
    assert isinstance(engine.checker_failed("--contract", "boom"), ValueError)


# -- #688: every hint carries code a proof checked -------------------------------


def test_a_key_lost_through_a_self_join_is_not_advice_to_declare_it() -> None:
    report = sv.verify(
        double_charges(PAYMENTS),
        requires={"payments": [sv.unique("txn_id"), _.ts < dt.datetime(9999, 1, 1)]},
        ensures=[sv.unique("dup_txn")],
    )
    (c,) = report.unproved
    assert c.why == (
        "the preconditions do not make it a key: `dup_txn` comes from payments.txn_id, whose "
        "key unique(txn_id) is lost on the way: a join, a union or an UNNEST can repeat a value"
    )
    assert "sv.unique('dup_txn')" not in report.details()


def test_a_key_lost_through_a_join_names_the_input_that_has_it() -> None:
    sql = (
        # Each order repeats its customer: the key of customers is lost.
        "SELECT c.customer_id, c.name FROM orders o JOIN customers c "
        "ON c.customer_id = o.customer_id"
    )
    report = sv.verify(
        sql,
        tables={"orders": ORDERS, "customers": CUSTOMERS},
        requires={"customers": [sv.unique("customer_id")]},
        ensures=[sv.unique("customer_id")],
    )
    (c,) = report.unproved
    assert (
        "`customer_id` comes from customers.customer_id, whose key unique(customer_id) is lost"
        in c.why
    )


def test_a_key_hint_is_declared_only_where_it_proves_the_key() -> None:
    report = sv.verify(ORDERS.select("order_id", "amount"), ensures=[sv.unique("order_id")])
    (c,) = report.unproved
    assert c.why.endswith("declare `sv.unique('order_id')` in the requires of 'orders'")
    again = sv.verify(
        ORDERS.select("order_id", "amount"),
        requires={"orders": [sv.unique("order_id")]},
        ensures=[sv.unique("order_id")],
    )
    assert again.verdict == sv.Verdict.PROVED


def test_a_null_output_is_allowed_not_declared_not_null() -> None:
    expr = READINGS.group_by("sensor").aggregate(sd_t=READINGS.temp_c.std())
    req = {"readings": [_.temp_c.between(-90, 60), _.sensor.notnull()]}
    report = sv.verify(expr, requires=req, ensures=[_.sd_t >= 0], counterexamples=0)
    (c,) = report.unproved
    assert "NOT NULL in the schema" not in c.why
    m = re.search(r"state `(.*)`$", c.why)
    assert m is not None
    code = m[1]
    assert code == "((_.sd_t >= 0) | _.sd_t.isnull())"
    assert (
        sv.verify(expr, requires=req, ensures=[eval(code)]).verdict == sv.Verdict.PROVED_WITH_CHECKS
    )


def test_the_and_or_guard_proves_when_pasted() -> None:
    t = ibis.table({"qty": "int64", "total": "int64"}, name="t")
    req = {"t": [_.total.between(0, 1000)]}
    per = ibis.cases((t.qty != 0, t.total // t.qty))
    guarded = t.filter((t.qty != 0) & (per > 1))  # type: ignore[operator]
    report = sv.verify(guarded, requires=req, on_inferred="error")
    assert not any(i.kind == "division by zero" for i in report.errors)
    assert not _needed(report)


def test_the_window_hint_bounds_the_column_it_reads() -> None:
    report = sv.verify(sessionize(CLICKS), on_inferred="off")
    (issue,) = report.errors
    assert issue.hint is not None
    assert issue.hint.startswith("bound the columns it reads: state `(_.seq >= ")
    assert "window function" not in issue.hint


def test_the_ties_hint_names_a_key_that_determines_the_result() -> None:
    w = ibis.window(group_by=ORDERS.customer_id, order_by=ORDERS.amount)
    expr = ORDERS.mutate(r=ibis.row_number().over(w))
    report = sv.verify(expr)
    assert report.ties == {"orders": ["unique(customer_id, amount)"]}
    assert "declare `unique(customer_id, amount)` in the requires of 'orders'" in report.details()
    again = sv.verify(expr, requires={"orders": [sv.unique("customer_id", "amount")]})
    assert again.deterministic


HINTED = [
    pytest.param(lambda: (margins(ITEMS), {"items": [_.price > 0]}), id="margins"),
    pytest.param(lambda: (sessionize(CLICKS), {}), id="window"),
    pytest.param(
        lambda: (ITEMS.select(x=ITEMS.price * ITEMS.qty + ITEMS.cost), {"items": []}),
        id="product",
    ),
    pytest.param(
        lambda: (ITEMS.select(x=ITEMS.price + 1), {"items": [_.price >= 0]}), id="increment"
    ),
]

_CODE = re.compile(r"((?:`[^`]+`(?:, )?)+) in the requires of '(\w+)'")


def _pasted(hint: str) -> dict[str, list]:
    """The conditions a hint proposes, read back as a user pastes them."""
    found: dict[str, list] = {}
    for codes, table in _CODE.findall(hint):
        for code in re.findall(r"`([^`]+)`", codes):
            env = {"_": _, "datetime": dt.datetime, "date": dt.date, "sv": sv, "ibis": ibis}
            found.setdefault(table, []).append(eval(code, env))
    return found


@pytest.mark.parametrize("case", HINTED)
def test_every_hint_removes_its_issue_when_pasted(case) -> None:
    """#688: the code each hint proposes, pasted into `requires`, makes its
    issue go away."""
    expr, requires = case()
    report = sv.verify(expr, requires=requires, on_inferred="off", counterexamples=0)
    hinted = [(i, i.hint) for i in report.errors if i.hint and "in the requires of" in i.hint]
    assert hinted, report
    for issue, hint in hinted:
        pasted = {t: list(cs) for t, cs in requires.items()}
        for t, cs in _pasted(hint).items():
            pasted.setdefault(t, []).extend(cs)
        again = sv.verify(expr, requires=pasted, on_inferred="off", counterexamples=0)
        assert (issue.kind, str(issue)) not in {(i.kind, str(i)) for i in again.errors}, issue.hint


def test_a_report_names_the_parameter_not_the_upstream_node():
    # `downstream(orders)` is fed by the transform `latest`: the report says
    # `requires orders`, the name in its own `requires`, not `requires latest` (#1485).
    @sv.transform(requires={"rows": [_.amount >= 0]}, ensures=[_.total >= 0])
    def latest(rows):
        return rows.group_by("id").aggregate(total=rows.amount.sum())

    @sv.transform(requires={"orders": [_.total >= 0]}, ensures=[])
    def downstream(orders):
        return orders.select("id", dbl=orders.total * orders.total)

    raw = ibis.table({"id": "int64", "amount": "int64"}, name="raw")
    with pytest.raises(VerificationError) as caught:
        downstream(latest(raw))
    text = caught.value.report.details()
    assert "requires orders: (_.total >= 0)" in text
    assert "requires latest" not in text


def test_str_is_the_plain_contract_and_details_the_full_text():
    # `print(report)` says what holds, what each run checks and what is not
    # proved; the semantics and the evidence per engine are in `details()` (#1485).
    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 10**9, sv.unique("id")]},
        ensures=[_.total >= 0, _.total < 10],
        on_unproved="warn",
    )
    def totals(orders):
        return orders.group_by("id").aggregate(total=orders.amount.sum())

    raw = ibis.table({"id": "int64", "amount": "int64"}, name="raw")
    with pytest.warns(sv.errors.UnprovedWarning):
        totals(raw)
    report = totals.report
    assert report is not None
    lines = str(report).splitlines()
    assert lines[0].startswith("NOT proved")
    assert "The output guarantees:" in lines and "  total ≥ 0" in lines
    assert "Each run checks on the data:" in lines and "  orders: no two rows share id" in lines
    assert "Not proved:" in lines and any("total < 10" in line for line in lines)
    assert not any(line.startswith(("semantics:", "evidence:", "route on")) for line in lines)
    full = report.details().splitlines()
    assert "semantics: reference" in full
    assert "requires orders: unique(id)" in full
