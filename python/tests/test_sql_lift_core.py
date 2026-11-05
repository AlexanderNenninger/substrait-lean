"""DuckDB SQL through sverify's own lift (`sverify.sql_lift`, #239):
`sv.sql(query, dialect="duckdb", semantics=...)`, its two profiles, its
refusals, and oracles A and C (`sverify_dev.lift`). This file: logic,
comparisons, arithmetic, numeric functions and NULLs, and `sv.sql` itself;
the other areas are in `test_sql_lift_<area>.py`."""

import json
from typing import Any

import ibis
import pytest

import sverify as sv
from _pipelines import arrow_table as table
from _pipelines import rows
from _sql_lift import CUSTOMER_ROWS, CUSTOMERS, ORDER_ROWS, ORDERS, SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.engines import Unsupported
from sverify.errors import VerificationError
from sverify.io import StaticSource
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import DUCKDB, REFERENCE, lift
from sverify_dev import catalogue
from sverify_dev.lift import check, score

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    "SELECT id, amount * 2 AS a2, qty + 1 AS q1, -amount AS neg FROM orders WHERE amount > 1",
    "SELECT id, amount / 2 AS half, amount // 2 AS q, amount % 3 AS m FROM orders",
    "SELECT id, amount / qty AS r, price / 2 AS p FROM orders",
    "SELECT id FROM orders WHERE price > 1.5 AND qty BETWEEN 2 AND 4 OR customer IS NULL",
    "SELECT id FROM orders WHERE NOT (customer IN ('ada', 'cy')) AND customer IS NOT NULL",
    "SELECT id, CASE WHEN qty > 3 THEN 'big' WHEN qty IS NULL THEN NULL ELSE 'small' END AS k,"
    " CASE qty WHEN 3 THEN 1.5 ELSE 2 END AS c, coalesce(qty, 0) AS z FROM orders",
    "SELECT id, cost * cost AS c2, cost + 1 AS c1, cost * 2 AS cd, cost > 3.5 AS big FROM orders",
    "SELECT 1 + 1 AS two, 7 // 2 AS q, 1 // 1 AS one",
    # IS [NOT] TRUE/FALSE, never NULL: COALESCE of the test (#177).
    "SELECT id, (qty > 2) IS TRUE AS t, (qty > 2) IS NOT TRUE AS nt,"
    " (price > 1.5) IS FALSE AS f, (price > 1.5) IS NOT FALSE AS nf FROM orders",
    # Numbers: DuckDB's `power` and elementary functions are of doubles; its
    # `greatest`/`least` leave NULLs out; `log(x)` is base 10.
    "SELECT id, power(amount, 2) AS p, amount ** 2 AS q, abs(qty) AS a, abs(price) AS af,"
    " sign(price) AS s, isnan(price) AS n FROM orders",
    "SELECT id, round(price) AS r, round(price, 1) AS r1, floor(price) AS f, ceil(price) AS c,"
    " floor(qty) AS fq, round(qty) AS rq FROM orders",
    "SELECT id, greatest(amount, qty, 4) AS g, least(amount, qty) AS l, nullif(amount, 0) AS z,"
    " qty IS DISTINCT FROM 3 AS d, qty IS NOT DISTINCT FROM NULL AS nn FROM orders",
    "SELECT id, sqrt(amount + 1) AS s, ln(amount + 1) AS l, log(amount + 1) AS lg,"
    " log2(amount + 1) AS l2, log(3, amount + 1) AS lb, exp(qty) AS e, sin(price) AS si"
    " FROM orders",
    "SELECT id, amount / 0 AS inf, price / 0 AS p FROM orders",
    # The written plan's division of two double literals (#96, fixed with #335).
    "SELECT 7 / 2 AS h",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "reference").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


def test_the_profiles_differ_only_in_what_functions_do():
    fields = DUCKDB.__dataclass_fields__
    assert {f for f in fields if getattr(DUCKDB, f) != getattr(REFERENCE, f)} == {
        "name",
        "float_to_int",
        "decimal_to_int",
        "domain_error",
        "log_zero",
        "corr_degenerate",
    }


def options(plan: dict, name: str) -> list[list[dict]]:
    """The options of each call of `name` in `plan`."""
    anchors = {
        e["extensionFunction"]["functionAnchor"]
        for e in plan["extensions"]
        if e["extensionFunction"]["name"] == name
    }
    found = []

    def walk(j):
        if isinstance(j, dict):
            f = j.get("scalarFunction")
            if f is not None and f["functionReference"] in anchors:
                found.append(f.get("options", []))
            for v in j.values():
                walk(v)
        elif isinstance(j, list):
            for v in j:
                walk(v)

    walk(plan)
    return found


def test_division_states_its_meaning():
    query = "SELECT amount / qty AS r, amount // qty AS q FROM orders"
    duck, ref = (lift(query, SCHEMAS, s).plan for s in ("duckdb", "reference"))
    zero = {"name": "on_division_by_zero"}
    # `/` divides doubles: by zero DuckDB gives inf, the reference raises.
    assert options(duck, "divide")[0] == [{**zero, "preference": ["IEEE"]}]
    assert options(ref, "divide")[0] == [{**zero, "preference": ["ERROR"]}]
    # `//` divides integers, and raises by zero in both.
    for plan in (duck, ref):
        assert {**zero, "preference": ["ERROR"]} in options(plan, "divide")[1]
    assert lift(query, SCHEMAS).schema == ibis.schema({"r": "float64", "q": "int64"})


def test_constants_compared_with_a_narrow_column_take_its_type():
    """`v >= -127` on a TINYINT compares `v` itself, as DuckDB binds it, so
    a contract's precondition bounds the column (#616); a constant that does
    not fit casts the column."""
    plan = lift(
        "SELECT * FROM t WHERE v >= -127 AND v < 300", {"t": ibis.schema({"v": "int8"})}
    ).plan
    cond = plan["relations"][0]["root"]["input"]["filter"]["condition"]
    fits, wide = (
        a["value"]["scalarFunction"]["arguments"] for a in cond["scalarFunction"]["arguments"]
    )
    assert fits[0]["value"] == {
        "selection": {"directReference": {"structField": {"field": 0}}, "rootReference": {}}
    }
    assert fits[1]["value"] == {"literal": {"i8": -127}}
    assert "cast" in wide[0]["value"] and wide[1]["value"] == {"literal": {"i32": 300}}


def test_duckdb_types_literals_and_decimals_its_own_way():
    schema = lift(
        "SELECT 1 AS i, 3000000000 AS b, 1.5 AS d, 1e3 AS f, qty + 1 AS q,"
        " cost * cost AS c2, cost + cost AS c1 FROM orders",
        SCHEMAS,
    ).schema
    assert schema == ibis.schema(
        {
            "i": "int32",
            "b": "int64",
            "d": "decimal(2, 1)",
            "f": "float64",
            "q": "int32",
            # DuckDB: a product of two decimals of up to 18 digits has 18.
            "c2": "decimal(18, 4)",
            "c1": "decimal(16, 2)",
        }
    )


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT my_udf(id) FROM orders", "unknown function my_udf"),
        # Literals SQLGlot reads otherwise.
        ("SELECT 1__2", "underscore not between two digits"),
        ("SELECT 1._5", "underscore not between two digits"),
        ("SELECT nope FROM orders", "cannot resolve"),
        ("SELECT 170141183460469231731687303715884105727 AS h", "HUGEINT"),
        ("SELEC id FROM orders", "cannot parse"),
        # `IN` over a map, not a list of values (#626): it was FALSE.
        ("SELECT 'my_key' IN map(['my_key'], ['my_value']) AS res", "a list or map"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


# --------------------------------------------------------------------------
# sv.sql(..., dialect="duckdb")


def sources():
    orders = StaticSource(table(ORDERS, ORDER_ROWS), version=1, name="orders")
    customers = StaticSource(table(CUSTOMERS, CUSTOMER_ROWS), version=1, name="customers")
    return orders, customers


@sv.transform(
    requires={"orders": ["amount >= 0", "qty > 0"]},
    ensures=["total >= 0", "n >= 1", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, sum(amount) AS total, count(*) AS n, avg(qty) AS avg_qty"
        " FROM orders GROUP BY customer",
        dialect="duckdb",
        orders=orders,
    )


def test_a_duckdb_sql_node_is_proved_and_runs_on_duckdb():
    with_qty = [r for r in ORDER_ROWS if r[3] is not None]
    orders = StaticSource(table(ORDERS, with_qty), version=1, name="orders")
    node = per_customer(orders)
    node.refresh(engine="duckdb")
    assert per_customer.report is not None and per_customer.report.proved
    got = sorted(rows(node), key=repr)
    assert got == sorted([("ada", 5, 2, 3.5), ("cy", 9, 1, 2.0), (None, 2, 1, 7.0)], key=repr)


def test_a_duckdb_sql_step_chains():
    orders, customers = sources()
    step = sv.sql(
        "SELECT o.id, c.region FROM orders o JOIN customers c ON c.name = o.customer",
        dialect="duckdb",
        semantics="reference",
    )
    assert step.dialect == "duckdb" and step.semantics == "reference"
    node = orders.pipe(step, customers=customers)
    node.refresh(engine="duckdb")
    assert sorted(rows(node)) == [(1, "eu"), (2, "us"), (3, "eu")]


def test_an_unproved_ensures_names_the_condition():
    @sv.transform(ensures=["half > 0"])
    def halves(orders):
        return sv.sql("SELECT amount / 2 AS half FROM orders", dialect="duckdb", orders=orders)

    orders, _ = sources()
    with pytest.raises(VerificationError, match="half > 0"):
        halves(orders)


def test_the_semantics_changes_what_the_contract_can_prove():
    # DuckDB's `/` by zero is inf, and `inf / inf` NaN, so neither is an error
    # there: the lift's `CASE` gives the NaN, and `verify` sees that it guards
    # the division (#702). The reference raises on both (#257), which `verify`
    # reports. An overflow to `±inf` is the reference's precondition only
    # (#575): DuckDB's semantics allows it.
    t = ibis.table({"a": "float64", "b": "float64"}, name="t")
    duck = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", semantics="duckdb", t=t)
    ref = sv.sql("SELECT a / b AS ratio FROM t", dialect="duckdb", t=t)
    assert [i.kind for i in sv.verify(duck, on_inferred="off").issues] == []
    assert "domain error" in [i.kind for i in sv.verify(ref, on_inferred="off").issues]
    assert "overflow to infinity" in [i.kind for i in sv.verify(ref, on_inferred="off").issues]
    assert any("zero" in str(i) for i in sv.verify(ref, on_inferred="off").issues)


def test_sql_checks_dialect_and_semantics():
    t = ibis.table({"a": "int64"}, name="t")
    with pytest.raises(ValueError, match="dialect must be 'duckdb'"):
        sv.sql("SELECT a FROM t", dialect="postgres", t=t)
    with pytest.raises(ValueError, match="semantics must be"):
        sv.sql("SELECT a FROM t", dialect="duckdb", semantics="spark", t=t)  # type: ignore[call-overload]
    with pytest.raises(Unsupported, match="unknown function"):
        sv.sql("SELECT my_udf(a) FROM t", dialect="duckdb", t=t)


def test_sql_uses_the_reference_semantics_by_default():
    # #411: DuckDB's semantics is an explicit opt-in.
    t = ibis.table({"a": "int64"}, name="t")
    op: Any = sv.sql("SELECT a FROM t", t=t).op()
    assert (op.dialect, op.semantics) == ("duckdb", "reference")
    assert sv.sql("SELECT a FROM t").semantics == "reference"


def test_verify_states_and_takes_its_semantics():
    # A SQL transformation and SQL conditions follow `verify(semantics=...)`.
    t = ibis.table({"a": "float64", "b": "float64"}, name="t")
    sql = "SELECT a / b AS ratio FROM t"
    ref = sv.verify(sql, tables={"t": t}, on_inferred="off")
    duck = sv.verify(sql, tables={"t": t}, semantics="duckdb", on_inferred="off")
    assert (ref.semantics, duck.semantics) == ("reference", "duckdb")
    assert "semantics: reference" in str(ref).splitlines()
    assert any("zero" in str(i) for i in ref.issues)
    assert not any("zero" in str(i) for i in duck.issues)
    with pytest.raises(ValueError, match="semantics must be"):
        sv.verify(sql, tables={"t": t}, semantics="spark")  # type: ignore[arg-type]


def test_transform_takes_a_semantics():
    @sv.transform(ensures=["a IS NOT NULL OR a IS NULL"], semantics="duckdb")
    def same(t):
        return t.select("a")

    t = ibis.table({"a": "float64"}, name="t")
    assert same.semantics == "duckdb"
    same(t)
    assert same.report is not None and same.report.semantics == "duckdb"


@pytest.mark.skipif(
    not (catalogue.ROOT / "schemas.toml").is_file(),
    reason="catalogue/ of the repository is not here",
)
def test_benchmark_queries_through_the_lift():
    # The #229 score (`python -m sverify_dev.lift`), on SSB's four queries.
    results = score(["ssb"])
    assert len(results) == 4
    assert all(c.ok for c in results.values()), results


# --------------------------------------------------------------------------
# Numbers


def test_a_remainder_of_doubles_runs_with_the_reference_semantics():
    # `sverify_fmod` (#256): C's `fmod`, as DuckDB computes `%` of doubles.
    result = check(
        "SELECT id, price % 2.0 AS m, -price % 4.0 AS n FROM orders", TABLES, "reference"
    )
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize(
    "query",
    [
        # NaN by zero and of an infinity, as DuckDB computes them.
        "SELECT id, price % 0 AS z, price % qty AS m, 7.5 % price AS r FROM orders",
        "SELECT id, (price / 0) % 2 AS i, (price / 0) / (price / 0) AS n FROM orders",
        # `log` of 0 is -inf, of a negative NaN.
        "SELECT id, log(price) AS l, log(qty - 3) AS lq, sign(price) AS s, sign(qty) AS sq"
        " FROM orders",
        "SELECT id, greatest(price, -price, 0.5) AS g, least(amount, id) AS l FROM orders",
        # IEEE 754's NaN of `inf - inf`, `0 * inf`, `inf / inf` and `0 / 0`,
        # where the reference raises. The first is `types/float/nan_arithmetic.test:90`.
        "SELECT 'inf'::DOUBLE - 'inf'::DOUBLE ",
        "SELECT 'inf'::DOUBLE - 'inf'::DOUBLE AS s, '-inf'::DOUBLE + 'inf'::DOUBLE AS a,"
        " 'inf'::DOUBLE * 0.0 AS m, 0.0 * '-inf'::DOUBLE AS n,"
        " 'inf'::DOUBLE / 'inf'::DOUBLE AS d, 0.0::DOUBLE / 0.0::DOUBLE AS z",
        "SELECT id, price / 0 - price / 0 AS s, price / 0 + -price / 0 AS a,"
        " (price / 0) * (price - price) AS m, price / 0 + price / 0 AS i FROM orders",
    ],
)
def test_the_generated_lift_is_duckdbs_with_nan_and_infinities(query):
    # With DuckDB's semantics, these come from Lean's generated lift table
    # (#268), which states NaN and ±inf exactly instead of refusing them.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_digit_separators_are_read_as_duckdb_reads_them():
    result = check("SELECT 1_000 AS a, 1_000.5 AS b, 2_5e1 AS c", {})
    assert result.ok, f"{result.stage}: {result.detail}"


def test_greatest_and_least_of_many_values_check_fast():
    # #340: GREATEST/LEAST were read as a conditional that copies its first
    # argument at each step, so checking 10 of them ran for minutes. As one
    # operation per pair, 30 check at once and agree with DuckDB.
    import time

    args = ", ".join(f"amount + {i}" for i in range(30))
    query = f"SELECT id, LEAST({args}) AS lo, GREATEST({args}, qty) AS hi FROM orders"
    start = time.monotonic()
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"
    assert time.monotonic() - start < 30


def test_an_error_in_a_conjunct_that_is_never_true_may_raise():
    # DuckDB's `signed_cast_repro.test` (#317): the left conjunct overflows on
    # every row, the right one is never TRUE. `Rel.eval` gives NULL, its value
    # if nothing went wrong, and `verify` reports that the plan may raise; the
    # written plan raises, as DuckDB 2.0 does.
    import duckdb
    import pyarrow as pa

    from sverify.engine import connect, run_plan, substrait_json, written_plan

    query = (
        "SELECT 43 - MAX(ALL - 87 + col1) FROM tab2"
        " WHERE col1 * col1 * - CAST(- col2 AS SIGNED) * + - col0 * + - 77 * - col0 IS NOT NULL"
        " AND NOT + col0 BETWEEN 35 * - col2 AND NULL"
    )
    columns = {"col0": [64, 75, 46], "col1": [77, 67, 51], "col2": [40, 58, 23]}
    tab2 = pa.table({k: pa.array(v, pa.int32()) for k, v in columns.items()})
    schema = ibis.Schema.from_pyarrow(tab2.schema)
    for semantics in ("duckdb", "reference"):
        report = sv.verify(query, tables={"tab2": schema}, semantics=semantics, counterexamples=0)
        assert any("overflow" in str(i) for i in report.issues), report
    con = connect()
    con.arrow["tab2"] = tab2
    with pytest.raises(Exception, match="out of range"):
        run_plan(con, written_plan(substrait_json(con, query)))
    db = duckdb.connect()
    db.register("tab2", tab2)
    with pytest.raises(duckdb.OutOfRangeException):
        db.sql(query).fetchall()


DOUBLES = {"t": {"r": "DOUBLE", "p": "DOUBLE", "q": "BIGINT", "g": "BIGINT"}}


@pytest.mark.parametrize("op", ["+", "-", "*", "/"])
def test_duckdb_double_arithmetic_raises_nothing(op):
    """DuckDB gives NaN for `inf - inf`, `0 * inf` and `inf / inf`, and the
    lift writes that NaN as a `CASE` around the operation; `verify` sees
    that the `CASE` guards it (#702). The reference raises there."""
    sql = f"SELECT r {op} p AS y, q {op} p AS z FROM t"
    duck = sv.verify(sql, tables=DOUBLES, semantics="duckdb", counterexamples=0)
    ref = sv.verify(sql, tables=DOUBLES, counterexamples=0)
    assert duck.errors == []
    assert "domain error" in [i.kind for i in ref.errors]


def test_a_guard_on_both_sides_rules_out_the_nan():
    """A `CASE` whose condition is an `AND` leaves its `ELSE` branch with
    alternatives (#702): one side or the other is not TRUE."""
    guarded = "SELECT CASE WHEN r <> 0 AND p <> 0 THEN r * p END AS y FROM t"
    assert sv.verify(guarded, tables=DOUBLES, counterexamples=0).errors == []
    # Only `inf * 0` is ruled out; `0 * inf` still raises in the reference.
    half = (
        "SELECT CASE WHEN (r = 'inf'::DOUBLE OR r = '-inf'::DOUBLE) AND p = 0 THEN 0"
        " ELSE r * p END AS y FROM t"
    )
    assert [i.kind for i in sv.verify(half, tables=DOUBLES, counterexamples=0).errors] == [
        "domain error"
    ]


@pytest.mark.parametrize("expr", ["q * r", "r + p", "r / (p + 1)", "r * 0.125", "(r + p) / 2"])
def test_double_arithmetic_keeps_its_sign(expr):
    """Rounding keeps the sign (#441): a sum or product of non-negative
    doubles, and a quotient of one by a positive one, is at least 0."""
    report = sv.verify(
        f"SELECT {expr} AS y FROM t",
        tables=DOUBLES,
        semantics="duckdb",
        requires={"t": ["q >= 1 AND q <= 10", "r >= 0 AND r <= 10", "p >= 0 AND p <= 10"]},
        ensures=["y >= 0"],
        counterexamples=0,
    )
    assert report.proved, report


def test_a_sum_of_non_negative_products_is_non_negative():
    """A dbt `accepted_range(min_value: 0)` on revenue: `sum(qty * price)`
    of non-negative factors (#441, sverify-dbt's sample project)."""
    report = sv.verify(
        "SELECT g, sum(q * r) FILTER (WHERE p > 1) AS revenue FROM t GROUP BY g",
        tables=DOUBLES,
        semantics="duckdb",
        requires={"t": ["q >= 1 AND q <= 1000", "r >= 0 AND r <= 10000"]},
        ensures=["revenue IS NULL OR revenue >= 0"],
        counterexamples=0,
    )
    assert report.proved, report
