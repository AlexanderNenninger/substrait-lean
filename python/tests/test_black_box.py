"""Black-box functions (#325): DuckDB functions the checker treats as opaque,
with the laws their row declares (`SubstraitLean/BlackBox.lean`,
`sverify.black_box`).

Each example, `base64` (a scalar) and `entropy` (an aggregate), is lifted,
verified with its laws, written back by Lean, and run on DuckDB against
DuckDB on the SQL (oracle C). The laws are checked on random data, and the
Python table against Lean's."""

import base64
import json
import math
import subprocess

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _sql_lift import SCHEMAS, TABLES
from sverify import black_box, duckdb_engine
from sverify.engine import checker_path, connect, create_table, run_checker, run_plan, written_plan
from sverify.plan_json import Unsupported as Refused
from sverify.sql import Unsupported, to_sql
from sverify.sql.snowflake import SNOWFLAKE
from sverify.sql.spark import SPARK
from sverify.sql_lift import lift
from sverify_dev.lift import check, duckdb_result

pytestmark = pytest.mark.backend("duckdb")

#: The examples' queries: oracle C for all, oracle A (Lean's evaluator) for
#: `base64`, which Lean evaluates.
SCALAR = (
    "SELECT id, base64(encode(customer)) AS b, to_base64(encode(customer || 'é')) AS c FROM orders"
)
AGGREGATES = [
    "SELECT customer, entropy(amount) AS e, entropy(DISTINCT price) AS f FROM orders"
    " GROUP BY customer",
    "SELECT entropy(customer) AS e, entropy(price) FILTER (WHERE price > 1) AS f,"
    " entropy(day) AS g FROM orders",
    # No values: the row's `empty`, 0.0.
    "SELECT entropy(placed) AS e FROM orders WHERE id > 100",
    "SELECT base64(encode(customer)) AS b, entropy(qty) AS e FROM orders GROUP BY customer",
]


def _rows(t: pa.Table) -> list:
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def test_the_table_is_leans():
    out = subprocess.run(
        [str(checker_path()), "--black-boxes"], capture_output=True, text=True, check=True
    ).stdout
    lean = json.loads(out)
    assert [r["name"] for r in lean] == [b.name for b in black_box.TABLE]
    for i, (r, b) in enumerate(zip(lean, black_box.TABLE, strict=True)):
        assert r["anchor"] == 700 + i
        assert r["kind"] == b.kind
        assert tuple(r["args"]) == b.args
        assert r["result"] == b.result
        assert tuple(tuple(law) for law in r["laws"]) == b.laws
        assert r["raises"] == b.raises
        if b.kind == "scalar":
            assert r["strict"] == b.strict
        else:
            # A double's code: `0` is `+0.0`.
            assert r["empty"] == ({"i64": "0"} if b.empty == 0.0 else {"null": {"i64": {}}})


def test_a_black_box_is_under_sverifys_urn():
    plan = lift(SCALAR, SCHEMAS).plan
    assert plan["extensionUrns"] == [{"extensionUrnAnchor": 1, "urn": black_box.URN}]
    exts = {e["extensionFunction"]["name"]: e["extensionFunction"] for e in plan["extensions"]}
    assert exts["base64"]["extensionUrnReference"] == 1
    assert "extensionUrnReference" not in exts["str_concat"]
    written = json.loads(written_plan(json.dumps(plan)))
    ref = {e["extensionFunction"]["name"]: e["extensionFunction"] for e in written["extensions"]}
    anchors = {b.name: 700 + i for i, b in enumerate(black_box.TABLE)}
    assert ref["base64"]["functionAnchor"] == 700
    assert ref["entropy"]["functionAnchor"] == anchors["entropy"]
    assert ref["entropy"]["extensionUrnReference"] == 1
    assert "extensionUrnReference" not in ref["add"]


def test_a_scalar_black_box_through_oracles_a_and_c():
    result = check(SCALAR, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("query", AGGREGATES)
def test_written_back_it_is_duckdbs_function(query, semantics):
    # Oracle C: DuckDB on the SQL, and DuckDB on the plan Lean writes back.
    plan = json.dumps(lift(query, SCHEMAS, semantics).plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    got = duckdb_engine.run(written_plan(plan), TABLES)
    assert _rows(got) == _rows(duckdb_result(query, TABLES))


def test_lean_does_not_evaluate_entropy():
    # No evaluator: the checker refuses to print rows rather than print wrong ones.
    result = check(AGGREGATES[0], TABLES)
    assert result.stage == "oracle A" and "black box Lean does not evaluate" in result.detail


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize(
    ("query", "ensures"),
    [
        ("SELECT customer, entropy(amount) AS e FROM orders GROUP BY customer",
         ["e >= 0", "e IS NOT NULL"]),
        ("SELECT entropy(price) FILTER (WHERE price > 100) AS e FROM orders",
         ["e >= 0.0", "e IS NOT NULL"]),
        ("SELECT base64(encode(customer)) AS b FROM orders WHERE customer IS NOT NULL",
         ["b IS NOT NULL"]),
    ],
)  # fmt: skip
def test_the_laws_prove_contracts(query, ensures, semantics):
    report = sv.verify(
        query, tables=SCHEMAS, ensures=ensures, counterexamples=0, semantics=semantics
    )
    assert report.proved, report
    assert not report.errors


def test_what_the_laws_do_not_say_stays_unproved():
    # `base64` of a NULL is NULL (strict); `entropy` has no upper bound.
    for query, ensures in [
        ("SELECT base64(encode(customer)) AS b FROM orders", ["b IS NOT NULL"]),
        ("SELECT entropy(amount) AS e FROM orders", ["e <= 100.0"]),
    ]:
        report = sv.verify(query, tables=SCHEMAS, ensures=ensures, counterexamples=0)
        assert not report.proved


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT base64(customer) FROM orders", "BLOB"),
        ("SELECT base64(encode(amount)) FROM orders", "base64 of a !?int64"),
        ("SELECT entropy(amount, id) FROM orders", "takes one argument"),
        ("SELECT entropy(amount) OVER () FROM orders", "over a window"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


@pytest.mark.parametrize("dialect", [SPARK, SNOWFLAKE])
@pytest.mark.parametrize("query", [SCALAR, AGGREGATES[0]])
def test_other_dialects_refuse(query, dialect):
    plan = json.loads(written_plan(json.dumps(lift(query, SCHEMAS).plan)))
    with pytest.raises(Unsupported, match="see #271"):
        to_sql(plan, dialect)


@pytest.mark.parametrize("engine", ["polars", "datafusion"])
@pytest.mark.parametrize(
    "query", ["SELECT base64(encode(s)) AS b FROM t", "SELECT s, entropy(x) AS e FROM t GROUP BY s"]
)
def test_other_engines_refuse(query, engine):
    con = connect(engine)
    schema = ibis.schema({"s": "string", "x": "int64"})
    create_table(con, "t", schema, [("a", 1), (None, 2)])
    plan = written_plan(json.dumps(lift(query, {"t": schema}).plan))
    # Each engine's own `Unsupported`, a `ValueError`.
    with pytest.raises(ValueError, match="see #271"):
        run_plan(con, plan, engine)


# -- the laws on random data ---------------------------------------------------

_values = st.one_of(
    st.lists(st.one_of(st.none(), st.integers(-3, 3)), max_size=12).map(
        lambda vs: (pa.int64(), vs)
    ),
    st.lists(
        st.one_of(st.none(), st.sampled_from([0.0, -0.0, 1.5, math.inf, math.nan])), max_size=12
    ).map(lambda vs: (pa.float64(), vs)),  # fmt: skip
    st.lists(st.one_of(st.none(), st.text(max_size=3)), max_size=12).map(
        lambda vs: (pa.string(), vs)
    ),
)


def _table(ty: pa.DataType, vs: list, groups: list[int]) -> pa.Table:
    return pa.table(
        {
            "g": pa.array(groups[: len(vs)] + [0] * (len(vs) - len(groups)), pa.int64()),
            "x": pa.array(vs, ty),
        }  # fmt: skip
    )


@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(col=_values, groups=st.lists(st.integers(0, 2), max_size=12))
def test_entropy_keeps_its_laws_on_random_data(col, groups):
    # `nonNull` and `atLeast 0` (a double ≥ +0.0), grouped and over no values.
    ty, vs = col
    t = _table(ty, vs, groups)
    queries = [
        "SELECT g, entropy(x) AS e FROM t GROUP BY g",
        "SELECT entropy(x) AS e FROM t",
        "SELECT entropy(DISTINCT x) AS e FROM t",
    ]
    for q in queries:
        for *_, e in (tuple(r.values()) for r in duckdb_result(q, {"t": t}).to_pylist()):
            assert e is not None and e >= 0.0 and math.copysign(1.0, e) == 1.0
    schemas = {"t": ibis.Schema.from_pyarrow(t.schema)}
    plan = json.dumps(lift(queries[0], schemas).plan)
    # Oracle C on the random data too.
    got = duckdb_engine.run(written_plan(plan), {"t": t})
    assert _rows(got) == _rows(duckdb_result(queries[0], {"t": t}))


@settings(max_examples=40, deadline=None)
@given(vs=st.lists(st.one_of(st.none(), st.text(max_size=6)), max_size=8))
def test_base64_keeps_its_laws_on_random_data(vs):
    # `nonNull` where the argument is not NULL, NULL where it is (strict):
    # the UTF-8 bytes in base64. Lean evaluates it, so oracles A and C both.
    t = pa.table({"s": pa.array(vs, pa.string())})
    query = "SELECT s, base64(encode(s)) AS b FROM t"
    for r in duckdb_result(query, {"t": t}).to_pylist():
        if r["s"] is None:
            assert r["b"] is None
        else:
            assert r["b"] == base64.b64encode(r["s"].encode()).decode()
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


# -- #328: scalars -------------------------------------------------------------

#: Lean evaluates these, so oracles A and C. `signbit` away from `±0.0` and
#: NaN, whose sign the model's codes drop; `weekday` is `dayofweek`, exact.
SCALARS_328 = [
    "SELECT id, octet_length(encode(customer)) AS o, strlen(customer || 'é') AS s FROM orders",
    "SELECT id, yearweek(day) AS y, weekday(day) AS w, yearweek(DATE '0001-01-01') AS z"
    " FROM orders",
    "SELECT id, signbit(price) AS b, signbit(-price) AS c FROM orders WHERE price <> 0",
]
#: Lean does not evaluate `printf` and `format`: oracle C only.
FORMATS = [
    "SELECT id, printf('%05d|', amount) AS p, format('{}-', customer) AS f FROM orders",
    "SELECT id, printf('%s!', customer) AS p, format('{:>4}', qty) AS f,"
    " printf('%d', amount > 3) AS b FROM orders",
]


@pytest.mark.parametrize("query", SCALARS_328)
def test_328_scalars_through_oracles_a_and_c(query):
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("query", FORMATS)
def test_printf_written_back_is_duckdbs(query, semantics):
    plan = json.dumps(lift(query, SCHEMAS, semantics).plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    got = duckdb_engine.run(written_plan(plan), TABLES)
    assert _rows(got) == _rows(duckdb_result(query, TABLES))


def test_printf_may_raise():
    # `printf('%d', 'x')` raises: `verify` reports a possible domain error.
    report = sv.verify("SELECT printf('%d', customer) AS p FROM orders", tables=SCHEMAS)
    assert any("domain" in str(e) for e in report.errors), report


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize(
    ("query", "ensures"),
    [
        ("SELECT octet_length(encode(customer)) AS o, strlen(customer) AS s FROM orders",
         ["o IS NULL OR o >= 0", "s IS NULL OR s >= 0"]),
        ("SELECT strlen(customer) AS s FROM orders WHERE customer IS NOT NULL",
         ["s IS NOT NULL", "s >= 0"]),
        ("SELECT signbit(price) AS b FROM orders WHERE price IS NOT NULL", ["b IS NOT NULL"]),
        ("SELECT yearweek(day) AS y FROM orders",
         ["y IS NULL OR y BETWEEN -587764053 AND 588158053"]),
        ("SELECT weekday(day) AS w FROM orders", ["w IS NULL OR w BETWEEN 0 AND 6"]),
        ("SELECT printf('%s', customer) AS p FROM orders WHERE customer IS NOT NULL",
         ["p IS NOT NULL"]),
    ],
)  # fmt: skip
def test_the_328_laws_prove_contracts(query, ensures, semantics):
    report = sv.verify(
        query, tables=SCHEMAS, ensures=ensures, counterexamples=0, semantics=semantics
    )
    # `printf` may raise, so its report has an error, and its law still holds.
    assert all(c.proved for c in report.ensures), report


def test_what_the_328_laws_do_not_say_stays_unproved():
    # `yearweek` of an infinite date is NULL; `octet_length` has no upper bound.
    for query, ensures in [
        ("SELECT yearweek(day) AS y FROM orders WHERE day IS NOT NULL", ["y IS NOT NULL"]),
        ("SELECT octet_length(encode(customer)) AS o FROM orders", ["o <= 1000"]),
        ("SELECT printf('%s', customer) AS p FROM orders", ["p IS NOT NULL"]),
    ]:
        report = sv.verify(query, tables=SCHEMAS, ensures=ensures, counterexamples=0)
        assert not any(c.proved for c in report.ensures)


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT printf('%f', price) FROM orders", "printf of a float64"),
        ("SELECT printf('%s', day) FROM orders", "printf of a date"),
        ("SELECT printf('%d %d', id, amount) FROM orders", "takes 2 argument"),
        ("SELECT octet_length(customer) FROM orders", "BLOB"),
        ("SELECT yearweek(placed) FROM orders", "yearweek of a timestamp"),
        # An INTERVAL, which the model lacks.
        ("SELECT age(placed, placed) FROM orders", "unknown function age"),
    ],
)
def test_328_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


@settings(max_examples=40, deadline=None)
@given(vs=st.lists(st.one_of(st.none(), st.text(max_size=6)), max_size=8))
def test_byte_lengths_keep_their_laws_on_random_data(vs):
    # The UTF-8 byte length, NULL for NULL: exact, so oracles A and C.
    t = pa.table({"s": pa.array(vs, pa.string())})
    query = "SELECT s, octet_length(encode(s)) AS o, strlen(s) AS n FROM t"
    for r in duckdb_result(query, {"t": t}).to_pylist():
        want = None if r["s"] is None else len(r["s"].encode())
        assert r["o"] == r["n"] == want
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


def _days_from_civil(y: int, m: int, d: int) -> int:
    # Proleptic Gregorian, astronomical years (H. Hinnant's `days_from_civil`).
    y -= m <= 2
    era = y // 400
    yoe = y - era * 400
    doy = (153 * (m + (-3 if m > 2 else 9)) + 2) // 5 + d - 1
    return era * 146097 + yoe * 365 + yoe // 4 - yoe // 100 + doy - 719468


def _year(z: int) -> int:
    z += 719468
    era = z // 146097
    doe = z - era * 146097
    yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    mp = (5 * doy + 2) // 153
    return yoe + era * 400 + (mp >= 10)


def _yearweek(d: int) -> int:
    # `BlackBox.yearweek`: the ISO year of the Thursday, and the ISO week,
    # subtracted in the years up to 0 (`duckdb-yearweek`).
    thursday = d - (d + 3) % 7 + 3
    y = _year(thursday)
    w = (thursday - _days_from_civil(y, 1, 1)) // 7 + 1
    return y * 100 + w if y > 0 else y * 100 - w


#: DuckDB's dates, as days: 5877642 BC (its first) to 5881580 AD (its last),
#: without the infinities.
_DAYS = st.one_of(
    st.integers(-2_147_483_646, 2_147_483_646),
    st.integers(-800_000, 3_000_000),
    st.sampled_from([-719_163, -719_162, 0, -1, 19_723, 18_628]),
)


@settings(max_examples=60, deadline=None)
@given(days=st.lists(st.one_of(st.none(), _DAYS), max_size=8))
def test_yearweek_keeps_its_laws_on_random_data(days):
    # Within its bounds, NULL for NULL, and the formula of Lean's evaluator.
    # Python's dates end at 9999, so the days stay integers here.
    # Before 5877641-01-04 BC DuckDB raises (the black box is NULL there).
    days = [d for d in days if d is None or d >= -2_147_483_453]
    t = pa.table({"d": pa.array(days, pa.int32()).cast(pa.date32())})
    rows = duckdb_result("SELECT yearweek(d) AS y FROM t", {"t": t}).column("y").to_pylist()
    for y, d in zip(rows, days, strict=True):
        if d is None:
            assert y is None
        else:
            assert y == _yearweek(d) and -587764053 <= y <= 588158053


@settings(max_examples=30, deadline=None)
@given(days=st.lists(st.one_of(st.none(), st.integers(-719_162, 2_932_896)), max_size=6))
def test_yearweek_is_leans_on_random_dates(days):
    # Oracles A and C over the reference's dates, 0001-01-01 to 9999-12-31.
    t = pa.table({"d": pa.array(days, pa.int32()).cast(pa.date32())})
    result = check("SELECT d, yearweek(d) AS y, weekday(d) AS w FROM t", {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


@settings(max_examples=60, deadline=None)
@given(
    vs=st.lists(
        st.one_of(st.none(), st.floats(), st.sampled_from([0.0, -0.0, math.nan, -math.nan])),
        max_size=8,
    )
)
def test_signbit_keeps_its_laws_on_random_data(vs):
    # Not NULL for a double, and the sign bit, `-0.0` and negative NaNs
    # included (`duckdb-signbit`).
    t = pa.table({"x": pa.array(vs, pa.float64())})
    rows = duckdb_result("SELECT x, signbit(x) AS b FROM t", {"t": t}).to_pylist()
    for r, v in zip(rows, vs, strict=True):
        assert r["b"] == (None if v is None else math.copysign(1.0, v) < 0)


@settings(max_examples=40, deadline=None)
@given(
    fmt=st.one_of(st.none(), st.sampled_from(["%d", "%s", "%5.2f", "<%x>", "{}", "{:>3}", "a"])),
    vs=st.lists(st.one_of(st.none(), st.integers(-(2**63), 2**63 - 1)), max_size=6),
)
def test_printf_keeps_its_laws_on_random_data(fmt, vs):
    # Strict, and a string where it does not raise.
    t = pa.table({"x": pa.array(vs, pa.int64())})
    for fn in ("printf", "format"):
        q = f"SELECT x, {fn}(?, x) AS p FROM t"
        con = duckdb.connect()
        con.register("t", t)
        try:
            rows = con.execute(q, [fmt]).fetchall()
        except Exception:  # noqa: BLE001, S112 - it may raise: `raises` says so
            continue
        for x, p in rows:
            assert (p is None) == (x is None or fmt is None)


# -- #327: lists and vectors ---------------------------------------------------

_VEC = ibis.schema(
    {"id": "!int64", "a": "array<float64>", "b": "array<float64>", "l": "array<int64>"}
)
_VECS = {
    "v": pa.table(
        {
            "id": pa.array([1, 2, 3, 4, 5], pa.int64()),
            "a": pa.array(
                [[1.0, 2.0, 3.0], [0.0, 0.0, 0.0], [-1.5, 0.5, 2.0], None, [3.0, -4.0, 0.5]],
                pa.list_(pa.float64()),
            ),
            "b": pa.array(
                [[2.0, 4.0, 6.0], [1.0, 1.0, 1.0], [1.5, -0.5, -2.0], [1.0, 1.0, 1.0], None],
                pa.list_(pa.float64()),
            ),
            "l": pa.array([[1, 2, None], [], None, [None], [2**62, 2**62]], pa.list_(pa.int64())),
        }
    )
}
_VEC_SCHEMAS = {"v": _VEC}


def _nan_rows(t: pa.Table) -> list:
    """`_rows` with NaN equal to itself, and one zero (the model's doubles)."""

    def canon(x: object) -> object:
        if isinstance(x, float) and math.isnan(x):
            return "NaN"
        if isinstance(x, float) and x == 0.0:
            return 0.0
        return [canon(y) for y in x] if isinstance(x, list) else x

    return _rows(
        pa.table({c: pa.array([repr(canon(x)) for x in t[c].to_pylist()]) for c in t.column_names})
    )


#: Oracle C: Lean does not evaluate the vector functions.
VECTORS = [
    "SELECT id, list_cosine_similarity(a, b) AS s, array_cosine_distance(a, b) AS d,"
    " list_distance(a, b) AS e FROM v",
    "SELECT id, list_inner_product(a, b) AS i, array_negative_inner_product(a, b) AS n,"
    " array_cross_product(a, b) AS c FROM v",
]
#: Exact, so oracles A and C: `list_sum` (Lean evaluates it), and DuckDB's
#: other names of `l[i]` and `[…]`.
LISTS = [
    "SELECT id, list_sum(l) AS s FROM v",
    "SELECT id, list_extract(l, 1) AS x, list_element(l, -1) AS y, array_extract(l, 3) AS z,"
    " list_extract(l, 0) AS w FROM v",
    "SELECT id, array_value(1, 2, 3) AS a, list_extract(array_value(4, 5), 2) AS b FROM v",
]


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("query", VECTORS)
def test_vectors_written_back_are_duckdbs(query, semantics):
    plan = json.dumps(lift(query, _VEC_SCHEMAS, semantics).plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    got = duckdb_engine.run(written_plan(plan), _VECS)
    want = duckdb_result(
        query.replace("array_cos", "list_cos").replace("array_neg", "list_neg"), _VECS
    )
    assert _nan_rows(got) == _nan_rows(want)


@pytest.mark.parametrize("query", LISTS)
def test_327_lists_through_oracles_a_and_c(query):
    # `list_sum` overflows a BIGINT on the last row: drop it.
    tables = {"v": _VECS["v"].slice(0, 4)}
    result = check(query, tables)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_list_sum_raises_past_a_bigint():
    # DuckDB's own is a HUGEINT; the model's a BIGINT, as `SUM`'s.
    plan = written_plan(json.dumps(lift(LISTS[0], _VEC_SCHEMAS).plan))
    with pytest.raises(Exception, match="out of range|Overflow|overflow"):
        duckdb_engine.run(plan, _VECS)
    report = sv.verify(LISTS[0], tables=_VEC_SCHEMAS)
    assert any("domain" in str(e) for e in report.errors), report


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize(
    ("query", "ensures"),
    [
        ("SELECT array_cosine_similarity(a, b) AS s FROM v", ["s IS NULL OR s >= -1"]),
        ("SELECT list_cosine_distance(a, b) AS d FROM v", ["d IS NULL OR d >= 0"]),
        ("SELECT list_distance(a, b) AS e FROM v WHERE a IS NOT NULL AND b IS NOT NULL",
         ["e IS NOT NULL", "e >= 0.0"]),
        ("SELECT list_inner_product(a, b) AS i, array_cross_product(a, b) AS c FROM v"
         " WHERE a IS NOT NULL AND b IS NOT NULL", ["i IS NOT NULL", "c IS NOT NULL"]),
    ],
)  # fmt: skip
def test_the_327_laws_prove_contracts(query, ensures, semantics):
    report = sv.verify(
        query, tables=_VEC_SCHEMAS, ensures=ensures, counterexamples=0, semantics=semantics
    )
    # They raise on NULL elements and unequal lengths: an error, and the laws.
    assert all(c.proved for c in report.ensures), report
    assert any("domain" in str(e) for e in report.errors), report


def test_what_the_327_laws_do_not_say_stays_unproved():
    # A similarity may be NaN (above 1) and is NULL for empty lists.
    for query, ensures in [
        ("SELECT list_cosine_similarity(a, b) AS s FROM v", ["s IS NULL OR s <= 1"]),
        ("SELECT list_cosine_similarity(a, b) AS s FROM v WHERE a IS NOT NULL AND b IS NOT NULL",
         ["s IS NOT NULL"]),
        ("SELECT list_sum(l) AS s FROM v WHERE l IS NOT NULL", ["s IS NOT NULL"]),
    ]:  # fmt: skip
        report = sv.verify(query, tables=_VEC_SCHEMAS, ensures=ensures, counterexamples=0)
        assert not any(c.proved for c in report.ensures)


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT list_sum(a) FROM v", "list_sum of a array<float64>"),
        ("SELECT list_cosine_similarity(l, l) FROM v", "list_cosine_similarity of a array<int64>"),
        ("SELECT list_inner_product(a) FROM v", "takes 2 argument"),
        ("SELECT list_extract(l, id) FROM v", "constant index"),
        ("SELECT array_value(id, 2) FROM v", "only constants"),
    ],
)
def test_327_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, _VEC_SCHEMAS)


_vec = st.lists(
    st.one_of(
        st.floats(-1e6, 1e6),
        st.sampled_from([0.0, -0.0, 1e-300, 1e300, math.inf, math.nan]),
    ),
    min_size=0,
    max_size=4,
)


@settings(max_examples=80, deadline=None)
@given(pairs=st.lists(st.tuples(_vec, _vec), max_size=6))
def test_vectors_keep_their_laws_on_random_data(pairs):
    # Equal lengths and no NULL elements, where they do not raise.
    pairs = [(a, b[: len(a)] + [1.0] * (len(a) - len(b))) for a, b in pairs]
    t = pa.table(
        {
            "a": pa.array([a for a, _ in pairs], pa.list_(pa.float64())),
            "b": pa.array([b for _, b in pairs], pa.list_(pa.float64())),
        }
    )
    query = (
        "SELECT a, b, list_cosine_similarity(a, b) AS s, list_cosine_distance(a, b) AS d,"
        " list_distance(a, b) AS e, list_inner_product(a, b) AS i,"
        " list_negative_inner_product(a, b) AS n FROM t"
    )
    for r in duckdb_result(query, {"t": t}).to_pylist():
        empty = not r["a"]
        for k in ("s", "d"):
            assert (r[k] is None) == empty
        assert r["s"] is None or math.isnan(r["s"]) or r["s"] >= -1.0
        assert r["d"] is None or math.isnan(r["d"]) or r["d"] >= 0.0
        assert r["e"] is not None and (math.isnan(r["e"]) or r["e"] >= 0.0)
        assert r["i"] is not None and r["n"] is not None
    schemas = {"t": ibis.Schema.from_pyarrow(t.schema)}
    plan = json.dumps(lift(query, schemas).plan)
    got = duckdb_engine.run(written_plan(plan), {"t": t})
    assert _nan_rows(got) == _nan_rows(duckdb_result(query, {"t": t}))


@settings(max_examples=40, deadline=None)
@given(
    ls=st.lists(
        st.one_of(
            st.none(), st.lists(st.one_of(st.none(), st.integers(-(2**40), 2**40)), max_size=4)
        ),
        max_size=6,
    )
)
def test_list_sum_keeps_its_laws_on_random_data(ls):
    # The sum of the values, NULLs skipped, NULL without any: oracles A and C.
    t = pa.table({"l": pa.array(ls, pa.list_(pa.int64()))})
    query = "SELECT l, list_sum(l) AS s FROM t"
    for r in duckdb_result(query, {"t": t}).to_pylist():
        vs = [v for v in r["l"] or [] if v is not None]
        assert r["s"] == (sum(vs) if vs else None)
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


# -- #326: statistical aggregates ----------------------------------------------

#: Oracle C: Lean evaluates none of them. Integers are converted to doubles.
STATS = [
    "SELECT customer, product(amount) AS p, kahan_sum(price) AS k, fsum(qty) AS f,"
    " favg(price) AS a FROM orders GROUP BY customer",
    "SELECT sem(amount) AS s, mad(price) AS m, sumkahan(amount) AS k, product(price) AS p"
    " FROM orders",
    "SELECT kurtosis(amount) AS k, kurtosis_pop(price) AS kp, skewness(qty) AS s,"
    " sem(price) FILTER (WHERE price > 0) AS f FROM orders",
    # No values: NULL.
    "SELECT product(amount) AS p, sem(price) AS s, mad(qty) AS m FROM orders WHERE id > 100",
]


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize("query", STATS)
def test_statistics_written_back_are_duckdbs(query, semantics):
    plan = json.dumps(lift(query, SCHEMAS, semantics).plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out
    got = duckdb_engine.run(written_plan(plan), TABLES)
    assert _nan_rows(got) == _nan_rows(duckdb_result(query, TABLES))


def test_bit_count_through_oracles_a_and_c():
    result = check("SELECT id, bit_count(amount) AS b, bit_count(-amount) AS c FROM orders", TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("semantics", ["duckdb", "reference"])
@pytest.mark.parametrize(
    ("query", "ensures"),
    [
        ("SELECT customer, sem(price) AS s, mad(amount) AS m FROM orders GROUP BY customer",
         ["s IS NULL OR s >= 0", "m IS NULL OR m >= 0"]),
        # `amount` is never NULL, so each group has values.
        ("SELECT customer, sem(amount) AS s, product(amount) AS p, kahan_sum(amount) AS k"
         " FROM orders GROUP BY customer", ["s >= 0", "p IS NOT NULL", "k IS NOT NULL"]),
        ("SELECT bit_count(id) AS b FROM orders", ["b BETWEEN 0 AND 64"]),
    ],
)  # fmt: skip
def test_the_326_laws_prove_contracts(query, ensures, semantics):
    report = sv.verify(
        query, tables=SCHEMAS, ensures=ensures, counterexamples=0, semantics=semantics
    )
    assert report.proved, report


def test_moments_may_raise():
    # DuckDB raises where a moment is out of range: a domain error.
    for fn in ("kurtosis", "kurtosis_pop", "skewness"):
        report = sv.verify(f"SELECT {fn}(price) AS k FROM orders", tables=SCHEMAS)
        assert any("domain" in str(e) for e in report.errors), report
    report = sv.verify("SELECT sem(price) AS s FROM orders", tables=SCHEMAS)
    assert not report.errors


def test_what_the_326_laws_do_not_say_stays_unproved():
    for query, ensures in [
        # Moments are NULL for few or equal values.
        ("SELECT kurtosis_pop(price) AS k FROM orders", ["k IS NOT NULL"]),
        ("SELECT product(amount) AS p FROM orders", ["p >= 0"]),
        ("SELECT sem(price) AS s FROM orders", ["s <= 1000.0"]),
    ]:
        report = sv.verify(query, tables=SCHEMAS, ensures=ensures, counterexamples=0)
        assert not any(c.proved for c in report.ensures)


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT histogram(amount) FROM orders", "MAP"),
        ("SELECT weighted_avg(price, amount) FROM orders", "two arguments"),
        ("SELECT wavg(price, amount) FROM orders", "two arguments"),
        ("SELECT mad(cost) FROM orders", "mad of a decimal"),
        ("SELECT mad(day) FROM orders", "mad of a date"),
        ("SELECT bit_count(qty) FROM orders", "cast it to BIGINT"),
        ("SELECT product(amount) OVER () FROM orders", "over a window"),
    ],
)
def test_326_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


_doubles = st.lists(
    st.one_of(
        st.none(),
        st.floats(-1e6, 1e6),
        st.sampled_from([0.0, -0.0, 1e300, -1e300, math.inf, -math.inf, math.nan]),
    ),
    max_size=10,
)


@settings(max_examples=80, deadline=None)
@given(vs=_doubles, groups=st.lists(st.integers(0, 2), max_size=10))
def test_statistics_keep_their_laws_on_random_data(vs, groups):
    # Not NULL over values, `sem` and `mad` at least 0 (or NaN), NULL without
    # values; the moments raise or are doubles.
    t = _table(pa.float64(), vs, groups)
    query = (
        "SELECT g, count(x) AS n, product(x) AS p, kahan_sum(x) AS k, favg(x) AS a,"
        " sem(x) AS s, mad(x) AS m FROM t GROUP BY g"
    )
    for r in duckdb_result(query, {"t": t}).to_pylist():
        for c in ("p", "k", "a", "s", "m"):
            assert (r[c] is None) == (r["n"] == 0)
        for c in ("s", "m"):
            assert r[c] is None or math.isnan(r[c]) or r[c] >= 0.0
    for fn in ("kurtosis", "kurtosis_pop", "skewness"):
        try:
            duckdb_result(f"SELECT g, {fn}(x) AS k FROM t GROUP BY g", {"t": t})
        except Exception as e:  # noqa: BLE001 - `raises` says it may
            assert "out of range" in str(e)
    schemas = {"t": ibis.Schema.from_pyarrow(t.schema)}
    plan = json.dumps(lift(query, schemas).plan)
    got = duckdb_engine.run(written_plan(plan), {"t": t})
    assert _nan_rows(got) == _nan_rows(duckdb_result(query, {"t": t}))


@settings(max_examples=40, deadline=None)
@given(vs=st.lists(st.one_of(st.none(), st.integers(-(2**63), 2**63 - 1)), max_size=8))
def test_bit_count_keeps_its_laws_on_random_data(vs):
    # The 1 bits of 64-bit two's complement, NULL for NULL: oracles A and C.
    t = pa.table({"x": pa.array(vs, pa.int64())})
    query = "SELECT x, bit_count(x) AS b FROM t"
    for r in duckdb_result(query, {"t": t}).to_pylist():
        assert r["b"] == (None if r["x"] is None else bin(r["x"] % 2**64).count("1"))
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"
