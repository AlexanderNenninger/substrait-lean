"""The shims of the translation from the reference to Polars (#444,
`sverify._polars_shims`).

Each shim is checked three ways on the edge cases of its Polars fact
(`characterization/polars/facts/`): Polars's native expression differs from
the reference there (so the shim is needed), the shim gives the reference's
value, and a plan that uses it runs on Polars as `Rel.eval` (`substrait-check`)
evaluates it, oracle style.
"""

import json
import math
from pathlib import Path

import ibis
import polars as pl
import pyarrow as pa
import pytest

from sverify import _polars_shims as shims
from sverify import polars_engine
from sverify.engine import connect, create_table, run_plan, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.testing import inline_tables, lean_rows, lean_values

pytestmark = pytest.mark.backend("polars")

ROOT = Path(__file__).parents[2]
MIN, MAX = -(2**63), 2**63 - 1
INTS = ibis.schema({"g": "int64", "a": "int64", "b": "int64"})
FLOATS = ibis.schema({"g": "int64", "x": "float64"})


def rows_of(table) -> list[tuple]:
    return [tuple(r.values()) for r in table.to_pylist()]


def lean_and_polars(schema, rows, sql: str, doubles: bool = False) -> tuple[list, list]:
    """`Rel.eval`'s rows and Polars's for `sql` under the reference."""
    con = connect()
    create_table(con, "r", schema, rows)
    plan = written_plan(substrait_json(con, sql, "reference"))
    inlined = json.dumps(inline_tables(json.loads(plan), {"r": rows}))
    lean = lean_values(inlined) if doubles else lean_rows(inlined)
    return lean, rows_of(run_plan(con, plan, "polars"))


def native(df: pl.DataFrame, *exprs: pl.Expr) -> list[tuple]:
    return df.select(e.alias(f"_{i}") for i, e in enumerate(exprs)).rows()


# --- The table -----------------------------------------------------------------


def test_every_shim_and_guard_is_a_function_with_a_fact():
    options = (ROOT / "SubstraitLean" / "Options.lean").read_text()
    areas = (ROOT / "characterization" / "areas.json").read_text()
    for s in shims.SHIMS:
        assert callable(getattr(shims, s.name)), s.name
        assert (ROOT / "characterization/polars/facts" / f"{s.fact}.json").exists(), s.fact
        # An option of the catalogue, or a checklist item it does not have yet.
        assert f'id := "{s.option}"' in options or f'"id": "{s.option}"' in areas, s.option
    for g in shims.GUARDS:
        assert callable(getattr(shims, g.flag)), g.flag
        assert (ROOT / "characterization/polars/facts" / f"{g.fact}.json").exists(), g.fact
        assert g.issue in polars_engine.ALL_GUARDS | {polars_engine.InfiniteResult.issue}
    assert len({s.name for s in shims.SHIMS}) == len(shims.SHIMS)


# --- Integer division and modulus: TRUNCATE ------------------------------------

#: polars-int-divide's and polars-int-modulus's cases: every sign pair, exact
#: and inexact, and `MIN % -1`.
DIVISIONS = [(-7, 2), (7, -2), (-7, -2), (7, 2), (1, -2), (-1, 2), (1, -7), (-6, 3), (MIN, -2),
             (MIN, 7), (MAX, -3), (0, -5)]  # fmt: skip


def test_polars_floors_and_the_shims_truncate():
    df = pl.DataFrame({"a": [a for a, _ in DIVISIONS], "b": [b for _, b in DIVISIONS]})
    a, b = pl.col("a"), pl.col("b")
    want = [_tdiv(a, b) for a, b in DIVISIONS]
    assert native(df, a // b, a % b) != want
    assert native(df, shims.int_div_trunc(a, b), shims.int_mod_trunc(a, b)) == want
    assert native(df, shims.int_mod_trunc(pl.lit(MIN), pl.lit(-1))) == [(0,)]


def _tdiv(a: int, b: int) -> tuple[int, int]:
    q = abs(a) // abs(b) * (1 if (a < 0) == (b < 0) else -1)
    return q, a - b * q


def test_division_and_modulus_match_lean():
    rows = [(0, a, b) for a, b in DIVISIONS] + [(0, None, 2), (0, 3, None)]
    lean, polars = lean_and_polars(INTS, rows, "SELECT a // b AS q, a % b AS m FROM r")
    assert (
        lean
        == polars
        == [(None, None) if a is None or b is None else _tdiv(a, b) for _, a, b in rows]
    )


def test_division_guards():
    con = connect()
    create_table(con, "r", INTS, [(0, MIN, -1)])
    plan = written_plan(substrait_json(con, "SELECT a // b AS q FROM r", "reference"))
    with pytest.raises(polars_engine.Overflow):
        run_plan(con, plan, "polars")
    create_table(con, "r", INTS, [(0, 1, 0)])
    with pytest.raises(polars_engine.DivisionByZero):
        run_plan(con, plan, "polars")
    # Without the guards Polars's own value is left: a verified plan has none.
    assert polars_engine.run(plan, {"r": con.arrow["r"]}, guards=False)["q"].to_pylist() == [None]


# --- Integer arithmetic: native, with the overflow guard ------------------------


def test_integer_arithmetic_is_native_and_guarded():
    rows = [(0, MAX - 1, 1), (0, MIN, 0), (0, -(2**31), 2**31), (0, None, 5)]
    lean, polars = lean_and_polars(INTS, rows, "SELECT a + b, a - b, a * b FROM r")
    assert lean == polars
    con = connect()
    create_table(con, "r", INTS, [(0, MAX, 1)])
    plan = written_plan(substrait_json(con, "SELECT a + b AS s FROM r", "reference"))
    with pytest.raises(polars_engine.IntegerOverflow):
        run_plan(con, plan, "polars")
    # Polars wraps (polars-int-arith): what the guard is for.
    out = polars_engine.run(plan, {"r": con.arrow["r"]}, guards=False)
    assert out["s"].to_pylist() == [MIN]


# --- SUM and AVG of integers -----------------------------------------------------

GROUPED = [(1, 2**62, 0), (1, 2**62, 0), (2, None, 0), (3, -7, 0), (3, 2, 0), (3, 2, 0),
           (4, -5, 0), (4, 2, 0), (5, MIN, 0), (5, MIN + 1, 0)]  # fmt: skip


def test_polars_sums_nothing_to_zero_and_averages_to_a_double():
    df = pl.DataFrame({"a": [None]}, schema={"a": pl.Int64})
    v = pl.col("a")
    assert native(df, v.sum(), v.mean()) == [(0, None)]
    assert native(df, shims.int_sum(v), shims.avg_int_declared(v)) == [(None, None)]
    df = pl.DataFrame({"a": [-7, 2, 2]})
    assert native(df, v.mean()) == [(-1.0,)]
    assert native(df, shims.avg_int_declared(v)) == [(-1,)]
    df = pl.DataFrame({"a": [2**62, 2**62, 1]})  # polars-avg-int: rounds above 2^53
    exact = (2**63 + 1) // 3
    assert native(df, v.mean()) != [(float(exact),)] or int(native(df, v.mean())[0][0]) != exact
    assert native(df, shims.avg_int_declared(v)) == [(exact,)]


@pytest.mark.parametrize("measure", ["SUM(a)", "AVG(a)::BIGINT", "COUNT(a)"])
def test_integer_sum_and_avg_match_lean(measure):
    # Groups 1 and 5 leave 64 bits when summed.
    rows = [r for r in GROUPED if r[0] not in (1, 5)] if measure == "SUM(a)" else GROUPED
    lean, polars = lean_and_polars(INTS, rows, f"SELECT g, {measure} AS m FROM r GROUP BY g")
    assert lean == polars


@pytest.mark.parametrize("where", ["WHERE g > 9", "WHERE g = 2", ""])
def test_ungrouped_sum_of_nothing_is_null(where):
    rows = [r for r in GROUPED if r[0] in (2, 3, 4)]
    sql = f"SELECT SUM(a) AS s, AVG(a)::BIGINT AS m FROM r {where}"
    lean, polars = lean_and_polars(INTS, rows, sql)
    assert lean == polars
    if where:
        assert polars == [(None, None)]


def test_sum_overflow_is_guarded_with_or_without_the_other_guards():
    con = connect()
    create_table(con, "r", INTS, GROUPED[:2])
    plan = written_plan(substrait_json(con, "SELECT g, SUM(a) AS s FROM r GROUP BY g", "reference"))
    for guards in (True, False, {"SUM overflow"}):
        with pytest.raises(polars_engine.SumOverflow, match="SUM leaves 64 bits"):
            polars_engine.run(plan, {"r": con.arrow["r"]}, guards=guards)
    # Not assumed: no check, and the sum outside 64 bits is NULL.
    out = polars_engine.run(plan, {"r": con.arrow["r"]}, guards=set())
    assert out["s"].to_pylist() == [None]


# --- Doubles ---------------------------------------------------------------------

#: Sums every order gives exactly: halves and small integers.
XS = [(1, 0.5), (1, -2.5), (1, 1.5), (2, None), (3, -0.0), (4, 2.5), (4, -2.5), (5, math.nan),
      (5, 1.0)]  # fmt: skip


@pytest.mark.parametrize("measure", ["SUM(x)", "AVG(x)"])
def test_float_sum_and_avg_match_lean(measure):
    sql = f"SELECT g, {measure} AS m FROM r GROUP BY g"
    lean, polars = lean_and_polars(FLOATS, XS, sql, doubles=True)
    assert [g for g, _ in polars] == [g for g, _ in lean]
    for (_, want), (_, got) in zip(lean, polars, strict=True):
        # Lean prints six decimals; `sum_order = ANY` allows Polars's order.
        assert (
            (want is None and got is None)
            or math.isclose(want, got, abs_tol=1e-6)
            or (math.isnan(want) and math.isnan(got))
        ), (lean, polars)
    # One zero: Polars keeps -0.0 for a group of one (polars-zero-sign).
    zeros = [m for g, m in polars if g in (3, 4)]
    assert all(math.copysign(1.0, z) == 1.0 for z in zeros)


def test_float_sum_of_nothing_is_null():
    lean, polars = lean_and_polars(
        FLOATS, XS, "SELECT SUM(x) AS s, AVG(x) AS m FROM r WHERE g > 9", doubles=True
    )
    assert lean == polars == [(None, None)]


def test_float_sum_of_both_infinities_is_guarded():
    con = connect()
    create_table(con, "r", FLOATS, [(1, math.inf), (1, -math.inf)])
    plan = written_plan(substrait_json(con, "SELECT g, SUM(x) AS s FROM r GROUP BY g", "reference"))
    with pytest.raises(polars_engine.DomainError, match="would make a NaN"):
        polars_engine.run(plan, {"r": con.arrow["r"]})
    # polars-nonfinite-aggregates: NaN, where the reference raises.
    out = polars_engine.run(plan, {"r": con.arrow["r"]}, guards=False)
    assert math.isnan(out["s"].to_pylist()[0])


@pytest.mark.parametrize(
    "sql",
    ["SELECT x * 10.0 AS y FROM r", "SELECT g, SUM(x) AS y FROM r GROUP BY g",
     "SELECT g, AVG(x) AS y FROM r GROUP BY g"],
)  # fmt: skip
def test_overflow_to_infinity_is_checked_when_assumed(sql):
    """#575: the reference assumes finite doubles give finite results; the
    report lists it, and the run checks it on the data."""
    con = connect()
    create_table(con, "r", FLOATS, [(1, 1e308), (1, 1e308)])
    plan = written_plan(substrait_json(con, sql, "reference"))
    tables = {"r": con.arrow["r"]}
    # Checked by the default guards, by name, and without guards, as a
    # `SUM`'s overflow is (`Issue.assumed`).
    for guards in (True, {"overflow to infinity"}, False):
        with pytest.raises(polars_engine.InfiniteResult):
            polars_engine.run(plan, tables, guards=guards)


def test_unknown_guards_are_refused():
    with pytest.raises(ValueError, match="unknown issues"):
        polars_engine.checks_of({"overflw"})


# --- ROUND: TIE_AWAY_FROM_ZERO ----------------------------------------------------

HALVES = [0.5, 1.5, 2.5, -0.5, -2.5, 0.49999999999999994, 4503599627370495.5]


def test_polars_rounds_halves_to_even_and_the_shim_away_from_zero():
    df = pl.DataFrame({"x": HALVES})
    x = pl.col("x")
    want = [(math.copysign(math.floor(abs(v) + 0.5), v) if abs(v) % 1 == 0.5 else round(v),)
            for v in HALVES]  # fmt: skip
    assert native(df, x.round(0)) != want
    assert native(df, shims.one_zero(shims.round_half_away(x))) == [(w + 0.0,) for (w,) in want]


def test_round_matches_lean():
    rows = [(0, v) for v in HALVES] + [(0, None)]
    lean, polars = lean_and_polars(FLOATS, rows, "SELECT ROUND(x) AS y FROM r", doubles=True)
    assert lean == polars


# --- Sorts: NULL order and ties ---------------------------------------------------

SORTABLE = [(1, 2, 0), (1, None, 1), (2, 0, 2), (3, None, 3), (4, 2, 4), (5, 0, 5)]


@pytest.mark.parametrize(
    "direction", ["", "ASC NULLS FIRST", "ASC NULLS LAST", "DESC NULLS FIRST", "DESC NULLS LAST"]
)
def test_sort_null_order_and_ties_match_lean(direction):
    sql = f"SELECT g, a, b FROM r ORDER BY a {direction}"
    lean, polars = lean_and_polars(INTS, SORTABLE, sql)
    assert lean == polars
    # Ties (a = 2, a = 0) keep their input order.
    assert [g for g, a, _ in polars if a == 2] == [1, 4]


def test_polars_puts_nulls_first_and_the_shim_states_each_key():
    df = pl.DataFrame({"a": [2, None, 0]})
    assert df.sort("a", descending=True)["a"].to_list()[0] is None  # polars-null-order
    desc, last = shims.SORT_DIRECTIONS["SORT_DIRECTION_DESC_NULLS_LAST"]
    assert df.sort("a", descending=desc, nulls_last=last)["a"].to_list() == [2, 0, None]


def test_an_unspecified_direction_is_ascending_with_nulls_last():
    """D6/D8: `SORT_DIRECTION_UNSPECIFIED` (left out of protobuf's JSON) is
    the model's default `SortKey`. Lean's parser refuses it until step 1c, so
    the plan with the stated direction is the oracle."""
    con = connect()
    create_table(con, "r", INTS, SORTABLE)
    plan = json.loads(
        written_plan(substrait_json(con, "SELECT g, a FROM r ORDER BY a", "reference"))
    )
    stated = rows_of(polars_engine.run(plan, {"r": con.arrow["r"]}))
    keys = [
        s
        for s in _find(plan, "sorts")
        for s in s
        if s["direction"] == "SORT_DIRECTION_ASC_NULLS_LAST"
    ]
    assert keys
    for unspecified in ("SORT_DIRECTION_UNSPECIFIED", None):
        for k in keys:
            if unspecified is None:
                k.pop("direction", None)
            else:
                k["direction"] = unspecified
        assert rows_of(polars_engine.run(plan, {"r": con.arrow["r"]})) == stated
    assert [a for _, a in stated][-2:] == [None, None]


def _find(node, key):
    if isinstance(node, dict):
        if key in node:
            yield node[key]
        for v in node.values():
            yield from _find(v, key)
    elif isinstance(node, list):
        for v in node:
            yield from _find(v, key)


def test_avg_of_integers_in_the_declared_type_matches_lean():
    """`AggFn.iavg`: an `AVG` of integers whose output type is an integer,
    which a producer states (no lift writes it from SQL)."""
    con = connect()
    create_table(con, "r", INTS, GROUPED)
    plan = json.loads(
        written_plan(substrait_json(con, "SELECT g, AVG(a) AS m FROM r GROUP BY g", "reference"))
    )
    (measure,) = [m["measure"] for ms in _find(plan, "measures") for m in ms]
    arg = measure["arguments"][0]["value"]
    measure["arguments"][0]["value"] = arg["cast"]["input"]
    measure["outputType"] = {"i64": {"nullability": "NULLABILITY_NULLABLE"}}
    lean = lean_rows(json.dumps(inline_tables(plan, {"r": GROUPED})))
    polars = rows_of(polars_engine.run(plan, {"r": con.arrow["r"]}))
    assert lean == polars
    assert dict(polars)[3] == -1  # (-7 + 2 + 2) / 3, truncated toward zero
    assert dict(polars)[2] is None


# --- Strings: positions in characters, from 1 -----------------------------------

STRINGS = ibis.schema({"g": "int64", "s": "string", "t": "string"})
#: polars-strpos's and polars-substring's cases: multibyte characters, the
#: empty string and pattern, absent patterns, NULLs.
TEXTS = [(0, "héllo", "l"), (1, "日本語本", "本"), (2, "", ""), (3, "", "a"), (4, "abc", ""),
         (5, "abcabc", "bc"), (6, "abc", "z"), (7, None, "a"), (8, "a", None)]  # fmt: skip


def test_polars_finds_bytes_from_zero_and_the_shim_characters_from_one():
    df = pl.DataFrame({"s": [s for _, s, _ in TEXTS], "t": [t for _, _, t in TEXTS]})
    s, t = pl.col("s"), pl.col("t")
    want = [
        (None,) if a is None or b is None else (a.find(b) + 1,) for _, a, b in TEXTS
    ]  # `Text.strpos`, as Python's `find`
    assert native(df, s.str.find(t, literal=True)) != want
    assert native(df, shims.strpos_chars(s, t)) == want


def test_strpos_matches_lean():
    lean, polars = lean_and_polars(STRINGS, TEXTS, "SELECT g, strpos(s, t) AS p FROM r")
    assert lean == polars


@pytest.mark.parametrize("start", [-10, -4, -3, -1, 0, 1, 2, 5])
def test_substring_with_a_negative_start_matches_lean(start):
    sql = f"SELECT g, substring(s, {start}, 2) AS a, substring(s, {start}) AS b FROM r"
    lean, polars = lean_and_polars(STRINGS, TEXTS, sql)
    assert lean == polars


# --- Double group keys: one zero, one NaN ---------------------------------------


def test_double_group_keys_have_one_zero_and_one_nan():
    """B2: Polars groups `-0.0` with `0.0` but keeps the first zero it sees
    as the key (polars-zero-sign); the reference has one zero."""
    df = pl.DataFrame({"x": [-0.0, 0.0, math.nan, -math.nan]})
    keys = df.group_by("x", maintain_order=True).len()["x"].to_list()
    assert math.copysign(1.0, keys[0]) == -1.0
    rows = [(1, -0.0), (2, 0.0), (3, math.nan), (4, -math.nan), (5, None), (6, -0.0)]
    lean, polars = lean_and_polars(
        FLOATS, rows, "SELECT x, COUNT(*) AS n FROM r GROUP BY x", doubles=True
    )
    assert repr(lean) == repr(polars)
    assert [n for _, n in polars] == [3, 2, 1]
    assert math.copysign(1.0, polars[0][0]) == 1.0


# --- Refused ---------------------------------------------------------------------


def test_md5_is_refused_on_polars_with_the_reason():
    """G1: no Polars expression computes `md5`; the engine support table
    (`_support.SUPPORT`) refuses it before the run, with #271."""
    con = connect()
    create_table(con, "r", STRINGS, TEXTS)
    t = ibis.table(STRINGS, name="r")
    plan = written_plan(to_substrait_json(t.select(h=t.s.hexdigest("md5"))))
    with pytest.raises(polars_engine.Unsupported, match="see #271"):
        run_plan(con, plan, "polars")


# --- The streaming engine ---------------------------------------------------------


def _batches(collect) -> int:
    """How many batches an elementwise function sees: 1 in memory, one per
    morsel when Polars streams."""
    calls: list[int] = []

    def f(s: pl.Series) -> pl.Series:
        calls.append(len(s))
        return s

    lf = pl.LazyFrame({"x": range(300_000)}).select(
        pl.col("x").map_batches(f, return_dtype=pl.Int64, is_elementwise=True)
    )
    collect(lf)
    return len(calls)


@pytest.mark.parametrize(
    "setting",
    [{}, {"POLARS_ENGINE_AFFINITY": "in-memory"}, {"POLARS_FORCE_STREAMING": "0"},
     {"POLARS_AUTO_STREAMING": "0"}, "config"],
)  # fmt: skip
def test_queries_stream_whatever_the_settings(setting, monkeypatch):
    """Sverify names the streaming engine, so neither `pl.Config` nor the
    environment moves its queries to the in-memory engine."""
    in_memory = lambda lf: lf.collect(engine="in-memory")  # noqa: E731
    assert _batches(in_memory) == 1
    if setting == "config":
        with pl.Config() as cfg:
            cfg.set_engine_affinity("in-memory")
            assert _batches(lambda lf: lf.collect()) == 1
            assert _batches(polars_engine.collect) > 1
        return
    for k, v in setting.items():
        monkeypatch.setenv(k, v)
    assert _batches(polars_engine.collect) > 1


def test_fallback_nodes_are_found():
    """`fallback_nodes` reads the physical plan: a list per group runs on
    the in-memory engine, a sum per group streams."""
    lf = pl.LazyFrame({"g": [1, 2, 1], "x": [1.0, 2.0, 3.0]}).group_by("g", maintain_order=True)
    assert polars_engine.fallback_nodes(lf.agg(pl.col("x").sum())) == []
    (node,) = polars_engine.fallback_nodes(lf.agg(pl.col("x").implode()))
    assert node.startswith("in-memory-map: AGGREGATE")
    assert polars_engine.disallowed_fallbacks(lf.agg(pl.col("x").implode())) == []
    q = lf.agg(pl.col("x").median())
    assert polars_engine.disallowed_fallbacks(q) == polars_engine.fallback_nodes(q) != []


# --- CASE: Polars computes every branch -----------------------------------------

CASES = ibis.schema({"a": "int64", "b": "int64", "x": "float64", "s": "string"})
CASE_ROWS = [(10, 0, 0.0, "ab"), (MIN, -1, -1.0, None), (7, -2, math.nan, "日本"),
             (3, 2, 1e308, "")]  # fmt: skip


@pytest.mark.parametrize(
    "case",
    ["CASE WHEN b <> 0 THEN a % b END",
     "CASE WHEN b <> 0 AND NOT (a = -9223372036854775808 AND b = -1) THEN a // b END",
     "CASE WHEN a > -9223372036854775808 THEN -a END",
     "CASE WHEN a < 1000 AND a > -1000 THEN a * a END",
     "CASE WHEN x = x AND x < 1e18 AND x > -1e18 THEN CAST(x AS BIGINT) END",
     "CASE WHEN x > 0 THEN sqrt(x) END",
     "CASE WHEN b > 0 THEN pow(a, b) END",
     "CASE WHEN a < 100 THEN repeat(s, a) END",
     "CASE WHEN a > 0 THEN CAST(a AS INTEGER) END",
     # Polars's CSE may hoist a repeated subexpression out of its branch
     # (`csee.rs`); the translator's casts are masked inside the expression.
     "CASE WHEN x = x AND x < 1e18 AND x > -1e18 THEN CAST(x AS BIGINT) + CAST(x AS BIGINT)"
     " WHEN x = x AND x < 1e17 THEN CAST(x AS BIGINT) END"],
)  # fmt: skip
def test_an_untaken_branch_neither_raises_nor_leaks(case):
    """Polars evaluates both sides of `when/then/otherwise` on every row. The
    translator gives an untaken branch safe arguments (a divisor of 1, a
    shift of 0) and masks its issues, as `Expr.issues` does, so a guarded
    `a // b`, overflow or cast raises nowhere and gives `Rel.eval`'s rows."""
    sql = f"SELECT {case} AS y FROM r"
    lean, polars = lean_and_polars(CASES, CASE_ROWS, sql, doubles="x" in case or "pow" in case)
    if "x" in case and "BIGINT" not in case:
        assert [y is None for (y,) in lean] == [y is None for (y,) in polars]
    else:
        assert lean == polars


# --- Native in place of numpy ------------------------------------------------------

POWERS = [(a, b) for a in (-3, -2, -1, 0, 1, 2, 3, 7, 2**31, -(2**31), MIN, MAX)
          for b in (0, 1, 2, 3, 31, 32, 62, 63, 64, 65, 127, 128, 200, MAX)]  # fmt: skip


def _pow(a: int, b: int) -> int | None:
    """`BinFn.ipow`, NULL where it leaves 64 bits."""
    if abs(a) <= 1:
        return a**b if a != -1 else (1 if b % 2 == 0 else -1)
    if b > 64:
        return None
    p = a**b
    return p if MIN <= p <= MAX else None


def test_integer_powers_are_native_and_exact():
    df = pl.DataFrame({"a": [a for a, _ in POWERS], "b": [b for _, b in POWERS]})
    got = df.select(polars_engine._ipow(pl.col("a"), pl.col("b")).alias("p"))["p"].to_list()
    assert got == [_pow(a, b) for a, b in POWERS]


def test_integer_powers_match_lean():
    from _pipelines import integer_powers

    rows = [(0, a, b) for a in (-3, -1, 0, 2, 3) for b in (0, 1, 2, 31, 39)]
    rows += [(1, a, b) for a in (-1, 0, 1) for b in (63, 64, 65, 200)]
    con = connect()
    create_table(con, "r", INTS, rows)
    sql = "SELECT pow(a, b) AS p FROM r"
    plan = integer_powers(json.loads(substrait_json(con, sql, "reference")))
    plan = json.loads(written_plan(json.dumps(plan)))
    lean = lean_rows(json.dumps(inline_tables(plan, {"r": rows})))
    assert lean == rows_of(polars_engine.run(plan, {"r": con.arrow["r"]}))


#: Days from 0001-01-01 to 9999-12-31 at month ends and leap days.
DAYS = sorted({polars_engine.DAY_MIN, polars_engine.DAY_MAX, -1, 0, 59, 60, 11016, 11017, 18321,
               -719162 + 30, 2932896 - 30, *range(10950, 11400, 7)})  # fmt: skip


@pytest.mark.parametrize("months", [-13, -1, 1, 3, 12, 25])
def test_month_arithmetic_is_native_and_the_calendars(months):
    """`Time.addMonths` and `truncDay` as Polars integer expressions, against
    the same integer formulas in Python and Polars's own calendar."""
    df = pl.DataFrame({"d": DAYS + [None]})
    d = pl.col("d")
    out = df.select(
        a=polars_engine.add_months_days(months, d),
        m=polars_engine.trunc_days("month", d),
        q=polars_engine.trunc_days("quarter", d),
        y=polars_engine.trunc_days("year", d),
    )
    dates = df.select(d.cast(pl.Date))["d"]
    want_m = dates.dt.truncate("1mo").cast(pl.Int64).to_list()
    want_q = dates.dt.truncate("1q").cast(pl.Int64).to_list()
    want_y = dates.dt.truncate("1y").cast(pl.Int64).to_list()
    assert out["m"].to_list() == want_m
    assert out["q"].to_list() == want_q
    assert out["y"].to_list() == want_y
    shifted = df.select(d.cast(pl.Date).dt.offset_by(f"{months}mo").cast(pl.Int64))["d"]
    inside = [polars_engine.DAY_MIN <= x <= polars_engine.DAY_MAX if x is not None else True
              for x in shifted.to_list()]  # fmt: skip
    for got, want, ok in zip(out["a"].to_list(), shifted.to_list(), inside, strict=True):
        if ok:
            assert got == want


def _ulps(a: float, b: float) -> float:
    return abs(a - b) / math.ulp(b) if b != 0.0 else abs(a) / math.ulp(0.0)


@pytest.mark.parametrize("n", [2, 5001])
def test_double_division_is_within_two_ulps_and_the_remainder_exact(n):
    """PL-3 (polars-double-scalar-divisor): Polars divides by a constant
    through its reciprocal, on both engines and from 2 rows on. The
    reference's `/` is `approx` there, 2 ulps per division, for a divisor
    that is not subnormal; `%` stays C's `fmod`, exact, and `ROUND`'s
    division by `10^d` exact."""
    xs = [49.0, 0.0, 1e-300, 7.0, -3.3, 1e308, 5e-324]
    lf = pl.LazyFrame({"x": xs * n})
    out = polars_engine.collect(
        lf.select(
            q=polars_engine.fdiv(pl.col("x"), pl.lit(49.0)),
            m=polars_engine.fmod(pl.col("x"), pl.lit(49.0)),
            r=polars_engine.exact_div(pl.col("x"), pl.lit(49.0)),
        )
    )
    for x, (q, m, r) in zip(xs, out.rows()[: len(xs)], strict=True):
        assert _ulps(q, x / 49.0) <= 2
        assert m == math.fmod(x, 49.0)
        assert r == x / 49.0
    rows = [(0, 49.0), (1, 0.0), (2, 1e-300)] * n
    sql = "SELECT g, x / 49.0 AS q, x % 49.0 AS m, ROUND(x / 7.0, 2) AS r FROM r"
    lean, polars = lean_and_polars(FLOATS, rows[:6], sql, doubles=True)
    for (g, q, m, r), (h, q2, m2, r2) in zip(polars, lean, strict=True):
        assert g == h and math.isclose(q, q2, abs_tol=1e-6) and math.isclose(m, m2, abs_tol=1e-6)
        assert math.isclose(r, r2, abs_tol=1e-6)


def test_a_subnormal_divisor_is_refused():
    con = connect()
    create_table(con, "r", FLOATS, [(0, 1.0), (1, 2.0)])
    plan = written_plan(substrait_json(con, "SELECT x / 1e-310 AS q FROM r", "reference"))
    with pytest.raises(polars_engine.SubnormalDivisor):
        run_plan(con, plan, "polars")
    # Without the check, the reciprocal overflows: 1 / 1e-310 is inf.
    out = polars_engine.run(plan, {"r": con.arrow["r"]}, guards=set())
    assert math.isinf(out["q"].to_pylist()[0])


def test_a_difference_of_zeros_is_the_one_zero():
    """polars-zero-sign: with more than one row, the in-memory engine
    computes `0.0 - x` as `-x`; the sum and difference go through `canon`."""
    rows = [(0, 0.0), (1, 0.0), (2, 0.0)]
    con = connect()
    create_table(con, "r", FLOATS, rows)
    plan = written_plan(
        substrait_json(con, "SELECT 0.0 - x AS a, x + 0.0 AS b FROM r", "reference")
    )
    out = polars_engine.run(plan, {"r": con.arrow["r"]})
    assert all(math.copysign(1.0, v) == 1.0 for c in ("a", "b") for v in out[c].to_pylist())
    assert pl.LazyFrame({"x": [0.0] * 3}).select(pl.lit(0.0) - pl.col("x")).collect(
        engine="in-memory"
    ).row(0) == (-0.0,)


@pytest.mark.parametrize(
    "measure",
    ["COUNT(a)", "MIN(a)", "MAX(a)", "MIN(s)", "MAX(s)"],
)
def test_native_measures_match_lean(measure):
    schema = ibis.schema({"g": "int64", "a": "int64", "s": "string"})
    rows = [(1, None, None), (2, 5, "b"), (2, -3, "a"), (3, 7, "z"), (4, 1, "é"), (4, 1, "e"),
            (5, MIN, "日"), (5, MAX, "本")]  # fmt: skip
    lean, polars = lean_and_polars(schema, rows, f"SELECT g, {measure} AS m FROM r GROUP BY g")
    assert lean == polars


@pytest.mark.parametrize(
    "measure", ["VAR_SAMP(x)", "VAR_POP(x)", "STDDEV_SAMP(x)", "STDDEV_POP(x)"]
)
def test_native_variances_match_lean(measure):
    rows = [(1, None), (2, 1.0), (2, 3.0), (3, 2.0), (4, -0.0), (4, -0.0), (5, 0.5), (5, 1.5),
            (5, -2.5)]  # fmt: skip
    sql = f"SELECT g, {measure} AS m FROM r GROUP BY g"
    lean, polars = lean_and_polars(FLOATS, rows, sql, doubles=True)
    assert [g for g, _ in lean] == [g for g, _ in polars]
    for (_, want), (_, got) in zip(lean, polars, strict=True):
        assert (want is None and got is None) or math.isclose(want, got, abs_tol=1e-6)
    assert all(math.copysign(1.0, m) == 1.0 for _, m in polars if m == 0.0)


def test_variance_of_an_infinity_is_guarded():
    con = connect()
    create_table(con, "r", FLOATS, [(1, math.inf), (1, 1.0)])
    plan = written_plan(
        substrait_json(con, "SELECT g, VAR_POP(x) AS v FROM r GROUP BY g", "reference")
    )
    with pytest.raises(polars_engine.DomainError, match="infinity"):
        polars_engine.run(plan, {"r": con.arrow["r"]})


def test_array_agg_of_nothing_is_null():
    schema = ibis.schema({"g": "int64", "a": "int64"})
    rows = [(1, None), (2, 5), (2, -3)]
    t = ibis.table(schema, name="r")
    plan = written_plan(to_substrait_json(t.group_by("g").agg(l=t.a.collect()).order_by("g")))
    con = connect()
    create_table(con, "r", schema, rows)
    lean = lean_rows(json.dumps(inline_tables(json.loads(plan), {"r": rows})))
    polars = rows_of(polars_engine.run(plan, {"r": con.arrow["r"]}))
    assert lean == polars
    assert polars[0][1] is None


def test_greatest_and_least_of_doubles_put_nan_above_all():
    rows = [(0, math.nan), (1, 1.0), (2, None)]
    sql = "SELECT g, GREATEST(x, 2.0) AS a, LEAST(x, 2.0) AS b, LEAST(x, x) AS c FROM r"
    lean, polars = lean_and_polars(FLOATS, rows, sql, doubles=True)
    assert repr(lean) == repr(polars)


@pytest.mark.parametrize("op", ["bit_and", "bit_or", "bit_xor"])
def test_native_bit_aggregates_match_lean(op):
    schema = ibis.schema({"g": "int64", "a": "int64"})
    rows = [(1, None), (2, 5), (2, -3), (3, 7), (4, MIN), (4, MAX), (4, 6)]
    t = ibis.table(schema, name="r")
    expr = t.group_by("g").agg(m=getattr(t.a, op)()).order_by("g")
    plan = written_plan(to_substrait_json(expr))
    con = connect()
    create_table(con, "r", schema, rows)
    lean = lean_rows(json.dumps(inline_tables(json.loads(plan), {"r": rows})))
    assert lean == rows_of(polars_engine.run(plan, {"r": con.arrow["r"]}))


def test_pow_of_minus_infinity_to_a_half_is_ieee():
    """Polars computes `pow(x, 0.5)` as `sqrt(x)`: NaN for `-inf`, where
    IEEE's `pow` and the reference give `+inf`."""
    df = pl.DataFrame({"x": [-math.inf, -0.0, 4.0], "y": [0.5, 0.5, 0.5]})
    x, y = pl.col("x"), pl.col("y")
    assert math.isnan(df.select(x.pow(0.5))["x"][0])  # a literal exponent
    got = df.select(shims.one_zero(shims.pow_ieee(x, y)).alias("p"))["p"].to_list()
    assert got == [math.inf, 0.0, 2.0]
    assert math.copysign(1.0, got[1]) == 1.0
    rows = [(0, -math.inf), (1, -0.0), (2, 4.0)]
    lean, polars = lean_and_polars(
        FLOATS, rows, "SELECT g, power(x, 0.5) AS p FROM r", doubles=True
    )
    assert repr(lean) == repr(polars)


# --- Streaming in a routed run ---------------------------------------------------


def test_a_routed_run_records_fallbacks_and_can_require_streaming():
    import sverify as sv
    from sverify.errors import RouteError

    t = ibis.table({"k": "int64", "i": "int64"}, name="t")
    con = sv.connect()
    con.put("t", pa.table({"k": [1, 1, 2], "i": [3, 4, 5]}))
    summed = sv.verify(t.group_by("k").aggregate(total=t.i.sum()))
    out = summed.run(con, "polars", route="auto", streaming="require")
    assert sorted(out.to_pylist(), key=lambda r: r["k"]) == [
        {"k": 1, "total": 7},
        {"k": 2, "total": 5},
    ]
    assert summed.routes["polars"].fallbacks == ()
    listed = sv.verify(t.group_by("k").aggregate(l=t.i.collect()))
    listed.run(con, "polars", route="auto")
    (node,) = listed.routes["polars"].fallbacks
    assert "implode" in node
    with pytest.raises(RouteError, match="in-memory engine"):
        listed.run(con, "polars", route="auto", streaming="require")
    with pytest.raises(RouteError, match="in-memory engine"):
        listed.run(con, "polars", streaming="require")


@pytest.mark.parametrize("kind", ["in-memory", "streaming"])
def test_a_guarded_cast_shared_by_two_branches_is_not_hoisted(kind):
    """PL-6 (polars-exec-cse-hoist): common-subexpression elimination moves a
    cast two `when/then` branches share onto every row, where it raises.
    sverify's plans run without it (`_OPTIMIZATIONS`)."""
    x = pl.col("x")
    lf = pl.LazyFrame({"x": ["1", "a"]}).select(
        pl.when(x == "1").then(x.cast(pl.Int64) + 1).alias("a"),
        pl.when(x == "1").then(x.cast(pl.Int64) + 2).alias("b"),
    )
    with pytest.raises(pl.exceptions.InvalidOperationError):
        lf.collect(engine=kind)
    assert lf.collect(engine=kind, optimizations=polars_engine._OPTIMIZATIONS).rows() == [
        (2, 3),
        (None, None),
    ]
    assert polars_engine.collect(lf).rows() == [(2, 3), (None, None)]


@pytest.mark.slow
def test_ties_keep_their_order_in_a_large_streaming_sort():
    """Above the streaming sort's 32 MiB threshold Polars does not keep ties
    in input order without `maintain_order`; the translation's `tie_order`
    shim writes it on every sort."""
    from sverify.engine import written_plan as written

    n = 4_000_000
    k = [(j * 7919) % 5 for j in range(n)]
    tab = pa.table({"k": pa.array(k, pa.int64()), "i": pa.array(range(n), pa.int64())})
    t = ibis.table({"k": "int64", "i": "int64"}, name="t")
    out = pl.DataFrame(polars_engine.run(written(to_substrait_json(t.order_by("k"))), {"t": tab}))

    def stable(df: pl.DataFrame) -> bool:
        """Do the rows of each key come in input order?"""
        steps = df.group_by("k").agg(pl.col("i").diff().drop_nulls().min().alias("d"))
        return steps.select((pl.col("d") > 0).all()).item()

    assert out["k"].is_sorted() and stable(out)
    raw = pl.DataFrame(tab).lazy().sort("k").collect(engine="streaming")
    assert not stable(raw)  # what the shim is for
