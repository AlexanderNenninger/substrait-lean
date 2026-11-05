# ruff: noqa: E501 - the probes are SQL strings, one per line where they fit
"""Probe Snowflake's SQL for the characterization.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The Snowflake counterpart of `sverify_dev.probe_spark`, for
`characterization/snowflake/`.

Each `Obs` is a SQL query whose result is recorded as it is. The queries run
through the Snowflake CLI (`snow sql -c <connection>`), on the maintainer's
account: CI has no Snowflake access, so no test runs them. Every query runs
in a session pinned by `SESSION`: time zone UTC, the result cache off, the
rest of the session's parameters at the account's defaults (the header of
`probes.json` records their values). They run in batches of statements, one
`snow` call each; a batch with an error runs again one statement at a time,
so each error is the result of its own query.

The `writer-*` probes run SQL that `sverify.sql.snowflake` itself writes, so
that a fact can say whether the writer's SQL gives the reference.

`python -m sverify_dev.probe_snowflake --list` prints the queries without
running them; `--write` runs them and writes
`characterization/snowflake/probes.json`, which the facts in
`characterization/snowflake/facts/` cite by `construct`. Keep the inputs
literal and small: every query is a few rows of `VALUES` on an X-Small
warehouse.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_HERE = Path(__file__).resolve()
#: Where `--write` writes: the repository's, when run from a checkout.
OUT = (
    (_HERE.parents[3] if len(_HERE.parents) > 3 else _HERE.parent)
    / "characterization"
    / "snowflake"
    / "probes.json"
)

#: The session parameters every query runs under.
SESSION: dict[str, str] = {
    "TIMEZONE": "'UTC'",
    "USE_CACHED_RESULT": "FALSE",
    "QUERY_TAG": "'sverify-probe'",
}
#: Session parameters whose values the header records: those that change
#: results (the `settings` item of the checklist).
RECORDED = (
    "TIMEZONE",
    "TIMESTAMP_TYPE_MAPPING",
    "TIMESTAMP_NTZ_OUTPUT_FORMAT",
    "TIMESTAMP_OUTPUT_FORMAT",
    "DATE_OUTPUT_FORMAT",
    "TIME_OUTPUT_FORMAT",
    "DATE_INPUT_FORMAT",
    "TIMESTAMP_INPUT_FORMAT",
    "WEEK_START",
    "WEEK_OF_YEAR_POLICY",
    "DEFAULT_NULL_ORDERING",
    "BINARY_OUTPUT_FORMAT",
    "BINARY_INPUT_FORMAT",
    "TIMESTAMP_DAY_IS_ALWAYS_24H",
    "ERROR_ON_NONDETERMINISTIC_MERGE",
    "QUOTED_IDENTIFIERS_IGNORE_CASE",
    "TWO_DIGIT_CENTURY_START",
    "AUTOCOMMIT",
)
BATCH = 25


@dataclass(frozen=True)
class Obs:
    construct: str
    sql: str
    note: str = ""


def _v(*rows: tuple[str, ...], cols: str = "a, b") -> str:
    """`(VALUES …) AS s(cols)` of literal rows."""
    body = ", ".join("(" + ", ".join(r) + ")" for r in rows)
    return f"(VALUES {body}) AS s({cols})"


def _t(x: str) -> str:
    return f"SYSTEM$TYPEOF({x})"


I64_MIN, I64_MAX = -(2**63), 2**63 - 1
N38 = "9" * 38
NAN, INF, NINF, NZERO = (
    "'NaN'::FLOAT",
    "'inf'::FLOAT",
    "'-inf'::FLOAT",
    "'-0.0'::FLOAT",
)


def _integer_probes() -> list[Obs]:
    o: list[Obs] = []
    for name, expr, a, b in (
        ("add", "a + b", I64_MAX, 1),
        ("subtract", "a - b", I64_MIN, 1),
        ("multiply", "a * b", I64_MAX, 2),
        ("negate", "-a", I64_MIN, 1),
        ("abs", "abs(a)", I64_MIN, 1),
        ("div-min", "a / b", I64_MIN, -1),
        ("mod-min", "mod(a, b)", I64_MIN, -1),
        ("percent-min", "a % b", I64_MIN, -1),
    ):
        o.append(
            Obs(
                f"bigint-{name}",
                f"SELECT {expr} AS r, {_t(expr)} AS t FROM {_v((f'{a}::BIGINT', f'{b}::BIGINT'))}",
            )
        )
    o += [
        Obs(
            "int-type-names",
            "SELECT "
            + ", ".join(
                f"{_t(f'1::{t}')}"
                for t in (
                    "TINYINT",
                    "SMALLINT",
                    "INT",
                    "INTEGER",
                    "BIGINT",
                    "BYTEINT",
                    "NUMBER",
                    "DECIMAL",
                    "NUMERIC",
                )
            ),
            "Every integer type is NUMBER(38,0).",
        ),
        Obs(
            "tinyint-no-range",
            f"SELECT a + b AS r, {_t('a + b')} FROM {_v(('127::TINYINT', '1::TINYINT'))}",
        ),
        Obs(
            "number38-add-overflow",
            f"SELECT a + b AS r FROM {_v((f'{N38}::NUMBER(38,0)', '1'))}",
        ),
        Obs(
            "number38-multiply-overflow",
            f"SELECT a * b AS r FROM {_v((f'{I64_MAX}::BIGINT', f'{I64_MAX}::BIGINT'), (f'{10**19}', f'{10**19}'))}",
            "i64 · i64 fits in 38 digits; 10^19 · 10^19 does not.",
        ),
        Obs(
            "number38-multiply-overflow-literal",
            f"SELECT {10**19} * {10**19} AS r",
        ),
        Obs(
            "int-divide",
            f"SELECT a, b, a / b AS q, {_t('a / b')} AS t FROM {_v(('7', '2'), ('-7', '2'), ('7', '-2'), ('1', '3'), ('2', '3'), (str(I64_MAX), '3'))}",
        ),
        Obs(
            "int-divide-scale",
            f"SELECT {_t('a / b')}, a / b FROM {_v(('1::NUMBER(38,0)', '7::NUMBER(38,0)'))} UNION ALL SELECT {_t('a / b')}, a / b FROM {_v(('1::NUMBER(10,2)', '7::NUMBER(10,4)'))}",
        ),
        Obs(
            "int-div-zero",
            f"SELECT a / b FROM {_v(('7', '0'))}",
        ),
        Obs(
            "int-mod-zero",
            f"SELECT mod(a, b) FROM {_v(('7', '0'))}",
        ),
        Obs(
            "int-percent-zero",
            f"SELECT a % b FROM {_v(('7', '0'))}",
        ),
        Obs(
            "int-div0",
            f"SELECT div0(a, b), div0null(a, b), div0(a, c), div0null(a, c) FROM {_v(('7', '0', 'NULL'), cols='a, b, c')}",
        ),
        Obs(
            "int-mod-signs",
            f"SELECT a, b, mod(a, b), a % b, trunc(a / b), floor(a / b) FROM {_v(('-7', '2'), ('7', '-2'), ('-7', '-2'), ('7', '2'))}",
        ),
        Obs(
            "int-divide-rounding",
            f"SELECT a, b, a / b, trunc(a / b), (a / b)::NUMBER(38,0) FROM {_v(('2', '3'), ('-2', '3'), (str(10**17 * 3 - 1), '3'), ('9999999999999999999', '10000000'))}",
            "Whether the 6-digit quotient rounds up to the next integer.",
        ),
        Obs(
            "int-shifts",
            "SELECT n, bitshiftleft(a, n), bitshiftright(a, n), "
            f"{_t('bitshiftleft(a, n)')} FROM "
            + _v(*(("-8", str(n)) for n in (1, 7, 63, 64, 65, 127, 128, 129)), cols="a, n"),
        ),
        Obs(
            "int-shift-bigint",
            f"SELECT bitshiftleft(a, 1), bitshiftleft(a, 63), bitshiftright(a, 1) FROM {_v((f'{I64_MAX}::BIGINT', '0'))}",
        ),
        Obs(
            "int-bitwise",
            f"SELECT bitand(a, b), bitor(a, b), bitxor(a, b), bitnot(a), {_t('bitand(a, b)')} FROM {_v((str(I64_MIN), '-1'), ('-8', '5'))}",
        ),
        Obs(
            "int-bitwise-wide",
            f"SELECT bitand(a, b), bitnot(a) FROM {_v((str(2**64), str(2**64 + 1)), (N38, '1'))}",
        ),
        Obs(
            "int-power",
            f"SELECT power(a, b), {_t('power(a, b)')} FROM {_v(('2', '62'), ('2', '63'), ('2', '64'), ('3', '40'), ('2', '-1'), ('0', '-1'))}",
        ),
    ]
    return o


def _decimal_probes() -> list[Obs]:
    d = "::NUMBER"
    o = [
        Obs(
            "decimal-arith-types",
            "SELECT "
            + ", ".join(
                f"{_t(e)}"
                for e in (
                    f"1.5{d}(5,1) + 2.25{d}(6,2)",
                    f"1.5{d}(5,1) - 2.25{d}(6,2)",
                    f"1.5{d}(5,1) * 2.25{d}(6,2)",
                    f"1.5{d}(5,1) / 2.25{d}(6,2)",
                    f"1{d}(38,10) * 1{d}(38,10)",
                    f"1{d}(38,20) / 3{d}(38,20)",
                    f"-1.5{d}(5,1)",
                    f"abs(-1.5{d}(5,1))",
                    f"mod(7.5{d}(5,1), 2{d}(3,0))",
                )
            ),
        ),
        Obs(
            "decimal-arith-values",
            f"SELECT a + b, a - b, a * b, a / b, mod(a, b) FROM {_v(('1.5::NUMBER(5,1)', '2.25::NUMBER(6,2)'), ('-1.5::NUMBER(5,1)', '0.07::NUMBER(6,2)'))}",
        ),
        Obs(
            "decimal-multiply-scale-cap",
            f"SELECT a * b, {_t('a * b')} FROM {_v(('0.1234567890123::NUMBER(20,13)', '0.1234567890123::NUMBER(20,13)'))}",
            "The product's scale is capped (12, the larger input scale, or 37); whether the dropped digits round or truncate.",
        ),
        Obs(
            "decimal-divide-scale",
            f"SELECT a / b, {_t('a / b')} FROM {_v(('1::NUMBER(10,0)', '3::NUMBER(10,0)'), ('2::NUMBER(10,0)', '3::NUMBER(10,0)'), ('-2::NUMBER(10,0)', '3::NUMBER(10,0)'), ('1.00::NUMBER(10,2)', '8::NUMBER(10,0)'))}",
        ),
        Obs(
            "decimal-rescale-cast",
            f"SELECT x, x::NUMBER(10,1), x::NUMBER(10,0) FROM {_v(('1.25::NUMBER(10,2)',), ('-1.25::NUMBER(10,2)',), ('1.35::NUMBER(10,2)',), ('2.5::NUMBER(10,2)',), ('-2.5::NUMBER(10,2)',), ('0.05::NUMBER(10,2)',), cols='x')}",
        ),
        Obs(
            "decimal-cast-overflow",
            f"SELECT x::NUMBER(3,0) FROM {_v(('1000',), cols='x')}",
        ),
        Obs(
            "decimal-cast-overflow-scale",
            f"SELECT x::NUMBER(3,2) FROM {_v(('9.999',), cols='x')}",
            "Rounding 9.999 to two places gives 10.00, which needs four digits.",
        ),
        Obs(
            "decimal-add-overflow",
            f"SELECT a + b FROM {_v((f'{N38}::NUMBER(38,0)', '1::NUMBER(38,0)'))}",
        ),
        Obs(
            "decimal-add-overflow-scaled",
            f"SELECT a + b, {_t('a + b')} FROM {_v(('9' * 36 + '.99', '0.01'))}",
        ),
        Obs(
            "decimal-round",
            f"SELECT x, round(x), round(x, 1), round(x, -1), trunc(x), floor(x), ceil(x), {_t('round(x, 1)')} FROM {_v(('2.5::NUMBER(10,2)',), ('-2.5::NUMBER(10,2)',), ('2.45::NUMBER(10,2)',), ('-2.45::NUMBER(10,2)',), ('15.00::NUMBER(10,2)',), cols='x')}",
        ),
        Obs(
            "decimal-round-half-even",
            f"SELECT x, round(x, 0, 'HALF_TO_EVEN'), round(x, 0, 'HALF_AWAY_FROM_ZERO') FROM {_v(('2.5::NUMBER(10,1)',), ('3.5::NUMBER(10,1)',), ('-2.5::NUMBER(10,1)',), cols='x')}",
        ),
        Obs(
            "decimal-sum-avg",
            f"SELECT sum(x), {_t('sum(x)')}, avg(x), {_t('avg(x)')} FROM {_v(('1.25::NUMBER(10,2)',), ('2.50::NUMBER(10,2)',), ('0.01::NUMBER(10,2)',), cols='x')}",
        ),
        Obs(
            "decimal-sum-overflow",
            f"SELECT sum(x) FROM {_v((f'{N38}::NUMBER(38,0)',), ('1::NUMBER(38,0)',), cols='x')}",
        ),
        Obs(
            "decimal-to-double",
            f"SELECT x::FLOAT, x::VARCHAR::FLOAT, to_varchar(x::FLOAT) FROM {_v(('0.1::NUMBER(10,1)',), ('1234567890.123456789::NUMBER(38,9)',), ('12345678901234567890123456789::NUMBER(38,0)',), cols='x')}",
        ),
        Obs(
            "decimal-to-int",
            f"SELECT x, x::NUMBER(38,0), trunc(x)::NUMBER(38,0) FROM {_v(('2.5::NUMBER(10,1)',), ('-2.5::NUMBER(10,1)',), ('2.4::NUMBER(10,1)',), ('-0.5::NUMBER(10,1)',), cols='x')}",
        ),
        Obs(
            "decimal-negate-wide",
            f"SELECT -x, abs(x), {_t('-x')} FROM {_v((f'-{N38}::NUMBER(38,0)',), cols='x')}",
        ),
        Obs(
            "decimal-negate-wide-scaled",
            f"SELECT -x, abs(x), {_t('-x')} FROM {_v(('-' + '9' * 37 + '.9',), cols='x')}",
        ),
        Obs(
            "number-past-38-digits",
            f"SELECT a + b, {_t('a + b')}, (a + b)::NUMBER(38,0), to_varchar(a + b), length(to_varchar(a + b)) FROM {_v((f'{N38}::NUMBER(38,0)', '1::NUMBER(38,0)'))}",
            "A sum past 38 digits: is it kept, cast, printed?",
        ),
        Obs(
            "number-past-38-digits-cast",
            f"SELECT (a + b)::NUMBER(38,0) FROM {_v((f'{N38}::NUMBER(38,0)', '1::NUMBER(38,0)'))}",
        ),
        Obs(
            "number-past-38-digits-compare",
            f"SELECT a + b > a, (a + b) - 1 = a, (a + b) * 1 FROM {_v((f'{N38}::NUMBER(38,0)', '1::NUMBER(38,0)'))}",
        ),
        Obs(
            "number-past-128-bits",
            f"SELECT a * b FROM {_v((f'{2**64}::NUMBER(38,0)', f'{2**64}::NUMBER(38,0)'))}",
            "2^128 needs 129 bits.",
        ),
        Obs(
            "number-past-38-digits-sum",
            f"SELECT sum(x), {_t('sum(x)')}, sum(x)::NUMBER(38,0) FROM {_v((f'{N38}::NUMBER(38,0)',), (f'{N38}::NUMBER(38,0)',), cols='x')}",
        ),
    ]
    return o


def _double_probes() -> list[Obs]:
    o = [
        Obs(
            "double-type-names",
            "SELECT "
            + ", ".join(
                _t(f"1::{t}")
                for t in ("FLOAT", "FLOAT4", "FLOAT8", "DOUBLE", "DOUBLE PRECISION", "REAL")
            ),
        ),
        Obs(
            "double-literals",
            f"SELECT {_t('1.5')}, {_t('1e3')}, {_t('1.5e0')}, {_t("'NaN'::FLOAT")}, {_t('-0.0')}, to_varchar(-0.0), to_varchar({NZERO})",
        ),
        Obs(
            "double-special-text",
            "SELECT "
            + ", ".join(
                f"to_varchar('{s}'::FLOAT)"
                for s in (
                    "NaN",
                    "nan",
                    "inf",
                    "-inf",
                    "Infinity",
                    "-Infinity",
                    "INF",
                    "+inf",
                    "-NaN",
                    "1e308",
                    "1e309",
                    "-0",
                    "4.9e-324",
                    "2.5e-324",
                )
            ),
        ),
        Obs(
            "double-arith-nan-creation",
            f"SELECT a - a, a * 0, a / a, b + c FROM {_v((INF, INF, NINF), cols='a, b, c')}",
        ),
        Obs(
            "double-arith-overflow",
            f"SELECT a * 10, a + a, -a * 10, {_t('a * 10')} FROM {_v(('1e308::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-arith-overflow-literal",
            "SELECT 1e308::FLOAT * 10",
        ),
        Obs(
            "double-div-zero",
            f"SELECT a / b FROM {_v(('1::FLOAT', '0::FLOAT'))}",
        ),
        Obs(
            "double-div-zero-cases",
            f"SELECT div0(a, b), div0null(a, b), div0(c, b) FROM {_v(('1::FLOAT', '0::FLOAT', NAN), cols='a, b, c')}",
        ),
        Obs(
            "double-div-negzero",
            f"SELECT a / b FROM {_v(('1::FLOAT', NZERO))}",
        ),
        Obs(
            "double-div-inf",
            f"SELECT a / b, b / a, 1 / a FROM {_v((INF, '2::FLOAT'))}",
        ),
        Obs(
            "double-mod",
            f"SELECT a, b, mod(a, b), a % b FROM {_v(('5.5::FLOAT', '2::FLOAT'), ('-5.5::FLOAT', '2::FLOAT'), ('5.5::FLOAT', '-2::FLOAT'), (INF, '2::FLOAT'), ('5.5::FLOAT', INF), (NAN, '2::FLOAT'))}",
        ),
        Obs(
            "double-mod-zero",
            f"SELECT mod(a, b) FROM {_v(('5.5::FLOAT', '0::FLOAT'))}",
        ),
        Obs(
            "double-rounding",
            f"SELECT a + b, to_varchar(a + b), a * 3, 1 / a FROM {_v(('0.1::FLOAT', '0.2::FLOAT'))}",
        ),
        Obs(
            "double-output-digits",
            "SELECT "
            + ", ".join(
                f"to_varchar({x}::FLOAT), {x}::FLOAT::VARCHAR"
                for x in (
                    "0.1",
                    "1/3",
                    "123456789012345678",
                    "1e21",
                    "1e-7",
                    "100",
                    "2.5",
                    "0.30000000000000004",
                )
            ),
            "How many digits a double prints with.",
        ),
        Obs(
            "double-nan-equality",
            f"SELECT a = b, a < c, a > c, a = a, a <> a, equal_null(a, b), greatest(a, c), least(a, c), {_t('greatest(a, c)')} FROM {_v((NAN, NAN, INF), cols='a, b, c')}",
        ),
        Obs(
            "double-nan-order",
            f"SELECT x FROM {_v((NAN,), (INF,), (NINF,), ('0::FLOAT',), ('NULL',), ('-1::FLOAT',), cols='x')} ORDER BY x",
        ),
        Obs(
            "double-nan-order-desc",
            f"SELECT x FROM {_v((NAN,), (INF,), (NINF,), ('0::FLOAT',), ('NULL',), ('-1::FLOAT',), cols='x')} ORDER BY x DESC",
        ),
        Obs(
            "double-nan-minmax",
            f"SELECT min(x), max(x), count(DISTINCT x) FROM {_v((NAN,), (INF,), ('1::FLOAT',), ('NULL',), cols='x')}",
        ),
        Obs(
            "double-nan-group",
            f"SELECT to_varchar(x), count(*) FROM {_v((NAN,), ("'nan'::FLOAT",), ('0::FLOAT / 0::FLOAT',), ("'-NaN'::FLOAT",), cols='x')} GROUP BY x",
            "0/0 raises; drop this row if it fails.",
        ),
        Obs(
            "double-nan-group-safe",
            f"SELECT to_varchar(x), count(*) FROM {_v((NAN,), ("'nan'::FLOAT",), (f'{INF} - {INF}',), ("'-NaN'::FLOAT",), cols='x')} GROUP BY x",
        ),
        Obs(
            "double-nan-sign",
            f"SELECT to_varchar(-x), to_varchar(x * -1), to_varchar(y - y), to_varchar(-(y - y)), sign(x), {_t('sign(x)')} FROM {_v((NAN, INF), cols='x, y')}",
        ),
        Obs(
            "double-zero-sign",
            f"SELECT to_varchar(a), to_varchar(-b), to_varchar(b * -1), to_varchar(a + b), a = b, a < b, to_varchar(1 / NULLIF(1, 0) * a), sign(a), atan2(a, -1) FROM {_v((NZERO, '0::FLOAT'))}",
        ),
        Obs(
            "double-zero-group",
            f"SELECT to_varchar(x), count(*) FROM {_v((NZERO,), ('0::FLOAT',), ('-0.0::FLOAT',), cols='x')} GROUP BY x",
        ),
        Obs(
            "double-zero-group-first",
            f"SELECT to_varchar(x), count(*) FROM {_v(('0::FLOAT',), (NZERO,), cols='x')} GROUP BY x",
        ),
        Obs(
            "double-zero-distinct-order",
            f"SELECT DISTINCT to_varchar(x) FROM (SELECT x FROM {_v((NZERO,), ('0::FLOAT',), cols='x')} ORDER BY x)",
        ),
        Obs(
            "double-math-domain",
            f"SELECT sqrt(a), asin(b), acos(b), power(a, 0.5), power(0::FLOAT, a) FROM {_v(('-1::FLOAT', '2::FLOAT'))}",
        ),
        Obs(
            "double-sqrt-neg",
            f"SELECT sqrt(a) FROM {_v(('-1::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-asin-out",
            f"SELECT asin(a) FROM {_v(('2::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-ln-zero",
            f"SELECT ln(a) FROM {_v(('0::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-ln-neg",
            f"SELECT ln(a) FROM {_v(('-1::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-log-cases",
            f"SELECT log(10, a), log(2, a), exp(a), {_t('ln(a)')} FROM {_v(('1000::FLOAT',), ('0.001::FLOAT',), cols='a')}",
        ),
        Obs(
            "double-power-neg-frac",
            f"SELECT power(a, b) FROM {_v(('-8::FLOAT', '0.3333333333333333::FLOAT'))}",
        ),
        Obs(
            "double-power-overflow",
            f"SELECT power(a, b), exp(c) FROM {_v(('10::FLOAT', '400::FLOAT', '1000::FLOAT'), cols='a, b, c')}",
        ),
        Obs(
            "double-trig-inf",
            f"SELECT sin(x), cos(x), tan(x) FROM {_v((INF,), cols='x')}",
        ),
        Obs(
            "double-atan2-zero",
            f"SELECT atan2(a, b), atan2(-a, b), atan2(a, -b) FROM {_v(('0::FLOAT', '0::FLOAT'))}",
        ),
        Obs(
            "double-elem-bits",
            f"SELECT to_varchar(sin(x)), to_varchar(exp(x)), to_varchar(ln(x)), to_varchar(power(x, 0.37)), to_varchar(tan(x)), to_varchar(x * x) FROM {_v(('1e22::FLOAT',), ('0.7853981633974483::FLOAT',), ('2.5::FLOAT',), cols='x')}",
            "Last bits of the elementary functions, against C's libm.",
        ),
        Obs(
            "double-elem-hex",
            f"SELECT to_varchar(to_binary(to_varchar(sin(x)), 'UTF-8')) , sin(x)::NUMBER(38,37) FROM {_v(('1e22::FLOAT',), cols='x')}",
            "Fallback if to_varchar does not print 17 digits.",
        ),
        Obs(
            "double-round",
            f"SELECT x, round(x), round(x, 2), round(x, -1), floor(x), ceil(x), trunc(x), {_t('round(x)')}, {_t('floor(x)')} FROM {_v(('2.5::FLOAT',), ('-2.5::FLOAT',), ('0.5::FLOAT',), ('1.5::FLOAT',), ('2.675::FLOAT',), ('1.005::FLOAT',), ('-0.4::FLOAT',), cols='x')}",
        ),
        Obs(
            "double-round-nonfinite",
            f"SELECT round(x), floor(x), ceil(x), round(x, 2), trunc(x) FROM {_v((NAN,), (INF,), (NINF,), ('1e300::FLOAT',), cols='x')}",
        ),
        Obs(
            "double-round-half-even",
            f"SELECT round(x, 0, 'HALF_TO_EVEN') FROM {_v(('2.5::FLOAT',), cols='x')}",
        ),
        Obs(
            "double-fp32",
            f"SELECT to_varchar(a::FLOAT4 + b::FLOAT4), {_t('a::FLOAT4')}, to_varchar(16777217::FLOAT4) FROM {_v(('0.1', '0.2'))}",
        ),
        Obs(
            "double-round-near-half",
            "SELECT x, round(x), to_varchar(round(x)), round(x, 2), floor(x + 0.5) FROM "
            + _v(
                *[
                    (f"'{t}'::FLOAT",)
                    for t in (
                        "0.49999999999999994",
                        "-0.49999999999999994",
                        "267.49999999999997",
                        "2.4999999999999996",
                        "4503599627370497",
                        "1.4999999999999998",
                        "2.675",
                        "1.005",
                        "0.285",
                    )
                ],
                cols="x",
            ),
            "Doubles just below a half: exact rounding gives the lower integer.",
        ),
        Obs(
            "double-round-scaled",
            f"SELECT x * 100, to_varchar(x * 100), round(x * 100), round(x * 100) / 100 FROM {_v(("'2.675'::FLOAT",), cols='x')}",
        ),
        Obs(
            "double-var-shifted",
            "SELECT var_samp(x), var_pop(x), stddev_samp(x), covar_samp(x, x), corr(x, y), var_samp(x - 1000000000) FROM "
            + _v(
                *[
                    (f"'{1000000000 + k}'::FLOAT", f"'{1000000000 + 2 * k + (k % 3)}'::FLOAT")
                    for k in (4, 7, 13, 16)
                ]
            ).replace("AS s(a, b)", "AS s(x, y)"),
            "Welford's example: the exact sample variance is 30.",
        ),
        Obs(
            "double-ieee-ops",
            "SELECT a, b, a * b, a + b, a - b, a / b FROM (VALUES ('-352.3344703336753'::FLOAT, '-698.3016521509962'::FLOAT), ('301.8689460797075'::FLOAT, '-855.1274266649145'::FLOAT), ('71.76400861337834'::FLOAT, '-268.622166174829'::FLOAT), ('-884.0021504505864'::FLOAT, '14.871466378840523'::FLOAT), ('-925.0086831160303'::FLOAT, '-132.70863267522827'::FLOAT), ('-860.2891528507621'::FLOAT, '-818.5739733122699'::FLOAT), ('-150.96162171497213'::FLOAT, '653.7042493440761'::FLOAT), ('-752.3960777007088'::FLOAT, '-553.522070785971'::FLOAT), ('254.86644481117855'::FLOAT, '895.4178849140112'::FLOAT), ('154.20589723499734'::FLOAT, '-206.63905069843963'::FLOAT), ('952.51021118584'::FLOAT, '-906.8346387644874'::FLOAT), ('716.936918097359'::FLOAT, '-420.7814273366474'::FLOAT), ('2.675'::FLOAT, '100'::FLOAT), ('0.1'::FLOAT, '3'::FLOAT), ('1.1'::FLOAT, '1.1'::FLOAT), ('0.7'::FLOAT, '0.1'::FLOAT), ('1e308'::FLOAT, '10'::FLOAT), ('3'::FLOAT, '0.1'::FLOAT)) AS s(a, b)",
            "Products, sums, differences and quotients of doubles, to compare with IEEE's (Python's) results.",
        ),
        Obs(
            "double-mul-number",
            "SELECT a * 100, a * 100::FLOAT, a * '100'::FLOAT, {_t('a * 100')} FROM (VALUES ('2.675'::FLOAT)) AS s(a)".replace(
                "{_t('a * 100')}", "SYSTEM$TYPEOF(a * 100)"
            ),
            "A double times a NUMBER literal, and times a double.",
        ),
        Obs(
            "double-fold-literal",
            "SELECT '2.675'::FLOAT * '100'::FLOAT, '0.1'::FLOAT * '3'::FLOAT, '1.1'::FLOAT * '1.1'::FLOAT, round('2.675'::FLOAT * '100'::FLOAT)",
            "Constant expressions, folded at compile time.",
        ),
        Obs(
            "double-fold-one-row",
            "SELECT a * b, round(a * b) FROM (VALUES ('2.675'::FLOAT, '100'::FLOAT)) AS s(a, b)",
        ),
        Obs(
            "double-fold-two-rows",
            "SELECT a * b, round(a * b) FROM (VALUES ('2.675'::FLOAT, '100'::FLOAT), ('1'::FLOAT, '1'::FLOAT)) AS s(a, b)",
        ),
        Obs(
            "double-fold-subquery",
            "SELECT a * b FROM (SELECT '2.675'::FLOAT AS a, '100'::FLOAT AS b UNION ALL SELECT '0.1'::FLOAT, '3'::FLOAT)",
        ),
        Obs(
            "double-fold-sum",
            "SELECT '0.1'::FLOAT + '0.2'::FLOAT, a + b FROM (VALUES ('0.1'::FLOAT, '0.2'::FLOAT)) AS s(a, b)",
        ),
        Obs(
            "double-var-small",
            "SELECT var_samp(x), var_pop(x), covar_samp(x, x) FROM "
            + _v(*[(f"'{k}'::FLOAT",) for k in (4, 7, 13, 16)], cols="x"),
        ),
        Obs(
            "double-var-1e6",
            "SELECT var_samp(x), var_pop(x) FROM "
            + _v(*[(f"'{1000000 + k}'::FLOAT",) for k in (4, 7, 13, 16)], cols="x"),
        ),
        Obs(
            "double-var-grouped",
            "SELECT g, var_samp(x) FROM "
            + _v(
                *[(str(g), f"'{1000000000 + k}'::FLOAT") for g in (1, 2) for k in (4, 7, 13, 16)],
                cols="g, x",
            )
            + " GROUP BY g ORDER BY g",
        ),
    ]
    return o


def _cast_probes() -> list[Obs]:
    o = [
        Obs(
            "cast-double-to-int",
            f"SELECT x, x::NUMBER(38,0), x::BIGINT, trunc(x)::NUMBER(38,0) FROM {_v(('2.5::FLOAT',), ('-2.5::FLOAT',), ('3.5::FLOAT',), ('0.49999999999999994::FLOAT',), ('-0.5::FLOAT',), ('1e19::FLOAT',), cols='x')}",
        ),
        Obs(
            "cast-double-to-int-big",
            f"SELECT x::NUMBER(38,0) FROM {_v(('1e40::FLOAT',), cols='x')}",
        ),
        Obs(
            "cast-double-to-int-nan",
            f"SELECT x::NUMBER(38,0) FROM {_v((NAN,), cols='x')}",
        ),
        Obs(
            "cast-double-to-int-inf",
            f"SELECT x::NUMBER(38,0) FROM {_v((INF,), cols='x')}",
        ),
        Obs(
            "cast-double-to-decimal",
            f"SELECT x::NUMBER(10,2), x::NUMBER(10,1) FROM {_v(('1.005::FLOAT',), ('2.675::FLOAT',), ('-1.25::FLOAT',), ('0.125::FLOAT',), cols='x')}",
        ),
        Obs(
            "cast-text-to-int",
            "SELECT "
            + ", ".join(
                f"try_cast('{s}' AS NUMBER(38,0))"
                for s in (
                    "12",
                    " 12 ",
                    "+12",
                    "-0",
                    "1e3",
                    "1.5",
                    "2.5",
                    "-2.5",
                    "0x10",
                    "1_000",
                    "",
                    "12a",
                    "9223372036854775808",
                    N38 + "9",
                )
            ),
        ),
        Obs(
            "cast-text-to-int-strict",
            "SELECT 'abc'::NUMBER(38,0)",
        ),
        Obs(
            "cast-text-to-int-strict-row",
            f"SELECT x::NUMBER(38,0) FROM {_v(("'abc'",), cols='x')}",
        ),
        Obs(
            "cast-text-to-double",
            "SELECT "
            + ", ".join(
                f"to_varchar(try_cast('{s}' AS FLOAT))"
                for s in (
                    "1.5",
                    " 1.5 ",
                    "1e3",
                    "1E-3",
                    ".5",
                    "5.",
                    "+1",
                    "NaN",
                    "nan",
                    "inf",
                    "Infinity",
                    "-Infinity",
                    "1e400",
                    "0x1p3",
                    "1,5",
                    "",
                )
            ),
        ),
        Obs(
            "cast-text-to-bool",
            "SELECT "
            + ", ".join(
                f"try_cast('{s}' AS BOOLEAN)"
                for s in (
                    "true",
                    "TRUE",
                    "t",
                    "yes",
                    "y",
                    "on",
                    "1",
                    "false",
                    "f",
                    "no",
                    "off",
                    "0",
                    " true",
                    "2",
                    "",
                )
            ),
        ),
        Obs(
            "cast-number-to-bool",
            f"SELECT x::BOOLEAN FROM {_v(('0',), ('1',), ('2',), ('-1',), ('0.5',), cols='x')}",
        ),
        Obs(
            "cast-text-to-date",
            "SELECT "
            + ", ".join(
                f"to_varchar(try_cast('{s}' AS DATE))"
                for s in (
                    "2024-01-05",
                    "2024-1-5",
                    " 2024-01-05",
                    "2024-01-05 ",
                    "2024-02-30",
                    "2024-02-29",
                    "2023-02-29",
                    "0001-01-01",
                    "9999-12-31",
                    "10000-01-01",
                    "-0001-01-01",
                    "05/01/2024",
                    "2024-01-05T10:00:00",
                    "20240105",
                    "1704412800",
                )
            ),
        ),
        Obs(
            "cast-text-to-timestamp",
            "SELECT "
            + ", ".join(
                f"try_cast('{s}' AS TIMESTAMP_NTZ(6))"
                for s in (
                    "2024-01-05 10:00:00",
                    "2024-01-05T10:00:00",
                    "2024-01-05 10:00:00.1234567",
                    "2024-01-05 10:00:00+02:00",
                    "2024-01-05",
                    "2024-01-05 24:00:00",
                    "1704412800",
                    "2024-01-05 10:00:60",
                )
            ),
        ),
        Obs(
            "cast-to-text",
            "SELECT "
            + ", ".join(
                f"to_varchar({x}), {x}::VARCHAR"
                for x in (
                    "TRUE",
                    "12::NUMBER(38,0)",
                    "1.50::NUMBER(10,2)",
                    "-0.5::NUMBER(10,1)",
                    "1.5::FLOAT",
                    "1e20::FLOAT",
                    "'2024-01-05'::DATE",
                    "'2024-01-05 10:00:00.123'::TIMESTAMP_NTZ(6)",
                    "'10:00:00'::TIME",
                )
            ),
        ),
        Obs(
            "cast-try-non-string",
            f"SELECT try_cast(x AS NUMBER(38,0)) FROM {_v(('1.5::FLOAT',), cols='x')}",
            "TRY_CAST is documented for string input only.",
        ),
        Obs(
            "cast-try-functions",
            "SELECT try_to_number('1.5'), try_to_number('1.5', 10, 1), try_to_double('x'), try_to_date('2024-02-30'), try_to_boolean('maybe'), try_to_number('"
            + N38
            + "9')",
        ),
        Obs(
            "cast-try-overflow",
            "SELECT try_cast('1000' AS NUMBER(3,0)), try_cast('9.999' AS NUMBER(3,2))",
        ),
        Obs(
            "cast-int-to-double-precision",
            f"SELECT to_varchar(x::FLOAT), x::FLOAT::NUMBER(38,0) FROM {_v((str(2**53 + 1),), (str(I64_MAX),), cols='x')}",
        ),
    ]
    return o


def _null_probes() -> list[Obs]:
    b = ("TRUE", "FALSE", "NULL::BOOLEAN")
    rows = [(x, y) for x in b for y in b]
    return [
        Obs(
            "kleene",
            f"SELECT a, b, a AND b, a OR b, NOT a, a = b, a IS DISTINCT FROM b, equal_null(a, b), coalesce(a, FALSE) FROM {_v(*rows)}",
        ),
        Obs(
            "bool-aggregates-nulls",
            f"SELECT booland_agg(x), boolor_agg(x), boolxor_agg(x), count(x), count(*) FROM {_v(('TRUE',), ('NULL::BOOLEAN',), cols='x')}",
        ),
        Obs(
            "bool-aggregates-only-nulls",
            f"SELECT booland_agg(x), boolor_agg(x) FROM {_v(('NULL::BOOLEAN',), cols='x')}",
        ),
        Obs(
            "null-functions",
            "SELECT concat('a', NULL), 'a' || NULL, concat_ws('-', 'a', NULL, 'b'), greatest(1, NULL), least(1, NULL), "
            "greatest_ignore_nulls(1, NULL), least_ignore_nulls(NULL, 2), abs(NULL), length(NULL), "
            "array_construct(1, NULL)",
        ),
        Obs(
            "null-join-keys",
            f"SELECT l.k, r.k FROM {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS l(')} JOIN {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS r(')} ON l.k = r.k",
        ),
        Obs(
            "null-join-keys-not-distinct",
            f"SELECT l.k, r.k FROM {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS l(')} JOIN {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS r(')} ON l.k IS NOT DISTINCT FROM r.k ORDER BY 1",
        ),
        Obs(
            "null-join-equal-null",
            f"SELECT l.k, r.k FROM {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS l(')} JOIN {_v(('1',), ('NULL',), cols='k').replace('AS s(', 'AS r(')} ON equal_null(l.k, r.k) ORDER BY 1",
        ),
        Obs(
            "null-in-list",
            f"SELECT x IN (1, NULL), x NOT IN (2, NULL), x IN (SELECT 1 UNION ALL SELECT NULL) FROM {_v(('1',), ('3',), cols='x')}",
        ),
        Obs(
            "null-group",
            f"SELECT x, count(*) FROM {_v(('NULL',), ('NULL',), ('1',), cols='x')} GROUP BY x ORDER BY x",
        ),
    ]


def _string_probes() -> list[Obs]:
    return [
        Obs(
            "str-length",
            "SELECT length('héllo'), len('héllo'), octet_length('héllo'), octet_length(to_binary('héllo', 'UTF-8')), length('😀'), length('é'), length('')",
        ),
        Obs(
            "str-case",
            "SELECT upper('straße'), lower('İ'), upper('ǆ'), initcap('ǆa'), lower('ΣΑΣ'), upper('ﬁ'), upper('é')",
        ),
        Obs(
            "str-trailing-spaces",
            "SELECT 'a' = 'a ', 'a' < 'a ', length('a '), 'a '::CHAR(3) = 'a', length('a'::CHAR(3)), 'a'::CHAR(3) || 'b'",
        ),
        Obs(
            "str-compare-bytes",
            f"SELECT x FROM {_v(("'b'",), ("'B'",), ("'a'",), ("'é'",), ("'z'",), ("'Z'",), ("'😀'",), ("'Ａ'",), ("''",), cols='x')} ORDER BY x",
        ),
        Obs(
            "str-compare-ops",
            "SELECT 'B' < 'a', 'é' > 'z', '😀' > '￿', 'a' < 'ab', 'Z' < 'a'",
        ),
        Obs(
            "str-collation",
            "SELECT 'a' = 'A' COLLATE 'en-ci', 'a' < 'B' COLLATE 'en', collation('a' COLLATE 'en-ci'), 'a ' = 'a' COLLATE 'en-rtrim', upper('a' COLLATE 'en-ci')",
        ),
        Obs(
            "str-like",
            "SELECT 'Abc' LIKE 'a%', 'Abc' ILIKE 'a%', 'a_c' LIKE 'a\\\\_c', 'abc' LIKE 'a\\\\_c', 'a%' LIKE 'a\\\\%', 'a\\\\b' LIKE 'a\\\\\\\\b', 'abc' LIKE 'a!_c' ESCAPE '!', 'a_c' LIKE 'a!_c' ESCAPE '!'",
            "Whether a backslash escapes in LIKE without an ESCAPE clause.",
        ),
        Obs(
            "str-like-escape-backslash",
            "SELECT 'a_c' LIKE 'a\\\\_c' ESCAPE '\\\\', 'abc' LIKE 'a\\\\_c' ESCAPE '\\\\', 'ab\\\\' LIKE 'ab\\\\' ESCAPE '\\\\'",
        ),
        Obs(
            "str-like-multiline",
            "SELECT 'a\\nb' LIKE 'a%b', 'a\\nb' LIKE 'a_b'",
        ),
        Obs(
            "str-literal-escapes",
            "SELECT length('a\\\\b'), length('a\\nb'), 'a\\tb', length('\\u00e9'), length('it''s'), $$a\\nb$$",
        ),
        Obs(
            "str-substr",
            "SELECT substr('hello', 0, 2), substr('hello', 1, 2), substr('hello', -2), substr('hello', -2, 1), substr('hello', 2, -1), substr('hello', 2, 0), substr('hello', 9), substr('hello', -9, 3), substr('héllo', 2, 2), substr('hello', 4294967297, 1)",
        ),
        Obs(
            "str-position",
            "SELECT position('' IN 'abc'), position('z' IN 'abc'), position('l' IN 'héllo'), position('L' IN 'hello'), charindex('l', 'hello'), position('l', 'hello', 4), position('' IN ''), contains('abc', ''), startswith('abc', ''), endswith('abc', '')",
        ),
        Obs(
            "str-position-null-empty",
            "SELECT POSITION(n IN h) AS p FROM (VALUES (NULL, 'a'), ('a', NULL), (NULL, ''), ('', NULL), ('', ''), ('abc', ''), ('héllo', 'l'), ('abc', 'z')) AS s(h, n)",
            "NULL with a NULL argument; an empty needle is found at 1, in an empty string too.",
        ),
        Obs(
            "str-match-case",
            "SELECT contains('Abc', 'a'), startswith('Abc', 'a'), endswith('abC', 'c'), position('A' IN 'abc'), regexp_like('Abc', 'a.*'), regexp_like('Abc', 'a.*', 'i')",
        ),
        Obs(
            "str-trim",
            "SELECT trim('xxaxx', 'x'), ltrim('xyaxy', 'xy'), rtrim('aé é', ' é'), trim('  a  '), trim('\\ta\\t'), length(trim('\\ta\\t'))",
        ),
        Obs(
            "str-regex",
            "SELECT regexp_instr('aé1', '\\\\d'), regexp_instr('é', '\\\\w'), regexp_instr('\\u00a0', '\\\\s'), regexp_instr('٣', '\\\\d'), regexp_like('abc', 'b'), regexp_like('abc', '.*b.*'), regexp_replace('abc', '(b)', '[\\\\1]'), regexp_replace('abc', 'b', '$0'), regexp_substr('abc', 'z')",
        ),
        Obs(
            "str-regex-lookahead",
            "SELECT regexp_like('ab', 'a(?=b)b')",
        ),
        Obs(
            "str-substr-wrap",
            "SELECT substr('hello', 4294967298, 1), substr('hello', 2, 4294967296), substr('hello', 2, 4294967297), substr('hello', -4294967295, 1), substr('hello', 2147483648, 1), substr('hello', 9223372036854775807, 1)",
            "Positions past 32 bits.",
        ),
        Obs(
            "str-substr-wrap-negative",
            "SELECT substr('hello', -4294967296, 2), substr('hello', -9223372036854775808, 1)",
        ),
        Obs(
            "str-position-wrap",
            "SELECT position('l', 'hello', 4294967297), position('l', 'hello', 4294967300)",
        ),
        Obs(
            "str-substr-int32",
            "SELECT substr('hello', 4294967295, 1), substr('hello', 2, 2147483648), substr('hello', 2, 3000000000), substr('hello', 2, 2147483647), substr('hello', 2147483647, 1), substr('hello', 2, 4611686018427387904)",
            "Positions and lengths inside the reference's range, from 2^31 on.",
        ),
        Obs(
            "str-regex-invalid",
            "SELECT regexp_instr('abc', '(')",
        ),
        Obs(
            "str-regex-dialect",
            "SELECT regexp_like('aaa', 'a{2,}'), regexp_like('ab', '[[:alpha:]]+'), regexp_like('a.b', 'a\\\\.b'), regexp_instr('foo bar', '\\\\bbar'), regexp_like('AB', '(?i)ab')",
        ),
        Obs(
            "str-digests",
            "SELECT md5('abc'), md5('é'), sha1('abc'), sha2('abc', 256), sha2('é', 256), sha2('abc', 512), md5(NULL), md5_binary('abc')",
        ),
        Obs(
            "str-concat-types",
            "SELECT concat('a', 1), 'a' || 1.50, 'a' || 1.5::FLOAT, 'a' || TRUE, 'a' || '2024-01-05'::DATE, "
            + _t("'a' || 1"),
        ),
        Obs(
            "str-editdistance",
            "SELECT editdistance('kitten', 'sitting'), editdistance('é', 'e'), editdistance('', 'abc'), editdistance(NULL, 'a')",
        ),
        Obs(
            "str-pad-repeat",
            "SELECT lpad('abc', 5, 'xy'), lpad('abcdef', 3, 'x'), rpad('é', 3, 'ü'), repeat('ab', 3), repeat('ab', -1), lpad('a', -1, 'x'), reverse('héllo')",
        ),
        Obs(
            "str-size-limit",
            "SELECT length(repeat('a', 16777216)), length(repeat('a', 134217728))",
        ),
        Obs(
            "str-size-limit-over",
            "SELECT length(repeat('a', 134217729))",
        ),
    ]


def _temporal_probes() -> list[Obs]:
    ts = "::TIMESTAMP_NTZ(6)"
    return [
        Obs(
            "ts-type-names",
            "SELECT "
            + ", ".join(
                _t(f"'2024-01-05 10:00:00'::{t}")
                for t in (
                    "TIMESTAMP",
                    "DATETIME",
                    "TIMESTAMP_NTZ",
                    "TIMESTAMP_NTZ(6)",
                    "TIMESTAMP_LTZ",
                    "TIMESTAMP_TZ",
                    "DATE",
                    "TIME",
                )
            ),
        ),
        Obs(
            "ts-parts-millisecond",
            f"SELECT date_part(MILLISECOND, x) FROM {_v((f"'2024-05-05 10:20:30.123456'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-parts-microsecond",
            f"SELECT date_part(MICROSECOND, x) FROM {_v((f"'2024-05-05 10:20:30.123456'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-precision",
            f"SELECT '2024-01-05 10:00:00.1234567'{ts}, '2024-01-05 10:00:00.9999999'{ts}, '2024-01-05 10:00:00.1234565'::TIMESTAMP_NTZ(6), '2024-01-05 10:00:00.123456789'::TIMESTAMP_NTZ(9)::TIMESTAMP_NTZ(6)",
            "Does a cast to fewer fractional digits truncate or round?",
        ),
        Obs(
            "ts-dateadd-us",
            f"SELECT dateadd(MICROSECOND, 1, x), {_t('dateadd(MICROSECOND, 1, x)')}, dateadd(MICROSECOND, -1, x), dateadd(MICROSECOND, 86400000000, x), datediff(MICROSECOND, x, y) FROM {_v((f"'2024-01-05 10:00:00'{ts}", f"'2024-01-05 09:59:59.999999'{ts}"), cols='x, y')}",
        ),
        Obs(
            "ts-datediff-boundaries",
            f"SELECT datediff(MONTH, a, b), datediff(YEAR, a, b), datediff(DAY, a, b), datediff(SECOND, c, d), datediff(MICROSECOND, c, d) FROM {_v(("'2024-01-31'::DATE", "'2024-02-01'::DATE", f"'2024-01-05 10:00:00.999999'{ts}", f"'2024-01-05 10:00:01.000001'{ts}"), cols='a, b, c, d')}",
        ),
        Obs(
            "ts-datediff-us-range",
            f"SELECT datediff(MICROSECOND, a, b), {_t('datediff(MICROSECOND, a, b)')} FROM {_v((f"'0001-01-01 00:00:00'{ts}", f"'9999-12-31 23:59:59.999999'{ts}"))}",
        ),
        Obs(
            "ts-epoch-us",
            f"SELECT date_part(EPOCH_MICROSECOND, x), date_part(EPOCH_SECOND, x), to_timestamp_ntz(date_part(EPOCH_MICROSECOND, x), 6) FROM {_v((f"'1969-12-31 23:59:59.5'{ts}",), (f"'0001-01-01 00:00:00'{ts}",), (f"'9999-12-31 23:59:59.999999'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-to-timestamp-scale",
            "SELECT "
            + ", ".join(
                f"to_varchar(to_timestamp_ntz({x}))"
                for x in (
                    "-1, 6",
                    "1704412800000000, 6",
                    "1704412800, 0",
                    "1704412800123, 3",
                    "253402300800000000, 6",
                )
            ),
        ),
        Obs(
            "date-range",
            f"SELECT to_varchar(dateadd(DAY, -1, a)), to_varchar(dateadd(DAY, 1, b)), to_varchar(dateadd(YEAR, 1, b)), {_t('dateadd(DAY, 1, b)')} FROM {_v(("'0001-01-01'::DATE", "'9999-12-31'::DATE"))}",
        ),
        Obs(
            "date-range-far",
            f"SELECT to_varchar(dateadd(DAY, 10000000, a)), to_varchar(dateadd(YEAR, 300000, a)) FROM {_v(("'2024-01-01'::DATE",), cols='a')}",
        ),
        Obs(
            "date-range-overflow",
            f"SELECT to_varchar(dateadd(DAY, 2147483647, a)) FROM {_v(("'2024-01-01'::DATE",), cols='a')}",
        ),
        Obs(
            "ts-range",
            f"SELECT to_varchar(dateadd(MICROSECOND, -1, a)), to_varchar(dateadd(MICROSECOND, 1, b)) FROM {_v((f"'0001-01-01 00:00:00'{ts}", f"'9999-12-31 23:59:59.999999'{ts}"))}",
        ),
        Obs(
            "date-add-months",
            f"SELECT dateadd(MONTH, 1, a), add_months(a, 1), dateadd(MONTH, 1, b), add_months(b, 1), dateadd(MONTH, -1, c), add_months(c, 1), dateadd(YEAR, 1, d) FROM {_v(("'2024-01-31'::DATE", "'2024-04-30'::DATE", "'2024-03-31'::DATE", "'2024-02-29'::DATE"), cols='a, b, c, d')}",
            "ADD_MONTHS keeps the end of a month; DATEADD may not.",
        ),
        Obs(
            "date-arith",
            f"SELECT a + 1, a - 1, b - a, {_t('b - a')}, a + INTERVAL '1 day', {_t("a + INTERVAL '1 day'")}, a + INTERVAL '1 hour', {_t("a + INTERVAL '1 hour'")} FROM {_v(("'2024-01-31'::DATE", "'2024-03-01'::DATE"))}",
        ),
        Obs(
            "ts-interval-month",
            f"SELECT x + INTERVAL '1 month', x - INTERVAL '1 year', {_t("x + INTERVAL '1 month'")} FROM {_v((f"'2024-01-31 10:00:00'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-interval-units",
            f"SELECT x + INTERVAL '1 day, 2 hours', x + INTERVAL '1 microsecond', x + INTERVAL '1500 milliseconds' FROM {_v((f"'2024-01-31 10:00:00'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-interval-compound",
            f"SELECT x + INTERVAL '1 day 2 hours' FROM {_v((f"'2024-01-31 10:00:00'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-interval-fraction",
            f"SELECT x + INTERVAL '1.5 seconds' FROM {_v((f"'2024-01-31 10:00:00'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-minus-ts",
            f"SELECT to_varchar(b - a), {_t('b - a')}, datediff(SECOND, a, b) FROM {_v((f"'2024-01-05 10:00:00'{ts}", f"'2024-01-06 11:00:00'{ts}"))}",
        ),
        Obs(
            "time-arith",
            f"SELECT timeadd(HOUR, 2, t), dateadd(HOUR, 25, t), t + INTERVAL '2 hours', datediff(SECOND, t, u), {_t('timeadd(HOUR, 2, t)')} FROM {_v(("'23:00:00'::TIME", "'01:00:00'::TIME"), cols='t, u')}",
        ),
        Obs(
            "time-month",
            f"SELECT dateadd(MONTH, 1, t) FROM {_v(("'23:00:00'::TIME",), cols='t')}",
        ),
        Obs(
            "time-parse",
            "SELECT try_cast('24:00:00' AS TIME), try_cast('23:59:60' AS TIME), try_cast('10:00:00.123456789' AS TIME), "
            + _t("'10:00:00'::TIME"),
        ),
        Obs(
            "week-parts",
            f"SELECT d, dayofweek(d), dayofweekiso(d), week(d), weekiso(d), yearofweek(d), yearofweekiso(d), date_trunc('WEEK', d), dayofyear(d), extract(dow FROM d), extract(dayofweek_iso FROM d) FROM {_v(*[(f"'{x}'::DATE",) for x in ('2021-01-01', '2021-01-03', '2021-01-04', '2024-12-30', '2026-11-05', '1969-12-29')], cols='d')} ORDER BY d",
        ),
        Obs(
            "week-parts-pre-1970",
            f"SELECT d, year(d), month(d), day(d), weekiso(d), dayofweekiso(d), date_trunc('MONTH', d), date_part(EPOCH_SECOND, d::TIMESTAMP_NTZ) FROM {_v(*[(f"'{x}'::DATE",) for x in ('0001-01-01', '1582-10-10', '1900-03-01', '1969-12-31')], cols='d')} ORDER BY d",
            "1582-10-10 falls in the Julian–Gregorian gap: proleptic Gregorian or not.",
        ),
        Obs(
            "ts-parts",
            f"SELECT hour(x), minute(x), second(x), extract(NANOSECOND FROM x), date_trunc('SECOND', x), date_trunc('MILLISECOND', x), date_trunc('QUARTER', x) FROM {_v((f"'2024-05-05 10:20:30.123456'{ts}",), cols='x')}",
        ),
        Obs(
            "ts-time-zones",
            "SELECT convert_timezone('America/New_York', 'UTC', '2024-03-10 02:30:00'::TIMESTAMP_NTZ), convert_timezone('America/New_York', 'UTC', '2024-11-03 01:30:00'::TIMESTAMP_NTZ), convert_timezone('UTC', 'America/New_York', '2024-03-10 07:30:00'::TIMESTAMP_NTZ), convert_timezone('Europe/Berlin', '2024-03-31 01:30:00 +00:00'::TIMESTAMP_TZ)",
            "A DST gap (02:30 on 2024-03-10 does not exist in New York) and an overlap (01:30 on 2024-11-03 is twice).",
        ),
        Obs(
            "ts-ltz-session",
            "ALTER SESSION SET TIMEZONE = 'America/New_York'; SELECT '2024-03-10 02:30:00'::TIMESTAMP_LTZ, '2024-11-03 01:30:00'::TIMESTAMP_LTZ, '2024-01-05 10:00:00'::TIMESTAMP_LTZ::TIMESTAMP_NTZ, to_varchar('2024-01-05 10:00:00 +00:00'::TIMESTAMP_TZ::TIMESTAMP_NTZ)",
            "Under a session time zone with DST; the result is the last statement's.",
        ),
        Obs(
            "ts-tz-compare",
            "SELECT '2024-01-05 10:00:00 +00:00'::TIMESTAMP_TZ = '2024-01-05 11:00:00 +01:00'::TIMESTAMP_TZ, '2024-01-05 10:00:00'::TIMESTAMP_NTZ = '2024-01-05 10:00:00'::TIMESTAMP_LTZ",
        ),
        Obs(
            "ts-day-is-24h",
            "SELECT dateadd(DAY, 1, '2024-03-09 12:00:00 -05:00'::TIMESTAMP_TZ), dateadd(DAY, 1, '2024-03-09 12:00:00'::TIMESTAMP_LTZ)",
        ),
    ]


def _aggregate_probes() -> list[Obs]:
    big = str(I64_MAX)
    return [
        Obs(
            "agg-sum-int",
            f"SELECT sum(x), {_t('sum(x)')}, avg(x), {_t('avg(x)')} FROM {_v((big,), (big,), cols='x')}",
        ),
        Obs(
            "agg-sum-int-bigint",
            f"SELECT sum(x), {_t('sum(x)')} FROM {_v((f'{big}::BIGINT',), (f'{big}::BIGINT',), (f'-{big}::BIGINT',), cols='x')}",
        ),
        Obs(
            "agg-avg-int",
            f"SELECT avg(x), {_t('avg(x)')}, avg(x::BIGINT) FROM {_v(('1',), ('2',), ('2',), cols='x')}",
        ),
        Obs(
            "agg-avg-int-neg",
            f"SELECT avg(x) FROM {_v(('-1',), ('-2',), cols='x')} UNION ALL SELECT avg(x) FROM {_v(('1',), ('1',), ('1',), ('0',), ('0',), ('0',), ('0',), ('0',), ('0',), cols='x')}",
            "Rounding of AVG past its scale.",
        ),
        Obs(
            "agg-empty",
            f"SELECT sum(x), count(x), count(*), min(x), max(x), avg(x), booland_agg(x > 0), listagg(x::VARCHAR), array_agg(x), var_samp(x), median(x) FROM {_v(('1',), cols='x')} WHERE x > 5",
        ),
        Obs(
            "agg-empty-grouped",
            f"SELECT x, sum(x) FROM {_v(('1',), cols='x')} WHERE x > 5 GROUP BY x",
        ),
        Obs(
            "agg-only-nulls",
            f"SELECT sum(x), count(x), avg(x), min(x), listagg(x::VARCHAR), array_agg(x) FROM {_v(('NULL::NUMBER',), ('NULL::NUMBER',), cols='x')}",
        ),
        Obs(
            "agg-sum-double-order",
            f"SELECT sum(x), to_varchar(sum(x)) FROM {_v(('1e20::FLOAT',), ('1::FLOAT',), ('-1e20::FLOAT',), cols='x')} UNION ALL SELECT sum(x), to_varchar(sum(x)) FROM {_v(('1::FLOAT',), ('1e20::FLOAT',), ('-1e20::FLOAT',), cols='x')}",
        ),
        Obs(
            "agg-sum-double-precision",
            f"SELECT to_varchar(sum(x)), to_varchar(avg(x)) FROM {_v(*[('0.1::FLOAT',)] * 10, cols='x')}",
            "A naive left-to-right sum of ten 0.1 is 0.9999999999999999.",
        ),
        Obs(
            "agg-nonfinite",
            f"SELECT sum(x), avg(x), min(x), max(x), var_pop(x), stddev(x) FROM {_v((INF,), (NINF,), ('1::FLOAT',), cols='x')}",
        ),
        Obs(
            "agg-nonfinite-nan",
            f"SELECT sum(x), avg(x), min(x), max(x), var_pop(x) FROM {_v((NAN,), ('1::FLOAT',), cols='x')}",
        ),
        Obs(
            "agg-sum-double-overflow",
            f"SELECT sum(x) FROM {_v(('1.7e308::FLOAT',), ('1.7e308::FLOAT',), cols='x')}",
        ),
        Obs(
            "agg-var",
            f"SELECT var_samp(x), var_pop(x), stddev_samp(x), stddev_pop(x), variance(x), stddev(x), {_t('var_samp(x)')} FROM {_v(('1e9 + 4',), ('1e9 + 7',), ('1e9 + 13',), ('1e9 + 16',), cols='x')}",
            "The exact sample variance is 30 (Welford's example); a naive sum of squares loses it.",
        ),
        Obs(
            "agg-var-double",
            f"SELECT to_varchar(var_samp(x)), to_varchar(var_pop(x)) FROM {_v(('1e9::FLOAT + 4',), ('1e9::FLOAT + 7',), ('1e9::FLOAT + 13',), ('1e9::FLOAT + 16',), cols='x')}",
        ),
        Obs(
            "agg-var-shifted",
            f"SELECT to_varchar(var_samp(x)) FROM {_v(('1e15::FLOAT + 4',), ('1e15::FLOAT + 7',), ('1e15::FLOAT + 13',), ('1e15::FLOAT + 16',), cols='x')}",
        ),
        Obs(
            "agg-var-degenerate",
            f"SELECT var_samp(x), var_pop(x), stddev_samp(x), covar_samp(x, y), covar_pop(x, y), corr(x, y) FROM {_v(('1::FLOAT', '2::FLOAT'), cols='x, y')}",
        ),
        Obs(
            "agg-corr-constant",
            f"SELECT corr(x, y), covar_samp(x, y), regr_slope(y, x) FROM {_v(('1::FLOAT', '5::FLOAT'), ('2::FLOAT', '5::FLOAT'), ('3::FLOAT', '5::FLOAT'), cols='x, y')}",
        ),
        Obs(
            "agg-var-int-type",
            f"SELECT var_samp(x), {_t('var_samp(x)')}, stddev(x), {_t('stddev(x)')}, corr(x, x), {_t('corr(x, x)')} FROM {_v(('1',), ('2',), ('4',), cols='x')}",
        ),
        Obs(
            "agg-quantiles",
            f"SELECT median(x), percentile_cont(0.25) WITHIN GROUP (ORDER BY x), percentile_disc(0.25) WITHIN GROUP (ORDER BY x), percentile_cont(0.5) WITHIN GROUP (ORDER BY x), percentile_disc(0.5) WITHIN GROUP (ORDER BY x), {_t('median(x)')}, {_t('percentile_disc(0.5) WITHIN GROUP (ORDER BY x)')} FROM {_v(('1',), ('2',), ('4',), ('10',), cols='x')}",
        ),
        Obs(
            "agg-quantiles-double",
            f"SELECT median(x), percentile_cont(0.1) WITHIN GROUP (ORDER BY x), {_t('median(x)')} FROM {_v(('1::FLOAT',), ('2::FLOAT',), cols='x')}",
        ),
        Obs(
            "agg-tie-pick",
            f"SELECT mode(x), any_value(y), min_by(y, x), max_by(y, x), array_agg(y) FROM {_v(('1', "'a'"), ('2', "'b'"), ('1', "'c'"), ('2', "'d'"), cols='x, y')}",
        ),
        Obs(
            "agg-array-agg-order",
            f"SELECT array_agg(y) WITHIN GROUP (ORDER BY x), listagg(y, ',') WITHIN GROUP (ORDER BY x) FROM {_v(('1', "'a'"), ('0', "'b'"), ('1', "'c'"), ('0', "'d'"), cols='x, y')}",
        ),
        Obs(
            "agg-bit",
            f"SELECT bitand_agg(x), bitor_agg(x), bitxor_agg(x), {_t('bitand_agg(x)')} FROM {_v(('-8',), ('5',), ('NULL',), cols='x')}",
        ),
        Obs(
            "agg-count-distinct-nan-zero",
            f"SELECT count(DISTINCT x), count(DISTINCT y) FROM {_v((NAN, NZERO), ("'nan'::FLOAT", '0::FLOAT'), cols='x, y')}",
        ),
    ]


def _window_probes() -> list[Obs]:
    rows = _v(("1", "1"), ("1", "1"), ("1", "2"), ("1", "NULL"), ("2", "5"), cols="p, x")
    return [
        Obs(
            "window-default-frame",
            f"SELECT p, x, sum(x) OVER (PARTITION BY p ORDER BY x), count(*) OVER (PARTITION BY p ORDER BY x), sum(x) OVER (PARTITION BY p), first_value(x) OVER (PARTITION BY p ORDER BY x), last_value(x) OVER (PARTITION BY p ORDER BY x) FROM {rows} ORDER BY p, x NULLS LAST",
            "RANGE frames take peers; ROWS frames do not.",
        ),
        Obs(
            "window-ranks",
            f"SELECT p, x, rank() OVER (PARTITION BY p ORDER BY x), dense_rank() OVER (PARTITION BY p ORDER BY x), percent_rank() OVER (PARTITION BY p ORDER BY x), cume_dist() OVER (PARTITION BY p ORDER BY x), row_number() OVER (PARTITION BY p ORDER BY x) FROM {rows} ORDER BY p, x NULLS LAST",
        ),
        Obs(
            "window-null-order",
            f"SELECT x, row_number() OVER (ORDER BY x), row_number() OVER (ORDER BY x DESC) FROM {_v(('1',), ('NULL',), ('2',), cols='x')} ORDER BY x NULLS LAST",
        ),
        Obs(
            "window-ntile",
            f"SELECT x, ntile(3) OVER (ORDER BY x), ntile(4) OVER (ORDER BY x) FROM {_v(*[(str(i),) for i in range(1, 8)], cols='x')} ORDER BY x",
        ),
        Obs(
            "window-lag-lead",
            f"SELECT x, lag(x) OVER (ORDER BY x), lag(x, 2, -1) OVER (ORDER BY x), lead(x, 1, -1) OVER (ORDER BY x), lag(x, 0) OVER (ORDER BY x) FROM {_v(('1',), ('2',), ('3',), cols='x')} ORDER BY x",
        ),
        Obs(
            "window-lag-no-order",
            f"SELECT lag(x) OVER () FROM {_v(('1',), ('2',), cols='x')}",
        ),
        Obs(
            "window-ignore-nulls",
            f"SELECT x, y, lag(y) IGNORE NULLS OVER (ORDER BY x), first_value(y) IGNORE NULLS OVER (ORDER BY x ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING), last_value(y) OVER (ORDER BY x ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) FROM {_v(('1', 'NULL'), ('2', '5'), ('3', 'NULL'), cols='x, y')} ORDER BY x",
        ),
        Obs(
            "window-range-frame",
            f"SELECT x, sum(x) OVER (ORDER BY x RANGE BETWEEN 1 PRECEDING AND CURRENT ROW), sum(x) OVER (ORDER BY x ROWS BETWEEN 1 PRECEDING AND 1 FOLLOWING) FROM {_v(('1',), ('2',), ('2',), ('4',), cols='x')} ORDER BY x",
        ),
        Obs(
            "window-sum-int-type",
            f"SELECT sum(x) OVER (ORDER BY x), {_t('sum(x) OVER (ORDER BY x)')}, avg(x) OVER (ORDER BY x) FROM {_v(('1',), ('2',), cols='x')} ORDER BY x",
        ),
        Obs(
            "window-tie-order",
            f"SELECT k, v, row_number() OVER (ORDER BY k) FROM {_v(*[('1', str(i)) for i in range(8)], cols='k, v')} ORDER BY 3",
            "Which tied row gets which number: no order is promised.",
        ),
    ]


def _relation_probes() -> list[Obs]:
    a = _v(("1",), ("1",), ("2",), ("NULL",), ("NULL",), cols="x")
    b = _v(("1",), ("NULL",), ("3",), cols="x")
    return [
        Obs("set-union", f"SELECT x FROM {a} UNION SELECT x FROM {b} ORDER BY x"),
        Obs("set-union-all", f"SELECT x FROM {a} UNION ALL SELECT x FROM {b} ORDER BY x"),
        Obs("set-intersect", f"SELECT x FROM {a} INTERSECT SELECT x FROM {b} ORDER BY x"),
        Obs("set-except", f"SELECT x FROM {a} EXCEPT SELECT x FROM {b} ORDER BY x"),
        Obs("set-minus", f"SELECT x FROM {a} MINUS SELECT x FROM {b} ORDER BY x"),
        Obs("set-intersect-all", f"SELECT x FROM {a} INTERSECT ALL SELECT x FROM {b}"),
        Obs("set-except-all", f"SELECT x FROM {a} EXCEPT ALL SELECT x FROM {b}"),
        Obs(
            "set-nan-zero",
            f"SELECT to_varchar(x) FROM {_v((NAN,), (NZERO,), cols='x')} UNION SELECT to_varchar(x) FROM {_v(("'nan'::FLOAT",), ('0::FLOAT',), cols='x')}",
        ),
        Obs(
            "set-nan-zero-values",
            f"SELECT x FROM {_v((NAN,), (NZERO,), cols='x')} INTERSECT SELECT x FROM {_v(("'nan'::FLOAT",), ('0::FLOAT',), cols='x')}",
        ),
        Obs(
            "set-union-types",
            f"SELECT x, {_t('x')} FROM (SELECT 1 AS x UNION ALL SELECT 1.5 UNION ALL SELECT 2::FLOAT)",
        ),
        Obs(
            "order-null-default",
            f"SELECT x FROM {_v(('1',), ('NULL',), ('2',), cols='x')} ORDER BY x",
        ),
        Obs(
            "order-null-default-desc",
            f"SELECT x FROM {_v(('1',), ('NULL',), ('2',), cols='x')} ORDER BY x DESC",
        ),
        Obs(
            "order-null-explicit",
            f"SELECT x FROM {_v(('1',), ('NULL',), ('2',), cols='x')} ORDER BY x DESC NULLS LAST",
        ),
        Obs(
            "order-null-setting",
            f"ALTER SESSION SET DEFAULT_NULL_ORDERING = 'FIRST'; SELECT x FROM {_v(('1',), ('NULL',), ('2',), cols='x')} ORDER BY x",
        ),
        Obs(
            "order-strings",
            f"SELECT x FROM {_v(("'b'",), ("'a '",), ("'a'",), ("'A'",), ("'ä'",), cols='x')} ORDER BY x",
        ),
        Obs(
            "order-ties",
            f"SELECT k, v FROM {_v(*[('1', str(i)) for i in range(8)], ('0', '99'), cols='k, v')} ORDER BY k",
            "The order of tied rows: whether a sort keeps input order.",
        ),
        Obs(
            "order-limit-ties",
            f"SELECT k, v FROM {_v(*[('1', str(i)) for i in range(8)], cols='k, v')} ORDER BY k LIMIT 3",
        ),
        Obs(
            "limit-null-offset",
            f"SELECT x FROM {_v(('1',), ('2',), ('3',), cols='x')} ORDER BY x LIMIT NULL OFFSET 1",
        ),
        Obs(
            "join-nan-zero",
            f"SELECT to_varchar(l.x), to_varchar(r.x) FROM {_v((NAN,), (NZERO,), cols='x').replace('AS s(', 'AS l(')} JOIN {_v(("'nan'::FLOAT",), ('0::FLOAT',), cols='x').replace('AS s(', 'AS r(')} ON l.x = r.x",
        ),
        Obs(
            "array-index",
            "SELECT array_construct(1, 2, 3)[0], array_construct(1, 2, 3)[5], get(array_construct(1, 2, 3), 1), array_construct(1, NULL, 3), array_size(array_construct(1, NULL)), "
            + _t("array_construct(1, 2)[0]"),
        ),
        Obs(
            "array-index-negative",
            "SELECT array_construct(1, 2, 3)[-1]",
        ),
        Obs(
            "array-compare",
            "SELECT array_construct(1, 2) = array_construct(1, 2), array_construct(1, NULL) = array_construct(1, NULL), object_construct('a', NULL) = object_construct(), array_construct(1, 2) < array_construct(1, 3)",
        ),
        Obs(
            "flatten-null-empty",
            "SELECT count(*) FROM (SELECT NULL::ARRAY AS a UNION ALL SELECT array_construct() UNION ALL SELECT array_construct(1)) t, LATERAL FLATTEN(input => t.a)",
        ),
        Obs(
            "flatten-outer",
            "SELECT t.k, f.value FROM (SELECT 1 AS k, NULL::ARRAY AS a UNION ALL SELECT 2, array_construct() UNION ALL SELECT 3, array_construct(1)) t, LATERAL FLATTEN(input => t.a, OUTER => TRUE) f ORDER BY t.k",
        ),
        Obs(
            "array-order",
            "SELECT a FROM (SELECT array_construct(1, 2) AS a UNION ALL SELECT array_construct(1, NULL) UNION ALL SELECT array_construct(1) UNION ALL SELECT array_construct(0, 5) UNION ALL SELECT NULL) ORDER BY a",
            "Where a NULL element sorts inside an array; ARRAY_CONSTRUCT keeps it as JSON null (undefined).",
        ),
        Obs(
            "array-null-element-compare",
            "SELECT array_construct(1, NULL) < array_construct(1, 2), array_construct(1, NULL) > array_construct(1, 2), array_construct(1) < array_construct(1, NULL)",
        ),
        Obs(
            "object-equality",
            "SELECT object_construct('a', 1, 'b', NULL) = object_construct('a', 1), object_construct_keep_null('a', 1, 'b', NULL) = object_construct('a', 1), object_construct_keep_null('b', NULL) = object_construct_keep_null('b', NULL), object_construct('a', 1, 'b', 2) = object_construct('b', 2, 'a', 1), object_construct('a', 1) < object_construct('a', 2)",
        ),
        Obs(
            "array-agg-order-nan",
            f"SELECT array_agg(x) WITHIN GROUP (ORDER BY x), median(x), percentile_disc(0.9) WITHIN GROUP (ORDER BY x) FROM {_v((NAN,), ('1::FLOAT',), (INF,), ('NULL',), cols='x')}",
        ),
        Obs(
            "array-agg-order-zero",
            f"SELECT array_agg(to_varchar(x)) WITHIN GROUP (ORDER BY x, y) FROM {_v(('0::FLOAT', '2'), (NZERO, '1'), cols='x, y')}",
            "Whether -0.0 sorts below 0.0 or ties with it (the second key breaks ties).",
        ),
    ]


#: TPC-H at scale factor 1 in Snowflake's shared sample database: real,
#: micro-partitioned tables (LINEITEM has 6,001,215 rows), read in parallel.
LINEITEM = "snowflake_sample_data.tpch_sf1.lineitem"


def _sample_probes() -> list[Obs]:
    s = f"SELECT sum(l_extendedprice::FLOAT * l_discount::FLOAT) AS s FROM {LINEITEM}"
    return [
        Obs(
            "sample-sum-double-repeat",
            f"{s} UNION ALL {s} UNION ALL {s} UNION ALL {s}",
            "One double sum over 6M rows, four times in one query: does the result vary?",
        ),
        Obs(
            "sample-sum-double-exact",
            f"SELECT sum(l_extendedprice * l_discount), sum(l_extendedprice::FLOAT * l_discount::FLOAT) FROM {LINEITEM}",
            "The exact NUMBER sum next to the double one.",
        ),
        Obs(
            "sample-var-shifted",
            f"SELECT var_samp(l_quantity::FLOAT), var_samp(l_quantity::FLOAT + 1e9), var_samp(l_quantity::FLOAT + 1e12), var_samp(l_quantity) FROM {LINEITEM}",
            "The variance does not change with a shift; a formula that cancels shows it.",
        ),
        Obs(
            "sample-tie-order",
            f"SELECT listagg(l_orderkey || ':' || l_linenumber, ',') FROM (SELECT l_orderkey, l_linenumber FROM {LINEITEM} ORDER BY l_returnflag, l_linestatus LIMIT 8) UNION ALL SELECT listagg(l_orderkey || ':' || l_linenumber, ',') FROM (SELECT l_orderkey, l_linenumber FROM {LINEITEM} ORDER BY l_returnflag, l_linestatus LIMIT 8)",
            "The first 8 rows of a sort with millions of ties, twice.",
        ),
        Obs(
            "sample-row-number-ties",
            f"SELECT count(*) FROM (SELECT l_orderkey, l_linenumber, row_number() OVER (PARTITION BY l_returnflag ORDER BY l_linestatus) AS r1, row_number() OVER (PARTITION BY l_returnflag ORDER BY l_linestatus) AS r2 FROM {LINEITEM}) WHERE r1 <> r2",
            "Two identical ROW_NUMBER windows over ties in one query: do they number the rows alike?",
        ),
    ]


def _execution_probes() -> list[Obs]:
    return [
        Obs(
            "eval-case-guard",
            f"SELECT CASE WHEN b = 0 THEN NULL ELSE a / b END FROM {_v(('1', '0'), ('4', '2'))}",
        ),
        Obs(
            "eval-iff-guard",
            f"SELECT iff(b = 0, NULL, a / b) FROM {_v(('1', '0'), ('4', '2'))}",
        ),
        Obs(
            "eval-where-guard",
            f"SELECT a / b FROM {_v(('1', '0'), ('4', '2'))} WHERE b <> 0",
        ),
        Obs(
            "eval-and-guard",
            f"SELECT a FROM {_v(('1', '0'), ('4', '2'))} WHERE b <> 0 AND a / b > 1",
        ),
        Obs(
            "eval-coalesce-guard",
            f"SELECT coalesce(a, 1 / b) FROM {_v(('1', '0'))}",
        ),
        Obs(
            "eval-constant-branch",
            "SELECT CASE WHEN 1 = 1 THEN 1 ELSE 1 / 0 END, iff(TRUE, 1, 'x'::NUMBER)",
            "Is an untaken branch with a constant error folded and raised at compile time?",
        ),
        Obs(
            "eval-cast-branch",
            f"SELECT iff(a > 0, a, CAST('sverify: e: ' || to_varchar(a) AS NUMBER(38,0))) FROM {_v(('1',), ('2',), cols='a')}",
        ),
        Obs(
            "eval-cast-branch-taken",
            f"SELECT iff(a > 0, a, CAST('sverify: integer overflow: ' || to_varchar(a) AS NUMBER(38,0))) FROM {_v(('1',), ('-2',), cols='a')}",
        ),
        Obs(
            "eval-cast-branch-null",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS NUMBER(38,0)) FROM {_v(('NULL::NUMBER',), cols='a')}",
        ),
        Obs(
            "eval-cast-raise-float",
            f"SELECT CAST('sverify: division by zero: ' || to_varchar(a) AS FLOAT) FROM {_v(('0::FLOAT',), cols='a')}",
            "The writer's raise for a double: a string that does not parse as a double. Must not be read as NaN or inf.",
        ),
        Obs(
            "eval-cast-raise-bool",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS BOOLEAN) FROM {_v(('1',), cols='a')}",
        ),
        Obs(
            "eval-cast-raise-date",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS DATE) FROM {_v(('1',), cols='a')}",
        ),
        Obs(
            "eval-cast-raise-timestamp",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS TIMESTAMP_NTZ(6)) FROM {_v(('1',), cols='a')}",
        ),
        Obs(
            "eval-cast-raise-time",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS TIME(9)) FROM {_v(('1',), cols='a')}",
        ),
        Obs(
            "eval-raise-varchar-via-number",
            f"SELECT to_varchar(CAST('sverify: e: ' || to_varchar(a) AS NUMBER(38,0))) FROM {_v(('1',), cols='a')}",
            "A raise for a string: through a NUMBER cast.",
        ),
        Obs(
            "int-shift-negative",
            "SELECT bitshiftleft(-8, -1)",
        ),
        Obs(
            "comment-slashes",
            "SELECT 7 // 2\n, 1",
            "`//` starts a comment in Snowflake SQL.",
        ),
        Obs(
            "eval-cast-raise-varchar",
            f"SELECT CAST('sverify: e: ' || to_varchar(a) AS VARCHAR) FROM {_v(('1',), cols='a')}",
            "A cast to VARCHAR never fails: the writer's raise cannot raise for a string.",
        ),
        Obs(
            "limits-number",
            f"SELECT {_t('1::NUMBER(38,37)')}, 1::NUMBER(38,37)",
        ),
        Obs(
            "limits-number-39",
            "SELECT 1::NUMBER(39,0)",
        ),
        Obs(
            "settings",
            "SHOW PARAMETERS IN SESSION",
            "Recorded in the header instead of here; this probe only checks the query runs.",
        ),
    ]


def _frontend_probes() -> list[Obs]:
    return [
        Obs(
            "literal-types",
            "SELECT "
            + ", ".join(
                _t(x)
                for x in (
                    "1",
                    "-1",
                    str(I64_MAX),
                    str(2**64),
                    N38,
                    "1.5",
                    "1.50",
                    "1e3",
                    "1E-3",
                    "'a'",
                    "TRUE",
                    "NULL",
                    "DATE '2024-01-05'",
                    "TIMESTAMP '2024-01-05 10:00:00'",
                    "X'AB'",
                    "-0.0",
                )
            ),
        ),
        Obs(
            "implicit-casts-arith",
            "SELECT 1 + '2', "
            + _t("1 + '2'")
            + ", 1 + '2.5', '3' * '4', "
            + _t("'3' * '4'")
            + ", 1 + 1.5::FLOAT, "
            + _t("1 + 1.5::FLOAT")
            + ", 1.5 + 1::FLOAT, "
            + _t("1.5 + 1::FLOAT"),
        ),
        Obs(
            "implicit-casts-compare",
            "SELECT '10' < 9, '10' < '9', 10 < '9', 1 = '1.0', 1 = 1.0, 1 = 1.0::FLOAT, '2024-01-05'::DATE = '2024-01-05', TRUE = 'true', 0.1::FLOAT = 0.1",
        ),
        Obs(
            "implicit-casts-bad",
            "SELECT 1 + 'abc'",
        ),
        Obs(
            "identifiers-case",
            'SELECT "x", X FROM (SELECT 1 AS "x", 2 AS x)',
        ),
        Obs(
            "integer-division-literal",
            "SELECT 7 / 2, " + _t("7 / 2"),
        ),
    ]


def _writer_probes() -> list[Obs]:
    """SQL that `sverify.sql.snowflake` writes, with the inputs where it might
    not give the reference."""
    from sverify.sql.snowflake import SNOWFLAKE as d

    i = _v(
        (str(I64_MIN), "-1"),
        (str(I64_MAX), "2"),
        ("-7", "2"),
        ("7", "-2"),
        (str(I64_MIN), "3"),
        ("9", "0"),
    )
    f = _v(
        *[
            (d.float_lit(x),)
            for x in (
                2.5,
                -2.5,
                1e19,
                -9.223372036854776e18,
                9.223372036854776e18,
                math.nan,
                math.inf,
            )
        ],
        cols="x",
    )
    ts = "CAST('2024-01-05 10:00:00.123456' AS TIMESTAMP_NTZ(6))"
    return [
        Obs(
            "writer-int-add",
            f"SELECT a, b, {d.int_add('a', 'b')} FROM {i} WHERE b <> 0 AND a > 0",
        ),
        Obs(
            "writer-int-add-overflow",
            f"SELECT {d.int_add('a', 'b')} FROM {_v((str(I64_MAX), '1'))}",
        ),
        Obs(
            "writer-int-mul-overflow",
            f"SELECT {d.int_mul('a', 'b')} FROM {_v((str(I64_MAX), '2'))}",
        ),
        Obs(
            "writer-trunc-div",
            f"SELECT a, b, {d.trunc_div('a', 'b')}, {d.trunc_mod('a', 'b')} FROM {i} WHERE b <> 0 AND NOT (a = {I64_MIN} AND b = -1)",
        ),
        Obs(
            "writer-trunc-div-min",
            f"SELECT {d.trunc_div('a', 'b')} FROM {_v((str(I64_MIN), '-1'))}",
        ),
        Obs(
            "writer-float-to-int",
            f"SELECT x, {d.float_to_int('x')} FROM {f} WHERE x BETWEEN -1e18 AND 1e18",
        ),
        Obs(
            "writer-float-to-int-nan",
            f"SELECT {d.float_to_int('x')} FROM {_v((d.float_lit(math.nan),), cols='x')}",
        ),
        Obs(
            "writer-float-to-int-edge",
            f"SELECT {d.float_to_int('x')} FROM {_v((d.float_lit(-(2.0**63)),), cols='x')}",
        ),
        Obs(
            "writer-float-lit",
            "SELECT "
            + ", ".join(
                f"to_varchar({d.float_lit(x)})"
                for x in (0.1, -0.0, 1e-320, 1.7976931348623157e308, 5e-324, math.nan, -math.inf)
            ),
        ),
        Obs(
            "writer-float-mod",
            f"SELECT a, b, {d.float_mod('a', 'b')} FROM {_v(*[(d.float_lit(x), d.float_lit(y)) for x, y in ((5.5, 2.0), (-5.5, 2.0), (math.inf, 2.0), (5.5, math.inf), (math.nan, 1.0))])}",
        ),
        Obs(
            "writer-float-round",
            f"SELECT x, {d.float_round('x')}, {d.float_round_to('x', 2)}, {d.float_round_to('x', -1)} FROM {_v(*[(d.float_lit(x),) for x in (2.5, -2.5, 0.5, 2.675, 1e300, math.inf, math.nan)], cols='x')}",
        ),
        Obs(
            "writer-int-avg",
            f"SELECT {d.int_avg('x', '')} FROM {_v(('-7',), ('0',), cols='x')} UNION ALL SELECT {d.int_avg('x', '')} FROM {_v(('7',), ('0',), cols='x')} UNION ALL SELECT {d.int_avg('x', '')} FROM {_v((str(I64_MAX),), (str(I64_MAX),), (str(I64_MAX),), cols='x')}",
        ),
        Obs(
            "writer-int-sum-overflow",
            f"SELECT {d.int_sum('x')} FROM {_v((str(I64_MAX),), ('1',), cols='x')}",
        ),
        Obs(
            "writer-date-part",
            "SELECT "
            + ", ".join(
                d.date_part(p, ts)
                for p in (
                    "year",
                    "month",
                    "day",
                    "hour",
                    "minute",
                    "second",
                    "millisecond",
                    "microsecond",
                    "dow",
                    "week",
                    "doy",
                    "quarter",
                )
            ),
        ),
        Obs(
            "writer-date-trunc",
            "SELECT "
            + ", ".join(
                d.date_trunc(u, ts) for u in ("week", "month", "year", "day", "hour", "second")
            ),
        ),
        Obs(
            "writer-time-micros",
            f"SELECT {d.time_micros(ts)}, {d.as_time(d.time_micros(ts))}, {d.time_diff(ts, d.timestamp_lit(-1))}, {d.time_add_interval(ts, '-1')}",
        ),
        Obs(
            "writer-like-pattern",
            f"SELECT p, {d.like('s', d.like_pattern('p'))} FROM {_v(*[(d.str_lit(s), d.str_lit(p)) for s, p in (('a\\\\', 'a\\\\'), ('a_c', 'a\\\\_c'), ('abc', 'a\\\\_c'), ('a\\\\', 'a\\\\\\\\'))], cols='s, p')}",
        ),
        Obs(
            "writer-substring",
            f"SELECT {d.substring(d.str_lit('héllo'), '2', '2')}, {d.substring(d.str_lit('héllo'), '4', None)}",
        ),
        Obs(
            "writer-str-lit",
            "SELECT "
            + ", ".join(
                f"length({d.str_lit(s)}), {d.str_lit(s)}"
                for s in ("a\\b", "it's", "a\nb", "\x01", "é")
            ),
        ),
        Obs(
            "writer-substring-int32",
            "SELECT "
            + ", ".join(
                d.substring(d.str_lit("hello"), a, n)
                for a, n in (
                    ("x", "1"),
                    ("y", "1"),
                    ("2", "z"),
                    ("2", "3000000000"),
                    ("4294967295", "1"),
                    ("2", None),
                )
            )
            + f" FROM {_v(('4294967295', '2147483648'), cols='x, y').replace('AS s(x, y)', 'AS s(x, y), (SELECT 3000000000 AS z)')}",
            "Starts and lengths from 2^31 on, inside the reference's range: '' for a start past the end, the rest for a long length.",
        ),
        Obs(
            "writer-substring-raise",
            f"SELECT {d.substring(d.str_lit('hello'), 'x', '1')} FROM {_v(('4294967298',), cols='x')}",
            "A start of 2^32 + 2 is outside the reference's range: it raises.",
        ),
        Obs(
            "writer-raise-str",
            f"SELECT {d.raise_('UPPER of non-ASCII text differs between engines', d.str_lit('é'), 'str')}",
        ),
        Obs(
            "writer-int-fold",
            f"SELECT {d.int_add('1', '1')}, {d.int_sub(d.int_lit(-5), '3')}, {d.int_mul(str(I64_MAX), '2')}, {d.int_neg(d.int_lit(I64_MIN))}",
            "Literal arithmetic folds to a literal; past 64 bits it keeps the check, which raises.",
        ),
        Obs(
            "writer-int-fold-values",
            f"SELECT {d.int_add('1', '1')}, {d.int_sub(d.int_lit(-5), '3')}, {d.int_mul(d.int_lit(-(2**31)), '2')}, {d.int_neg(d.int_lit(-7))}",
        ),
        Obs(
            "writer-is-ascii",
            f"SELECT {d.is_ascii(d.str_lit('abc'))}, {d.is_ascii(d.str_lit('é'))}, {d.octet_length(d.str_lit('😀'))}",
        ),
        Obs(
            "writer-greatest",
            f"SELECT {d.greatest('1', 'NULL')}, {d.least('NULL', '2')}, {d.greatest(d.float_lit(math.nan), d.float_lit(1.0))}",
        ),
        Obs(
            "writer-timestamp-lit",
            f"SELECT {d.timestamp_lit(-1)}, {d.timestamp_lit(253402300799999999)}, {d.date_lit(-719162)}",
        ),
        Obs(
            "writer-add-months",
            f"SELECT {d.add_months(d.date_lit(19753), 1, 'date')}, {d.add_months(d.timestamp_lit(1706698800000000), 1, 'time')}",
            "2024-01-31 plus a month.",
        ),
        Obs(
            "writer-is-nan",
            f"SELECT {d.is_nan(d.float_lit(math.nan))}, {d.is_nan(d.float_lit(1.0))}, {d.float_eq(d.float_lit(-0.0) + ' * -1', d.float_lit(0.0))}",
        ),
    ]


def observations() -> list[Obs]:
    found = [
        *_integer_probes(),
        *_decimal_probes(),
        *_double_probes(),
        *_cast_probes(),
        *_null_probes(),
        *_string_probes(),
        *_temporal_probes(),
        *_aggregate_probes(),
        *_window_probes(),
        *_relation_probes(),
        *_execution_probes(),
        *_sample_probes(),
        *_frontend_probes(),
        *_writer_probes(),
    ]
    names = [o.construct for o in found]
    dupes = {n for n in names if names.count(n) > 1}
    if dupes:
        raise ValueError(f"duplicate constructs: {sorted(dupes)}")
    return found


# Running


def _session_sql() -> str:
    return "ALTER SESSION SET " + ", ".join(f"{k} = {v}" for k, v in SESSION.items())


def _value(v: Any) -> str:
    if v is None:
        return "NULL"
    if isinstance(v, float):
        if math.isnan(v):
            return "NaN"
        return repr(v)
    if isinstance(v, (list, dict)):
        return json.dumps(v, ensure_ascii=False)
    return str(v)


def _rows(result: Any) -> str:
    if isinstance(result, dict):
        result = [result]
    return "; ".join("(" + ", ".join(_value(x) for x in r.values()) + ")" for r in result)


#: The query id each error quotes, which changes from run to run.
_QID = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}: ")
_ERR = re.compile(r"(\d{6} \([0-9A-Z]{5}\):.*)", re.S)


def _error(text: str) -> str:
    # `snow` frames errors in a box of rule characters; keep the message.
    flat = " ".join(re.sub(r"[│╭╮╰╯─]", " ", text).split())
    m = _ERR.search(flat)
    msg = _QID.sub("", m.group(1) if m else flat)
    return "error " + msg[:300]


#: How many `snow` calls this process made (`--stats`).
CALLS = 0


def _snow(connection: str, sql: str) -> tuple[str | None, list[Any]]:
    """Run `sql`'s statements in one `snow` call: the error of the first
    statement that fails (or None), and the results of those before it.
    `snow` stops at the first error but has already printed the results
    before it, as JSON that the error cut off."""
    global CALLS
    CALLS += 1
    with tempfile.NamedTemporaryFile("w", suffix=".sql", delete=False) as f:
        f.write(sql)
        path = f.name
    try:
        p = subprocess.run(
            ["snow", "sql", "-c", connection, "--format", "json", "-f", path],
            capture_output=True,
            text=True,
            timeout=600,
        )
    finally:
        Path(path).unlink()
    if p.returncode == 0:
        out = json.loads(p.stdout)
        return None, out if out and isinstance(out[0], list) else [out]
    done: list[Any] = []
    text = p.stdout.strip()
    if text.startswith("["):
        for tail in ("]", "]]", ""):
            try:
                done = json.loads(text.rstrip().rstrip(",") + tail)
                break
            except json.JSONDecodeError:
                continue
        if done and not isinstance(done[0], list):
            done = [done]
    err = (
        _error(p.stderr)
        if p.stderr.strip()
        else "error (no message: snow could not render a value)"
    )
    return err, done


def _split(sql: str) -> list[str]:
    return [s.strip() for s in sql.split("; ") if s.strip()]


def _run_one(connection: str, o: Obs) -> str:
    stmts = [_session_sql(), *_split(o.sql)]
    err, done = _snow(connection, ";\n".join(stmts) + ";")
    if err is not None:
        return err
    return _rows(done[-1])


def probe(connection: str, only: set[str] | None = None) -> dict[str, Any]:
    obs = [o for o in observations() if not only or o.construct in only]
    results: dict[str, str] = {}
    # Batches of single-statement probes; probes that change the session run
    # alone. A batch with an error goes on after the statement that failed.
    queue = [o for o in obs if len(_split(o.sql)) == 1 and o.construct != "settings"]
    while queue:
        batch = queue[:BATCH]
        err, done = _snow(connection, ";\n".join([_session_sql(), *(o.sql for o in batch)]) + ";")
        if not done:  # the session statement itself failed, or nothing parsed
            done = [[]]
            if err is not None:
                results[batch[0].construct] = _run_one(connection, batch[0])
                print(batch[0].construct, results[batch[0].construct][:80], file=sys.stderr)
                queue = queue[1:]
                continue
        ran = done[1:]
        for o, r in zip(batch, ran, strict=False):
            results[o.construct] = _rows(r)
            print(o.construct, results[o.construct][:80], file=sys.stderr)
        if err is not None and len(ran) < len(batch):
            failed = batch[len(ran)]
            results[failed.construct] = err
            print(failed.construct, err[:80], file=sys.stderr)
            queue = queue[len(ran) + 1 :]
        else:
            queue = queue[len(batch) :]
    for o in obs:
        if o.construct not in results and o.construct != "settings":
            results[o.construct] = _run_one(connection, o)
    err, res = _snow(
        connection,
        f"{_session_sql()};\nSELECT current_version() AS v;\nSHOW PARAMETERS IN SESSION;",
    )
    if err is not None or len(res) != 3:
        raise RuntimeError(f"cannot read the version and parameters: {err}")
    version = str(res[1][0]["V"])
    params = {str(r["key"]): str(r["value"]) for r in res[2] if str(r.get("key")) in RECORDED}
    if any(o.construct == "settings" for o in obs):
        results["settings"] = f"({len(res[2])} parameters; see the header)"
    return {
        "snowflake": version,
        "session": {k: v.strip("'") for k, v in SESSION.items()},
        "parameters": dict(sorted(params.items())),
        "probes": [
            {
                "construct": o.construct,
                "sql": o.sql,
                **({"note": o.note} if o.note else {}),
                "observed": results[o.construct],
            }
            for o in obs
        ],
    }


def listing() -> dict[str, Any]:
    return {
        "snowflake": "not yet run",
        "session": {k: v.strip("'") for k, v in SESSION.items()},
        "probes": [
            {"construct": o.construct, "sql": o.sql, **({"note": o.note} if o.note else {})}
            for o in observations()
        ],
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("-c", "--connection", default="sverify", help="the snow connection")
    parser.add_argument("--list", action="store_true", help="print the queries, run nothing")
    parser.add_argument("--write", action="store_true", help=f"write {OUT}")
    parser.add_argument("--out", type=Path, help="write here instead")
    parser.add_argument(
        "--only", nargs="*", help="run only these constructs (prints, never writes)"
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help=f"run only the constructs {OUT.name} lacks, and add them to it",
    )
    args = parser.parse_args(argv)
    if args.update:
        old = json.loads(OUT.read_text())
        have = {p["construct"] for p in old["probes"]}
        new = {o.construct for o in observations()} - have
        found = probe(args.connection, new) if new else {"probes": []}
        by = {p["construct"]: p for p in [*old["probes"], *found["probes"]]}
        old["probes"] = [by[o.construct] for o in observations() if o.construct in by]
        OUT.write_text(json.dumps(old, indent=1, ensure_ascii=False) + "\n")
        print(f"{len(new)} probes, {CALLS} snow calls", file=sys.stderr)
        return
    found = (
        listing() if args.list else probe(args.connection, set(args.only) if args.only else None)
    )
    text = json.dumps(found, indent=1, ensure_ascii=False) + "\n"
    print(f"{len(found['probes'])} probes, {CALLS} snow calls", file=sys.stderr)
    if args.write or args.out:
        if args.only:
            raise SystemExit("--only prints; it never writes")
        (args.out or OUT).write_text(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
