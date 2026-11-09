# ruff: noqa: E501 - the probes are SQL strings, one per line where they fit
"""Probe open-source Spark's SQL for the characterization (#738).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The Spark counterpart of `sverify_dev.probe_polars`'s observations, for
`engines/spark/`.

Each `Obs` is a SQL query whose result is recorded as it is. Every query runs
four times on one local session: with `spark.sql.ansi.enabled` on and off, and
on each of Spark's two paths for a small query. On the folded path the
optimizer evaluates a query over a `VALUES` table on the driver with the
interpreted expressions (`ConvertToLocalRelation`, `ConstantFolding`); on the
codegen path those rules are excluded, so the query runs as a job with
whole-stage code generation, as it does over a table. Where the two paths agree
the observation keeps one result per ANSI setting.

`python -m sverify_dev.probe_spark --write` writes
`engines/spark/probes/probes.json`; the facts in
`engines/spark/facts/` cite its constructs. It needs `pyspark` and a
JVM (Java 17 or 21); run it on homelab (CLAUDE.md), where it takes about a
minute. No test checks it is current: a JVM is too heavy for the test suite.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import sys
from dataclasses import dataclass, field
from decimal import Decimal
from pathlib import Path
from typing import Any

_HERE = Path(__file__).resolve()
#: Where `--write` writes: the repository's, when run from a checkout.
OUT = (
    (_HERE.parents[3] if len(_HERE.parents) > 3 else _HERE.parent)
    / "engines"
    / "spark"
    / "probes"
    / "probes.json"
)

#: The session's settings, apart from the two that vary. `sverify_spark.dialect`'s
#: `SPARK_CONF` without `spark.sql.ansi.enabled`, and the local session of
#: `sverify_spark.engine.session()`.
BASE_CONF: dict[str, str] = {
    "spark.master": "local[2]",
    "spark.driver.memory": "1g",
    "spark.ui.enabled": "false",
    "spark.sql.shuffle.partitions": "2",
    "spark.sql.session.timeZone": "UTC",
    "spark.sql.timestampType": "TIMESTAMP_NTZ",
    "spark.sql.caseSensitive": "true",
    "spark.sql.parser.escapedStringLiterals": "false",
}
#: The rules the codegen path excludes.
CODEGEN_EXCLUDED = (
    "org.apache.spark.sql.catalyst.optimizer.ConvertToLocalRelation,"
    "org.apache.spark.sql.catalyst.optimizer.ConstantFolding"
)


@dataclass(frozen=True)
class Obs:
    construct: str
    sql: str
    conf: dict[str, str] = field(default_factory=dict)
    note: str = ""


_INT_TYPES = {
    "TINYINT": (-(2**7), 2**7 - 1),
    "SMALLINT": (-(2**15), 2**15 - 1),
    "INT": (-(2**31), 2**31 - 1),
    "BIGINT": (-(2**63), 2**63 - 1),
}


def _int_probes() -> list[Obs]:
    found: list[Obs] = []
    for t, (lo, hi) in _INT_TYPES.items():
        k = t.lower()

        def v(x: int, t: str = t) -> str:
            return f"CAST({x} AS {t})"

        cases = {
            "add": ("a + b", hi, 1),
            "subtract": ("a - b", lo, 1),
            "multiply": ("a * b", hi, 2),
            "negate": ("-a", lo, 1),
            "abs": ("abs(a)", lo, 1),
            "div-min": ("a div b", lo, -1),
            "mod-min": ("a % b", lo, -1),
            "pmod-min": ("pmod(a, b)", lo, -1),
            "div-zero": ("a div b", 7, 0),
            "mod-zero": ("a % b", 7, 0),
            "slash-zero": ("a / b", 7, 0),
        }
        for name, (expr, a, b) in cases.items():
            found.append(
                Obs(
                    f"{k}-{name}",
                    f"SELECT {expr} AS r, typeof({expr}) AS t "
                    f"FROM VALUES ({v(a)}, {v(b)}) AS s(a, b)",
                )
            )
        found.append(
            Obs(
                f"{k}-div-mod-signs",
                "SELECT a, b, a div b, a % b, pmod(a, b), a / b, typeof(a / b) FROM VALUES "
                f"({v(-7)}, {v(2)}), ({v(7)}, {v(-2)}), ({v(-7)}, {v(-2)}) AS s(a, b)",
            )
        )
        found.append(
            Obs(
                f"{k}-shifts",
                "SELECT n, shiftleft(a, n), shiftright(a, n), shiftrightunsigned(a, n), "
                "typeof(shiftleft(a, n)) FROM VALUES "
                + ", ".join(
                    f"({v(-8)}, {n})" for n in (1, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, -1)
                )
                + " AS s(a, n)",
            )
        )
        found.append(
            Obs(
                f"{k}-bitwise",
                "SELECT a & b, a | b, a ^ b, ~a, typeof(a & b) "
                f"FROM VALUES ({v(lo)}, {v(-1)}) AS s(a, b)",
            )
        )
        found.append(
            Obs(
                f"{k}-sum-overflow",
                "SELECT sum(a), typeof(sum(a)), avg(a), typeof(avg(a)) "
                f"FROM VALUES ({v(hi)}), ({v(hi)}) AS s(a)",
            )
        )
    found.append(
        Obs(
            "bigint-sum-partial-overflow",
            "SELECT sum(a) FROM VALUES (9223372036854775807L), (1L), (-2L) AS s(a)",
            note="the total fits in 64 bits; a partial sum does not",
        )
    )
    found.append(
        Obs(
            "bigint-sum-order",
            "SELECT sum(a) FROM (SELECT /*+ COALESCE(1) */ * FROM VALUES "
            "(9223372036854775807L), (1L), (-2L) AS s(a))",
            note="one partition, in input order: the first partial sum overflows",
        )
    )
    found.append(
        Obs(
            "bigint-sum-order-reversed",
            "SELECT sum(a) FROM (SELECT /*+ COALESCE(1) */ * FROM VALUES "
            "(-2L), (1L), (9223372036854775807L) AS s(a))",
        )
    )
    found.append(
        Obs(
            "int-power",
            "SELECT power(a, b), typeof(power(a, b)) FROM VALUES "
            "(2L, 63L), (2L, 64L), (-8L, 3L), (0L, -1L), (2L, -1L), (0L, 0L), (-2L, 1023L), (-2L, 1024L) AS s(a, b)",
        )
    )
    found.append(Obs("int-shift-operator", "SELECT 1 << 33, 1L << 65, -8 >> 1, -8 >>> 1"))
    return found


def _double(x: str) -> str:
    return f"CAST('{x}' AS DOUBLE)"


DOUBLE_EDGES = (
    "("
    + "), (".join(
        _double(x) for x in ("0", "-0", "1", "-1", "2.5", "1e308", "Infinity", "-Infinity", "NaN")
    )
    + ")"
)


def _double_probes() -> list[Obs]:
    nan, inf = _double("NaN"), _double("Infinity")
    return [
        Obs(
            "double-nan-creation",
            "SELECT a + b, a - b, a * b, a / b, a % b FROM VALUES "
            f"({inf}, -{inf}), ({inf}, {inf}), ({_double('0')}, {inf}), ({inf}, {_double('2')}) AS s(a, b)",
        ),
        Obs(
            "double-overflow",
            "SELECT a * 10.0D, a + a, -a * 10.0D, a / 1e-308D FROM VALUES (1e308D) AS s(a)",
        ),
        Obs(
            "double-divide-zero",
            "SELECT a / b, a % b, pmod(a, b), typeof(a / b) FROM VALUES "
            "(1.0D, 0.0D), (-1.0D, 0.0D), (0.0D, 0.0D), (1.0D, -0.0D), "
            f"({nan}, 0.0D), ({inf}, 0.0D) AS s(a, b)",
        ),
        Obs(
            "double-modulus",
            "SELECT a, b, a % b, pmod(a, b), typeof(a % b) FROM VALUES "
            f"(-7.5D, 2.0D), (7.5D, -2.0D), (-6.0D, 2.0D), (5.0D, {inf}), (-5.0D, {inf}), "
            f"({inf}, 2.0D), (5.0D, {nan}) AS s(a, b)",
        ),
        Obs(
            "double-zero-sign",
            "SELECT a + b, a - b, a * b, -a, a * -1.0D, b / -1.0D, abs(a) FROM VALUES "
            "(-0.0D, 0.0D), (-0.0D, -0.0D), (0.0D, 0.0D) AS s(a, b)",
        ),
        Obs(
            "double-zero-literal",
            "SELECT -0.0D, -0.0, CAST('-0.0' AS DOUBLE), 0.0D * -1, typeof(-0.0)",
            note="whether a literal or a cast keeps the sign of zero",
        ),
        Obs(
            "double-rounding-arith",
            "SELECT 0.1D + 0.2D, 1.0D / 3.0D, 1e16D + 1.0D, 0.1D * 3.0D",
        ),
        Obs(
            "double-math-domain",
            "SELECT x, sqrt(x), ln(x), log10(x), log2(x), log(2.0D, x), log(x, 8.0D), "
            "asin(x), acos(x), exp(x), sin(x), cos(x), tan(x), atan(x) FROM VALUES "
            + DOUBLE_EDGES
            + ", (-1e-320D), (2.0D) AS s(x)",
        ),
        Obs(
            "double-atan2",
            "SELECT atan2(a, b) FROM VALUES (0.0D, 0.0D), (-0.0D, 0.0D), (0.0D, -0.0D), "
            f"(-0.0D, -0.0D), ({inf}, {inf}), (1.0D, {nan}) AS s(a, b)",
        ),
        Obs(
            "double-power",
            "SELECT a, b, power(a, b), typeof(power(a, b)) FROM VALUES "
            f"(-8.0D, 1.0D / 3.0D), (0.0D, -1.0D), (-0.0D, -1.0D), (1.0D, {nan}), ({nan}, 0.0D), "
            f"(10.0D, 400.0D), (-1.0D, {inf}), (2.0D, 0.5D) AS s(a, b)",
        ),
        Obs(
            "double-round",
            "SELECT x, round(x), round(x, 1), round(x, -1), bround(x), bround(x, 1), "
            "typeof(round(x)) FROM VALUES (0.5D), (1.5D), (2.5D), (-2.5D), (-0.5D), "
            f"(2.675D), (0.285D), (1.005D), (15.0D), (25.0D), (1e300D), ({nan}), ({inf}), (-0.4D) AS s(x)",
        ),
        Obs(
            "double-round-digits",
            "SELECT round(x, 2), bround(x, 2), round(y, -2), bround(y, -2), round(z, 2), round(z, 400), "
            "round(x, -400) FROM VALUES (2.675D, 1250.0D, 1e300D), (0.285D, 1350.0D, 5e-324D), "
            "(1.005D, -1250.0D, 1.7976931348623157e308D), (-0.004D, -40.0D, -0.004D) AS s(x, y, z)",
        ),
        Obs(
            "double-floor-ceil",
            "SELECT x, floor(x), ceil(x), typeof(floor(x)), floor(x, 0), typeof(floor(x, 0)) FROM VALUES "
            + DOUBLE_EDGES
            + ", (1e20D), (-2.5D) AS s(x)",
        ),
        Obs(
            "double-floor-ceil-finite",
            "SELECT x, floor(x), ceil(x), typeof(floor(x)), floor(x, 0), ceil(x, 1), typeof(ceil(x, 1)) "
            "FROM VALUES (2.5D), (-2.5D), (-0.5D), (-0.0D), (9.2e18D) AS s(x)",
        ),
        Obs("double-floor-nan", f"SELECT floor({nan}), ceil({nan})"),
        Obs("double-floor-inf", f"SELECT floor({inf})"),
        Obs(
            "double-compare",
            "SELECT a, b, a = b, a < b, a > b, a <=> b, greatest(a, b), least(a, b) FROM VALUES "
            f"({nan}, {nan}), ({nan}, {inf}), (1.0D, {nan}), (-0.0D, 0.0D), (0.0D, -0.0D), "
            f"(CAST(NULL AS DOUBLE), {nan}) AS s(a, b)",
        ),
        Obs(
            "double-sort",
            "SELECT x FROM VALUES "
            + DOUBLE_EDGES
            + ", (CAST(NULL AS DOUBLE)), (-0.0D) AS s(x) ORDER BY x",
        ),
        Obs(
            "double-sort-desc",
            "SELECT x FROM VALUES "
            + DOUBLE_EDGES
            + ", (CAST(NULL AS DOUBLE)) AS s(x) ORDER BY x DESC",
        ),
        Obs(
            "double-group-nan-zero",
            "SELECT x, count(*) FROM VALUES "
            f"(0.0D), (-0.0D), (-0.0D), ({nan}), (-{nan}), (CAST('NaN' AS DOUBLE) * 0.0D) AS s(x) "
            "GROUP BY x ORDER BY x",
        ),
        Obs(
            "double-group-zero-first",
            "SELECT x, count(*) FROM VALUES (-0.0D), (0.0D) AS s(x) GROUP BY x",
            note="which zero represents the group when -0.0 comes first",
        ),
        Obs(
            "double-distinct-nan-zero",
            f"SELECT DISTINCT x FROM VALUES (-0.0D), (0.0D), ({nan}), (-{nan}) AS s(x) ORDER BY x",
        ),
        Obs(
            "double-join-nan-zero",
            "SELECT l.x, r.y FROM VALUES (0.0D), (" + nan + ") AS l(x) "
            "JOIN VALUES (-0.0D), (-" + nan + ") AS r(y) ON l.x = r.y ORDER BY l.x",
        ),
        Obs(
            "double-min-max",
            "SELECT min(x), max(x) FROM VALUES (1.0D), (" + nan + "), (-1.0D) AS s(x)",
        ),
        Obs(
            "double-min-max-zero",
            "SELECT min(x), max(x), min(y), max(y) FROM VALUES (-0.0D, 0.0D), (0.0D, -0.0D) AS s(x, y)",
        ),
        Obs(
            "double-nan-sign",
            f"SELECT x, -x, x * -1.0D, abs(x), CAST(x AS STRING) FROM VALUES ({nan}), (-{nan}), "
            f"({inf} - {inf}), ({inf} * 0.0D) AS s(x)",
            note="NaN's sign is read from the double the driver receives (copysign)",
        ),
        Obs(
            "float-arith",
            "SELECT a + b, a * b, a / b, typeof(a + b), CAST(16777216 AS FLOAT) + CAST(1 AS FLOAT), "
            "a + 0.1D, typeof(a + 0.1D), typeof(a + 1) "
            "FROM VALUES (CAST(0.1 AS FLOAT), CAST(0.2 AS FLOAT)) AS s(a, b)",
        ),
        Obs(
            "float-edges",
            "SELECT a * CAST(10 AS FLOAT), typeof(a * CAST(10 AS FLOAT)), -CAST(0 AS FLOAT), "
            "CAST(1e-50D AS FLOAT), sqrt(CAST(-1 AS FLOAT)), typeof(sqrt(a)), "
            "a - a * CAST('Infinity' AS FLOAT), typeof(round(a)), typeof(floor(a)) "
            "FROM VALUES (CAST(3e38 AS FLOAT)) AS s(a)",
        ),
        Obs(
            "float-divide-zero",
            "SELECT a / CAST(0 AS FLOAT), a % CAST(0 AS FLOAT) FROM VALUES (CAST(1 AS FLOAT)) AS s(a)",
        ),
        Obs("float-cast-overflow", "SELECT CAST(1e40D AS FLOAT), CAST('1e40' AS FLOAT)"),
        Obs(
            "float-literal",
            "SELECT 1.5F, typeof(1.5F), typeof(CAST(1 AS REAL)), CAST(0.1F AS DOUBLE), CAST(CAST(0.1F AS DOUBLE) AS STRING)",
        ),
    ]


def _decimal_probes() -> list[Obs]:
    return [
        Obs(
            "decimal-types",
            "SELECT typeof(a + b), typeof(a - b), typeof(a * b), typeof(a / b), typeof(a % b), "
            "a * b, a / b FROM VALUES (CAST(0.05 AS DECIMAL(10,2)), CAST(0.5 AS DECIMAL(10,1))) AS s(a, b)",
        ),
        Obs(
            "decimal-rescale",
            "SELECT x, CAST(x AS DECIMAL(10,2)), round(x, 2), bround(x, 2) FROM VALUES "
            "(CAST(0.125 AS DECIMAL(10,3))), (CAST(-0.125 AS DECIMAL(10,3))), "
            "(CAST(0.135 AS DECIMAL(10,3))), (CAST(0.124 AS DECIMAL(10,3))) AS s(x)",
        ),
        Obs(
            "decimal-divide",
            "SELECT a / b, typeof(a / b) FROM VALUES (CAST(1.00 AS DECIMAL(10,2)), CAST(8 AS DECIMAL(10,0))), "
            "(CAST(2 AS DECIMAL(10,0)), CAST(3 AS DECIMAL(10,0))), (CAST(1 AS DECIMAL(38,0)), CAST(3 AS DECIMAL(38,0))) AS s(a, b)",
        ),
        Obs(
            "decimal-precision-loss",
            "SELECT a * b, typeof(a * b) FROM VALUES "
            "(CAST(1.0000000005 AS DECIMAL(38,10)), CAST(1.0000005 AS DECIMAL(38,10))) AS s(a, b)",
        ),
        Obs(
            "decimal-precision-loss-off",
            "SELECT a * b, typeof(a * b) FROM VALUES "
            "(CAST(1.0000000005 AS DECIMAL(38,10)), CAST(1.0000005 AS DECIMAL(38,10))) AS s(a, b)",
            conf={"spark.sql.decimalOperations.allowPrecisionLoss": "false"},
        ),
        Obs(
            "decimal-overflow-add",
            "SELECT a + a, typeof(a + a) FROM VALUES "
            "(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))) AS s(a)",
        ),
        Obs(
            "decimal-overflow-multiply",
            "SELECT a * CAST(10 AS DECIMAL(2,0)), typeof(a * CAST(10 AS DECIMAL(2,0))) FROM VALUES "
            "(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))) AS s(a)",
        ),
        Obs(
            "decimal-overflow-subtract",
            "SELECT -a - a FROM VALUES "
            "(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))) AS s(a)",
        ),
        Obs(
            "decimal-overflow-scaled",
            "SELECT a + a, typeof(a + a) FROM VALUES "
            "(CAST('9999999999999999999999999999999999.9999' AS DECIMAL(38,4))) AS s(a)",
            note="a result type of precision 39 borrows from the scale",
        ),
        Obs(
            "decimal-negate-34-digits",
            "SELECT CAST(-a AS STRING), CAST(abs(-a) AS STRING), CAST(0 - a AS STRING), "
            "CAST(-b AS STRING) FROM VALUES (CAST('12345678901234567890123456789012345678' AS DECIMAL(38,0)), "
            "CAST('1234567890123456789.0123456789012345678' AS DECIMAL(38,19))) AS s(a, b)",
            note="negation and abs of a decimal with more than 34 significant digits (SP-1)",
        ),
        Obs(
            "decimal-negate-max",
            "SELECT -a FROM VALUES (CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))) AS s(a)",
        ),
        Obs(
            "decimal-divide-zero",
            "SELECT a / b, a % b, a div b FROM VALUES (CAST(1 AS DECIMAL(10,2)), CAST(0 AS DECIMAL(10,2))) AS s(a, b)",
        ),
        Obs(
            "decimal-aggregates",
            "SELECT sum(x), typeof(sum(x)), avg(x), typeof(avg(x)), variance(x), typeof(variance(x)) "
            "FROM VALUES (CAST(1.25 AS DECIMAL(10,2))), (CAST(2.50 AS DECIMAL(10,2))), "
            "(CAST(2.50 AS DECIMAL(10,2))) AS s(x)",
        ),
        Obs(
            "decimal-sum-overflow",
            "SELECT sum(x), typeof(sum(x)) FROM VALUES "
            "(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))), "
            "(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0))) AS s(x)",
        ),
        Obs("decimal-too-wide", "SELECT CAST(1 AS DECIMAL(39,0))"),
        Obs(
            "decimal-abs-compare",
            "SELECT abs(a), a = b, a < b, typeof(abs(a)) FROM VALUES "
            "(CAST(-1.50 AS DECIMAL(10,2)), CAST(-1.5 AS DECIMAL(5,1))) AS s(a, b)",
        ),
    ]


def _string_probes() -> list[Obs]:
    return [
        Obs(
            "string-case",
            "SELECT s, upper(s), lower(s), initcap(s), length(upper(s)) FROM VALUES "
            "('ß'), ('ﬁ'), ('İ'), ('ǅ'), ('ΣΑΣ'), ('straße'), ('Ⅻ') AS t(s)",
        ),
        Obs(
            "string-case-sensitivity",
            "SELECT 'ABC' LIKE 'a%', 'ABC' ILIKE 'a%', contains('ABC', 'b'), startswith('ABC', 'a'), "
            "endswith('ABC', 'c'), instr('ABC', 'b'), locate('b', 'ABC'), 'ABC' RLIKE 'b', "
            "replace('ABC', 'b', 'x'), 'ABC' = 'abc'",
        ),
        Obs(
            "string-substring",
            "SELECT p, l, substring('héllo', p, l), substr('héllo', p, l) FROM VALUES "
            "(1, 2), (0, 2), (-1, 2), (-3, 2), (-5, 2), (-6, 2), (-10, 3), (2, -1), (2, 0), "
            "(6, 1), (2, 2147483647), (-2147483648, 2147483647) AS t(p, l)",
        ),
        Obs(
            "string-substring-no-length",
            "SELECT p, substring('héllo', p) FROM VALUES (0), (1), (-2), (-10), (10) AS t(p)",
        ),
        Obs(
            "string-substring-bigint",
            "SELECT substring('hello', p, 2) FROM VALUES (4294967297L) AS t(p)",
        ),
        Obs(
            "string-substring-bigint-length",
            "SELECT substring('hello', 2, l) FROM VALUES (4294967297L) AS t(l)",
        ),
        Obs(
            "string-positions",
            "SELECT instr(s, 'l'), locate('l', s), locate('l', s, 4), position('l' IN s), "
            "instr(s, 'z'), instr(s, ''), locate('l', s, 0), length(s), octet_length(s), char_length(s) "
            "FROM VALUES ('héllo') AS t(s)",
        ),
        Obs(
            "string-length",
            "SELECT s, length(s), char_length(s), octet_length(s), reverse(s) FROM VALUES "
            "('😀a'), ('éx'), ('') AS t(s)",
        ),
        Obs(
            "string-trim",
            "SELECT '[' || trim(s) || ']', '[' || btrim(s) || ']', '[' || ltrim(s) || ']', "
            "'[' || rtrim(s) || ']', '[' || trim(BOTH 'x' FROM 'xxaxx') || ']' FROM VALUES "
            "(' \ta\n ') AS t(s)",
        ),
        Obs(
            "string-misc",
            "SELECT ascii('é'), ascii(''), repeat('ab', 2), repeat('ab', -1), "
            "levenshtein('kitten', 'sitting'), levenshtein('héllo', 'hello'), replace('aaa', 'a', ''), "
            "replace('abc', '', 'x'), startswith('abc', ''), startswith('abc', NULL)",
        ),
        Obs(
            "string-concat-null",
            "SELECT concat('a', NULL), 'a' || NULL, concat_ws(',', 'a', NULL, 'b'), concat(), "
            "concat_ws(',', NULL)",
        ),
        Obs(
            "string-regex",
            "SELECT regexp_extract('abc', 'x', 0), regexp_extract('abc', '(b)', 1), "
            "regexp_extract('abc', '(x)?b', 1), regexp_replace('abc', '(b)', '[$1]'), "
            "regexp_replace('abc', '(b)', '[\\\\1]'), '٣' RLIKE '^\\\\d$', 'é' RLIKE '^\\\\w$', "
            "'É' RLIKE '(?i)é', regexp_like('a\\nb', 'a.b'), regexp_extract_all('a1b22', '\\\\d+', 0), "
            "regexp_count('aaa', 'aa'), regexp_instr('xabc', 'b')",
        ),
        Obs("string-regex-invalid", "SELECT 'a' RLIKE '('"),
        Obs("string-regex-group-out-of-range", "SELECT regexp_extract('abc', '(b)', 2)"),
        Obs(
            "string-regex-null-pattern",
            "SELECT regexp_extract('abc', NULL, 0), regexp_replace('abc', 'b', NULL), 'abc' RLIKE NULL",
        ),
        Obs(
            "string-digests",
            "SELECT md5('abc'), sha2('abc', 256), sha1('abc'), crc32('abc'), md5('é'), "
            "sha2('abc', 0), sha2('abc', 1), md5(CAST('abc' AS BINARY)), typeof(md5('a'))",
        ),
        Obs(
            "string-order",
            "SELECT s FROM VALUES ('b'), ('B'), ('a'), ('é'), ('z'), (''), ('😀'), ('Ａ') AS t(s) ORDER BY s",
        ),
        Obs(
            "string-like-escape",
            "SELECT 'a_c' LIKE 'a\\\\_c', 'abc' LIKE 'a\\\\_c', 'a%' LIKE 'a!%' ESCAPE '!', "
            "'aXc' LIKE 'a_c', 'é' LIKE '_', '\\n' LIKE '_'",
        ),
    ]


def _temporal_probes() -> list[Obs]:
    return [
        Obs(
            "date-range",
            "SELECT CAST(date_add(d, 1) AS STRING), CAST(d + INTERVAL 1 DAY AS STRING), "
            "CAST(date_sub(DATE'0001-01-01', 1) AS STRING), typeof(date_add(d, 1)) "
            "FROM VALUES (DATE'9999-12-31') AS t(d)",
        ),
        Obs(
            "date-range-far",
            "SELECT CAST(date_add(DATE'2024-01-01', n) AS STRING) FROM VALUES (2000000000), (-2000000000), "
            "(2147483647) AS t(n)",
        ),
        Obs(
            "date-literal-far",
            "SELECT CAST(DATE'+10000-01-01' AS STRING), CAST(make_date(10000, 1, 1) AS STRING), "
            "CAST(DATE'-0044-03-15' AS STRING)",
        ),
        Obs("make-date-zero", "SELECT CAST(make_date(0, 1, 1) AS STRING)"),
        Obs("make-date-invalid", "SELECT make_date(2024, 2, 30)"),
        Obs(
            "timestamp-range",
            "SELECT CAST(ts + INTERVAL 1 DAY AS STRING), CAST(ts - INTERVAL 3000 YEAR AS STRING) FROM VALUES "
            "(TIMESTAMP'9999-12-31 23:59:59') AS t(ts)",
        ),
        Obs(
            "timestamp-add-overflow",
            "SELECT CAST(timestampadd(YEAR, 300000, TIMESTAMP'9999-12-31 23:59:59') AS STRING)",
        ),
        Obs(
            "timestamp-ltz-range",
            "SELECT CAST(ts + INTERVAL 1 DAY AS STRING), typeof(ts) FROM VALUES "
            "(TIMESTAMP_LTZ'9999-12-31 23:59:59') AS t(ts)",
        ),
        Obs(
            "date-months",
            "SELECT add_months(d, 1), d + INTERVAL 1 MONTH, add_months(d, -1), d + INTERVAL '1-1' YEAR TO MONTH, "
            "months_between(DATE'2024-03-31', d) FROM VALUES (DATE'2024-01-31') AS t(d)",
        ),
        Obs(
            "time-type",
            "SELECT t, typeof(t), t + INTERVAL 13 HOUR, t - INTERVAL 13 HOUR FROM VALUES (TIME'12:00:00') AS s(t)",
        ),
        Obs("time-months", "SELECT TIME'12:00:00' + INTERVAL 1 MONTH"),
        Obs(
            "time-type-enabled",
            "SELECT CAST(t AS STRING), typeof(t), CAST(t + INTERVAL 13 HOUR AS STRING), "
            "CAST(t - INTERVAL 13 HOUR AS STRING) FROM VALUES (TIME'12:00:00') AS s(t)",
            conf={"spark.sql.timeType.enabled": "true"},
        ),
        Obs(
            "time-months-enabled",
            "SELECT TIME'12:00:00' + INTERVAL 1 MONTH",
            conf={"spark.sql.timeType.enabled": "true"},
        ),
        Obs(
            "timestamp-precision",
            "SELECT CAST('2024-01-01 00:00:00.123456789' AS TIMESTAMP), "
            "CAST(CAST('2024-01-01 00:00:00.123456789' AS TIMESTAMP) AS STRING), "
            "TIMESTAMP'2024-01-01 00:00:00.1234567', unix_micros(TIMESTAMP_LTZ'1970-01-01 00:00:00.000001')",
        ),
        Obs(
            "timestamp-extremes",
            "SELECT CAST(TIMESTAMP_NTZ'-290308-12-21 19:59:06.224192' AS STRING), "
            "CAST(TIMESTAMP_NTZ'+294247-01-10 04:00:54.775807' AS STRING)",
        ),
        Obs(
            "timestamp-overflow",
            "SELECT TIMESTAMP_NTZ'+294247-01-10 04:00:54.775807' + INTERVAL 1 DAY",
        ),
        Obs(
            "time-zone-gap",
            "SELECT CAST(TIMESTAMP_LTZ'2024-03-10 02:30:00' AS STRING), "
            "CAST(to_utc_timestamp(TIMESTAMP_NTZ'2024-03-10 02:30:00', 'America/New_York') AS STRING), "
            "CAST(CAST(TIMESTAMP_NTZ'2024-03-10 02:30:00' AS TIMESTAMP_LTZ) AS STRING)",
            conf={"spark.sql.session.timeZone": "America/New_York"},
        ),
        Obs(
            "time-zone-overlap",
            "SELECT unix_seconds(TIMESTAMP_LTZ'2024-11-03 01:30:00'), "
            "unix_seconds(to_utc_timestamp(TIMESTAMP_NTZ'2024-11-03 01:30:00', 'America/New_York')), "
            "CAST(TIMESTAMP_LTZ'2024-11-03 05:30:00Z' AS STRING), CAST(TIMESTAMP_LTZ'2024-11-03 06:30:00Z' AS STRING)",
            conf={"spark.sql.session.timeZone": "America/New_York"},
        ),
        Obs(
            "time-zone-convert",
            "SELECT CAST(convert_timezone('UTC', 'Asia/Kolkata', TIMESTAMP_NTZ'2024-01-01 00:00:00') AS STRING), "
            "CAST(from_utc_timestamp(TIMESTAMP_NTZ'2024-01-01 00:00:00', '+05:30') AS STRING), "
            "CAST(TIMESTAMP_LTZ'2024-01-01 00:00:00+05:30' AS STRING), typeof(current_timestamp())",
        ),
        Obs(
            "time-zone-invalid",
            "SELECT from_utc_timestamp(TIMESTAMP_NTZ'2024-01-01 00:00:00', 'Mars/Olympus')",
        ),
        Obs(
            "week-parts",
            "SELECT d, weekofyear(d), dayofweek(d), weekday(d), extract(DOW FROM d), extract(DOW_ISO FROM d), "
            "extract(YEAROFWEEK FROM d), date_part('week', d), extract(QUARTER FROM d), dayofyear(d), "
            "CAST(date_trunc('week', d) AS DATE), trunc(d, 'week') FROM VALUES (DATE'2021-01-03'), (DATE'2024-12-30'), "
            "(DATE'2024-01-01'), (DATE'1969-12-31'), (DATE'0001-01-01') AS t(d)",
        ),
        Obs(
            "pre-1970-parts",
            "SELECT ts, extract(SECOND FROM ts), second(ts), date_trunc('second', ts), date_trunc('month', ts), "
            "date_trunc('year', ts), unix_micros(CAST(ts AS TIMESTAMP_LTZ)) FROM VALUES "
            "(TIMESTAMP_NTZ'1969-12-31 23:59:59.5'), (TIMESTAMP_NTZ'1900-03-01 00:00:00.000001') AS t(ts)",
        ),
        Obs(
            "date-diff",
            "SELECT datediff(DATE'2024-03-01', DATE'2024-02-01'), date_diff(DATE'2024-03-01', DATE'2024-02-01'), "
            "timestampdiff(MONTH, TIMESTAMP'2024-01-31 00:00:00', TIMESTAMP'2024-02-29 00:00:00'), "
            "timestampdiff(YEAR, DATE'2023-02-28', DATE'2024-02-28'), "
            "timestampdiff(DAY, TIMESTAMP'2024-01-01 12:00:00', TIMESTAMP'2024-01-02 11:00:00')",
        ),
        Obs(
            "date-format",
            "SELECT date_format(TIMESTAMP'2024-01-05 13:04:05.123456', 'yyyy-MM-dd HH:mm:ss.SSSSSS EEE'), "
            "date_format(DATE'2021-01-03', 'YYYY-ww e'), CAST(to_date('05/01/2024', 'dd/MM/yyyy') AS STRING)",
        ),
        Obs("date-format-legacy-pattern", "SELECT date_format(DATE'2024-01-05', 'u')"),
        Obs("to-date-invalid", "SELECT to_date('2024-02-30')"),
        Obs(
            "date-format-invalid-input",
            "SELECT to_date('2024-13-01', 'yyyy-MM-dd')",
        ),
        Obs(
            "date-bin",
            "SELECT window(TIMESTAMP'2024-01-01 00:07:00', '5 minutes').start, "
            "date_trunc('hour', TIMESTAMP'2024-01-01 00:07:00')",
        ),
    ]


def _cast_probes() -> list[Obs]:
    return [
        Obs(
            "cast-double-to-int",
            "SELECT x, CAST(x AS TINYINT), CAST(x AS SMALLINT), CAST(x AS INT), CAST(x AS BIGINT) FROM VALUES "
            "(1.9D), (-1.9D), (2.5D), (-2.5D), (130.0D), (40000.0D), (3e9D), (1e20D), "
            f"({_double('NaN')}), ({_double('Infinity')}), (-{_double('Infinity')}) AS s(x)",
        ),
        Obs(
            "cast-decimal-to-int",
            "SELECT x, CAST(x AS INT), CAST(x AS TINYINT) FROM VALUES (CAST(1.9 AS DECIMAL(10,2))), "
            "(CAST(-1.9 AS DECIMAL(10,2))), (CAST(300.5 AS DECIMAL(10,2))) AS s(x)",
        ),
        Obs(
            "cast-int-narrow",
            "SELECT CAST(x AS TINYINT), CAST(x AS INT), CAST(x AS FLOAT), CAST(x AS DOUBLE) FROM VALUES "
            "(300L), (9007199254740993L), (9223372036854775807L) AS s(x)",
        ),
        Obs(
            "cast-string-to-int",
            "SELECT s, CAST(s AS INT) FROM VALUES (' 12 '), ('+12'), ('-0'), ('1e3'), ('1.5'), ('-1.9'), "
            "('12abc'), ('0x10'), (''), ('\t7\n'), ('2147483648'), ('١٢') AS t(s)",
        ),
        Obs(
            "cast-string-to-double",
            "SELECT s, CAST(s AS DOUBLE), CAST(s AS FLOAT) FROM VALUES ('nan'), ('NaN'), ('-nan'), ('inf'), "
            "('Infinity'), ('-infinity'), ('+Inf'), (' 1.5 '), ('1e400'), ('1e-400'), ('1.5d'), ('1.5f'), "
            "('0x1p3'), ('.5'), ('5.'), ('1_000') AS t(s)",
        ),
        Obs(
            "cast-string-to-decimal",
            "SELECT s, CAST(s AS DECIMAL(10,2)) FROM VALUES ('1.005'), ('1.015'), ('-1.005'), (' 2 '), "
            "('1e2'), ('123456789012') AS t(s)",
        ),
        Obs(
            "try-cast-string-parsing",
            "SELECT s, try_cast(s AS INT), try_cast(s AS DOUBLE), try_cast(s AS DECIMAL(10,2)), "
            "try_cast(s AS BOOLEAN) FROM VALUES (' 12 '), ('+12'), ('1e3'), ('1.5'), ('12abc'), ('0x10'), "
            "(''), ('nan'), ('-nan'), ('Infinity'), ('1.5d'), ('0x1p3'), ('1_000'), ('t'), ('yes'), "
            "('2'), ('1.005') AS t(s)",
            note="try_cast parses as the ANSI cast does and gives NULL where it would raise",
        ),
        Obs(
            "try-cast-string-to-date",
            "SELECT s, CAST(try_cast(s AS DATE) AS STRING) FROM VALUES ('2024-01-05'), ('2024-1-5'), "
            "(' 2024-01-05 '), ('2024-01-05T10:00'), ('2024-01-05 10:00:00'), ('2024'), ('2024-01'), "
            "('2024-02-30'), ('+10000-01-01'), ('05/01/2024') AS t(s)",
        ),
        Obs(
            "try-cast-numeric",
            "SELECT x, try_cast(x AS TINYINT), try_cast(x AS INT), try_cast(x AS BIGINT) FROM VALUES "
            f"(1.9D), (-1.9D), (130.0D), (3e9D), (1e20D), ({_double('NaN')}), ({_double('Infinity')}) AS s(x)",
        ),
        Obs(
            "cast-string-to-bool",
            "SELECT s, CAST(s AS BOOLEAN) FROM VALUES ('true'), ('TRUE '), ('t'), ('yes'), ('y'), ('1'), "
            "('false'), ('f'), ('no'), ('0'), ('2'), ('') AS t(s)",
        ),
        Obs(
            "cast-string-to-date",
            "SELECT s, CAST(CAST(s AS DATE) AS STRING) FROM VALUES ('2024-01-05'), ('2024-1-5'), (' 2024-01-05 '), "
            "('2024-01-05T10:00'), ('2024-01-05 10:00:00'), ('2024'), ('2024-01'), ('2024-02-30'), "
            "('+10000-01-01'), ('05/01/2024') AS t(s)",
        ),
        Obs(
            "cast-string-to-timestamp",
            "SELECT s, CAST(s AS TIMESTAMP) FROM VALUES ('2024-01-05 10:00:00'), ('2024-01-05T10:00:00Z'), "
            "('2024-01-05 10:00:00+02:00'), ('2024-01-05'), ('2024-01-05 25:00:00') AS t(s)",
        ),
        Obs(
            "cast-to-string",
            "SELECT CAST(1e20D AS STRING), CAST(1e-5D AS STRING), CAST(0.1D AS STRING), CAST(100.0D AS STRING), "
            "CAST(1e7D AS STRING), CAST(1.0E-3D AS STRING), CAST(123456789.0D AS STRING), CAST(-0.0D AS STRING), "
            f"CAST({_double('NaN')} AS STRING), CAST({_double('Infinity')} AS STRING), "
            "CAST(CAST(0.1 AS FLOAT) AS STRING), CAST(true AS STRING), CAST(CAST(1.50 AS DECIMAL(10,2)) AS STRING), "
            "CAST(CAST(0.0000001 AS DECIMAL(20,10)) AS STRING), CAST(DATE'0001-01-01' AS STRING), "
            "CAST(TIMESTAMP'2024-01-05 10:00:00.120' AS STRING), CAST(INTERVAL 1 DAY AS STRING), "
            "CAST(array(1, NULL) AS STRING), CAST(named_struct('a', 1, 'b', CAST(NULL AS INT)) AS STRING), "
            "CAST(X'00FF' AS STRING)",
        ),
        Obs(
            "cast-to-bool",
            "SELECT CAST(2 AS BOOLEAN), CAST(0.0D AS BOOLEAN), "
            f"CAST({_double('NaN')} AS BOOLEAN), CAST(true AS INT)",
        ),
        Obs(
            "try-variants",
            "SELECT try_cast('abc' AS INT), try_cast(1e20D AS INT), try_add(9223372036854775807L, 1L), "
            "try_subtract(-9223372036854775808L, 1L), try_multiply(9223372036854775807L, 2L), "
            "try_divide(1, 0), try_mod(1, 0), try_element_at(array(1), 5), try_to_number('x', '9'), "
            "try_to_timestamp('nope'), try_cast(300 AS TINYINT)",
        ),
        Obs(
            "try-aggregates",
            "SELECT try_sum(x), try_avg(x) FROM VALUES (9223372036854775807L), (1L) AS s(x)",
        ),
        Obs(
            "try-still-raises",
            "SELECT try_cast(array('a') AS ARRAY<INT>), try_divide(1, 0) + (1 div 0)",
            note="the second column raises from outside the try_ form",
        ),
        Obs("try-regex-still-raises", "SELECT try_cast(regexp_extract('a', '(', 0) AS INT)"),
    ]


def _null_probes() -> list[Obs]:
    return [
        Obs(
            "kleene",
            "SELECT a, b, a AND b, a OR b, NOT a FROM VALUES (NULL, false), (NULL, true), (NULL, NULL), "
            "(true, NULL) AS s(a, b)",
        ),
        Obs(
            "bool-aggregates",
            "SELECT bool_and(a), bool_or(a), every(a), some(a), count(a) FROM VALUES "
            "(true), (CAST(NULL AS BOOLEAN)) AS s(a)",
        ),
        Obs(
            "bool-aggregates-null",
            "SELECT bool_and(a), bool_or(a) FROM VALUES (CAST(NULL AS BOOLEAN)), (CAST(NULL AS BOOLEAN)) AS s(a)",
        ),
        Obs(
            "null-join-keys",
            "SELECT (SELECT count(*) FROM VALUES (1), (NULL) AS l(x) JOIN VALUES (1), (NULL) AS r(y) ON x = y), "
            "(SELECT count(*) FROM VALUES (1), (NULL) AS l(x) JOIN VALUES (1), (NULL) AS r(y) ON x <=> y), "
            "(SELECT count(*) FROM VALUES (1), (NULL) AS l(x) JOIN VALUES (1), (NULL) AS r(y) "
            "ON x IS NOT DISTINCT FROM y)",
        ),
        Obs(
            "null-group-keys",
            "SELECT x, count(*) FROM VALUES (1), (NULL), (NULL) AS s(x) GROUP BY x ORDER BY x",
        ),
        Obs(
            "null-in",
            "SELECT 1 IN (2, NULL), 1 NOT IN (2, NULL), 1 IN (SELECT * FROM VALUES (NULL) AS s(x))",
        ),
        Obs(
            "null-functions",
            "SELECT abs(NULL), NULL + 1, coalesce(NULL, 1), nvl(NULL, 2), greatest(1, NULL), least(1, NULL), "
            "nanvl(CAST('NaN' AS DOUBLE), NULL), length(NULL), upper(NULL)",
        ),
    ]


def _nested_probes() -> list[Obs]:
    return [
        Obs(
            "array-compare",
            "SELECT a, b, a < b, a = b, a <=> b, greatest(a, b) FROM VALUES "
            "(array(1, NULL), array(1, 2)), (array(1, NULL), array(1, NULL)), (array(1), array(1, 2)), "
            "(array(CAST(NULL AS INT)), array(0)), (array(2), array(1, 5)) AS s(a, b)",
        ),
        Obs(
            "array-sort-order",
            "SELECT a FROM VALUES (array(1, 2)), (array(1, NULL)), (array(1)), (array(CAST(NULL AS INT))), "
            "(CAST(NULL AS ARRAY<INT>)), (array()) AS s(a) ORDER BY a",
        ),
        Obs(
            "array-sort-order-desc",
            "SELECT a FROM VALUES (array(1, 2)), (array(1, NULL)), (array(1)), (array(CAST(NULL AS INT))), "
            "(CAST(NULL AS ARRAY<INT>)) AS s(a) ORDER BY a DESC",
        ),
        Obs(
            "array-min-max",
            "SELECT min(a), max(a) FROM VALUES (array(1, NULL)), (array(1, 2)), (array(1)) AS s(a)",
        ),
        Obs(
            "array-element-functions",
            "SELECT sort_array(array(2, NULL, 1)), sort_array(array(2, NULL, 1), false), "
            "array_sort(array(2, NULL, 1)), array_max(array(1, NULL, 3)), array_min(array(CAST('NaN' AS DOUBLE), 1.0D))",
        ),
        Obs(
            "array-index",
            "SELECT element_at(a, 1), element_at(a, -1), element_at(a, -3), a[0], a[2], get(a, 5), "
            "get(a, -1), try_element_at(a, 5), try_element_at(a, -5) FROM VALUES (array(10, 20, 30)) AS s(a)",
        ),
        Obs("array-element-at-out", "SELECT element_at(array(10, 20, 30), 5)"),
        Obs("array-subscript-out", "SELECT array(10, 20, 30)[5]"),
        Obs("array-subscript-negative", "SELECT array(10, 20, 30)[-1]"),
        Obs("array-index-zero", "SELECT element_at(array(10, 20, 30), 0)"),
        Obs(
            "array-size-null",
            "SELECT size(a), cardinality(a), array_size(a) FROM VALUES (CAST(NULL AS ARRAY<INT>)), (array()) AS s(a)",
        ),
        Obs(
            "array-lambdas",
            "SELECT transform(a, x -> x * 2), filter(a, x -> x > 1), exists(a, x -> x > 1), "
            "forall(a, x -> x > 1), aggregate(a, 0, (acc, x) -> acc + x) FROM VALUES (array(1, NULL, 3)) AS s(a)",
        ),
        Obs(
            "struct-equality",
            "SELECT a = b, a <=> b, a < c FROM VALUES (named_struct('x', 1, 'y', CAST(NULL AS INT)), "
            "named_struct('x', 1, 'y', CAST(NULL AS INT)), named_struct('x', 1, 'y', 0)) AS s(a, b, c)",
        ),
        Obs(
            "struct-group-order",
            "SELECT a, count(*) FROM VALUES (named_struct('x', 1, 'y', CAST(NULL AS INT))), "
            "(named_struct('x', 1, 'y', CAST(NULL AS INT))), (named_struct('x', 1, 'y', 0)), "
            "(named_struct('x', CAST(NULL AS INT), 'y', 0)) AS s(a) GROUP BY a ORDER BY a",
        ),
        Obs(
            "array-equality-nan",
            "SELECT array(CAST('NaN' AS DOUBLE)) = array(CAST('NaN' AS DOUBLE)), array(-0.0D) = array(0.0D)",
        ),
        Obs(
            "unnest",
            "SELECT id, x FROM VALUES (1, array(1, 2)), (2, CAST(NULL AS ARRAY<INT>)), (3, array()), "
            "(4, array(CAST(NULL AS INT))) AS s(id, a) LATERAL VIEW explode(a) e AS x ORDER BY id",
        ),
        Obs(
            "unnest-outer",
            "SELECT id, x FROM VALUES (1, array(1, 2)), (2, CAST(NULL AS ARRAY<INT>)), (3, array()) AS s(id, a) "
            "LATERAL VIEW OUTER explode(a) e AS x ORDER BY id",
        ),
        Obs(
            "unnest-select",
            "SELECT explode(a) FROM VALUES (CAST(NULL AS ARRAY<INT>)), (array(7)) AS s(a)",
        ),
    ]


def _aggregate_probes() -> list[Obs]:
    nan, inf = _double("NaN"), _double("Infinity")
    return [
        Obs(
            "empty-aggregates",
            "SELECT sum(x), count(x), count(*), min(x), max(x), avg(x), variance(x), bool_and(x > 0), "
            "collect_list(x), bit_and(x) FROM VALUES (1L) AS s(x) WHERE x > 5",
        ),
        Obs(
            "null-aggregates",
            "SELECT sum(x), count(x), count(*), min(x), avg(x), sum(d), avg(d) FROM VALUES "
            "(CAST(NULL AS BIGINT), CAST(NULL AS DOUBLE)), (CAST(NULL AS BIGINT), CAST(NULL AS DOUBLE)) AS s(x, d)",
        ),
        Obs(
            "empty-group-by",
            "SELECT k, sum(x) FROM VALUES (1, 1L) AS s(k, x) WHERE x > 5 GROUP BY k",
        ),
        Obs(
            "avg-int",
            "SELECT avg(x), typeof(avg(x)), mean(x) FROM VALUES (9007199254740993L), (9007199254740993L) AS s(x)",
        ),
        Obs(
            "avg-int-large",
            "SELECT avg(x) FROM VALUES (9223372036854775807L), (9223372036854775807L) AS s(x)",
        ),
        Obs(
            "avg-int-small",
            "SELECT avg(x), typeof(avg(x)) FROM VALUES (1), (2) AS s(x)",
        ),
        Obs(
            "sum-double-order-1",
            "SELECT sum(x), avg(x) FROM (SELECT /*+ REPARTITION(1) */ * FROM VALUES "
            "(1e16D), (1.0D), (-1e16D), (1.0D) AS s(x))",
        ),
        Obs(
            "sum-double-order-3",
            "SELECT sum(x), avg(x) FROM (SELECT /*+ REPARTITION(3) */ * FROM VALUES "
            "(1e16D), (1.0D), (-1e16D), (1.0D) AS s(x))",
        ),
        Obs(
            "sum-double-order-values",
            "SELECT sum(x) FROM VALUES (1e16D), (1.0D), (-1e16D), (1.0D) AS s(x)",
            note="input order, one partition: a sequential sum",
        ),
        Obs(
            "sum-double-nonfinite",
            f"SELECT sum(x), avg(x), variance(x), stddev(x), min(x), max(x) FROM VALUES ({inf}), (-{inf}) AS s(x)",
        ),
        Obs(
            "sum-double-inf",
            f"SELECT sum(x), avg(x), variance(x), stddev_pop(x) FROM VALUES ({inf}), (1.0D) AS s(x)",
        ),
        Obs(
            "sum-double-nan",
            f"SELECT sum(x), avg(x), variance(x), min(x), max(x), median(x) FROM VALUES ({nan}), (1.0D) AS s(x)",
        ),
        Obs(
            "sum-double-overflow",
            "SELECT sum(x), avg(x), variance(x) FROM VALUES (1e308D), (1e308D) AS s(x)",
        ),
        Obs(
            "sum-float",
            "SELECT sum(x), typeof(sum(x)), avg(x), typeof(avg(x)), max(x), typeof(max(x)) FROM VALUES "
            "(CAST(0.1 AS FLOAT)), (CAST(0.2 AS FLOAT)) AS s(x)",
        ),
        Obs(
            "var-one",
            "SELECT var_samp(x), var_pop(x), stddev_samp(x), stddev_pop(x), variance(x), stddev(x), std(x), "
            "covar_samp(x, x), covar_pop(x, x), corr(x, x) FROM VALUES (2.0D) AS s(x)",
        ),
        Obs(
            "var-one-legacy",
            "SELECT var_samp(x), stddev_samp(x), covar_samp(x, x), corr(x, x) FROM VALUES (2.0D) AS s(x)",
            conf={"spark.sql.legacy.statisticalAggregate": "true"},
        ),
        Obs(
            "var-types",
            "SELECT var_samp(i), typeof(var_samp(i)), var_samp(d), typeof(var_samp(d)), stddev(i), "
            "covar_samp(i, d), corr(i, d), typeof(corr(i, d)) FROM VALUES "
            "(1L, CAST(1.5 AS DECIMAL(10,2))), (2L, CAST(2.5 AS DECIMAL(10,2))), (4L, CAST(3.0 AS DECIMAL(10,2))) AS s(i, d)",
        ),
        Obs(
            "var-cancellation",
            "SELECT var_samp(x), var_pop(x) FROM VALUES (1e9D + 4.0D), (1e9D + 7.0D), (1e9D + 13.0D), (1e9D + 16.0D) AS s(x)",
            note="the exact sample variance is 30",
        ),
        Obs(
            "corr-degenerate",
            "SELECT corr(x, y), covar_samp(x, y), covar_pop(x, y) FROM VALUES (1.0D, 5.0D), (2.0D, 5.0D), "
            "(3.0D, 5.0D) AS s(x, y)",
        ),
        Obs(
            "corr-one-pair",
            "SELECT corr(x, y), covar_samp(x, y) FROM VALUES (1.0D, 2.0D) AS s(x, y)",
        ),
        Obs(
            "quantiles",
            "SELECT median(x), percentile_cont(0.5) WITHIN GROUP (ORDER BY x), "
            "percentile_disc(0.5) WITHIN GROUP (ORDER BY x), percentile(x, 0.25), "
            "percentile_cont(0.25) WITHIN GROUP (ORDER BY x), percentile_disc(0.25) WITHIN GROUP (ORDER BY x), "
            "percentile_approx(x, 0.5), typeof(median(x)) FROM VALUES (1L), (2L), (3L), (10L) AS s(x)",
        ),
        Obs(
            "quantiles-decimal",
            "SELECT median(x), typeof(median(x)), percentile_disc(0.5) WITHIN GROUP (ORDER BY x), "
            "typeof(percentile_disc(0.5) WITHIN GROUP (ORDER BY x)) FROM VALUES "
            "(CAST(1.10 AS DECIMAL(10,2))), (CAST(2.25 AS DECIMAL(10,2))) AS s(x)",
        ),
        Obs(
            "quantiles-double",
            f"SELECT median(x), percentile_disc(0.5) WITHIN GROUP (ORDER BY x), percentile_cont(1.0) WITHIN GROUP "
            f"(ORDER BY x) FROM VALUES (1.0D), ({nan}), (3.0D), (CAST(NULL AS DOUBLE)) AS s(x)",
        ),
        Obs(
            "quantiles-disc-position",
            "SELECT "
            + ", ".join(
                f"percentile_disc({p}) WITHIN GROUP (ORDER BY x), "
                f"percentile_cont({p}) WITHIN GROUP (ORDER BY x)"
                for p in ("0.0", "0.25", "0.26", "0.5", "0.75", "1.0")
            )
            + " FROM VALUES (1), (2), (3), (4) AS s(x)",
        ),
        Obs(
            "first-last",
            "SELECT first(x), last(x), first(x, true), last(x, true), any_value(x), first_value(x) "
            "FROM VALUES (CAST(NULL AS INT)), (1), (2), (CAST(NULL AS INT)) AS s(x)",
        ),
        Obs(
            "first-partitions",
            "SELECT first(x), last(x) FROM (SELECT /*+ REPARTITION(3) */ * FROM range(0, 1000) AS s(x))",
        ),
        Obs(
            "arg-min-max",
            "SELECT min_by(v, k), max_by(v, k), min_by(v, n), max_by(v, n) FROM VALUES "
            "('a', 1, CAST(NULL AS INT)), ('b', 1, 1), ('c', 2, 1), ('d', 2, CAST(NULL AS INT)) AS s(v, k, n)",
        ),
        Obs(
            "mode",
            "SELECT mode(x), mode(x, true), mode(x, false), mode() WITHIN GROUP (ORDER BY x), "
            "mode() WITHIN GROUP (ORDER BY x DESC) FROM VALUES (3), (1), (2), (2), (1), (CAST(NULL AS INT)), "
            "(CAST(NULL AS INT)), (CAST(NULL AS INT)) AS s(x)",
        ),
        Obs(
            "collect-order",
            "SELECT collect_list(x), array_agg(x), string_agg(CAST(x AS STRING), ','), "
            "listagg(CAST(x AS STRING), ',') WITHIN GROUP (ORDER BY x DESC), collect_set(x) "
            "FROM VALUES (3), (CAST(NULL AS INT)), (1), (2) AS s(x)",
        ),
        Obs(
            "collect-partitions",
            "SELECT slice(collect_list(x), 1, 5) FROM (SELECT /*+ REPARTITION(3) */ * FROM range(0, 1000) AS s(x))",
        ),
        Obs(
            "bit-aggregates",
            "SELECT bit_and(x), bit_or(x), bit_xor(x), typeof(bit_and(x)) FROM VALUES "
            "(CAST(6 AS TINYINT)), (CAST(3 AS TINYINT)), (CAST(NULL AS TINYINT)) AS s(x)",
        ),
        Obs(
            "count-distinct-nan",
            f"SELECT count(DISTINCT x), approx_count_distinct(x) FROM VALUES ({nan}), (-{nan}), (0.0D), (-0.0D) AS s(x)",
        ),
    ]


def _window_probes() -> list[Obs]:
    return [
        Obs(
            "ntile",
            "SELECT x, ntile(3) OVER (ORDER BY x), ntile(10) OVER (ORDER BY x) FROM range(1, 8) AS s(x) ORDER BY x",
        ),
        Obs("ntile-zero", "SELECT ntile(0) OVER (ORDER BY x) FROM range(1, 3) AS s(x)"),
        Obs(
            "default-frame",
            "SELECT k, v, sum(v) OVER (ORDER BY k), sum(v) OVER (), first_value(v) OVER (ORDER BY k), "
            "last_value(v) OVER (ORDER BY k), count(*) OVER (ORDER BY k) FROM VALUES (1, 10), (2, 20), (2, 30), "
            "(3, 40) AS s(k, v) ORDER BY k, v",
        ),
        Obs(
            "rank-ties-nulls",
            "SELECT k, row_number() OVER w, rank() OVER w, dense_rank() OVER w, percent_rank() OVER w, "
            "cume_dist() OVER w FROM VALUES (1), (2), (2), (CAST(NULL AS INT)), (CAST(NULL AS INT)), (3) AS s(k) "
            "WINDOW w AS (ORDER BY k) ORDER BY k",
        ),
        Obs(
            "window-values",
            "SELECT k, lag(k) OVER w, lead(k, 2) OVER w, lag(k, 1, -1) OVER w, nth_value(k, 2) OVER w, "
            "nth_value(k, 2) IGNORE NULLS OVER w FROM VALUES (1), (CAST(NULL AS INT)), (3), (4) AS s(k) "
            "WINDOW w AS (ORDER BY k NULLS LAST) ORDER BY k",
        ),
        Obs(
            "window-tie-order",
            "SELECT g, row_number() OVER (ORDER BY g) AS rn, id FROM (SELECT /*+ REPARTITION(3) */ id, id % 2 AS g "
            "FROM range(0, 12) AS s(id)) ORDER BY rn",
            note="which id each tie gets: the input order after a shuffle",
        ),
        Obs(
            "window-range-double",
            "SELECT x, count(*) OVER (ORDER BY x RANGE BETWEEN 1 PRECEDING AND CURRENT ROW) FROM VALUES "
            f"(1.0D), (2.0D), ({_double('NaN')}), ({_double('Infinity')}) AS s(x) ORDER BY x",
        ),
    ]


def _relation_probes() -> list[Obs]:
    return [
        Obs(
            "null-order",
            "SELECT (SELECT collect_list(coalesce(x, -1)) FROM (SELECT x FROM VALUES (2), (NULL), (1) AS s(x) "
            "ORDER BY x)), (SELECT collect_list(coalesce(x, -1)) FROM (SELECT x FROM VALUES (2), (NULL), (1) AS s(x) "
            "ORDER BY x DESC))",
        ),
        Obs(
            "null-order-rows",
            "SELECT x FROM VALUES (2), (NULL), (1) AS s(x) ORDER BY x DESC",
        ),
        Obs(
            "sort-ties",
            "SELECT k, id FROM (SELECT /*+ REPARTITION(3) */ id, id % 2 AS k FROM range(0, 12) AS s(id)) "
            "ORDER BY k LIMIT 6",
            note="ties after a shuffle: the order the partitions return them",
        ),
        Obs(
            "sort-ties-one-partition",
            "SELECT k, id FROM VALUES (1, 'a'), (0, 'b'), (1, 'c'), (0, 'd'), (1, 'e') AS s(k, id) ORDER BY k",
        ),
        Obs(
            "sort-within-partitions",
            "SELECT id % 3 AS k, id FROM range(0, 9) AS s(id) DISTRIBUTE BY id % 3 SORT BY k",
        ),
        Obs(
            "set-operations",
            "SELECT 'union' AS op, sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES (1), (1), "
            "(NULL), (NULL), (2) AS a(x) UNION SELECT * FROM VALUES (1), (NULL), (3) AS b(x)) "
            "UNION ALL SELECT 'union all', sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES (1), "
            "(1), (NULL), (NULL), (2) AS a(x) UNION ALL SELECT * FROM VALUES (1), (NULL), (3) AS b(x)) "
            "UNION ALL SELECT 'intersect', sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES (1), "
            "(1), (NULL), (NULL), (2) AS a(x) INTERSECT SELECT * FROM VALUES (1), (1), (NULL), (3) AS b(x)) "
            "UNION ALL SELECT 'intersect all', sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES "
            "(1), (1), (NULL), (NULL), (2) AS a(x) INTERSECT ALL SELECT * FROM VALUES (1), (1), (NULL), (3) AS b(x)) "
            "UNION ALL SELECT 'except', sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES (1), "
            "(1), (NULL), (NULL), (2) AS a(x) EXCEPT SELECT * FROM VALUES (1), (3) AS b(x)) "
            "UNION ALL SELECT 'except all', sort_array(collect_list(coalesce(x, -1))) FROM (SELECT * FROM VALUES "
            "(1), (1), (NULL), (NULL), (2) AS a(x) EXCEPT ALL SELECT * FROM VALUES (1), (NULL), (3) AS b(x))",
        ),
        Obs(
            "set-operations-nan-zero",
            "SELECT x FROM VALUES (0.0D), ("
            + _double("NaN")
            + ") AS a(x) INTERSECT SELECT * FROM VALUES (-0.0D), "
            "(-" + _double("NaN") + ") AS b(x)",
        ),
        Obs(
            "union-order",
            "SELECT * FROM VALUES (2), (1) AS a(x) UNION ALL SELECT * FROM VALUES (4), (3) AS b(x)",
        ),
    ]


def _execution_probes() -> list[Obs]:
    t = "FROM VALUES (10, 2, '5'), (10, 0, 'x') AS s(a, b, c)"
    return [
        Obs("case-guard", f"SELECT CASE WHEN b <> 0 THEN a div b END {t}"),
        Obs("if-guard", f"SELECT if(b = 0, NULL, a div b), nullif(b, 0) {t}"),
        Obs("and-guard", f"SELECT a {t} WHERE b <> 0 AND a div b > 1"),
        Obs("and-guard-reversed", f"SELECT a {t} WHERE a div b > 1 AND b <> 0"),
        Obs("coalesce-guard", f"SELECT coalesce(a, a div b) {t}"),
        Obs("case-guard-cast", f"SELECT CASE WHEN c RLIKE '^[0-9]+$' THEN CAST(c AS INT) END {t}"),
        Obs(
            "case-guard-cse",
            f"SELECT CASE WHEN c RLIKE '^[0-9]+$' THEN CAST(c AS INT) + CAST(c AS INT) ELSE 0 END {t}",
        ),
        Obs(
            "case-guard-cse-both",
            f"SELECT CASE WHEN c RLIKE '^[0-9]+$' THEN CAST(c AS INT) + 1 ELSE 0 END, "
            f"CASE WHEN c RLIKE '^[0-9]+$' THEN CAST(c AS INT) + 2 ELSE 0 END {t}",
        ),
        Obs(
            "stacked-filter-cast",
            f"SELECT * FROM (SELECT * {t} WHERE c RLIKE '^[0-9]+$') WHERE CAST(c AS INT) > 1",
        ),
        Obs(
            "stacked-filter-divide",
            f"SELECT * FROM (SELECT * {t} WHERE b <> 0) WHERE a div b > 1",
        ),
        Obs(
            "projection-under-filter",
            f"SELECT * FROM (SELECT a div b AS q, b {t}) WHERE b <> 0",
        ),
        Obs(
            "aggregate-guard",
            f"SELECT sum(CASE WHEN b <> 0 THEN a div b END) {t}",
        ),
        Obs(
            "join-filter-order",
            f"SELECT * FROM (SELECT * {t}) l JOIN VALUES (2), (0) AS r(y) ON l.b = r.y WHERE l.b <> 0 AND l.a div l.b = 5",
        ),
        Obs(
            "settings",
            "SELECT 1",
            note="read the settings below (see `settings` of the output)",
        ),
    ]


def _frontend_probes() -> list[Obs]:
    return [
        Obs(
            "literal-types",
            "SELECT typeof(1), typeof(2147483648), typeof(9223372036854775808), typeof(1.5), typeof(1e0), "
            "typeof(1.5D), typeof(1L), typeof(1Y), typeof(1S), typeof(1BD), typeof('a'), typeof(X'00'), "
            "typeof(DATE'2024-01-01'), typeof(TIMESTAMP'2024-01-01 00:00:00'), typeof(NULL), typeof(INTERVAL 1 DAY), "
            "typeof(INTERVAL 1 MONTH), typeof(array(1, 2L)), typeof(1.5E10BD)",
        ),
        Obs(
            "implicit-casts-numeric",
            "SELECT typeof(1 + 1.5), typeof(1L + 1.5), typeof(CAST(1 AS INT) + 1.5D), typeof(1Y + 1S), "
            "typeof(coalesce(1, 1.5D)), 9007199254740993L = 9007199254740992.0D, typeof(1L + 1.5F), "
            "typeof(CAST(1 AS DECIMAL(20,0)) + 1.5D), typeof(1 / 2), typeof(CAST(1 AS DECIMAL(5,0)) / 2)",
        ),
        Obs(
            "implicit-casts-string",
            "SELECT 1 + '2', typeof(1 + '2'), 1 = '1', 1L = '1', DATE'2024-01-01' = '2024-01-01', "
            "typeof(concat(1, 'a')), 1.5D = '1.5'",
        ),
        Obs("implicit-cast-string-fraction", "SELECT '1.5' + 1, typeof('1.5' + 1)"),
        Obs("implicit-cast-int-equals-fraction", "SELECT 1 = '1.0'"),
        Obs("implicit-cast-bad-string", "SELECT 1 + 'x'"),
        Obs("implicit-cast-compare-bad-string", "SELECT 1 = 'x'"),
        Obs(
            "type-names",
            "SELECT typeof(CAST(1 AS BYTE)), typeof(CAST(1 AS SHORT)), typeof(CAST(1 AS INTEGER)), "
            "typeof(CAST(1 AS LONG)), typeof(CAST(1 AS REAL)), typeof(CAST(1 AS DOUBLE)), typeof(CAST(1 AS DEC)), "
            "typeof(CAST(1 AS NUMERIC(5,2))), typeof(CAST('a' AS VARCHAR(3))), typeof(CAST('a' AS CHAR(3))), "
            "typeof(CAST('a' AS BINARY)), typeof(CAST(NULL AS TIMESTAMP_LTZ)), typeof(CAST(NULL AS TIMESTAMP_NTZ)), "
            "typeof(CAST(NULL AS TIMESTAMP)), typeof(CAST(NULL AS MAP<STRING, INT>)), typeof(CAST(NULL AS VARIANT))",
        ),
        Obs(
            "type-names-ltz-default",
            "SELECT typeof(CAST(NULL AS TIMESTAMP)), typeof(TIMESTAMP'2024-01-01 00:00:00')",
            conf={"spark.sql.timestampType": "TIMESTAMP_LTZ"},
        ),
        Obs("integer-literal-overflow", "SELECT 2147483647 + 1"),
        Obs("varchar-length", "SELECT CAST('abcd' AS VARCHAR(3)), length(CAST('a' AS CHAR(3)))"),
    ]


def _writer_probes() -> list[Obs]:
    """The functions `sverify_spark.dialect` writes that no other fact covers,
    spelled as the writer spells them (#271: a run profile states only what a
    fact says)."""
    return [
        Obs("is-null-kinds",
            "SELECT b IS NULL, d IS NULL, s IS NULL FROM VALUES "
            "(CAST(NULL AS BIGINT), CAST(NULL AS DOUBLE), CAST(NULL AS STRING)), "
            "(0L, CAST('NaN' AS DOUBLE), ''), (-9223372036854775808L, -0.0D, 'ß') AS t(b, d, s)"),
        Obs("bigint-to-double",
            "SELECT CAST(x AS DOUBLE) FROM VALUES (9007199254740993L), (9007199254740995L), "
            "(-9223372036854775808L), (9223372036854775807L), (CAST(NULL AS BIGINT)) AS t(x)"),
        Obs("timestamp-to-date",
            "SELECT CAST(CAST(t AS DATE) AS STRING) FROM VALUES (TIMESTAMP_NTZ'1969-12-31 23:59:59.999999'), "
            "(TIMESTAMP_NTZ'0001-01-01 00:00:00'), (TIMESTAMP_NTZ'9999-12-31 23:59:59.999999') AS v(t)"),
        Obs("micros-to-timestamp",
            "SELECT CAST(CAST(timestamp_micros(u) AS TIMESTAMP_NTZ) AS STRING) FROM VALUES (-1L), (0L), "
            "(-62135596800000000L), (253402300799999999L) AS t(u)"),
        Obs("timestamp-to-micros",
            "SELECT unix_micros(CAST(t AS TIMESTAMP_LTZ)) FROM VALUES (TIMESTAMP_NTZ'1969-12-31 23:59:59.999999'), "
            "(TIMESTAMP_NTZ'0001-01-01 00:00:00'), (TIMESTAMP_NTZ'9999-12-31 23:59:59.999999') AS v(t)"),
        Obs("unix-date-diff",
            "SELECT CAST(unix_date(a) AS BIGINT) - CAST(unix_date(b) AS BIGINT) FROM VALUES "
            "(DATE'0001-01-01', DATE'9999-12-31'), (DATE'9999-12-31', DATE'0001-01-01'), "
            "(DATE'1969-12-31', DATE'1970-01-01') AS t(a, b)"),
        Obs("floor-remainder-bigint",
            "SELECT u - (((u - 3L) % 10L + 10L) % 10L) FROM VALUES (-1L), (-7L), (7L), (0L), "
            "(-9223372036854775805L) AS t(u)",
            note="date_bin's floor, as sql/core/temporal.py writes it: `%` truncates, `+ k) % k` floors"),
        Obs("decimal-to-double-text",
            "SELECT CAST(CAST(CAST('0.1' AS DECIMAL(38,37)) AS STRING) AS DOUBLE), "
            "CAST(CAST(CAST('2.5' AS DECIMAL(10,1)) AS STRING) AS DOUBLE), "
            "CAST(CAST(CAST('-0.0' AS DECIMAL(5,1)) AS STRING) AS DOUBLE), "
            "CAST(CAST(CAST('99999999999999999999999999999999999999' AS DECIMAL(38,0)) AS STRING) AS DOUBLE), "
            "CAST(CAST(CAST('0.30000000000000000444089209850062616169' AS DECIMAL(38,38)) AS STRING) AS DOUBLE)"),
        Obs("double-to-decimal-round",
            "SELECT CAST((CAST(CAST(ROUND(x * 100.0D) AS BIGINT) AS DECIMAL(10,0)) * 0.01) AS DECIMAL(10,2)) "
            "FROM VALUES (2.675D), (-2.675D), (0.125D), (1.005D) AS t(x)",
            note="`decimal_cast` of a double at scale 2, as sverify_spark/dialect.py writes it"),
        Obs("repeat-bigint-count", "SELECT REPEAT('', 2147483648L), REPEAT('a', CAST(0 AS BIGINT))"),
        Obs("double-to-bigint-edge",
            "SELECT CAST(9.223372036854775807E18D AS BIGINT), CAST(-9.223372036854775808E18D AS BIGINT), "
            "CAST(9.2233720368547748E18D AS BIGINT)",
            note="`float_to_int` checks -2^63 <= x < 2^63 before the cast"),
    ]  # fmt: skip


def observations() -> list[Obs]:
    return [
        *_int_probes(),
        *_double_probes(),
        *_decimal_probes(),
        *_string_probes(),
        *_temporal_probes(),
        *_cast_probes(),
        *_null_probes(),
        *_nested_probes(),
        *_aggregate_probes(),
        *_window_probes(),
        *_relation_probes(),
        *_execution_probes(),
        *_frontend_probes(),
        *_writer_probes(),
    ]


def _value(v: Any) -> str:
    if v is None:
        return "NULL"
    if isinstance(v, float):
        if math.isnan(v):
            return "-NaN" if math.copysign(1.0, v) < 0 else "NaN"
        return repr(v)
    if isinstance(v, Decimal):
        return str(v)
    if isinstance(v, (dt.datetime, dt.date, dt.time)):
        return v.isoformat()
    if isinstance(v, (bytes, bytearray)):
        return "X'" + bytes(v).hex().upper() + "'"
    if isinstance(v, list):
        return "[" + ", ".join(_value(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(f"{_value(k)}: {_value(x)}" for k, x in v.items()) + "}"
    if hasattr(v, "asDict"):
        return "{" + ", ".join(f"{k}: {_value(x)}" for k, x in v.asDict().items()) + "}"
    return str(v)


def _run(spark: Any, sql: str) -> str:
    try:
        rows = spark.sql(sql).collect()
    except Exception as e:  # noqa: BLE001 - every error is a result here
        cond = None
        for name in ("getCondition", "getErrorClass"):
            fn = getattr(e, name, None)
            if fn is not None:
                try:
                    cond = fn()
                except Exception:  # noqa: BLE001
                    cond = None
                if cond:
                    break
        java = getattr(e, "java_exception", None)
        if not cond and java is not None:
            # A Py4JJavaError without an error class: the Java exception's own text.
            cause = java
            while cause.getCause() is not None:
                cause = cause.getCause()
            return f"error {cause.getClass().getName()}: {str(cause.getMessage())[:240]}"
        msg = str(e).strip().splitlines()[0][:240] if str(e).strip() else type(e).__name__
        return f"error {cond or type(e).__name__}: {msg}"
    return "; ".join("(" + ", ".join(_value(x) for x in row) + ")" for row in rows)


def probe(only: set[str] | None = None) -> dict[str, Any]:
    import os
    import time

    import pyspark
    from pyspark.sql import SparkSession

    # The driver turns TIMESTAMP_LTZ values into Python datetimes in its local
    # time zone: pin it to the session's.
    os.environ["TZ"] = "UTC"
    time.tzset()

    builder = SparkSession.builder.appName("sverify-probe-spark")
    for k, v in BASE_CONF.items():
        builder = builder.config(k, v)
    spark = builder.getOrCreate()
    spark.sparkContext.setLogLevel("OFF")
    out: list[dict[str, Any]] = []
    for o in observations():
        if only and o.construct not in only:
            continue
        results: dict[str, str] = {}
        for ansi in ("true", "false"):
            for path in ("folded", "codegen"):
                conf = {
                    "spark.sql.ansi.enabled": ansi,
                    "spark.sql.optimizer.excludedRules": CODEGEN_EXCLUDED
                    if path == "codegen"
                    else "",
                    **o.conf,
                }
                old = {k: spark.conf.get(k, None) for k in conf}
                for k, v in conf.items():
                    spark.conf.set(k, v)
                try:
                    results[f"ansi={ansi} {path}"] = _run(spark, o.sql)
                finally:
                    for k, v in old.items():
                        if v is None:
                            spark.conf.unset(k)
                        else:
                            spark.conf.set(k, v)
        observed: dict[str, str] = {}
        for ansi in ("true", "false"):
            f, c = results[f"ansi={ansi} folded"], results[f"ansi={ansi} codegen"]
            if f == c:
                observed[f"ansi={ansi}"] = f
            else:
                observed[f"ansi={ansi} folded"] = f
                observed[f"ansi={ansi} codegen"] = c
        entry: dict[str, Any] = {"construct": o.construct, "sql": o.sql}
        if o.conf:
            entry["conf"] = o.conf
        if o.note:
            entry["note"] = o.note
        entry["observed"] = observed
        out.append(entry)
        print(o.construct, file=sys.stderr)
    import platform

    settings = dict(BASE_CONF)
    settings["spark.sql.optimizer.excludedRules (codegen path)"] = CODEGEN_EXCLUDED
    row = spark.sql("SELECT java_method('java.lang.System', 'getProperty', 'java.version')").first()
    java = str(row[0]) if row is not None else "unknown"
    spark.stop()
    return {
        "spark": pyspark.__version__,
        "java": java,
        "platform": f"{platform.system()} {platform.machine()}",
        "driver_tz": "UTC",
        "settings": settings,
        "probes": out,
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help=f"write {OUT}")
    parser.add_argument("--out", type=Path, help="write here instead")
    parser.add_argument(
        "--only", nargs="*", help="run only these constructs (prints, never writes)"
    )
    args = parser.parse_args(argv)
    found = probe(set(args.only) if args.only else None)
    text = json.dumps(found, indent=1, ensure_ascii=False) + "\n"
    if args.only:
        print(text)
    elif args.write or args.out:
        (args.out or OUT).write_text(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
