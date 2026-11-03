# duckdb: facts

Generated from [facts/](facts/) by `uv run python -m sverify_dev.facts --write`; do not edit by hand. One JSON document per finding, in the format of [fact.schema.json](../fact.schema.json). Version checked: 2.0.0.

| Id | Finding | Area | Status | Verdict | ≈ entries | Last checked |
|---|---|---|---|---|---:|---|
| [duckdb-R1](#duckdb-r1) | Integer overflow of `+ - *` and negation | integers | deviation | deviation: unbounded, and reported as a warning | 80 | 2026-11-02 |
| [duckdb-R1-min](#duckdb-r1-min) | `abs(MIN)` and `divide(MIN, -1)` | integers | no-finding | no finding (`verify`: overflow error) |  | 2026-11-01 |
| [duckdb-R2](#duckdb-r2) | Integer division by zero | integers | no-finding | no finding (`verify`: division by zero error) | 23 | 2026-11-02 |
| [duckdb-R3](#duckdb-r3) | Integer `modulus`: zero divisor and sign | integers | open | no finding; `division_type` open, no diff |  | 2026-11-02 |
| [duckdb-R4](#duckdb-r4) | `modulus` on doubles | doubles | fixed | fixed (#203): C's `fmod` (no such Substrait function) | 30 | 2026-11-02 |
| [duckdb-R5](#duckdb-r5) | Double division by zero | doubles | fixed | fixed (#204): an error unless the plan asks for IEEE, LIMIT or NULL | 10 | 2026-11-02 |
| [duckdb-R6](#duckdb-r6) | Integer `sum` | aggregates | deviation | deviation: unbounded, and reported as a warning | 5 | 2026-11-02 |
| [duckdb-R7](#duckdb-r7) | `sum`/`avg` of a double constant | aggregates | fixed | fixed (#205) | 3 | 2026-11-01 |
| [duckdb-R8](#duckdb-r8) | A cast to a narrower integer that does not fit | casts | no-finding | no finding (`verify`: cast out of range error) | 10 | 2026-11-01 |
| [duckdb-R9](#duckdb-r9) | Casts of doubles and decimals to integers: rounding | casts | decided | decided: truncate; DuckDB shim | 28 | 2026-11-02 |
| [duckdb-R10](#duckdb-r10) | Casts between date and timestamp literals | temporal | fixed | fixed (#206) | 60 | 2026-11-01 |
| [duckdb-R11](#duckdb-r11) | Ordering comparisons of lists | nested | shimmed | fixed (#207): lexicographic; DuckDB shim | 22 | 2026-11-01 |
| [duckdb-R12](#duckdb-r12) | `fp32` | doubles | fixed | fixed (#208): `fp32` arithmetic refused until modelled | 5 | 2026-11-02 |
| [duckdb-R13](#duckdb-r13) | `substring` with a negative start | strings | fixed | fixed (#209): `WRAP_FROM_END` | 10 | 2026-11-02 |
| [duckdb-R14](#duckdb-r14) | `-0.0` and `0.0` | doubles | decided | decided: one zero; DuckDB shim | 2 | 2026-11-02 |
| [duckdb-R15-atan2](#duckdb-r15-atan2) | `atan2(0, 0)` | doubles | shimmed | no option matches: 0, where the reference raises |  | 2026-11-02 |
| [duckdb-R15-digests](#duckdb-r15-digests) | `md5`, `sha256` of VARCHAR | strings | no-finding | the reference |  | 2026-11-02 |
| [duckdb-R15-double-arith](#duckdb-r15-double-arith) | `DOUBLE + - * /` | doubles | shimmed | no option matches: NaN from ±inf; `/` by zero is IEEE |  | 2026-11-02 |
| [duckdb-R15-double-modulus](#duckdb-r15-double-modulus) | `DOUBLE % DOUBLE` | doubles | shimmed | no option matches: NaN for a zero divisor or an infinite dividend |  | 2026-11-02 |
| [duckdb-R15-elementary](#duckdb-r15-elementary) | `abs`, `floor`, `ceil`, `exp`, `atan` | doubles | no-finding | the reference |  | 2026-11-02 |
| [duckdb-R15-int-arith](#duckdb-r15-int-arith) | `BIGINT + - *` and `-BIGINT` | integers | no-finding | matches `overflow: ERROR` |  | 2026-11-02 |
| [duckdb-R15-int-divide](#duckdb-r15-int-divide) | `BIGINT // BIGINT` | integers | no-finding | matches `on_division_by_zero: ERROR` |  | 2026-11-02 |
| [duckdb-R15-int-modulus](#duckdb-r15-int-modulus) | `BIGINT % BIGINT` | integers | shimmed | no option matches: `MIN % -1` raises |  | 2026-11-02 |
| [duckdb-R15-math-domain](#duckdb-r15-math-domain) | `power`, `sqrt`, `ln`, `log10`, `log2`, `asin`, `acos`, `sin`, `cos`, `tan` | doubles | shimmed | no option matches: NaN outside the domain, `-inf` for a logarithm of 0 |  | 2026-11-02 |
| [duckdb-R15-regexp](#duckdb-r15-regexp) | `regexp_extract`, `regexp_replace` of constant patterns, on ASCII text | strings | no-finding | the reference (RE2's meaning, #50) |  | 2026-11-02 |
| [duckdb-R15-round](#duckdb-r15-round) | `round(DOUBLE)` | doubles | no-finding | matches `rounding: TIE_AWAY_FROM_ZERO` |  | 2026-11-02 |
| [duckdb-R15-round-digits](#duckdb-r15-round-digits) | `round(DOUBLE, d)` for `d` from -1000 to 400 | doubles | no-finding | the reference (DuckDB's formula since #335) |  | 2026-11-02 |
| [duckdb-R15-shift-left](#duckdb-r15-shift-left) | `BIGINT << BIGINT` | integers | shimmed | no option matches |  | 2026-11-02 |
| [duckdb-R15-shift-right](#duckdb-r15-shift-right) | `BIGINT >> BIGINT` | integers | shimmed | no option matches |  | 2026-11-02 |
| [duckdb-F1](#duckdb-f1) | `/` and `//` on integers | integers | no-finding | frontend |  | 2026-11-01 |
| [duckdb-F2](#duckdb-f2) | NULLs in `ORDER BY` | relations | no-finding | frontend |  | 2026-11-01 |
| [duckdb-F3](#duckdb-f3) | Integer literal types | integers | no-finding | frontend |  | 2026-11-01 |
| [duckdb-F4](#duckdb-f4) | Collations, macros and identifiers | strings | no-finding | frontend |  | 2026-11-01 |

Settings the facts depend on (probes check every value):

- `default_null_order`: duckdb-F2
- `error_on_division_by_zero`: duckdb-R2, duckdb-R3, duckdb-R4
- `ieee_floating_point_ops`: duckdb-R4, duckdb-R5
- `integer_division`: duckdb-F1

## <a id="duckdb-r1"></a>duckdb-R1. Integer overflow of `+ - *` and negation

duckdb 2.0.0 · integers · deviation · `+`, `-`, `*`, `unary -`, `add`, `subtract`, `multiply`, `negate` · #185

DuckDB raises `Out of Range Error: Overflow …` at the declared width, `TINYINT` included, which is the reference (native). If a plan asks for `SILENT` or `SATURATE`, it needs a shim: compute in `HUGEINT` and wrap, `((x::HUGEINT + y + 2^(w-1)) % 2^w + 2^w) % 2^w - 2^(w-1)`, or clamp, `LEAST(GREATEST(x::HUGEINT + y, MIN_w), MAX_w)`, then cast back. `HUGEINT` holds every `i64` product, so both are exact. The written plan must emit the arithmetic at its declared width (S2 in the [README](README.md)).

Frontend (duckdb-F3): DuckDB gives an integer literal the narrowest type that holds it, so `100::TINYINT + 50` is an `i8` addition in DuckDB, and an `i64` one in DataFusion's plan.

Reference:

Substrait and the reference: `add`, `subtract`, `multiply`, `negate` and `abs` on `i8`/`i16`/`i32`/`i64` return the same type; `divide` on integers overflows for `MIN / -1`. With `overflow` omitted, the reference raises when the result does not fit the declared type.

Lean, `+ - *` and negation: deviation. `Rel.eval`'s integers are unbounded, and `UnFn.wrap n`, which marks arithmetic narrower than 64 bits, is the identity ([`Expr.lean:134`](../../SubstraitLean/Expr.lean#L134)). `verify` reports the overflow only as a warning (`may wrap around`, not an error), and the parser accepts only `SILENT` for `+ - *` ([`Parse.lean:770`](../../SubstraitLean/Parse.lean#L770)). So `9223372036854775800 + 5000` and `100::TINYINT + 50::TINYINT` answer `9223372036854780800` and `150`, with no error, where the reference raises. The fix: report overflow at the declared width as an error, and accept `overflow: ERROR` (and the omitted option) rather than only `SILENT`.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [overflow/integer_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/integer_overflow.test); [overflow/bigint_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/bigint_overflow.test); [overflow/table_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/table_overflow.test); [overflow/test_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/test_overflow.test); [function/operator/test_division_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/operator/test_division_overflow.test); [optimizer/expression/test_negation_limits.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/optimizer/expression/test_negation_limits.test); [overflow.json](overflow.json).
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__int_overflow.json](fuzz__int_overflow.json); [fuzz__int_division.json](fuzz__int_division.json). `+`, `-`, `*`, negation, `abs(-2⁶³)`, `-2⁶³ / -1`
- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT + BIGINT` in [probes.json](probes.json); `BIGINT - BIGINT` in [probes.json](probes.json); `BIGINT * BIGINT` in [probes.json](probes.json); `-BIGINT` in [probes.json](probes.json). `overflow: ERROR` matches, under every setting. `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r1-min"></a>duckdb-R1-min. `abs(MIN)` and `divide(MIN, -1)`

duckdb 2.0.0 · integers · no-finding · `abs`, `/`, `//`, `divide` · #185

DuckDB raises `Out of Range Error: Overflow …` for `abs(-2⁶³)` and `-2⁶³ // -1` (native).

Reference:

Substrait and the reference: `abs` and `divide` on `i8`…`i64` return the same type; with `overflow` omitted, `abs(MIN)` and `MIN / -1` raise.

Lean: no finding. `verify` reports `overflow` as an error for both.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/operator/test_division_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/operator/test_division_overflow.test); [function__operator.json](function__operator.json). Counted with duckdb-R1.
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__int_overflow.json](fuzz__int_overflow.json); [fuzz__int_division.json](fuzz__int_division.json).

## <a id="duckdb-r2"></a>duckdb-R2. Integer division by zero

duckdb 2.0.0 · integers · no-finding · `//`, `divide` · `error_on_division_by_zero = true` · #185

Native, under `error_on_division_by_zero = true`, the 2.0 default. With the setting off, DuckDB returns NULL, so it needs a guard, `CASE WHEN y = 0 THEN error('division by zero') ELSE x // y END`. A plan that asks for `NULL` needs `CASE WHEN y = 0 THEN NULL ELSE x // y END`.

Truncation is native: `-7 // 2 = -3`, in every agreeing entry and fuzz case.

Reference:

Substrait and the reference: `divide` on integers truncates toward zero; with `on_division_by_zero` omitted, a zero divisor raises.

Lean: no finding. `verify` reports `division by zero` as an error, so on those rows the plan may raise, which is the reference. `Rel.eval`'s NULL there ([`Expr.lean:195`](../../SubstraitLean/Expr.lean#L195)) is not an answer anyone sees. It is the reference value for `NULL`, should a plan ask for it.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/operator/test_division_by_zero.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/operator/test_division_by_zero.test); [function__operator.json](function__operator.json).
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__int_division.json](fuzz__int_division.json).
- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT // BIGINT` in [probes.json](probes.json). `on_division_by_zero: ERROR` matches; `NULL` with `error_on_division_by_zero` off. `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r3"></a>duckdb-R3. Integer `modulus`: zero divisor and sign

duckdb 2.0.0 · integers · open · `%`, `modulus` · `error_on_division_by_zero = true` · #185, #209

Native, except `MIN % -1`. `%` raises on zero and truncates (`-7 % 2 = -1`, `7 % -2 = 1`), as Lean does, so `division_type` makes no difference between the two. But `MIN % -1` raises `Overflow in division`, where the reference gives 0 (found by the probes, duckdb-R15-int-modulus), so the SQL writes that case out.

If the reference picks `FLOOR`, DuckDB needs a shim, `x % y + CASE WHEN x % y <> 0 AND (x % y < 0) <> (y < 0) THEN y ELSE 0 END`. With `error_on_division_by_zero` off, the guard of duckdb-R2.

Reference:

Substrait and the reference: `modulus` on integers raises on a zero divisor (the decided default for division by zero). Its `division_type: [TRUNCATE, FLOOR]`, the remainder's sign, is open. The parser accepts an explicit `TRUNCATE`, which is what it models, and refuses `FLOOR`.

Lean: no finding. `verify` reports `division by zero` as an error. The remainder truncates (`Int.tmod`).

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/operator/test_division_by_zero.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/operator/test_division_by_zero.test) (lines 28,39,64); [function/numeric/test_mod.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/numeric/test_mod.test) (line 17); [function__operator.json](function__operator.json). Counted with duckdb-R2.
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__int_division.json](fuzz__int_division.json).
- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT % BIGINT` in [probes.json](probes.json). `MIN % -1` raises. `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r4"></a>duckdb-R4. `modulus` on doubles

duckdb 2.0.0 · doubles · fixed · `%`, `modulus`, `sverify_fmod` · `error_on_division_by_zero = true`, `ieee_floating_point_ops = true` · #203, #256, #257

DuckDB's `%` on doubles is `fmod` (native): `7.5 % 2 = 1.5`, `% 0.0` is NaN, or an error with `error_on_division_by_zero`. sverify raises on a zero divisor and writes out the NaN and infinite cases, so only finite operands reach `%`.

Changed (#257): an infinite dividend with a non-NaN divisor now raises a domain error instead of giving NaN, since no operation creates a NaN.

Polars' `%` floors (the sign of the divisor); numpy's `fmod` covers it.

Reference:

Substrait: `functions_arithmetic.yaml` has no `fp32`/`fp64` impl of `modulus`. DataFusion writes `modulus` with `fp64` arguments anyway.

Lean: `"modulus"` always parsed to integer `imod` ([`Parse.lean:956`](../../SubstraitLean/Parse.lean#L956)); `mkFloatCall` ([`Parse.lean:1032`](../../SubstraitLean/Parse.lean#L1032)) had no case for it. On doubles, `imod` worked on the float codes: `7.5 % 2.0` evaluated to a 300-digit integer, `d % 0.0` to NULL. A deviation, and a soundness bug, since the plan was accepted and the result was wrong.

Fixed (#203): a `modulus` of doubles is C's `fmod` (`FloatCode.fmod` in [`Float.lean`](../../SubstraitLean/Float.lean)), as DuckDB, DataFusion and Spark compute `%`: the sign of the dividend (`-7.5 % 2.0 = -1.5`); NaN for a NaN or an infinite dividend; the dividend for an infinite divisor. It is exact, computed on the codes. A zero divisor is an error, as on integers and as #185 decides for an omitted `on_division_by_zero`, so `verify` can prove it absent. Substrait has no such impl; the reference takes the plan DataFusion writes as `fmod`.

Since #256 it is sverify's own function `sverify_fmod`, which Lean writes and the frontends emit; Lean still reads DataFusion's `modulus` of doubles as the same function.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/numeric/decimal_mod.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/numeric/decimal_mod.test) (lines 5,10,16); [function/numeric/test_mod.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/numeric/test_mod.test) (line 11); [types/float/ieee_floating_points.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/float/ieee_floating_points.test) (line 24); [types/float/nan_arithmetic.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/float/nan_arithmetic.test) (line 51); [function__numeric.json](function__numeric.json); [types__float.json](types__float.json).
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__float_arith.json](fuzz__float_arith.json); [fuzz__int_division.json](fuzz__int_division.json).
- 2026-11-01, source-reading, by commit e8b4144 (#203). Compute modulus of doubles as C fmod; a zero divisor raises (commit 8e400f6).
- 2026-11-02, source-reading, by commits 5b5afba (#256) and cb9e558 (#257). `sverify_fmod`; an infinite dividend raises a domain error.
- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `DOUBLE % DOUBLE` in [probes.json](probes.json). NaN for a zero divisor or an infinite dividend (duckdb-R15-double-modulus).

## <a id="duckdb-r5"></a>duckdb-R5. Double division by zero

duckdb 2.0.0 · doubles · fixed · `/`, `divide` · `ieee_floating_point_ops = true` · #204, #257

IEEE, under DuckDB's default settings (corrected by the probes, duckdb-R15). `error_on_division_by_zero` is about integers; doubles follow `ieee_floating_point_ops`, on by default, under which `x / 0.0` is `±inf` and `0.0 / 0.0` NaN, whatever `error_on_division_by_zero` says.

So the reference default (`ERROR`) needs the guard of duckdb-R2, and so does `IEEE` where the dividend is infinite (`inf / inf` is NaN in DuckDB, a domain error in the reference). With `ieee_floating_point_ops` off, a zero divisor raises, which is the reference. `NULL` and `LIMIT` need a `CASE`.

Reference:

Substrait and the reference: `divide` on `fp32`/`fp64` takes `on_division_by_zero: [IEEE, LIMIT, NULL, ERROR]`. With it omitted, a zero divisor raises, `0.0 / 0.0` included.

Lean: deviation, fixed (#204). `Rel.eval` gave IEEE values (`1.0 / 0.0 = inf`, `0.0 / 0.0 = NaN`), `verify` reported nothing for a double divisor, and the parser accepted only `IEEE`. So `7.5::DOUBLE / 0` answered `inf` where the reference raises. Now `verify` reports `division by zero` as an error when the option is omitted or `ERROR`. The parser writes `IEEE`, `LIMIT` and `NULL` as a `CASE` on the divisor (`Parse.divByZero`): IEEE gives `±inf` by the dividend's sign and NaN for `0 / 0`, LIMIT gives `±inf` for `0 / 0` too (the one zero is positive), NULL gives NULL, and a NaN dividend stays NaN. `inf / inf` raises a domain error under every mode (#257), as no operation creates a NaN; only `IEEE`'s `0 / 0`, which the plan asks for, is NaN.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/operator/test_division_by_zero.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/operator/test_division_by_zero.test) (lines 73,98,108,181,186); [function__operator.json](function__operator.json). The first draft said DuckDB raises under `error_on_division_by_zero`; the probes corrected it.
- 2026-11-01, fuzz, by sverify_dev.duckdb_fuzz on homelab (commit 7dbf2f7): [fuzz__float_arith.json](fuzz__float_arith.json). `d / d` with `d = 0.0`
- 2026-11-01, source-reading, by commit 6ab8289 (#204). The division options, mirrored in the SQL reader.
- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `DOUBLE / DOUBLE` in [probes.json](probes.json). No option matches: `/` by zero is IEEE. `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r6"></a>duckdb-R6. Integer `sum`

duckdb 2.0.0 · aggregates · deviation · `sum`, `avg` · #185, #209

Shim. `SUM(BIGINT)` returns `HUGEINT` and never overflows at 64 bits, so DuckDB alone answers where the reference raises. `CAST(SUM(x) AS BIGINT)` raises past `i64`. sverify's written plan already guards this and raises (`test_sum.test:68`).

`avg` of integers: the exact `HUGEINT` sum `//` the count. DataFusion's `avg` is a double, so it refuses an integer one.

Reference:

Substrait and the reference: `sum` of `i8`…`i64` returns `i64?`; with `overflow` omitted, a sum outside `i64` raises.

Lean: deviation. The sum is unbounded, and `verify` reports it as a warning (`may wrap around`, `sumWraps`); the parser accepts only `SILENT`. `SUM(b)` of values summing past `2⁶³` answers `4611686018427388403500`, and `SUM(b)::BIGINT` the same, since a cast to `BIGINT` is not checked.

`avg` of integers (decided on #209, fixed): it follows the plan's declared output type. With `fp64` (DataFusion's plans), it is the mean as a double; with `i64` (Substrait's own impl), it is the exact mean truncated toward zero (`AggFn.iavg`), which always fits.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [aggregate/aggregates/test_sum.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/aggregate/aggregates/test_sum.test) (lines 68,74); [aggregate.json](aggregate.json).
- 2026-11-02, source-reading, by commit ceaf0de (#209). `avg` of integers follows the declared output type.

## <a id="duckdb-r7"></a>duckdb-R7. `sum`/`avg` of a double constant

duckdb 2.0.0 · aggregates · fixed · `sum`, `avg` · #205

DuckDB's sums of doubles are IEEE (native): `inf`, `-inf`, `nan`.

Reference:

Substrait: `sum(fp64)` returns `fp64?`.

Lean: `SUM(CAST('inf' AS DOUBLE))` evaluated to a 500-digit integer, and `avg(42) OVER ()` to `inf`. The aggregate took a constant argument for an integer and added float codes; over a double column it was right. A deviation and a soundness bug. Fixed (#205): a constant argument has its declared type, so `sum(fp64)` adds doubles.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [types/float/nan_aggregates.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/float/nan_aggregates.test) (line 7); [window/test_scalar_window.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/window/test_scalar_window.test) (line 11); [types__float.json](types__float.json); [window.json](window.json).
- 2026-11-01, source-reading, by commit f861bdd (#205). Aggregate constants have their declared type.

## <a id="duckdb-r8"></a>duckdb-R8. A cast to a narrower integer that does not fit

duckdb 2.0.0 · casts · no-finding · `CAST`, `TRY_CAST`, `cast` · #185

Native. `CAST` raises (`Conversion Error`); `RETURN_NULL` is `TRY_CAST`, also native.

Reference:

Substrait and the reference: the plan's cast says `failureBehavior: THROW_EXCEPTION`, so the cast raises.

Lean: no finding. `verify` reports `cast out of range` as an error, and the checker refuses a constant one (`CAST(200 AS TINYINT)`). `Rel.eval`'s NULL there ([`Expr.lean:133`](../../SubstraitLean/Expr.lean#L133)) is the value for `RETURN_NULL`. A cast to `BIGINT` is not checked, which matters only for values that are already outside `i64` (duckdb-R6).

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [overflow/test_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/test_overflow.test) (lines 31,36,54); [overflow/table_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/table_overflow.test) (line 154); [overflow.json](overflow.json).

## <a id="duckdb-r9"></a>duckdb-R9. Casts of doubles and decimals to integers: rounding

duckdb 2.0.0 · casts · decided · `CAST`, `cast` · #209

DuckDB rounds half away from zero natively: `CAST(0.55 AS INTEGER) = 1`, `CAST(-0.55 AS BIGINT) = -1`, and `avg(d)::INTEGER` rounds too.

Shim: sverify's SQL writes `CAST(trunc(x) AS BIGINT)` (`DuckDBDialect.float_to_int`).

Reference:

Substrait: the cast's rounding is not specified.

Lean: truncates (`ftoi`), as DataFusion does. Decided on #209: the reference truncates toward zero, so no Lean change.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [cast/decimal_integer_cast.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/cast/decimal_integer_cast.test); [cast/float_integer_cast.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/cast/float_integer_cast.test); [function/numeric/test_floor_ceil.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/numeric/test_floor_ceil.test); [aggregate/aggregate_state_export/test_combine_aggr.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/aggregate/aggregate_state_export/test_combine_aggr.test) (line 18); [cast.json](cast.json).
- 2026-11-02, source-reading, by commit 5b168e0 (#209). Decided: the reference truncates toward zero.

## <a id="duckdb-r10"></a>duckdb-R10. Casts between date and timestamp literals

duckdb 2.0.0 · temporal · fixed · `CAST`, `cast`, `COALESCE`, `>=` · #206

DuckDB's conversions are the standard ones (native).

Reference:

Substrait: a `date` is a day, and a `precision_timestamp` a point in time. A cast from date to timestamp is that day at midnight.

Lean: a date or timestamp literal was an integer in the model (`argKind`, [`Parse.lean:833`](../../SubstraitLean/Parse.lean#L833)), so `CAST(DATE '2020-05-05' AS TIMESTAMP)` took the `.int → .time` branch ([`Parse.lean:1248`](../../SubstraitLean/Parse.lean#L1248)) and read 18387 days as 18387 µs. `(TIMESTAMP …)::DATE` kept the microsecond count as days. Then `ts >= DATE '1993-08-15'` compared microseconds with days, and `COALESCE(date, timestamp)` mixed both codes. A deviation and a soundness bug.

Fixed (#206): date and timestamp constants keep their kinds; a cast from a date is that day at midnight, a cast from a timestamp floors to its day, and a comparison of a date with a timestamp that the plan does not cast is refused. A cast of a date column to a timestamp is still refused, as before.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [types/date/date_implicit_cast.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/date/date_implicit_cast.test) (line 13); [types/timestamp/test_timestamp.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/timestamp/test_timestamp.test) (lines 119,139); [function/generic/test_if_null.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/generic/test_if_null.test) (line 15); [function/generic/test_if.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/generic/test_if.test) (line 20); [types__date.json](types__date.json); [types__timestamp.json](types__timestamp.json).
- 2026-11-01, source-reading, by commit f861bdd (#206). Date and timestamp casts converted.

## <a id="duckdb-r11"></a>duckdb-R11. Ordering comparisons of lists

duckdb 2.0.0 · nested · shimmed · `<`, `>`, `<=`, `>=`, `lt`, `gt`, `lte`, `gte`, `list_lt` · #207, #209

DuckDB orders lists lexicographically natively, but a NULL element sorts above every value, so `[1, NULL] < [1, 3]` is FALSE.

Shim: it finds the first position whose elements are distinct (`list_position` over `IS DISTINCT FROM`) and gives NULL when one of them is NULL. DataFusion sorts NULL first and Polars has no list order: both refuse.

Reference:

Substrait: `lt(x, y)` (and `gt`, `lte`, `gte`) takes `any1`, and "if either/both of `x` and `y` are `null`, `null` is returned"; it does not define an order on lists.

Lean: `[1, 2] < [1, 3]` was NULL on every row, a deviation. Fixed (#207), with the order decided on #209: lexicographic, element by element (`Value.listLt3`). A proper prefix sorts first, two NULL elements at a position are equal (as in list equality), and a NULL element against a value makes the result NULL: `[1, NULL] < [2]` is TRUE, `[1, NULL] < [1, 3]` is NULL, `[NULL, 1] < [NULL, 2]` is TRUE. Lists of lists are refused. The written plan spells the comparison `list_lt`, so every engine knows it compares lists.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [types/list/list_comparison.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/list/list_comparison.test) (lines 136-186); [types/list/list_null_members.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/list/list_null_members.test); [join/test_nested_inequality.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/join/test_nested_inequality.test) (lines 57,94); [types__list.json](types__list.json).
- 2026-11-01, source-reading, by commit 691a5c4 (#207). Lists are ordered lexicographically.

## <a id="duckdb-r12"></a>duckdb-R12. `fp32`

duckdb 2.0.0 · doubles · fixed · `FLOAT`, `+`, `-`, `*`, `/`, `sqrt`, `CAST` · #208

DuckDB's `FLOAT` is 32 bits (native): `inf`, and `1e308::FLOAT` fails to convert.

Reference:

Substrait: `fp32` and `fp64` are distinct types with their own impls.

Lean: one double kind, so `2e38::FLOAT / 0.1` was `2e39`. A deviation of width (principle 3). Fixed (#208) by refusing what is not modelled: arithmetic on `FLOAT` values (`+ - * /`, `sqrt`, …) and casts to `FLOAT` round to 32 bits, so they are refused ("cast them to DOUBLE first"). Reading a `FLOAT`, comparing it, and widening it to `DOUBLE` (`UnFn.widen`) are exact, as is a `FLOAT` literal, which is the single-precision value of its digits. Modelling binary32 arithmetic is left for later.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [overflow/double_float_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/double_float_overflow.test) (line 43); [cast/double_float_cast.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/cast/double_float_cast.test); [overflow/test_numeric_overflow.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/overflow/test_numeric_overflow.test) (line 11); [optimizer/expression/test_float_identity.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/optimizer/expression/test_float_identity.test) (line 123); [overflow.json](overflow.json).
- 2026-11-02, source-reading, by commit cc1f880 (#208). FLOAT arithmetic is refused until binary32 is modelled.

## <a id="duckdb-r13"></a>duckdb-R13. `substring` with a negative start

duckdb 2.0.0 · strings · fixed · `substring` · #209

`WRAP_FROM_END` is native, but sverify's SQL normalizes the start for every engine (`CASE WHEN a < 0 THEN a + length + 1`, then the `LEFT_OF_BEGINNING` normalization it already had).

DataFusion's own `substring` is `LEFT_OF_BEGINNING`, so a wrapping one whose start is not a constant ≥ 0 is refused there.

Reference:

Substrait: `negative_start: [WRAP_FROM_END, LEFT_OF_BEGINNING, ERROR]`.

Lean: was `LEFT_OF_BEGINNING`, as DataFusion does (`substring('hello' FROM -2 FOR 2) = ''`). Fixed (#209): the reference is `WRAP_FROM_END` when the plan omits the option (`Text.substrWrap`: `'lo'`; a start that wraps past the beginning, or 0, is left of it, so `substring('hello', -10, 7) = 'he'`, as in DuckDB). A plan that sets `LEFT_OF_BEGINNING` gets that (sverify's Ibis producer sets it for the starts it computes); `ERROR` is refused.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [function/string/test_substring.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/function/string/test_substring.test) (lines 129,207); [types/string/test_unicode.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/types/string/test_unicode.test) (lines 31-41); [function__string.json](function__string.json).
- 2026-11-02, source-reading, by commit 5b168e0 (#209). substring counts a negative start from the end.

## <a id="duckdb-r14"></a>duckdb-R14. `-0.0` and `0.0`

duckdb 2.0.0 · doubles · decided · `ORDER BY`, `/`, `-0.0` · #209, #89

DuckDB sorts `-0.0` before `0.0`, and `1.0 / -0.0 = -inf` natively.

Shim: sverify's SQL normalizes `-0.0` to `0.0` on every read and after every operation that can make it (`Dialect.canon`).

Reference:

Substrait: `fp64` is IEEE. The spec says nothing about grouping or ordering `-0.0`.

Lean: one zero (#89), so `1.0 / -0.0` is `inf`, not IEEE's `-inf`. Decided on #209: one zero, so no Lean change.

Checked:

- 2026-11-01, replay, by sverify_dev.slt on DataFusion 51's plans (commit 7dbf2f7): [order/order_by_negative_zero.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/order/order_by_negative_zero.test) `SELECT v, 1.0 / v FROM zero_probe ORDER BY v, id;` (line 28); [order.json](order.json).
- 2026-11-02, source-reading, by commit 5b168e0 (#209). Decided: one zero.

## <a id="duckdb-r15-atan2"></a>duckdb-R15-atan2. `atan2(0, 0)`

duckdb 2.0.0 · doubles · shimmed · `atan2` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

`atan2(0, 0)` is 0.

With `ieee_floating_point_ops` off, a zero divisor of doubles raises, and so do the elementary functions outside their domains (as the reference does), and `power(0, negative)` raises; the NaN of `inf - inf`, `0 * inf` and `inf / inf`, `atan2(0, 0)` and the shifts are unchanged.

Reference:

`atan2(0, 0)` raises.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `atan2(DOUBLE, DOUBLE)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-digests"></a>duckdb-R15-digests. `md5`, `sha256` of VARCHAR

duckdb 2.0.0 · strings · no-finding · `md5`, `sha256` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242, #50

Gives the reference's value on every probed row.

Reference:

`md5`, `sha256`.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#50, commit f1c86f3): `md5(VARCHAR)` in [probes.json](probes.json); `sha256(VARCHAR)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-double-arith"></a>duckdb-R15-double-arith. `DOUBLE + - * /`

duckdb 2.0.0 · doubles · shimmed · `+`, `-`, `*`, `/` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242, #257

Operations on ±inf that have no value give NaN (`inf - inf`, `0 * inf`, `inf / inf`), where the reference raises a domain error (#257); `/` by zero is IEEE (duckdb-R5).

With `ieee_floating_point_ops` off, a zero divisor of doubles raises, and so do the elementary functions outside their domains (as the reference does), and `power(0, negative)` raises; the NaN of `inf - inf`, `0 * inf` and `inf / inf`, `atan2(0, 0)` and the shifts are unchanged.

Reference:

`add` … `divide`: no operation creates a NaN (#257); a zero divisor raises unless the plan asks otherwise.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `DOUBLE + DOUBLE` in [probes.json](probes.json); `DOUBLE - DOUBLE` in [probes.json](probes.json); `DOUBLE * DOUBLE` in [probes.json](probes.json); `DOUBLE / DOUBLE` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-double-modulus"></a>duckdb-R15-double-modulus. `DOUBLE % DOUBLE`

duckdb 2.0.0 · doubles · shimmed · `%` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

NaN for a zero divisor or an infinite dividend (duckdb-R4).

Reference:

`modulus` of doubles is `fmod` (duckdb-R4); a zero divisor and an infinite dividend raise.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `DOUBLE % DOUBLE` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-elementary"></a>duckdb-R15-elementary. `abs`, `floor`, `ceil`, `exp`, `atan`

duckdb 2.0.0 · doubles · no-finding · `abs`, `floor`, `ceil`, `exp`, `atan` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

Gives the reference's value on every probed row.

Reference:

The functions of `functions_arithmetic.yaml` and `functions_rounding.yaml`.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `abs(BIGINT)` in [probes.json](probes.json); `floor(DOUBLE)` in [probes.json](probes.json); `ceil(DOUBLE)` in [probes.json](probes.json); `exp(DOUBLE)` in [probes.json](probes.json); `atan(DOUBLE)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-int-arith"></a>duckdb-R15-int-arith. `BIGINT + - *` and `-BIGINT`

duckdb 2.0.0 · integers · no-finding · `+`, `-`, `*`, `unary -` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

Raises on overflow at 64 bits, under every setting (duckdb-R1).

Reference:

`add`, `subtract`, `multiply`, `negate` with `overflow: ERROR`.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT + BIGINT` in [probes.json](probes.json); `BIGINT - BIGINT` in [probes.json](probes.json); `BIGINT * BIGINT` in [probes.json](probes.json); `-BIGINT` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-int-divide"></a>duckdb-R15-int-divide. `BIGINT // BIGINT`

duckdb 2.0.0 · integers · no-finding · `//` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

Raises on a zero divisor; gives NULL with `error_on_division_by_zero` off (duckdb-R2).

Reference:

`divide` with `on_division_by_zero: ERROR`; `NULL` matches with `error_on_division_by_zero` off.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT // BIGINT` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-int-modulus"></a>duckdb-R15-int-modulus. `BIGINT % BIGINT`

duckdb 2.0.0 · integers · shimmed · `%` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

`MIN % -1` raises `Overflow in division` (duckdb-R3); the SQL writes that case out.

Reference:

`modulus`: `MIN % -1` is 0.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT % BIGINT` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-math-domain"></a>duckdb-R15-math-domain. `power`, `sqrt`, `ln`, `log10`, `log2`, `asin`, `acos`, `sin`, `cos`, `tan`

duckdb 2.0.0 · doubles · shimmed · `power`, `sqrt`, `ln`, `log10`, `log2`, `asin`, `acos`, `sin`, `cos`, `tan` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

NaN outside the domain, `-inf` for a logarithm of 0.

With `ieee_floating_point_ops` off, a zero divisor of doubles raises, and so do the elementary functions outside their domains (as the reference does), and `power(0, negative)` raises; the NaN of `inf - inf`, `0 * inf` and `inf / inf`, `atan2(0, 0)` and the shifts are unchanged.

Reference:

Outside the domain, the reference raises.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `power(DOUBLE, DOUBLE)` in [probes.json](probes.json); `sqrt(DOUBLE)` in [probes.json](probes.json); `ln(DOUBLE)` in [probes.json](probes.json); `log10(DOUBLE)` in [probes.json](probes.json); `log2(DOUBLE)` in [probes.json](probes.json); `asin(DOUBLE)` in [probes.json](probes.json); `acos(DOUBLE)` in [probes.json](probes.json); `sin(DOUBLE)` in [probes.json](probes.json); `cos(DOUBLE)` in [probes.json](probes.json); `tan(DOUBLE)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-regexp"></a>duckdb-R15-regexp. `regexp_extract`, `regexp_replace` of constant patterns, on ASCII text

duckdb 2.0.0 · strings · no-finding · `regexp_extract`, `regexp_replace` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242, #50

With and without `'g'`, DuckDB gives the reference's value on every probed row.

Reference:

`regexp_extract`, `regexp_replace`: RE2's meaning (#50).

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#50, commit f1c86f3): `regexp_extract(VARCHAR, '^(a+)(b)?', 2)` in [probes.json](probes.json); `regexp_replace(VARCHAR, 'a+', '<\0>')` in [probes.json](probes.json); `regexp_replace(VARCHAR, 'a+', '<\0>', 'g')` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-round"></a>duckdb-R15-round. `round(DOUBLE)`

duckdb 2.0.0 · doubles · no-finding · `round` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

Rounds half away from zero.

Reference:

`round` with `rounding: TIE_AWAY_FROM_ZERO`.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `round(DOUBLE)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-round-digits"></a>duckdb-R15-round-digits. `round(DOUBLE, d)` for `d` from -1000 to 400

duckdb 2.0.0 · doubles · no-finding · `round` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242, #335

DuckDB rounds to `d` digits; below zero it computes `round(x / 10^-d) · 10^-d`, and 0 where that is not finite.

Reference:

`round` with a digit count: DuckDB's formula since #335, so the outcomes match on every probed `d`.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#335, commit 4b8d8bb): `round(DOUBLE, -1000)` in [probes.json](probes.json); `round(DOUBLE, -309)` in [probes.json](probes.json); `round(DOUBLE, -308)` in [probes.json](probes.json); `round(DOUBLE, -20)` in [probes.json](probes.json); `round(DOUBLE, -1)` in [probes.json](probes.json); `round(DOUBLE, 1)` in [probes.json](probes.json); `round(DOUBLE, 2)` in [probes.json](probes.json); `round(DOUBLE, 16)` in [probes.json](probes.json); `round(DOUBLE, 308)` in [probes.json](probes.json); `round(DOUBLE, 309)` in [probes.json](probes.json); `round(DOUBLE, 400)` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-shift-left"></a>duckdb-R15-shift-left. `BIGINT << BIGINT`

duckdb 2.0.0 · integers · shimmed · `<<`, `shift_left` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

Raises on a negative operand, on bits shifted out, and on shifts below 0 or beyond 63 (but `0 << y` is 0 for any `y`).

Reference:

`shift_left` drops the bits shifted out, and raises on shifts below 0 or beyond 63.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT << BIGINT` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-r15-shift-right"></a>duckdb-R15-shift-right. `BIGINT >> BIGINT`

duckdb 2.0.0 · integers · shimmed · `>>`, `shift_right` · `error_on_division_by_zero = [true, false]`, `ieee_floating_point_ops = [true, false]` · #242

0 for shifts below 0 or beyond 63 (`-5 >> 64` too).

Reference:

`shift_right` raises on shifts below 0 or beyond 63.

Checked:

- 2026-11-02, probe, by sverify_dev.probe (#242, commit d5efa18): `BIGINT >> BIGINT` in [probes.json](probes.json). `sverify_dev.probe` runs the function at each signature on edge cases (0, ±1, ±2, 3, ±7, the 64-bit bounds, 0.5, ±2.5, 1e308, ±inf, NaN, NULL), one row at a time from columns, under every combination of `error_on_division_by_zero` and `ieee_floating_point_ops`. Lean evaluates the Substrait call on the same rows once per candidate value of its option (`substrait-check --outcomes`), and the candidates whose outcomes all match are DuckDB's options. No input is -0.0 (duckdb-R14).

## <a id="duckdb-f1"></a>duckdb-F1. `/` and `//` on integers

duckdb 2.0.0 · integers · no-finding · frontend · `/`, `//` · `integer_division = false`

In DuckDB, `/` on integers is float division and `//` is integer division; the setting `integer_division` switches `/`.

Reference:

The lift reads `/` as DuckDB does: it divides as doubles, and `//` divides integers.

Checked:

- 2026-11-01, replay, by commit 20b02e9. Recorded from the replay's translation of DuckDB's SQL to DataFusion's (`sverify_dev.slt.translate`).

## <a id="duckdb-f2"></a>duckdb-F2. NULLs in `ORDER BY`

duckdb 2.0.0 · relations · no-finding · frontend · `ORDER BY` · `default_null_order = "nulls_last"`

DuckDB puts NULLs last in both directions; DataFusion puts them first for `DESC`.

Reference:

The replay writes the order out and follows `SET default_null_order`.

Checked:

- 2026-11-01, replay, by commit 20b02e9. Recorded from the replay's translation of DuckDB's SQL to DataFusion's (`sverify_dev.slt.translate`).

## <a id="duckdb-f3"></a>duckdb-F3. Integer literal types

duckdb 2.0.0 · integers · no-finding · frontend · `integer literal`

DuckDB types an integer literal as the narrowest type that holds it (duckdb-R1).

Reference:

`100::TINYINT + 50` is an `i8` addition in DuckDB, and an `i64` one in DataFusion's plan.

Checked:

- 2026-11-01, replay, by commit 20b02e9. Recorded from the replay's translation of DuckDB's SQL to DataFusion's (`sverify_dev.slt.translate`).

## <a id="duckdb-f4"></a>duckdb-F4. Collations, macros and identifiers

duckdb 2.0.0 · strings · no-finding · frontend · `COLLATE`, `CREATE MACRO`

DuckDB has collations (`NOCASE`, `NOACCENT`), macros that shadow functions, and case-insensitive identifiers.

Reference:

The replay skips queries under a collation or macro, and follows the identifiers.

Checked:

- 2026-11-01, replay, by commit 20b02e9. Recorded from the replay's translation of DuckDB's SQL to DataFusion's (`sverify_dev.slt.translate`).
