# Reference semantics

What sverify's plans mean. `Rel.eval` (`SubstraitLean/Rel.lean`) is the
**reference semantics**: `verify` proves things about it, and every engine's
behaviour is stated as a difference from it. This page collects the choices
the project owner decided, mostly in comments on epic
[#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185), and
says for each row whether it holds on `main` or which issue or pull request
brings it there.

Status marks: **✓** holds on `main`; **#n** is the open issue or pull request
that changes it. Rows describe `main` as of this page, not the open pull
requests, except where a row names one.

Where this page and the code disagree, the code is what `verify` proves, and
this page has a bug. Where this page and
[#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185)
disagree, #185 wins; please say so.

After the general sections, each area has its own section: core (numbers and
NULLs), strings, temporal, nested, casts, aggregates, windows and relations.

## What it is

An engine runs a plan **correctly** when, on every input, it gives
`Rel.eval`'s rows or raises an error. It may not give other rows.

The reference is not a model of any engine, DuckDB included. Each engine is
characterized as a **diff** against it (`characterization/<engine>/`): which
behaviours it has natively, which need a shim (a guard, a cast, a `CASE`), and
which the translation refuses. The shims are proved against the reference in
Lean (`SubstraitLean/Profile.lean`: `Profile.reference`,
`Expr.evalP_reference`; `SubstraitLean/Lowering.lean`: `Lowering.lower_correct`,
`Rel.duckdb_shim_sound`).
That each engine matches its profile is tested, not proved. How profiles and
shims work is in [engine-profiles.md](engine-profiles.md).

## Principles

Decided on #185 ("Principles for the reference model"):

| # | Principle | What it means in practice |
|---|---|---|
| 1 | **Substrait's semantics, options included.** | A function means what its extension YAML says. An option set in the plan is part of its meaning. |
| 2 | **The least surprising choice where Substrait is silent**, with its reason. | An option the plan omits, or behaviour the spec leaves open, gets one choice, written down below with the reason. |
| 3 | **Can be emulated on every backend.** | Types keep their declared widths (`i8`…`i64`); there are no unbounded integers. Every choice is one DuckDB, Polars, DataFusion, Spark and Snowflake can follow with a shim. |
| 4 | **Keeps optimizations provable.** | Filter pushdown, reordering, sharding and incremental maintenance stay provable. This is why an error means "may raise" ([Errors](#errors)). |

Engine quirks belong in profiles, never in the reference. Changing the
reference is a breaking change and is treated as one (#185,
"The reference model may need to evolve").

## Errors

`Rel.eval` has no error value. It gives a row's value as if nothing went
wrong, and `verify` reports separately where the plan **may raise**
(`Rel.mayIssues`, `SubstraitLean/Safety.lean`). On a row where an error issue
fires, `Rel.eval`'s value is not the answer.

* **An error means "may raise".** The reference may raise wherever the plan
  hits an error issue. ✓
* **Rewrites are refinements.** An optimized plan may raise in fewer cases
  than the original. It never answers differently and never raises where the
  original didn't. ✓ (#185)
* **An error that can't be ruled out makes the report unproved.**
  `Report.proved` is false until a precondition excludes it. ✓ for division
  by zero, casts out of range, domain errors, decimal precision and the
  other error issues. Integer `+ - *` and negation overflow are still only a
  warning on `main` ("may wrap around"): [#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202),
  [PR #255](https://github.com/AlexanderNenninger/substrait-lean/pull/255).
* **Exception: integer `SUM` overflow** (decided on #202). It is reported as
  "SUM overflow" and does not make the report unproved, because no
  condition on rows can bound how many rows a group has. The written SQL
  guards the sum and every engine raises if it leaves 64 bits, so the job
  never answers wrongly, and the report says that the check runs while the
  job runs. Today (`main`) it is the warning `sumWraps`; the change is
  [PR #255](https://github.com/AlexanderNenninger/substrait-lean/pull/255).
  Row-count bounds in contracts, which could settle it, are a separate issue.

## Core: numbers and NULLs

### Integers

| Topic | Reference | Status |
|---|---|---|
| Widths | `i8`, `i16`, `i32` and `i64` have their declared widths. `Rel.eval`'s integers are mathematical; a result outside the declared width is an overflow error, not a wrapped value. | Narrow-width arithmetic is checked via `UnFn.wrap`, as a warning. #202 / [#255](https://github.com/AlexanderNenninger/substrait-lean/pull/255) makes it an error. |
| `overflow` omitted or `ERROR` | `+ - *`, negate, `abs`, `sum`: an error when the result doesn't fit the declared width. | `abs(MIN)` and `MIN / -1` are errors ✓. `+ - *`, negate and `sum`: a warning on `main`, which also accepts only `SILENT` (or omitted) in the parser; #202 / [#255](https://github.com/AlexanderNenninger/substrait-lean/pull/255). |
| `overflow: SILENT` / `SATURATE` | Wrap-around / clamp at the declared width, when the plan asks. | ✓ for integer `+ - *` and negation: `UnFn.fit` on the exact result ([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241)). DuckDB runs them through the generated lowering (128-bit arithmetic); Polars, Spark, Snowflake and DataFusion refuse them for now. `sum`, `abs` and decimals accept only `ERROR`. |
| `divide` | Truncates toward zero (`Int.tdiv`). | ✓ |
| Division or `modulus` by zero | An error when `on_division_by_zero` is omitted or `ERROR`; `NULL` only when the plan asks. | ✓ (`Rel.eval` gives NULL there; `verify` reports the error, so that value is never an answer) |
| `modulus` | `division_type` TRUNCATE: the remainder takes the dividend's sign (`Int.tmod`). | ✓ A plan may state `division_type: TRUNCATE`; the parser refuses `FLOOR`, which is not modelled yet. |

Decisions: #185 "Decided: what the reference does when a plan omits an
option"; #202 "Decided (2026-11-01)"; #209 "Decided".

### Floating point

| Topic | Reference | Status |
|---|---|---|
| `fp64` | IEEE 754 binary64, computed with Lean's native `Float`. | ✓ |
| `fp32` | IEEE binary32. | **Not yet.** One double kind: `fp32` is computed as `fp64`. [#208](https://github.com/AlexanderNenninger/substrait-lean/issues/208) |
| Zero | One zero. `-0.0` is `0.0` everywhere, so `1.0 / -0.0 = inf`. | ✓ ([#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), decided on #209) |
| NaN | One NaN, equal to itself, greater than every number, `+∞` included. `GROUP BY`, `DISTINCT` and sorting treat all NaNs alike. | ✓ |
| **No operation creates a NaN** | A NaN from the data passes through. An operation on non-NaN inputs whose IEEE result is NaN raises instead: `0/0`, `inf - inf`, `inf + (-inf)`, `0 * inf`, `inf / inf`, domain errors (`sqrt(-1)`, `sin(±inf)`, a negative base to a fractional power), `fmod(±inf, y)`, and a double `SUM` or `AVG` of `+∞` and `-∞`. With no NaN in the inputs (`~_.v.isnan()` in `requires`), there is none in the outputs. | ✓ ([#257](https://github.com/AlexanderNenninger/substrait-lean/issues/257)): `Issue.domain` (`nanCase` in `Safety.lean`), and the parser accepts only `on_domain_error: ERROR` for `divide` and `power`. Two exceptions: `on_division_by_zero: IEEE` asks for NaN at `0.0 / 0.0` and gets it, a window `SUM`/`AVG` of `+∞` and `-∞` still gives NaN (`verify` does not report it yet), and DataFusion runs the written plan natively, so it gives NaN where the reference raises (as it gives `±∞` for a zero divisor); DuckDB, Polars, Spark and Snowflake raise. (Decided on #185, "no newly created NaNs") |
| Division by zero | An error when `on_division_by_zero` is omitted or `ERROR`. `IEEE`, `LIMIT` and `NULL` when the plan asks. | ✓ (#204) |
| Domain errors | `sqrt`, `log`, `asin`, `acos`, `logb`, `atan2(0, 0)` and shifts outside their domain raise (`on_domain_error`, `on_log_zero` = `ERROR`). | ✓ (#215) |
| `round(x, d)` | Halves away from zero, as DuckDB computes it: with `m = 10^abs(d)`, `round(x · m) / m` for `d ≥ 0` (`x` itself where that is not finite), and `round(x / m) · m` for `d < 0` (0 where that is not finite), so `round(42, -1000)` is 0 rather than NaN. `±∞` and NaN stay. DataFusion's `round(x · 10ᵈ) / 10ᵈ` differs, so DataFusion refuses it until #271. | ✓ (#335) |
| `%` on doubles | Substrait has no such function, so the reference defines its own, `sverify_fmod`: C's `fmod`, exact, with the dividend's sign. A zero divisor is an error (`NULL` if the plan asks), an infinite dividend is an error (#257), an infinite divisor gives the dividend, and a NaN passes through. Lean also reads the `modulus` of doubles that DataFusion writes, as the same function. | ✓ ([#256](https://github.com/AlexanderNenninger/substrait-lean/issues/256)): Lean writes `sverify_fmod`, the Ibis producer and the SQLGlot lift emit it for `%` of doubles, and DataFusion runs it as its own `%` |
| Casts to and from decimals | See [Decimals](#decimals) and [Casts](#casts). | ✓ |

### Decimals

A `DECIMAL(p, s)` is its unscaled integer with the scale `s`. Arithmetic is
exact, and a result of more than `p` digits is an overflow error
(`UnFn.decimal`, `Safety.lean`). The rules, from `Parse.decimalCall`,
`Parse.parseMeasure` and `Aggregate.lean` (#27); the aggregates' are in
[Aggregates of decimals](#of-decimals):

| Operation | Result type | Notes | Status |
|---|---|---|---|
| `a + b`, `a - b` | `DECIMAL(max(p₁−s₁, p₂−s₂) + max(s₁, s₂) + 1, max(s₁, s₂))`, at most 38 digits | Exact; operands are brought to the larger scale. | ✓ |
| `a × b` | `DECIMAL(p₁ + p₂ + 1, s₁ + s₂)`, at most 38 digits | Exact. A scale over 38 is refused. | ✓ |
| negate, `abs` | the argument's type | | ✓ |
| comparisons | — | At the larger scale. | ✓ |
| `/` | — | **Refused** (apart from sverify's own `sverify_decimal_div`, a decimal by an integer, which is how a windowed `AVG` is written). | ✓ |
| declared output type | If the plan declares a precision, it is used. A declared scale that differs from the exact one is refused. | | ✓ |
| mixed with a double | **Refused**; cast one side. | | ✓ |

If the plan declares a precision smaller than the exact result's, a value that
needs more digits raises. Rounding, when a cast drops places, is half away from
zero. Casts are in [Casts](#casts).

DuckDB computes some of these differently (result types, `×` past 18 digits,
`AVG` as a `DOUBLE`); its translation compensates, see
[engine-profiles.md](engine-profiles.md#decimals-27). One reporting problem is
open: `verify` prints a decimal's bound in unscaled units and calls it "an
integer" ([#250](https://github.com/AlexanderNenninger/substrait-lean/issues/250)).
The values are right; the rendering is not.

### NULL

| Topic | Reference | Status |
|---|---|---|
| Logic | Three-valued (Kleene): `AND`, `OR`, `NOT`, comparisons. | ✓ |
| `WHERE`, `ON`, `HAVING`-style conditions | Keep a row only when the condition `IS TRUE` (`Value.isTrue`). | ✓ |
| Functions | Propagate NULL, unless Substrait says otherwise (`COALESCE`, `IS NULL`, `CASE`, `any_match`…). | ✓ |
| Equality for grouping | `GROUP BY`, `DISTINCT` and list equality treat NULLs as equal (`[1, NULL] = [1, NULL]` is TRUE). | ✓ |

## Strings

| Topic | Reference | Status |
|---|---|---|
| Characters | Unicode code points (Lean `Char`); `length`, `substring`, `strpos` count them. Strings compare by code point, which is UTF-8 byte order. | ✓ |
| `substring` with a negative start | `negative_start` omitted means `WRAP_FROM_END`: `substring('hello', -2, 2) = 'lo'`. A plan that sets `LEFT_OF_BEGINNING` gets that. | ✓ (#209, R13) |
| Matching | Case-sensitive only (`case_sensitivity` = `CASE_SENSITIVE`); `LIKE` has `%`, `_` and a backslash escape. | ✓ |
| **Black boxes** | `upper`, `lower`, `ilike`, regular expressions and the digests `md5` and `sha256` are opaque to the proofs: no proof depends on what they compute, only on their types, that NULL in gives NULL out, and that equal inputs give equal outputs. Their meaning is Rust's (`str::to_uppercase`, the `regex` crate). Lean's evaluator maps ASCII case only, and evaluates regular expressions with RE2's meaning (`SubstraitLean/Regex.lean`) where it agrees with Rust's, which is everywhere but `\d`, `\w`, `\s` and `\b` on non-ASCII text (and `\s` on `\v`); there `substrait-check` refuses to print rows rather than print wrong ones. | ✓ (#70, #50) |
| `regexp_extract`, `regexp_replace` | A constant pattern that `Text.simpleRegex` accepts, or the plan is refused. `regexp_extract(s, p, g)` is group `g` of the leftmost-first match, `''` where nothing matches, the group took no part, or `p` has fewer groups. `regexp_replace` replaces the first match, or every match with the flag `'g'` (an empty match right after the previous one is skipped); in the replacement, `\0` … `\9` are groups and `\\` a backslash, and other escapes are refused. DuckDB only so far (#271). | ✓ (#50) |
| `md5`, `sha256` | Lowercase hex of the UTF-8 bytes' digest; never NULL for a string. DuckDB's `hash()` is refused: it is the engine's own and changes between versions. | ✓ (#50) |
| Not modelled | `translate` (it works on grapheme clusters). | refused |

## Temporal

| Topic | Reference | Status |
|---|---|---|
| `date` | Days since 1970-01-01, proleptic Gregorian. | ✓ |
| `timestamp` | Microseconds since 1970-01-01 00:00, **no time zone**. Time-zone-aware timestamps (`timestampTz`) are a separate kind the model does not compute with. | ✓ |
| Intervals | Day-to-second intervals are microseconds; year-to-month intervals are months. Adding months keeps the day of month. | ✓ |
| Range | **Dates: the SQL standard's, 0001-01-01 to 9999-12-31** (`Time.dayMin`, `Time.dayMax`; decided on #251). Every engine represents them. Date arithmetic (adding days or months) whose operand or result leaves them is an error, reported by `verify` and raised by the engines as "outside the reference's dates". With constant operands (TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`) this is decided when the plan is written, and the SQL has no guard. **Not yet the reference's own:** `date_part` is NULL outside chrono's years −262143 to 262142, and calendar truncations raise outside DataFusion's ±2⁶³ nanoseconds. | ✓ date arithmetic ([#251](https://github.com/AlexanderNenninger/substrait-lean/issues/251)); `date_part` and truncation ranges open |

## Nested: lists and structs

| Topic | Reference | Status |
|---|---|---|
| Representation | A struct is the list of its fields, in order. Equality is structural. | ✓ |
| Order of lists | Lexicographic, element by element; a proper prefix sorts first. `lt`, `gt`, `lte` and `gte` are three-valued: a NULL element that decides the result makes it NULL (`[1, NULL] < [2]` is TRUE, `[1, NULL] < [1, 3]` is NULL). In `ORDER BY` and `MIN`/`MAX`, NULL elements sort after every other value. | ✓ (#207) |
| Lambdas | `any_match`, `all_match`, `transform` and `filter` take closed lambdas only. `any_match` is TRUE if some element matches, else NULL if some result is NULL, else FALSE (`[]` gives FALSE). | ✓ (#94) |
| `UNNEST` | One row per element, none for an empty list or NULL (sverify's own extension). | ✓ |

Design notes: [nested-values.md](nested-values.md).

## Casts

| Cast | Reference | Status |
|---|---|---|
| Out of range (`BIGINT` from a wider value, `i8`…`i32` from a larger integer, a double that is NaN, infinite or out of range) | An error: `FAILURE_BEHAVIOR_THROW_EXCEPTION`. | ✓ (`badCast`) |
| `RETURN_NULL` (`TRY_CAST`) | NULL instead of an error. | **Not honoured**: `Parse.lean` ignores `failureBehavior` and treats every cast as raising. That is conservative: `verify` reports an error that can't happen, never misses one. [#58](https://github.com/AlexanderNenninger/substrait-lean/issues/58) |
| Double or decimal to integer | Truncates toward zero. | ✓ (decided on #209) |
| `TRY_CAST` (`failureBehavior: RETURN_NULL`) | NULL where the cast would raise, and then no error: a double to an integer (NaN, `±∞`, outside 64 bits) and an integer to a narrower one. `TRY_CAST` to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. | ✓ on DuckDB (#58); other engines refuse it until #271 |
| Decimal to a smaller scale | Rounds half away from zero. | ✓ |
| Integer to decimal | Exact; an error if it doesn't fit the precision. | ✓ |
| Double to decimal | `round(x · 10ˢ)` computed in doubles, half away from zero (`-2.675` gives `-2.68`). NaN and `±∞` raise. | ✓ (#27) |
| Decimal to double | The nearest double. | ✓ |
| `date` ↔ `timestamp` | A date is days since 1970-01-01, a timestamp microseconds. `date` to `timestamp` is midnight; `timestamp` to `date` rounds down, before 1970 too. Comparing a date with a timestamp without a cast is refused. | ✓ (#206) |

## Aggregates

### Of integers

| Topic | Reference | Status |
|---|---|---|
| `avg` of integers | Follows the plan's declared output type: `fp64` is the mean as a double, `i64` is Substrait's integer `avg`, truncated toward zero (`AggFn.iavg`). The integer one lies between the smallest and largest value ([#237](https://github.com/AlexanderNenninger/substrait-lean/issues/237)). Any other output type is refused. | ✓ (#209) |
| `sum` of integers | Returns `i64`; exact, checked at the end ([Errors](#errors)). | ✓ unbounded in `Rel.eval`; check: #255 |

### Of doubles

| Topic | Reference | Status |
|---|---|---|
| `SUM` / `AVG` | Added in list order with native floats. Rounding can take `AVG` past the values (the mean of three `0.1` is `0.10000000000000002`). Contracts get exact signs (a `SUM` or `AVG` of values `≥ 0` is `≥ 0`) and, for inputs with a row cap (`sv.max_rows(n)`, `n ≤ 2³²`) and values within `2⁴⁰⁰`, the interval of the exact result widened by the proved error bound (`floatSum_mem`, `floatAvg_mem` in `Aggregate.lean`, proved in [`float-bounds/`](float-bounds.md)). `sv.approx` states a postcondition up to that rounding. A sharded or parallel sum may differ in the last bits, so `--shard` refuses it unless `float_order="any"`; engines that don't fix the order are refused unless `tie_free` justifies it. | ✓ order; error bounds ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)) |
| `VARIANCE` / `STDDEV` | Of a sample (`n - 1`, the default) or a population (`n`, `distribution: POPULATION`), of doubles; integers are converted first. **Each engine's own algorithm** for now (decided on #54), so results may differ in the last bits: the model claims a double ≥ 0 or NULL, exactly NULL for no values and for a sample of one value. A NaN passes through; an infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, approximate ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); refused over windows; whatever the algorithm (two-pass, textbook, or DuckDB's Welford and Chan), the result is within a proved bound, `64 · n² · u · B²` on the co-moment ([`float-bounds.md`](float-bounds.md)); the checker keeps "a double ≥ 0 or NULL" |
| `COVAR_SAMP` / `COVAR_POP` / `CORR` | Of pairs of doubles (integers converted), rows with a NULL in either skipped (`BinFn.pair`). Each engine's own algorithm, as for `VARIANCE`: the model claims a double or NULL. NULL for no pairs, for a sample covariance of one pair, and for `CORR` of fewer than two pairs or of a side whose values are all equal, as the SQL standard says (DuckDB's own `CORR` gives NaN there). An infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, on DuckDB ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); other engines refuse it until #271; refused over windows |
| `MIN` / `MAX` of doubles | By the codes' order, `-∞ < … < +∞ < NaN`, as DuckDB orders doubles. | ✓ on DuckDB ([#371](https://github.com/AlexanderNenninger/substrait-lean/issues/371)); Polars and DataFusion (whose grouped min/max of doubles is not IEEE) refuse them until #271 |

### Of decimals

The rules for decimals are in [Decimals](#decimals).

| Operation | Result type | Notes | Status |
|---|---|---|---|
| `MIN`, `MAX` | the argument's type | | ✓ |
| `SUM` | `DECIMAL(min(38, p + 10), s)` | Exact. | ✓ |
| `AVG` | `DECIMAL(min(38, p + 4), s + 4)` | Rounded half away from zero. A scale over 34 is refused. | ✓ |
| `AVG` with an `fp64` result (DuckDB's type) | `fp64` | The exact sum converted to a double, divided by the count as a double (`CAST(n AS DOUBLE)`); NULL without values. DuckDB's native `AVG` divides once and may differ in the last bit. Over a window too. | ✓ (M2) |

### NULLs and order

| Topic | Reference | Status |
|---|---|---|
| Aggregates | NULLs are skipped. `COUNT` of no rows is 0; every other aggregate of no rows is NULL. Without grouping keys, an empty input still gives one row; with keys, none. | ✓ |
| `FIRST` / `LAST` (#55) | The first or last non-NULL value in the aggregate's own `ORDER BY`, NULL without one. Rows tied in the order go in list order, so a report is `deterministic` only when the group's and the order's columns contain a key. Without an `ORDER BY` every row ties (any row's value, as in Ibis's `distinct(on=)`), and an engine may take each measure's value from a different row. | ✓ on DuckDB; other engines refuse it until #271 |
| `STRING_AGG` (#55) | The non-NULL strings in the aggregate's own `ORDER BY`, joined by a constant separator; NULL without one. Refused without an `ORDER BY` (the order would be the engine's), and determined as `FIRST` is: ties go in list order, so a report is `deterministic` only when the group's and the order's columns contain a key. | ✓ on DuckDB; other engines refuse it until #271 |

## Windows

| Topic | Reference | Status |
|---|---|---|
| `NTILE(k)` | The SQL standard's buckets: of `n` rows, the first `n % k` buckets hold `⌊n / k⌋ + 1` rows and the rest `⌊n / k⌋`; with fewer rows than buckets, a bucket for each row (`ntileOf`). Between 1 and the row's number, proved. | ✓ on DuckDB, Spark, Snowflake and Polars; **refused** on DataFusion, which spreads the larger buckets out (`upstream/LEDGER.md` DF-11) |

## Relations

| Topic | Reference | Status |
|---|---|---|
| Bags | A relation is a list of rows read as a bag: two relations are equal when they are permutations of each other (`Rel.Equiv`). | ✓ |
| Operators | `read`, `values`, `filter`, `project`, `emit`, `cross`, inner and left `join`, `semi` and `anti`, `fetch`, `orderBy`, `distinct`, `aggregate` (one grouping set), `window`, `unnest`, `UNION ALL`. | ✓ |
| Set operations | `UNION ALL` is bag union and `UNION DISTINCT` is `distinct` of it. The SQL lift writes `INTERSECT` and `EXCEPT` as the left rows with (without) an equal right row, NULLs equal, by a semi (anti) join, and `DISTINCT`; with `ALL` it numbers each side's equal rows (`ROW_NUMBER() OVER (PARTITION BY` every column`)`) and joins on the number too, so `m` and `n` copies leave `min(m, n)` and `max(m − n, 0)`. The window has no order, but the rows it ties are equal, so `INTERSECT ALL` and `EXCEPT ALL` are deterministic without keys (`Rel.window_allColumns`). Substrait's `SET_OP_INTERSECTION_*`/`SET_OP_MINUS_*` are not read yet. | ✓ (#344) |
| Ties | `Rel.eval` sorts stably and takes `fetch` rows in list order. Engines promise neither, so theorems about `fetch`, ties and windows hold for one choice. A report's `deterministic` says whether the plan's sort keys and window orders are total on the input's keys; the Spark and Snowflake translations, which have no row order, refuse sorts, `LIMIT` and windows that are not, unless `tie_free=True` is justified by it. | ✓ |
| Sort keys | Every key states where NULLs go. The parser reads only `SORT_DIRECTION_{ASC,DESC}_NULLS_{FIRST,LAST}` and **refuses** any other direction (unspecified, clustered), so there is no default to choose. The Ibis producer and the SQL writer always write all four parts. | ✓ (`parseSortKey`; the model's `SortKey` has a default of NULLs last only for hand-built values) |

## Trusted assumptions

What a proof does not cover. A theorem about `Rel.eval` holds for the model;
these links connect it to a real run.

| Assumption | Where | Status |
|---|---|---|
| **The size hypothesis** (`Rel.Small`): every string has fewer than 2⁶² characters, and every relation a window reads has fewer than 2⁶² rows. No machine's memory holds more. | Used by the range analysis (`CHARACTER_LENGTH`, `strpos`, `ROW_NUMBER`, …). | Not on `main`; [PR #254](https://github.com/AlexanderNenninger/substrait-lean/pull/254) states it, and the theorems that need it take `Rel.Small` |
| **The frontends** produce the plan the user meant: the Ibis producer, and SQLGlot with sverify's own Substrait producer for SQL ([#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231), [PR #252](https://github.com/AlexanderNenninger/substrait-lean/pull/252)). The SQLGlot lift writes each function's options explicitly from the source dialect. | `python/src/sverify/ibis_substrait/`, `python/src/sverify/sql_lift/` | On `main`: the Ibis producer, and the SQLGlot lift for DuckDB's SQL (#252, #264). DataFusion's SQL producer is no longer a frontend (#211) |
| **The engines match their profiles.** Tier 1 replays the engine's own tests and fuzzing ([#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211)); Tiers 2 and 3 are differentially tested only. | `characterization/` | Tested, not proved |
| **The printers and `Parse.lean`.** The JSON parser and writer, the SQL printers and the Polars translator read and write plans faithfully, a shimmed plan's `isNum` as `IS NOT NULL` included. | `SubstraitLean/Parse.lean`, `Write.lean`, `Pretty.lean`, `python/src/sverify/sql/` | Golden and round-trip tests |
| **Native `Float`.** Lean's `Float` is an opaque `extern` to C `double`; the model trusts that it is IEEE binary64. An integer converts to a double through `FloatCode.finite`, which clamps a result of `±∞` to the largest finite double; IEEE rounds an integer to `±∞` only from 2¹⁰²⁴ on, so for 64-bit integers the clamp never applies; a decimal (`FloatCode.ofDecimal`, at most 38 digits) converts the same way (#257). | `SubstraitLean/Float.lean` | Stated. The error bounds of `SUM` and `AVG` are three axioms in `Aggregate.lean` (`floatSum_mem`, `floatAvg_mem`, `floatSum_sign`), proved in [`float-bounds/`](float-bounds.md) from `NativeLink`, the stated link of `Float` to IEEE rounding ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)) |

## Where things are decided

| What | Where |
|---|---|
| Principles and defaults | [#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185): "Principles for the reference model", "Decided: what the reference does when a plan omits an option", "Decided (2026-11-02): no newly created NaNs" |
| Modulus, casts, `substring`, `-0.0`, lists, `avg` | [#209](https://github.com/AlexanderNenninger/substrait-lean/issues/209), "Decided" |
| Overflow and `SUM` | [#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202), "Decided (2026-11-01)" |
| Engine tiers | [#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211) |
| DuckDB's findings, judged against this page | [`characterization/duckdb/FACTS.md`](../characterization/duckdb/FACTS.md) |
