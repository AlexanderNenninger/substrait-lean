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

The reference follows Substrait. Where it overrides Substrait, it says so
([Overrides](#overrides)).

The reference is a relation: for each input it allows a set of results
(`Rel.Allowed`, `SubstraitLean/Allowed.lean`). An engine runs a plan
**correctly** when, on every input, it returns an allowed result or raises an
error. `Rel.eval` (`SubstraitLean/Rel.lean`) computes one allowed result, a
witness (`Rel.eval_allowed`), and `verify` proves its theorems through it.

The set holds more than one result only where the reference leaves a choice
to the engine:

* the order of rows, except what an `ORDER BY` promises, and how ties in an
  `ORDER BY` or a window's order are broken;
* the row `FIRST`, `LAST`, `collect` and `STRING_AGG` take first where their
  order ties (any row without an order, as in Ibis's `distinct(on=)`);
* the order and grouping in which a double `SUM` or `AVG` adds its values
  (`FloatSums`), each result within the error bound of
  [#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85);
* a statistical aggregate's value (`VARIANCE`, `STDDEV`, `COVAR_*`, `CORR`),
  within its generic properties (`StatProps`, with #85).

A plan without these choices (`Rel.detPlan`) allows only `Rel.eval`'s rows, in
any order (`Rel.allowed_perm_eval`), so a theorem about `Rel.eval`'s rows holds
of every allowed result. `Report.deterministic` is false where rows may tie in
the order of a window or of `FIRST`, `LAST` or `STRING_AGG`
(`Rel.windowsTotal`); it does not yet flag the other choices.

The reference is not a model of any engine, DuckDB included. Each engine is
characterized as a **diff** against it (`characterization/<engine>/`): which
behaviours it has natively, which need a shim (a guard, a cast, a `CASE`), and
which the translation refuses. The shims are proved against the reference in
Lean (`SubstraitLean/Profile.lean`: `Profile.reference`,
`Expr.evalP_reference`; `SubstraitLean/Lowering.lean`: `Lowering.lower_correct`,
`Rel.duckdb_shim_sound`), and so return allowed results
(`Rel.duckdb_shim_allowed`, `Rel.guardFree_allowed`).
That each engine matches its profile is tested, not proved. How profiles and
shims work is in [engine-profiles.md](engine-profiles.md).

For now the reference is demonstrated on DuckDB only. New functions run on
DuckDB, and the other engines refuse them until their lowerings land
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).

## Principles

Decided on #185 ("Principles for the reference model"):

| # | Principle | What it means in practice |
|---|---|---|
| 1 | **Follows Substrait, options included.** | A function means what its extension YAML says. An option set in the plan is part of its meaning. Where the reference overrides Substrait, it says so, with the reason ([Overrides](#overrides)). |
| 2 | **The least surprising choice where Substrait is silent**, with its reason. | An option the plan omits, or behaviour the spec leaves open, gets one choice, written down below with the reason. |
| 3 | **Every engine can follow it with reasonable effort.** | Types keep their declared widths (`i8`…`i64`); there are no unbounded integers. Every choice has a reasonable shim or translation on DuckDB, Polars, DataFusion, Spark and Snowflake, one that can be built and run. |
| 4 | **Keeps optimizations provable.** | Filter pushdown, reordering, sharding and incremental maintenance stay provable. A rewrite refines the plan (`Rel.Refines`): it may narrow the set of allowed results, never widen it. This is why an error means "may raise" ([Errors](#errors)). |

## Overrides

Where the reference departs from Substrait, and why:

| Override | What the reference does | Why |
|---|---|---|
| One zero | `-0.0` is `0.0` everywhere, so `1.0 / -0.0 = inf`, and `GROUP BY`, `DISTINCT` and joins see one zero. | DuckDB, Spark and Snowflake have one zero ([#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89)); IEEE's two zeros, which DataFusion keeps apart, surprise `-0.0 >= 0`. |
| One NaN | One NaN, equal to itself and greater than every number, `+∞` included. | DuckDB, Spark and Snowflake treat NaN this way (#89); IEEE's NaN, unequal to itself, would split `GROUP BY` and `DISTINCT` and drop rows from joins. |
| The size hypothesis | Every string has fewer than 2³² characters (`Text.sizeCap`), and every relation a window reads fewer than 2⁶² rows (`Rel.Small`). | Substrait's types are unbounded; DuckDB's strings hold fewer than 2³² bytes (#336), no machine's memory holds 2⁶² rows, and the range analysis needs a bound for `CHARACTER_LENGTH`, `strpos` and `ROW_NUMBER`. |

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
  than the original, and allow fewer results (`Rel.Refines`). It never gives a
  result the original doesn't allow and never raises where the original
  didn't. A rewrite to a plan without choices whose rows are the original's
  refines it (`Rel.refines_of_perm`). ✓ (#185)
* **An error that can't be ruled out makes the report unproved.**
  `Report.proved` is false until a precondition excludes it. ✓ for division
  by zero, casts out of range, domain errors, decimal precision and the
  other error issues, and for integer `+ - *` and negation overflow at the
  declared width ([#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202)).
  Inferred bounds (#244) discharge most overflows.
* **`SUM` overflow is an inferred assumption, checked on the data.**
  A group's integer sum may leave 64 bits, and a decimal sum its precision
  (`DECIMAL(min(38, p + 10), s)`, [#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316));
  the reference raises there, and so does DuckDB past 38 digits.
  Where the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an
  aggregate without groups: `Rel.maxRows`) and the argument's range bounds
  each value (`Measure.sumFits`), it is ruled out. Elsewhere `verify` assumes
  each sum fits, as it assumes inferred bounds (#244), and lists it in
  `Report.assumed`; the written SQL checks it on the data while the job runs
  and raises if a sum does not fit. The proof holds under that assumption
  (`Rel.noIssue_of_sumsFit`). With `infer=False` it is an error that makes the
  report unproved. A row cap on the inputs (`sv.max_rows(n)`,
  [#219](https://github.com/AlexanderNenninger/substrait-lean/issues/219))
  discharges it statically: with values in `[-m, m]` and at most `n` rows,
  `n · m < 2⁶³` proves the sum fits (`Rel.issuesCapped_sound` in
  [Rows.lean](../SubstraitLean/Rows.lean)).

## Core: numbers and NULLs

### Integers

| Topic | Reference | Status |
|---|---|---|
| Widths | `i8`, `i16`, `i32` and `i64` have their declared widths. `Rel.eval`'s integers are mathematical; a result outside the declared width is an overflow error, not a wrapped value. | ✓ An overflow at the declared width is an error ([#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202)); a call's declared output type gives its width (#419). |
| `overflow` omitted or `ERROR` | `+ - *`, negate, `abs`, `sum`: an error when the result doesn't fit the declared width. | ✓ (#202). An integer `sum` that may overflow is an assumption checked on the data (above). |
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
| `fp32` | IEEE binary32. | **Not yet.** `fp32` arithmetic is refused (fact [duckdb-R12](../characterization/duckdb/facts/duckdb-R12.json), #208); [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417) models it. |
| Zero | One zero. `-0.0` is `0.0` everywhere, so `1.0 / -0.0 = inf`. | ✓ ([#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), decided on #209) |
| NaN | One NaN, equal to itself, greater than every number, `+∞` included. `GROUP BY`, `DISTINCT` and sorting treat all NaNs alike. | ✓ |
| **No operation creates a NaN** | A NaN from the data passes through. An operation on non-NaN inputs whose IEEE result is NaN raises instead: `0/0`, `inf - inf`, `inf + (-inf)`, `0 * inf`, `inf / inf`, domain errors (`sqrt(-1)`, `sin(±inf)`, a negative base to a fractional power), `fmod(±inf, y)`, and a double `SUM` or `AVG` of `+∞` and `-∞`. With no NaN in the inputs (`~_.v.isnan()` in `requires`), there is none in the outputs. | ✓ ([#257](https://github.com/AlexanderNenninger/substrait-lean/issues/257)): `Issue.domain` (`nanCase` in `Safety.lean`), and the parser accepts only `on_domain_error: ERROR` for `divide` and `power`. A window `SUM`/`AVG` whose frame may hold `+∞` and `-∞` is a domain error too, as the grouped one is. Two exceptions: `on_division_by_zero: IEEE` asks for NaN at `0.0 / 0.0` and gets it, and DataFusion runs the written plan natively, so it gives NaN where the reference raises (as it gives `±∞` for a zero divisor); DuckDB, Polars, Spark and Snowflake raise. (Decided on #185, "no newly created NaNs") |
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
| `substring` range | An offset outside `[-2³², 2³²)` or a length of `2³²` or more is an error, as in DuckDB ("Substring offset outside of supported range"); NULL arguments give NULL. `verify` reports it as a domain error unless the offset's bounds rule it out, for example `_.start >= -2**32` and `_.start < 2**32` in `requires`. | ✓ ([#336](https://github.com/AlexanderNenninger/substrait-lean/issues/336)): `Text.substrInRange`, `Issue.domain`; DuckDB raises itself, and the written plan guards the offset its wrap-around arithmetic shifts |
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
| Double or decimal to integer | Truncates toward zero. Monotone, so a double's bounds bound the integer: a computed double within its error bound `[x − ε, x + ε]` ([float-bounds.md](float-bounds.md#in-contracts)) casts to `[trunc(x − ε), trunc(x + ε)]`. | ✓ (decided on #209) |
| `TRY_CAST` (`failureBehavior: RETURN_NULL`) | NULL where the cast would raise, and then no error: a double to an integer (NaN, `±∞`, outside 64 bits) and an integer to a narrower one. `TRY_CAST` to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. | ✓ on DuckDB (#58); other engines refuse it until #271 |
| Decimal to a smaller scale | Rounds half away from zero. | ✓ |
| Integer to decimal | Exact; an error if it doesn't fit the precision. | ✓ |
| Double to decimal | `round(x · 10ˢ)` computed in doubles, half away from zero (`-2.675` gives `-2.68`). NaN, `±∞` and a product that overflows raise. Monotone, so a double's bounds bound the decimal, and `verify` reports neither the failed cast nor the precision overflow where the casts of the bounds fit (`FloatCode.toDecimal?_between`). | ✓ (#27, [#223](https://github.com/AlexanderNenninger/substrait-lean/issues/223)) |
| Decimal to double | The nearest double, halves to even: within `2⁻⁵³` of the decimal, relatively (`FloatCode.ofDecimal_rel`), and monotone. | ✓ |
| Integer to double | The nearest double, halves to even: exact up to `2⁵³` in magnitude (`FloatCode.ofInt_exact`), within `2⁻⁵³` relatively beyond (`FloatCode.ofInt_rel`), and monotone (`ofInt_mono`). An integer up to `2⁵³` survives the round trip to a double and back (`FloatCode.toInt?_ofInt`). | ✓ |
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
| `SUM` / `AVG` | Added in list order with native floats. Rounding can take `AVG` past the values (the mean of three `0.1` is `0.10000000000000002`). Contracts get exact signs (a `SUM` or `AVG` of values `≥ 0` is `≥ 0`) and, for inputs with a row cap (`sv.max_rows(n)`, `n ≤ 2³²`) and values within `2⁴⁰⁰`, the interval of the exact result widened by the proved error bound (`floatSum_mem`, `floatAvg_mem` in `Aggregate.lean`, proved in [`float-bounds/`](float-bounds.md)). `sv.approx` states a postcondition up to that rounding. A sharded or parallel sum may differ in the last bits, so `--shard` refuses it unless `float_order="any"`, which reports a proved bound on the difference (`floatSplit_sum`); engines that don't fix the order are refused unless `tie_free` justifies it. | ✓ order; error bounds ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)) |
| `VARIANCE` / `STDDEV` | Of a sample (`n - 1`, the default) or a population (`n`, `distribution: POPULATION`), of doubles; integers are converted first. Each engine's own algorithm, within the generic properties of [Statistical aggregates](#statistical-aggregates) (#54, #85): the model claims a double ≥ 0 or NULL, exactly NULL for no values and for a sample of one value. A NaN passes through; an infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, approximate ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); refused over windows; for two-pass and for DuckDB's Welford and Chan, the result is within a proved bound that scales with the spread of the values ([`float-bounds.md`](float-bounds.md)); the checker keeps "a double ≥ 0 or NULL" |
| `COVAR_SAMP` / `COVAR_POP` / `CORR` | Of pairs of doubles (integers converted), rows with a NULL in either skipped (`BinFn.pair`). Each engine's own algorithm, within the generic properties of [Statistical aggregates](#statistical-aggregates): the model claims a double or NULL. NULL for no pairs, for a sample covariance of one pair, and for `CORR` of fewer than two pairs or of a side whose values are all equal, as the SQL standard says (DuckDB's own `CORR` gives NaN there). An infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, on DuckDB ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); other engines refuse it until #271; refused over windows |
| `MIN` / `MAX` of doubles | By the codes' order, `-∞ < … < +∞ < NaN`, as DuckDB orders doubles. | ✓ on DuckDB ([#371](https://github.com/AlexanderNenninger/substrait-lean/issues/371)); Polars and DataFusion (whose grouped min/max of doubles is not IEEE) refuse them until #271 |

### Statistical aggregates

Engines compute `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` with different
algorithms, none documented: DuckDB 2.0 and Spark 4.3 use Welford's update
with Chan's merge, Polars 2.1 a two-pass per block of 128 values when
ungrouped and Welford when grouped (`characterization/*/facts/`, ids
`duckdb-var-stddev`, `duckdb-covar`, `duckdb-corr`, `polars-var-std`,
`polars-cov`, `polars-corr`, `spark-var-stddev`, `spark-covar`, `spark-corr`).
The reference picks none. It allows any result with the generic properties
that every reasonable algorithm keeps (`StatProps` in
`SubstraitLean/StatProps.lean`, the set `AggFn.Allowed` uses). For `n ≤ 2³²`
finite values at most `2³⁹⁸`, with `u = 2⁻⁵³`, `tiny = 2⁻¹⁰²²`, the exact
co-moments `C = Σxy − Σx · Σy / n`, `S_xx` and `S_yy`, and
`Q' = Σ (|xᵢ| + tiny)²` of each side:

- `NULL` for no values and for a sample of one value; for `CORR`, for fewer
  than two pairs and for a side whose values are all equal.
- A variance or deviation is `≥ 0`.
- `VAR_*` is within `τ = (160 n u √(Q' S) + 3970 n² u² Q' + 800 n² u · tiny) / d`
  of `S / d`, `d = n − 1` for a sample, `n` for a population (`varTol`).
- `COVAR_*` is within
  `(71 n u (√(Q'_x S_yy) + √(Q'_y S_xx)) + 15 n u √(S_xx S_yy) + 3970 n² u² √(Q'_x Q'_y) + 800 n² u · tiny) / d`
  of `C / d` (`covTol`).
- `STDDEV_*` is within `(1 ± u)` of `√(V ± τ)`.
- `|CORR| ≤ 1 + 3E/L + 8u`, `E = 447 n u R + 11883 n² u² (Q'_x + Q'_y) + 2379 n² u · tiny`
  (`corrErr`), where `R` is at least `√(Q' S)` of each side, `√(Q'_x S_yy)`,
  `√(Q'_y S_xx)` and `√(S_xx S_yy)`, when the co-moments of both sides are at
  least `L ≥ 8E`. Without such a lower bound `CORR` can be any double, and no
  engine clamps it to `[−1, 1]`.

The bounds scale with the spread of the values: for values near `10⁶` that
vary by about `1`, the variance of `10⁶` of them is within about `2 · 10⁻²`.
`StatProps` states each square root by a rational witness above it, so the
core needs no square roots. The bounds are proved for the two-pass algorithm
(the reference's own) and for DuckDB's Welford update with Chan's merge in any
tree ([`float-bounds.md`](float-bounds.md)), and a property test checks
DuckDB's results against them (`tests/test_float_bounds.py`). The textbook
formula `Σx² − (Σx)²/n` cancels and is outside them. Outside the finite range
the reference's own value is the one allowed. An engine profile may name a
stricter algorithm (`Profile.statAlgo`, `Profile.sumAlgo`, `AggAlgo`); without
one, the generic properties hold. No profile names one yet. Engines differ
from the reference where it raises: DuckDB and Polars give NaN for an
infinite value and for `CORR` with a zero variance, Spark NULL for the latter.

### Of decimals

The rules for decimals are in [Decimals](#decimals).

| Operation | Result type | Notes | Status |
|---|---|---|---|
| `MIN`, `MAX` | the argument's type | | ✓ |
| `SUM` | `DECIMAL(min(38, p + 10), s)` | Exact; raises past the precision, an inferred assumption like integer `SUM` overflow (#316). | ✓ |
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
| `NTILE(k)` | The SQL standard's buckets: of `n` rows, the first `n % k` buckets hold `⌊n / k⌋ + 1` rows and the rest `⌊n / k⌋`; with fewer rows than buckets, a bucket for each row (`ntileOf`). Between 1 and the row's number, proved. | ✓ on DuckDB, Spark, Snowflake and Polars; **refused** on DataFusion, which spreads the larger buckets out ([DF-11](../upstream/bugs/DF-11.json)) |

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
| **The size hypothesis**: every string has fewer than 2³² characters (`Text.sizeCap`, decided on [#336](https://github.com/AlexanderNenninger/substrait-lean/issues/336): DuckDB's strings hold fewer than 2³² bytes), and every relation a window reads has fewer than 2⁶² rows (`Rel.Small`, `Text.rowCap`). | Used by the range analysis (`CHARACTER_LENGTH`, `strpos`, `levenshtein`, `ROW_NUMBER`, …). | ✓ The theorems that need it take `Rel.Small`; an override of Substrait ([Overrides](#overrides)) |
| **The frontends** produce the plan the user meant: the Ibis producer, and SQLGlot with sverify's own Substrait producer for SQL ([#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231), [PR #252](https://github.com/AlexanderNenninger/substrait-lean/pull/252)). The SQLGlot lift writes each function's options explicitly from the source dialect. | `python/src/sverify/ibis_substrait/`, `python/src/sverify/sql_lift/` | On `main`: the Ibis producer, and the SQLGlot lift for DuckDB's SQL (#252, #264). DataFusion's SQL producer is no longer a frontend (#211) |
| **The engines match their profiles.** Tier 1 replays the engine's own tests and fuzzing ([#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211)); Tiers 2 and 3 are differentially tested only. | `characterization/` | Tested, not proved |
| **The printers and `Parse.lean`.** The JSON parser and writer, the SQL printers and the Polars translator read and write plans faithfully, a shimmed plan's `isNum` as `IS NOT NULL` included. | `SubstraitLean/Parse.lean`, `Write.lean`, `Pretty.lean`, `python/src/sverify/sql/` | Golden and round-trip tests |
| **Native `Float`.** Lean's `Float` is an opaque `extern` to C `double`; the model trusts that it is IEEE binary64 for arithmetic. The conversions between integers, decimals and doubles are computed exactly instead (`SubstraitLean/Conversions.lean`), behind `opaque` constants with their proved properties, and `#guard`s compare them with the native ones. An integer or decimal that IEEE would round to `±∞` (from 2¹⁰²⁴ on, never for 64-bit integers or 38-digit decimals) becomes the largest finite double (#257). | `SubstraitLean/Float.lean`, `SubstraitLean/Conversions.lean` | Stated. The error bounds of `SUM` and `AVG` are three axioms in `Aggregate.lean` (`floatSum_mem`, `floatAvg_mem`, `floatSum_sign`), proved in [`float-bounds/`](float-bounds.md) from `NativeLink`, the stated link of `Float` to IEEE rounding ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)) |

## Where things are decided

| What | Where |
|---|---|
| Principles and defaults | [#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185): "Principles for the reference model", "Decided: what the reference does when a plan omits an option", "Decided (2026-11-02): no newly created NaNs" |
| Modulus, casts, `substring`, `-0.0`, lists, `avg` | [#209](https://github.com/AlexanderNenninger/substrait-lean/issues/209), "Decided" |
| Overflow and `SUM` | [#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202), "Decided (2026-11-01)" |
| Engine tiers | [#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211) |
| DuckDB's findings, judged against this page | [`characterization/duckdb/facts/`](../characterization/duckdb/facts/) |
