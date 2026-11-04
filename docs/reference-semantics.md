# Reference semantics

What sverify's plans mean. `Rel.eval` (`SubstraitLean/Rel.lean`) is the
**reference semantics**, the strict profile plans are verified under:
`verify` proves things about it, and every engine's row of the realizability
table is its difference from it. The loose core it refines, the engine
profiles and what a proof under the reference guarantees are in
[core-semantics.md](core-semantics.md#terminology). This page collects the choices
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
**correctly** when, on every input, it returns an allowed result, or raises
only where the reference may raise; resource errors, such as running out of
memory, are excluded ([D16](core-semantics.md#d16-engine-correctness)). Lean
proves partial correctness today, an allowed result or an error
(`Rel.duckdb_shim_sound`); for a plan verified to never raise the two agree
(`Rel.duckdb_sound`). `Rel.eval` (`SubstraitLean/Rel.lean`) computes one allowed result, a
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

The reference is not a model of any engine, DuckDB included. It is stricter
than every engine in most options: where engines disagree on an edge case it
raises, so a verified plan never reaches that case. Each engine is
characterized as a **diff** against it (`characterization/<engine>/`): which
behaviours it has natively, which need a shim (a guard, a cast, a `CASE`), and
which the translation refuses. The shims are proved against the reference in
Lean, and that each engine matches its profile is tested; both are in
[engine-profiles.md](engine-profiles.md#profiles-and-shims-in-lean-185-first-slice).

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
| The size hypothesis | Every string has fewer than 2³² characters (`Text.sizeCap`), every relation a window reads fewer than 2⁶² rows, and every relation an aggregate reads fewer than 2⁶³ rows (`Rel.Small`). | Substrait's types are unbounded; DuckDB's strings hold fewer than 2³² bytes (#336), no machine's memory holds 2⁶² rows, `COUNT(*)` is a 64-bit integer in the reference and in every engine, and the range analysis needs a bound for `CHARACTER_LENGTH`, `strpos`, `ROW_NUMBER` and `SUM` ([#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)). |

Engine quirks belong in profiles, never in the reference. While sverify is on
0.x, a change to the reference ships in a minor version bump, with a
`changelog.d/` fragment that says what changed (#185, "The reference model
may need to evolve"; [D17](core-semantics.md#d17-changing-the-reference)).

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
* **An overflow to `±∞` raises; an inferred precondition rules it out.**
  An operation on finite doubles whose result is `±∞` raises
  ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575),
  [Floating point](#floating-point)). `verify` rules it out by an inferred
  precondition, as for a `SUM` below: proved from the bounds where they do
  it, otherwise listed in `Report.assumed` and checked on the data by the
  written SQL while the job runs. The proof holds
  under these assumptions (`Rel.noIssue_of_assumedHold`). With
  `infer=False` it is an error that makes the report unproved.
* **`SUM` overflow is an inferred assumption, checked on the data.**
  A group's integer sum may leave 64 bits, and a decimal sum its precision
  (`DECIMAL(min(38, p + 10), s)`, [#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316));
  the reference raises there, and so does DuckDB past 38 digits.
  Where the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an
  aggregate without groups: `Rel.maxRows`) and the argument's range bounds
  each value (`Measure.sumFits`), it is ruled out. A group has fewer than
  2⁶³ rows by the size hypothesis (`Rel.sumRows`, [#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)),
  so an integer `SUM` of values in `[-1, 1]`, such as
  `SUM(CASE WHEN … THEN 1 ELSE 0 END)`, always fits. Elsewhere `verify` assumes
  each sum fits, as it assumes inferred bounds (#244), and lists it in
  `Report.assumed`; the written SQL checks it on the data while the job runs
  and raises if a sum does not fit. The proof holds under that assumption
  (`Rel.noIssue_of_sumsFit`). With `infer=False` it is an error that makes the
  report unproved. A row cap on the inputs (`sv.max_rows(n)`,
  [#219](https://github.com/AlexanderNenninger/substrait-lean/issues/219))
  or a bound on the rows per grouping key (`sv.rows_per(cols, at_most=n)`)
  discharges it statically: with values in `[-m, m]` and at most `n` rows
  in a group, `n · m < 2⁶³` proves the sum fits (`Rel.issuesCapped_sound` in
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
| `power(-inf, y)`, `y` finite and not an integer | A domain error, as for a finite negative base. IEEE 754 gives `+inf` for `y > 0` and `0` for `y < 0`, as DuckDB does, but Polars's `** 0.5` is a square root and gives NaN; raising keeps every engine within the reference with no shim, and a plan meets it only where `-inf` reaches a fractional power. `power(-inf, 2.0)` is `+inf` and `power(-inf, 3.0)` is `-inf`, as before. | ✓ (`negInfPow` in `Safety.lean`; DuckDB's value in `Profile.duckdb`, fact [duckdb-R15-power-neginf](../characterization/duckdb/facts/duckdb-R15-power-neginf.json)) |
| No operation creates `±∞` | A `±∞` from the data passes through. An operation on finite doubles whose IEEE result is `±∞` raises: `+`, `-`, `*`, `/` and `power` that overflow (`1e308 * 10`, `power(10, 400)`, `power(0, -1)`), `exp` past `709.78`, and a `SUM`, `AVG`, variance, covariance or correlation of finite values that overflows. As for a `SUM` that leaves 64 bits, `verify` rules the error out by an inferred precondition: proved from the bounds where they do it, otherwise listed in `Report.assumed` ("stays finite where its inputs are") and checked on the data, where the SQL sverify writes raises `overflow to infinity`. With no NaN and no `±∞` in the inputs, there is none in the outputs. | ✓ ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)): `Issue.infinite` (`BinFn.infIssue`, `UnFn.infIssue`, `Measure.makesInf` in `Safety.lean`), on DuckDB and Polars. A `SUM` or `AVG` of values within `2⁴⁰⁰` over at most `2³²` rows (`max_rows`) is proved finite (#85's `floatBound`); a single operation's result has no bound in the checker, so its precondition is always checked on the data ([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582) proves it from bounds). `Rel.eval` keeps the IEEE value on the rows the precondition excludes, which is what DuckDB and Polars give without the check ([duckdb-double-overflow](../characterization/duckdb/facts/duckdb-double-overflow.json)), so the lift of DuckDB's SQL with `semantics="duckdb"` states it exactly. Substrait's YAMLs leave it unspecified ([ST-9](../upstream/bugs/ST-9.json)). |
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
| Constants that raise | A constant subexpression that raises (`1 // 0 = 1`, in any branch of a `CASE`, in a `WHERE`) raises for the whole plan, on any data, an empty table included ([D21](core-semantics.md#d21-tighten-the-reference-where-it-stays-practical), #609): DuckDB evaluates a `CASE`'s constant conditions when it plans the query (DD-5). No precondition rules one out; the report names the constant (`Issue.constant`). | ✓ (`Rel.constIssues`) |
| Errors under `AND`, `OR` | Eager: an error in either operand may raise, whatever the other operand's value, as DuckDB and Polars evaluate both ([D19](core-semantics.md#d19-and-and-or-raise-eagerly), #604). `x <> 0 AND 10 // x > 1` may divide by zero; `(CASE WHEN x <> 0 THEN 10 // x END) > 1` does not. A boolean `CASE` is evaluated whole, as `AND`/`OR` (`Parse.eagerly`); another `CASE` evaluates only the branch it takes. The report flags an error inside an `AND` or `OR` and suggests the `CASE`. | ✓ (`Expr.issues` of `.bin`; the hint: `Issue.under_and_or`) |
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
| Time of day (`TIME`) | Microseconds since midnight, from 0 to a day less one microsecond. | ✓ (#52) |
| Time of day ± interval | The time plus the interval's microseconds, modulo a day (Euclidean, `Time.timeOfDay` of the sum): it wraps around midnight both ways, so `TIME '23:30' + INTERVAL 1 HOUR` is `00:30` and `TIME '00:30' - INTERVAL 1 HOUR` is `23:30`. The interval is a constant of days or less; one with months is refused. DuckDB computes the same and drops an interval's months ([`duckdb-time-plus-interval`](../characterization/duckdb/facts/duckdb-time-plus-interval.json)). | ✓ on DuckDB ([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)); other engines refuse it until #271 |
| Truncating a time of day | A floor of the microseconds to an hour, minute, second or millisecond (`Time.trunc`), which stays within the day. | ✓ on DuckDB ([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)); other engines refuse it until #271 |
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
| `typeof` | Of a column, a string constant: DuckDB's name of the column's type (`BIGINT`, `DECIMAL(10,2)`, `VARCHAR[]`; [`duckdb-typeof-names`](../characterization/duckdb/facts/duckdb-typeof-names.json)), whichever engine runs the plan, so every engine gives the same string. The Ibis producer folds it before the plan is checked. Of an expression, or of a struct or map, it is refused: DuckDB infers that type its own way. | ✓ ([#508](https://github.com/AlexanderNenninger/substrait-lean/issues/508)) |
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
| `COVAR_SAMP` / `COVAR_POP` / `CORR` | Of pairs of doubles (integers converted), rows with a NULL in either skipped (`BinFn.pair`). Each engine's own algorithm, within the generic properties of [Statistical aggregates](#statistical-aggregates): the model claims a double or NULL. NULL for no pairs, for a sample covariance of one pair, and for `CORR` of fewer than two pairs or of a side whose values are all equal, as the SQL standard says (DuckDB's own `CORR` gives NaN there, and so does the SQL lift with `semantics="duckdb"`, `duckdb-corr`). An infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, on DuckDB ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); other engines refuse it until #271; refused over windows |
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

### Quantiles, mode and arg_min

These need every value of a group ([#53](https://github.com/AlexanderNenninger/substrait-lean/issues/53)).
NULLs are skipped, no values give NULL, and `DISTINCT` and `FILTER` apply
as for the others. The fraction `q` of a quantile is a constant decimal in
`[0, 1]`, exact (`0.1` is one tenth); the frontends write it as a DECIMAL
literal, which DuckDB reads exactly. Approximate quantiles stay refused
([#469](https://github.com/AlexanderNenninger/substrait-lean/issues/469)).

| Topic | Reference | Status |
|---|---|---|
| `QUANTILE_DISC(x, q)` | Of the `n` values in `ORDER BY` order (doubles: `-∞ < … < +∞ < NaN`), the one at position `⌈n·q⌉`, counting from 1, and the first where `n·q ≤ 1` (`discIndex`). Any type `MIN` takes; the result has the argument's type and is one of its values, so contracts keep the argument's range. DuckDB's `QUANTILE` and the `MEDIAN` of a value that is not a number are `QUANTILE_DISC(x, 0.5)`. | ✓ on DuckDB (`duckdb-quantile-disc`); other engines refuse it until #271; refused over windows |
| `QUANTILE_CONT(x, q)`, `MEDIAN(x)` | Of doubles, integers converted first; the result is a double. With `lo` and `hi` the values at 0-based positions `⌊(n−1)·q⌋` and `⌈(n−1)·q⌉`: `lo` where they coincide, else a double between `lo` and `hi` (`contAllowed`). Engines round the interpolation their own way; the model computes DuckDB's `lo·(1−d) + hi·d`, `d = frac((n−1)·q)`, kept between the two. Contracts know the result lies within the argument's range. `MEDIAN` is `QUANTILE_CONT(x, 0.5)`. DECIMAL, DATE and TIMESTAMP arguments are refused (DuckDB interpolates them in their own types). | ✓ on DuckDB, which may round past the neighbours and gives NaN between `-∞` and `+∞`; the written SQL clamps (`duckdb-quantile-cont-interpolation`); other engines refuse it until #271 |
| `MODE(x ORDER BY …)` | The most frequent value; of the values that tie, the first in the aggregate's own `ORDER BY`, rows tied there in list order (`modeOf`). Refused without an `ORDER BY`, as DuckDB's ties then follow its scan. `MODE(x ORDER BY x)` takes the smallest of the most frequent values, and Ibis's `mode()` is written so; a report is `deterministic` when the order includes `x`'s column, or when the group's and the order's columns contain a key. | ✓ on DuckDB (`duckdb-mode-ties`); other engines refuse it until #271 |
| `ARG_MIN(x, y)` / `ARG_MAX(x, y)` | `x` at the row with the smallest (largest) `y`, over the rows where neither is NULL: `FIRST(x ORDER BY y)` (`DESC`) with the filter `y IS NOT NULL`, which the parser makes it. `y` is a column. The result is one of `x`'s values. Ties are the engine's, as for `FIRST`: a report is `deterministic` only when the group's and `y`'s columns contain a key. | ✓ on DuckDB (`duckdb-arg-min-nulls`); other engines refuse it until #271 |

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
| Aggregates | NULLs are skipped. `COUNT` of no rows is 0, a [black box](#black-boxes) its row's `empty`; every other aggregate of no rows is NULL. Without grouping keys, an empty input still gives one row; with keys, none. | ✓ |
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

## Black boxes

DuckDB functions that are hard or pointless to model exactly are black boxes
([#325](https://github.com/AlexanderNenninger/substrait-lean/issues/325)): one
row each in a table, `SubstraitLean/BlackBox.lean`, mirrored for the lift and
the writers in `python/src/sverify/black_box.py`.

| Topic | Reference | Status |
|---|---|---|
| The table | A row gives the function's name, its argument and result types (an integer, a double, a string, a boolean, a date, an `atom`, which is an integer, string or boolean, a list of doubles or of integers, or any value), how it treats NULL (a scalar is strict or not; an aggregate skips NULLs and gives `empty` without values), whether it may raise, and its laws: `nonNull`, `atLeast k`, `atMost k`. A double's bounds are on its code (`atLeast 0` is `≥ +0.0`). | ✓ |
| Meaning | The function itself is an `opaque` constant (`rawScalar`, `rawAgg`). The model's value is that function where it keeps the row's laws, and the row's `sample` elsewhere, so each law is a theorem (`BlackBox.Scalar.call_ok`, `Aggregate.call_ok`), proved from the table by `decide`, with no axiom. That DuckDB computes the model's function, and so keeps the laws, is the trusted part, in `Impl.Faithful` and the profile's agreement with the engine ([Trusted assumptions](#trusted-assumptions)). | ✓ |
| Contracts | The range analysis knows a black box's result only from its type and laws (`BlackBox.lawsAbs`): `entropy(x) >= 0`, `base64(encode(s)) IS NOT NULL` for a non-NULL `s`, `strlen(s) >= 0`, `yearweek(d) <= 588158053` and `array_cosine_similarity(a, b) >= -1` are proved. | ✓ |
| Errors | A scalar that may raise reports a domain error (`Issue.domain`) on the arguments it raises on, which the function decides (`rawRaises`). An aggregate that may raise reports one on the groups it raises on (`rawAggRaises`), as a variance of an infinity does (`AggFn.makesNan`, #326). | ✓ |
| Plans | A call is the extension function of the row's name under the URN `extension:io.sverify:black_box`, anchors 700–799 (`SubstraitLean/Write.lean`). One or two arguments for a scalar, one for an aggregate, which is not decomposable (shards refuse it) and not over a window yet. | ✓ |
| `base64` | `base64(encode(s))` (also `to_base64`): the UTF-8 bytes of a string in base64. Strict, and not NULL for a string. Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `printf`, `format` | `printf(fmt, x)` (C's format strings) and `format(fmt, x)` (`{}` fields) of one integer, string or boolean ([#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). Strict; raise where a field does not fit the value or has none, which `verify` reports as a domain error; a string where they do not. A double or a date is refused: the model's value of either is an integer, which the function could not tell apart from one (`duckdb-printf`). More values are refused. Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |
| `octet_length`, `strlen` | `octet_length(encode(s))` and `strlen(s)`: the number of UTF-8 bytes of a string (#328). Strict, not NULL for a string, and at least 0. Lean evaluates them. | ✓ on DuckDB; other engines refuse them until #271 |
| `signbit` | `signbit(x)` of a double: its sign bit (#328), TRUE for `-0.0` and a negative NaN. Strict, and not NULL for a double. The model's codes have one zero and one NaN, so Lean evaluates it everywhere else and refuses to print rows there (`duckdb-signbit`). | ✓ on DuckDB; other engines refuse it until #271 |
| `yearweek` | `yearweek(d)` of a date: its ISO year times 100 plus its ISO week, the week subtracted in the years up to 0 (#328, `duckdb-yearweek`). Strict, between -587764053 and 588158053, and NULL for an infinite date and before 5877641-01-04 BC, where DuckDB raises (as `date_part` is NULL outside chrono's dates). Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `weekday` | `weekday(d)` is `dayofweek(d)`, `date_part('dow', d)`: modelled exactly, Sunday 0 (#328). | ✓ |
| Vectors | `list_cosine_similarity`, `list_cosine_distance`, `list_distance`, `list_inner_product` (also `list_dot_product`), `list_negative_inner_product` and `array_cross_product` of two lists of doubles ([#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)). Strict; raise where a list holds a NULL or the two differ in length (the cross product: are not of length 3). The similarity is at least `-1.0` and the cosine distance at least `+0.0`: NULL for empty lists, NaN for a zero vector or one with NaN or an infinity, so neither has an upper bound. The distance is not NULL and at least `+0.0`; the inner products and the cross product are not NULL (`duckdb-list-vectors`). The model has no fixed-size ARRAY, so DuckDB's `array_cosine_similarity`, `array_distance`, `array_inner_product`, … are read as the functions of lists. Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |
| `list_sum` | `list_sum(l)` of a list of integers: the sum of its values, NULLs skipped, NULL without any (#327). DuckDB's is a HUGEINT; the model's a BIGINT, which raises past its range, as `SUM` (`duckdb-list-sum`). Lean evaluates it. Of doubles it is refused. | ✓ on DuckDB; other engines refuse it until #271 |
| `list_extract`, `array_value` | `list_extract(l, i)`, `list_element` and `array_extract` of a list are `l[i]`, and `array_value(a, …)` is the list literal `[a, …]`: modelled exactly (#327), with their limits (a constant index, constant elements). | ✓ |
| `bit_count` | `bit_count(x)` of a BIGINT: the 1 bits of its 64-bit two's complement ([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)). Strict, not NULL, in [0, 64]. DuckDB counts the bits of the argument's own width, so narrower integers are refused. Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `age` | `age(a, b)` is an INTERVAL of months, days and microseconds, which the model lacks; `age(ts)` reads the clock. Refused (#328). | Refused |
| `entropy` | `entropy(x)` of any type: the Shannon entropy, in bits, of the counts of the distinct values; `0.0` without values. Not NULL and at least `+0.0`. Lean does not evaluate it, so `substrait-check` refuses to print rows of a plan with it. | ✓ on DuckDB; other engines refuse it until #271 |

| Statistical aggregates | `product`, `kahan_sum` (also `fsum`, `sumkahan`), `favg`, `sem`, `mad`, `kurtosis`, `kurtosis_pop` and `skewness` of doubles, integers converted as DuckDB converts them (#326). NULL without values. `product`, `kahan_sum` and `favg` are not NULL over values; `sem` and `mad` are not NULL and at least `+0.0`. `kurtosis`, `kurtosis_pop` and `skewness` are NULL for few or equal values and raise on an infinity, NaN, or a value whose fourth (third) power overflows (`duckdb-moments`). `mad` of a DECIMAL or a temporal type is refused. `histogram` (a MAP) and `weighted_avg` (two arguments) are refused (`duckdb-statistical-aggregates`). Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |

## Trusted assumptions

What a proof does not cover. A theorem about `Rel.eval` holds for the model;
these links connect it to a real run.

| Assumption | Where | Status |
|---|---|---|
| **The size hypothesis**: every string has fewer than 2³² characters (`Text.sizeCap`, decided on [#336](https://github.com/AlexanderNenninger/substrait-lean/issues/336): DuckDB's strings hold fewer than 2³² bytes), every relation a window reads has fewer than 2⁶² rows (`Rel.Small`, `Text.rowCap`), and every relation an aggregate reads fewer than 2⁶³ (`Rel.sumRows`, #437). | Used by the range analysis (`CHARACTER_LENGTH`, `strpos`, `levenshtein`, `ROW_NUMBER`, …) and by `SUM` overflow (a `SUM` of values in `[-1, 1]`). | ✓ The theorems that need it take `Rel.Small`; an override of Substrait ([Overrides](#overrides)) |
| **The frontends** produce the plan the user meant: the Ibis producer, and SQLGlot with sverify's own Substrait producer for SQL ([#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231), [PR #252](https://github.com/AlexanderNenninger/substrait-lean/pull/252)). The SQLGlot lift writes each function's options explicitly from the source dialect. | `python/src/sverify/ibis_substrait/`, `python/src/sverify/sql_lift/` | On `main`: the Ibis producer, and the SQLGlot lift for DuckDB's SQL (#252, #264). DataFusion's SQL producer is no longer a frontend (#211) |
| **Black boxes are DuckDB's functions.** Each black box ([Black boxes](#black-boxes)) means the function DuckDB computes under its name, and DuckDB's keeps its row's laws. | `SubstraitLean/BlackBox.lean` | Tested: DuckDB on the SQL against DuckDB on the plan Lean writes back, and the laws on random data (`python/tests/test_black_box.py`) |
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
| The loose core and profiles as constraints (design) | [core-semantics.md](core-semantics.md), [#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444) |
