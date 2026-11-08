# Reference semantics

What sverify's plans mean. `Rel.eval` (`SubstraitLean/Rel.lean`) is the
**reference semantics**, the strict profile plans are proved under:
`verify` proves things about it, and every engine's row of the realizability
table is its difference from it. The reference is one profile of the core,
which does a superset of operations; the other profiles and the engines are
in [core, profiles and engines](core-semantics.md#core-profiles-and-engines),
and what a proof under the reference guarantees in
[core-semantics.md](core-semantics.md#what-a-proof-under-the-reference-guarantees). This page collects the choices
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
(`Rel.duckdb_shim_sound`); for a plan proved to never raise the two agree
(`Rel.duckdb_sound`). `Rel.eval` (`SubstraitLean/Rel.lean`) computes one allowed result, a
witness (`Rel.eval_allowed`), and `verify` proves its theorems through it.

The set holds more than one result only where the reference leaves a choice
to the engine:

* the order of rows, except what an `ORDER BY` promises, and how ties in an
  `ORDER BY` or a window's order are broken;
* the row `FIRST`, `LAST`, `collect` and `STRING_AGG` take first where their
  order ties (any row without an order, as in Ibis's `distinct(on=)`);
* a statistical aggregate's value (`VARIANCE`, `STDDEV`, `COVAR_*`, `CORR`),
  within its generic properties (`StatProps`, with #85) before D30; since
  D30 the reference's is the exact moments rounded once, and the generic
  properties are an engine's.

A plan without these choices (`Rel.detPlan`) allows only `Rel.eval`'s rows, in
any order (`Rel.allowed_perm_eval`), so a theorem about `Rel.eval`'s rows holds
of every allowed result. Where a plan leaves ties open, the contract checker
proves its postconditions and keys over every order
(`Rel.OrderAllowed`, `contract_sound_all`, `SubstraitLean/OrderAllowed.lean`, `SubstraitLean/Contracts.lean`), and
`Rel.eval`'s order is the deterministic profile's
([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)).
`Report.deterministic` is false where rows may tie in the order of a window,
of `FIRST`, `LAST`, `STRING_AGG` or `MODE`, or of a `FETCH`
(`Rel.windowsTotal`, `Rel.fetchesTotal`), `str(report)` names each place, and
`Report.ties` gives the keys that would close them.
`RANK`, `DENSE_RANK`, `PERCENT_RANK` and `CUME_DIST` over the window's own
order need no key: tied rows get the same value in every arrangement
(`window_tieFree`). A key on one column of a pair an inner join's or a filter's
condition equates is a key on the other (`KeyOn.eqVariants`), so a key breaks ties
through a join from either side;
it does not yet flag the other choices.

The reference is not a model of any engine, DuckDB included. It is stricter
than every engine in most options: where engines disagree on an edge case it
raises, so a proved plan never reaches that case. Each engine is
characterized as a **diff** against it (`characterization/<engine>/`): which
behaviours it has natively, which need a shim (a guard, a cast, a `CASE`), and
which the translation refuses. The shims are proved against the reference in
Lean, and that each engine matches its profile is tested; both are in
[engine-profiles.md](engine-profiles.md#profiles-and-shims-in-lean-185-first-slice).

New functions run on DuckDB first, and the other engines refuse them until
their lowerings land
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).

## Principles

Decided on #185 ("Principles for the reference model"):

| # | Principle | What it means in practice |
|---|---|---|
| 1 | **Follows Substrait, options included.** | A function means what its extension YAML says. An option set in the plan is part of its meaning. Where the reference overrides Substrait, it says so, with the reason ([Overrides](#overrides)). |
| 2 | **The least surprising choice where Substrait is silent**, with its reason. | An option the plan omits, or behaviour the spec leaves open, gets one choice, written down below with the reason. |
| 3 | **Every engine can follow it with reasonable effort.** | Types keep their declared widths (`i8`…`i64`); there are no unbounded integers. Every choice has a reasonable shim or translation on each engine sverify supports, DuckDB, Polars, Spark and Snowflake ([the engines](stability.md#engines)), one that can be built and run. |
| 4 | **Keeps optimizations provable.** | Filter pushdown, reordering, sharding and incremental maintenance stay provable. A rewrite refines the plan (`Rel.Refines`): it may narrow the set of allowed results, never widen it. This is why an error means "may raise" ([Errors](#errors)). |

## Overrides

Where the reference departs from Substrait, and why:

| Override | What the reference does | Why |
|---|---|---|
| One zero | `-0.0` is `0.0` everywhere, so `1.0 / -0.0 = inf`, and `GROUP BY`, `DISTINCT` and joins see one zero. | SQL users expect `-0.0 >= 0` ([#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89)). DuckDB, Polars and Spark keep IEEE's two zeros in arithmetic (`zero_sign` `IEEE` in their tables; [duckdb-R14](../characterization/duckdb/facts/duckdb-R14.json), [spark-zero-sign](../characterization/spark/facts/spark-zero-sign.json)), and their writers read results with one zero (`canon`); DataFusion keeps them apart in its order ([D32](core-semantics.md#d32-doubles-have-one-zero-and-one-nan)). |
| One NaN | One NaN, equal to itself and greater than every number, `+∞` included. | DuckDB, Polars and Spark compare, group and sort NaN this way (`nan_equality` `NAN_IS_NAN`, `nan_order` `GREATEST` in their tables; #89, D32); IEEE's NaN, unequal to itself, would split `GROUP BY` and `DISTINCT` and drop rows from joins. |
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
  than the original, and allow fewer results. It never gives a result the
  original doesn't allow, up to an observation, and never raises where the
  original didn't (`Rel.RefinesUpTo`, #897). `Rel.Refines` is the exact case,
  which keeps the order an `ORDER BY` fixes, and `Rel.RefinesBag` the case up
  to the order of rows. A rewrite to a plan without choices whose rows are
  the original's refines it up to the order of rows (`Rel.refines_of_perm`,
  `Rel.refines_of_same`); `optimize`'s rewrites do (`Rel.optimize_refines`).
  An unsorted plan refines its `ORDER BY` twin up to the order of rows and
  not exactly (`Rel.unsorted_refinesBag_not_refines`). ✓ (#185)
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
  `on_inferred="off"` it is an error that makes the report unproved.
* **`SUM` overflow is an assumption, checked at run time.**
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
  (`Rel.noIssue_of_sumsFit`). With `on_inferred="off"` it is an error that makes the
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
| `modulus` | `division_type` TRUNCATE: the remainder takes the dividend's sign (`Int.tmod`). | ✓ A plan may state `division_type: TRUNCATE`. The parser reads `FLOOR` (`Expr.floorModOf`, Polars's `%`), which the reference profile refuses and `semantics="polars"` allows. |

Decisions: #185 "Decided: what the reference does when a plan omits an
option"; #202 "Decided (2026-11-01)"; #209 "Decided".

### Floating point

| Topic | Reference | Status |
|---|---|---|
| `fp64` | IEEE 754 binary64. `+ − × ÷` are the exact result rounded once, to nearest, ties to even ([D31](core-semantics.md#d31-double-arithmetic-is-exact-rounded-once), `FloatArith.lean`); `pow`, `log` and the other libm functions use Lean's native `Float`. | ✓ |
| `fp32` | IEEE binary32. | **Not yet.** `fp32` arithmetic is refused (fact [duckdb-R12](../characterization/duckdb/facts/duckdb-R12.json), #208); [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417) models it. |
| Zero | One zero. `-0.0` is `0.0` everywhere, so `1.0 / -0.0 = inf`. | ✓ ([#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), decided on #209; [D32](core-semantics.md#d32-doubles-have-one-zero-and-one-nan)) |
| NaN | One NaN, equal to itself, greater than every number, `+∞` included. `GROUP BY`, `DISTINCT` and sorting treat all NaNs alike. A NaN's sign is no value of the reference: the sign of a NaN an operation creates depends on the platform, negative on Linux x86_64 and positive on macOS arm64, in DuckDB and Polars alike ([duckdb-exec-platform](../characterization/duckdb/facts/duckdb-exec-platform.json)). | ✓ |
| **No operation creates a NaN** | A NaN from the data passes through. An operation on non-NaN inputs whose IEEE result is NaN raises instead: `0/0`, `inf - inf`, `inf + (-inf)`, `0 * inf`, `inf / inf`, domain errors (`sqrt(-1)`, `sin(±inf)`, a negative base to a fractional power), `fmod(±inf, y)`, and a double `SUM` or `AVG` of `+∞` and `-∞`. With no NaN in the inputs (`~_.v.isnan()` in `requires`), there is none in the outputs. | ✓ ([#257](https://github.com/AlexanderNenninger/substrait-lean/issues/257)): `Issue.domain` (`nanCase` in `Safety.lean`), and the parser accepts only `on_domain_error: ERROR` for `divide` and `power`. A window `SUM`/`AVG` whose frame may hold `+∞` and `-∞` is a domain error too, as the grouped one is. Two exceptions: `on_division_by_zero: IEEE` asks for NaN at `0.0 / 0.0` and gets it, and DataFusion runs the written plan natively, so it gives NaN where the reference raises (as it gives `±∞` for a zero divisor); DuckDB, Polars, Spark and Snowflake raise. (Decided on #185, "no newly created NaNs"; [D33](core-semantics.md#d33-no-operation-creates-a-nan)) |
| `power(-inf, y)`, `y` finite and not an integer | A domain error, as for a finite negative base. IEEE 754 gives `+inf` for `y > 0` and `0` for `y < 0`, as DuckDB does, but Polars's `** 0.5` is a square root and gives NaN; raising keeps every engine within the reference with no shim, and a plan meets it only where `-inf` reaches a fractional power. `power(-inf, 2.0)` is `+inf` and `power(-inf, 3.0)` is `-inf`, as before. | ✓ (`negInfPow` in `Safety.lean`; DuckDB's value in `Profile.duckdb`, fact [duckdb-R15-power-neginf](../characterization/duckdb/facts/duckdb-R15-power-neginf.json)) |
| No operation creates `±∞` | A `±∞` from the data passes through. An operation on finite doubles whose IEEE result is `±∞` raises: `+`, `-`, `*`, `/` and `power` that overflow (`1e308 * 10`, `power(10, 400)`, `power(0, -1)`), `exp` past `709.78`, and a `SUM`, `AVG`, variance, covariance or correlation of finite values that overflows. As for a `SUM` that leaves 64 bits, `verify` rules the error out by an inferred precondition: proved from the bounds where they do it, otherwise listed in `Report.assumed` ("stays finite where its inputs are") and checked on the data, where the SQL sverify writes raises `overflow to infinity`. With no NaN and no `±∞` in the inputs, there is none in the outputs. | ✓ ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)): `Issue.infinite` (`BinFn.infIssue`, `UnFn.infIssue`, `Measure.makesInf` in `Safety.lean`), on DuckDB and Polars. A `SUM` or `AVG` of values within `2⁴⁰⁰` over at most `2³²` rows (`max_rows`) is proved finite (#85's `floatBound`); a single operation's result has no bound in the checker, so its precondition is always checked on the data ([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582) proves it from bounds). `Rel.eval` keeps the IEEE value on the rows the precondition excludes, which is what DuckDB and Polars give without the check ([duckdb-double-overflow](../characterization/duckdb/facts/duckdb-double-overflow.json)), so the lift of DuckDB's SQL with `semantics="duckdb"` states it exactly. Substrait's YAMLs leave it unspecified ([ST-9](../upstream/bugs/ST-9.json)). [D34](core-semantics.md#d34-no-operation-on-finite-doubles-overflows-to-infinity) |
| Division by zero | An error when `on_division_by_zero` is omitted or `ERROR`. `IEEE`, `LIMIT` and `NULL` when the plan asks. | ✓ (#204) |
| Domain errors | `sqrt`, `log`, `asin`, `acos`, `logb`, `atan2(0, 0)` and shifts outside their domain raise (`on_domain_error`, `on_log_zero` = `ERROR`). | ✓ (#215) |
| `round(x, d)` | Halves away from zero, as DuckDB 2.0 computes it ([`duckdb-round-digits-2`](../characterization/duckdb/facts/duckdb-round-digits-2.json)): with `m = 10^abs(d)`, `round(x · m) / m` for `d ≥ 0` and `round(x / m) · m` for `d < 0`, `x` itself where that is not finite (`round(1.5e308, -308)` is `1.5e308`), and 0 for `d < 0` when `m` is infinite (`round(42, -1000)` is 0). `±∞` and NaN stay. DataFusion's `round(x · 10ᵈ) / 10ᵈ` differs, so DataFusion refuses it until #271. | ✓ (#335) |
| `%` on doubles | Substrait has no such function, so the reference defines its own, `sverify_fmod`: C's `fmod`, exact, with the dividend's sign. A zero divisor is an error (`NULL` if the plan asks), an infinite dividend is an error (#257), an infinite divisor gives the dividend, and a NaN passes through. Lean also reads the `modulus` of doubles that DataFusion writes, as the same function. DuckDB's own `%` of doubles gives NaN for a zero divisor, where its documentation says it raises ([DD-8](../upstream/bugs/DD-8.json), [duckdb-R15-double-modulus](../characterization/duckdb/facts/duckdb-R15-double-modulus.json)). | ✓ ([#256](https://github.com/AlexanderNenninger/substrait-lean/issues/256)): Lean writes `sverify_fmod`, the Ibis producer and the SQLGlot lift emit it for `%` of doubles, and DataFusion runs it as its own `%` |
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
[engine-profiles.md](engine-profiles.md#decimals-27).

### NULL

| Topic | Reference | Status |
|---|---|---|
| Logic | Three-valued (Kleene): `AND`, `OR`, `NOT`, comparisons. | ✓ |
| Constants that raise | A constant subexpression that raises (`1 // 0 = 1`, in any branch of a `CASE`, in a `WHERE`) raises for the whole plan, on any data, an empty table included ([D21](core-semantics.md#d21-tighten-the-reference-where-it-stays-practical), #609): DuckDB evaluates a `CASE`'s constant conditions when it plans the query (DD-7). No precondition rules one out; the report names the constant (`Issue.constant`). | ✓ (`Rel.constIssues`) |
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
| `regexp_extract`, `regexp_replace` | A constant pattern that `Text.simpleRegex` accepts, or the plan is refused. `regexp_extract(s, p, g)` is group `g` (0 to 9; DuckDB raises past 9) of the leftmost-first match, `''` where nothing matches, the group took no part, or `p` has fewer groups. `regexp_replace` replaces the first match, or every match with the flag `'g'` (an empty match right after the previous one is skipped); in the replacement, `\0` … `\9` are groups and `\\` a backslash, and other escapes are refused. DuckDB only so far (#271). | ✓ (#50) |
| `regexp_matches`, `regexp_full_match` | Whether a constant pattern matches somewhere in the string, or all of it (the pattern in `^(?:…)$`); NULL for a NULL string. Both are `array_length(regexp_match(s, p)) > 0`. Options, and patterns outside `Text.simpleRegex`, are refused, and so is the operator `~`: SQLGlot reads it as a full match, DuckDB as a match anywhere ([SG-10](../upstream/bugs/SG-10.json)). | ✓ ([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)) |
| `right`, `lpad`, `rpad` | Of a constant count, in characters. `right(s, n)` is the last `n` characters, or all but the first `-n` for a negative `n`. `lpad(s, n, p)` and `rpad(s, n, p)` are the first `n` characters of `s`, or `s` filled to `n` with the constant `p` repeated and cut, as DuckDB pads; `''` for `n ≤ 0`. An empty `p` is refused, as DuckDB raises where `s` is shorter. | ✓ (#808) |
| `split_part`, `concat_ws` | `split_part(s, sep, n)` of a constant `n` is piece `n` of `string_split(s, sep)` (a black box): from 1, from the end for a negative `n`, `''` for `0` and past the pieces, NULL if `s` or `sep` is. `string_split(s, sep)[n]` is the list element. `concat_ws(sep, …)` joins the strings that are not NULL with `sep`: `''` if all are NULL, NULL if `sep` is. | ✓ (#808) |
| `md5`, `sha256` | Lowercase hex of the UTF-8 bytes' digest; never NULL for a string. DuckDB's `hash()` is refused: it is the engine's own and changes between versions. | ✓ (#50) |
| Refused | `translate` (it works on grapheme clusters). | refused |

## Temporal

| Topic | Reference | Status |
|---|---|---|
| `date` | Days since 1970-01-01, proleptic Gregorian. | ✓ |
| `timestamp` | Microseconds since 1970-01-01 00:00, **no time zone**. Time-zone-aware timestamps (`timestampTz`) are a separate kind the model does not compute with. | ✓ |
| Intervals | Day-to-second intervals are microseconds; year-to-month intervals are months. Adding months keeps the day of month. | ✓ |
| Time of day (`TIME`) | Microseconds since midnight, from 0 to a day less one microsecond. | ✓ (#52) |
| Time of day ± interval | The time plus the interval's microseconds, modulo a day (Euclidean, `Time.timeOfDay` of the sum): it wraps around midnight both ways, so `TIME '23:30' + INTERVAL 1 HOUR` is `00:30` and `TIME '00:30' - INTERVAL 1 HOUR` is `23:30`. The interval is a constant of days or less; one with months is refused. DuckDB computes the same and drops an interval's months ([`duckdb-time-plus-interval`](../characterization/duckdb/facts/duckdb-time-plus-interval.json)). | ✓ on DuckDB ([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)); other engines refuse it until #271 |
| Truncating a time of day | A floor of the microseconds to an hour, minute, second or millisecond (`Time.trunc`), which stays within the day. | ✓ on DuckDB ([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)); other engines refuse it until #271 |
| A DATE as a TIMESTAMP | DuckDB types `date_trunc` of a DATE and `DATE ± INTERVAL` as TIMESTAMPs. Of whole days or months they are a date at midnight, which the plan holds as the date; where a TIMESTAMP is needed (an output column, an aggregate) it is cast to its midnight. `DATE ± INTERVAL` of hours or less is the midnight's timestamp plus the interval. | ✓ ([#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807)) |
| `date_diff(unit, a, b)` | The boundaries of `unit` from `a` to `b`, as DuckDB counts them: microseconds, and milliseconds, seconds, minutes and hours floored, before 1970 too; days of the dates; weeks as 7 of those days, toward zero; months, quarters and years of the calendar. A DATE is its midnight. Other units are refused. | ✓ ([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809)) |
| `epoch`, `extract(epoch …)` | The seconds since 1970-01-01, a DOUBLE: the microseconds as a double, divided by 10⁶, as DuckDB computes them. `epoch_us` is the microseconds. | ✓ on DuckDB (#809); other engines refuse it until #271 |
| `make_date`, `last_day` | `make_date(y, m, d)`: the date by `days_from_civil`, NULL if an argument is; an error for a month or day outside the calendar, as in DuckDB, and for a year outside 1 to 9999, where DuckDB gives a date. `last_day(d)` is the last day of the month, a DATE. | ✓ (#809); `make_date` of columns on DuckDB only until #271 |
| Names and ISO parts | `dayname` and `monthname` in English, `isodow` from Monday 1 to Sunday 7, `isoyear` the year of the week's Thursday. | ✓ (#809) |
| Range | **Dates: the SQL standard's, 0001-01-01 to 9999-12-31** (`Time.dayMin`, `Time.dayMax`; decided on #251). Every engine represents them. Date arithmetic (adding days or months) whose operand or result leaves them is an error, reported by `verify` and raised by the engines as "outside the reference's dates". With constant operands (TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`) this is decided when the plan is written, and the SQL has no guard. **Not yet the reference's own:** `date_part` is NULL outside chrono's years −262143 to 262142, and calendar truncations raise outside DataFusion's ±2⁶³ nanoseconds. | ✓ date arithmetic ([#251](https://github.com/AlexanderNenninger/substrait-lean/issues/251)); `date_part` and truncation ranges open |

## Nested: lists and structs

| Topic | Reference | Status |
|---|---|---|
| Representation | A struct is the list of its fields, in order. Equality is structural. | ✓ |
| Order of lists | Lexicographic, element by element; a proper prefix sorts first. `lt`, `gt`, `lte` and `gte` are three-valued: a NULL element that decides the result makes it NULL (`[1, NULL] < [2]` is TRUE, `[1, NULL] < [1, 3]` is NULL). In `ORDER BY` and `MIN`/`MAX`, NULL elements sort after every other value. | ✓ (#207) |
| Lambdas | `any_match`, `all_match`, `transform` and `filter` take a lambda that reads its parameter and the enclosing row ([D28](core-semantics.md#d28-lambdas-have-lexical-scope)). `any_match` is TRUE if some element matches, else NULL if some result is NULL, else FALSE (`[]` gives FALSE). | ✓ (#94) |
| `UNNEST` | One row per element, none for an empty list or NULL (sverify's own extension). | ✓ |
| `list_prepend`, `[a, b]` | `list_prepend(x, l)` is `x` before `l`'s elements, NULL elements kept; a NULL `l` is empty (`BinFn.listPrepend`). A list of computed elements `[a, b]` is `list_prepend(a, list_prepend(b, []))` at the elements' common type. | ✓ on DuckDB; other engines refuse it until #271 (#812) |
| `list_concat` | The elements of both lists; a NULL list is empty, so two NULLs give `[]` (DuckDB 2.0, `BinFn.listConcat`). | ✓ on DuckDB; other engines refuse it until #271 (#812) |
| `list_contains`, `list_position` | `list_contains(l, x)`: TRUE if an element equals `x`, NULL elements equal to nothing; NULL for a NULL `l` or `x`. `list_position(l, x)`: the position from 1 of the first element equal to `x`, a NULL `x` finding the first NULL element; NULL when none is or `l` is NULL, an `INTEGER`. Lists of doubles, decimals and nested values are refused, which DuckDB compares otherwise (`-0.0 = 0.0`). | ✓ on DuckDB; other engines refuse it until #271 (#812) |
| `flatten` | The elements of a list's lists in order, a NULL inner list adding none; NULL for a NULL list (`UnFn.flatten`). DuckDB's `list(x)`, which keeps NULLs, is `flatten(array_agg([x]))`. | ✓ on DuckDB; other engines refuse it until #271 (#810) |

Design notes: [nested-values.md](nested-values.md).

## Casts

| Cast | Reference | Status |
|---|---|---|
| Out of range (`BIGINT` from a wider value, `i8`…`i32` from a larger integer, a double that is NaN, infinite or out of range) | An error: `FAILURE_BEHAVIOR_THROW_EXCEPTION`. | ✓ (`badCast`) |
| Double or decimal to integer | Truncates toward zero. Monotone, so a double's bounds bound the integer: a computed double within its error bound `[x − ε, x + ε]` ([float-bounds.md](float-bounds.md#in-contracts)) casts to `[trunc(x − ε), trunc(x + ε)]`. DuckDB's own cast rounds a double half to even and a decimal half away from zero (`CAST(2.5::DOUBLE AS INTEGER)` is 2, `CAST(2.5 AS INTEGER)` is 3, [duckdb-R9](../characterization/duckdb/facts/duckdb-R9.json)); sverify's SQL truncates a double first, `CAST(trunc(x) AS BIGINT)`. | ✓ (decided on #209) |
| `TRY_CAST` (`failureBehavior: RETURN_NULL`) | NULL where the cast would raise, and then no error: a double to an integer (NaN, `±∞`, outside 64 bits), an integer to a narrower one, and a string (below). `TRY_CAST` to a DECIMAL and of a DECIMAL to an integer are refused. | ✓ on DuckDB (#58); other engines refuse it until #271 |
| A string to a BIGINT, DOUBLE, BOOLEAN, DATE or TIMESTAMP | DuckDB's rules ([`duckdb-cast-varchar`](../characterization/duckdb/facts/duckdb-cast-varchar.json)): spaces around dropped; numbers with a sign, fraction and exponent, a BIGINT rounding the exact decimal half away from zero, a DOUBLE correctly rounded; `true`/`t`/`yes`/`y`/`1` and `false`/`f`/`no`/`n`/`0` in any case; dates and timestamps in ISO form. `CAST` raises on a string DuckDB rejects, and is not NULL for a string; `TRY_CAST` is NULL there. A narrower integer is the BIGINT cast down. Black boxes ([Black boxes](#black-boxes)); a string to a DECIMAL is refused (#27). | ✓ on DuckDB ([#806](https://github.com/AlexanderNenninger/substrait-lean/issues/806)); other engines refuse it until #271 |
| Decimal to a smaller scale | Rounds half away from zero. | ✓ |
| Integer to decimal | Exact; an error if it doesn't fit the precision. | ✓ |
| Double to decimal | `round(x · 10ˢ)` computed in doubles, half away from zero (`-2.675` gives `-2.68`). NaN, `±∞` and a product that overflows raise. Monotone, so a double's bounds bound the decimal, and `verify` reports neither the failed cast nor the precision overflow where the casts of the bounds fit (`FloatCode.toDecimal?_between`). | ✓ (#27, [#223](https://github.com/AlexanderNenninger/substrait-lean/issues/223)) |
| Decimal to double | The nearest double, halves to even: within `2⁻⁵³` of the decimal, relatively (`FloatCode.ofDecimal_rel`), and monotone. | ✓ |
| Integer to double | The nearest double, halves to even: exact up to `2⁵³` in magnitude (`FloatCode.ofInt_exact`), within `2⁻⁵³` relatively beyond (`FloatCode.ofInt_rel`), and monotone (`ofInt_mono`). An integer up to `2⁵³` survives the round trip to a double and back (`FloatCode.toInt?_ofInt`). | ✓ |
| `typeof` | Of a column, a string constant: DuckDB's name of the column's type (`BIGINT`, `DECIMAL(10,2)`, `VARCHAR[]`; [`duckdb-typeof-names`](../characterization/duckdb/facts/duckdb-typeof-names.json)), whichever engine runs the plan, so every engine gives the same string. The Ibis producer folds it before the plan is checked. Of an expression, or of a struct or map, it is refused: DuckDB infers that type its own way. | ✓ ([#508](https://github.com/AlexanderNenninger/substrait-lean/issues/508)) |
| `date` ↔ `timestamp` | A date is days since 1970-01-01, a timestamp microseconds. `date` to `timestamp` is midnight (`UnFn.dateTime`), an error outside the reference's dates; `timestamp` to `date` rounds down, before 1970 too. A date compared with a timestamp is cast to one, as DuckDB does. | ✓ (#206, [#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807)); other engines refuse the cast of a DATE column until #271 |
| `timestamp` to `BIGINT` | `epoch_us(ts)`: the microseconds since 1970-01-01 (`UnFn.epochUs`), the same number. | ✓ on DuckDB ([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809)); other engines refuse it until #271 |

## Aggregates

### Of integers

| Topic | Reference | Status |
|---|---|---|
| `avg` of integers | Follows the plan's declared output type: `fp64` is the mean as a double, `i64` is Substrait's integer `avg`, truncated toward zero (`AggFn.iavg`). The integer one lies between the smallest and largest value ([#237](https://github.com/AlexanderNenninger/substrait-lean/issues/237)). Any other output type is refused. | ✓ (#209) |
| `sum` of integers | Returns `i64`; exact, checked at the end ([Errors](#errors)). | ✓ unbounded in `Rel.eval`, checked at `i64` ([#255](https://github.com/AlexanderNenninger/substrait-lean/pull/255)) |

### Of doubles

| Topic | Reference | Status |
|---|---|---|
| `SUM` / `AVG` | The exact sum of the values as dyadic rationals, rounded once to the nearest double, ties to even; `AVG` the exact sum divided by the count, rounded once (`floatSumCR`, `floatAvgCR`, [D25](core-semantics.md#d25-float-aggregates-are-correctly-rounded-exact-sums)). A NaN, or `+∞` with `-∞`, gives NaN; one kind of infinity gives it; a sum past the largest double is `±∞`. The value does not depend on the order of the rows (`floatSumCR_perm`), and the mean of three `0.1` is `0.1`. Contracts get exact signs (a `SUM` or `AVG` of values `≥ 0` is `≥ 0`) and, for inputs with a row cap (`sv.max_rows(n)`, `n ≤ 2³²`) and values within `2⁴⁰⁰`, the interval of the exact result widened by half an ulp (`floatSumCR_mem`, `floatAvgCR_mem`, proved without axioms). An engine adds in its own order, within the plan's bound of this value (`epsilon_sum_cr` in [`float-bounds/`](float-bounds.md)). `sv.approx` states a postcondition up to that rounding. A sharded or parallel sum may differ in the last bits, so `--shard` refuses it unless `reproducible=` accepts a tolerance on doubles, and `tolerance=True` reports a proved bound on the difference (`floatSplit_sum`); engines that don't fix the order are refused unless `deterministic=True` justifies it. | ✓ order; error bounds ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)) |
| `VARIANCE` / `STDDEV` | Of a sample (`n - 1`, the default) or a population (`n`, `distribution: POPULATION`), of doubles; integers are converted first. The exact moments rounded once (D30); each engine's own algorithm is within the plan's bound of it ([Statistical aggregates](#statistical-aggregates), #54, #85): the model claims a double ≥ 0 or NULL, exactly NULL for no values and for a sample of one value. A NaN passes through; an infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, approximate ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); over a window on DuckDB, tested ([Windows](#windows)); `Report.epsilon` bounds a `VAR_*` column, proved on DuckDB and Spark (`epsilon_var_cr`) and tested on Polars ([`float-bounds.md`](float-bounds.md)); Snowflake runs it on values shifted by their group's mean ([#1023](https://github.com/AlexanderNenninger/substrait-lean/issues/1023)), a `DISTINCT` one refused; the checker keeps "a double ≥ 0 or NULL" |
| `COVAR_SAMP` / `COVAR_POP` / `CORR` | Of pairs of doubles (integers converted), rows with a NULL in either skipped (`BinFn.pair`). The exact co-moments rounded once (D30); each engine's own algorithm is within the plan's bound of it ([Statistical aggregates](#statistical-aggregates)): the model claims a double or NULL. NULL for no pairs, for a sample covariance of one pair, and for `CORR` of fewer than two pairs or of a side whose values are all equal, as the SQL standard says (DuckDB's own `CORR` gives NaN there, and so does the SQL lift with `semantics="duckdb"`, `duckdb-corr`). An infinite value raises, as a deviation from the mean would be NaN. | ✓ grouped, on DuckDB ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)); `Report.epsilon` bounds a `COVAR_*` column from the pair's two ranges (`epsilon_cov_cr`), and gives `CORR` none: its error grows as a side's variance shrinks ([#918](https://github.com/AlexanderNenninger/substrait-lean/issues/918)); other engines refuse it until #271; refused over windows |
| `MIN` / `MAX` of doubles | By the codes' order, `-∞ < … < +∞ < NaN`, as DuckDB orders doubles. | ✓ on DuckDB ([#371](https://github.com/AlexanderNenninger/substrait-lean/issues/371)) and Polars, whose `max` skips NaN, by the shim `max_nan_greatest` ([#697](https://github.com/AlexanderNenninger/substrait-lean/issues/697)); DataFusion (whose grouped min/max of doubles is not IEEE) refuses them until #271 |

### Statistical aggregates

Engines compute `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` with different
algorithms, none documented: DuckDB 2.0 and Spark 4.3 use Welford's update
with Chan's merge, Polars 2.1 a two-pass per block of 128 values when
ungrouped and Welford when grouped (`characterization/*/facts/`, ids
`duckdb-var-stddev`, `duckdb-covar`, `duckdb-corr`, `polars-var-std`,
`polars-cov`, `polars-corr`, `spark-var-stddev`, `spark-covar`, `spark-corr`).
The reference picks none. Since [D30](core-semantics.md#d30-statistical-aggregates-are-correctly-rounded-exact-moments)
its value is the exact moments rounded once (`varOf`, `covOf`, `corrOf`): one
value, whatever the order of the rows. Before D30 it allowed any result with
the generic properties below; they are now what an engine's algorithm may
give (`StatProps` in `SubstraitLean/StatProps.lean`, `StatAlgo` in
`AllowedP.lean`), and each engine is within the plan's bound of the
reference. For `n ≤ 2³²`
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
  least `L ≥ 8E`. Without such a lower bound `CORR` can be any double; the
  writers clamp each engine's to `[−1, 1]` (D30).

The bounds scale with the spread of the values: for values near `10⁶` that
vary by about `1`, the variance of `10⁶` of them is within about `2 · 10⁻²`.
`StatProps` states each square root by a rational witness above it, so the
core needs no square roots. The bounds are proved for the two-pass algorithm
and for DuckDB's Welford update with Chan's merge in any
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
| `QUANTILE_CONT(x, q)`, `MEDIAN(x)` | Of doubles, integers converted first; the result is a double. With `lo` and `hi` the values at 0-based positions `⌊(n−1)·q⌋` and `⌈(n−1)·q⌉`: `lo` where they coincide, else a double between `lo` and `hi` (`contAllowed`). Engines round the interpolation their own way; the model computes DuckDB's `lo·(1−d) + hi·d`, `d = frac((n−1)·q)`, kept between the two. Contracts know the result lies within the argument's range. `MEDIAN` is `QUANTILE_CONT(x, 0.5)`. Between `lo = -∞` and `hi = +∞` the interpolation is NaN (IEEE, DuckDB), a NaN created from numbers: the reference raises there, a domain error ruled out by a precondition ([D21](core-semantics.md#d21-tighten-the-reference-where-it-stays-practical), #561). DECIMAL, DATE and TIMESTAMP arguments are refused (DuckDB interpolates them in their own types). | ✓ on DuckDB, which may round past the neighbours: the written SQL clamps, and raises where the interpolation is NaN and no value is (`duckdb-quantile-cont-interpolation`); other engines refuse it until #271 |
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
| `FIRST` / `LAST` / `list` in SQL (#810) | DuckDB's `first(x ORDER BY …)`, `last(x …)` and `list(x …)` (`array_agg`) keep NULLs: the lift aggregates `[x]`, never NULL, and takes `first([x])[1]` or `flatten(array_agg([x]))`. `bool_and` and `bool_or` are `MIN` and `MAX` of booleans. | ✓ on DuckDB; other engines refuse it until #271 |
| `STRING_AGG` (#55) | The non-NULL strings in the aggregate's own `ORDER BY`, joined by a constant separator; NULL without one. Without an `ORDER BY` every row ties, and the strings may come in any order. It is determined as `FIRST` is: ties go in list order, so a report is `deterministic` only when the group's and the order's columns contain a key. A contract sees some string or NULL, and a postcondition is proved for every order the ties allow ([Ties](#relations)). | ✓ on DuckDB; other engines refuse it until #271 |

## Windows

| Topic | Reference | Status |
|---|---|---|
| `NTILE(k)` | The SQL standard's buckets: of `n` rows, the first `n % k` buckets hold `⌊n / k⌋ + 1` rows and the rest `⌊n / k⌋`; with fewer rows than buckets, a bucket for each row (`ntileOf`). Between 1 and the row's number, proved. | ✓ on DuckDB, Spark, Snowflake and Polars; **refused** on DataFusion, which spreads the larger buckets out ([DF-11](../upstream/bugs/DF-11.json)) |
| `FIRST_VALUE(x IGNORE NULLS)`, `LAST_VALUE(…)` | The frame's first (last) non-NULL `x` in the window's order, NULL without one: the measure `FIRST` (`LAST`) over the frame, whose rows come in that order (`Parse.parseWindow`). Last observation carried forward is `LAST_VALUE(x IGNORE NULLS)` over `ROWS UNBOUNDED PRECEDING`. | ✓ on DuckDB; other engines refuse it until #271 (#811) |
| `RANGE` frames with an `INTERVAL` | A constant interval of days or less, over one timestamp (in microseconds) or date (whole days) sort key; months and years have no fixed length and are refused. | ✓ (#811) |
| `SUM` and `AVG` of doubles over a frame | The measure over the frame's rows, as the aggregate. | ✓: the engine's own sum, within the plan's bound for the input's row cap. Each engine's window algorithm (`window_sum_algo`, [#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)) sums the frame's values: DuckDB a segment tree, a running sum or each frame anew (duckdb-window-sum-order), Polars each frame anew (polars-window-agg), Spark each frame anew or a running sum (spark-window-agg); the probe is `sverify_dev.probe_window_sums`. Snowflake's SQL is written as before, with no class claimed for it (its window algorithm has no public fact, #1032) |
| `VARIANCE` / `STDDEV` over a frame | `varOf` of the frame's doubles: the exact moments rounded once (D30). NULL, NaN and an infinity as for the aggregate. | ✓ on DuckDB, its own `VAR_*` or `STDDEV_*` clamped at `0`, with no bound on the column yet: a run is tested ([#918](https://github.com/AlexanderNenninger/substrait-lean/issues/918)); other engines refuse it until [#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271); `COVAR_*` and `CORR` over a frame are refused |

## Relations

| Topic | Reference | Status |
|---|---|---|
| Bags | A relation is a list of rows read as a bag: two relations are equal when they are permutations of each other (`Rel.Equiv`). | ✓ |
| Operators | `read`, `values`, `filter`, `project`, `emit`, `cross`, inner and left `join`, `semi` and `anti`, `fetch`, `orderBy`, `distinct`, `aggregate` (one grouping set), `window`, `unnest`, `UNION ALL`. | ✓ |
| Set operations | `UNION ALL` is bag union and `UNION DISTINCT` is `distinct` of it. The SQL lift writes `INTERSECT` and `EXCEPT` as the left rows with (without) an equal right row, NULLs equal, by a semi (anti) join, and `DISTINCT`; with `ALL` it numbers each side's equal rows (`ROW_NUMBER() OVER (PARTITION BY` every column`)`) and joins on the number too, so `m` and `n` copies leave `min(m, n)` and `max(m − n, 0)`. The window has no order, but the rows it ties are equal, so `INTERSECT ALL` and `EXCEPT ALL` are deterministic without keys (`Rel.window_allColumns`). Substrait's `SET_OP_INTERSECTION_*`/`SET_OP_MINUS_*` are not read yet. | ✓ (#344) |
| Ties | Any order: rows that tie in a sort or a window's order, the rows a `fetch` takes and the rows `FIRST`, `STRING_AGG` and `MODE` take where their order ties (`Rel.OrderAllowed`). Postconditions and keys are proved for every order (`contract_sound_all`, `Rel.keys_sound_all`). `Rel.eval` sorts stably and takes `fetch` rows in list order, the deterministic profile's order ([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)). A report's `deterministic` says whether the plan's sort keys and window orders are total on the input's keys, and `str(report)` names each place where they are not; the Spark and Snowflake translations, which have no row order, refuse sorts, `LIMIT` and windows that are not, unless `deterministic=True` is justified by it. | ✓ |
| Sort keys | A key states where NULLs go with `SORT_DIRECTION_{ASC,DESC}_NULLS_{FIRST,LAST}`. A sort relation's key may also leave it open: an `UNSPECIFIED` or missing direction puts NULLs last ([D8](core-semantics.md#d8-the-references-null-order)), and `CLUSTERED` keeps equal keys adjacent with the groups in any order ([D6](core-semantics.md#d6-sort-keys-without-a-null-order)). A window's or a measure's key must state its direction. The Ibis producer and the SQL writer always write all four parts. | ✓ (`parseSortKey`) |

## Black boxes

DuckDB functions that are hard or pointless to model exactly are black boxes
([#325](https://github.com/AlexanderNenninger/substrait-lean/issues/325)): one
row each in a table, `SubstraitLean/BlackBox.lean`, mirrored for the lift and
the writers in `python/src/sverify/black_box.py`.

| Topic | Reference | Status |
|---|---|---|
| The table | A row gives the function's name, its argument and result types (an integer, a double, a string, a boolean, a date, an `atom`, which is an integer, string or boolean, a timestamp, a list of doubles, of integers or of strings, or any value), how it treats NULL (a scalar is strict or not; an aggregate skips NULLs and gives `empty` without values), whether it may raise, and its laws: `nonNull`, `atLeast k`, `atMost k`. A double's bounds are on its code (`atLeast 0` is `≥ +0.0`). | ✓ |
| Meaning | The function itself is an `opaque` constant (`rawScalar`, `rawAgg`). The model's value is that function where it keeps the row's laws, and the row's `sample` elsewhere, so each law is a theorem (`BlackBox.Scalar.call_ok`, `Aggregate.call_ok`), proved from the table by `decide`, with no axiom. That DuckDB computes the model's function, and so keeps the laws, is the trusted part, in `Impl.Faithful` and the profile's agreement with the engine ([Trusted assumptions](#trusted-assumptions)). | ✓ |
| Contracts | The range analysis knows a black box's result only from its type and laws (`BlackBox.lawsAbs`): `entropy(x) >= 0`, `base64(encode(s)) IS NOT NULL` for a non-NULL `s`, `strlen(s) >= 0`, `yearweek(d) <= 588158053` and `array_cosine_similarity(a, b) >= -1` are proved. | ✓ |
| Errors | A scalar that may raise reports a domain error (`Issue.domain`) on the arguments it raises on, which the function decides (`rawRaises`). An aggregate that may raise reports one on the groups it raises on (`rawAggRaises`), as a variance of an infinity does (`AggFn.makesNan`, #326). | ✓ |
| Plans | A call is the extension function of the row's name under the URN `extension:io.sverify:black_box`, anchors 700–799 (`SubstraitLean/Write.lean`). One or two arguments for a scalar, one for an aggregate, which is not decomposable (shards refuse it) and not over a window yet. | ✓ |
| `base64` | `base64(encode(s))` (also `to_base64`): the UTF-8 bytes of a string in base64. Strict, and not NULL for a string. Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `printf`, `format` | `printf(fmt, x)` (C's format strings) and `format(fmt, x)` (`{}` fields) of one integer, string or boolean ([#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). Strict; raise where a field does not fit the value or has none, which `verify` reports as a domain error; a string where they do not. A double or a date is refused: the model's value of either is an integer, which the function could not tell apart from one (`duckdb-printf`). More values are refused. Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |
| `octet_length`, `strlen` | `octet_length(encode(s))` and `strlen(s)`: the number of UTF-8 bytes of a string (#328). Strict, not NULL for a string, and at least 0. Lean evaluates them. | ✓ on DuckDB; other engines refuse them until #271 |
| `signbit` | `signbit(x)` of a double: its sign bit (#328), TRUE for `-0.0` and a negative NaN. Strict, and not NULL for a double. The reference reads doubles with one zero and one NaN, so Lean evaluates it everywhere else and refuses to print rows there (`duckdb-signbit`). | ✓ on DuckDB; other engines refuse it until #271 |
| `yearweek` | `yearweek(d)` of a date: its ISO year times 100 plus its ISO week, the week subtracted in the years up to 0 (#328, `duckdb-yearweek`). Strict, between -587764053 and 588158053, and NULL for an infinite date and before 5877641-01-04 BC, where DuckDB raises (as `date_part` is NULL outside chrono's dates). Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `weekday` | `weekday(d)` is `dayofweek(d)`, `date_part('dow', d)`: modelled exactly, Sunday 0 (#328). | ✓ |
| Vectors | `list_cosine_similarity`, `list_cosine_distance`, `list_distance`, `list_inner_product` (also `list_dot_product`), `list_negative_inner_product` and `array_cross_product` of two lists of doubles ([#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)). Strict; raise where a list holds a NULL or the two differ in length (the cross product: are not of length 3). The similarity is at least `-1.0` and the cosine distance at least `+0.0`: NULL for empty lists, NaN for a zero vector or one with NaN or an infinity, so neither has an upper bound. The distance is not NULL and at least `+0.0`; the inner products and the cross product are not NULL (`duckdb-list-vectors`). The model has no fixed-size ARRAY, so DuckDB's `array_cosine_similarity`, `array_distance`, `array_inner_product`, … are read as the functions of lists. Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |
| `list_sum` | `list_sum(l)` of a list of integers: the sum of its values, NULLs skipped, NULL without any (#327). DuckDB's is a HUGEINT; the model's a BIGINT, which raises past its range, as `SUM` (`duckdb-list-sum`). Lean evaluates it. Of doubles it is refused. | ✓ on DuckDB; other engines refuse it until #271 |
| `list_extract`, `array_value` | `list_extract(l, i)`, `list_element` and `array_extract` of a list are `l[i]`, and `array_value(a, …)` is the list literal `[a, …]`: modelled exactly (#327), with their limits (a constant index, constant elements). | ✓ |
| `bit_count` | `bit_count(x)` of a BIGINT: the 1 bits of its 64-bit two's complement ([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)). Strict, not NULL, in [0, 64]. DuckDB counts the bits of the argument's own width, so narrower integers are refused. Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| `string_split` | `string_split(s, sep)` (also `str_split`): the pieces of `s` between the occurrences of `sep`, found left to right without overlapping, a list of strings ([#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808)). Its characters (code points) for `sep = ''`, and `['']` for `s = ''`. NULL for a NULL `s`, and `[s]` for a NULL `sep`, so not strict; not NULL otherwise. Lean evaluates it. | ✓ on DuckDB; other engines refuse it until #271 |
| Casts from VARCHAR | `varchar_bigint`, `varchar_double`, `varchar_boolean`, `varchar_date` and `varchar_timestamp` are `CAST(s AS …)` of a string: strict, raising on a string DuckDB rejects, and not NULL. Their `try_` rows are `TRY_CAST`: strict, never raising, NULL there (#806, `duckdb-cast-varchar`). Lean evaluates them on a subset (`SubstraitLean/VarcharCasts.lean`): numbers without `_`, hexadecimal or binary, ISO dates of the years 1 to 9999 and times to 23:59:59, and the strings DuckDB rejects for sure; elsewhere it refuses to print rows. | ✓ on DuckDB; other engines refuse them until #271 |
| `age` | `age(a, b)` is an INTERVAL of months, days and microseconds, which the model lacks; `age(ts)` reads the clock. Refused (#328). | Refused |
| `entropy` | `entropy(x)` of any type: the Shannon entropy, in bits, of the counts of the distinct values; `0.0` without values. Not NULL and at least `+0.0`. Lean does not evaluate it, so `substrait-check` refuses to print rows of a plan with it. | ✓ on DuckDB; other engines refuse it until #271 |

| Statistical aggregates | `product`, `kahan_sum` (also `fsum`, `sumkahan`), `favg`, `sem`, `mad`, `kurtosis`, `kurtosis_pop` and `skewness` of doubles, integers converted as DuckDB converts them (#326). NULL without values. `product`, `kahan_sum` and `favg` are not NULL over values; `sem` and `mad` are not NULL and at least `+0.0`. `kurtosis`, `kurtosis_pop` and `skewness` are NULL for few or equal values and raise on an infinity, NaN, or a value whose fourth (third) power overflows (`duckdb-moments`). `mad` of a DECIMAL or a temporal type is refused. `histogram` (a MAP) and `weighted_avg` (two arguments) are refused (`duckdb-statistical-aggregates`). Lean does not evaluate them. | ✓ on DuckDB; other engines refuse them until #271 |

## The Ibis frontend

What an Ibis expression means to `verify`.

`sverify.verify(expr)` compiles an Ibis expression with the vendored producer
(`sverify.ibis_substrait`), not with Ibis's SQL for some backend. A proof is
about the plan that producer writes, under `Rel.eval`. So the meaning of an
Ibis expression is the producer's, and it is the same whichever Ibis backend
the expression came from.

Where Ibis backends disagree (see
`catalogue/backend_semantics.py`), this table says which meaning
`verify` takes. `python/tests/test_ibis_semantics.py` runs each row through the
producer and checks Lean's evaluation against it.

| operation | meaning in `verify` | DataFusion | DuckDB | Polars |
|---|---|---|---|---|
| `a % b` (integers) | truncating: `-7 % 2 = -1` | same | same | floor (`+1`) |
| `a // b` (integers) | floor, exact in 64 bits: `-7 // 2 = -4` | same | same | same |
| `a % 0`, `a // 0` | error (division by zero) | error | conversion error | NULL |
| `s.length()` | code points: `'é'` is 1, `'🎉'` is 1 | same | same | bytes |
| `s.find(t)` | 0-based, −1 if absent, NULL for a NULL string | same | same | −1 for NULL |
| `s.substr(i, n)` | 0-based start | same | same | same |
| `s.like(p)` | `\` escapes the next character | same | no escape | no LIKE |
| `x.nunique()` | NULL is not a value | same | same | counts NULL |
| `v.round()` | half away from zero: `2.5 → 3` | same | same | half to even |
| `v.cast("int64")` (double) | truncates; NaN, ±inf and out-of-range values are an error | same (error) | rounds half to even | truncates |
| `v == 0.0` with `v = -0.0` | true: one zero (#89) | false (total order) | true | true |
| `x == ibis.null()` | `x IS NULL` (TRUE for NULL rows) | same | same | same |
| `ibis.row_number()` | 0-based | same | same | same |
| `order_by(...)` | NULLs last in both directions | same | same | same |
| window with `order_by`, no frame | the whole partition | same | same | same |
| 64-bit overflow of `+ - *` | an error at the declared width (#202); DataFusion wraps around, which an error allows | wraps | error | wraps |
| `v.max()` of doubles | NaN, the greatest double (#371, #697) | NaN | NaN | skips NaN |
| `ts.day_of_week.index()` | Monday = 0 | same | same | same |
| `s.upper()`, `s.lower()`, `re_search` | Rust's case mapping and `regex` classes; SQL engines raise on non-ASCII text (#70) | same | utf8proc, RE2 | same |

"Same" means the backend's Ibis result agrees with `verify`'s meaning on the
notebook's edge rows. A **refused** operation is outside what `verify` can
give a backend-independent meaning today.

Which Ibis backends implement this semantics fully: none of them on every
row. Ibis-on-DataFusion is closest (it differs on `-0.0 == 0.0` and on
`max` of NaN). To run a proved expression with exactly this meaning, run
the plan: `sverify.engines.run(con, plan, engine)` on DuckDB, Polars or
Spark ([the engines](stability.md#engines)), whose translations raise where
they would differ.

### Any row's value

`first()` and `last()` without `order_by`, and so `distinct(on=…)`, which
Ibis writes as `FIRST` (or `LAST`) of each other column, take any row's
value (#55). `verify` proves what holds for every row an engine may take,
and reports the result as not `deterministic` unless the grouping (`on`)
columns form a key
([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)). Each column is chosen on its own: `FIRST` skips NULLs column by column,
so `distinct(on="name")` may keep `a` from one row and `b` from another, and
a fact about every input row, such as `a <= b`, need not hold of the result.
`keep=None` keeps the groups of one row, but the report still calls it
not `deterministic`. The plan runs on DuckDB for now (#271).

### Parameters

An `ibis.param` has no value until the expression runs, so `verify` takes
one, as Ibis's `execute(params=...)` does: `sv.verify(expr, params={p: 5})`
replaces each parameter with a literal of its type before compiling (#58).
The report is then about the expression with those values, and says so
(`Report.notes`): a proof for `p = 5` says nothing about `p = 0`. A
parameter left unbound is refused. Proving a contract for every value of a
parameter, as an unknown value of its type, is planned (#354).

## How the model holds a plan

Choices of the Lean model that shape how a plan is represented and
evaluated. Where an entry names DataFusion, it records how that optional
engine differs ([the engines](stability.md#engines)).

* Positional schemas. Substrait field references are ordinals, so a
  schema is an arity, with a kind per column that the kind checker keeps
  (`Rel.kinds_sound` in `Kinds.lean`).
* Project appends, Emit narrows. This matches Substrait's `ProjectRel` +
  `RelCommon.emit`. Here `Emit` is its own node, and no rel carries an emit field.
* Bags as lists. `Rel.eval` returns a `List`, and plan equivalence is `List.Perm`.
  Several rewrites are stronger than that and hold as exact list equality.
* Semi joins and `DISTINCT` are their own operators. `Rel.semi` keeps the left
  rows with some (or, for anti joins, no) matching right row; `Rel.distinct` keeps
  the first occurrence of every row (NULLs equal, doubles by their codes as
  the reference reads them: one zero and one NaN). `DISTINCT` rows are a key (`Rel.keys`). DataFusion writes
  `DISTINCT` as an aggregate with one empty grouping, which its own consumer
  rejects; the parser reads it as "all columns".
* Aggregates have one grouping set. `Rel.aggregate` outputs one row per
  distinct grouping value (NULLs group together; doubles by their codes, so
  -0.0 and 0.0 are one group), or exactly one row without
  grouping expressions, even on an empty input. Measures skip NULLs; on no
  values `COUNT` is 0 and the rest are NULL. Integer `SUM` is exact (DataFusion
  wraps around; the reference raises outside 64 bits, checked while the job runs), double `SUM`/`AVG` are the correctly
  rounded exact sum and mean ([Of doubles](#of-doubles), D25), and `AVG` of integers is the `AVG` of their
  conversion to double. `MIN`/`MAX` of doubles compare by the
  codes, as DuckDB does; DataFusion's grouped version turns a group of +∞ into
  the largest finite double and skips NaN next to other values, so it is refused
  there. Contracts see `MIN`, `MAX`, an integer `AVG` and a decimal `AVG` within
  the values' bounds, measures over a group of a column that is never NULL as
  never NULL, and `MIN ≤ MAX` (#372). An `AVG` of doubles rounds, so it is some
  double.
  The grouping columns are a key of the result.
* Ill-typed calls evaluate to `null`. This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.
* Some operations are rewrites in the parser. `IN` lists become `OR`s of
  equalities; `COALESCE`, `NULLIF`, `GREATEST`, `LEAST` and `ABS` become
  conditionals; `RIGHT JOIN` becomes a `LEFT JOIN` with its sides swapped;
  `FULL OUTER JOIN` becomes the left join plus the anti join of the right side,
  padded with NULLs; `x IN (subquery)` in a filter becomes a semi join on `=`;
  `UNION` is `DISTINCT` of `UNION ALL`; `IS NOT DISTINCT FROM` becomes a
  conditional. The rewrites are trusted code, checked against DuckDB by
  `python/tests/test_rewrites.py` and `python/tests/test_relations.py`. (`ABS` of the smallest `BIGINT` fails in
  DataFusion; here it is reported as an overflow.)
* Overflow is an error at the declared width. `Rel.eval` computes exact
  integers, and [Safety.lean](../SubstraitLean/Safety.lean) reports every operation whose
  result may not fit its declared width (64 bits, or narrower integers). Where DataFusion fails instead (division, `POWER`, casts), the
  value in the model is `NULL`.
* Strings are Unicode scalar values. `substring`, `strpos`, `LIKE`, `btrim`, `||`,
  `character_length`, `repeat`, `reverse`, `replace`, `ascii` and `levenshtein` are
  computed exactly, by Rust's string functions: `python/tests/test_text.py` checks
  them against DuckDB where DuckDB computes them so, and Polars and DuckDB running
  Lean's plans everywhere; a `repeat` of more than 2³¹ - 1 bytes is an error. `UPPER`, `LOWER`,
  `ILIKE`, regular expressions, `md5` and `sha256` are black boxes (`opaque`): no proof
  depends on what they compute. Lean's evaluator handles only ASCII case, and evaluates
  regular expressions with RE2's leftmost-first matching ([Regex.lean](../SubstraitLean/Regex.lean))
  where RE2 and Rust agree, checked against DuckDB by `python/tests/test_regex.py`.
  `translate` is refused: DataFusion translates grapheme clusters. A pattern is an error
  (for `regexp_match`) or refused (for `regexp_extract` and `regexp_replace`) unless
  `Text.simpleRegex` accepts it, a conservative subset of Rust's and RE2's syntax that is
  tested to compile in both.
* Elementary functions follow Substrait, with errors outside their domains.
  `sqrt`, `exp`, `ln`, `log10`, `log2`, `logb`, the trigonometric functions and
  `atan2` are computed with C's libm ([Numeric.lean](../SubstraitLean/Numeric.lean)), and
  contracts treat each result as "some double". Outside a function's domain (`sqrt` of a
  negative, the logarithm of zero or a negative, `asin` and `acos` outside `[-1, 1]`,
  `atan2(0, 0)`, `logb` to a base that is not positive or is 1) the result is an error,
  Substrait's `on_domain_error` = ERROR when a plan omits the option; NaN is in every
  domain. Bitwise operations are exact in 64-bit two's complement, and a shift count
  outside 0–63, which Substrait leaves open, is an error too. Polars and the SQL of
  DuckDB raise where Lean reports a domain error; DataFusion returns NaN, ±∞ or a
  wrapped shift there, which an error allows. Spark runs `sqrt` and the bitwise
  operations (its other functions are Java's `StrictMath`); Snowflake runs `&`, `|` and
  `^` only (its shifts are not 64-bit, and its libm is not documented). Checked by
  `python/tests/test_math.py`.
* Timestamps are microseconds (UTC). `date_part` and `date_trunc` are computed
  exactly, checked against DuckDB and Python's calendar by `python/tests/test_time.py`,
  including at the ends of the nanosecond range; dates are in [Temporal](#temporal).
* Integer `//` from Ibis is exact. Ibis compiles it through doubles
  (`CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT)`), which is wrong beyond 2⁵³;
  `sverify` compiles it to integer division instead.

## Trusted assumptions

A theorem about `Rel.eval` holds for the model; what links it to a real run
is trusted: the size hypothesis (an override of Substrait,
[Overrides](#overrides)), the frontends, black boxes as DuckDB's functions,
the engines' match with their profiles, the printers and the parser, and
native `Float` for `pow`, `log` and the other libm functions (`+ − × ÷` are
exact since D31). [proofs.md, What is trusted](proofs.md#what-is-trusted)
states each, with its status.

## Where things are decided

| What | Where |
|---|---|
| Principles and defaults | [#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185): "Principles for the reference model", "Decided: what the reference does when a plan omits an option", "Decided (2026-11-02): no newly created NaNs" |
| Modulus, casts, `substring`, `-0.0`, lists, `avg` | [#209](https://github.com/AlexanderNenninger/substrait-lean/issues/209), "Decided" |
| Overflow and `SUM` | [#202](https://github.com/AlexanderNenninger/substrait-lean/issues/202), "Decided (2026-11-01)" |
| Engine tiers | [#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211) |
| DuckDB's findings, judged against this page | [`characterization/duckdb/facts/`](../characterization/duckdb/facts/) |
| Float aggregates as correctly rounded exact sums, two NULL equalities, the size hypothesis, lexical lambdas | [core-semantics.md](core-semantics.md#decisions): D25 to D28, [#922](https://github.com/AlexanderNenninger/substrait-lean/issues/922) |
| Statistical aggregates as correctly rounded exact moments | [core-semantics.md](core-semantics.md#d30-statistical-aggregates-are-correctly-rounded-exact-moments): D30, [#918](https://github.com/AlexanderNenninger/substrait-lean/issues/918) |
| The loose core and profiles as constraints (design) | [core-semantics.md](core-semantics.md), [#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444) |
