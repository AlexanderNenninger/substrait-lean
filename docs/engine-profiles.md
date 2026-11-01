# Engine profiles: the reference semantics and the engines

How a proof relates to the engines that run a plan. The design work lives in
epic [#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185)
(which supersedes the first design for #23), and the evidence for each engine
in [`characterization/`](../characterization/). This note sums up what was
decided there; where the two differ, #185 wins.

## The reference model

`verify` proves things about `Rel.eval`, the **reference semantics**. It is
not a model of any engine, DuckDB included. It is (#185, "Principles for the
reference model"):

1. **Substrait's semantics.** Each function means what its extension YAML
   says, including its options (`overflow`, `on_division_by_zero`,
   `division_type`, …). An option set in the plan is part of its meaning.
2. **The least surprising choice where Substrait leaves one open**, written
   down with its reason.
3. **Easy to emulate on every backend.** Types have their declared widths
   (`i8`…`i64` are fixed-width), and every choice is one that DuckDB,
   Polars, DataFusion, Spark and Snowflake can be made to follow with a shim
   (a guard, a cast, a `CASE`).
4. **Good for optimizations.** Filter pushdown, reordering, sharding and
   incremental maintenance stay provable.

The decided defaults for a plan that omits an option (#185, "Decided: …"):

* **Overflow** (`add`, `subtract`, `multiply`, `negate`, `abs`, …): ERROR,
  at the declared width. SILENT and SATURATE only when the plan asks.
* **Division by zero** (`divide`, `modulus`): ERROR. NULL only when the plan
  asks.
* **Errors mean "may raise"**, and rewrites are proved as refinements: an
  optimized plan may raise in fewer cases, but never answers differently and
  never raises where the original didn't.

An engine runs a plan **correctly** when, on every input, it gives
`Rel.eval`'s rows or fails.

## An engine profile is a diff

An engine's characterization records only where it differs from the
reference: which options it implements natively and which need a shim, its
settings (such as DuckDB's `error_on_division_by_zero`), the widths of its
accumulators, and its frontend quirks. Translating a plan for the engine
means applying that diff: writing each function in a form the engine
evaluates to the reference result, or refusing it where no shim exists.

DuckDB is the first engine characterized this way:
[`characterization/duckdb/FACTS.md`](../characterization/duckdb/FACTS.md)
judges DuckDB's own sqllogictests and the fuzzer's findings against
Substrait's definitions and options, not against ISO SQL or DuckDB. The plan
is to state each profile in Lean and prove the shims (`shim_correct` in
#185); engine fidelity itself stays tested, not proved.

## Engine tiers

From [#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211):

| Tier | Engines | Meaning |
|---|---|---|
| **1** | DuckDB | Characterized as a diff against the reference. Every reference behaviour is native, shimmed or refused, the shims are proved, and CI replays the engine's own tests plus fuzzing. In progress: until #185's profile work lands, DuckDB is Tier 1 in intent. |
| **2** | Polars, Spark, DataFusion | Run checked plans and are differentially tested against `Rel.eval` in CI, with known deviations documented. Not yet characterized or proved. Polars and Spark aim for Tier 1. |
| **3** | Snowflake | Aspirational: sverify writes the SQL and checks it on an emulator (fakesnow), never on a real account ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)). |

SQL strings are planned to go through Isthmus only, with DataFusion an
execution backend (#211).

## Profiles and shims in Lean (#185, first slice)

`SubstraitLean/Profile.lean` states the scalar part:

* An engine evaluation gives an **`Outcome`**, a value or an error.
* A **`Profile`** gives each function's outcome; `Expr.evalP` evaluates under
  one (strictly, left to right; a `CASE` takes one branch; a lambda runs on
  every element).
* **`Profile.reference`** raises exactly where `Safety.lean` reports an error,
  and `Expr.evalP_reference` proves that evaluating under it is `eval`,
  raising the first error `issues` reports. So the reference is one profile
  among others.
* **`Profile.duckdb s`** is the reference except where
  `characterization/duckdb/FACTS.md` records a difference. So far that is
  division and modulus by zero (R2–R5), which depend on the setting
  `error_on_division_by_zero` (on by default since 2.0).
* **`shimDuckDB s`** rewrites an expression into one DuckDB evaluates to the
  reference's outcome. Its guards are two functions of the model:
  `UnFn.raise` (always an error, `Issue.raised`; DuckDB's `error()`) and
  `UnFn.isNum` (written `x IS NOT NULL`). So a shimmed plan is an ordinary
  plan, written and run like any other. With the setting off, a division gets
  `CASE WHEN x IS NOT NULL AND y = 0 THEN error() ELSE x / y END`; `NULL / 0`
  is NULL in the reference. **`shimDuckDB_correct`** proves that the shimmed
  expression, under DuckDB's profile, has the reference's outcome: the same
  value, or an error.

Trusted: that `Profile.duckdb` matches DuckDB (to be checked by the fuzzer),
and that the SQL printer prints the shimmed plan faithfully (`isNum` as `IS
NOT NULL` included). Next: relations, the
fuzzer check, writing shimmed plans for the SQL printer, and the other rows of
the DuckDB diff.

## The translations today

Each engine reaches the reference through a **translation**, a function from
a plan to something the engine runs. Until the shims of #185 replace them,
these are hand-written and tested, not proved:

| engine | translation | where |
|---|---|---|
| DataFusion | `substrait-check --write-datafusion` | `Write.writeRel (df := true)` |
| Polars | `polars_engine` (LazyFrame) | Python |
| DuckDB, Snowflake, Spark | `sverify.sql.to_sql` with a `Dialect` | Python |

A translation compensates for its engine where it can (an exact `SUM`
through `DECIMAL(38,0)`, `canonical` doubles, explicit `NULLS FIRST/LAST`,
guards that raise) and refuses the plan where it cannot (`Unsupported`).
"Raise rather than differ" is the standard each one is tested against:
`Rel.eval` (`lean_rows`), another engine's rows, or a raised error. Guard
elimination (`SubstraitLean/Guards.lean`) is the part already proved in Lean.
