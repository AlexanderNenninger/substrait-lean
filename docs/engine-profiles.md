# Engine profiles: the reference semantics and the engines

Design note for #23 (engine profiles), #24 (DataFusion translation) and #71
(Ibis semantics). It says what a proof is about, where engine behaviour lives
today, and the order in which to move it.

## The claim

`verify` proves things about `Rel.eval`, the **reference semantics**: exact
integers, one zero and one NaN, NULLs last, Kleene logic, strings as Unicode
scalar values, black boxes (`UPPER`, `LOWER`, regular expressions) meaning
Rust's functions. An engine runs a plan **correctly** when, on every input, it
either gives `Rel.eval`'s rows or fails.

Each engine reaches that through a **translation**: a function from a plan to
something the engine runs.

| engine | translation | where |
|---|---|---|
| DataFusion | `substrait-check --write-datafusion` | `Write.writeRel (df := true)` |
| Polars | `polars_engine` (LazyFrame) | Python |
| DuckDB, Snowflake, Spark | `sverify.sql.to_sql` with a `Dialect` | Python |

A translation compensates for its engine where it can (an exact `SUM`
through `DECIMAL(38,0)`, `canonical` doubles, explicit `NULLS FIRST/LAST`,
guards that raise) and refuses the plan where it cannot (`Unsupported`).
"Raise rather than differ" is the standard every translation is tested
against: `Rel.eval` (`lean_rows`), DataFusion's rows, or a raised error.

## What a run-time issue is

`Safety.lean` reports what can go wrong at run time: errors (`divByZero`,
`overflow`, `badCast`, `negExponent`, `badRegex`) and silent wrap-around
(`wraps`, `sumWraps`). Which operations fail and which wrap is **DataFusion's**
behaviour, and so is the evaluation strategy the soundness proof assumes:

* `Rel.loose`: DataFusion may evaluate a projection's or a join condition's
  expressions on rows a filter later removes (filter pushdown), so issues are
  computed over the loosened plan;
* a boolean `CASE` and `COALESCE` are evaluated eagerly (quirks E4, E5);
* `-0.0` and `0.0` are one group (since #89), as on every engine but raw
  DataFusion, whose results `canonical` fixes.

The parser also holds DataFusion-specific choices: its `DISTINCT` encoding
(one empty grouping), negative `substring` lengths, refusing `MIN`/`MAX` of
doubles; and the trusted rules `Text.simpleRegex` (what Rust's `regex`
compiles) and `Time.nsMin`/`nsMax` (where `date_trunc` overflows).

So today a report says what happens **on DataFusion**. On Polars an integer
overflow raises (Polars checks), so a `wraps` warning there is an error; on
the SQL translations every issue is an error, because the guards raise.

## Design

### Lean: `Engine`

```lean
structure Engine where
  name : String
  /-- How the engine handles an issue: fail, wrap around, or not at all
  (the translation guards it). -/
  outcome : Issue → Outcome          -- .error | .wraps | .none
  /-- May the engine evaluate expressions on rows a filter removes? -/
  pushesFilters : Bool
  /-- Does it evaluate both branches of a boolean CASE / of COALESCE? -/
  eagerCase : Bool
  eagerCoalesce : Bool
  /-- Plans the engine (or its translation) cannot run. -/
  refuses : Rel → Option String

def Engine.datafusion : Engine := …   -- today's behaviour, exactly
def Engine.polars : Engine := …       -- wraps ↦ error
def Engine.guarded : Engine := …      -- the SQL translations: every issue an error
```

* `Rel.mayIssues (E : Engine)` and `Rel.mayIssues_sound (E)`: `Rel.loose`
  only when `E.pushesFilters`; `Expr.issues` follows `E.eagerCase` and
  `E.eagerCoalesce`; each issue is classified by `E.outcome`.
* `Rel.eval` does not change. The engine never enters the reference
  semantics, only the issue analysis and the refusals.
* `Engine.datafusion` reproduces today's reports exactly: the goldens and
  the Python tests must not change in the step that introduces it.

### The parser keeps only Substrait

DataFusion's encodings move to a DataFusion **frontend** (`Parse/DataFusion`):
reading `DISTINCT` as one empty grouping is a fact about DataFusion's
producer, not about Substrait. Refusals that are about what an engine runs
(`MIN`/`MAX` of doubles, negative substring lengths) become `Engine.refuses`.

### Translations

A translation for engine `E` is correct if `E` runs `T p` to `Rel.eval p` or
an error. Where the engine model is precise enough (guards, range checks),
prove it in Lean, as `Guards.lean` does for guard elimination; elsewhere,
differential tests (`tests/test_sql.py`, `test_polars.py`,
`test_datafusion_quirks.py`). `--write-datafusion` (#24) is the first
translation written in Lean; it does not parse back to the same `Rel`, so the
round-trip check covers `--write` only.

### Python

* Each backend declares its profile: `ENGINE_PROFILES = {"datafusion": …,
  "polars": …, "duckdb": "guarded", "snowflake": "guarded", "spark":
  "guarded"}`.
* `sv.verify(..., engine="polars")` passes `--engine polars` to the checker;
  `Report.errors`/`warnings` are that engine's. The default stays
  `"datafusion"`.

### Ibis (#71)

An Ibis expression means what `sverify.ibis_substrait` (the vendored producer)
writes, not what Ibis-on-DataFusion computes: since #45 Ibis expressions no
longer go through DataFusion's SQL. Where Ibis backends disagree (chapter 15
of the notebook tour), the producer's choice is the meaning, and it is
documented per operation in `docs/ibis-semantics.md` with a test that runs
the operation through the producer and Lean. An operation the producer cannot
give a backend-independent meaning is refused.

## Order of work

1. Translations that compensate instead of refusing: #64, #65, #70, #24
   (done in their PRs).
2. Ibis semantics table and tests (#71); no Lean change.
3. After the soundness fixes (#17–#20) land in `Safety.lean`, `Parse.lean` and
   `Value.lean`: introduce `Engine` with `Engine.datafusion` only, threading
   it through `Safety.lean` and `Contracts.lean`. No behaviour change.
4. Move the DataFusion encodings out of the parser into a frontend, and the
   engine refusals into `Engine.refuses`. No behaviour change.
5. `Engine.polars` and `Engine.guarded`, `--engine`, and
   `sv.verify(..., engine=...)`.
