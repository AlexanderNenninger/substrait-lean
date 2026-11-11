---
name: query-semantics
description: Answer what sverify and each engine make of an example SQL query or Ibis expression, profile by profile - the strict reference that plans are verified under, the DuckDB, Polars and Spark engine profiles, and Substrait's own - with the route and class by which a verified plan reaches each engine, the characterization facts and upstream ledger entries behind them, and a probe that runs it. Use when asked "what does engine X do with this query", "does sverify verify/accept this", "do the engines agree on …", "is this query portable", "why is it refused on Polars", or to probe or compare a query across engines.
---

Answer from the repository's static sources first:
- `lookup.py` verifies the query under each profile (with `--table`) and collects the options it meets, each profile's choice rows, the engine facts and the upstream ledger entries.
- `probe.py` runs the query only when those don't settle the question.

Both live in `.claude/skills/query-semantics/`. The terms (reference, profile, option, choice, route, class, observation) are those of `docs/core-semantics.md`; read its Terminology and "Classes of an engine's functions" once.

## How to frame the answer

Answer per profile, never just "Lean vs engine":

- Profiles. The reference (`semantics="reference"`, strict: raises where engines disagree) is what plans are verified under by default. `semantics="duckdb"` verifies DuckDB's SQL as DuckDB computes it, `semantics="polars"` an Ibis expression as Polars computes it, `semantics="spark"` one as Spark 4.3.0 computes it under ANSI mode (`engines/spark/Sverify/Spark/Profile.lean`, `Engine.spark_sound`; until #1288 the report is the reference's with ±inf allowed, labelled `"reference"` with a `ProfilePendingWarning`, and runs on Spark through its translation), and `semantics="substrait"` under Substrait's own loose semantics. Say which of these verify the query.
- Preconditions. Name what `sv.verify` inferred (`requires … (inferred)`, `assumes: … stays finite`). `Report.run` checks them on the data before a routed run.
- Route and class (`sverify.routes.choose`, D13, D15), per engine with a profile (DuckDB, Polars, Spark): route `native`, `translated`, `transfer` or `recheck`, or refused with the reason; class `exact`, `observed`, `shim` or `refused`, the worst over the options the proof depends on. The tables are in [docs/guide.md](../../../docs/guide.md#routes-classes-and-profiles). An `observed` option needs a postcondition whose observation it refines (`sv.equivalent(...)`, D11, D18), or the row's shim; say which. What a rerun must reproduce is a second observation (D20, #613).
- Facts. Cite the engine facts the class rests on, with evidence level and status, and any ledger entry.
- Engines without a profile run the writer's shims, tested only; mark their results as such. Snowflake's is planned (#851). Engines list: [docs/stability.md](../../../docs/stability.md#engines).

## Prerequisites

`uv`, and a built `substrait-check`. In a worktree without a Lean build, point sverify at a checker of the same commit:

```bash
export SVERIFY_CHECKER=/path/to/substrait-lean/.lake/build/bin/substrait-check
```

Otherwise build it (`lake build substrait-check`; check the load first, CLAUDE.md). `--spark` needs a JVM (Java 17 or 21).

## Step 1: lookup (always first)

```bash
uv run --project python python .claude/skills/query-semantics/lookup.py \
    --sql 'SELECT a, CASE WHEN b <> 0 THEN a / b END AS q FROM r' --table r 'a:int64,b:int64'
```

```bash
uv run --project python python .claude/skills/query-semantics/lookup.py \
    --sql 'SELECT k, sum(v) AS s FROM m GROUP BY k' --table m 'k:string,v:float64' \
    --requires m '_.v.between(-1e17, 1e17)' --requires m 'sv.max_rows(10**6)' \
    --ensures 'sv.equivalent(floats=sv.within(abs=1e-6))'
```

- `--sql` is DuckDB's SQL. `--table NAME COLS` (Ibis type names) turns on the profiles block; without it the options come from the SQL's syntax alone.
- `--ibis` code sees the `--table` tables, or one table `t` with `x y` (int64), `v` (float64), `s` (string), `ts` (timestamp), `d` (date) and `b` (boolean). It prints where the vendored producer translates each Ibis operation.
- `--requires TABLE EXPR` and `--ensures EXPR` take Ibis expressions over `_` and sverify's conditions (`sv.max_rows`, `sv.unique`, `sv.equivalent`).
- `--word nan` adds search words; `--prose` adds the older catalogue prose.

It prints:

| section | source | answers |
|---|---|---|
| profiles | `sv.verify(semantics=…)`, `routes.choose` | verified under which profile, preconditions inferred, issues, route and class per engine |
| options | `substrait-check --functions`, the plan's `depends` | the (group, option) pairs the query meets |
| choices | `substrait-check --options` | each profile's row: allowed behaviours, default, class, `q`, shim, rerun, facts |
| facts | `characterization/<engine>/facts/*.json` | the facts for those options (by `rows` where a fact has them, else `options`) and functions, with evidence (`docs` < `source` < `engine_test` < `probe` < `fuzz` < `proof`) and status |
| ledger | `upstream/bugs/*.json` | engine bugs and spec gaps (`ST-*`, `kind: spec-gap`) linked to those facts or naming the functions |
| parser | `frontend/Sverify/Frontend/Parse.lean` | how the Substrait function is read, or refused |
| prose (`--prose`) | `catalogue/pitfalls.toml`, `features.toml`, `backend_semantics.py`, engine module docstrings, `status.json` | older notes, from before the facts; the facts win where they disagree |

Then read the cited facts and lines before answering: the lookup finds candidates. A fact's `description`, `reference` and `provenance` say what the engine does, what the reference does, and how that is known. `python -m sverify_dev.facts --coverage <engine>` (from `python/`) lists the checklist items and choice-table rows that have no fact yet.

## Step 2: probe (only if the static sources don't settle it)

Run from `python/`:

```bash
cd python
uv run python ../.claude/skills/query-semantics/probe.py \
    --table n 'x:int64,s:string' '[(2, "a"), (None, "b"), (1, None), (3, "c")]' \
    --sql 'SELECT x, s FROM n ORDER BY x DESC LIMIT 3' \
    --ibis 'n.order_by(ibis.desc("x")).limit(3)'
```

```bash
cd python
uv run python ../.claude/skills/query-semantics/probe.py --catalogue win-top-n-per-group
```

Inputs: `--table NAME COLS ROWS` (repeatable; `ROWS` a Python list of tuples, timestamps and dates as ISO strings, doubles as `"nan"`, `"inf"`, `"-inf"`), `--sql`, `--ibis` (an expression, or statements that assign `q`), `--catalogue ID`, `--requires`/`--ensures` as in the lookup, `--spark`.

Output:
1. Environment: package versions, each profile's fact versions against the installed engine (D14), the DuckDB settings the facts depend on (#598), and how Polars runs.
2. Frontends: the lift's and the Ibis producer's plans, the checker's verdict under the reference, the `Rel`, and `Rel.eval` on the rows.
3. Profiles: as in the lookup.
4. Engines on the written plan: DuckDB and Polars, each `= Rel.eval`, `DIFFERS`, `raises` or `refused`, with the route and class under it; Spark with `--spark`, which the probe runs without a route; Snowflake as SQL text only.
5. Native: the SQL as written on DuckDB and Polars SQL (and Spark), and the Ibis expression on Ibis's backends. No route applies; this is what the engine itself does.

Polars runs on its streaming engine, as sverify does (#605), with sverify's flags for plans and Polars's defaults for native queries. Rows compare as bags, or in order where a sort reaches the result; doubles to 6 decimals, times as µs, dates as days.

## Gotchas

- Give tables of at least 2 rows. Polars rewrites arithmetic with literals differently on a one-row frame (PL-3, `polars-zero-sign`), so a one-row probe can hide a difference. The probe warns.
- A difference under a window or `LIMIT` may be allowed. Where sort keys tie, the reference leaves `tie_order` open; an engine that orders ties differently refines it up to the observation "ties permuted". Check whether the differing rows tie.
- `raises` on an engine running the plan is by design where the reference raises: division by zero, i64 overflow, a double overflowing to ±∞ (#575). `Report.issues` and `Safety.lean` say where that can happen; a guard (`CASE WHEN b <> 0`) or a precondition removes it.
- A float `SUM` or `AVG` verifies only once the inputs are bounded and NaN-free (`between` gives both, with `max_rows`); otherwise the report says `may fail: domain error`. Its order is the open option `sum_order`. Where an engine's row bounds the difference per plan (Polars streaming), the route checks that bound against the postcondition's tolerance (`sv.equivalent(floats=sv.within(...))`), and a rerun may differ in the last bits (D20).
- Polars SQL and the Polars expression API differ, and Ibis is not SQL (`row_number()` is 0-based, `== ibis.null()` becomes `IS NULL`). Give both `--sql` and `--ibis` when the question is about Ibis. `semantics="polars"` checks Ibis expressions only: integer `//` and `%` floor and state `division_type: FLOOR`, which Polars runs natively and DuckDB refuses.
- A run on a DuckDB or Polars version other than the profile's warns, another major version refuses (D14). A DuckDB setting a choice depends on (`default_null_order`, `integer_division`, …) refuses a routed run (#598).
- `catalogue/status.json` is a snapshot. Re-probe one query from `python/` with `uv run python -m sverify_dev.catalogue <query-id>`.

## Troubleshooting

- `this checker has no Profile.polars to check under yet`: the checker predates `Profile.polars` (`engines/polars/Sverify/Polars/Profile.lean`); rebuild it. The reference's route still applies.
- `CheckerVersionError` or `FileNotFoundError` for `_bin/substrait-check`: set `SVERIFY_CHECKER` (above).
- `memtable() got an unexpected keyword argument 'name'`: the probe uses `ibis.memtable` for native Ibis runs; keep it that way.
- `Relations no longer have fetchone()`: DuckDB 2.0; use `.fetchall()` or `.fetch_arrow_table()`.
- `ArrowTypeError: object of type <class 'str'> cannot be converted to int`: a row value doesn't match its column type.
