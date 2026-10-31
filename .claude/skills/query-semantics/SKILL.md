---
name: query-semantics
description: Answer how sverify's frontends (DataFusion's SQL producer, the vendored Ibis producer, Isthmus) and backends (DuckDB, Polars, DataFusion, Spark, Snowflake) handle an example SQL query or Ibis expression, compared with the Lean model (Rel.eval). Use when asked "what does engine X do with this query", "does Lean accept/model this", "do the engines agree on …", "is this query portable", or to probe or compare a query across backends.
---

Answer from the repository's static sources first:
- `lookup.py` collects what the docs, notebooks, catalogue and code already say about the query's constructs.
- `probe.py` runs the query only when those don't settle the question.

Both scripts live in `.claude/skills/query-semantics/`. Paths below are relative to the repository root unless a command `cd`s to `python/`.

## Prerequisites

`uv` and the Lean toolchain (`elan`; if `lake` is not found, `export PATH=$HOME/.elan/bin:$PATH`). The probe needs `substrait-check`; build it once:

```bash
lake build substrait-check
```

`--spark` needs a JVM (Java 17 or 21; `java -version`). Isthmus is used only in a checkout that has `sverify.engine.isthmus_json` (PR #92), with `$SVERIFY_ISTHMUS` set.

## Step 1: static lookup (always first)

```bash
uv run --project python python .claude/skills/query-semantics/lookup.py \
    --sql 'SELECT x, x NOT IN (2, NULL) AS ni, a / b AS q FROM n ORDER BY x DESC LIMIT 2'
```

```bash
uv run --project python python .claude/skills/query-semantics/lookup.py \
    --ibis 't.select("x", r=ibis.row_number().over(order_by="x"), q=t.x // t.y)'
```

- `--sql` is parsed as Postgres by sqlglot.
- `--ibis` code sees one table `t` with columns `x y` (int64), `v` (float64), `s` (string), `ts` (timestamp), `d` (date) and `b` (boolean). It prints Ibis's SQL, then where the vendored producer translates each Ibis operation.
- `--word nan --word collation` adds search words.

It prints, per source:

| section | source | answers |
|---|---|---|
| features | `catalogue/features.toml` | is the construct in the Lean model (`yes`/`partial`/`no`) |
| pitfalls | `catalogue/pitfalls.toml` | what each engine does, plus DataFusion quirk ids |
| nb15 | `notebooks/15_backend_semantics.py` (`E(...)` entries) | per engine, Ibis backend, standard SQL and Snowflake; `picks` is the Lean model's answer |
| nb14 | `notebooks/14_datafusion_semantics.py` (`Q(...)` entries) | DataFusion quirks, tagged agree/handled/GAP |
| parser | `SubstraitLean/Parse.lean` | how Lean reads the Substrait function, or that it refuses it |
| backends | docstrings of `python/src/sverify/sql/{duckdb,snowflake,spark,core}.py` and `polars_engine.py` | how each backend is made to give Lean's value, and the divergences it works around |
| catalogue | `catalogue/status.json` | real queries with the same features: verified? which engines run them? |
| producer | `python/src/sverify/ibis_substrait/__init__.py` | (`--ibis`) the translation of each Ibis operation |

Then **read the cited lines** before answering: the lookup only finds candidates. For a construct none of these cover, grep the sources yourself. Throws in `Parse.lean` and `Unsupported(` in `python/src/sverify` give the exact refusal. The README's sections on the producer and engines, and `catalogue/FINDINGS.md` ("Why engines refuse verified queries", "What each engine needs"), are the prose behind these.

Answer with one line per frontend and per backend:
- Frontends: produces a plan? Lean accepts or refuses it, and why?
- Backends running Lean's plan: same rows as `Rel.eval`, raises by design, or refused (translation `Unsupported`)?
- Native: what the engine makes of the original SQL or Ibis code on its own, and whether that is the model's answer.

Say which source each line rests on.

## Step 2: probe (only if the static sources don't determine it)

Run from `python/`:

```bash
cd python
uv run python ../.claude/skills/query-semantics/probe.py \
    --table n 'x:int64,s:string' '[(1, "a"), (2, None), (None, "c")]' \
    --sql 'SELECT x, x IN (1, NULL) AS i, x NOT IN (2, NULL) AS ni FROM n' \
    --ibis 't.select("x", i=t.x.isin([1, None]), ni=t.x.notin([2, None]))'
```

```bash
cd python
uv run python ../.claude/skills/query-semantics/probe.py \
    --table r 'a:int64,b:int64,v:float64,ts:timestamp' \
    '[(7, 2, 1.5, "2024-01-01 10:00:00"), (-7, 2, None, None), (None, 3, "nan", "2024-03-01 00:00:00")]' \
    --sql 'SELECT a / b AS q, a % b AS m, v * 3 AS w, ts FROM r ORDER BY a DESC' --spark
```

```bash
cd python
uv run python ../.claude/skills/query-semantics/probe.py --catalogue win-top-n-per-group
```

Inputs:
- `--table NAME COLS ROWS` (repeatable): `COLS` takes Ibis type names. `ROWS` is a Python literal list of tuples; timestamps and dates may be ISO strings, and doubles `"nan"`, `"inf"` or `"-inf"`.
- `--ibis`: an expression over the tables (`t` is the first table), or statements that assign `q`.
- `--catalogue ID`: a catalogue query with its synthetic tables.

Output, in four blocks:
1. **Frontends.** Each producer's plan, the checker's verdict, Lean's `Rel`, and `Rel.eval` on the given rows.
2. **Backends on Lean's written plan.** DuckDB, Polars, DataFusion (and Spark with `--spark`), each shown as `= Lean`, `DIFFERS from Lean`, `raises (…)` or `refused`. Snowflake is SQL text only, never run.
3. **Native SQL.** The query as written, on DataFusion, DuckDB, Polars SQL (and Spark).
4. **Native Ibis.** The expression on Ibis's DuckDB, Polars and DataFusion backends.

Rows compare as bags, or in order when an ORDER BY reaches the result. Doubles compare to 6 decimals, times as µs since the epoch, dates as days.

## Gotchas

- **A difference under a window or FETCH may be legitimate.** Where sort keys tie, engines may number, pair or pick rows differently from `Rel.eval`'s stable order. The probe prints a note; check whether the differing rows tie (pitfall `tie_order`, notebook 14 O2/O3/O5). In `win-top-n-per-group`, DataFusion "differs" only on two products tied at 85.
- **`raises` on a backend is by design, not a bug.** For division by zero, i64 overflow or a bad cast, Lean's `Rel.eval` value is NULL. The engines running Lean's plan raise instead (`sverify: division by zero`); `SubstraitLean/Safety.lean` and the contract checks say when that can happen. Natively, DuckDB and Polars SQL give `inf`, and DataFusion and Spark raise.
- **Polars SQL and the Polars expression API differ.** `x IN (1, NULL)` follows SQL in `pl.SQLContext`, but notebook 15 N2 shows `pl.col('x').is_in([1, None])` ignoring the NULL. The probe runs Polars SQL; for the expression API, read the `polars:` field of the notebook 15 entry.
- **Ibis is not SQL.** Notebook 15's "leaky" entries mean different things per Ibis backend: `row_number()` is 0-based, `== ibis.null()` becomes `IS NULL`, and the default window frame is the whole partition. Give both `--sql` and `--ibis` when the question is about Ibis.
- **Snowflake is never executed.** Its SQL is generated and (in the catalogue) parsed with sqlglot only. It refuses sorts, FETCH and windows over named tables (no row order) unless `tie_free=True`, and so does Spark for windows.
- **Native DataFusion can be wrong** where Lean refuses. For example, `NOT IN (subquery)` with a NULL returns rows (quirk N3); the parser refuses that plan, so nothing is proved.
- **`catalogue/status.json` is a snapshot.** If the checker or producers changed on your branch, re-probe the query from `python/` with `uv run python -m sverify.catalogue <query-id>`; `--write` re-probes everything and rewrites `status.json`.
- **Notebook entries are static prose plus code.** The `why`, `std`, `snowflake` and `picks` fields are written answers. The row tables in the notebook are computed when it runs, so for actual rows, run the probe (or the notebook).

## Troubleshooting

- `memtable() got an unexpected keyword argument 'name'`, or `Parser Error: syntax error at or near "EXISTS"` from Ibis's DuckDB `create_table`: the pinned Ibis can't create tables from Arrow on DuckDB. The probe uses `ibis.memtable` for native Ibis runs; keep it that way.
- `'pyarrow.lib.RecordBatchReader' object has no attribute 'columns'`: DuckDB's `.arrow()` returns a reader in this version; use `.fetch_arrow_table()`.
- `ArrowTypeError: object of type <class 'str'> cannot be converted to int`: a row value doesn't match its column type. Timestamps and dates must be ISO strings in timestamp/date columns.
- `isthmus  not in this checkout (PR #92)`: expected on branches without the Isthmus producer.
