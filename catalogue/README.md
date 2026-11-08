# Query catalogue

Real analytical queries, collected from public sources, to ground a
practitioner-first specification of query plans. Each query records what a
practitioner wants, where it comes from, what relational machinery it needs,
and how far this repository gets with it today: whether `substrait-check`
verifies it, and which engines run it.

* [`INDEX.md`](INDEX.md): every query with its status (generated).
* [`FINDINGS.md`](FINDINGS.md): feature frequency and gaps ranked by the
  queries they block (generated), with a dated note on the catalogue.

## Contents

| File | Contents |
|---|---|
| `queries/*.toml` | The queries, one file per suite: `tpch` (all 22), `tpcds` (8), `ssb` (4), `clickbench` (7), `job` (3), `h2o` (10), and practitioner idioms in `windows`, `timeseries`, `product`, `modelling`, `iot` (12) and `finance` (18) |
| `features.toml` | The vocabulary of operators and features, with Lean's support for each (`yes`, `partial`, `no`), found by probing |
| `pitfalls.toml` | Cross-engine correctness pitfalls, each linked to the entries of [backend_semantics.py](backend_semantics.py), a marimo app that asks one question of every engine |
| `schemas.toml` | The tables of each dataset (only the columns the queries use), with value pools for synthetic data |
| `status.json` | What the probes found for every query (generated) |
| `contracts.toml` | The contract census: 49 contracts on aggregates of doubles (a bound, a HAVING threshold, a top-N, a tolerance, a window) and controls, over `schemas.toml`'s datasets |
| `contracts.json` | How each census contract reaches DuckDB, Polars, Spark and Snowflake: proved, tested (with the cause) or refused (with the reason), checked by `tests/test_contract_census.py` |
| `INDEX.md`, `FINDINGS.md` tables | Generated from the above, on `main` only (see below) |

A query looks like this:

```toml
[[query]]
id = "win-dedup-latest"
title = "Latest row per key (dedup)"
intent = "Keep only the most recent update of each customer."
domain = "generic"
source = { name = "dbt-utils deduplicate macro", url = "https://github.com/…/deduplicate.sql", licence = "Apache-2.0" }
features = ["row_number", "dedup_latest", "qualify", "filter"]
pitfalls = ["tie_order: two updates with the same updated_at: …"]
ibis = '''
w = ibis.window(group_by="customer_id", order_by=ibis.desc("updated_at"))
q = customer_updates.mutate(rn=ibis.row_number().over(w)).filter(_.rn == 0).drop("rn")
'''
```

* `ibis` is Python that binds `q`; the dataset's tables, `ibis`, `_`, `sv`
  (`sverify`) and `D` (a DATE literal, see below) are in scope. Where Ibis
  cannot express a query (ROLLUP, recursion, time zones, frames ending before
  the current row) it is `sql` (DuckDB's SQL) instead, with a note why.
* `features` are those of the formulation given; `rewrites` lists features of
  the original query the formulation rewrote away (`"correlated_subquery ->
  join with the average per part"`), so the frequency counts see the original.
* `pitfalls` are `tag: what it means here`, with tags from `pitfalls.toml`.
* `requires` and `ensures` are the query's **contract**: Python expressions in
  `ibis`'s scope for `sv.verify`'s preconditions (a mapping from table name to
  conditions) and postconditions (a list). Where the benchmark's
  specification gives ranges, keys and NOT NULL columns, the preconditions
  state them; otherwise they are plausible choices, written down. A query
  has both or neither.

A dataset in `schemas.toml` can list `keys` (columns of distinct values in
the synthetic data, never NULL), `not_null` and `rows` (a table's number of
rows, for a table of fixed size such as TPC-H's 25 nations), so that the
synthetic tables meet the contracts' preconditions.

### Verified SQL on DuckDB (#229)

For a query with a contract, the probe records `contract` (whether `verify`
proves it, whether the plan is `guard_free`, the preconditions `verify`
inferred besides the stated ones, and whether the synthetic tables meet the
preconditions) and `verified_sql.duckdb`. It is `yes` when every
postcondition is proved, no window's rows depend on how ties are broken
(`deterministic`: `Rel.window_deterministic`, `window_orderFree`), the
synthetic tables meet the preconditions, and DuckDB gives the reference's rows
on them. (`proved` additionally rules out runtime errors.) Two theorems in
`core/Sverify/Core/Profile.lean` then say what DuckDB does on *every* database
that meets the preconditions:

* `Rel.duckdb_shim_sound`: the plan, shimmed for DuckDB, gives `Rel.eval`'s
  rows unless one of its expressions raises (partial correctness). So DuckDB
  returns the rows the contract is proved about, or an error, never other
  rows.
* `Rel.duckdb_sound`, for a `guard_free` plan: no expression raises, so it
  always returns them (except for an integer `SUM` leaving 64 bits, which
  keeps its runtime check; bounding sums needs row counts, #219).

Trusted: that `Profile.duckdb` is DuckDB's, and the SQL printer.

## Sources and licences

Every query carries its source URL and licence. Benchmark intents are
paraphrased; the expressions are our own, with the benchmarks' qualification
parameters. TPC-H and TPC-DS are under the TPC EULA; ClickBench is CC BY-NC-SA
4.0 and the Join Order Benchmark states no licence, so only their intent is
used; H2O db-benchmark is MPL-2.0; dbt-utils, dbt docs and Ibis are
Apache-2.0; pandas BSD-3-Clause; Polars and DuckDB docs MIT; PostgreSQL docs
under the PostgreSQL licence. Blog posts and vendor tutorials without a licence
are paraphrased only, never quoted.

## Probing

```bash
cd python
uv run python -m sverify_dev.catalogue                 # validate the TOML
uv run python -m sverify_dev.catalogue tpch win-dedup-latest   # probe a suite or query
uv run python -m sverify_dev.catalogue --write         # probe all; rewrite status.json
uv run python -m sverify_dev.catalogue --write-tables  # rewrite INDEX.md and FINDINGS.md's tables from status.json
uv run python -m sverify_dev.contract_census --write --table  # rerun the census; rewrite contracts.json and print its table
```

A probe compiles the query as `sverify` compiles everything (an Ibis
expression through `sverify`'s vendored producer, SQL through its lift, then
`substrait-check`) and runs it on DuckDB itself (`native`: Ibis's own DuckDB
SQL for an expression) over small seeded synthetic tables. When the checker
accepts the plan it runs Lean's written plan (`substrait-check --write`) on
Polars and DuckDB and compares their rows with DuckDB's own, and writes
Snowflake SQL (parsed with sqlglot, not run). Where the plan has a FETCH or a
window, ties in the synthetic data make the native choice of rows
legitimately differ, so there Polars and DuckDB are compared with each other
only. Where a pitfall of the query makes DuckDB's own rows rightly differ
(`NATIVE_DIFFERS` in `sverify_dev/catalogue.py`: `degenerate_statistic`,
`null_at_extreme`, `duration_vs_interval`, `tie_order`), rows that differ from
them are compared with Lean's own (`Rel.eval` of the plan over the same
tables) instead, and agree as `runs (Lean's rows: <pitfalls>)`. A query on a
dataset with DECIMAL columns that fails is probed again with DOUBLE in their
place (`as_double`), to separate DECIMAL from the other gaps.

`tests/test_catalogue.py` (part of `poe test`) re-probes every query and fails
when a recorded status no longer holds, and checks the annotations against the
probes: no verified query may need a feature marked `no`, and every failure
message must point at a feature the query lists as not fully supported. After
a change in coverage, run `--write` and review the diff of `status.json`.

`INDEX.md` and the tables in `FINDINGS.md` are not committed on feature
branches: commit `status.json` and the TOML, and leave the generated tables
to the `Generated files` workflow
([`.github/workflows/generated.yml`](../.github/workflows/generated.yml)),
which runs `--write-tables` after every push to `main` and pushes the result.
Run `--write-tables` locally to look at them, then `git checkout` them again.

Date literals are written `D("1994-01-01")`, a cast of a string. Through
Ibis's DataFusion SQL, `ibis.date("…")` compiled to `DATE_TRUNC('DAY', '…')`,
which the checker refuses; `sverify`'s own producer handles both.
