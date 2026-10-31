# Query catalogue

Real analytical queries, collected from public sources, to ground a
practitioner-first specification of query plans. Each query records what a
practitioner wants, where it comes from, what relational machinery it needs,
and how far this repository gets with it today: whether `substrait-check`
verifies it, and which engines run it.

* [`INDEX.md`](INDEX.md): every query with its status (generated).
* [`FINDINGS.md`](FINDINGS.md): feature frequency, gaps ranked by the queries
  they block, and recommendations for the specification.

## Contents

| File | Contents |
|---|---|
| `queries/*.toml` | The queries, one file per suite: `tpch` (all 22), `tpcds` (8), `ssb` (4), `clickbench` (7), `job` (3), `h2o` (10), and practitioner idioms in `windows`, `timeseries`, `product`, `modelling`, `iot` (12) and `finance` (18) |
| `features.toml` | The vocabulary of operators and features, with Lean's support for each (`yes`, `partial`, `no`), found by probing |
| `pitfalls.toml` | Cross-engine correctness pitfalls, each linked to the DataFusion quirks of [chapter 14 of the tour](../notebooks/14_datafusion_semantics.py) |
| `schemas.toml` | The tables of each dataset (only the columns the queries use), with value pools for synthetic data |
| `status.json` | What the probes found for every query (generated) |
| `INDEX.md`, `FINDINGS.md` tables | Generated from the above |

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
  the current row) it is DataFusion `sql` instead, with a note why.
* `features` are those of the formulation given; `rewrites` lists features of
  the original query the formulation rewrote away (`"correlated_subquery ->
  join with the average per part"`), so the frequency counts see the original.
* `pitfalls` are `tag: what it means here`, with tags from `pitfalls.toml`.

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
uv run python -m sverify.catalogue                 # validate the TOML
uv run python -m sverify.catalogue tpch win-dedup-latest   # probe a suite or query
uv run python -m sverify.catalogue --write         # probe all; rewrite status.json, INDEX.md, FINDINGS.md tables
```

A probe compiles the query as `sverify` compiles everything (an Ibis
expression through `sverify`'s vendored producer, SQL through DataFusion's,
then `substrait-check`) and runs it on DataFusion (Ibis's own SQL for an
expression) over small seeded synthetic tables. When the checker accepts the
plan it runs Lean's written plan (`substrait-check --write`) on Polars and
DuckDB and compares their rows with DataFusion's, and writes Snowflake SQL
(parsed with sqlglot, not run). Where the plan has a FETCH or a window, ties in
the synthetic data make DataFusion's choice of rows legitimately differ, so
there Polars and DuckDB are compared with each other only. A query on a
dataset with DECIMAL columns that fails is probed again with DOUBLE in their
place (`as_double`), to separate DECIMAL from the other gaps.

`tests/test_catalogue.py` (part of `poe test`) re-probes every query and fails
when a recorded status no longer holds, and checks the annotations against the
probes: no verified query may need a feature marked `no`, and every failure
message must point at a feature the query lists as not fully supported. After
a change in coverage, run `--write` and review the diff.

Date literals are written `D("1994-01-01")`, a cast of a string. Through
Ibis's DataFusion SQL, `ibis.date("…")` compiled to `DATE_TRUNC('DAY', '…')`,
which the checker refuses; `sverify`'s own producer handles both.
