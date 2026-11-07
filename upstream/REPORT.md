# Upstream report

<!-- Generated from `bugs/*.json` by `python -m sverify_dev.bugs --write`. -->

Sverify's upstream ledger holds 73 entries ([README](README.md)). 27 are bugs to report: each reproduces on the version named, and no upstream issue reports it. Each entry has the repro, what was searched and how sverify handles it. The `upstream-report` skill drafts the issue.

## To report

| Entry | Project | What goes wrong | Reproduces on |
|---|---|---|---|
| [DD-6](bugs/DD-6.json) | DuckDB | `least` and `greatest` on `FLOAT` turn `-0.0` into `+0.0` and drop a NaN's sign | duckdb 2.0.0, duckdb main d4eea3f208 (2026-11-07) |
| [DD-8](bugs/DD-8.json) | DuckDB | Docs: `%` on `FLOAT` and `DOUBLE` by zero gives NaN, where the page says it raises | duckdb 2.0.0, duckdb-web main cab31bd0 (2026-11-07) |
| [DD-9](bugs/DD-9.json) | DuckDB | Docs: the `pow` and `**` examples show integers, and the result is always `DOUBLE` | duckdb 2.0.0, duckdb-web main cab31bd0 (2026-11-07) |
| [PL-5](bugs/PL-5.json) | Polars | Streaming `cov` and `corr` of `Decimal` columns raise; the in-memory engine computes them | polars 2.1.0 (2026-11-07) |
| [PL-6](bugs/PL-6.json) | Polars | CSE hoists a strict cast that two `when/then` branches share onto every row | polars 2.1.0 (2026-11-07) |
| [PL-7](bugs/PL-7.json) | Polars | Predicate pushdown merges a filter on `str.to_integer` into the one before, which then raises | polars 2.1.0 (2026-11-07) |
| [PL-8](bugs/PL-8.json) | Polars | Docs: float division by a literal or one-row divisor does not follow IEEE 754 as documented | polars 2.1.0 (2026-11-07) |
| [PL-9](bugs/PL-9.json) | Polars | Docs: `round`'s `half_` modes do not round to the nearest value (2.675 gives 2.68) | polars 2.1.0 (2026-11-07) |
| [PL-10](bugs/PL-10.json) | Polars | Docs: `nan_max` and `nan_min` describe numpy's `nanmax` and `nanmin` backwards | polars 2.1.0, polars main 8dcc6b28 (2026-11-07) |
| [PL-11](bugs/PL-11.json) | Polars | Docs: `quantile` says it returns f64, and a `Float32` input stays `Float32` | polars 2.1.0 (2026-11-07) |
| [PL-12](bugs/PL-12.json) | Polars | Docs: `list.get` says an out-of-bounds index gives None, and by default it raises | polars 2.1.0 (2026-11-07) |
| [PL-14](bugs/PL-14.json) | Polars | Streaming `group_by`: `var` and `std` of a group with only a NULL are 0.0, not null | polars 2.1.0 (2026-11-07) |
| [SP-3](bugs/SP-3.json) | Spark | Timestamp plus interval past the range raises a bare `ArithmeticException`, no error class | pyspark 4.3.0 (2026-11-07) |
| [SP-4](bugs/SP-4.json) | Spark | An invalid constant regex raises an error class interpreted, a bare exception through codegen | pyspark 4.3.0 (2026-11-07) |
| [SP-5](bugs/SP-5.json) | Spark | ANSI mode: `floor` and `ceil` of NaN return 0 | pyspark 4.3.0 (2026-11-07) |
| [SP-6](bugs/SP-6.json) | Spark | `to_timestamp` past the microsecond range raises a bare `ArithmeticException` | pyspark 4.3.0 (2026-11-07) |
| [SP-7](bugs/SP-7.json) | Spark | `TIMESTAMP_SECONDS` of a decimal with more than six fractional digits raises a bare `Rounding necessary` | pyspark 4.3.0 (2026-11-07) |
| [SG-8](bugs/SG-8.json) | SQLGlot | DuckDB: `INTERVAL '1 day ago'` loses `ago` and reads as a positive interval | sqlglot 30.30.0, sqlglot main b99f5d58b1 (2026-11-07) |
| [SG-9](bugs/SG-9.json) | SQLGlot | DuckDB: `agg(x) EXPORT_STATE` parses as the column alias `EXPORT_STATE` | sqlglot 30.30.0, sqlglot main b99f5d58b1 (2026-11-07) |
| [IB-1](bugs/IB-1.json) | Ibis | Every `execute()` warns: Ibis reads pandas's deprecated `future.infer_string` | ibis-framework 12.0.0, ibis main 6d40f963, duckdb 2.0.0, pandas 3.1.1 (2026-11-07) |
| [IB-2](bugs/IB-2.json) | Ibis | DuckDB: `time.truncate()` compiles to `DATE_TRUNC` of a `TIME`, which fails to bind | ibis-framework 12.0.0, ibis main 6d40f963, duckdb 2.0.0 (2026-11-07) |
| [IB-3](bugs/IB-3.json) | Ibis | DuckDB: `argmin` and `argmax` of a group whose keys are all NULL return a value | ibis-framework 12.0.0, ibis main 6d40f963, duckdb 2.0.0 (2026-11-07) |
| [IB-4](bugs/IB-4.json) | Ibis | A negative `following` or `preceding` writes `-1 following`, which DuckDB refuses | ibis-framework 12.0.0, ibis main 6d40f963, duckdb 2.0.0 (2026-11-07) |
| [DL-2](bugs/DL-2.json) | delta-rs | `history()` after `load_as_version` lists the latest commits, numbered from the loaded version | deltalake 1.6.6, delta-rs main ca279b73 (2026-11-07) |
| [ST-13](bugs/ST-13.json) | Substrait | Thirteen test cases expect values their inputs do not give (`variance`, `std_dev`, `multiply`, `shift_left`) | substrait main ecb826b53abd (2026-11-07) |
| [ST-14](bugs/ST-14.json) | Substrait | Four `logb` test cases read the base first, and the YAML defines `logb(x, b)` | substrait main ecb826b53abd (2026-11-07) |
| [ST-15](bugs/ST-15.json) | Substrait | Forty-five test cases state an option or value their function's YAML does not have | substrait main ecb826b53abd (2026-11-07) |

## To comment on

An open upstream issue covers these; the case is worth a comment there.

| Entry | Project | Issue |
|---|---|---|
| [PL-1](bugs/PL-1.json) | Polars | [pola-rs/polars#30398](https://github.com/pola-rs/polars/issues/30398) |
| [PL-2](bugs/PL-2.json) | Polars | [pola-rs/polars#25742](https://github.com/pola-rs/polars/issues/25742) |

## By class and project

| Project | report | filed | fixed | duplicate | not-a-bug | spec-gap | total |
|---|---:|---:|---:|---:|---:|---:|---:|
| DuckDB | 3 | 3 | 2 | 0 | 1 | 0 | 9 |
| Polars | 9 | 0 | 0 | 2 | 3 | 0 | 14 |
| Spark | 5 | 2 | 0 | 0 | 0 | 0 | 7 |
| SQLGlot | 2 | 0 | 7 | 0 | 1 | 0 | 10 |
| Ibis | 4 | 0 | 0 | 0 | 0 | 0 | 4 |
| delta-rs | 1 | 1 | 0 | 0 | 0 | 0 | 2 |
| DataFusion | 0 | 5 | 4 | 0 | 2 | 0 | 11 |
| Substrait | 3 | 0 | 0 | 0 | 0 | 13 | 16 |
| total | 27 | 11 | 13 | 2 | 7 | 13 | 73 |

The classes:

- `report`: reproduces on the latest release or main, and no upstream issue reports it.
- `filed`: reported upstream, still open.
- `fixed`: fixed on the project's main, released or due in a release.
- `duplicate`: an open upstream issue covers it: a comment there with the case.
- `not-a-bug`: documented or intended, or matters only to sverify's model (an engine fact).
- `spec-gap`: Substrait leaves it unspecified: for the spec discussion.

filed: [DD-3](bugs/DD-3.json), [DD-4](bugs/DD-4.json), [DD-5](bugs/DD-5.json), [SP-1](bugs/SP-1.json), [SP-2](bugs/SP-2.json), [DL-1](bugs/DL-1.json), [DF-1](bugs/DF-1.json), [DF-4](bugs/DF-4.json), [DF-8](bugs/DF-8.json), [DF-9](bugs/DF-9.json), [DF-10](bugs/DF-10.json).

fixed: [DD-1](bugs/DD-1.json), [DD-7](bugs/DD-7.json), [SG-1](bugs/SG-1.json), [SG-3](bugs/SG-3.json), [SG-4](bugs/SG-4.json), [SG-5](bugs/SG-5.json), [SG-6](bugs/SG-6.json), [SG-7](bugs/SG-7.json), [SG-10](bugs/SG-10.json), [DF-2](bugs/DF-2.json), [DF-3](bugs/DF-3.json), [DF-6](bugs/DF-6.json), [DF-11](bugs/DF-11.json).

not-a-bug: [DD-2](bugs/DD-2.json), [PL-3](bugs/PL-3.json), [PL-4](bugs/PL-4.json), [PL-13](bugs/PL-13.json), [SG-2](bugs/SG-2.json), [DF-5](bugs/DF-5.json), [DF-7](bugs/DF-7.json).

spec-gap: [ST-1](bugs/ST-1.json), [ST-2](bugs/ST-2.json), [ST-3](bugs/ST-3.json), [ST-4](bugs/ST-4.json), [ST-5](bugs/ST-5.json), [ST-6](bugs/ST-6.json), [ST-7](bugs/ST-7.json), [ST-8](bugs/ST-8.json), [ST-9](bugs/ST-9.json), [ST-10](bugs/ST-10.json), [ST-11](bugs/ST-11.json), [ST-12](bugs/ST-12.json), [ST-16](bugs/ST-16.json).
