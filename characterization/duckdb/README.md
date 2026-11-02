# DuckDB characterization

The replay of DuckDB's sqllogictests through sverify (`python -m sverify_dev.slt`)
and the fuzz findings against DuckDB (`python -m sverify_dev.duckdb_fuzz`), one
ledger per area of DuckDB's `test/sql/`, for epic #185. [FACTS.md](FACTS.md)
draws the facts out of them.

The quoted tests (queries and expected results) are © Stichting DuckDB
Foundation, MIT-licensed ([LICENSE-duckdb](LICENSE-duckdb)), taken from
[duckdb/duckdb](https://github.com/duckdb/duckdb) at `v2.0.0` (commit
`d54cbbe3df17e8e5ce68312f483b4155836112aa`), the version `python/uv.lock`
pins; each ledger records it (`"duckdb"`, `"source"`). The ledgers and
facts themselves are MPL-2.0, like the rest of the repository.

Each result is `agree` (Lean's `Rel.eval` and DuckDB running the plan Lean
writes both give the expected result), `disagree` (`side`: `lean`, `engine`
or `both`), `refused` (sverify does not plan the query) or `skipped` (it
needs an extension, a setting, a second connection, …). Rerun with:

```bash
cd python && uv run python -m sverify_dev.slt --jobs 2
```

Totals over 46367 queries of DuckDB's tests: 7117 agree, 407 disagree, 26169 refused, 12674 skipped (1034 files skipped whole). The fuzzer checked 42306 random queries on homelab and kept 17 distinct disagreements (`fuzz/*`).

<!-- slt:start -->
| Area | Agree | Disagree | Disagree side | Refused | Skipped | Files skipped | Refused by |
|---|---:|---:|---|---:|---:|---:|---|
| [aggregate](aggregate.json) | 166 | 11 | both 9, engine 1, lean 1 | 2249 | 655 | 14 | producer 1019, translate 1012 |
| [alter](alter.json) | 91 | 0 |  | 66 | 140 | 1 | checker 43, producer 20 |
| [attach](attach.json) | 7 | 0 |  | 150 | 90 | 15 | producer 96, tables 52 |
| [binder](binder.json) | 46 | 0 |  | 176 | 87 | 3 | producer 153, checker 20 |
| [cast](cast.json) | 28 | 36 | both 34, engine 2 | 998 | 172 | 2 | producer 492, checker 466 |
| [catalog](catalog.json) | 83 | 10 | both 10 | 392 | 712 | 4 | producer 317, translate 67 |
| [collate](collate.json) | 11 | 0 |  | 24 | 232 | 7 | producer 18, checker 6 |
| [conjunction](conjunction.json) | 3 | 0 |  | 0 | 0 | 0 |  |
| [connect](connect.json) | 0 | 0 |  | 1 | 0 | 3 | producer 1 |
| [constraints](constraints.json) | 53 | 0 |  | 15 | 19 | 0 | producer 14, tables 1 |
| [copy](copy.json) | 34 | 0 |  | 1024 | 873 | 337 | producer 1022, checker 2 |
| [copy_database](copy_database.json) | 1 | 0 |  | 26 | 11 | 0 | producer 22, tables 4 |
| [create](create.json) | 15 | 0 |  | 8 | 2 | 2 | producer 7, tables 1 |
| [cte](cte.json) | 90 | 0 |  | 444 | 159 | 8 | producer 323, translate 115 |
| [delete](delete.json) | 68 | 0 |  | 6 | 39 | 3 | producer 4, translate 2 |
| [detailed_profiler](detailed_profiler.json) | 3 | 0 |  | 2 | 0 | 0 | checker 1, producer 1 |
| [error](error.json) | 0 | 0 |  | 11 | 53 | 2 | translate 10, producer 1 |
| [execution](execution.json) | 1 | 0 |  | 23 | 0 | 0 | producer 23 |
| [explain](explain.json) | 3 | 0 |  | 3 | 5 | 0 | producer 3 |
| [export](export.json) | 1 | 0 |  | 6 | 48 | 11 | producer 4, checker 2 |
| [extensions](extensions.json) | 0 | 0 |  | 408 | 9 | 7 | producer 408 |
| [filter](filter.json) | 126 | 0 |  | 64 | 76 | 4 | producer 34, translate 19 |
| [function](function.json) | 1 | 0 |  | 4 | 0 | 0 | producer 4 |
| [function/array](function__array.json) | 1 | 0 |  | 85 | 11 | 0 | producer 83, tables 1 |
| [function/autocomplete](function__autocomplete.json) | 0 | 0 |  | 0 | 0 | 25 |  |
| [function/blob](function__blob.json) | 0 | 0 |  | 72 | 4 | 0 | producer 65, checker 6 |
| [function/comparison](function__comparison.json) | 0 | 0 |  | 15 | 0 | 0 | producer 15 |
| [function/date](function__date.json) | 34 | 3 | both 2, engine 1 | 392 | 160 | 0 | producer 233, checker 86 |
| [function/enum](function__enum.json) | 0 | 0 |  | 0 | 24 | 0 |  |
| [function/generic](function__generic.json) | 103 | 6 | both 2, engine 4 | 226 | 89 | 2 | producer 145, translate 66 |
| [function/index](function__index.json) | 0 | 0 |  | 27 | 20 | 0 | producer 27 |
| [function/interval](function__interval.json) | 4 | 0 |  | 137 | 27 | 0 | producer 91, checker 36 |
| [function/list](function__list.json) | 4 | 0 |  | 1872 | 1530 | 10 | producer 1394, checker 463 |
| [function/nested](function__nested.json) | 0 | 0 |  | 32 | 10 | 0 | producer 32 |
| [function/numeric](function__numeric.json) | 84 | 28 | both 14, lean 14 | 251 | 121 | 0 | checker 126, producer 119 |
| [function/operator](function__operator.json) | 61 | 22 | both 4, lean 18 | 98 | 59 | 0 | producer 47, checker 37 |
| [function/string](function__string.json) | 165 | 12 | both 9, lean 3 | 1528 | 169 | 4 | producer 1001, checker 487 |
| [function/table](function__table.json) | 0 | 0 |  | 5 | 12 | 0 | producer 5 |
| [function/time](function__time.json) | 4 | 0 |  | 79 | 59 | 0 | producer 70, checker 9 |
| [function/timestamp](function__timestamp.json) | 15 | 1 | lean 1 | 437 | 137 | 18 | translate 232, producer 179 |
| [function/timetz](function__timetz.json) | 2 | 2 | both 2 | 24 | 44 | 2 | producer 20, checker 4 |
| [function/tokenize](function__tokenize.json) | 0 | 0 |  | 0 | 0 | 2 |  |
| [function/uuid](function__uuid.json) | 2 | 0 |  | 6 | 0 | 1 | producer 4, translate 2 |
| [function/variant](function__variant.json) | 0 | 0 |  | 92 | 48 | 8 | producer 89, translate 2 |
| [fuzz/float_arith](fuzz__float_arith.json) | 14527 | 3 | lean 3 | 0 | 0 | 0 |  |
| [fuzz/int_division](fuzz__int_division.json) | 13708 | 6 | lean 6 | 0 | 0 | 0 |  |
| [fuzz/int_overflow](fuzz__int_overflow.json) | 14054 | 8 | lean 8 | 0 | 0 | 0 |  |
| [generated_columns](generated_columns.json) | 86 | 0 |  | 8 | 22 | 1 | producer 8 |
| [index](index.json) | 230 | 0 |  | 217 | 162 | 5 | producer 156, tables 45 |
| [insert](insert.json) | 30 | 0 |  | 5 | 11 | 0 | checker 3, translate 1 |
| [join](join.json) | 272 | 4 | lean 4 | 985 | 211 | 4 | translate 550, producer 407 |
| [json](json.json) | 1 | 0 |  | 0 | 0 | 121 |  |
| [keywords](keywords.json) | 0 | 0 |  | 0 | 16 | 0 |  |
| [limit](limit.json) | 2 | 0 |  | 5 | 7 | 1 | producer 5 |
| [logging](logging.json) | 20 | 0 |  | 58 | 19 | 9 | producer 54, translate 4 |
| [merge](merge.json) | 36 | 0 |  | 24 | 3 | 0 | producer 19, translate 5 |
| [multi_file](multi_file.json) | 0 | 0 |  | 0 | 0 | 4 |  |
| [optimizer](optimizer.json) | 382 | 19 | both 17, lean 2 | 440 | 448 | 14 | producer 340, checker 73 |
| [order](order.json) | 46 | 1 | both 1 | 631 | 50 | 3 | producer 587, translate 18 |
| [ordinality](ordinality.json) | 0 | 0 |  | 6 | 0 | 1 | producer 6 |
| [overflow](overflow.json) | 73 | 61 | both 40, engine 1, lean 20 | 8 | 10 | 0 | checker 4, producer 2 |
| [parallelism](parallelism.json) | 8 | 0 |  | 3 | 837 | 6 | producer 2, translate 1 |
| [parser](parser.json) | 212 | 12 | both 12 | 308 | 355 | 3 | producer 177, translate 76 |
| [peg_parser](peg_parser.json) | 53 | 0 |  | 34 | 54 | 60 | producer 23, checker 7 |
| [pg_catalog](pg_catalog.json) | 0 | 0 |  | 54 | 74 | 0 | producer 49, translate 4 |
| [pivot](pivot.json) | 1 | 0 |  | 93 | 28 | 1 | translate 86, producer 5 |
| [pragma](pragma.json) | 3 | 0 |  | 25 | 18 | 23 | producer 24, translate 1 |
| [prepared](prepared.json) | 18 | 0 |  | 15 | 5 | 0 | producer 15 |
| [progress](progress.json) | 0 | 0 |  | 35 | 8 | 0 | producer 34, translate 1 |
| [projection](projection.json) | 56 | 0 |  | 146 | 45 | 0 | producer 137, checker 8 |
| [returning](returning.json) | 16 | 0 |  | 1 | 0 | 0 | producer 1 |
| [sample](sample.json) | 0 | 0 |  | 36 | 17 | 7 | translate 28, producer 8 |
| [secrets](secrets.json) | 0 | 0 |  | 16 | 14 | 3 | producer 16 |
| [select](select.json) | 11 | 0 |  | 37 | 21 | 0 | producer 37 |
| [serialization](serialization.json) | 2 | 0 |  | 1 | 0 | 0 | tables 1 |
| [setops](setops.json) | 122 | 6 | both 3, engine 1, lean 2 | 94 | 30 | 0 | producer 86, checker 8 |
| [settings](settings.json) | 8 | 0 |  | 714 | 81 | 7 | producer 714 |
| [show_select](show_select.json) | 1 | 0 |  | 20 | 0 | 1 | producer 18, translate 1 |
| [sql_export](sql_export.json) | 102 | 3 | engine 3 | 747 | 1183 | 8 | producer 433, translate 246 |
| [storage](storage.json) | 2591 | 4 | both 4 | 1157 | 910 | 170 | producer 648, checker 321 |
| [storage_version](storage_version.json) | 0 | 0 |  | 5 | 0 | 0 | tables 5 |
| [subquery](subquery.json) | 111 | 1 | engine 1 | 647 | 139 | 2 | producer 637, translate 6 |
| [table_function](table_function.json) | 0 | 0 |  | 221 | 114 | 7 | producer 211, checker 8 |
| [timezone](timezone.json) | 0 | 0 |  | 0 | 0 | 21 |  |
| [topn](topn.json) | 62 | 0 |  | 33 | 36 | 0 | tables 17, checker 11 |
| [tpcds](tpcds.json) | 0 | 0 |  | 0 | 0 | 3 |  |
| [tpch](tpch.json) | 0 | 0 |  | 0 | 0 | 3 |  |
| [transactions](transactions.json) | 74 | 0 |  | 27 | 235 | 2 | producer 14, tables 10 |
| [trigger](trigger.json) | 220 | 0 |  | 63 | 10 | 1 | producer 48, translate 13 |
| [types](types.json) | 4 | 0 |  | 96 | 31 | 0 | producer 84, checker 11 |
| [types/alias](types__alias.json) | 0 | 0 |  | 0 | 22 | 0 |  |
| [types/bignum](types__bignum.json) | 0 | 0 |  | 261 | 10 | 0 | producer 257, translate 2 |
| [types/bit](types__bit.json) | 0 | 0 |  | 84 | 55 | 0 | producer 76, checker 4 |
| [types/blob](types__blob.json) | 1 | 0 |  | 50 | 0 | 0 | checker 34, tables 9 |
| [types/date](types__date.json) | 3 | 28 | both 18, engine 4, lean 6 | 168 | 10 | 0 | checker 145, producer 23 |
| [types/decimal](types__decimal.json) | 3 | 0 |  | 2106 | 16 | 0 | checker 1969, producer 113 |
| [types/enum](types__enum.json) | 1 | 0 |  | 2 | 192 | 1 | producer 2 |
| [types/float](types__float.json) | 312 | 13 | both 2, lean 11 | 235 | 57 | 0 | checker 117, producer 110 |
| [types/geo](types__geo.json) | 0 | 0 |  | 186 | 215 | 7 | producer 172, tables 9 |
| [types/hugeint](types__hugeint.json) | 15 | 0 |  | 169 | 77 | 0 | producer 159, checker 5 |
| [types/interval](types__interval.json) | 5 | 68 | both 44, engine 23, lean 1 | 204 | 63 | 0 | checker 100, producer 78 |
| [types/list](types__list.json) | 89 | 18 | lean 18 | 411 | 32 | 0 | checker 204, producer 175 |
| [types/map](types__map.json) | 0 | 0 |  | 34 | 7 | 0 | producer 18, checker 15 |
| [types/nested](types__nested.json) | 8 | 0 |  | 725 | 129 | 6 | producer 390, checker 259 |
| [types/null](types__null.json) | 14 | 0 |  | 8 | 7 | 0 | producer 8 |
| [types/numeric](types__numeric.json) | 0 | 0 |  | 381 | 37 | 0 | producer 348, checker 28 |
| [types/string](types__string.json) | 4 | 3 | both 3 | 1 | 0 | 0 | checker 1 |
| [types/struct](types__struct.json) | 0 | 0 |  | 670 | 72 | 5 | producer 530, tables 81 |
| [types/time](types__time.json) | 1 | 3 | both 2, lean 1 | 102 | 41 | 1 | producer 56, checker 43 |
| [types/timestamp](types__timestamp.json) | 8 | 24 | both 13, engine 6, lean 5 | 223 | 44 | 5 | checker 159, producer 61 |
| [types/type](types__type.json) | 0 | 0 |  | 0 | 6 | 0 |  |
| [types/uhugeint](types__uhugeint.json) | 2 | 0 |  | 131 | 15 | 0 | producer 126, tables 3 |
| [types/union](types__union.json) | 0 | 0 |  | 123 | 10 | 1 | producer 121, tables 2 |
| [types/unsigned](types__unsigned.json) | 0 | 0 |  | 154 | 0 | 0 | producer 151, translate 2 |
| [types/uuid](types__uuid.json) | 0 | 0 |  | 20 | 2 | 0 | producer 20 |
| [types/variant](types__variant.json) | 1 | 0 |  | 317 | 10 | 14 | producer 268, tables 46 |
| [unnest](unnest.json) | 0 | 0 |  | 1 | 0 | 0 | producer 1 |
| [update](update.json) | 89 | 0 |  | 9 | 164 | 0 | producer 6, translate 2 |
| [upsert](upsert.json) | 91 | 0 |  | 30 | 30 | 2 | producer 28, checker 2 |
| [vacuum](vacuum.json) | 0 | 0 |  | 0 | 0 | 1 |  |
| [variables](variables.json) | 0 | 0 |  | 3 | 14 | 0 | producer 3 |
| [variant](variant.json) | 0 | 0 |  | 0 | 0 | 2 |  |
| [vector_types](vector_types.json) | 0 | 0 |  | 0 | 32 | 0 |  |
| [window](window.json) | 307 | 8 | both 7, lean 1 | 868 | 195 | 3 | producer 697, checker 103 |
<!-- slt:end -->
