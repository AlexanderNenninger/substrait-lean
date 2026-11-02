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
| [aggregate](aggregate.json) | 121 | 6 | engine 1, lean 5 | 1962 | 992 | 14 | lift 1956, checker 6 |
| [alter](alter.json) | 90 | 31 | lean 31 | 35 | 141 | 1 | lift 33, tables 2 |
| [attach](attach.json) | 7 | 0 |  | 150 | 90 | 15 | lift 98, tables 52 |
| [binder](binder.json) | 60 | 0 |  | 146 | 103 | 3 | lift 146 |
| [cast](cast.json) | 27 | 3 | engine 1, lean 2 | 1028 | 176 | 2 | lift 699, checker 329 |
| [catalog](catalog.json) | 109 | 0 |  | 412 | 676 | 4 | lift 404, tables 8 |
| [collate](collate.json) | 4 | 0 |  | 31 | 232 | 7 | lift 30, checker 1 |
| [conjunction](conjunction.json) | 0 | 0 |  | 3 | 0 | 0 | lift 3 |
| [connect](connect.json) | 0 | 0 |  | 1 | 0 | 3 | lift 1 |
| [constraints](constraints.json) | 45 | 0 |  | 14 | 28 | 0 | lift 14 |
| [copy](copy.json) | 34 | 0 |  | 1023 | 874 | 337 | lift 1023 |
| [copy_database](copy_database.json) | 1 | 0 |  | 26 | 11 | 0 | lift 22, tables 4 |
| [create](create.json) | 14 | 0 |  | 9 | 2 | 2 | lift 9 |
| [cte](cte.json) | 126 | 1 | both 1 | 470 | 96 | 8 | lift 468, checker 2 |
| [delete](delete.json) | 68 | 0 |  | 5 | 40 | 3 | lift 5 |
| [detailed_profiler](detailed_profiler.json) | 4 | 0 |  | 1 | 0 | 0 | lift 1 |
| [error](error.json) | 0 | 0 |  | 11 | 53 | 2 | lift 11 |
| [execution](execution.json) | 1 | 0 |  | 23 | 0 | 0 | lift 23 |
| [explain](explain.json) | 3 | 0 |  | 3 | 5 | 0 | lift 3 |
| [export](export.json) | 1 | 2 | lean 2 | 1 | 51 | 11 | lift 1 |
| [extensions](extensions.json) | 0 | 0 |  | 408 | 9 | 7 | lift 408 |
| [filter](filter.json) | 78 | 0 |  | 64 | 124 | 4 | lift 64 |
| [function](function.json) | 1 | 0 |  | 4 | 0 | 0 | lift 4 |
| [function/array](function__array.json) | 1 | 0 |  | 85 | 11 | 0 | lift 84, tables 1 |
| [function/autocomplete](function__autocomplete.json) | 0 | 0 |  | 0 | 0 | 25 |  |
| [function/blob](function__blob.json) | 0 | 0 |  | 72 | 4 | 0 | lift 72 |
| [function/comparison](function__comparison.json) | 0 | 0 |  | 15 | 0 | 0 | lift 15 |
| [function/date](function__date.json) | 29 | 0 |  | 199 | 361 | 0 | lift 199 |
| [function/enum](function__enum.json) | 0 | 0 |  | 0 | 24 | 0 |  |
| [function/generic](function__generic.json) | 42 | 0 |  | 221 | 161 | 2 | lift 216, checker 4 |
| [function/index](function__index.json) | 0 | 0 |  | 27 | 20 | 0 | lift 27 |
| [function/interval](function__interval.json) | 4 | 0 |  | 33 | 131 | 0 | lift 33 |
| [function/list](function__list.json) | 2 | 0 |  | 1868 | 1536 | 10 | lift 1847, checker 20 |
| [function/nested](function__nested.json) | 0 | 0 |  | 32 | 10 | 0 | lift 32 |
| [function/numeric](function__numeric.json) | 48 | 7 | lean 7 | 230 | 199 | 0 | lift 230 |
| [function/operator](function__operator.json) | 47 | 21 | lean 21 | 98 | 74 | 0 | lift 98 |
| [function/string](function__string.json) | 263 | 7 | both 4, lean 3 | 1351 | 253 | 4 | lift 1292, checker 59 |
| [function/table](function__table.json) | 0 | 0 |  | 10 | 7 | 0 | lift 10 |
| [function/time](function__time.json) | 0 | 0 |  | 63 | 79 | 0 | lift 63 |
| [function/timestamp](function__timestamp.json) | 18 | 0 |  | 330 | 242 | 18 | lift 330 |
| [function/timetz](function__timetz.json) | 0 | 0 |  | 28 | 44 | 2 | lift 28 |
| [function/tokenize](function__tokenize.json) | 0 | 0 |  | 0 | 0 | 2 |  |
| [function/uuid](function__uuid.json) | 2 | 0 |  | 6 | 0 | 1 | lift 6 |
| [function/variant](function__variant.json) | 0 | 0 |  | 92 | 48 | 8 | lift 92 |
| [fuzz/float_arith](fuzz__float_arith.json) | 14527 | 3 | lean 3 | 0 | 0 | 0 |  |
| [fuzz/int_division](fuzz__int_division.json) | 13708 | 6 | lean 6 | 0 | 0 | 0 |  |
| [fuzz/int_overflow](fuzz__int_overflow.json) | 14054 | 8 | lean 8 | 0 | 0 | 0 |  |
| [generated_columns](generated_columns.json) | 70 | 0 |  | 24 | 22 | 1 | lift 24 |
| [index](index.json) | 307 | 0 |  | 132 | 170 | 5 | lift 85, tables 47 |
| [insert](insert.json) | 29 | 1 | lean 1 | 3 | 13 | 0 | lift 3 |
| [join](join.json) | 244 | 0 |  | 915 | 313 | 4 | lift 908, tables 6 |
| [json](json.json) | 1 | 0 |  | 0 | 0 | 121 |  |
| [keywords](keywords.json) | 0 | 0 |  | 0 | 16 | 0 |  |
| [limit](limit.json) | 2 | 0 |  | 5 | 7 | 1 | lift 5 |
| [logging](logging.json) | 20 | 0 |  | 63 | 14 | 9 | lift 63 |
| [merge](merge.json) | 34 | 0 |  | 26 | 3 | 0 | lift 26 |
| [multi_file](multi_file.json) | 0 | 0 |  | 0 | 0 | 4 |  |
| [optimizer](optimizer.json) | 355 | 5 | lean 5 | 467 | 462 | 14 | lift 429, checker 27 |
| [order](order.json) | 51 | 0 |  | 576 | 101 | 3 | lift 574, checker 2 |
| [ordinality](ordinality.json) | 0 | 0 |  | 6 | 0 | 1 | lift 6 |
| [overflow](overflow.json) | 66 | 57 | both 17, lean 40 | 19 | 10 | 0 | lift 16, checker 3 |
| [parallelism](parallelism.json) | 8 | 0 |  | 2 | 838 | 6 | lift 2 |
| [parser](parser.json) | 198 | 4 | both 4 | 328 | 357 | 3 | lift 302, checker 26 |
| [peg_parser](peg_parser.json) | 47 | 0 |  | 40 | 54 | 60 | lift 40 |
| [pg_catalog](pg_catalog.json) | 0 | 0 |  | 50 | 78 | 0 | lift 50 |
| [pivot](pivot.json) | 3 | 0 |  | 80 | 39 | 1 | lift 80 |
| [pragma](pragma.json) | 3 | 0 |  | 25 | 18 | 23 | lift 25 |
| [prepared](prepared.json) | 17 | 0 |  | 16 | 5 | 0 | lift 16 |
| [progress](progress.json) | 0 | 0 |  | 36 | 7 | 0 | lift 36 |
| [projection](projection.json) | 104 | 0 |  | 84 | 59 | 0 | lift 78, checker 6 |
| [returning](returning.json) | 16 | 0 |  | 1 | 0 | 0 | lift 1 |
| [sample](sample.json) | 0 | 0 |  | 15 | 38 | 7 | lift 15 |
| [secrets](secrets.json) | 0 | 0 |  | 16 | 14 | 3 | lift 16 |
| [select](select.json) | 11 | 0 |  | 37 | 21 | 0 | lift 37 |
| [serialization](serialization.json) | 2 | 0 |  | 1 | 0 | 0 | tables 1 |
| [setops](setops.json) | 18 | 0 |  | 87 | 147 | 0 | lift 87 |
| [settings](settings.json) | 6 | 0 |  | 712 | 85 | 7 | lift 712 |
| [show_select](show_select.json) | 1 | 0 |  | 20 | 0 | 1 | lift 19, tables 1 |
| [sql_export](sql_export.json) | 124 | 2 | engine 2 | 739 | 1170 | 8 | lift 732, tables 5 |
| [storage](storage.json) | 2663 | 37 | both 6, lean 31 | 1070 | 892 | 170 | lift 829, tables 134 |
| [storage_version](storage_version.json) | 0 | 0 |  | 5 | 0 | 0 | tables 5 |
| [subquery](subquery.json) | 125 | 0 |  | 384 | 389 | 2 | lift 379, checker 5 |
| [table_function](table_function.json) | 0 | 0 |  | 228 | 107 | 7 | lift 228 |
| [timezone](timezone.json) | 0 | 0 |  | 0 | 0 | 21 |  |
| [topn](topn.json) | 65 | 8 | lean 8 | 33 | 25 | 0 | tables 28, lift 5 |
| [tpcds](tpcds.json) | 0 | 0 |  | 0 | 0 | 3 |  |
| [tpch](tpch.json) | 0 | 0 |  | 0 | 0 | 3 |  |
| [transactions](transactions.json) | 74 | 0 |  | 27 | 235 | 2 | lift 18, tables 9 |
| [trigger](trigger.json) | 223 | 0 |  | 65 | 5 | 1 | lift 64, tables 1 |
| [types](types.json) | 8 | 5 | lean 5 | 83 | 35 | 0 | lift 76, checker 7 |
| [types/alias](types__alias.json) | 0 | 0 |  | 0 | 22 | 0 |  |
| [types/bignum](types__bignum.json) | 0 | 0 |  | 218 | 53 | 0 | lift 218 |
| [types/bit](types__bit.json) | 0 | 0 |  | 80 | 59 | 0 | lift 80 |
| [types/blob](types__blob.json) | 0 | 0 |  | 46 | 5 | 0 | lift 46 |
| [types/date](types__date.json) | 7 | 0 |  | 192 | 10 | 0 | lift 156, checker 36 |
| [types/decimal](types__decimal.json) | 1598 | 13 | both 1, lean 12 | 498 | 16 | 0 | checker 252, lift 246 |
| [types/enum](types__enum.json) | 2 | 0 |  | 1 | 192 | 1 | lift 1 |
| [types/float](types__float.json) | 165 | 14 | both 12, engine 2 | 369 | 69 | 0 | lift 351, checker 18 |
| [types/geo](types__geo.json) | 0 | 0 |  | 192 | 209 | 7 | lift 187, tables 5 |
| [types/hugeint](types__hugeint.json) | 1 | 0 |  | 175 | 85 | 0 | lift 175 |
| [types/interval](types__interval.json) | 42 | 1 | both 1 | 223 | 74 | 0 | lift 215, checker 8 |
| [types/list](types__list.json) | 102 | 11 | lean 11 | 396 | 41 | 0 | lift 395, checker 1 |
| [types/map](types__map.json) | 0 | 0 |  | 37 | 4 | 0 | lift 37 |
| [types/nested](types__nested.json) | 25 | 4 | both 1, lean 3 | 666 | 176 | 5 | lift 645, checker 21 |
| [types/null](types__null.json) | 6 | 0 |  | 2 | 21 | 0 | lift 2 |
| [types/numeric](types__numeric.json) | 10 | 7 | engine 1, lean 6 | 274 | 34 | 3 | lift 246, checker 21 |
| [types/string](types__string.json) | 7 | 0 |  | 1 | 0 | 0 | lift 1 |
| [types/struct](types__struct.json) | 45 | 6 | lean 6 | 598 | 93 | 5 | lift 595, checker 3 |
| [types/time](types__time.json) | 2 | 2 | both 1, lean 1 | 101 | 42 | 1 | lift 60, checker 41 |
| [types/timestamp](types__timestamp.json) | 6 | 4 | both 4 | 222 | 67 | 5 | lift 220, checker 2 |
| [types/type](types__type.json) | 0 | 0 |  | 0 | 6 | 0 |  |
| [types/uhugeint](types__uhugeint.json) | 2 | 0 |  | 125 | 21 | 0 | lift 125 |
| [types/union](types__union.json) | 0 | 0 |  | 23 | 110 | 1 | lift 21, tables 2 |
| [types/unsigned](types__unsigned.json) | 0 | 0 |  | 154 | 0 | 0 | lift 154 |
| [types/uuid](types__uuid.json) | 0 | 0 |  | 20 | 2 | 0 | lift 20 |
| [types/variant](types__variant.json) | 1 | 0 |  | 317 | 10 | 14 | lift 317 |
| [unnest](unnest.json) | 0 | 0 |  | 1 | 0 | 0 | lift 1 |
| [update](update.json) | 87 | 0 |  | 11 | 164 | 0 | lift 11 |
| [upsert](upsert.json) | 91 | 0 |  | 30 | 30 | 2 | lift 30 |
| [vacuum](vacuum.json) | 0 | 0 |  | 0 | 0 | 1 |  |
| [variables](variables.json) | 0 | 0 |  | 3 | 14 | 0 | lift 3 |
| [variant](variant.json) | 0 | 0 |  | 0 | 0 | 2 |  |
| [vector_types](vector_types.json) | 0 | 0 |  | 0 | 32 | 0 |  |
| [window](window.json) | 105 | 6 | both 6 | 946 | 321 | 3 | lift 945, checker 1 |
<!-- slt:end -->
