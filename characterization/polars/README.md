# Polars characterization

What Polars does at each of the core's options
([core-semantics.md](../../docs/core-semantics.md)), recorded as facts, one
JSON document each in [facts/](facts/), in the format of
[fact.schema.json](../fact.schema.json) (`python -m sverify_dev.facts` checks
them). They are the evidence a future `Profile.polars` and its row of the
realizability table are built from. Polars has no profile yet: its backend is
paused for new features until #271.

Polars here is version 2.1.0, the version `python/uv.lock` pins: the Python
package `polars` 2.1.0 and its Rust crates at tag
[`py-2.1.0`](https://github.com/pola-rs/polars/tree/py-2.1.0) (commit
`7f902bd3`). The facts' `engine_version` is `py-2.1.0`. What is probed is
Polars's expression API (`pl.col(...)`, `DataFrame.select`, `group_by`,
`sort`, `join`), which `sverify.polars_engine` writes plans to; Polars's
SQL interface (`pl.SQLContext`) is out of scope.

Each fact names the items of the characterization checklist
([../areas.json](../areas.json)) it settles; `python -m sverify_dev.facts
--coverage polars` lists them, and the items no fact settles yet.

## How the facts are judged

As DuckDB's ([../duckdb/README.md](../duckdb/README.md#how-the-facts-are-judged)):
`Rel.eval` means Substrait's semantics, each function's extension YAML with
its options; where Substrait leaves a choice open, the reference raises if
engines disagree on an edge case, and otherwise takes the least surprising
value every backend can emulate; an engine's profile refines the loose core,
and its diff against the reference is its row of the realizability table
([Terminology](../../docs/core-semantics.md#terminology)). A fact's `status` is `open` where Polars differs from
the reference and the profile has not decided how to bridge it, and
`no-finding` where Polars gives the reference natively.

## The probes

`python -m sverify_dev.probe_polars` (`python/tools/sverify_dev/probe_polars.py`)
writes [probes.json](probes.json), which `tests/test_probe_polars.py` checks is
current. It holds two kinds of entry:

- A probe runs a Polars expression on edge cases (0, ±1, ±2, 3, ±7, the
  bounds of each integer width; 0.5, ±2.5, 7, 1e308, ±inf, NaN; NULL), one
  row at a time, and compares each row with Lean's outcome of the Substrait
  call under each candidate value of its option (`substrait-check
  --outcomes`), as `sverify_dev.probe` does for DuckDB. `matching` lists the
  candidates that agree on every row; `candidates` gives, for each, the
  number of rows that differ and up to four of them.
- An observation is a short Polars program whose result no single Substrait
  call describes (a sort, a grouping, a cast that fails, a date), with its
  `observed` result.

Facts cite both by their `construct`. Rerun after a Polars or model change:

```bash
cd python && uv run python -m sverify_dev.probe_polars --write
```

The probes ran on macOS arm64. The elementary functions are Rust's `f64`
functions, which call the platform's libm, and the sign of a NaN that
arithmetic creates is the platform's, so no observation depends on either.

## The Polars diff, as a table

How Polars 2.1.0 compares with the reference, option by option. "Native"
means Polars's own expression gives the reference result.

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `add` `subtract` `multiply` `negate` (`i8`…`i64`) | `overflow` | `ERROR` | `SILENT`, at the column's width; `**` too | [int-arith](facts/polars-int-arith.json) |
| `abs` (`i8`…`i64`) | `overflow` | `ERROR` | `abs(MIN)` is `MIN` | [int-abs](facts/polars-int-abs.json) |
| `divide` (`i8`…`i64`) | rounding | truncate | `//` floors; no truncating division in the Python API | [int-divide](facts/polars-int-divide.json) |
| | `on_division_by_zero` | `ERROR` | `NULL` | |
| | `overflow` (`MIN / -1`) | `ERROR` | wraps to `MIN` | |
| `modulus` (`i8`…`i64`) | `division_type` | `TRUNCATE` | `FLOOR` | [int-modulus](facts/polars-int-modulus.json) |
| | `on_division_by_zero` | `ERROR` | `NULL` | |
| | `MIN % -1` | 0 | 0, native | |
| `/` on integers | | an integer `divide` | a `Float64` division; a literal divisor takes the reciprocal, as below | [int-true-divide](facts/polars-int-true-divide.json) |
| `shift_left`, `shift_right` | range (ST-1) | drop bits, raise outside `[0, 63]` | no shift expressions | [int-shift](facts/polars-int-shift.json) |
| `sum` (`i8`…`i64`) | `overflow` | `ERROR`, at the input's type | `i8`, `i16` widen to `i64`; `i32`, `i64` wrap | [sum-int](facts/polars-sum-int.json) |
| `sum` (all) | no values | NULL | 0 (Substrait's `sum0`) | sum-int, [sum-float](facts/polars-sum-float.json) |
| `avg` (integers) | `avg_int_result` | the declared type | `Float64` | [avg-int](facts/polars-avg-int.json) |
| `add` `subtract` `multiply` (`fp64`) | `nan_creation` | raise | NaN (IEEE) | [double-arith](facts/polars-double-arith.json) |
| `divide` (`fp64`) | `on_division_by_zero` | `ERROR` | `IEEE`; `±inf / ±inf` is NaN | [double-divide](facts/polars-double-divide.json) |
| `divide`, `modulus` by a literal (`fp32`, `fp64`) | `rounding`, `nan_creation` | one rounding; no NaN from finite operands | `x · (1 / c)`: an ulp off, NaN or inf for a subnormal `c`, `49.0 % 49.0` is 49.0; on streaming per morsel, so it depends on the thread count ([PL-3](../../upstream/bugs/PL-3.json)) | [double-scalar-divisor](facts/polars-double-scalar-divisor.json) |
| `modulus` (`fp64`) | | truncated (`fmod`), zero divisor raises | `x - y·floor(x / y)`: floor sign, NaN for `x % 0` and finite `x % ±inf` ([PL-1](../../upstream/bugs/PL-1.json)) | [double-modulus](facts/polars-double-modulus.json) |
| `sqrt`, logs, `asin`, `acos`, `power`, trig of ±inf | `on_domain_error` | `ERROR` | `NAN` | [math-domain](facts/polars-math-domain.json) |
| `ln`, `log10`, `log2` | `on_log_zero` | `ERROR` | `MINUS_INFINITY` | math-domain |
| `log10`, `log2` | last bits | the platform's `log10`, `log2` | `ln(x) / ln(b)`, an ulp off at times; on `Float32` the natural `log()` too ([PL-4](../../upstream/bugs/PL-4.json)) | [log-base](facts/polars-log-base.json) |
| `atan2` | `atan2(0, 0)` | raise | 0 | [atan2](facts/polars-atan2.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | `TIE_TO_EVEN` by default; native with `mode='half_away_from_zero'` | [round](facts/polars-round.json) |
| `round` to `d` digits | | `TIE_AWAY_FROM_ZERO`, `d < 0` allowed | `op(x · 10ᵈ) / 10ᵈ`; `d < 0` refused by the API | [round-digits](facts/polars-round-digits.json) |
| `floor`, `ceil`, `exp`, `atan` | | | native | round, math-domain |
| doubles | `zero_sign` | `ONE_ZERO` | two zeros in arithmetic; a `±0.0` literal gives -0.0 for `-0.0 + 0.0`, per morsel on streaming | [zero-sign-streaming](facts/polars-zero-sign-streaming.json) |
| doubles | `nan_kind` | `ONE_NAN` | the sign survives | [nan-sign](facts/polars-nan-sign.json) |
| `sum`, `avg`, `variance`, `std_dev` over ±inf | `nan_creation`, `stat_degenerate` | raise | NaN | [nonfinite-aggregates](facts/polars-nonfinite-aggregates.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | streaming: pairwise per morsel, in turn when grouped, varying between runs; in memory: pairwise, Kahan when grouped | [sum-float-streaming](facts/polars-sum-float-streaming.json), [mean-float-streaming](facts/polars-mean-float-streaming.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo`, `stat_degenerate` | generic properties; NULL for `corr` of one pair | two-pass blocks or Welford by path; NaN for degenerate `corr`; `Decimal` raises on streaming ([PL-5](../../upstream/bugs/PL-5.json)) | [var-std-streaming](facts/polars-var-std-streaming.json), [cov](facts/polars-cov.json), [corr](facts/polars-corr.json) |
| `quantile_disc`, `quantile_cont`, `median` | `quantile_interp` | a value of the input; any double between neighbours | `nearest` by default; `linear` for `median` | [quantile](facts/polars-quantile.json) |
| decimals | result type | the YAML's (`multiply`: s₁ + s₂) | `Decimal(38, max(s₁, s₂))` | [decimal-arith](facts/polars-decimal-arith.json) |
| | `decimal_rescale` | `TIE_AWAY_FROM_ZERO` | `TIE_TO_EVEN` ([ST-8](../../upstream/bugs/ST-8.json)) | |

### NULLs, NaN and order

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `equal`, grouping, `DISTINCT`, joins (`fp64`) | `nan_equality` | `NAN_IS_NAN` | native | [nan-equality](facts/polars-nan-equality.json) |
| `lt`, sorts, `rank`, `median` (`fp64`) | `nan_order` | `GREATEST` | native | [nan-order](facts/polars-nan-order.json) |
| `max`, `greatest`, `arg_max` (`fp64`) | `nan_order` | `GREATEST`: `max(1, NaN)` is NaN | NaN skipped unless all NaN; `nan_max` native | [min-max-nan](facts/polars-min-max-nan.json) |
| `equal`, sorts, grouping (`fp64`) | `zero_sign` | `ONE_ZERO` | one zero; a group key keeps the zero seen first | [zero-order](facts/polars-zero-order.json) |
| sort key | `null_order` | as the key states; `NULLS_LAST` for `UNSPECIFIED` | `NULLS_FIRST` by default in both directions; native with `nulls_last` | [null-order](facts/polars-null-order.json) |
| sort, `fetch` | `tie_order` | any order | stable with `maintain_order`; on streaming unstable above 32 MiB without it | [sort-stability-streaming](facts/polars-sort-stability-streaming.json) |
| strings, booleans | order | code points; `false < true` | native | [string-order](facts/polars-string-order.json) |
| `aggregate` keys, joins | NULL keys | one group; `=` skips NULL | native (`nulls_equal` for `IS NOT DISTINCT FROM`) | [null-keys](facts/polars-null-keys.json) |
| `and`, `or`, `not`, `bool_and`, `bool_or` | | Kleene; aggregates skip NULLs | native | [kleene](facts/polars-kleene.json) |
| `count`, aggregates of no values | | `count` skips NULLs; NULL | native, but `sum` is 0 | [count-empty](facts/polars-count-empty.json) |
| `first`, `last`, `arg_min`, `arg_max` | `tie_pick` | any row | the first (last) in input order, deterministic | [first-last](facts/polars-first-last.json), [arg-min-max](facts/polars-arg-min-max.json) |
| `string_agg`, `array_agg` | `tie_order` | any order | input order; `str.join` skips NULLs | first-last |
| `mode` | `tie_pick` | one value of the tie | every mode, as a list | [mode](facts/polars-mode.json) |
| `rank`, `dense_rank`, `row_number` | | SQL's; NULLs ranked | `rank('min')`, `'dense'`, `'ordinal'`; NULL's rank is NULL; no `ntile`, `percent_rank`, `cume_dist` | [rank](facts/polars-rank.json) |
| `lag`, `first_value`, windowed sums | `tie_order` | the window's order | `.over` in input order | [window-values](facts/polars-window-values.json) |
| `i64` vs `fp64` comparison | | a cast first | compares as `Float64` | [int-float-compare](facts/polars-int-float-compare.json) |

### Strings, dates and casts

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `substring` | `negative_start` | `WRAP_FROM_END`, 1-based | `str.slice`, 0-based, `WRAP_FROM_END` | [substring](facts/polars-substring.json) |
| `strpos` | | 1-based characters, 0 when absent | `str.find`: 0-based bytes, NULL when absent | [strpos](facts/polars-strpos.json) |
| `upper`, `lower` | `char_set` | `UTF8` (Rust's mappings) | native | [case](facts/polars-case.json) |
| `character_length` | | code points | native | [length](facts/polars-length.json) |
| `reverse` | | code points | grapheme clusters | [reverse](facts/polars-reverse.json) |
| `btrim` | | spaces | `strip_chars(' ')` native; `strip_chars()` trims all whitespace | [trim](facts/polars-trim.json) |
| `str_concat` | `null_handling` | `ACCEPT_NULLS` | native; `ignore_nulls=True` for `IGNORE_NULLS` | [concat](facts/polars-concat.json) |
| `starts_with`, `ends_with`, `replace` | `case_sensitivity` | `CASE_SENSITIVE` | native | [match-functions](facts/polars-match-functions.json) |
| `regexp_extract`, `regexp_replace` | | RE2; `''` without a match | Rust `regex`; NULL without a match; `$1` replacements | [regex](facts/polars-regex.json) |
| `levenshtein`, `md5`, `sha256`, `repeat`, `ascii`, `like`, `ilike` | | defined | no expression | [string-functions-missing](facts/polars-string-functions-missing.json) |
| date arithmetic | `date_range` | raise outside 0001 … 9999 | computes past them; huge day counts panic ([PL-2](../../upstream/bugs/PL-2.json)) | [date-range](facts/polars-date-range.json) |
| date + months | | the month's last day where shorter | native | [month-arith](facts/polars-month-arith.json) |
| timestamps | precision | microseconds | `Datetime('us')` | [timestamp-unit](facts/polars-timestamp-unit.json) |
| `date_part`, `date_trunc` | | ISO weeks, floor before 1970 | native | [date-parts](facts/polars-date-parts.json) |
| `strftime` | | opaque | chrono's specifiers | [strftime](facts/polars-strftime.json) |
| `TIME ± INTERVAL`, time zones, invalid dates | `time_interval_months` | refused | refused or raises | [temporal-errors](facts/polars-temporal-errors.json) |
| `cast` `fp64` → integer | `float_to_int` | `TRUNCATE` | native | [cast-double-to-int](facts/polars-cast-double-to-int.json) |
| `cast` (numbers) | `cast_failure` | as stated | `strict=True` throws, `strict=False` returns NULL; `wrap_numerical` wraps integers, saturates doubles | [cast-int](facts/polars-cast-int.json), cast-double-to-int |
| `cast` `i64` → `fp64`, `fp64` → `fp32` | | nearest | native | [cast-to-double](facts/polars-cast-to-double.json) |
| `cast` from and to strings | | the reference's rules | strict parsing; shortest round-trip text; no text to bool or date | [cast-string](facts/polars-cast-string.json) |

### Lists, set operations, frontend and I/O

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `ORDER BY` of lists, `<` of lists | `list_null_order` | NULL in `<`, `GREATEST` in sorts | `LEAST` in sorts; `<`, `min`, `max` of lists raise | [list-order](facts/polars-list-order.json) |
| `list_extract` | indexing | 1-based | `list.get`: 0-based, negative from the end, raises out of range | [list-index](facts/polars-list-index.json) |
| `=` on lists and structs | | structural, NULLs equal | native | [nested-equality](facts/polars-nested-equality.json) |
| `UNNEST` | NULL and empty lists | no row | a NULL row for a NULL list, none for an empty one; native with `keep_nulls=False` | [explode](facts/polars-explode.json) |
| `UNION`, `INTERSECT`, `EXCEPT` | | NULLs equal | `concat`, `unique`, semi/anti joins with `nulls_equal=True` | [set-operations](facts/polars-set-operations.json) |
| sort key | `clustered` | equal keys adjacent | a sort | [clustered](facts/polars-clustered.json) |
| `substring` | `substring_range` | raise outside 32 bits | computes; a negative length raises | [substring-range](facts/polars-substring-range.json) |
| `fp32` arithmetic | | refused (#417) | native single precision; literals take `Float32` | [fp32](facts/polars-fp32.json) |
| types | implicit casts, literals, names | explicit in the plan | wider type; literals adopt the column's; `Int32` literals | [implicit-casts](facts/polars-implicit-casts.json), [literal-types](facts/polars-literal-types.json), [type-names](facts/polars-type-names.json) |
| I/O | formats, object stores, catalogs | outside the plan | Parquet, CSV, IPC, NDJSON, Delta, Iceberg; `storage_options`; `pl.Catalog` | [io](facts/polars-io.json) |

### Execution

| Construct | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `CASE` (`when/then`) | `evaluation_order` | a branch sees only its rows | an elementwise branch is masked on both engines; other branches run on every row | [exec-when-eager](facts/polars-exec-when-eager.json) |
| a subexpression shared by two branches | `evaluation_order` | a branch sees only its rows | CSE hoists it onto every row, so a guarded strict cast raises ([PL-6](../../upstream/bugs/PL-6.json)) | [exec-cse-hoist](facts/polars-exec-cse-hoist.json) |
| stacked filters | `evaluation_order` | a filter's condition sees the rows below it | predicate pushdown merges them; `str.to_integer` raises on removed rows ([PL-7](../../upstream/bugs/PL-7.json)); sverify turns pushdown off | [exec-predicate-pushdown](facts/polars-exec-predicate-pushdown.json) |
