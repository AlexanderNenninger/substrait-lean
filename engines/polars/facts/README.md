# Polars characterization

What Polars does at each of the core's options
([core-semantics.md](../../../docs/core-semantics.md)), recorded as facts, one
JSON document each in [facts/](./), in the format of
[fact.schema.json](../../../characterization/fact.schema.json) (`python -m sverify_dev.facts` checks
them). They are the evidence `Profile.polars`
(`engines/polars/Sverify/Polars/Profile.lean`, the profile
`verify(semantics="polars")` will check under, #2545; [Polars as a
profile](../../../docs/engine-profiles.md#polars-as-a-profile)) and its row of the
realizability table are built from.

Polars here is version 2.1.0, the version `python/uv.lock` pins: the Python
package `polars` 2.1.0 and its Rust crates at tag
[`py-2.1.0`](https://github.com/pola-rs/polars/tree/py-2.1.0) (commit
`7f902bd3`). The facts' `engine_version` is `py-2.1.0`. What is probed is
Polars's expression API (`pl.col(...)`, `DataFrame.select`, `group_by`,
`sort`, `join`), which `sverify_polars.engine` writes plans to; Polars's
SQL interface (`pl.SQLContext`) is out of scope.

Each fact names the items of the characterization checklist
([areas.json](../../../characterization/areas.json)) it settles; `python -m sverify_dev.facts
--coverage polars` lists them, and the items no fact settles yet.

## How the facts are judged

The facts are judged as every engine's are
([../README.md](../../../characterization/README.md#how-the-facts-are-judged)). A fact's `status` is `open` where Polars differs from the reference
and the profile has not decided how to bridge it, and `no-finding` where
Polars gives the reference natively.

## The probes

`python -m sverify_dev.probe_polars` (`python/tools/sverify_dev/probe_polars.py`)
writes [probes.json](../probes/probes.json), which `engines/polars/tests/test_probe_polars.py` checks is
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

## Polars's own tests

`python -m sverify_dev.polars_tests` (`python/tools/sverify_dev/polars_tests.py`, #2615)
replays a slice of Polars's Python unit tests at `py-2.1.0` (MIT,
[LICENSE-polars](../replay/LICENSE-polars)): each query a passing test collects is
translated to Ibis, verified under `semantics="polars"`, and compared three ways: the
model, sverify's run on Polars, and Polars's own result on its developers' inputs. A
collect where the model and the run agree with each other but not with Polars is triaged
in [triage.json](../replay/triage.json), into a translation gap, a fact or a bug. The
ledgers are [../replay/](../replay/), one per module, and the run belongs on homelab:

```bash
cd python && uv run python -m sverify_dev.polars_tests --write
```

<!-- replay:start -->
Totals over 10736 tests of Polars's `py-2.1.0` suite: 817 agree, 0 disagree, 3 unattributed, 691 refused, 42 unproved, 9183 skipped.

| Module | Agree | Disagree | Unattributed | Refused | Unproved | Skipped |
|---|---:|---:|---:|---:|---:|---:|
| [expr/test_arity](../replay/expr__test_arity.json) | 3 | 0 | 0 | 1 | 0 | 8 |
| [expr/test_binary](../replay/expr__test_binary.json) | 0 | 0 | 0 | 0 | 0 | 24 |
| [expr/test_dtype_of](../replay/expr__test_dtype_of.json) | 0 | 0 | 0 | 0 | 0 | 1 |
| [expr/test_dunders](../replay/expr__test_dunders.json) | 2 | 0 | 0 | 0 | 0 | 0 |
| [expr/test_expr_apply_eval](../replay/expr__test_expr_apply_eval.json) | 1 | 0 | 0 | 0 | 0 | 0 |
| [expr/test_expr_multi_cols](../replay/expr__test_expr_multi_cols.json) | 0 | 0 | 0 | 0 | 0 | 5 |
| [expr/test_exprs](../replay/expr__test_exprs.json) | 7 | 0 | 0 | 1 | 1 | 131 |
| [expr/test_is_sorted](../replay/expr__test_is_sorted.json) | 0 | 0 | 0 | 0 | 0 | 17 |
| [expr/test_literal](../replay/expr__test_literal.json) | 0 | 0 | 0 | 0 | 0 | 47 |
| [expr/test_meta](../replay/expr__test_meta.json) | 0 | 0 | 0 | 0 | 0 | 4 |
| [expr/test_pipe_with_dtype](../replay/expr__test_pipe_with_dtype.json) | 0 | 0 | 0 | 0 | 0 | 14 |
| [expr/test_serde](../replay/expr__test_serde.json) | 0 | 0 | 0 | 0 | 0 | 13 |
| [expr/test_udfs](../replay/expr__test_udfs.json) | 0 | 0 | 0 | 0 | 0 | 8 |
| [functions/as_datatype/test_concat_arr](../replay/functions__as_datatype__test_concat_arr.json) | 0 | 0 | 0 | 0 | 0 | 10 |
| [functions/as_datatype/test_concat_list](../replay/functions__as_datatype__test_concat_list.json) | 1 | 0 | 0 | 0 | 0 | 17 |
| [functions/as_datatype/test_concat_str](../replay/functions__as_datatype__test_concat_str.json) | 0 | 0 | 0 | 0 | 0 | 16 |
| [functions/as_datatype/test_datetime](../replay/functions__as_datatype__test_datetime.json) | 0 | 0 | 0 | 0 | 0 | 23 |
| [functions/as_datatype/test_duration](../replay/functions__as_datatype__test_duration.json) | 0 | 0 | 0 | 0 | 0 | 15 |
| [functions/as_datatype/test_format](../replay/functions__as_datatype__test_format.json) | 0 | 0 | 0 | 0 | 0 | 1 |
| [functions/as_datatype/test_struct](../replay/functions__as_datatype__test_struct.json) | 0 | 0 | 0 | 128 | 0 | 43 |
| [functions/as_datatype/test_time](../replay/functions__as_datatype__test_time.json) | 0 | 0 | 0 | 0 | 0 | 1 |
| [functions/range/test_date_range](../replay/functions__range__test_date_range.json) | 0 | 0 | 0 | 0 | 0 | 15 |
| [functions/range/test_date_ranges](../replay/functions__range__test_date_ranges.json) | 0 | 0 | 0 | 0 | 0 | 13 |
| [functions/range/test_datetime_range](../replay/functions__range__test_datetime_range.json) | 0 | 0 | 0 | 0 | 0 | 38 |
| [functions/range/test_datetime_ranges](../replay/functions__range__test_datetime_ranges.json) | 0 | 0 | 0 | 0 | 0 | 94 |
| [functions/range/test_int_range](../replay/functions__range__test_int_range.json) | 1 | 0 | 0 | 0 | 0 | 32 |
| [functions/range/test_linear_space](../replay/functions__range__test_linear_space.json) | 9 | 0 | 0 | 121 | 0 | 212 |
| [functions/range/test_time_range](../replay/functions__range__test_time_range.json) | 0 | 0 | 0 | 0 | 0 | 18 |
| [functions/test_business_day_count](../replay/functions__test_business_day_count.json) | 0 | 0 | 0 | 0 | 0 | 10 |
| [functions/test_col](../replay/functions__test_col.json) | 3 | 0 | 0 | 0 | 0 | 3 |
| [functions/test_concat](../replay/functions__test_concat.json) | 24 | 0 | 0 | 0 | 0 | 31 |
| [functions/test_cum_count](../replay/functions__test_cum_count.json) | 0 | 0 | 0 | 0 | 0 | 6 |
| [functions/test_cumulative_eval](../replay/functions__test_cumulative_eval.json) | 0 | 0 | 0 | 0 | 0 | 6 |
| [functions/test_ewm_by](../replay/functions__test_ewm_by.json) | 0 | 0 | 0 | 0 | 0 | 3 |
| [functions/test_functions](../replay/functions__test_functions.json) | 11 | 0 | 0 | 0 | 2 | 63 |
| [functions/test_horizontal](../replay/functions__test_horizontal.json) | 0 | 0 | 0 | 0 | 0 | 5 |
| [functions/test_lit](../replay/functions__test_lit.json) | 0 | 0 | 0 | 0 | 0 | 43 |
| [functions/test_nth](../replay/functions__test_nth.json) | 4 | 0 | 0 | 0 | 0 | 1 |
| [functions/test_repeat](../replay/functions__test_repeat.json) | 0 | 0 | 0 | 0 | 0 | 68 |
| [functions/test_union](../replay/functions__test_union.json) | 19 | 0 | 0 | 0 | 0 | 14 |
| [functions/test_when_then](../replay/functions__test_when_then.json) | 175 | 0 | 0 | 127 | 2 | 414 |
| [functions/test_wildcard_expansion](../replay/functions__test_wildcard_expansion.json) | 0 | 0 | 0 | 0 | 0 | 10 |
| [operations/aggregation/test_aggregations](../replay/operations__aggregation__test_aggregations.json) | 17 | 0 | 0 | 6 | 3 | 1015 |
| [operations/aggregation/test_folds](../replay/operations__aggregation__test_folds.json) | 0 | 0 | 0 | 0 | 0 | 4 |
| [operations/aggregation/test_horizontal](../replay/operations__aggregation__test_horizontal.json) | 23 | 0 | 0 | 4 | 2 | 60 |
| [operations/aggregation/test_implode](../replay/operations__aggregation__test_implode.json) | 1 | 0 | 0 | 1 | 0 | 3 |
| [operations/aggregation/test_vertical](../replay/operations__aggregation__test_vertical.json) | 4 | 0 | 0 | 1 | 0 | 11 |
| [operations/arithmetic/test_arithmetic](../replay/operations__arithmetic__test_arithmetic.json) | 29 | 0 | 0 | 26 | 3 | 283 |
| [operations/arithmetic/test_array](../replay/operations__arithmetic__test_array.json) | 0 | 0 | 0 | 0 | 0 | 117 |
| [operations/arithmetic/test_list](../replay/operations__arithmetic__test_list.json) | 0 | 0 | 0 | 6 | 0 | 154 |
| [operations/arithmetic/test_neg](../replay/operations__arithmetic__test_neg.json) | 8 | 0 | 0 | 2 | 1 | 2 |
| [operations/arithmetic/test_pos](../replay/operations__arithmetic__test_pos.json) | 1 | 0 | 0 | 0 | 0 | 2 |
| [operations/arithmetic/test_pow](../replay/operations__arithmetic__test_pow.json) | 0 | 0 | 0 | 0 | 0 | 1 |
| [operations/test_cast](../replay/operations__test_cast.json) | 4 | 0 | 0 | 25 | 10 | 926 |
| [operations/test_comparison](../replay/operations__test_comparison.json) | 207 | 0 | 0 | 146 | 1 | 266 |
| [operations/test_fill_null](../replay/operations__test_fill_null.json) | 2 | 0 | 0 | 0 | 0 | 16 |
| [operations/test_filter](../replay/operations__test_filter.json) | 9 | 0 | 0 | 2 | 1 | 2830 |
| [operations/test_group_by](../replay/operations__test_group_by.json) | 66 | 0 | 2 | 12 | 7 | 508 |
| [operations/test_is_in](../replay/operations__test_is_in.json) | 0 | 0 | 0 | 0 | 0 | 687 |
| [operations/test_is_null](../replay/operations__test_is_null.json) | 1 | 0 | 0 | 0 | 1 | 1 |
| [operations/test_join](../replay/operations__test_join.json) | 84 | 0 | 0 | 52 | 2 | 437 |
| [operations/test_over](../replay/operations__test_over.json) | 1 | 0 | 0 | 0 | 0 | 35 |
| [operations/test_select](../replay/operations__test_select.json) | 2 | 0 | 0 | 0 | 0 | 6 |
| [operations/test_sort](../replay/operations__test_sort.json) | 82 | 0 | 0 | 23 | 1 | 147 |
| [operations/test_window](../replay/operations__test_window.json) | 6 | 0 | 1 | 5 | 3 | 111 |
| [operations/test_with_columns](../replay/operations__test_with_columns.json) | 3 | 0 | 0 | 0 | 0 | 5 |
| [operations/unique/test_is_unique](../replay/operations__unique__test_is_unique.json) | 1 | 0 | 0 | 0 | 0 | 10 |
| [operations/unique/test_n_unique](../replay/operations__unique__test_n_unique.json) | 0 | 0 | 0 | 2 | 0 | 9 |
| [operations/unique/test_unique](../replay/operations__unique__test_unique.json) | 6 | 0 | 0 | 0 | 2 | 35 |
| [operations/unique/test_unique_counts](../replay/operations__unique__test_unique_counts.json) | 0 | 0 | 0 | 0 | 0 | 5 |
<!-- replay:end -->

## The Polars diff, as a table

How Polars 2.1.0 compares with the reference, option by option. "Native"
means Polars's own expression gives the reference result.

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `add` `subtract` `multiply` `negate` (`i8`…`i64`) | `overflow` | `ERROR` | `SILENT`, at the column's width; `**` too | [int-arith](polars-int-arith.json) |
| `abs` (`i8`…`i64`) | `overflow` | `ERROR` | `abs(MIN)` is `MIN` | [int-abs](polars-int-abs.json) |
| `divide` (`i8`…`i64`) | rounding | truncate | `//` floors; no truncating division in the Python API | [int-divide](polars-int-divide.json) |
| | `on_division_by_zero` | `ERROR` | `NULL` | |
| | `overflow` (`MIN / -1`) | `ERROR` | wraps to `MIN` | |
| `modulus` (`i8`…`i64`) | `division_type` | `TRUNCATE` | `FLOOR` | [int-modulus](polars-int-modulus.json) |
| | `on_division_by_zero` | `ERROR` | `NULL` | |
| | `MIN % -1` | 0 | 0, native | |
| `/` on integers | | an integer `divide` | a `Float64` division; a literal divisor takes the reciprocal, as below | [int-true-divide](polars-int-true-divide.json) |
| `shift_left`, `shift_right` | range (ST-1) | drop bits, raise outside `[0, 63]` | no shift expressions | [int-shift](polars-int-shift.json) |
| `sum` (`i8`…`i64`) | `overflow` | `ERROR`, at the input's type | `i8`, `i16` widen to `i64`; `i32`, `i64` wrap | [sum-int](polars-sum-int.json) |
| `sum` (all) | no values | NULL | 0 (Substrait's `sum0`) | sum-int, [sum-float-streaming](polars-sum-float-streaming.json) |
| `avg` (integers) | `avg_int_result` | the declared type | `Float64` | [avg-int](polars-avg-int.json) |
| `add` `subtract` `multiply` (`fp64`) | `nan_creation` | raise | NaN (IEEE) | [double-arith](polars-double-arith.json) |
| `divide` (`fp64`) | `on_division_by_zero` | `ERROR` | `IEEE`; `±inf / ±inf` is NaN | [double-divide](polars-double-divide.json) |
| `divide`, `modulus` by a literal (`fp32`, `fp64`) | `rounding`, `nan_creation` | one rounding; no NaN from finite operands | `x · (1 / c)`: an ulp off, NaN or inf for a subnormal `c`, `49.0 % 49.0` is 49.0; on streaming per morsel, so it depends on the thread count ([PL-3](../../../upstream/bugs/PL-3.json)) | [double-scalar-divisor](polars-double-scalar-divisor.json) |
| `modulus` (`fp64`) | | truncated (`fmod`), zero divisor raises | `x - y·floor(x / y)`: floor sign, NaN for `x % 0` and finite `x % ±inf` ([PL-1](../../../upstream/bugs/PL-1.json)) | [double-modulus](polars-double-modulus.json) |
| `sqrt`, logs, `asin`, `acos`, `power`, trig of ±inf | `on_domain_error` | `ERROR` | `NAN` | [math-domain](polars-math-domain.json) |
| `ln`, `log10`, `log2` | `on_log_zero` | `ERROR` | `MINUS_INFINITY` | math-domain |
| `log10`, `log2` | last bits | the platform's `log10`, `log2` | `ln(x) / ln(b)`, an ulp off at times; on `Float32` the natural `log()` too ([PL-4](../../../upstream/bugs/PL-4.json)) | [log-base](polars-log-base.json) |
| `atan2` | `atan2(0, 0)` | raise | 0 | [atan2](polars-atan2.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | `TIE_TO_EVEN` by default; native with `mode='half_away_from_zero'` | [round](polars-round.json) |
| `round` to `d` digits | | `TIE_AWAY_FROM_ZERO`, `d < 0` allowed | `op(x · 10ᵈ) / 10ᵈ`; `d < 0` refused by the API | [round-digits](polars-round-digits.json) |
| `floor`, `ceil`, `exp`, `atan` | | | native | round, math-domain |
| doubles | `zero_sign` | `ONE_ZERO` | two zeros in arithmetic; a `±0.0` literal gives -0.0 for `-0.0 + 0.0`, per morsel on streaming | [zero-sign-streaming](polars-zero-sign-streaming.json) |
| doubles | `nan_kind` | `ONE_NAN` | the sign survives | [nan-sign](polars-nan-sign.json) |
| `sum`, `avg`, `variance`, `std_dev` over ±inf | `nan_creation` | raise | NaN | [nonfinite-aggregates](polars-nonfinite-aggregates.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | streaming: pairwise per morsel, in turn when grouped, varying between runs; in memory: pairwise, Kahan when grouped | [sum-float-streaming](polars-sum-float-streaming.json), [mean-float-streaming](polars-mean-float-streaming.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo`, `stat_degenerate` | generic properties; NULL for `corr` of one pair | two-pass blocks or Welford by path; NaN for degenerate `corr`; `Decimal` raises on streaming ([PL-5](../../../upstream/bugs/PL-5.json)) | [var-std-streaming](polars-var-std-streaming.json), [cov](polars-cov.json), [corr](polars-corr.json) |
| `quantile_disc`, `quantile_cont`, `median` | `quantile_interp` | a value of the input; any double between neighbours | `nearest` by default; `linear` for `median` | [quantile](polars-quantile.json) |
| decimals | result type | the YAML's (`multiply`: s₁ + s₂) | `Decimal(38, max(s₁, s₂))` | [decimal-arith](polars-decimal-arith.json) |
| | `decimal_rescale` | `TIE_AWAY_FROM_ZERO` | `TIE_TO_EVEN` ([ST-8](../../../upstream/bugs/ST-8.json)) | |

### NULLs, NaN and order

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `equal`, grouping, `DISTINCT`, joins (`fp64`) | `nan_equality` | `NAN_IS_NAN` | native | [nan-equality](polars-nan-equality.json) |
| `lt`, sorts, `rank`, `median` (`fp64`) | `nan_order` | `GREATEST` | native | [nan-order](polars-nan-order.json) |
| `max`, `greatest`, `arg_max` (`fp64`) | `nan_order` | `GREATEST`: `max(1, NaN)` is NaN | NaN skipped unless all NaN; `nan_max` native | [min-max-nan](polars-min-max-nan.json) |
| `equal`, sorts, grouping (`fp64`) | `zero_sign` | `ONE_ZERO` | one zero; a group key keeps the zero seen first | [zero-order](polars-zero-order.json) |
| sort key | `null_order` | as the key states; `NULLS_LAST` for `UNSPECIFIED` | `NULLS_FIRST` by default in both directions; native with `nulls_last` | [null-order](polars-null-order.json) |
| sort, `fetch` | `tie_order` | any order | stable with `maintain_order`; on streaming unstable above 32 MiB without it | [sort-stability-streaming](polars-sort-stability-streaming.json) |
| strings, booleans | order | code points; `false < true` | native | [string-order](polars-string-order.json) |
| `aggregate` keys, joins | NULL keys | one group; `=` skips NULL | native (`nulls_equal` for `IS NOT DISTINCT FROM`) | [null-keys](polars-null-keys.json) |
| `and`, `or`, `not`, `bool_and`, `bool_or` | | Kleene; aggregates skip NULLs | native | [kleene](polars-kleene.json) |
| `count`, aggregates of no values | | `count` skips NULLs; NULL | native, but `sum` is 0 | [count-empty](polars-count-empty.json) |
| `first`, `last`, `arg_min`, `arg_max` | `tie_pick` | any row | the first (last) in input order, deterministic | [first-last](polars-first-last.json), [arg-min-max](polars-arg-min-max.json) |
| `string_agg`, `array_agg` | `tie_order` | any order | input order; `str.join` skips NULLs | first-last |
| `mode` | `tie_pick` | one value of the tie | every mode, as a list | [mode](polars-mode.json) |
| `rank`, `dense_rank`, `row_number` | | SQL's; NULLs ranked | `rank('min')`, `'dense'`, `'ordinal'`; NULL's rank is NULL; no `ntile`, `percent_rank`, `cume_dist` | [rank](polars-rank.json) |
| `lag`, `first_value`, windowed sums | `tie_order` | the window's order | `.over` in input order | [window-values](polars-window-values.json) |
| `i64` vs `fp64` comparison | | a cast first | compares as `Float64` | [int-float-compare](polars-int-float-compare.json) |

### Strings, dates and casts

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `substring` | `negative_start` | `WRAP_FROM_END`, 1-based | `str.slice`, 0-based, `WRAP_FROM_END` | [substring](polars-substring.json) |
| `strpos` | | 1-based characters, 0 when absent | `str.find`: 0-based bytes, NULL when absent | [strpos](polars-strpos.json) |
| `upper`, `lower` | `char_set` | `UTF8` (Rust's mappings) | native | [case](polars-case.json) |
| `character_length` | | code points | native | [length](polars-length.json) |
| `reverse` | | code points | grapheme clusters | [reverse](polars-reverse.json) |
| `btrim` | | spaces | `strip_chars(' ')` native; `strip_chars()` trims all whitespace | [trim](polars-trim.json) |
| `str_concat` | `null_handling` | `ACCEPT_NULLS` | native; `ignore_nulls=True` for `IGNORE_NULLS` | [concat](polars-concat.json) |
| `starts_with`, `ends_with`, `replace` | `case_sensitivity` | `CASE_SENSITIVE` | native | [match-functions](polars-match-functions.json) |
| `regexp_extract`, `regexp_replace` | | RE2; `''` without a match | Rust `regex`; NULL without a match; `$1` replacements | [regex](polars-regex.json) |
| `levenshtein`, `md5`, `sha256`, `repeat`, `ascii`, `like`, `ilike` | | defined | no expression | [string-functions-missing](polars-string-functions-missing.json) |
| date arithmetic | `date_range` | raise outside 0001 … 9999 | computes past them; huge day counts panic ([PL-2](../../../upstream/bugs/PL-2.json)) | [date-range](polars-date-range.json) |
| date + months | | the month's last day where shorter | native | [month-arith](polars-month-arith.json) |
| timestamps | precision | microseconds | `Datetime('us')` | [timestamp-unit](polars-timestamp-unit.json) |
| `date_part`, `date_trunc` | | ISO weeks, floor before 1970 | native | [date-parts](polars-date-parts.json) |
| `strftime` | | opaque | chrono's specifiers | [strftime](polars-strftime.json) |
| `TIME ± INTERVAL`, time zones, invalid dates | `time_interval_months` | refused | refused or raises | [temporal-errors](polars-temporal-errors.json) |
| `cast` `fp64` → integer | `float_to_int` | `TRUNCATE` | native | [cast-double-to-int](polars-cast-double-to-int.json) |
| `cast` (numbers) | `cast_failure` | as stated | `strict=True` throws, `strict=False` returns NULL; `wrap_numerical` wraps integers, saturates doubles | [cast-int](polars-cast-int.json), cast-double-to-int |
| `cast` `i64` → `fp64`, `fp64` → `fp32` | | nearest | native | [cast-to-double](polars-cast-to-double.json) |
| `cast` from and to strings | | the reference's rules | strict parsing; shortest round-trip text; no text to bool or date | [cast-string](polars-cast-string.json) |

### Lists, set operations, frontend and I/O

| Function (types) | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `ORDER BY` of lists, `<` of lists | `list_null_order` | NULL in `<`, `GREATEST` in sorts | `LEAST` in sorts; `<`, `min`, `max` of lists raise | [list-order](polars-list-order.json) |
| `list_extract` | indexing | 1-based | `list.get`: 0-based, negative from the end, raises out of range | [list-index](polars-list-index.json) |
| `=` on lists and structs | | structural, NULLs equal | native | [nested-equality](polars-nested-equality.json) |
| `UNNEST` | NULL and empty lists | no row | a NULL row for a NULL list, none for an empty one; native with `keep_nulls=False` | [explode](polars-explode.json) |
| `UNION`, `INTERSECT`, `EXCEPT` | | NULLs equal | `concat`, `unique`, semi/anti joins with `nulls_equal=True` | [set-operations](polars-set-operations.json) |
| sort key | `clustered` | equal keys adjacent | a sort | [clustered](polars-clustered.json) |
| `substring` | `substring_range` | raise outside 32 bits | computes; a negative length raises | [substring-range](polars-substring-range.json) |
| `fp32` arithmetic | | refused (#417) | native single precision; literals take `Float32` | [fp32](polars-fp32.json) |
| types | implicit casts, literals, names | explicit in the plan | wider type; literals adopt the column's; `Int32` literals | [implicit-casts](polars-implicit-casts.json), [literal-types](polars-literal-types.json), [type-names](polars-type-names.json) |
| I/O | formats, object stores, catalogs | outside the plan | Parquet, CSV, IPC, NDJSON, Delta, Iceberg; `storage_options`; `pl.Catalog` | [io](polars-io.json) |

### Execution

| Construct | Option | Reference | Polars | Fact |
|---|---|---|---|---|
| `CASE` (`when/then`) | `evaluation_order` | a branch sees only its rows | an elementwise branch is masked on both engines; other branches run on every row | [exec-when-eager](polars-exec-when-eager.json) |
| a subexpression shared by two branches | `evaluation_order` | a branch sees only its rows | CSE hoists it onto every row, so a guarded strict cast raises ([PL-6](../../../upstream/bugs/PL-6.json)) | [exec-cse-hoist](polars-exec-cse-hoist.json) |
| stacked filters | `evaluation_order` | a filter's condition sees the rows below it | predicate pushdown merges them; `str.to_integer` raises on removed rows ([PL-7](../../../upstream/bugs/PL-7.json)); sverify turns pushdown off | [exec-predicate-pushdown](polars-exec-predicate-pushdown.json) |
