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
its options; where Substrait leaves a choice open, the reference takes the
least surprising one every backend can emulate; an engine's profile is a diff
against the reference. A fact's `status` is `open` where Polars differs from
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
| `/` on integers | | an integer `divide` | a `Float64` division | [int-true-divide](facts/polars-int-true-divide.json) |
| `shift_left`, `shift_right` | range (ST-1) | drop bits, raise outside `[0, 63]` | no shift expressions | [int-shift](facts/polars-int-shift.json) |
| `sum` (`i8`…`i64`) | `overflow` | `ERROR`, at the input's type | `i8`, `i16` widen to `i64`; `i32`, `i64` wrap | [sum-int](facts/polars-sum-int.json) |
| `sum` (all) | no values | NULL | 0 (Substrait's `sum0`) | sum-int, [sum-float](facts/polars-sum-float.json) |
| `avg` (integers) | `avg_int_result` | the declared type | `Float64` | [avg-int](facts/polars-avg-int.json) |
| `add` `subtract` `multiply` (`fp64`) | `nan_creation` | raise | NaN (IEEE) | [double-arith](facts/polars-double-arith.json) |
| `divide` (`fp64`) | `on_division_by_zero` | `ERROR` | `IEEE`; `±inf / ±inf` is NaN | [double-divide](facts/polars-double-divide.json) |
| `modulus` (`fp64`) | | truncated (`fmod`), zero divisor raises | `x - y·floor(x / y)`: floor sign, NaN for `x % 0` and finite `x % ±inf` ([PL-1](../../upstream/bugs/PL-1.json)) | [double-modulus](facts/polars-double-modulus.json) |
| `sqrt`, logs, `asin`, `acos`, `power`, trig of ±inf | `on_domain_error` | `ERROR` | `NAN` | [math-domain](facts/polars-math-domain.json) |
| `ln`, `log10`, `log2` | `on_log_zero` | `ERROR` | `MINUS_INFINITY` | math-domain |
| `log10`, `log2` | last bits | the platform's `log10`, `log2` | `ln(x) / ln(b)`, an ulp off at times | [log-base](facts/polars-log-base.json) |
| `atan2` | `atan2(0, 0)` | raise | 0 | [atan2](facts/polars-atan2.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | `TIE_TO_EVEN` by default; native with `mode='half_away_from_zero'` | [round](facts/polars-round.json) |
| `round` to `d` digits | | `TIE_AWAY_FROM_ZERO`, `d < 0` allowed | `op(x · 10ᵈ) / 10ᵈ`; `d < 0` refused by the API | [round-digits](facts/polars-round-digits.json) |
| `floor`, `ceil`, `exp`, `atan` | | | native | round, math-domain |
| doubles | `zero_sign` | `ONE_ZERO` | two zeros in arithmetic | [zero-sign](facts/polars-zero-sign.json) |
| doubles | `nan_kind` | `ONE_NAN` | the sign survives | [nan-sign](facts/polars-nan-sign.json) |
| `sum`, `avg`, `variance`, `std_dev` over ±inf | `nan_creation`, `stat_degenerate` | raise | NaN | [nonfinite-aggregates](facts/polars-nonfinite-aggregates.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | pairwise, Kahan when grouped | [sum-float](facts/polars-sum-float.json), [mean-float](facts/polars-mean-float.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo`, `stat_degenerate` | generic properties; NULL for `corr` of one pair | two-pass blocks or Welford by path; NaN for degenerate `corr` | [var-std](facts/polars-var-std.json), [cov](facts/polars-cov.json), [corr](facts/polars-corr.json) |
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
| sort, `fetch` | `tie_order` | any order | stable on the probe; guaranteed with `maintain_order` | [sort-stability](facts/polars-sort-stability.json) |
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
