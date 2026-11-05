# Snowflake characterization

What Snowflake does at each of the core's options
([core-semantics.md](../../docs/core-semantics.md)), recorded as facts, one
JSON document each in [facts/](facts/), in the format of
[fact.schema.json](../fact.schema.json) (`python -m sverify_dev.facts` checks
them). They are the evidence for the SQL `sverify.sql.snowflake` writes, and
for a Snowflake profile later.

Snowflake here is 10.40.102, the value of `CURRENT_VERSION()` when the probes
ran on 2026-11-05. The facts' `engine_version` is `10.40.102`. Snowflake is a
service with weekly releases, so a rerun may meet a newer version.

Each fact names the items of the characterization checklist
([../areas.json](../areas.json)) it settles; `python -m sverify_dev.facts
--coverage snowflake` lists them, and the rows of the engine choice tables each
fact settles. Every row and item is settled, all of them by probes.

## How the facts are judged

As DuckDB's ([../duckdb/README.md](../duckdb/README.md#how-the-facts-are-judged)):
`Rel.eval` means Substrait's semantics, each function's extension YAML with
its options; where Substrait leaves a choice open, the reference raises if
engines disagree on an edge case, and otherwise takes the least surprising
value every backend can emulate. A fact's `status` is `no-finding` where
Snowflake gives the reference natively, `shimmed` where sverify's SQL rewrites
the construct to give it, and `open` where Snowflake differs and sverify
refuses the construct or does not write it yet.

## The probes

`python -m sverify_dev.probe_snowflake` (`python/tools/sverify_dev/probe_snowflake.py`)
writes [probes.json](probes.json): 312 SQL queries, each with its result. They
run through the Snowflake CLI (`snow sql -c sverify`, CLI 3.32.1) on an
X-Small warehouse, with the session's `TIMEZONE` set to UTC and the result
cache off; the header of probes.json records the other session parameters
that change results, at the account's defaults. The inputs are literal
`VALUES`, except the `sample-*` probes, which read TPC-H's LINEITEM
(6,001,215 rows) in the shared `SNOWFLAKE_SAMPLE_DATA`, so that a double sum
and the order of ties run on a real, parallel scan. The `writer-*` probes run
SQL that `sverify.sql.snowflake` writes.

CI has no Snowflake account, so no test checks the file is current. Rerun it
from a machine with the connection, after a writer change or to recheck a
new Snowflake version:

```bash
cd python && uv run python -m sverify_dev.probe_snowflake --write
```

`--update` runs only the probes probes.json lacks; `--list` prints the queries
without running them. A full run takes about 90 `snow` calls and three
minutes: a batch of 25 statements is one call, and a failing statement ends
it, so the next call resumes after it.

Four findings are upstream bugs, [SF-1](../../upstream/bugs/SF-1.json) to
[SF-4](../../upstream/bugs/SF-4.json).

## The Snowflake diff, as a table

How Snowflake 10.40.102 compares with the reference, option by option.
"Native" means Snowflake's own SQL gives the reference result; "sverify"
says what its SQL does instead.

| Function (types) | Option | Reference | Snowflake | Fact |
|---|---|---|---|---|
| `add` `subtract` `multiply` `negate` `abs` (integers) | `overflow` | `ERROR` at the width | every integer is `NUMBER(38,0)`, exact; sverify checks 64 bits | [int-arith](facts/snowflake-int-arith.json), [int-abs](facts/snowflake-int-abs.json) |
| `divide` (integers) | rounding, zero, `MIN / -1` | truncate, `ERROR` | `/` is a decimal rounded half up at 6 more places; zero raises; sverify divides through `MOD` | [int-divide](facts/snowflake-int-divide.json) |
| `modulus` (integers) | `division_type`, zero, `MIN % -1` | `TRUNCATE`, `ERROR`, 0 | native | [int-modulus](facts/snowflake-int-modulus.json) |
| `power` (integers) | `overflow` | `ERROR` | a `FLOAT`; sverify multiplies | [int-pow](facts/snowflake-int-pow.json) |
| `shift_left`, `shift_right` | range (ST-1) | 64 bits | 128 bits; negative counts raise; refused | [int-shift](facts/snowflake-int-shift.json) |
| decimals | types, `decimal_rescale`, `overflow` | the YAML's, `TIE_AWAY_FROM_ZERO`, `ERROR` | rescaling native; values past 38 digits kept to 2^127 ([SF-1](../../upstream/bugs/SF-1.json)); not written yet (#27) | [decimal-arith](facts/snowflake-decimal-arith.json) |
| `add` `subtract` `multiply` `divide` (`fp64`) | `rounding` | `TIE_TO_EVEN` | native, folded or executed | [double-arith](facts/snowflake-double-arith.json) |
| | `nan_creation`, `float_overflow` | raise | NaN, `±inf`; sverify checks | double-arith |
| `divide` (`fp64`) | `on_division_by_zero` | `ERROR` | native | [double-divide](facts/snowflake-double-divide.json) |
| `modulus` (`fp64`) | | `fmod` | NaN for an infinite divisor; sverify writes the cases | [double-modulus](facts/snowflake-double-modulus.json) |
| `sqrt`, logs, `asin`, `power` | `on_domain_error`, `on_log_zero` | `ERROR` | native; trigonometry of inf NaN | [math-domain](facts/snowflake-math-domain.json) |
| elementary functions | last bits | the platform's libm | correctly rounded where checked; refused, undocumented | [elem-rounding](facts/snowflake-elem-rounding.json) |
| `round` | `rounding` | `TIE_AWAY_FROM_ZERO` | native, exact near a half | [round](facts/snowflake-round.json) |
| `fp32` | | refused (#417) | no single precision | [fp32](facts/snowflake-fp32.json) |
| `equal`, keys (`fp64`) | `nan_equality` | `NAN_IS_NAN` | native | [nan-equality](facts/snowflake-nan-equality.json) |
| `lt`, sorts, `max` | `nan_order` | `GREATEST` | native | [nan-order](facts/snowflake-nan-order.json) |
| doubles | `zero_sign` | `ONE_ZERO` | -0.0 kept and shown; equal, one group; sverify canonicalises | [zero-sign](facts/snowflake-zero-sign.json), [zero-order](facts/snowflake-zero-order.json) |
| `cast` `fp64` → integer | `float_to_int` | `TRUNCATE` | rounds half away from zero; sverify truncates first | [cast-double-to-int](facts/snowflake-cast-double-to-int.json) |
| casts from and to text | parsing, formatting | the reference's rules | lenient parsing; doubles print 15 digits, timestamps milliseconds | [cast-string](facts/snowflake-cast-string.json) |
| `cast` with `RETURN_NULL` | `try_variants` | NULL | `TRY_CAST` of text only; `TRY_TO_*` | [try-variants](facts/snowflake-try-variants.json) |
| `and`, `or`, `not` | | Kleene | native | [kleene](facts/snowflake-kleene.json) |
| `str_concat` | `null_handling` | `ACCEPT_NULLS` | native; `CONCAT_WS` is NULL too | [concat](facts/snowflake-concat.json) |
| `upper`, `lower` | `char_set` | full mappings | full mappings; sverify raises on non-ASCII | [case](facts/snowflake-case.json) |
| `like`, `strpos`, … | `case_sensitivity` | `CASE_SENSITIVE` | native; `LIKE` escapes only with `ESCAPE` | [match-functions](facts/snowflake-match-functions.json) |
| `substring` | `negative_start` | `WRAP_FROM_END` | start 0 reads as 1; sverify passes starts ≥ 1 | [substring](facts/snowflake-substring.json) |
| | `substring_range` | raise outside `[-2³², 2³²)` | wraps at 32 bits ([SF-2](../../upstream/bugs/SF-2.json)); sverify clamps and raises | [substring-range](facts/snowflake-substring-range.json) |
| `regexp_*` | `regex_dialect` | RE2 | POSIX with Perl classes, ASCII only; no lookaround | [regex](facts/snowflake-regex.json) |
| `md5`, `sha256` | `digests` | hex of UTF-8 | native | [digests](facts/snowflake-digests.json) |
| timestamps | precision | microseconds | nanoseconds by default; sverify writes `TIMESTAMP_NTZ(6)` | [timestamp-precision](facts/snowflake-timestamp-precision.json) |
| date arithmetic | `date_range` | raise outside 0001 … 9999 | computes past both; `DATEADD` wraps at 2³¹ days ([SF-3](../../upstream/bugs/SF-3.json)); sverify range-checks | [date-range](facts/snowflake-date-range.json) |
| `date_part`, `date_trunc` | `week_numbering` | ISO | session parameters; sverify writes the ISO forms | [week-parts](facts/snowflake-week-parts.json) |
| `sum` (integers) | `overflow` | `ERROR` | exact to 2^127; sverify checks 64 bits | [sum-int](facts/snowflake-sum-int.json) |
| `avg` (integers) | `avg_int_result` | the declared type | a decimal; sverify truncates | [avg-int](facts/snowflake-avg-int.json) |
| `sum`, `avg` (`fp64`) | `sum_order` | any order, within #85's bound | varies run to run; refused | [sum-double](facts/snowflake-sum-double.json) |
| `variance`, `std_dev`, `covar_*`, `corr` | `stat_algo` | `StatProps` | the textbook formula ([SF-4](../../upstream/bugs/SF-4.json)); refused | [var-stddev](facts/snowflake-var-stddev.json), [covar](facts/snowflake-covar.json), [corr](facts/snowflake-corr.json) |
| `quantile_cont`, `quantile_disc` | `quantile_interp` | between neighbours | linear at (n - 1)·p | [quantile](facts/snowflake-quantile.json) |
| `first_value`, `last_value` | frame | the plan's | the whole partition by default; sverify writes every frame | [window-values](facts/snowflake-window-values.json) |
| sort key | `null_order` | as stated | `NULLS LAST` ascending by default; sverify states it | [null-order](facts/snowflake-null-order.json) |
| sort | `tie_order` | any order | varies on tables | [sort-stability](facts/snowflake-sort-stability.json) |
| `UNION`, `INTERSECT`, `EXCEPT` | | NULLs equal | native; no `ALL` forms but `UNION ALL` | [set-operations](facts/snowflake-set-operations.json) |
| lists, structs | | | 0-based arrays, NULL lowest; refused | [list-index](facts/snowflake-list-index.json), [list-order](facts/snowflake-list-order.json) |

The rest, among them evaluation order, settings, sizes and the frontend, are
in [facts/](facts/).
