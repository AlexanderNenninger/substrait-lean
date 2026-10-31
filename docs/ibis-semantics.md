# What an Ibis expression means to `verify`

`sverify.verify(expr)` compiles an Ibis expression with the vendored producer
(`sverify.ibis_substrait`), not with Ibis's SQL for some backend. A proof is
about the plan that producer writes, under `Rel.eval`. So the meaning of an
Ibis expression is the producer's, and it is the same whichever Ibis backend
the expression came from.

Where Ibis backends disagree (chapter 15 of the notebook tour,
`notebooks/15_backend_semantics.py`), this table says which meaning
`verify` takes. `python/tests/test_ibis_semantics.py` runs each row through the
producer and checks Lean's evaluation against it.

| operation | meaning in `verify` | DataFusion | DuckDB | Polars |
|---|---|---|---|---|
| `a % b` (integers) | truncating: `-7 % 2 = -1` | same | same | floor (`+1`) |
| `a // b` (integers) | floor, exact in 64 bits: `-7 // 2 = -4` | same | same | same |
| `a % 0`, `a // 0` | error (division by zero) | error | conversion error | NULL |
| `s.length()` | code points: `'é'` is 1, `'🎉'` is 1 | same | same | bytes |
| `s.find(t)` | 0-based, −1 if absent, NULL for a NULL string | same | same | −1 for NULL |
| `s.substr(i, n)` | 0-based start | same | same | same |
| `s.like(p)` | `\` escapes the next character | same | no escape | no LIKE |
| `x.nunique()` | NULL is not a value | same | same | counts NULL |
| `v.round()` | half away from zero: `2.5 → 3` | same | same | half to even |
| `v.cast("int64")` (double) | truncates; NaN, ±inf and out-of-range values are an error | same (error) | rounds half to even | truncates |
| `v == 0.0` with `v = -0.0` | true: one zero (#89) | false (total order) | true | true |
| `x == ibis.null()` | `x IS NULL` (TRUE for NULL rows) | same | same | same |
| `ibis.row_number()` | 0-based | same | same | same |
| `order_by(...)` | NULLs last in both directions | same | same | same |
| window with `order_by`, no frame | the whole partition | same | same | same |
| 64-bit overflow of `+ - *` | a warning: DataFusion wraps around (#23 makes this per engine) | wraps | error | wraps |
| `v.max()` of doubles | refused (`max of doubles is not supported`) | NaN | NaN | skips NaN |
| `ts.day_of_week.index()` | refused by the producer | Monday = 0 | Monday = 0 | Monday = 0 |
| `s.upper()`, `s.lower()`, `re_search` | Rust's case mapping and `regex` classes; SQL engines raise on non-ASCII text (#70) | same | utf8proc, RE2 | same |

"Same" means the backend's Ibis result agrees with `verify`'s meaning on the
notebook's edge rows. A **refused** operation is outside what `verify` can
give a backend-independent meaning today.

Which Ibis backends implement this semantics fully: none of them on every
row. Ibis-on-DataFusion is closest (it differs on `-0.0 == 0.0` and on
`max` of NaN). To run a verified expression with exactly this meaning, run
the plan, not the Ibis expression: `sverify.run_plan(con, plan, engine)` on
DataFusion, DuckDB or Polars, whose translations raise rather than differ.
