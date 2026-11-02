### The SQL lift reads numeric functions, DISTINCT and FILTER in aggregates

The SQL lift now reads (#240):
- **Numbers:** `power` (`**`, `pow`), `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`, `greatest`, `least`, `nullif`, and `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`.
- **Comparisons:** `IS [NOT] DISTINCT FROM`.
- **Aggregates:** `DISTINCT` in every aggregate, and `FILTER (WHERE …)`.

They have DuckDB's meanings:
- `power` and the elementary functions compute in doubles;
- `log(x)` is base 10;
- `greatest` and `least` leave NULLs out;
- `sign` is a TINYINT, 0 for NaN;
- `isnan(NULL)` is NULL.

Outside their domain (`sqrt(-1)`, `ln(0)`), DuckDB gives NaN or `-inf`. The plan states that preference and then `ERROR`, the reference's, which the model takes, so `verify` reports such rows as possible errors.
