### Polars computes shifts, `ROUND` and `log(x, b)` natively

On Polars, `<<` and `>>`, `ROUND(x, d)` for `0 ≤ d ≤ 22` and `log(x, b)` run
as Polars expressions where they called Python per row or numpy per batch
([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
The values are the same. On a million rows the shifts take 1 to 2 ms, down
from 56 to 109 ms.
