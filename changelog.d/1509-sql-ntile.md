### SQL `NTILE(k)` is proved

The SQL lift wrote `NTILE` as arithmetic over `ROW_NUMBER` and `COUNT`, whose
product was reported as a possible overflow that no precondition could rule
out, so no SQL plan with `NTILE` was proved. It now writes the model's `ntile`
window function, the SQL standard's buckets, as the Ibis producer does
([#1509](https://github.com/AlexanderNenninger/substrait-lean/issues/1509)).
