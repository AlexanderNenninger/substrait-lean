### `verify` proves that a `SUM` of a 0/1 flag fits 64 bits

Counting rows with `SUM(CASE WHEN … THEN 1 ELSE 0 END)` no longer gets a
"SUM overflow" warning. A group has fewer than 2⁶³ rows, as `COUNT(*)` is a
BIGINT in the reference and in every engine, so a `SUM` of values in
`[-1, 1]` fits 64 bits without a row cap. The size hypothesis of the
reference semantics now states that bound. Values in a wider range still
need `sv.max_rows(n)` to be proved
([#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)).
