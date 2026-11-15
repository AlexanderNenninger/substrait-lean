### Polars runs `%` of doubles natively under `semantics="polars"`

`Profile.polars` models Polars's `%` of doubles, `x - y * floor(x / y)` over Polars's own `/`, and the Polars engine runs it natively, for column and literal divisors alike ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270), decision D41: `fp.mod` accepts `division_type: FLOOR`). A zero divisor and an infinite operand raise under the profile, where Polars gives NaN. Under the reference, `%` of doubles stays refused on Polars.
