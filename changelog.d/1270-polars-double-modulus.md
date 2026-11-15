### Polars runs `%` of doubles natively under `semantics="polars"`

`Profile.polars` models Polars's `%` of doubles, `x - y * floor(x / y)`, and the Polars engine runs it natively for a column divisor ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)). A zero divisor and an infinite operand raise under the profile, where Polars gives NaN. A literal divisor takes Polars's reciprocal kernel (`49.0 % 49.0` is `49.0`) and is refused with the way out. Under the reference, `%` of doubles stays refused on Polars.
