### Polars tables no longer name a `column_divisor` shim

The Polars tables listed a `column_divisor` shim for `%` of doubles that nothing implemented. The row now says what the engine does: Polars refuses `%` of doubles until `Profile.polars` models the floored `%` ([#1270](https://github.com/AlexanderNenninger/substrait-lean/issues/1270)).
