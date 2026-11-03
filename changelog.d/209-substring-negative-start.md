### `substring` counts a negative start from the end

A plan that omits `negative_start` counts a negative start from the end of
the string, as DuckDB does: `substring('hello', -2, 2)` is `'lo'` (#209).
A plan that asks for `LEFT_OF_BEGINNING` gets that, and `ERROR` is refused.
The SQL writers and Polars rewrite the start before calling the engine's
`substring`.
