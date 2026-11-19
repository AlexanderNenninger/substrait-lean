### `lean_values` raises on a window's aggregates too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in the argument or filter of a window's aggregate, on the frame of each row (`substrait-check --raises`): a row that no frame holds raises nothing.
