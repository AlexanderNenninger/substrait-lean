### `lean_values` raises on join conditions too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a join or semi-join condition, on the pairs the checker's hash join tests (`substrait-check --raises`). A window's aggregates are not looked into: a frame may leave a row out.
