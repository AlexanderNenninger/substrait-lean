### `lean_values` raises on join conditions too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a join or semi-join condition, on the pairs the checker's hash join tests (`substrait-check --raises`), so a raise on a pair without matching join keys can be missed; every error it raises is the reference's. A window's aggregates are not looked into: a frame may leave a row out.
