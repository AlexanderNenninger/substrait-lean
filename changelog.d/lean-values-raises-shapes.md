### `lean_values` raises on filters and aggregates too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a filter condition, a projection, a join condition or an aggregate's groups and arguments, at any depth of the plan (`substrait-check --raises`). A window's aggregates are not looked into: a frame may leave a row out.
