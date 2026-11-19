### `lean_values` raises on filters and aggregates too

`sverify.testing.lean_values` raises `LeanRaised` where the reference raises in a filter condition, a projection or an aggregate's groups and arguments, at any depth of the plan (`substrait-check --raises`). Joins and windows are not looked into.
