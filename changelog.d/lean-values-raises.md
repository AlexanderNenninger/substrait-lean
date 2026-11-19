### `lean_values` raises where the reference raises

The internal test oracle `sverify.testing.lean_values` returns `Rel.eval`'s rows, which have a value where the reference raises (a cast that does not fit gives `NULL` or an out-of-range integer). For a projection over a `VALUES` it now raises `LeanRaised` with the error (`substrait-check --outcomes`). Other plan shapes are not checked.
