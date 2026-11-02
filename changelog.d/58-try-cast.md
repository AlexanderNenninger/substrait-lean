### `try_cast()`

Ibis's `try_cast()` (Substrait's `failureBehavior: RETURN_NULL`, SQL's
`TRY_CAST`) is verified for a double to an integer and an integer to a
narrower integer (#58): NULL where `cast()` would raise, so `verify` reports
no "cast out of range" for it. A double still truncates toward zero, as the
reference's `cast()` does, where DuckDB's own `TRY_CAST` rounds. `TRY_CAST`
to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. It runs
on DuckDB for now; the other engines refuse it until #271.
