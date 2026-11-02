### `any()` and `all()`

Ibis's `any()` and `all()` of booleans are now verified, as `MAX` and `MIN`
(`BOOL_OR` and `BOOL_AND`): NULLs are skipped, and a group without a
non-NULL value gives NULL (#53).
