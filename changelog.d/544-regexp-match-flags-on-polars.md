### Polars refuses `regexp_match` patterns with flags or lookarounds

The Polars engine counted the entries of `regexp_match` by asking Polars, so it
ran patterns with `(?i)`, named groups or lookarounds, where the reference
model raises a bad-regex error (`Text.simpleRegex`). It now counts groups as the SQL writer
does and refuses those patterns too, in one definition shared by both
([#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544)).
