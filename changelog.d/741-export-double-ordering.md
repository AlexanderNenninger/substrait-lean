### `to_substrait()` exports ordering comparisons of doubles (#741)

`<`, `<=`, `>`, `>=` and `between` on doubles are written with NaN greatest and
the two zeros one (ST-4), as equality, sort keys and grouping keys already were.
`t.filter(t.w > 1.0)` no longer refuses the export.
