### Unspecified and clustered sort directions

A `SortRel` key may now leave its direction unspecified, read as ascending
with NULLs last, or be `SORT_DIRECTION_CLUSTERED`, any order with equal keys
adjacent; both were refused before. A window's or a measure's order still
states its direction. Lean's `Rel.AllowedP` states what each profile allows,
with `Rel.allowed_core` proving the reference within the core
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
`docs/core-semantics.md`, D6 and D8).
