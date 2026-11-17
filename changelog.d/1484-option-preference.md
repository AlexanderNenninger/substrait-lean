### A function option takes its first supported preference

A plan may list several preferences for a function option, and Substrait applies
the first one the engine supports. The parser accepted an option when any
preference was supported but modelled the first listed one, so
`on_division_by_zero: ["IEEE", "NULL"]` on an integer `divide` was read as `IEEE`.
`checkOptions` now keeps the supported preferences and the parse reads the first
of them (#1484, R1).
