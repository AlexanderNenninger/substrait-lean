### More of `ε`: scalar rules, thresholds and relative bounds

`epsilon_by_engine` now carries `ε` through `abs`, `FLOOR`, `CEIL`, `ROUND`,
casts to integers and `sqrt`, each by a rule proved in
`float-bounds/FloatBounds/Propagate.lean`
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)). A
comparison is exact where its sides' ranges, widened by `ε`, do not meet, so a
filter or key on it keeps the same rows; the contract reports per engine
whether every filter, key and sort does (`"rows_exact"`). A column whose
range leaves out zero gets a relative bound too, and a difference of nearly
equal values gets none
([docs/float-bounds.md](docs/float-bounds.md#through-arithmetic)).
