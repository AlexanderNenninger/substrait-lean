### Proved float tolerances for `SUM` and `AVG`

The per-plan tolerance `--contract` reports for a double `SUM` or `AVG`
(`"epsilon"`) is now proved in Lean for every summation order the engines
use: trees of additions, DuckDB's constant runs and Polars's Kahan sum
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)). So is
the relative bound for values of one sign, and the propagation of `ε` through
`+`, `-`, `*` and `/` per engine
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)).
Routes that rest on these bounds report evidence `proved` where they reported
`tested`; elementary functions and `Float32` sums stay `tested`
([docs/float-bounds.md](docs/float-bounds.md#the-engines-orders-and-epsilon-444)).
