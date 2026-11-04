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
`tested`; elementary functions other than `exp` and `Float32` sums stay `tested`
([docs/float-bounds.md](docs/float-bounds.md#the-engines-orders-and-epsilon-444)).

A double `+`, `-`, `*`, `/` or `exp` whose inputs' bounds keep the result
below the largest double no longer needs a "stays finite" check on the data,
and chains of them have bounds
([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582)).
`exp` propagates `ε` too, trusted to one ulp of the platform's `libm`.
