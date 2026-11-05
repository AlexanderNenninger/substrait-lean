### Bounds of one double operation, and `exp`

A double `+`, `-`, `*`, `/` or `exp` whose inputs' bounds keep the result
below the largest double no longer needs a "stays finite" check on the data,
and chains of them have bounds
([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582)).
`exp` propagates `ε` too, trusted to one ulp of the platform's `libm`
([docs/float-bounds.md](docs/float-bounds.md#one-operations-bounds-and-overflow-582)).
