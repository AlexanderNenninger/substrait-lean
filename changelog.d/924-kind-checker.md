### A kind checker, and lambdas that read the row

The checker infers each column's kind and refuses a plan whose functions do
not fit their arguments (`+` of a double, a cast of a timestamp as a double),
with `well-kinded: no` and exit code 2. `Rel.kinds_sound` proves that a
well-kinded plan evaluates to values of its kinds, so the parser is no longer
trusted for typing ([#924](https://github.com/AlexanderNenninger/substrait-lean/issues/924)).

Lambdas have lexical scope ([D28](docs/core-semantics.md#d28-lambdas-have-lexical-scope)):
a body of `any_match`, `all_match`, `transform` or `filter` may read the
row's columns and an outer lambda's parameter. Plans that read only the
parameter keep their meaning; Polars still runs only those.
