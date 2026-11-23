### Polars runs its generated lowering

The translation to Polars now writes integer `//` and `%`, `round` and `ceil`
from the generated lowering table (`sverify_polars.lowering`), the templates
`Lowering.polars_exact` proves
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)). The
hand-written shims `int_div_trunc` and `int_mod_trunc` are gone. `round` and
`ceil` of a negative value that rounds to zero now give `0.0` on Polars, as the
reference does, where they gave `-0.0`; the two are one value for every
comparison sverify makes. Polars's `division_type` and `round_zero_sign` rows
are proved by `Lowering.polars_exact`.
