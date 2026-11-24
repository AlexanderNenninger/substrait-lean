### Polars's `<<` and `>>` are proved templates

Polars has no shift. Sverify now writes `<<` and `>>` on Polars from the generated lowering table, in Polars's 64-bit functions, each proved in Lean to give the reference's value on every input (`Polars.bit_shl_agree`, `Polars.bit_shr_agree`), in place of two hand-written helpers ([#2586](https://github.com/AlexanderNenninger/substrait-lean/issues/2586)).
