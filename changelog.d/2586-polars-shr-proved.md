### Polars's `>>` is a proved template

Polars has no shift. Sverify now writes `>>` on Polars from the generated lowering table: a floored `//` by `2ᵏ`, proved in Lean to give the reference's value on every input (`Polars.bit_shr_agree`), in place of a hand-written helper ([#2586](https://github.com/AlexanderNenninger/substrait-lean/issues/2586)).
