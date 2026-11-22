### A CASE over doubles on Polars runs in the memory of its input

A `CASE` around ordering comparisons of doubles took 5 to 6 GB on Polars for a 64-row table: the plan Polars collects has no common-subexpression elimination, and the lowering wrote a nested operand six times per comparison and listed an operand's issues once per read. Each operand is written once and each distinct issue is checked once; the same plan peaks near 500 MB
([#2210](https://github.com/AlexanderNenninger/substrait-lean/issues/2210)).
