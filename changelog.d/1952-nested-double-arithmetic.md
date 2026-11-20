### Nested double arithmetic in DuckDB SQL checks in under a second

`sv.verify` of DuckDB SQL under `semantics="duckdb"` took time exponential in
how deeply double arithmetic nests: six chained divisions took 193 s
([#1952](https://github.com/AlexanderNenninger/substrait-lean/issues/1952)).
Each operation's NaN and infinity handling names its operands several times,
and the lift copied a nested operand once per mention. It now computes a
nested operand once, as a column below the `SELECT` list, wherever every row
evaluates it anyway, so the plan grows linearly: ten divisions check in about
0.6 s. The checker also keys a projection's declared column types by a short
encoding of its expressions, which makes the check of a plan 10 to 20
projections deep 13 to 20 times cheaper.
