### Black boxes come from the engine package's catalogue

The reference's semantics no longer hold DuckDB's black boxes. A black box is a
row of a black-box catalogue (`Boxes`) that an engine package supplies, and the
core, `Rel.Allowed` and their theorems are parametric in it
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
DuckDB's rows, their evaluators and the opaque functions behind them are in
`SubstraitLean/DuckDBBoxes.lean`, and the core holds no `opaque` black box.
A package that builds its own checker opens DuckDB's catalogue with
`open scoped Substrait.DuckDB` before calling `checkerMain`
(`SubstraitCheckExamples/DummyEngine.lean`). Verdicts do not change.
