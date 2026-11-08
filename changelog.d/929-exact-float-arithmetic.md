### Double arithmetic is exact, rounded once (D31)

Sverify's reference now defines `+`, `−`, `×` and `÷` of doubles as the exact
result rounded once to binary64, to nearest with ties to even
([D31](docs/core-semantics.md#d31-double-arithmetic-is-exact-rounded-once),
[#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)). No
result changes on an IEEE 754 engine. The eight trusted axioms about one
double operation (#582) are now theorems, so a contract over double
arithmetic rests on Lean's standard axioms. The checker computes these
operations on integers and checks them against native doubles on every
build.
