### Docs: Ibis `//` floors and `%` truncates, and a hint for the pair

The guide has a section, "Integer division in Ibis and SQL", with the quotient and remainder of `-7` under each front end and semantics ([#693](https://github.com/AlexanderNenninger/substrait-lean/issues/693)). A report carries a hint when one plan uses Ibis `//` and `%` on the same operands, since `q * d + r == x` fails for negative `x`. Ten wrong statements and gaps in the README, `docs/` and the `Contract` docstring are fixed ([#698](https://github.com/AlexanderNenninger/substrait-lean/issues/698)).
