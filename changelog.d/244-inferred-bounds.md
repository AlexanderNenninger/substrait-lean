### Inferred bounds against overflow

Contracts no longer have to state the bounds that rule out integer overflow
(#244). For `amount * 2` on a `BIGINT`, sverify infers `_.amount < 2**62`,
proves the contract with it, and treats it as a precondition: it is checked
on the data at call time and on every refresh, or proved from Delta and
Iceberg file statistics, and reports list it as inferred. The inference
covers `+`, `-` and `*` with constants or bounded columns, negation, `abs`,
narrow integers and timestamp truncation (#379), through projections,
filters, joins and `MIN`/`MAX`. Lean proves the contract again with the
inferred bounds, so a wrong inference only fails the proof. Where no single
bound exists (the product of two columns, a `SUM`, a value from another
contracted transformation), the report's `Issue.hint` suggests one.
`@sv.transform(strict=True)` and `sv.verify(..., infer=False)` require
explicit bounds.
