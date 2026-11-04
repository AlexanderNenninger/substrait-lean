### `AND` and `OR` evaluate both operands, and the report says so (#604)

An error in either operand of `AND` or `OR` may raise, whatever the other
operand's value, as DuckDB and Polars evaluate both (decision D19 in
`docs/core-semantics.md`). The checker already analysed both operands. A
plan such as `filter((x != 0) & (10 // x > 1))` was proved only under the
precondition `x != 0` that `verify` inferred, and `Report.run` did not check
it, so a batch with `x = 0` raised on the engine (now refused: see the next
entry). The report now flags an error inside an `AND` or `OR`
(`Issue.under_and_or`) and suggests guarding the operation itself:
`(CASE WHEN x <> 0 THEN 10 // x END) > 1`, in Ibis
`ibis.cases((_.x != 0, 10 // _.x)) > 1`, which is proved without the
precondition.
