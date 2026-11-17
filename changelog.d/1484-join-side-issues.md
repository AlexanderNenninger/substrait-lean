### Errors in a condition on one side of a join

The proof that a plan with no reported issue raises no runtime error now
covers a condition that an engine evaluates on one side of a join before any
pair exists, even when the other side is empty. DuckDB pushes a filter on one
side into that side, and a hash join computes a key such as `10 // a.x` on
every row of its side (#1484). Before, this case was outside the proof. The
issues sverify reports are unchanged.
