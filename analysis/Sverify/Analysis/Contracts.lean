import Sverify.Analysis.Contracts.Lattice
import Sverify.Analysis.Contracts.Transfer
import Sverify.Analysis.Contracts.TransferSound
import Sverify.Analysis.Contracts.Refine
import Sverify.Analysis.Contracts.Facts
import Sverify.Analysis.Contracts.Plan
import Sverify.Analysis.Contracts.Sound

/-!
# Pre- and postconditions: a verified abstract interpreter

Data scientists state **preconditions** about input rows ("`amount ≥ 0`",
"`id` is not NULL") and **postconditions** about output rows. Postconditions are
proved, not tested: `Rel.aeval` computes, for every column of a plan's output,
an over-approximation (`AVal`) of the values it can hold. It tracks
whether a column can be NULL, an integer range, the possible booleans and
whether it can be a string. A postcondition holds when its column is
*certainly TRUE*.

* `Expr.abs_sound`: abstract expression evaluation is sound.
* `Expr.refine_sound`: a row that passes a filter satisfies what the filter
  condition says about it (`amount > 10` ⇒ `amount` is a non-NULL int ≥ 11).
* `Rel.aeval_sound`: every row a plan produces is described by `Rel.aeval`.
* `contract_sound`: if every postcondition column is certainly TRUE under the
  preconditions, then every output row satisfies every postcondition.

This module re-exports its parts, in import order: `Contracts.Lattice` (`Bound`,
`AVal`), `Contracts.Transfer` (`Expr.abs`), `Contracts.TransferSound`
(`Expr.abs_sound`), `Contracts.Refine` (`Expr.refine`), `Contracts.Facts`
(`Rel.facts`), `Contracts.Plan` (`Rel.maxRows`, `Rel.aeval`, `Rel.lane`) and
`Contracts.Sound` (`Rel.aeval_sound`, `contract_sound`).
-/
