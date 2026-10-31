import SubstraitLean.Rewrites
import SubstraitLean.Incremental
import SubstraitLean.Weighted
import SubstraitLean.Terms
import SubstraitLean.Contracts
import SubstraitLean.Safety
import SubstraitLean.Keys
import SubstraitLean.Completeness
import SubstraitLean.Compose
import SubstraitLean.TableFormat
import SubstraitLean.Partition
import SubstraitLean.Guards

/-!
# Examples

The semantics is executable, so concrete plans can be run with `#eval` and
checked with `#guard` at build time.
-/

namespace Substrait.Examples

open Rel

/-- `orders(id, customer, amount)` -/
def orders : Table :=
  { arity := 3
    rows := [[.int 1, .str "ada", .int 30],
             [.int 2, .str "bob", .int 5],
             [.int 3, .str "ada", .null]] }

def cat : Catalog := fun
  | "orders" => orders
  | _ => ⟨0, []⟩

/-- `SELECT id, amount * 2 FROM orders WHERE amount > 10`, written the way a
Substrait producer emits it: Project appends column 3, Emit narrows to (0, 3). -/
def plan : Rel :=
  emit
    (project
      (filter (read "orders") (.bin .lt (.lit (.int 10)) (.field 2)))
      [.bin .mul (.field 2) (.lit (.int 2))])
    [0, 3]

#guard plan.eval cat == [[.int 1, .int 60]]

-- The null amount is filtered out: `10 < NULL` is NULL, not true.
#guard ((filter (read "orders") (.bin .lt (.lit (.int 10)) (.field 2))).eval cat).length == 1

-- A left join pads unmatched rows with nulls on the right.
#guard (join (read "orders") (values 1 [[.str "ada"]]) .left
          (.bin .eq (.field 1) (.field 3))).eval cat
       == [[.int 1, .str "ada", .int 30, .str "ada"],
           [.int 2, .str "bob", .int 5, .null],
           [.int 3, .str "ada", .null, .str "ada"]]

/-! ## Incremental maintenance

A change set on `orders`: delete order 1, insert order 4, and update order 2's
amount from 5 to 20 (a delete plus an insert). Change tables are named
`<table>$delta`. -/

def zcat : ZCatalog := fun t => ZSet.lift (cat t).rows

def customers : ZSet := ZSet.lift [[.str "ada"], [.str "bob"]]

def zcat₂ : ZCatalog := fun
  | "customers" => customers
  | t => zcat t

def Δ : ZCatalog := fun
  | "orders" => [([.int 1, .str "ada", .int 30], -1),
                 ([.int 4, .str "cy", .int 50], 1),
                 ([.int 2, .str "bob", .int 5], -1),
                 ([.int 2, .str "bob", .int 20], 1)]
  | "customers" => [([.str "cy"], 1)]
  | _ => []

def δ (t : String) : String := t ++ "$delta"

/-- What the engine sees: old tables plus change tables. -/
def engineCat (old : ZCatalog) : ZCatalog := fun t =>
  if t.endsWith "$delta" then Δ (t.dropEnd 6).toString else old t

-- The delta plan reads `orders$delta` and is itself an ordinary plan.
#guard (plan.delta δ).tables == ["orders$delta"]

-- ΔQ: order 1 leaves the result, orders 2 and 4 enter it.
#guard ZSet.consolidate ((plan.delta δ).zeval (engineCat zcat))
       == [([.int 1, .int 60], -1), ([.int 4, .int 100], 1), ([.int 2, .int 40], 1)]

-- Old result + ΔQ = recomputing from scratch (`Rel.incremental_sound`).
#guard (ZSet.consolidate (plan.zeval zcat ++ (plan.delta δ).zeval (engineCat zcat))).isPerm
       (ZSet.consolidate (plan.zeval (zcat + Δ)))

/-- `orders ⋈ customers ON orders.customer = customers.name`, with both
sides changing at once (the bilinear case). -/
def joinPlan : Rel := join (read "orders") (read "customers") .inner (.bin .eq (.field 1) (.field 3))

#guard (ZSet.consolidate (joinPlan.zeval zcat₂ ++ (joinPlan.delta δ).zeval (engineCat zcat₂))).isPerm
       (ZSet.consolidate (joinPlan.zeval (zcat₂ + Δ)))

-- The new `cy` customer joins with the newly inserted order 4.
#guard (ZSet.consolidate (joinPlan.zeval (zcat₂ + Δ))).contains
       ([.int 4, .str "cy", .int 50, .str "cy"], 1)

/-! ## Windows -/

/-- Readings `(sensor, ts, value)`, out of order. -/
def readings : Rel :=
  .values 3 [[.int 1, .int 20, .int 7], [.int 2, .int 10, .int 5], [.int 1, .int 10, .int 3]]

/-- `LAG(value)` and `ROW_NUMBER()` per sensor, by timestamp. -/
def withPrev : Rel := .window readings [0] [{ col := 1 }] [.lag 2 1 .null, .rowNumber]

#guard withPrev.eval (fun _ => ⟨0, []⟩) ==
  [[.int 2, .int 10, .int 5, .null, .int 1],
   [.int 1, .int 10, .int 3, .null, .int 1],
   [.int 1, .int 20, .int 7, .int 3, .int 2]]

/-! ## Aggregates -/

/-- `SELECT customer, COUNT(*), SUM(amount), MAX(amount) FROM orders GROUP BY customer`:
`ada`'s NULL amount counts as a row but not as a value. -/
def totals : Rel :=
  .aggregate (read "orders") [.field 1]
    [{ fn := .count, arg := .lit (.int 1) }, { fn := .sum, arg := .field 2 },
     { fn := .max, arg := .field 2 }]

#guard totals.eval cat ==
  [[.str "ada", .int 2, .int 30, .int 30],
   [.str "bob", .int 1, .int 5, .int 5]]

-- Without grouping there is one row, even for no input.
#guard (Rel.aggregate (.values 1 []) [] [{ fn := .count, arg := .field 0 },
    { fn := .sum, arg := .field 0 }]).eval cat == [[.int 0, .null]]

-- Two-phase aggregation: `totals` on two shards of `orders`, then combined.
#guard
  let shards := [(cat "orders").rows.take 1, (cat "orders").rows.drop 1]
  let ms := [{ fn := .count, arg := .lit (.int 1) }, { fn := .sum, arg := .field 2 },
    { fn := .max, arg := .field 2 : Measure }]
  aggregateEval (keyFields 1) (combineMeasures 1 ms) (shards.flatMap (aggregateEval [.field 1] ms))
    == totals.eval cat

end Substrait.Examples

-- Proofs rely only on Lean's standard axioms (no `sorry`).
#print axioms Substrait.Rel.eval_arity
#print axioms Substrait.filter_project_pushdown
#print axioms Substrait.filter_cross_pushdown_left
#print axioms Substrait.emit_project_identity
#print axioms Substrait.Rel.incremental_sound
#print axioms Substrait.Rel.zeval_lift
#print axioms Substrait.Rel.weighted_eval
#print axioms Substrait.Rel.zeval_terms
#print axioms Substrait.contract_sound
#print axioms Substrait.Rel.mayIssues_sound
#print axioms Substrait.FloatCode.round_mono
#print axioms Substrait.Time.monthIndex_spec
#print axioms Substrait.Time.trunc_mono
#print axioms Substrait.Rel.keys_sound
#print axioms Substrait.IoT.window_complete
#print axioms Substrait.window_tiebreak
#print axioms Substrait.Rel.window_deterministic
#print axioms Substrait.Measure.abs_sound
#print axioms Substrait.aggregateEval_key
#print axioms Substrait.Triple.compose
#print axioms Substrait.Triple.compose_spec
#print axioms Substrait.Triple.of_contract
#print axioms Substrait.Triple.of_keys
#print axioms Substrait.Triple.of_aeval
#print axioms Substrait.RowsSat.update
#print axioms Substrait.KeyOn.update
#print axioms Substrait.Spec.update
#print axioms Substrait.Triple.maintained
#print axioms Substrait.Rel.stack_sound
#print axioms Substrait.Rel.chain_sound
#print axioms Substrait.ZSet.diff_correct
#print axioms Substrait.Rel.zeval_weight_congr
#print axioms Substrait.ChangeFeed.of_diff
#print axioms Substrait.Rel.cdf_sound
#print axioms Substrait.stats_table
#print axioms Substrait.stats_append
#print axioms Substrait.stats_bounds
#print axioms Substrait.Rel.eval_sharded
#print axioms Substrait.Rel.keyRows
#print axioms Substrait.Sharding.coDisjoint
#print axioms Substrait.windowEval_sharded
#print axioms Substrait.aggregateEval_flatten_disjoint
#print axioms Substrait.Measure.combine_eval
#print axioms Substrait.twoPhase_correct
#print axioms Substrait.Rel.shardSplit_sound
#print axioms Substrait.inI64_partial
#print axioms Substrait.Rel.evalI_eq
#print axioms Substrait.Rel.guardFree_sound
