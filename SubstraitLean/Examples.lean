import SubstraitLean.Rewrites
import SubstraitLean.Incremental
import SubstraitLean.Weighted
import SubstraitLean.Terms

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
