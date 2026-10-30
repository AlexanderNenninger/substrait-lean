import SubstraitLean.Rel

/-!
# Verified plan rewrites

Each theorem states that an optimizer rewrite preserves a plan's meaning.
Most are *exact* (same list of rows); `unionAll_comm` holds only up to bag
equivalence (`≈ᵣ`), which is the notion that matters for unordered results.
Rewrites that move predicates need `Rel.WF`, because pushing a predicate
below an operator is only sound when it references columns that exist there.
-/

namespace Substrait

open Rel

/-- `Filter(Filter(r, p), q)` ⟶ `Filter(r, p AND q)`. Sound even under
three-valued logic, because `and3` is true iff both sides are true. -/
theorem filter_filter (r : Rel) (p q : Expr) (cat : Catalog) :
    (filter (filter r p) q).eval cat = (filter r (.bin .and p q)).eval cat := by
  simp [eval, List.filter_filter, Expr.eval, BinFn.apply, isTrue_and3, Bool.and_comm]

theorem filter_true (r : Rel) (cat : Catalog) :
    (filter r (.lit (.bool true))).eval cat = r.eval cat := by
  simp [eval, Expr.eval, Value.isTrue]

theorem filter_unionAll (a b : Rel) (p : Expr) (cat : Catalog) :
    (filter (unionAll a b) p).eval cat = (unionAll (filter a p) (filter b p)).eval cat := by
  simp [eval, List.filter_append]

/-- An inner join is a filtered cross product. -/
theorem join_inner_eq_filter_cross (a b : Rel) (on : Expr) (cat : Catalog) :
    (join a b .inner on).eval cat = (filter (cross a b) on).eval cat := rfl

theorem unionAll_comm (a b : Rel) : unionAll a b ≈ᵣ unionAll b a :=
  fun _ => List.perm_append_comm

/-- **Filter pushdown through Project**: a predicate that only reads the
input columns of a `ProjectRel` can be evaluated before the projection. -/
theorem filter_project_pushdown {cat : Catalog} (hcat : cat.WF)
    {r : Rel} {es : List Expr} {p : Expr}
    (hr : r.WF cat) (hp : p.refsLt (r.arity cat)) :
    (filter (project r es) p).eval cat = (project (filter r p) es).eval cat := by
  simp only [eval, List.filter_map]
  congr 1
  apply List.filter_congr
  intro row hrow
  simp [Expr.eval_append _ hp (eval_arity hcat hr row hrow)]

/-- **Filter pushdown into the left side of a cross product**. -/
theorem filter_cross_pushdown_left {cat : Catalog} (hcat : cat.WF)
    {a b : Rel} {p : Expr}
    (ha : a.WF cat) (hp : p.refsLt (a.arity cat)) :
    (filter (cross a b) p).eval cat = (cross (filter a p) b).eval cat := by
  have hlen := eval_arity hcat ha
  simp only [eval, crossRows, List.filter_flatMap]
  generalize eval cat a = xs at hlen ⊢
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hlen x (by simp)
    have ih := ih fun y hy => hlen y (by simp [hy])
    -- A predicate on the left columns is constant across `x`'s output rows.
    have hrow : ((eval cat b).map (x ++ ·)).filter (fun row => (p.eval row).isTrue)
        = if (p.eval x).isTrue then (eval cat b).map (x ++ ·) else [] := by
      rw [List.filter_map]
      split <;> rename_i h <;> simp only [Function.comp_def, Expr.eval_append _ hp hx, h]
      · rw [List.filter_eq_self.2 (by simp)]
      · simp
    rw [List.flatMap_cons, hrow, ih, List.filter_cons]
    split <;> simp

/-- `Fetch(r, 0, ∅)` is the identity. -/
theorem fetch_zero_none (r : Rel) (cat : Catalog) :
    (fetch r 0 none).eval cat = r.eval cat := by
  simp [eval]

/-- Projecting then emitting only the original columns undoes the projection
(dead-expression elimination). -/
theorem emit_project_identity {cat : Catalog} (hcat : cat.WF)
    {r : Rel} {es : List Expr} (hr : r.WF cat) :
    (emit (project r es) (List.range (r.arity cat))).eval cat = r.eval cat := by
  simp only [eval, List.map_map]
  conv => rhs; rw [← List.map_id (r.eval cat)]
  apply List.map_congr_left
  intro row hrow
  have hlen := eval_arity hcat hr row hrow
  simp only [Function.comp_apply, id]
  apply List.ext_getElem (by simp [hlen])
  intro i _ hi
  simp [List.getD, List.getElem?_append_left hi, hi]

end Substrait
