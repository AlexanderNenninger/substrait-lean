import SubstraitLean.Retention

/-!
# Touched-group recompute for aggregates

An aggregate without delta rules can still be maintained at the cost of the
groups a batch touches: take the group keys of the rows the batch inserts
into or deletes from the aggregate's input, recompute only those groups from
the new input (a semi-join on the keys), and keep every other group's row.

* `untouched_unchanged`: a batch whose rows all have touched keys leaves the
  input rows of the other groups as they were.
* `touched_sound`: the aggregate after the batch is the untouched groups'
  rows from before, plus the aggregate of the new input rows with touched
  keys, for every measure.
* `touched_eval`: the same for `Rel.eval` of an `Rel.aggregate`.

Groups are independent (`Retention.aggregateEval_filter_key`), so this holds
for any aggregate: MIN, MAX, AVG, COUNT, SUM and the rest. The Python glue
(`sverify._touched`) computes the input's change with the input's delta
rules, the touched keys from it, and the recompute, and is trusted.
-/

namespace Substrait
namespace TouchedGroups

open Retention (applyBatch filter_foldl_erase)

variable {gs : List Expr} {ms : List Measure}

/-- Every row the batch deletes or inserts has a key in `K`. -/
def Touches (gs : List Expr) (K : Row → Bool) (dels ins : Relation) : Prop :=
  ∀ r ∈ dels ++ ins, K (groupKey gs r) = true

/-- The input rows of the groups a batch does not touch are as they were. -/
theorem untouched_unchanged {K : Row → Bool} {rows dels ins : Relation}
    (h : Touches gs K dels ins) :
    (applyBatch rows dels ins).filter (fun r => !K (groupKey gs r)) =
      rows.filter (fun r => !K (groupKey gs r)) := by
  have hd : ∀ d ∈ dels, (!K (groupKey gs d)) = false := fun d hd => by
    simp [h d (List.mem_append_left _ hd)]
  have hi : ins.filter (fun r => !K (groupKey gs r)) = [] :=
    List.filter_eq_nil_iff.mpr fun r hr => by simp [h r (List.mem_append_right _ hr)]
  simp only [applyBatch, List.filter_append, hi, List.append_nil]
  exact filter_foldl_erase dels rows hd

/-- **Touched-group recompute is sound**: the aggregate after a batch is the
rows of the groups it does not touch, from before the batch, and the
aggregate of the new input rows whose keys it touches. -/
theorem touched_sound (hg : gs ≠ []) {K : Row → Bool} {rows dels ins : Relation}
    (h : Touches gs K dels ins) :
    (aggregateEval gs ms (applyBatch rows dels ins)).Perm
      ((aggregateEval gs ms rows).filter (fun o => !K (o.take gs.length)) ++
        aggregateEval gs ms ((applyBatch rows dels ins).filter fun r => K (groupKey gs r))) := by
  refine (List.filter_append_perm (fun o => !K (o.take gs.length)) _).symm.trans
    (List.Perm.append ?_ ?_)
  · refine (Retention.aggregateEval_filter_key hg ms (fun k => !K k) _).trans ?_
    rw [untouched_unchanged h]
    exact (Retention.aggregateEval_filter_key hg ms (fun k => !K k) rows).symm
  · simpa using Retention.aggregateEval_filter_key hg ms K (applyBatch rows dels ins)

/-- `touched_sound` for `Rel.eval`: when the input `r` goes from `rows` to
`applyBatch rows dels ins` and the batch touches only keys in `K`. -/
theorem touched_eval (hg : gs ≠ []) {r : Rel} {cat cat' : Catalog} {K : Row → Bool}
    {dels ins : Relation} (hr : r.eval cat' = applyBatch (r.eval cat) dels ins)
    (h : Touches gs K dels ins) :
    ((Rel.aggregate r gs ms).eval cat').Perm
      (((Rel.aggregate r gs ms).eval cat).filter (fun o => !K (o.take gs.length)) ++
        aggregateEval gs ms ((r.eval cat').filter fun x => K (groupKey gs x))) := by
  simp only [Rel.eval, hr]
  exact touched_sound hg h

end TouchedGroups
end Substrait
