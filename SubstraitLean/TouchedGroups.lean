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
* `touched_window_sound`: the same for a window and the partitions a batch
  touches (`window_split`, from `windowEval_sharded`).

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

/-- The rows a batch does not change, by a predicate `q` true on every row
it deletes or inserts, are as they were. -/
theorem filter_untouched {q : Row → Bool} {rows dels ins : Relation}
    (h : ∀ r ∈ dels ++ ins, q r = true) :
    (applyBatch rows dels ins).filter (fun r => !q r) = rows.filter (fun r => !q r) := by
  have hd : ∀ d ∈ dels, (!q d) = false := fun d hd => by
    simp [h d (List.mem_append_left _ hd)]
  have hi : ins.filter (fun r => !q r) = [] :=
    List.filter_eq_nil_iff.mpr fun r hr => by simp [h r (List.mem_append_right _ hr)]
  simp only [applyBatch, List.filter_append, hi, List.append_nil]
  exact filter_foldl_erase dels rows hd

/-- The input rows of the groups a batch does not touch are as they were. -/
theorem untouched_unchanged {K : Row → Bool} {rows dels ins : Relation}
    (h : Touches gs K dels ins) :
    (applyBatch rows dels ins).filter (fun r => !K (groupKey gs r)) =
      rows.filter (fun r => !K (groupKey gs r)) :=
  filter_untouched h

/-- **Touched-group recompute is sound**: the aggregate after a batch is the
rows of the groups it does not touch, from before the batch, and the
aggregate of the new input rows whose keys it touches. -/
theorem touched_sound (hg : gs ≠ []) {K : Row → Bool} (hK : RespectsCanon K)
    {rows dels ins : Relation} (h : Touches gs K dels ins) :
    (aggregateEval gs ms (applyBatch rows dels ins)).Perm
      ((aggregateEval gs ms rows).filter (fun o => !K (o.take gs.length)) ++
        aggregateEval gs ms ((applyBatch rows dels ins).filter fun r => K (groupKey gs r))) := by
  refine (List.filter_append_perm (fun o => !K (o.take gs.length)) _).symm.trans
    (List.Perm.append ?_ ?_)
  · have hK' : RespectsCanon fun k => !K k := fun k k' he => by simp only [hK k k' he]
    refine (Retention.aggregateEval_filter_key hg ms (fun k => !K k) _ hK').trans ?_
    rw [untouched_unchanged h]
    exact (Retention.aggregateEval_filter_key hg ms (fun k => !K k) rows hK').symm
  · simpa using Retention.aggregateEval_filter_key hg ms K (applyBatch rows dels ins) hK

/-- `touched_sound` for `Rel.eval`: when the input `r` goes from `rows` to
`applyBatch rows dels ins` and the batch touches only keys in `K`. -/
theorem touched_eval (hg : gs ≠ []) {r : Rel} {cat cat' : Catalog} {K : Row → Bool}
    (hK : RespectsCanon K) {dels ins : Relation} (hr : r.eval cat' = applyBatch (r.eval cat) dels ins)
    (h : Touches gs K dels ins) :
    ((Rel.aggregate r gs ms).eval cat').Perm
      (((Rel.aggregate r gs ms).eval cat).filter (fun o => !K (o.take gs.length)) ++
        aggregateEval gs ms ((r.eval cat').filter fun x => K (groupKey gs x))) := by
  simp only [Rel.eval, hr]
  exact touched_sound hg hK h

/-! ## Windows: touched partitions -/

section Windows

variable {part : List Nat} {sort : List SortKey} {fns : List WinFn}

/-- A window splits by any predicate `K` of the partition key, given a key
on the partition and sort columns (`windowEval_sharded`). -/
theorem window_split (K : List Value → Bool) {rows : Relation}
    (hk : KeyOn (part ++ sort.map (·.col)) rows) :
    (windowEval part sort fns rows).Perm
      (windowEval part sort fns (rows.filter fun r => K (keyOf part r)) ++
        windowEval part sort fns (rows.filter fun r => !K (keyOf part r))) := by
  let f : Bool → Relation := fun b => rows.filter fun r => K (keyOf part r) == b
  have hp : rows.Perm ([true, false].flatMap f) := by
    simpa [f] using (List.filter_append_perm (fun r => K (keyOf part r)) rows).symm
  have hd : ([true, false].map f).Pairwise
      fun A B => ∀ a ∈ A, ∀ b ∈ B, samePart part a b = false := by
    rw [List.map_cons, List.map_cons, List.map_nil, List.pairwise_pair]
    intro a ha b hb
    simp only [f, List.mem_filter, beq_iff_eq] at ha hb
    have hne : keyOf part a ≠ keyOf part b := fun he => by
      rw [he, hb.2] at ha; exact Bool.false_ne_true ha.2
    simpa [samePart, keyOf] using hne
  simpa [f] using windowEval_sharded (fns := fns) hp hk hd

/-- An output row of a window has the partition key of an input row. -/
theorem keyOf_windowEval {rows : Relation} (hw : ∀ r ∈ rows, ∀ i ∈ part, i < r.length)
    {out : Row} (h : out ∈ windowEval part sort fns rows) :
    ∃ x ∈ rows, keyOf part out = keyOf part x := by
  obtain ⟨b, x, a, _, hx, rfl⟩ := mem_windowEval h
  refine ⟨x, hx, List.map_congr_left fun i hi => ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hw x hx i hi)]

/-- **Touched-partition recompute is sound**: for a window whose partitions
a batch touches only with keys in `K`, the window after the batch is the old
rows of the untouched partitions and the window over the new input rows of
the touched ones. It needs what `windowEval_sharded` needs: no two input
rows equal on the partition and sort columns, before or after the batch,
and every partition column within every row. -/
theorem touched_window_sound (K : List Value → Bool) {rows dels ins : Relation}
    (h : ∀ r ∈ dels ++ ins, K (keyOf part r) = true)
    (hk : KeyOn (part ++ sort.map (·.col)) rows)
    (hk' : KeyOn (part ++ sort.map (·.col)) (applyBatch rows dels ins))
    (hw : ∀ r ∈ rows, ∀ i ∈ part, i < r.length) :
    (windowEval part sort fns (applyBatch rows dels ins)).Perm
      ((windowEval part sort fns rows).filter (fun o => !K (keyOf part o)) ++
        windowEval part sort fns
          ((applyBatch rows dels ins).filter fun r => K (keyOf part r))) := by
  have hu : (applyBatch rows dels ins).filter (fun r => !K (keyOf part r)) =
      rows.filter (fun r => !K (keyOf part r)) := filter_untouched h
  have h1 : (windowEval part sort fns (rows.filter fun r => K (keyOf part r))).filter
      (fun o => !K (keyOf part o)) = [] :=
    List.filter_eq_nil_iff.mpr fun o ho => by
      obtain ⟨x, hx, he⟩ :=
        keyOf_windowEval (fun r hr => hw r (List.mem_filter.mp hr).1) ho
      simp [he, (List.mem_filter.mp hx).2]
  have h2 : (windowEval part sort fns (rows.filter fun r => !K (keyOf part r))).filter
      (fun o => !K (keyOf part o)) =
        windowEval part sort fns (rows.filter fun r => !K (keyOf part r)) :=
    List.filter_eq_self.mpr fun o ho => by
      obtain ⟨x, hx, he⟩ :=
        keyOf_windowEval (fun r hr => hw r (List.mem_filter.mp hr).1) ho
      have := (List.mem_filter.mp hx).2
      simpa [he] using this
  have hold : ((windowEval part sort fns rows).filter fun o => !K (keyOf part o)).Perm
      (windowEval part sort fns (rows.filter fun r => !K (keyOf part r))) := by
    refine ((window_split K hk).filter _).trans ?_
    rw [List.filter_append, h1, h2, List.nil_append]
  refine (window_split K hk').trans (List.perm_append_comm.trans ?_)
  rw [hu]
  exact List.Perm.append_right _ hold.symm

end Windows

end TouchedGroups
end Substrait
