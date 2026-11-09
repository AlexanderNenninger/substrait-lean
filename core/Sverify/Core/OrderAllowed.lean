import Sverify.Core.Forall2
import Sverify.Core.Rel

/-!
# Every order the reference allows, below the analyses (#679, D24, #904)

`Rel.OrderAllowed` holds the results of every order the reference leaves
open: ties in an `ORDER BY` or a window's order, the rows a `FETCH` takes,
and the order `FIRST`, `LAST`, `STRING_AGG`, `collect` and `MODE` read.
`Rel.eval` picks one (`Rel.eval_orderAllowed`). It sits below
`Contracts.lean`, so the analyses' soundness theorems can be stated over
every order; `Ties.lean` links it to `Rel.Allowed`.
-/

namespace Substrait

/-! ## Measures -/

theorem Measure.eval_sorts {m : Measure} (h : m.fn.sorts = true) (rows : Relation) :
    m.eval rows = m.fn.apply (m.inputs (rows.mergeSort (sortLe m.sort))) := by
  cases hf : m.fn <;> simp [Measure.eval, hf, AggFn.sorts] at h ⊢


/-- What a measure over a group's `rows` gives for some order of them: a
measure that sorts its rows (`FIRST`, `LAST`, `STRING_AGG`, `collect`,
`MODE`) its value over the rows in any order its own `ORDER BY` allows; the
others `Measure.eval`'s value. -/
def Measure.OrderAllowed (m : Measure) (rows : Relation) (v : Value) : Prop :=
  ∃ s, s.Perm rows ∧ s.Pairwise (sortLe m.sort · · = true) ∧
    v = if m.fn.sorts then m.eval s else m.eval rows

theorem mergeSort_sorted (sort : List SortKey) (rows : Relation) :
    (rows.mergeSort (sortLe sort)).Pairwise (sortLe sort · · = true) :=
  List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total rows

/-- A sorted list sorts to itself. -/
theorem mergeSort_eq_of_sorted {sort : List SortKey} {s : Relation}
    (h : s.Pairwise (sortLe sort · · = true)) : s.mergeSort (sortLe sort) = s :=
  List.mergeSort_of_pairwise h

theorem Measure.eval_orderAllowed (m : Measure) (rows : Relation) :
    m.OrderAllowed rows (m.eval rows) := by
  refine ⟨rows.mergeSort (sortLe m.sort), List.mergeSort_perm _ _, mergeSort_sorted _ _, ?_⟩
  split
  · next h => rw [Measure.eval_sorts h, Measure.eval_sorts h,
      mergeSort_eq_of_sorted (mergeSort_sorted _ _)]
  · rfl

/-- Each value is `Measure.eval`'s over some order of the rows, and over the
rows themselves where the measure does not sort them. -/
theorem Measure.OrderAllowed.eval {m : Measure} {rows : Relation} {v : Value}
    (h : m.OrderAllowed rows v) :
    ∃ s, s.Perm rows ∧ v = m.eval s ∧ (m.fn.sorts = false → v = m.eval rows) := by
  obtain ⟨s, hp, _, rfl⟩ := h
  split
  · next hs => exact ⟨s, hp, rfl, fun h => by rw [hs] at h; cases h⟩
  · exact ⟨rows, .refl _, rfl, fun _ => rfl⟩

/-- What an aggregate's output may be for some order of each group's rows:
`aggAllowed` with `Measure.OrderAllowed`. -/
def aggOrderAllowed (gs : List Expr) (ms : List Measure) (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.OrderAllowed rows v) ms vs
  else Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.OrderAllowed (groupRows gs rows k) v) ms vs)
    (distinctRows (rows.map (groupKey gs))) out

theorem aggregateEval_orderAllowed (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggOrderAllowed gs ms rows (aggregateEval gs ms rows) := by
  unfold aggOrderAllowed aggregateEval
  split
  · exact ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m rows⟩
  · exact forall₂_map_self _ fun k _ =>
      ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m _⟩

/-- A row of an aggregate's output: a group key and the measures' values over
the group's rows, in some order of them. -/
theorem mem_aggOrderAllowed {gs : List Expr} {ms : List Measure} {rows out : Relation}
    {row : Row} (h : aggOrderAllowed gs ms rows out) (hr : row ∈ out) :
    ∃ k vs grp, row = k ++ vs ∧ Forall2 (fun m v => m.OrderAllowed grp v) ms vs ∧
      (∀ y ∈ grp, y ∈ rows) ∧ ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k = groupKey gs x) ∧
      (gs ≠ [] → grp ≠ []) ∧ grp.length ≤ rows.length := by
  unfold aggOrderAllowed at h
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨[], row, rows, by simp, hv, fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩,
      fun hne => absurd (List.isEmpty_iff.mp hg) hne, Nat.le_refl _⟩
  · obtain ⟨k, hk, vs, rfl, hv⟩ := Forall2.mem_right h hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
    refine ⟨_, vs, _, rfl, hv, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, rfl⟩,
      fun _ => List.ne_nil_of_mem (a := x) (List.mem_filter.mpr ⟨hx, by simp⟩),
      List.length_filter_le _ _⟩

/-! ## Plans -/

/-- **The results of every order the reference allows** for `r` on `cat`:
`Rel.Allowed` with each measure as `Measure.OrderAllowed` takes it. -/
def Rel.OrderAllowed (cat : Catalog) : Rel → Relation → Prop
  | .read t, out => out.Perm (cat t).rows
  | .values _ rows, out => out.Perm rows
  | .filter r c, out => ∃ i, r.OrderAllowed cat i ∧ out = i.filter fun row => (c.eval row).isTrue
  | .project r es, out => ∃ i, r.OrderAllowed cat i ∧
      out = i.map fun row => row ++ es.map (·.eval row)
  | .emit r m, out => ∃ i, r.OrderAllowed cat i ∧ out = i.map fun row => m.map (row.getD · .null)
  | .cross a b, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm (crossRows x y)
  | .join a b .inner on, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm ((crossRows x y).filter fun row => (on.eval row).isTrue)
  | .join a b .left on, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm (x.flatMap (leftJoinRow on (b.arity cat) y))
  -- The first rows of any order: any rows, unless an `ORDER BY` fixes it.
  | .fetch r off cnt, out => ∃ i, r.OrderAllowed cat i ∧ out = match cnt with
      | none => i.drop off
      | some n => (i.drop off).take n
  | .unionAll a b, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm (x ++ y)
  -- The window functions over the input in any order its sort allows.
  | .window r part sort fns, out => ∃ i, r.OrderAllowed cat i ∧ ∃ s, s.Perm i ∧
      s.Pairwise (sortLe sort · · = true) ∧ out.Perm (windowRows part fns [] s)
  | .semi a b anti on, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row != anti)
  -- The input sorted, ties and a clustered key's groups in any order.
  | .orderBy r keys, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm i ∧ SortAllowed keys out
  | .distinct r, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm (distinctRows i)
  | .aggregate r gs ms, out => ∃ i, r.OrderAllowed cat i ∧ ∃ o, out.Perm o ∧
      aggOrderAllowed gs ms i o
  | .unnest r c, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm (i.flatMap (unnestRow c))

/-- **`Rel.eval` takes one of the orders**: the deterministic profile's. -/
theorem Rel.eval_orderAllowed (cat : Catalog) : ∀ r : Rel, r.OrderAllowed cat (r.eval cat)
  | .read _ | .values _ _ => .refl _
  | .filter r _ | .project r _ | .emit r _ => ⟨_, eval_orderAllowed cat r, rfl⟩
  | .cross a b | .unionAll a b | .semi a b _ _ =>
    ⟨_, _, eval_orderAllowed cat a, eval_orderAllowed cat b, .refl _⟩
  | .join a b .inner _ | .join a b .left _ =>
    ⟨_, _, eval_orderAllowed cat a, eval_orderAllowed cat b, .refl _⟩
  | .fetch r _ cnt => ⟨_, eval_orderAllowed cat r, by cases cnt <;> rfl⟩
  | .window r _ sort _ => ⟨_, eval_orderAllowed cat r, _, List.mergeSort_perm _ _,
      mergeSort_sorted sort _, .refl _⟩
  | .orderBy r keys => ⟨_, eval_orderAllowed cat r, List.mergeSort_perm _ _,
      .of_sorted (mergeSort_sorted keys _)⟩
  | .distinct r | .unnest r _ => ⟨_, eval_orderAllowed cat r, .refl _⟩
  | .aggregate r gs ms => ⟨_, eval_orderAllowed cat r, _, .refl _,
      aggregateEval_orderAllowed gs ms _⟩

/-- A row of a window over a sorted list: the rows before it sort no later,
the rows after no earlier. -/
theorem mem_windowRows_sorted {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {s : Relation} {row : Row} (hs : s.Pairwise (sortLe sort · · = true))
    (h : row ∈ windowRows part fns [] s) :
    ∃ b x a, s = b ++ x :: a ∧ row = x ++ fns.map (·.value part b a x) ∧
      (∀ y ∈ b, sortLe sort y x = true) ∧ (∀ y ∈ a, sortLe sort x y = true) ∧
      ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → y ∈ s := by
  obtain ⟨b, x, a, he, rfl⟩ := mem_windowRows h
  rw [List.nil_append] at he
  have hs' := hs
  rw [he, List.pairwise_append, List.pairwise_cons] at hs'
  refine ⟨b, x, a, he, rfl, fun y hy => hs'.2.2 y hy x (by simp), fun y hy => hs'.2.1.1 y hy,
    fun y hy => ?_⟩
  rw [he]; rcases hy with rfl | hy | hy <;> simp [*]

/-- Every row of every order has the arity `Rel.arity` predicts. -/
theorem Rel.orderAllowed_arity {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, row.length = r.arity cat
  | .read t, _, _, h, row, hr => hcat t row (h.mem_iff.mp hr)
  | .values _ _, hwf, _, h, row, hr => hwf row (h.mem_iff.mp hr)
  | .filter r _, hwf, _, ⟨i, hi, rfl⟩, row, hr =>
    orderAllowed_arity hcat hwf.1 hi row (List.mem_filter.mp hr).1
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    simp [arity, orderAllowed_arity hcat hwf.1 hi x hx]
  | .emit _ _, _, _, ⟨_, _, rfl⟩, row, hr => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [arity]
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
    simp [arity, orderAllowed_arity hcat hwf.1 hx u hu, orderAllowed_arity hcat hwf.2 hy v hv]
  | .join a b .inner _, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (List.mem_filter.mp (h.mem_iff.mp hr)).1
    simp [arity, orderAllowed_arity hcat hwf.1 hx u hu, orderAllowed_arity hcat hwf.2.1 hy v hv]
  | .join a b .left _, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
    obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
    have hul := orderAllowed_arity hcat hwf.1 hx u hu
    unfold leftJoinRow at h
    simp only [] at h
    split at h
    · simp only [List.mem_singleton] at h
      subst h
      simp [arity, hul]
    · simp only [List.mem_filter, List.mem_map] at h
      obtain ⟨⟨v, hv, rfl⟩, _⟩ := h
      simp [arity, hul, orderAllowed_arity hcat hwf.2.1 hy v hv]
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
    have := orderAllowed_arity hcat (r := r) hwf hi
    cases cnt with
    | none => exact this row (List.mem_of_mem_drop hr)
    | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
    rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
    · exact orderAllowed_arity hcat hwf.1 hx row h
    · simp only [arity, hwf.2.2]; exact orderAllowed_arity hcat hwf.2.1 hy row h
  | .window r _ _ _, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
    obtain ⟨_, x, _, _, rfl, _, _, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
    simp [arity, orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp (hin x (.inl rfl)))]
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
    orderAllowed_arity hcat hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
    orderAllowed_arity hcat hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
    orderAllowed_arity hcat (r := r) hwf hi row (canonReps_sub (h.mem_iff.mp hr))
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
    obtain ⟨k, vs, _, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
    have hkl : k.length = gs.length := by
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
    simp [arity, hkl, ← hv.length_eq]
  | .unnest r _, hwf, _, ⟨i, hi, h⟩, row, hr => by
    obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
    obtain ⟨_, _, _, _, rfl⟩ := mem_unnestRow h
    simp [arity, orderAllowed_arity hcat hwf.1 hi x hx]

/-! ## Windows keyed on every order -/

/-- Windows whose partition and sort columns contain a key on every order. -/
def WindowKeys.SoundAll (T : WindowKeys) (cat : Catalog) : Prop :=
  ∀ r part sort, T r part sort = true → r.WF cat → ∀ {i : Relation}, r.OrderAllowed cat i →
    KeyOn (part ++ sort.map (·.col)) i

theorem WindowKeys.SoundAll.sound {T : WindowKeys} {cat : Catalog} (h : T.SoundAll cat) :
    T.Sound cat :=
  fun r part sort ht hwf => h r part sort ht hwf (r.eval_orderAllowed cat)

theorem WindowKeys.none_soundAll (cat : Catalog) : WindowKeys.none.SoundAll cat :=
  fun _ _ _ h => by simp [WindowKeys.none] at h

end Substrait
