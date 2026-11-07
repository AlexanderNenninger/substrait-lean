import SubstraitLean.Allowed

/-!
# Every order the reference allows (#679, D24)

The reference leaves the order of rows open, and with it how ties are broken
(`tie_order`, `tie_pick`): the rows that tie in an `ORDER BY` or in a
window's order come in any order, a `FETCH` takes the first rows of any
order the plan allows, and `FIRST`, `LAST`, `ARG_MIN`/`ARG_MAX`,
`STRING_AGG`, `collect` and `MODE` take their rows in any order their own
`ORDER BY` allows. `Rel.eval` picks one of these orders (a stable
`List.mergeSort`, rows in list order): it is the evaluator of the
deterministic profile, which fixes them.

`Rel.OrderAllowed` holds the results of every such order. It is
`Rel.Allowed` with every other choice taken as `Rel.eval` takes it: a double
`SUM` or a statistical aggregate keeps `Rel.eval`'s value, so `sum_order` and
`stat_algo` stay with `Rel.Allowed` and #85's bounds.

* `Rel.eval_orderAllowed`: `Rel.eval`'s result is one of them;
  `Rel.orderAllowed_allowed`: each is one `Rel.Allowed` allows.
* `Rel.aeval_sound_all`, `Rel.facts_sound_all`, `Rel.keys_sound_all`,
  `Rel.maxRows_sound_all`: the abstract interpreter, the facts, the derived
  keys and the row bounds describe every row of every order, as they do
  `Rel.eval`'s.
* `contract_sound_all`: a postcondition the checker proves holds on every
  row of every order. So a contract about ties holds for every tie choice,
  and the checker proves postconditions over windows, `FIRST` or a `FETCH`
  whose order the plan leaves open.
-/

namespace Substrait

/-! ## Lists -/

theorem Forall2.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ {b : β}, b ∈ l' → ∃ a ∈ l, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, hr⟩ := Forall2.mem_right t h
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem Forall2.getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ i : Nat,
      (∃ a b, l[i]? = some a ∧ l'[i]? = some b ∧ R a b) ∨ (l[i]? = none ∧ l'[i]? = none)
  | _, _, .nil, _ => .inr ⟨rfl, rfl⟩
  | _, _, .cons hab _, 0 => .inl ⟨_, _, rfl, rfl, hab⟩
  | _, _, .cons _ t, i + 1 => by simpa using Forall2.getElem? t i

theorem Forall2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [Forall2.length_eq t]

theorem Forall2.weaken {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons hab t => .cons (h _ _ hab) (Forall2.weaken h t)

/-! ## Measures -/

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

theorem Measure.OrderAllowed.allowed {m : Measure} {rows : Relation} {v : Value}
    (h : m.OrderAllowed rows v) : m.Allowed rows v := by
  obtain ⟨s, hp, hs, rfl⟩ := h
  split
  · next hsorts =>
    refine ⟨s, hp, fun _ => hs, ?_⟩
    rw [Measure.eval_sorts hsorts, mergeSort_eq_of_sorted hs]
    exact AggFn.apply_allowed _ _
  · exact Measure.eval_allowed m rows

/-- What an aggregate's output may be for some order of each group's rows:
`aggAllowed` with `Measure.OrderAllowed`. -/
def aggOrderAllowed (gs : List Expr) (ms : List Measure) (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.OrderAllowed rows v) ms vs
  else Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.OrderAllowed (groupRows gs rows k) v) ms vs)
    (dedup (rows.map (groupKey gs))) out

theorem aggregateEval_orderAllowed (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggOrderAllowed gs ms rows (aggregateEval gs ms rows) := by
  unfold aggOrderAllowed aggregateEval
  split
  · exact ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m rows⟩
  · exact forall₂_map_self _ fun k _ =>
      ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m _⟩

theorem aggOrderAllowed_allowed {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (h : aggOrderAllowed gs ms rows out) : aggAllowed gs ms rows out := by
  have hm : ∀ {grp : Relation} {vs : List Value},
      Forall2 (fun m v => m.OrderAllowed grp v) ms vs → Forall2 (fun m v => m.Allowed grp v) ms vs :=
    Forall2.weaken fun _ _ h => h.allowed
  unfold aggOrderAllowed at h; unfold aggAllowed
  split at h
  · next hg => obtain ⟨vs, rfl, hv⟩ := h; simp only [hg, ite_true]; exact ⟨vs, rfl, hm hv⟩
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    exact Forall2.weaken (fun _ _ ⟨vs, he, hv⟩ => ⟨vs, he, hm hv⟩) h

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
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
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
  | .distinct r, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm (dedup i)
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

/-- **Every order is one the reference allows.** -/
theorem Rel.orderAllowed_allowed {cat : Catalog} :
    ∀ {r : Rel} {out : Relation}, r.OrderAllowed cat out → r.Allowed cat out
  | .read _, _, h | .values _ _, _, h => h
  | .filter r _, _, ⟨i, hi, h⟩ | .project r _, _, ⟨i, hi, h⟩ | .emit r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .fetch r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .cross a b, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_allowed (r := a) hx, orderAllowed_allowed (r := b) hy, h⟩
  | .join a b .inner _, _, ⟨x, y, hx, hy, h⟩ | .join a b .left _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_allowed (r := a) hx, orderAllowed_allowed (r := b) hy, h⟩
  | .window r _ _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .orderBy r _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .distinct r, _, ⟨i, hi, h⟩ | .unnest r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .aggregate r _ _, _, ⟨i, hi, o, h, ho⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, o, h, aggOrderAllowed_allowed ho⟩

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
    orderAllowed_arity hcat (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
    obtain ⟨k, vs, _, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
    have hkl : k.length = gs.length := by
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
    simp [arity, hkl, ← hv.length_eq]
  | .unnest r _, hwf, _, ⟨i, hi, h⟩, row, hr => by
    obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
    obtain ⟨_, _, _, _, rfl⟩ := mem_unnestRow h
    simp [arity, orderAllowed_arity hcat hwf.1 hi x hx]

/-! ## Row bounds -/

theorem Rel.maxRows_sound_all {cat : Catalog} :
    ∀ {r : Rel} {n : Nat}, r.maxRows = some n → ∀ {out : Relation}, r.OrderAllowed cat out →
      out.length ≤ n
  | .read _, _, h, _, _ => by simp [maxRows] at h
  | .values _ _, _, h, _, ho => by
    simp only [maxRows, Option.some.injEq] at h; rw [ho.length_eq, h]; exact Nat.le_refl _
  | .filter r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .project r _, _, h, _, ⟨i, hi, rfl⟩ | .emit r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h; simp only [List.length_map]; exact maxRows_sound_all (r := r) h hi
  | .orderBy r _, _, h, _, ⟨i, hi, hp, _⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]; exact maxRows_sound_all (r := r) h hi
  | .distinct r, _, h, _, ⟨i, hi, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans (dedup_length_le _) (maxRows_sound_all (r := r) h hi)
  | .semi r _ _ _, _, h, _, ⟨i, _, hi, _, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .window r _ _ _, _, h, _, ⟨i, hi, s, hs, _, hp⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq, windowRows_length, hs.length_eq]
    exact maxRows_sound_all (r := r) h hi
  | .fetch r _ cnt, n, h, _, ⟨i, hi, rfl⟩ => by
    cases cnt with
    | none =>
      simp only [maxRows] at h
      have := maxRows_sound_all (cat := cat) h hi
      simp only [List.length_drop]; omega
    | some k =>
      cases hr : r.maxRows with
      | none =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h; simp only [List.length_take]; exact Nat.min_le_left _ _
      | some m =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h
        have := maxRows_sound_all (cat := cat) hr hi
        simp only [List.length_take, List.length_drop]; omega
  | .cross a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, length_crossRows]
    exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .join a b .inner _, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _)
      (by rw [length_crossRows]; exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy))
  | .join _ _ .left _, _, h, _, _ => by simp [maxRows] at h
  | .unionAll a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, List.length_append]
    exact Nat.add_le_add (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .aggregate r gs _, n, h, _, ⟨i, hi, o, hp, ho⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq]
    unfold aggOrderAllowed at ho
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp only [hg, ite_true] at ho
      obtain ⟨_, rfl, _⟩ := ho; exact Nat.le_refl _
    · rename_i hg
      simp only [hg, Bool.false_eq_true, ite_false] at ho
      rw [← ho.length_eq]
      exact Nat.le_trans (dedup_length_le _) (by simpa using maxRows_sound_all (r := r) h hi)
  | .unnest _ _, _, h, _, _ => by simp [maxRows] at h

/-! ## Facts and the abstract interpreter -/

/-- Windows whose partition and sort columns contain a key on every order. -/
def WindowKeys.SoundAll (T : WindowKeys) (cat : Catalog) : Prop :=
  ∀ r part sort, T r part sort = true → r.WF cat → ∀ {i : Relation}, r.OrderAllowed cat i →
    KeyOn (part ++ sort.map (·.col)) i

theorem WindowKeys.SoundAll.sound {T : WindowKeys} {cat : Catalog} (h : T.SoundAll cat) :
    T.Sound cat :=
  fun r part sort ht hwf => h r part sort ht hwf (r.eval_orderAllowed cat)

theorem WindowKeys.none_soundAll (cat : Catalog) : WindowKeys.none.SoundAll cat :=
  fun _ _ _ h => by simp [WindowKeys.none] at h

/-- The facts relating two measures are about measures that do not sort. -/
theorem pairFacts_sorts {ci cj : Nat} {mi mj : Measure} (h : pairFacts ci cj mi mj ≠ []) :
    mi.fn.sorts = false ∧ mj.fn.sorts = false := by
  unfold pairFacts at h
  repeat' split at h
  all_goals first | exact absurd rfl h | (simp_all [AggFn.sorts])

/-- `aggFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem aggFacts_sound_of {g : Nat} {ms : List Measure} {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp) :
    FactsHold (aggFacts g ms) row := by
  intro f hf
  simp only [aggFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    have hs := pairFacts_sorts (List.ne_nil_of_mem hf)
    exact pairFacts_sound (col i mi hmi hs.1) (col j mj hmj hs.2) f hf
  · simp at hf

/-- `ratioFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem ratioFacts_sound_of {g : Nat} {env : List AVal} {fs : List Fact} {ms : List Measure}
    {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp)
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) :
    FactsHold (ratioFacts g env fs ms) row := by
  intro f hf
  simp only [ratioFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    split at hf
    · rename_i hc
      obtain ⟨hsum, hcount, harg, hfil, hdis, honly⟩ := hc
      split at hf
      · rename_i b hb
        simp only [List.mem_singleton] at hf; subst hf
        intro x n hx hn
        rw [col i mi hmi (by rw [hsum]; rfl), Measure.eval_eq (by rw [hsum]; rfl), hsum] at hx
        rw [col j mj hmj (by rw [hcount]; rfl), Measure.eval_eq (by rw [hcount]; rfl), hcount] at hn
        have hsame : mj.inputs grp = mi.inputs grp := by
          simp only [Measure.inputs, Measure.kept, harg, hfil, hdis]
        rw [hsame] at hn
        cases hvs : mi.inputs grp with
        | nil => rw [hvs] at hx; simp [AggFn.apply] at hx
        | cons v vs =>
          rw [hvs] at hx hn
          simp only [AggFn.apply] at hx hn
          have hx' := sumOf_unscaled hx
          simp only [Value.unscaled?, Option.some.injEq] at hn
          subst hx' hn
          have hint : ∀ w ∈ v :: vs, ∃ i, w.unscaled? = some i ∧ b.Mem i := by
            intro w hw
            have hw' : w ∈ mi.inputs grp := hvs ▸ hw
            obtain ⟨hnn, y, hy, rfl⟩ := Measure.mem_inputs hw'
            have hm := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) mi.arg
            obtain ⟨i, b', he, hb', hi⟩ := AVal.unscaledOnly_mem honly hm hnn
            rw [hb] at hb'; cases hb'
            exact ⟨i, he, hi⟩
          obtain ⟨hlo, hhi⟩ := intSum_bounds hint
          exact ⟨by simp, hlo, hhi⟩
      · simp at hf
    · simp at hf
  · simp at hf

/-- The measures' columns of an aggregate's row, for `aggFacts_sound_of`. -/
theorem aggCol {ms : List Measure} {grp : Relation} {k : Row} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) :
    ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      (k ++ vs).getD (k.length + i) .null = m.eval grp := by
  intro i m hm hs
  rw [getD_append_right']
  rcases hv.getElem? i with ⟨a, v, ha, hb, hr⟩ | ⟨ha, _⟩
  · rw [hm] at ha; cases ha
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
    obtain ⟨_, _, _, h⟩ := hr.eval
    exact h hs
  · rw [hm] at ha; cases ha

theorem EnvMem.measures_all {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) {ms : List Measure} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    EnvMem (ms.map fun m => Measure.abs env fs m grouped rows) vs := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hv.getElem? j with ⟨m, v, hm, hb, hr⟩ | ⟨hm, hb⟩
  · obtain ⟨s, hp, rfl, _⟩ := hr.eval
    simp only [hm, hb, Option.map_some, Option.getD_some]
    exact Measure.abs_sound (grp := s) (fun y hy => hall y (hp.mem_iff.mp hy)) m grouped
      (fun hg hs => hne hg (List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, hs]; rfl))) rows
      (fun n hn => hp.length_eq ▸ hrows n hn)
  · simp [hm, hb, AVal.mem_top]

/-- **The facts hold on every row of every order.** -/
theorem Rel.facts_sound_all {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.facts cat F T) row
  | .read t, _, _, h, row, hr => hF t row (h.mem_iff.mp hr)
  | .values _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact (facts_sound_all hcat hF hT hwf.1 hi row hr.1).append (c.factsOf_sound hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      have hfx := facts_sound_all hcat hF hT hwf.1 hi x hx
      have hpre : ∀ i < r.arity cat, (x ++ es.map (·.eval x)).getD i .null = x.getD i .null :=
        fun i hi => getD_append_left' (hlen ▸ hi)
      simp only [Rel.facts]
      refine FactsHold.append ?_ (linFacts_sound hpre _ es fun k hk => ?_)
      · intro g hg
        simp only [List.mem_flatMap, List.mem_filter] at hg
        obtain ⟨f, ⟨hf, hfr⟩, hg⟩ := hg
        exact Fact.rename_holds_inRange (fun i hi p hp => copyCols_getD hlen hi hp) hfr (hfx f hf) g hg
      · rw [← hlen, getD_append_right']
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (facts_sound_all hcat hF hT hwf.1 hi x hx).rename fun i p hp => positions_getD hp
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact ((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2 hy v hv).shift fun i => hlen ▸ getD_append_right' i)
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact (((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2.1 hy v hv).shift fun i => hlen ▸ getD_append_right' i)).append
        (on.factsOf_sound ht)
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      have hfx := facts_sound_all hcat hF hT hwf.1 hx u hu
      simp only [Rel.facts]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (FactsHold.shift_nulls fun i => by
            rw [← hlen, getD_append_right']
            simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)).append
          (FactsHold.rightOf_nulls fun i hi => getD_pad_null (hlen ▸ hi))
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨v, hv, rfl⟩, ht⟩ := h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (((facts_sound_all hcat hF hT hwf.2.1 hy v hv).filter _).shift
            fun i => hlen ▸ getD_append_right' i)).append
          fun f hf => on.factsOf_sound ht f (List.mem_filter.mp hf).1
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := facts_sound_all hcat hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      facts_sound_all hcat hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      simp only [Rel.facts]
      exact aggFacts_sound_of (grp := grp) (hkl ▸ aggCol hv)
  | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      intro f hf
      simp only [Rel.facts, List.mem_filter, List.contains_iff_mem] at hf
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact facts_sound_all hcat hF hT hwf.1 hx row h f hf.1
      · exact facts_sound_all hcat hF hT hwf.2.1 hy row h f hf.2
  | .window r part sort _, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, he, rfl, hb, ha, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hx := hp.mem_iff.mp (hin x (.inl rfl))
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      simp only [Rel.facts]
      refine ((facts_sound_all hcat hF hT hwf.1 hi x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        (winFacts_sound hlen hwf.2.2.2 hb ha fun hT' y hy _ => ?_)
      -- With a key, rows at different positions of the sorted input differ on it.
      have hk := (hT _ _ _ hT' hwf.1 hi).perm hp.symm fun h => Ne.symm h
      unfold KeyOn at hk
      rw [he, List.pairwise_append, List.pairwise_cons] at hk
      rcases hy with hy | hy
      · exact hk.2.2 y hy x (by simp)
      · exact Ne.symm (hk.2.1.1 y hy)

mutual
/-- **The abstract interpreter describes every row of every order.** -/
theorem Rel.aeval_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, EnvMem (r.aeval cat A F T) row
  | .read t, _, _, h, row, hr =>
      useFacts_sound (hF t row (h.mem_iff.mp hr)) ((hA t row (h.mem_iff.mp hr)).fit _)
  | .values _ _, _, _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact useFacts_sound ((Rel.facts_sound_all hcat hF hT hwf.1 hi row hr.1).append
        (c.factsOf_sound hr.2)) (Expr.refine_sound _ c (aeval_sound_all hcat hA hF hT hwf.1 hi row hr.1) hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hm := aeval_sound_all hcat hA hF hT hwf.1 hi x hx
      have hrp := ratioPart_sound_all hcat hA hF hT hwf.1 hi x hx
      exact hm.append (hm.mapF ((Rel.facts_sound_all hcat hF hT hwf.1 hi x hx).append hrp) es)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x hx])
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).emit m
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      exact (aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      exact Expr.refine_sound _ on ((aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])) ht
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hum := aeval_sound_all hcat hA hF hT hwf.1 hx u hu
      have hl : (a.aeval cat A F T).length = u.length := by
        rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hum.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨v, hv, rfl⟩, _⟩ := h
        exact hum.append (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv).nullable hl
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := aeval_sound_all hcat hA hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .unnest r c, hwf, _, ⟨i, hi, h⟩, row, hr => by
      obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      obtain ⟨_, v, _, _, rfl⟩ := mem_unnestRow h
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).set_top c v
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, hne, hglen⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
      have hm := EnvMem.measures_all hall hv (!gs.isEmpty) (fun hg => hne (by simpa using hg))
        (rows := r.maxRows) (fun n hn => Nat.le_trans hglen (Rel.maxRows_sound_all hn hi))
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) hm (by simp)
      · exact (EnvMem.mapD (aeval_sound_all hcat hA hF hT hwf.1 hi x hx)
          (Rel.facts_sound_all hcat hF hT hwf.1 hi x hx) gs).append hm (by simp)
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact (aeval_sound_all hcat hA hF hT hwf.1 hx row h).zip_left
      · exact (aeval_sound_all hcat hA hF hT hwf.2.1 hy row h).zip_right
  | .window r _ _ fns, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, _, rfl, _, _, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T) y :=
        fun y hy => aeval_sound_all hcat hA hF hT hwf.1 hi y (hp.mem_iff.mp (hin y hy))
      exact (hall x (.inl rfl)).append (EnvMem.window (sz := false) hall nofun fns)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp (hin x (.inl rfl)))])

theorem Rel.ratioPart_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.ratioPart cat A F T) row
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, -⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      exact ratioFacts_sound_of (hkl ▸ aggCol hv) fun y hy =>
        ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
  | .read _, _, _, _, _, _ | .values _ _, _, _, _, _, _ | .filter _ _, _, _, _, _, _
  | .project _ _, _, _, _, _, _ | .emit _ _, _, _, _, _, _ | .cross _ _, _, _, _, _, _
  | .join _ _ _ _, _, _, _, _, _ | .fetch _ _ _, _, _, _, _, _ | .unionAll _ _, _, _, _, _, _
  | .window _ _ _ _, _, _, _, _, _ | .semi _ _ _ _, _, _, _, _, _ | .orderBy _ _, _, _, _, _, _
  | .distinct _, _, _, _, _, _ | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [ratioPart] at hf
end

/-! ## Keys -/

/-- An aggregate's group columns are a key of its output, in every order. -/
theorem aggOrderAllowed_key {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (h : aggOrderAllowed gs ms rows out) : KeyOn (List.range gs.length) out := by
  unfold aggOrderAllowed at h
  split at h
  · obtain ⟨_, rfl, _⟩ := h; exact List.pairwise_singleton _ _
  · have hmap : ∀ {ks : List Row} {out : Relation}, (∀ k ∈ ks, k.length = gs.length) →
        Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
          Forall2 (fun m v => m.OrderAllowed (groupRows gs rows k) v) ms vs) ks out →
        out.map (keyOf (List.range gs.length)) = ks := by
      intro ks out hl h
      induction h with
      | nil => rfl
      | cons hk _ ih =>
        obtain ⟨vs, rfl, _⟩ := hk
        have hlk := hl _ (List.mem_cons_self ..)
        rw [List.map_cons, ih fun k hk => hl k (List.mem_cons_of_mem _ hk)]
        simp only [List.cons.injEq, and_true]
        rw [← hlk]; exact keyOf_range_append
    have hl : ∀ k ∈ dedup (rows.map (groupKey gs)), k.length = gs.length := fun k hk => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk); simp [groupKey]
    unfold KeyOn
    rw [← List.pairwise_map, hmap hl h]
    exact dedup_pairwise _

/-- **Derived keys hold on every order.** -/
theorem Rel.keys_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → ∀ k ∈ r.keys cat A F K, ∀ {out : Relation}, r.OrderAllowed cat out →
      KeyOn k out
  | .read t, _, k, hk, _, h => (hK t k hk).perm h.symm fun h => Ne.symm h
  | .values _ rows, _, k, hk, _, h => by
      simp only [Rel.keys] at hk
      split at hk
      · simp only [List.mem_singleton] at hk
        subst hk
        exact KeyOn.of_length_le_one (h.length_eq ▸ ‹_›)
      · simp at hk
  | .filter r c, hwf, k, hk, _, ⟨i, hi, rfl⟩ => by
      simp only [Rel.keys, mem_dedup, List.mem_flatMap, List.mem_map] at hk
      obtain ⟨_, ⟨k₀, hk₀, rfl⟩, hv⟩ := hk
      refine KeyOn.eqVariants ?_ (fun x hx => by
        simp only [List.mem_filter] at hx; exact hx.2) hv
      have := keys_sound_all hcat hA hF hK hwf.1 k₀ hk₀ hi
      unfold KeyOn at *
      rw [List.pairwise_filter]
      refine this.imp fun {x y} hne hx hy heq => hne ?_
      have hp := Expr.pinned_sound hx hy
      simp only [keyOf, List.map_inj_left, List.mem_filter, Bool.not_eq_true'] at heq ⊢
      intro i hi
      by_cases h : i ∈ c.pinned
      · exact hp i h
      · exact heq i ⟨hi, by simpa using h⟩
  | .project r es, hwf, k, hk, _, ⟨i, hi, rfl⟩ => by
      simp only [Rel.keys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨k₀, ⟨hk₀, hr⟩, hv⟩ := hk
      have := keys_sound_all hcat hA hF hK hwf.1 k₀ hk₀ hi
      unfold KeyOn at *
      rw [List.pairwise_map]
      refine this.imp_of_mem fun {x y} hx hy hne heq => hne ?_
      refine variants_inj (fun c hc p hp he => ?_) hv heq
      rcases List.mem_append.mp hp with hp | hp
      · rwa [copyCols_getD (orderAllowed_arity hcat hwf.1 hi _ hx) (hr c hc) hp,
          copyCols_getD (orderAllowed_arity hcat hwf.1 hi _ hy) (hr c hc) hp] at he
      · exact linCols_inj (orderAllowed_arity hcat hwf.1 hi _ hx)
          (orderAllowed_arity hcat hwf.1 hi _ hy)
          (aeval_sound_all hcat hA hF (WindowKeys.none_soundAll cat) hwf.1 hi _ hx)
          (aeval_sound_all hcat hA hF (WindowKeys.none_soundAll cat) hwf.1 hi _ hy) hp he
  | .emit r m, hwf, k, hk, _, ⟨i, hi, rfl⟩ => by
      simp only [Rel.keys, List.mem_filterMap] at hk
      obtain ⟨k₀, hk₀, he⟩ := hk
      have := keys_sound_all hcat hA hF hK hwf.1 k₀ hk₀ hi
      unfold KeyOn at *
      rw [List.pairwise_map]
      refine this.imp fun hne heq => hne ?_
      rwa [emitKey_keyOf he, emitKey_keyOf he] at heq
  | .cross a b, hwf, k, hk, _, ⟨x, y, hx, hy, h⟩ => by
      simp only [Rel.keys, crossKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk
      exact (crossRows_key (orderAllowed_arity hcat hwf.1 hx) hkr
        (keys_sound_all hcat hA hF hK hwf.1 ka hka hx)
        (keys_sound_all hcat hA hF hK hwf.2 kb hkb hy)).perm h.symm fun h => Ne.symm h
  | .join a b .inner on, hwf, k, hk, _, ⟨x, y, hx, hy, h⟩ => by
      simp only [Rel.keys, joinEqKeys, mem_dedup, List.mem_flatMap] at hk
      obtain ⟨k₁, hk₁, hv⟩ := hk
      refine KeyOn.eqVariants ?_ (fun u hu => by
        have := h.subset hu
        simp only [List.mem_filter] at this; exact this.2) hv
      simp only [joinKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk₁
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk₁
      have hA' := orderAllowed_arity hcat hwf.1 hx
      refine List.Pairwise.perm ?_ h.symm fun h => Ne.symm h
      show KeyOn _ _
      simp only [crossRows, List.filter_flatMap]
      exact flatMap_key (keys_sound_all hcat hA hF hK hwf.1 ka hka hx)
        (fun u hu r hr => by
          simp only [List.mem_filter, List.mem_map] at hr
          obtain ⟨⟨v, _, rfl⟩, _⟩ := hr
          exact keyOf_append_left fun c hc => hA' u hu ▸ hkr c hc)
        (fun u hu => match_block (hA' u hu) (keys_sound_all hcat hA hF hK hwf.2.1 kb hkb hy))
  | .join a b .left on, hwf, k, hk, _, ⟨x, y, hx, hy, h⟩ => by
      simp only [Rel.keys, joinEqKeys, joinKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk
      have hA' := orderAllowed_arity hcat hwf.1 hx
      refine List.Pairwise.perm ?_ h.symm fun h => Ne.symm h
      show KeyOn _ _
      refine flatMap_key (keys_sound_all hcat hA hF hK hwf.1 ka hka hx) (fun u hu r hr => ?_)
        (fun u hu => ?_)
      · unfold leftJoinRow at hr
        simp only [] at hr
        split at hr
        · simp only [List.mem_singleton] at hr; subst hr
          exact keyOf_append_left fun c hc => hA' u hu ▸ hkr c hc
        · simp only [List.mem_filter, List.mem_map] at hr
          obtain ⟨⟨v, _, rfl⟩, _⟩ := hr
          exact keyOf_append_left fun c hc => hA' u hu ▸ hkr c hc
      · unfold leftJoinRow
        simp only []
        split
        · exact List.pairwise_singleton _ _
        · exact match_block (hA' u hu) (keys_sound_all hcat hA hF hK hwf.2.1 kb hkb hy)
  | .fetch r _ cnt, hwf, k, hk, _, ⟨i, hi, rfl⟩ => by
      simp only [Rel.keys, List.mem_append] at hk
      rcases hk with hk | hk
      · split at hk
        · simp only [List.mem_singleton] at hk
          subst hk
          obtain ⟨n, rfl, hn⟩ : ∃ n, cnt = some n ∧ n ≤ 1 := by
            cases cnt <;> simp_all
          exact KeyOn.of_length_le_one (Nat.le_trans (List.length_take_le _ _) hn)
        · simp at hk
      have := keys_sound_all hcat hA hF hK (r := r) hwf k hk hi
      cases cnt with
      | none => exact this.sublist (List.drop_sublist _ _)
      | some _ => exact this.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  | .unionAll a b, hwf, k, hk, _, ⟨x, y, hx, hy, h⟩ => by
      simp only [Rel.keys, unionKeys] at hk
      split at hk
      · rename_i c hc
        have hdis := List.find?_some hc
        obtain ⟨ka, hka, kb, hkb, rfl⟩ : ∃ ka ∈ a.keys cat A F K, ∃ kb ∈ b.keys cat A F K,
            k = ka ++ kb ++ [c] := by
          have := List.mem_of_mem_take hk
          simp only [List.mem_flatMap, List.mem_map] at this
          obtain ⟨ka, hka, kb, hkb, rfl⟩ := this
          exact ⟨ka, hka, kb, hkb, rfl⟩
        refine List.Pairwise.perm ?_ h.symm fun h => Ne.symm h
        show KeyOn _ _
        unfold KeyOn
        rw [List.pairwise_append]
        refine ⟨(keys_sound_all hcat hA hF hK hwf.1 ka hka hx).superset (by simp_all),
          (keys_sound_all hcat hA hF hK hwf.2.1 kb hkb hy).superset (by simp_all), ?_⟩
        intro u hu v hv heq
        have hum := aeval_sound_all hcat hA hF (WindowKeys.none_soundAll cat) hwf.1 hx u hu c
        have hvm := aeval_sound_all hcat hA hF (WindowKeys.none_soundAll cat) hwf.2.1 hy v hv c
        apply AVal.disjoint_ne hdis hum hvm
        simp only [keyOf, List.map_inj_left] at heq
        exact heq c (by simp)
      · simp at hk
  | .semi a _ _ _, hwf, k, hk, _, ⟨x, _, hx, _, h⟩ =>
      ((keys_sound_all hcat hA hF hK hwf.1 k hk hx).sublist List.filter_sublist).perm h.symm
        fun h => Ne.symm h
  | .orderBy r _, hwf, k, hk, _, ⟨i, hi, h, _⟩ =>
      (keys_sound_all hcat hA hF hK (r := r) hwf.1 k hk hi).perm h.symm fun h => Ne.symm h
  | .unnest _ _, _, k, hk, _, _ => by simp [Rel.keys] at hk
  | .distinct r, hwf, k, hk, _, ⟨i, hi, h⟩ => by
      refine List.Pairwise.perm ?_ h.symm fun h => Ne.symm h
      simp only [Rel.keys, List.mem_cons] at hk
      rcases hk with rfl | hk
      · refine (dedup_pairwise i).imp_of_mem fun hx hy hne => ?_
        rw [keyOf_range (orderAllowed_arity hcat (r := r) hwf hi _ (mem_dedup.mp hx)),
          keyOf_range (orderAllowed_arity hcat (r := r) hwf hi _ (mem_dedup.mp hy))]
        exact hne
      · exact (keys_sound_all hcat hA hF hK (r := r) hwf k hk hi).sublist (dedup_sublist _)
  | .aggregate _ gs _, _, k, hk, _, ⟨_, _, _, h, ho⟩ => by
      simp only [Rel.keys, List.mem_singleton] at hk
      subst hk
      exact (aggOrderAllowed_key ho).perm h.symm fun h => Ne.symm h
  | .window r part sort fns, hwf, k, hk, _, ⟨i, hi, s, hp, hs, h⟩ => by
      refine List.Pairwise.perm ?_ h.symm fun h => Ne.symm h
      show KeyOn _ _
      have harity : ∀ x ∈ s, x.length = r.arity cat :=
        fun x hx => orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp hx)
      simp only [Rel.keys, List.mem_append] at hk
      rcases hk with hk | hk
      rotate_left
      · simp only [windowKeys, List.mem_filterMap] at hk
        obtain ⟨⟨f, t⟩, hft, hk⟩ := hk
        split at hk
        · rename_i hf
          subst hf
          simp only [Option.some.injEq] at hk
          subst hk
          exact windowRows_rowNumber_key hwf.2.1 (List.mem_zipIdx_iff_getElem?.mp hft) harity
        · simp at hk
      simp only [List.mem_filter, List.all_eq_true, decide_eq_true_eq] at hk
      have hks : KeyOn k s :=
        (keys_sound_all hcat hA hF hK hwf.1 k hk.1 hi).perm hp.symm fun h => Ne.symm h
      have hmap : (windowRows part fns [] s).map (keyOf k) = s.map (keyOf k) := by
        have ht := windowRows_take (part := part) (fns := fns) (pre := []) (n := r.arity cat)
          (l := s) harity
        conv => rhs; rw [← ht]
        rw [List.map_map]
        exact List.map_congr_left fun row _ => (keyOf_take hk.2).symm
      have h1 : List.Pairwise (· ≠ ·) (s.map (keyOf k)) := List.pairwise_map.mpr hks
      rw [← hmap] at h1
      exact List.pairwise_map.mp h1

/-- The window-key oracle of `ContractCheck` holds on every order. -/
theorem Rel.keyedWindows_soundAll {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) : (Rel.keyedWindows cat A F K).SoundAll cat := by
  intro r part sort h hwf i hi
  obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp h
  simp only [List.all_eq_true, decide_eq_true_eq] at hsub
  exact (keys_sound_all hcat hA hF hK hwf k hk hi).superset hsub

/-! ## Row caps -/

/-- On tables within their caps, every order of a plan is one of the plan
with capped reads (`Rel.capReads`), which the checker interprets. -/
theorem Rel.orderAllowed_capReads {caps : String → Option Nat} {cat : Catalog}
    (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel} {out : Relation}, r.OrderAllowed cat out → (r.capReads caps).OrderAllowed cat out
  | .read t, out, h => by
    unfold capReads
    split
    · rename_i n hn
      refine ⟨out, h, ?_⟩
      simp only [List.drop_zero]
      exact (List.take_of_length_le (h.length_eq ▸ hc t n hn)).symm
    · exact h
  | .values _ _, _, h => h
  | .filter r _, _, ⟨i, hi, h⟩ | .project r _, _, ⟨i, hi, h⟩ | .emit r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .fetch r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .cross a b, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, h⟩
  | .join a b .inner _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, h⟩
  | .join a b .left _, _, ⟨x, y, hx, hy, h⟩ => by
    refine ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, ?_⟩
    rw [capReads_arity]; exact h
  | .window r _ _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .orderBy r _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .distinct r, _, ⟨i, hi, h⟩ | .unnest r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .aggregate r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩

/-! ## Contracts -/

/-- **Contract soundness for every order.** Under `contract_sound`'s
hypotheses, every postcondition holds on every row of every order the
reference allows: for every way an engine breaks ties, takes the rows of a
`FETCH` or orders the rows of `FIRST`, `STRING_AGG` or a window. -/
theorem contract_sound_all {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out → ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  intro out hout row hrow v hv
  have hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold ((pre t).flatMap Expr.factsOf) row := by
    intro t row h f hf
    simp only [List.mem_flatMap] at hf
    obtain ⟨e, he, hf⟩ := hf
    exact Expr.factsOf_sound e (hpre t row h e he) f hf
  have hm := Q.aeval_sound_all hcat (fun t row h => tableEnv_sound (hS t row h) (hpre t row h)) hF
    hT hQ hout row hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : j < (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).length := by
    rw [Rel.aeval_length hQ, ← Rel.orderAllowed_arity hcat hQ hout row hrow]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen)
  have := hm j
  simp only [List.getElem?_eq_getElem hlen, Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

end Substrait
