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
variable [Boxes.Ambient]

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
    if m.fn.sorts then v = m.eval s else m.fn.Picks (m.inputs rows) v

omit [Boxes.Ambient] in
theorem mergeSort_sorted (sort : List SortKey) (rows : Relation) :
    (rows.mergeSort (sortLe sort)).Pairwise (sortLe sort · · = true) :=
  List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total rows

/-- Rows that tie in the measure's order agree on its argument: the order
of the ties, which the reference leaves open, changes none of its inputs. -/
def Measure.TiesAgree (m : Measure) (rows : Relation) : Prop :=
  ∀ x ∈ rows, ∀ y ∈ rows, sortLe m.sort x y = true → sortLe m.sort y x = true →
    m.arg.eval x = m.arg.eval y

theorem Measure.TiesAgree.perm {m : Measure} {xs ys : Relation} (h : m.TiesAgree ys)
    (hp : xs.Perm ys) : m.TiesAgree xs :=
  fun x hx y hy => h x (hp.mem_iff.mp hx) y (hp.mem_iff.mp hy)

/-- Two arrangements of the rows in the measure's order give it the same
inputs, when its ties agree on its argument. -/
theorem Measure.inputs_eq_of_sorted {m : Measure} {s s' : Relation} (hp : s.Perm s')
    (hs : s.Pairwise (sortLe m.sort · · = true)) (hs' : s'.Pairwise (sortLe m.sort · · = true))
    (ht : m.TiesAgree s') : m.inputs s = m.inputs s' := by
  have : (m.kept s).map (fun row => m.arg.eval row) = (m.kept s').map (fun row => m.arg.eval row) := by
    unfold Measure.kept; split
    · exact map_eq_of_perm_of_pairwise hp hs hs' ht
    · exact map_eq_of_perm_of_pairwise (hp.filter _) (hs.filter _) (hs'.filter _)
        fun a ha b hb => ht a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1
  simp only [Measure.inputs, this]

/-- A measure that sorts its rows gives one value on the same rows in any
order, when its ties agree on its argument. -/
theorem Measure.eval_perm_of_ties {m : Measure} (hs : m.fn.sorts = true) {xs ys : Relation}
    (h : xs.Perm ys) (ht : m.TiesAgree ys) : m.eval xs = m.eval ys := by
  rw [Measure.eval_sorts hs, Measure.eval_sorts hs]
  have hy := List.mergeSort_perm ys (sortLe m.sort)
  rw [Measure.inputs_eq_of_sorted ((List.mergeSort_perm xs _).trans (h.trans hy.symm))
    (mergeSort_sorted _ _) (mergeSort_sorted _ _) (ht.perm hy)]

/-- Rows of one group that tie in the measure's order agree on its argument. -/
def Measure.TiesAgreeIn (m : Measure) (gs : List Expr) (rows : Relation) : Prop :=
  ∀ x ∈ rows, ∀ y ∈ rows, (groupKey gs x).canon = (groupKey gs y).canon →
    sortLe m.sort x y = true → sortLe m.sort y x = true → m.arg.eval x = m.arg.eval y

theorem Measure.TiesAgreeIn.group {m : Measure} {gs : List Expr} {rows : Relation}
    (h : m.TiesAgreeIn gs rows) (k : Row) : m.TiesAgree (groupRows gs rows k) := by
  intro x hx y hy
  simp only [groupRows, List.mem_filter, beq_iff_eq] at hx hy
  exact h x hx.1 y hy.1 (hx.2.trans hy.2.symm)

theorem Measure.TiesAgreeIn.nil {m : Measure} {rows : Relation} (h : m.TiesAgreeIn [] rows) :
    m.TiesAgree rows :=
  fun x hx y hy => h x hx y hy rfl

omit [Boxes.Ambient] in
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
  · next h => rw [Measure.eval_eq (by simpa using h)]; exact AggFn.picks_apply _ _

/-- A measure that sorts its rows gives `Measure.eval`'s value over some
order of them; the others give their value over the rows, or for `MIN` and
`MAX` another member of its class (`AggFn.Picks`). -/
theorem Measure.OrderAllowed.eval {m : Measure} {rows : Relation} {v : Value}
    (h : m.OrderAllowed rows v) :
    ∃ s, s.Perm rows ∧ (m.fn.sorts = true → v = m.eval s) ∧
      (m.fn.sorts = false → m.fn.Picks (m.inputs rows) v) := by
  obtain ⟨s, hp, _, h⟩ := h
  split at h
  · next hs => exact ⟨s, hp, fun _ => h, fun h' => by rw [hs] at h'; cases h'⟩
  · next hs => exact ⟨s, hp, fun h' => absurd h' hs, fun _ => h⟩

/-- What an aggregate's output may be for some order of each group's rows:
`aggAllowed` with `Measure.OrderAllowed`. -/
def aggOrderAllowed (gs : List Expr) (ms : List Measure) (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.OrderAllowed rows v) ms vs
  else ∃ ks, IsReps Row.canon (rows.map (groupKey gs)) ks ∧ Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.OrderAllowed (groupRows gs rows k) v) ms vs) ks out

theorem aggregateEval_orderAllowed (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggOrderAllowed gs ms rows (aggregateEval gs ms rows) := by
  unfold aggOrderAllowed aggregateEval
  split
  · exact ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m rows⟩
  · exact ⟨_, canonReps_isReps Row.leRaw_rawOrder _, forall₂_map_self _ fun k _ =>
      ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_orderAllowed m _⟩⟩

/-- A row of an aggregate's output: a group key and the measures' values over
the group's rows, in some order of them. -/
theorem mem_aggOrderAllowed {gs : List Expr} {ms : List Measure} {rows out : Relation}
    {row : Row} (h : aggOrderAllowed gs ms rows out) (hr : row ∈ out) :
    ∃ k vs grp, row = k ++ vs ∧ Forall2 (fun m v => m.OrderAllowed grp v) ms vs ∧
      (∀ y ∈ grp, y ∈ rows) ∧ ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k.canon = (groupKey gs x).canon) ∧
      (gs ≠ [] → grp ≠ []) ∧ grp.length ≤ rows.length := by
  unfold aggOrderAllowed at h
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨[], row, rows, by simp, hv, fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩,
      fun hne => absurd (List.isEmpty_iff.mp hg) hne, Nat.le_refl _⟩
  · obtain ⟨ks, hks, h⟩ := h
    obtain ⟨k, hk, vs, rfl, hv⟩ := Forall2.mem_right h hr
    obtain ⟨_, hy, he⟩ := hks.class_mem hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    refine ⟨_, vs, _, rfl, hv, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, he⟩,
      fun _ => List.ne_nil_of_mem (a := x) (List.mem_filter.mpr ⟨hx, by simp [he]⟩),
      List.length_filter_le _ _⟩

/-! ## Windows (D45) -/

/-- What the reference allows a window function to give at `x`, from its
partition's rows before (`pb`) and after (`pa`) it (D45, amended
2026-11-17): a function that picks from a class (`AggFn.classPick`: `MIN`,
`MAX`, `QUANTILE_DISC`) any value `AggFn.Picks` allows over the frame's
values in the frame's order; every other function its value. -/
def WinFn.Allowed (pb : List Row) (x : Row) (pa : List Row) (f : WinFn) (v : Value) : Prop :=
  match f with
  | .agg m sort fr =>
    if m.fn.classPick then m.fn.Picks (m.inputs (fr.rows sort pb x pa)) v
    else v = m.eval (fr.rows sort pb x pa)
  | _ => v = f.valueIn pb x pa

/-- `windowRows` with each function's value one that `A` allows, from the
rows of its partition before and after it. -/
def windowRowsWith (A : List Row → Row → List Row → WinFn → Value → Prop) (part : List Nat)
    (fns : List WinFn) : List Row → List Row → Relation → Prop
  | _, [], out => out = []
  | before, x :: after, out => ∃ vs rest, out = (x ++ vs) :: rest ∧
      Forall2 (fun f v => A (before.filter (samePart part x)) x (after.filter (samePart part x)) f v)
        fns vs ∧
      windowRowsWith A part fns (before ++ [x]) after rest

/-- `windowRows` with each function's value one the reference allows. -/
abbrev windowRowsA := windowRowsWith WinFn.Allowed

omit [Boxes.Ambient] in
theorem AggFn.sorts_of_classPick {f : AggFn} (h : f.classPick = true) : f.sorts = false := by
  cases f <;> simp_all [AggFn.classPick, AggFn.sorts]

theorem WinFn.allowed_valueIn (pb : List Row) (x : Row) (pa : List Row) (f : WinFn) :
    f.Allowed pb x pa (f.valueIn pb x pa) := by
  cases f <;> simp only [WinFn.Allowed, WinFn.valueIn]
  split
  · next h => rw [Measure.eval_eq (AggFn.sorts_of_classPick h)]; exact AggFn.picks_apply _ _
  · trivial

/-- **`windowRows` is one of the results the reference allows.** -/
theorem windowRows_windowRowsA (part : List Nat) (fns : List WinFn) :
    ∀ before s, windowRowsA part fns before s (windowRows part fns before s)
  | _, [] => rfl
  | before, x :: after => ⟨_, _, rfl, forall₂_map_self fns fun f _ => WinFn.allowed_valueIn _ _ _ f,
      windowRows_windowRowsA part fns (before ++ [x]) after⟩

/-- The class-picking functions' arguments are alone in their classes on
`rows`: then there is no member to choose (D31, D45). -/
def WinFn.ClassArgsLone (fns : List WinFn) (rows : List Row) : Prop :=
  ∀ f ∈ fns, ∀ m sort fr, f = .agg m sort fr → m.fn.classPick = true →
    ∀ r ∈ rows, (m.arg.eval r).Lone

theorem WinFn.Allowed.eq {pb : List Row} {x : Row} {pa : List Row} {f : WinFn} {v : Value}
    (h : f.Allowed pb x pa v)
    (hl : ∀ m sort fr, f = .agg m sort fr → m.fn.classPick = true →
      ∀ r ∈ pb ++ x :: pa, (m.arg.eval r).Lone) :
    v = f.valueIn pb x pa := by
  cases f <;> simp only [WinFn.Allowed, WinFn.valueIn] at h ⊢ <;> try exact h
  rename_i m sort fr
  split at h
  · next hc =>
    rw [Measure.eval_eq (AggFn.sorts_of_classPick hc)]
    refine AggFn.Picks.eq h fun w hw => ?_
    obtain ⟨-, y, hy, rfl⟩ := Measure.mem_inputs hw
    exact hl m sort fr rfl hc y (Frame.mem_rows hy)
  · exact h

theorem WinFn.Allowed.canon {pb : List Row} {x : Row} {pa : List Row} {f : WinFn} {v : Value}
    (h : f.Allowed pb x pa v) : v.canonV = (f.valueIn pb x pa).canonV := by
  cases f <;> simp only [WinFn.Allowed, WinFn.valueIn] at h ⊢ <;> try rw [h]
  split at h
  · next hc => rw [Measure.eval_eq (AggFn.sorts_of_classPick hc)]; exact h.canon
  · rw [h]

/-- Window values the reference allows are `WinFn.value`'s up to their
classes, so the row is in the class of `windowRows`'s. -/
theorem WinFn.allowed_canon_row {part : List Nat} {b a : List Row} {x : Row} :
    ∀ {fns : List WinFn} {vs : List Value},
      Forall2 (fun f v => f.Allowed (b.filter (samePart part x)) x (a.filter (samePart part x)) v)
        fns vs → (x ++ vs).canon = (x ++ fns.map (·.value part b a x)).canon
  | _, _, .nil => rfl
  | f :: fns, v :: vs, .cons h t => by
    have ih := WinFn.allowed_canon_row t
    simp only [Row.canon, List.map_append, List.map_cons, List.append_cancel_left_eq,
      List.cons.injEq] at ih ⊢
    exact ⟨h.canon, ih⟩

/-- **Without doubles to choose among, the reference allows only
`windowRows`.** -/
theorem windowRowsA_eq {part : List Nat} {fns : List WinFn} :
    ∀ {before s : List Row} {o : Relation}, WinFn.ClassArgsLone fns (before ++ s) →
      windowRowsA part fns before s o → o = windowRows part fns before s
  | _, [], _, _, h => h
  | before, x :: after, _, hl, ⟨vs, rest, rfl, hv, hr⟩ => by
    have hrest := windowRowsA_eq (before := before ++ [x]) (by simpa using hl) hr
    rw [hrest, eq_map_of_forall₂ (Forall2.imp_mem (fun f hf v h => ?_) hv)]
    · rfl
    refine h.eq fun m sort fr he hc r hr => hl f hf m sort fr he hc r ?_
    simp only [List.mem_append, List.mem_filter, List.mem_cons] at hr ⊢
    rcases hr with ⟨h, -⟩ | rfl | ⟨h, -⟩ <;> simp [*]

/-- **Every result the reference allows is `windowRows` up to the class of
each window value.** -/
theorem windowRowsA_canon {part : List Nat} {fns : List WinFn} :
    ∀ {before s : List Row} {o : Relation}, windowRowsA part fns before s o →
      Forall2 (fun r w => ∃ x vs ws, r = x ++ vs ∧ w = x ++ ws ∧
        vs.map Value.canonV = ws.map Value.canonV) o (windowRows part fns before s)
  | _, [], _, h => by subst h; exact .nil
  | before, x :: after, _, ⟨vs, rest, rfl, hv, hr⟩ => by
    refine .cons ⟨x, vs, _, rfl, rfl, ?_⟩ (windowRowsA_canon hr)
    clear hr
    induction hv with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, ih, h.canon, WinFn.value]

/-- A function that reads rows up to their classes reads the reference's
results as `windowRows`. -/
theorem windowRowsA_map_canon {part : List Nat} {fns : List WinFn} {before s : List Row}
    {o : Relation} (h : windowRowsA part fns before s o) {β : Type} (g : Row → β)
    (hg : ∀ x y, x.canon = y.canon → g x = g y) : o.map g = (windowRows part fns before s).map g := by
  have hc := windowRowsA_canon h
  generalize windowRows part fns before s = w at hc ⊢
  clear h
  induction hc with
  | nil => rfl
  | cons hr _ ih =>
    obtain ⟨x, vs, ws, rfl, rfl, he⟩ := hr
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    exact hg _ _ (by simp [Row.canon, he])

/-- A row the reference allows is a row of `windowRows` with each window value
in its class. -/
theorem windowRowsA_mem {part : List Nat} {fns : List WinFn} {before s : List Row} {o : Relation}
    (h : windowRowsA part fns before s o) {row : Row} (hr : row ∈ o) :
    ∃ w ∈ windowRows part fns before s, ∃ x vs ws, row = x ++ vs ∧ w = x ++ ws ∧
      vs.map Value.canonV = ws.map Value.canonV :=
  Forall2.mem_right (windowRowsA_canon h).flip hr

theorem windowRowsA_length {part : List Nat} {fns : List WinFn} {before s : List Row}
    {o : Relation} (h : windowRowsA part fns before s o) : o.length = s.length :=
  (windowRowsA_canon h).length_eq.trans windowRows_length

theorem windowRowsA_mem_length {part : List Nat} {fns : List WinFn} {before s : List Row}
    {o : Relation} (h : windowRowsA part fns before s o) {row : Row} (hr : row ∈ o) :
    ∃ w ∈ windowRows part fns before s, row.length = w.length := by
  obtain ⟨w, hw, x, vs, ws, rfl, rfl, he⟩ := windowRowsA_mem h hr
  exact ⟨_, hw, by simpa using congrArg List.length he⟩

/-! ## Plans -/

/-- **The results of every order the reference allows** for `r` on `cat`:
`Rel.Allowed` with each measure as `Measure.OrderAllowed` takes it, and each
window function as `WinFn.Allowed` does. -/
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
  -- The window functions over the input in any order its sort allows, a
  -- class-picking function any member of its class (D45).
  | .window r part sort fns, out => ∃ i, r.OrderAllowed cat i ∧ ∃ s, s.Perm i ∧
      s.Pairwise (sortLe sort · · = true) ∧ ∃ o, out.Perm o ∧ windowRowsA part fns [] s o
  | .semi a b anti on, out => ∃ x y, a.OrderAllowed cat x ∧ b.OrderAllowed cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row != anti)
  -- The input sorted, ties and a clustered key's groups in any order.
  | .orderBy r keys, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm i ∧ SortAllowed keys out
  | .distinct r, out => ∃ i, r.OrderAllowed cat i ∧ ∃ d, IsReps Row.canon i d ∧ out.Perm d
  | .aggregate r gs ms, out => ∃ i, r.OrderAllowed cat i ∧ ∃ o, out.Perm o ∧
      aggOrderAllowed gs ms i o
  | .unnest r c, out => ∃ i, r.OrderAllowed cat i ∧ out.Perm (i.flatMap (unnestRow c))

/-- **`Rel.eval` takes one of the orders** (D24). -/
theorem Rel.eval_orderAllowed (cat : Catalog) : ∀ r : Rel, r.OrderAllowed cat (r.eval cat)
  | .read _ | .values _ _ => .refl _
  | .filter r _ | .project r _ | .emit r _ => ⟨_, eval_orderAllowed cat r, rfl⟩
  | .cross a b | .unionAll a b | .semi a b _ _ =>
    ⟨_, _, eval_orderAllowed cat a, eval_orderAllowed cat b, .refl _⟩
  | .join a b .inner _ | .join a b .left _ =>
    ⟨_, _, eval_orderAllowed cat a, eval_orderAllowed cat b, .refl _⟩
  | .fetch r _ cnt => ⟨_, eval_orderAllowed cat r, by cases cnt <;> rfl⟩
  | .window r part sort fns => ⟨_, eval_orderAllowed cat r, _, List.mergeSort_perm _ _,
      mergeSort_sorted sort _, _, .refl _, windowRows_windowRowsA part fns [] _⟩
  | .orderBy r keys => ⟨_, eval_orderAllowed cat r, List.mergeSort_perm _ _,
      .of_sorted (mergeSort_sorted keys _)⟩
  | .distinct r => ⟨_, eval_orderAllowed cat r, _, canonReps_isReps Row.leRaw_rawOrder _, .refl _⟩
  | .unnest r _ => ⟨_, eval_orderAllowed cat r, .refl _⟩
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

omit [Boxes.Ambient] in
/-- Each row `windowRowsWith` admits extends some row `x` of the sorted
list with values `A` allows from the rows before and after it. -/
theorem mem_windowRowsWith {A : List Row → Row → List Row → WinFn → Value → Prop} {part : List Nat}
    {fns : List WinFn} :
    ∀ {pre l : List Row} {o : Relation} {row : Row}, windowRowsWith A part fns pre l o → row ∈ o →
      ∃ b x a vs, pre ++ l = b ++ x :: a ∧ row = x ++ vs ∧
        Forall2 (fun f v => A (b.filter (samePart part x)) x (a.filter (samePart part x)) f v) fns vs
  | _, [], _, _, h, hr => by subst h; simp at hr
  | pre, x :: l, _, row, ⟨vs, rest, he, hv, hr'⟩, hr => by
    subst he
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨pre, x, l, vs, rfl, rfl, hv⟩
    · obtain ⟨b, y, a, ws, he, rfl, hw⟩ := mem_windowRowsWith hr' hr
      exact ⟨b, y, a, ws, by simpa using he, rfl, hw⟩

/-- `mem_windowRows_sorted` for every result the reference allows. -/
theorem mem_windowRowsA_sorted {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {s o : Relation} {row : Row} (hs : s.Pairwise (sortLe sort · · = true))
    (ho : windowRowsA part fns [] s o) (h : row ∈ o) :
    ∃ b x a vs, s = b ++ x :: a ∧ row = x ++ vs ∧
      Forall2 (fun f v => f.Allowed (b.filter (samePart part x)) x (a.filter (samePart part x)) v)
        fns vs ∧
      (∀ y ∈ b, sortLe sort y x = true) ∧ (∀ y ∈ a, sortLe sort x y = true) ∧
      ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → y ∈ s := by
  obtain ⟨b, x, a, vs, he, rfl, hv⟩ := mem_windowRowsWith ho h
  rw [List.nil_append] at he
  have hs' := hs
  rw [he, List.pairwise_append, List.pairwise_cons] at hs'
  refine ⟨b, x, a, vs, he, rfl, hv, fun y hy => hs'.2.2 y hy x (by simp), fun y hy => hs'.2.1.1 y hy,
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
  | .window r _ _ _, hwf, _, ⟨i, hi, s, hp, hs, o, h, ho⟩, row, hr => by
    obtain ⟨w, hw, hl⟩ := windowRowsA_mem_length ho (h.mem_iff.mp hr)
    obtain ⟨_, x, _, _, rfl, _, _, hin⟩ := mem_windowRows_sorted hs hw
    simp [hl, arity, orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp (hin x (.inl rfl)))]
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
    orderAllowed_arity hcat hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
    orderAllowed_arity hcat hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, _, hd, h⟩, row, hr => by
    obtain ⟨y, hy, he⟩ := hd.class_mem (h.mem_iff.mp hr)
    rw [Row.length_of_canon he]; exact orderAllowed_arity hcat (r := r) hwf hi y hy
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
    obtain ⟨k, vs, _, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
    have hkl : k.length = gs.length := by
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, he⟩
      · rfl
      · rw [Row.length_of_canon he]; simp [groupKey]
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
