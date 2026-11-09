import SubstraitLean.Lipschitz

/-!
# The `M₁` fold (#929)

`Relation.NearL1 t a b` matches the rows of `a` and `b` so that, per double
column, the distances of the matched pairs sum to at most `t` of it: what a
downstream `SUM` over the column sees. This module folds a plan's `M₁`
budget from its sources' (`Rel.tol1`) and proves it (`Rel.plan_nearL1`):

* a filter on exact columns, `ORDER BY` and a semi-join keep the budget
  (fewer pairs sum to less);
* a projection and an emit give each column the budget of the column it
  copies, and an expression of exact columns is exact;
* `UNION ALL` adds its inputs' budgets (`M∞` takes the larger);
* a cross or inner join pairs every left row with every right row: the left
  columns' budget counts once per right row and the right's once per left
  row, at most the other side's row bound (`Rel.rowsK`);
* `DISTINCT` and an aggregate of exact keys and measures are exact;

* a `SUM` or `AVG` of a tolerated column adds its group's distances, one code
  per value and one rounding per group (`floatSumCR_nearL1`,
  `floatAvgCR_nearL1`): over the groups, the column's budget once, plus a
  cost per input row (`Measure.l1`, `aggregateEval_nearL1`). The groups'
  budgets sum within the input's (`PairsWithin.groups`), where `M∞` gives
  each group the whole tolerance and a `SUM` multiplies it by the group's
  rows.

As in `Rel.plan_near`, distances are between canonical codes, and the
engine's sources need no condition. Arithmetic stays exact or refused here
for now; `M∞` has its rows.
-/

namespace Substrait

/-! ## Budgets -/

/-- Each output column's budget from the input column it copies (`none`:
exact). -/
def Tol.pull (src : Nat → Option Nat) (t : Tol) : Tol := fun j => (src j).bind t

/-- `n` times a budget. -/
def Tol.scale (n : Nat) (t : Tol) : Tol := fun c => (t c).map (n * ·)

section
variable {a b c d t t' : Tol}

theorem Tol.Le.add_left_le (h : (a.add b).Le t) : a.Le t := fun c => by
  have x := Tol.le_add_left a b c; have y := h c
  revert x y; cases a c <;> cases (a.add b) c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.Le.add_right_le (h : (a.add b).Le t) : b.Le t := fun c => by
  have x := Tol.le_add_right a b c; have y := h c
  revert x y; cases b c <;> cases (a.add b) c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.le_add_of_le_right (h : b.Le t) : b.Le (a.add t) := fun c => by
  have y := h c; revert y; simp only [Tol.add]
  cases a c <;> cases b c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.add_assoc_le : (a.add (b.add c)).Le ((a.add b).add c) := fun k => by
  simp only [Tol.add]; cases a k <;> cases b k <;> cases c k <;> simp [OLe] <;> omega

theorem Tol.pull_mono (src : Nat → Option Nat) (h : a.Le b) : (Tol.pull src a).Le (Tol.pull src b) :=
  fun j => by simp only [Tol.pull]; cases src j <;> simp [OLe]; exact h _

theorem Tol.pull_add (src : Nat → Option Nat) :
    ((Tol.pull src a).add (Tol.pull src b)).Le (Tol.pull src (a.add b)) := fun j => by
  unfold Tol.add Tol.pull
  cases src j with
  | none => simp [OLe]
  | some i => simp only [Option.bind_some]; cases a i <;> cases b i <;> simp [OLe]

theorem Tol.scale_mono {m n : Nat} (hmn : m ≤ n) (h : a.Le b) : (Tol.scale m a).Le (Tol.scale n b) :=
  fun k => by
    have x := h k; revert x; simp only [Tol.scale]
    cases a k <;> cases b k <;> simp [OLe]
    intro hx; exact Nat.mul_le_mul hmn hx

theorem Tol.scale_add (n : Nat) : ((Tol.scale n a).add (Tol.scale n b)).Le (Tol.scale n (a.add b)) :=
  fun k => by
    simp only [Tol.scale, Tol.add]; cases a k <;> cases b k <;> simp [OLe, Nat.mul_add]

theorem Tol.scale_succ (n : Nat) : (a.add (Tol.scale n a)).Le (Tol.scale (n + 1) a) := fun k => by
  simp only [Tol.scale, Tol.add]; cases a k <;> simp [OLe, Nat.succ_mul]; omega

theorem Tol.cat_add (n : Nat) :
    ((Tol.cat n a b).add (Tol.cat n c d)).Le (Tol.cat n (a.add c) (b.add d)) := fun k => by
  by_cases hk : k < n <;> simp only [Tol.cat, Tol.add, hk, ite_true, ite_false] <;> exact OLe.refl _

theorem Tol.cat_mono (n : Nat) (h₁ : a.Le c) (h₂ : b.Le d) : (Tol.cat n a b).Le (Tol.cat n c d) :=
  fun k => by simp only [Tol.cat]; split <;> first | exact h₁ _ | exact h₂ _

end

/-! ## Matchings through the operators -/

theorem PairsWithin.length_eq : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → a.length = p.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, _, _, h, _⟩ => by simp [PairsWithin.length_eq h]
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- Every pair is within the whole budget. -/
theorem PairsWithin.forall2 {T0 : Tol} : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t →
    t.Le T0 → Forall2 T0.Rows a p
  | [], [], _, _, _ => .nil
  | _ :: _, _ :: _, _, ⟨_, _, r, h, le⟩, ht =>
    .cons ⟨r.1, fun j => Tol.cell_transfer ((le.add_left_le.trans ht) j) (r.2 j)⟩
      (PairsWithin.forall2 h (le.add_right_le.trans ht))
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- **Fewer pairs** sum to less: a filter that reads the same on both rows of
a pair keeps the budget. `Q` holds of the right side's rows. -/
theorem PairsWithin.filter {T0 : Tol} {Q : Row → Prop} {P P' : Row → Bool}
    (hP : ∀ (tr : Tol) (x y : Row), tr.Le T0 → tr.Rows x y → Q y → P x = P' y) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → t.Le T0 → (∀ y ∈ p, Q y) →
      PairsWithin (a.filter P) (p.filter P') t
  | [], [], _, _, _, _ => trivial
  | x :: xs, y :: ys, t, ⟨tr, rest, r, h, le⟩, ht, hq => by
    have ih := PairsWithin.filter hP h (le.add_right_le.trans ht)
      fun z hz => hq z (List.mem_cons_of_mem _ hz)
    rw [List.filter_cons, List.filter_cons,
      hP tr x y (le.add_left_le.trans ht) r (hq y (List.mem_cons_self ..))]
    split
    · exact ⟨tr, rest, r, ih, le⟩
    · exact ih.mono le.add_right_le
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => h.elim

/-- **A row map** whose output columns copy input columns (`Tol.pull src`).
`Q` holds of the right side's rows. -/
theorem PairsWithin.map {T0 : Tol} {Q : Row → Prop} {src : Nat → Option Nat} {f g : Row → Row}
    (hf : ∀ (tr : Tol) (x y : Row), tr.Le T0 → tr.Rows x y → Q y →
      (Tol.pull src tr).Rows (f x) (g y)) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → t.Le T0 → (∀ y ∈ p, Q y) →
      PairsWithin (a.map f) (p.map g) (Tol.pull src t)
  | [], [], _, _, _, _ => trivial
  | x :: _, y :: _, _, ⟨tr, rest, r, h, le⟩, ht, hq =>
    ⟨Tol.pull src tr, Tol.pull src rest,
      hf tr x y (le.add_left_le.trans ht) r (hq y (List.mem_cons_self ..)),
      PairsWithin.map hf h (le.add_right_le.trans ht) fun z hz => hq z (List.mem_cons_of_mem _ hz),
      (Tol.pull_add src).trans (Tol.pull_mono src le)⟩
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => h.elim

/-- **`UNION ALL`**: budgets add. -/
theorem PairsWithin.append : ∀ {a p b q : List Row} {ta tb : Tol}, PairsWithin a p ta →
    PairsWithin b q tb → PairsWithin (a ++ b) (p ++ q) (ta.add tb)
  | [], [], _, _, _, _, _, h => h.mono (fun c => Tol.le_add_right _ _ c)
  | _ :: _, _ :: _, _, _, _, _, ⟨tr, rest, r, h, le⟩, h' =>
    ⟨tr, rest.add _, r, PairsWithin.append h h',
      Tol.add_assoc_le.trans (Tol.add_mono le (Tol.Le.refl _))⟩
  | [], _ :: _, _, _, _, _, h, _ | _ :: _, [], _, _, _, _, h, _ => h.elim

/-- One left pair against the right side's pairs: the left pair's budget
counts once per right row. -/
theorem PairsWithin.prefix {n : Nat} {x y : Row} {tr : Tol} (r : tr.Rows x y) (hy : y.length = n) :
    ∀ {b q : List Row} {tb : Tol}, PairsWithin b q tb →
      PairsWithin (b.map (x ++ ·)) (q.map (y ++ ·)) (Tol.cat n (Tol.scale b.length tr) tb)
  | [], [], _, _ => trivial
  | _ :: bs, _ :: _, _, ⟨tu, rest, ru, h, le⟩ =>
    ⟨Tol.cat n tr tu, Tol.cat n (Tol.scale bs.length tr) rest, Tol.rows_append r ru hy,
      PairsWithin.prefix r hy h,
      (Tol.cat_add n).trans (Tol.cat_mono n (by simpa using Tol.scale_succ bs.length) le)⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- **A cross**: the left columns' budget once per right row, the right's
once per left row. -/
theorem PairsWithin.cross {n : Nat} {b q : List Row} {tb : Tol} (hb : PairsWithin b q tb) :
    ∀ {a p : List Row} {ta : Tol}, PairsWithin a p ta → (∀ y ∈ p, y.length = n) →
      PairsWithin (crossRows a b) (crossRows p q)
        (Tol.cat n (Tol.scale b.length ta) (Tol.scale a.length tb))
  | [], [], _, _, _ => trivial
  | _ :: xs, y :: _, _, ⟨tr, rest, r, h, le⟩, hp => by
    have ih := PairsWithin.cross hb h fun z hz => hp z (List.mem_cons_of_mem _ hz)
    have hx := PairsWithin.prefix r (hp y (List.mem_cons_self ..)) hb
    simp only [crossRows, List.flatMap_cons] at ih ⊢
    refine (hx.append ih).mono ((Tol.cat_add n).trans (Tol.cat_mono n ?_ ?_))
    · exact (Tol.scale_add b.length).trans (Tol.scale_mono (Nat.le_refl _) le)
    · simpa [Nat.add_comm] using Tol.scale_succ (a := tb) xs.length
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-! ## The fold -/

/-- A projection's columns: the input's, then each expression's, a field
copying its column and anything else exact. -/
def projSrc (n : Nat) (es : List Expr) (j : Nat) : Option Nat :=
  if j < n then some j else
  match es[j - n]? with
  | some (.field i) => some i
  | _ => none

theorem Tol.exactOn_of_le {tr t : Tol} (h : tr.Le t) {cols : List Nat} (he : t.exactOn cols = true) :
    tr.exactOn cols = true := by
  simp only [Tol.exactOn, List.all_eq_true, Option.isNone_iff_eq_none] at he ⊢
  intro i hi
  have := h i; rw [he i hi] at this
  revert this; cases tr i <;> simp [OLe]

theorem Tol.rows_project {tr t : Tol} {n : Nat} {es : List Expr}
    (hes : es.all (fun e => (e.tol? t).isSome) = true) (hle : tr.Le t) {x y : Row}
    (r : tr.Rows x y) (hy : y.length = n) :
    (Tol.pull (projSrc n es) tr).Rows (x ++ es.map (·.eval x)) (y ++ es.map (·.eval y)) := by
  refine ⟨by simp [r.1], fun j => ?_⟩
  rw [getD_append_split, getD_append_split, r.1, hy]
  by_cases hj : j < n
  · simp only [hj, ite_true]
    exact Tol.cell_transfer (by simp [Tol.pull, projSrc, hj, OLe.refl]) (r.2 j)
  · simp only [hj, ite_false, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases he : es[j - n]? with
    | none => exact Tol.cell_null _ _
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      have hs : (e.tol? t).isSome = true := List.all_eq_true.1 hes e (List.mem_of_getElem? he)
      by_cases hf : ∃ i, e = .field i
      · obtain ⟨i, rfl⟩ := hf
        have hc : Tol.pull (projSrc n es) tr j = tr i := by simp [Tol.pull, projSrc, hj, he]
        exact Tol.cell_transfer (by rw [hc]; exact OLe.refl _) (r.2 i)
      · have hx : t.exactOn e.cols = true := by
          unfold Expr.tol? at hs
          split at hs
          · exact absurd ⟨_, rfl⟩ hf
          · split at hs <;> simp_all
        rw [Expr.eval_rows (Tol.exactOn_of_le hle hx) r]
        exact Tol.cell_refl _ _ _

/-! ## `SUM` and `AVG` in `M₁`

A group's `SUM` moves by its pairs' distances, one code per value and the
rounding of both sides (`floatSumCR_nearL1`); an `AVG` by the distances, one
code and the rounding (`floatAvgCR_nearL1`). A group has a row, so the count
and the rounding are at most a cost `c` per row of the group, and over the
groups the budget is the column's, plus `c` per input row. -/

section
open FloatCode

/-- A budget's bound in one column, `0` where it is exact. -/
def Tol.val (t : Tol) (c : Nat) : Nat := (t c).getD 0

theorem Tol.val_add (a b : Tol) (c : Nat) : (a.add b).val c = a.val c + b.val c := by
  unfold Tol.val Tol.add; cases a c <;> cases b c <;> simp

theorem Tol.Le.val {a b : Tol} (h : a.Le b) (c : Nat) : a.val c ≤ b.val c := by
  have := h c; unfold Tol.val; revert this; cases a c <;> cases b c <;> simp [OLe]

theorem OLe.val {o : Option Nat} : OLe o (some (o.getD 0)) := by cases o <;> simp [OLe]

theorem OLe.of_getD {o : Option Nat} {e : Nat} (h : o.getD 0 ≤ e) : OLe o (some e) := by
  cases o <;> simp_all [OLe]

/-- **A matching's values of an argument column**, each pair within its
bound there. -/
theorem PairsWithin.arg {e : Expr} {i : Nat} (he : e = .field i) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t →
      ListL1 (fun d v w => (Tol.all d).Cell 0 v w) (a.map fun row => e.eval row)
        (p.map fun row => e.eval row) (t.val i)
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, _, ⟨tr, rest, r, h, le⟩ =>
    ⟨tr.val i, rest.val i,
      Expr.tol?_sound (t := tr) (by simp [he, Expr.tol?]) r (t' := Tol.all _) (j := 0) OLe.val,
      PairsWithin.arg he h, by rw [← Tol.val_add]; exact le.val i⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- A measure's inputs on two matched groups, in `M₁`. -/
theorem Measure.inputs_cellsL1 {t : Tol} {m : Measure} {i : Nat} (harg : m.arg = .field i)
    (hd : m.distinct = false) (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    {g g' : Relation} {tg : Tol} (w : PairsWithin g g' tg) (hle : tg.Le t) :
    ListL1 (fun d v w => (Tol.all d).Cell 0 v w) (m.inputs g) (m.inputs g') (tg.val i) := by
  have hk : PairsWithin (m.kept g) (m.kept g') tg := by
    unfold Measure.kept
    cases hc : m.filter with
    | none => exact w
    | some c =>
      simp only [hc, Option.all_some] at hf
      exact w.filter (Q := fun _ => True) (fun tr x y htr r _ => by
        rw [Expr.eval_rows (Tol.exactOn_of_le htr hf) r]) hle (fun _ _ => trivial)
  have hn := (hk.arg harg).filter (p := (· != .null)) (p' := (· != .null))
    fun _ _ _ h => Tol.cell_null_iff h
  unfold Measure.inputs
  simp only [hd, Bool.false_eq_true, ite_false]
  exact hn

/-- A `SUM`'s or `AVG`'s inputs on two matched groups in `M₁`: paired within
the group's budget, and the facts of `Measure.sum_facts`. -/
theorem Measure.sum_factsL1 {t : Tol} {m : Measure} {env : List AVal}
    {i e N : Nat} {lo hi : Int} (harg : m.arg = .field i) (hti : t i = some e)
    (hcr : colRange env i = some (lo, hi)) (hd : m.distinct = false)
    (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (hlo : negInf < lo - e) (hhi : hi + e < posInf) {g g' : Relation} {tg : Tol}
    (w : PairsWithin g g' tg) (hle : tg.Le t)
    (henv : ∀ row ∈ g', EnvMem env row) (hN : g'.length ≤ N) :
    ListL1 CodeNear (m.inputs g) (m.inputs g') (tg.val i) ∧ FinCodes (m.inputs g) ∧
      FinCodes (m.inputs g') ∧
      (exactSum (m.inputs g)).natAbs ≤ (m.inputs g).length * (magOf lo hi + e) ∧
      (exactSum (m.inputs g')).natAbs ≤ (m.inputs g').length * (magOf lo hi + e) ∧
      (m.inputs g).length ≤ N ∧ (m.inputs g').length ≤ N := by
  obtain ⟨-, hv, hw, hS, hS', hl, hl'⟩ :=
    Measure.sum_facts harg hti hcr hd hf hlo hhi (w.forall2 hle) henv hN
  refine ⟨?_, hv, hw, hS, hS', hl, hl'⟩
  have hD : tg.val i ≤ e := by have := hle.val i; simpa [Tol.val, hti] using this
  have hQ : ∀ w ∈ m.inputs g', ∀ c, w = .float c → lo ≤ canon c ∧ canon c ≤ hi := by
    intro w hw c hc
    obtain ⟨-, row, hr, rfl⟩ := Measure.mem_inputs hw
    rw [harg] at hc
    have hm := henv row hr i
    simp only [Expr.eval] at hc
    rw [hc] at hm
    obtain ⟨b, hb, hbm, -⟩ := hm
    unfold colRange at hcr
    split at hcr
    · rename_i lo' hi' hint
      simp only [Option.some.injEq, Prod.mk.injEq] at hcr
      obtain ⟨rfl, rfl⟩ := hcr
      rw [hint] at hb; cases hb
      exact ⟨hbm.1 _ rfl, hbm.2 _ rfl⟩
    · cases hcr
  exact (Measure.inputs_cellsL1 harg hd hf w hle).imp
    (fun d v w hd' hv' hw' h => (pair_near (by omega) (by omega) h (hQ w hw')).1)
    (Nat.le_trans (Nat.le_refl _) hD) (fun _ h => h) (fun _ h => h)

theorem CodeNear.mono {e e' : Nat} (h : e ≤ e') {v w : Value} (h' : CodeNear e v w) :
    CodeNear e' v w := by
  cases v <;> cases w <;> first | exact Nat.le_trans h' h | exact h'

end

section
open FloatCode
set_option exponentiation.threshold 2100

theorem Measure.fsum_nearL1 {m : Measure} {D : Nat} (hfn : m.fn = .fsum) {g g' : Relation}
    (hn : ListL1 CodeNear (m.inputs g) (m.inputs g') D) (hv : FinCodes (m.inputs g))
    (hw : FinCodes (m.inputs g')) (rv : IsFin (ofExact (exactSum (m.inputs g))))
    (rw' : IsFin (ofExact (exactSum (m.inputs g')))) :
    CodeNear (D + (m.inputs g).length + ulpDiv (exactSum (m.inputs g)) 1 +
      ulpDiv (exactSum (m.inputs g')) 1 + 4) (m.eval g) (m.eval g') := by
  have hs : m.fn.sorts = false := by rw [hfn]; rfl
  rw [Measure.eval_eq hs, Measure.eval_eq hs, hfn]
  generalize m.inputs g = I at *
  generalize m.inputs g' = I' at *
  cases I with
  | nil =>
    cases I' with
    | nil => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
    | cons _ _ => exact hn.elim
  | cons v vs =>
    cases I' with
    | nil => exact hn.elim
    | cons w ws =>
      have := floatSumCR_nearL1 hn hv hw rv rw'
      simp only [AggFn.apply, CodeNear, canon_floatSumCR]; exact this

theorem Measure.avg_nearL1 {m : Measure} {D : Nat} (hfn : m.fn = .avg) {g g' : Relation}
    (hn : ListL1 CodeNear (m.inputs g) (m.inputs g') D) (hv : FinCodes (m.inputs g))
    (hw : FinCodes (m.inputs g'))
    (rv : IsFin (ofExactDiv (exactSum (m.inputs g)) (m.inputs g).length))
    (rw' : IsFin (ofExactDiv (exactSum (m.inputs g')) (m.inputs g').length)) :
    CodeNear ((D + 1) + ulpDiv (exactSum (m.inputs g)) (m.inputs g).length +
      ulpDiv (exactSum (m.inputs g')) (m.inputs g').length + 4) (m.eval g) (m.eval g') := by
  have hs : m.fn.sorts = false := by rw [hfn]; rfl
  rw [Measure.eval_eq hs, Measure.eval_eq hs, hfn]
  generalize m.inputs g = I at *
  generalize m.inputs g' = I' at *
  cases I with
  | nil =>
    cases I' with
    | nil => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
    | cons _ _ => exact hn.elim
  | cons v vs =>
    cases I' with
    | nil => exact hn.elim
    | cons w ws =>
      have := floatAvgCR_nearL1 hn hv hw rv rw'
      simp only [AggFn.apply, CodeNear, canon_floatAvgCR]; exact this

/-- A `SUM`'s cost per row in `M₁`, beyond its column's budget: one code per
value and the rounding of both sides. -/
def sumCost1 (N e M : Nat) : Nat := 1 + (2 * ulpDiv ((N * (M + e) : Nat) : Int) 1 + 4)

/-- An `AVG`'s cost per row in `M₁`: one code and the rounding of both sides. -/
def avgCost1 (e M : Nat) : Nat := 1 + (2 * ulpDiv ((M + e : Nat) : Int) 1 + 4)

/-- **A measure in the `M₁` fold**, its input within the budget `t`: `some
none` for a measure of exact columns, `some (some (i, c))` for a `SUM` or
`AVG` of column `i` that costs `c` per input row beyond `i`'s budget, `none`
otherwise. The conditions are `Measure.tolOut`'s. -/
def Measure.l1 (t : Tol) (mask : Nat → Bool) (env : List AVal) (N : Option Nat)
    (m : Measure) : Option (Option (Nat × Nat)) :=
  if m.tolOk t then some none else
  match m.arg, N with
  | .field i, some N =>
    match t i, colRange env i with
    | some e, some (lo, hi) =>
      if !m.distinct && (m.filter.all fun c => t.exactOn c.cols) && mask i &&
          decide (negInf < lo - e) && decide (hi + e < posInf) &&
          decide (N * (magOf lo hi + e) ≤ 2 ^ 2097) then
        match m.fn with
        | .fsum => some (some (i, sumCost1 N e (magOf lo hi)))
        | .avg => some (some (i, avgCost1 e (magOf lo hi)))
        | _ => none
      else none
    | _, _ => none
  | _, _ => none

theorem Measure.l1_none {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} (h : m.l1 t mask env N = some none) : m.tolOk t = true := by
  unfold Measure.l1 at h
  by_cases hok : m.tolOk t = true
  · exact hok
  simp only [hok, Bool.false_eq_true, ite_false] at h
  repeat' (split at h)
  all_goals simp_all

theorem Measure.l1_orderFree {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {o : Option (Nat × Nat)} (h : m.l1 t mask env N = some o) : m.orderFree = true := by
  by_cases hok : m.tolOk t = true
  · simp only [Measure.tolOk, Bool.and_eq_true] at hok; exact hok.1.1.1
  unfold Measure.orderFree
  cases hfn : m.fn <;> first
    | (simp [AggFn.orderFree, AggFn.decomposable]; done)
    | (exfalso
       unfold Measure.l1 at h
       simp only [hok, Bool.false_eq_true, ite_false] at h
       repeat' (split at h)
       all_goals simp_all)

theorem Measure.l1_rows {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {i c : Nat} (h : m.l1 t mask env N = some (some (i, c))) :
    ∃ n, N = some n := by
  unfold Measure.l1 at h
  by_cases hok : m.tolOk t = true
  · simp [hok] at h
  simp only [hok, Bool.false_eq_true, ite_false] at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- **A `SUM` or `AVG` of a matched group in `M₁`**: within the group's
budget in its column plus its cost per row. -/
theorem Measure.l1_cell {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {i c : Nat} (h : m.l1 t mask env N = some (some (i, c))) {g g' : Relation}
    {tg : Tol} (w : PairsWithin g g' tg) (hle : tg.Le t) (henv : ∀ row ∈ g', EnvMem env row)
    (hN : ∀ n, N = some n → g'.length ≤ n) :
    CodeNear (tg.val i + g'.length * c) (m.eval g) (m.eval g') := by
  unfold Measure.l1 at h
  by_cases hok : m.tolOk t = true
  · simp [hok] at h
  simp only [hok, Bool.false_eq_true, ite_false] at h
  cases harg : m.arg with
  | field j =>
    rw [harg] at h
    cases N with
    | none => simp at h
    | some n =>
      simp only at h
      cases htj : t j with
      | none => simp [htj] at h
      | some e =>
        cases hcr : colRange env j with
        | none => simp [htj, hcr] at h
        | some r =>
          obtain ⟨lo, hi⟩ := r
          simp only [htj, hcr] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
            obtain ⟨⟨⟨⟨⟨hd, hf⟩, -⟩, hlo⟩, hhi⟩, hbig⟩ := hc
            obtain ⟨hp, hv, hw, hS, hS', hl, hl'⟩ :=
              Measure.sum_factsL1 harg htj hcr hd hf hlo hhi w hle henv (hN n rfl)
            have hlen := hp.length_eq
            have hs : m.fn.sorts = false := by
              cases hfn : m.fn <;> simp only [hfn, reduceCtorEq] at h <;> rfl
            -- No values: both sides NULL.
            rcases Nat.eq_zero_or_pos (m.inputs g).length with h0 | hpos
            · have e1 : m.inputs g = [] := List.eq_nil_of_length_eq_zero h0
              have e2 : m.inputs g' = [] := List.eq_nil_of_length_eq_zero (hlen ▸ h0)
              rw [Measure.eval_eq hs, Measure.eval_eq hs, e1, e2]
              cases hfn : m.fn <;> simp only [hfn, reduceCtorEq] at h <;>
                exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
            have hg' : (m.inputs g).length ≤ g'.length :=
              hlen ▸ Measure.inputs_length_le m g'
            generalize hM : magOf lo hi = M at hS hS' hbig h
            cases hfn : m.fn <;> simp only [hfn, reduceCtorEq] at h
            · -- SUM
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have big : ((n * (M + e) : Nat) : Int).natAbs = n * (M + e) := Int.natAbs_natCast _
              have hS1 : (exactSum (m.inputs g)).natAbs ≤ n * (M + e) :=
                Nat.le_trans hS (Nat.mul_le_mul_right _ hl)
              have hS2 : (exactSum (m.inputs g')).natAbs ≤ n * (M + e) :=
                Nat.le_trans hS' (Nat.mul_le_mul_right _ hl')
              have rv := ofExactDiv_fin (v := exactSum (m.inputs g)) (n := 1) (by omega) (by omega)
              have rw' := ofExactDiv_fin (v := exactSum (m.inputs g')) (n := 1) (by omega) (by omega)
              refine CodeNear.mono ?_ (Measure.fsum_nearL1 hfn hp hv hw rv rw')
              have u1 := ulpDiv_mono (v := exactSum (m.inputs g))
                (w := ((n * (M + e) : Nat) : Int)) 1 (by rw [big]; exact hS1)
              have u2 := ulpDiv_mono (v := exactSum (m.inputs g'))
                (w := ((n * (M + e) : Nat) : Int)) 1 (by rw [big]; exact hS2)
              unfold sumCost1
              generalize ulpDiv ((n * (M + e) : Nat) : Int) 1 = U at *
              have : 2 * U + 4 ≤ g'.length * (2 * U + 4) := Nat.le_mul_of_pos_left _ (by omega)
              rw [Nat.mul_add, Nat.mul_one]; omega
            · -- AVG
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hfin : ∀ {I : List Value}, (exactSum I).natAbs ≤ I.length * (M + e) →
                  I.length ≤ n → IsFin (ofExactDiv (exactSum I) I.length) := by
                intro I hI hIn
                rcases Nat.eq_zero_or_pos I.length with h0 | hpos
                · rw [h0] at hI ⊢
                  have : exactSum I = 0 := by omega
                  rw [this, ofExactDiv_zero]
                  exact ⟨by have := negInf_eq; omega, by have := posInf_eq; omega⟩
                · refine ofExactDiv_fin hpos (Nat.le_trans hI (Nat.mul_le_mul_left _ ?_))
                  have : 1 * (M + e) ≤ n * (M + e) := Nat.mul_le_mul_right _ (by omega)
                  omega
              refine CodeNear.mono ?_ (Measure.avg_nearL1 hfn hp hv hw (hfin hS hl) (hfin hS' hl'))
              have u1 := ulpDiv_le_of_mean hS
              have u2 := ulpDiv_le_of_mean hS'
              simp only [Int.natCast_add] at u1 u2
              unfold avgCost1
              push_cast
              generalize ulpDiv ((M : Int) + (e : Int)) 1 = U at *
              have : 2 * U + 4 ≤ g'.length * (2 * U + 4) := Nat.le_mul_of_pos_left _ (by omega)
              rw [Nat.mul_add, Nat.mul_one]; omega
          · cases h
  | _ => rw [harg] at h; simp at h

/-- The `M₁` budget of a group's measure row: each `SUM` or `AVG` of column
`i` costing `c` per row gets the group's budget in `i` plus `n · c`. -/
def Tol.ofL1 (ls : List (Option (Option (Nat × Nat)))) (tg : Tol) (n : Nat) : Tol := fun k =>
  match ls.getD k none with
  | some (some (i, c)) => some (tg.val i + n * c)
  | _ => none

/-- **A group's measures in `M₁`.** -/
theorem measures_rowsL1 {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {ms : List Measure} (hls : (ms.map (·.l1 t mask env N)).all Option.isSome = true)
    {g g' : Relation} {tg : Tol} (w : PairsWithin g g' tg) (hle : tg.Le t)
    (henv : ∀ row ∈ g', EnvMem env row) (hN : ∀ n, N = some n → g'.length ≤ n) :
    (Tol.ofL1 (ms.map (·.l1 t mask env N)) tg g'.length).Rows (ms.map (·.eval g))
      (ms.map (·.eval g')) := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hj : ms[j]? with
  | none => exact Tol.cell_null _ _
  | some m =>
    simp only [Option.map_some, Option.getD_some]
    have hm : m ∈ ms := List.mem_of_getElem? hj
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1
      (List.all_eq_true.1 hls _ (List.mem_map_of_mem (f := (·.l1 t mask env N)) hm))
    have hk : Tol.ofL1 (ms.map (·.l1 t mask env N)) tg g'.length j =
        match o with | some (i, c) => some (tg.val i + g'.length * c) | none => none := by
      simp only [Tol.ofL1, List.getD_eq_getElem?_getD, List.getElem?_map, hj, Option.map_some,
        Option.getD_some, ho]
      cases o <;> rfl
    cases o with
    | none =>
      rw [Measure.eval_rows (Measure.l1_none ho) (w.forall2 hle)]; exact Tol.cell_refl _ _ _
    | some ic =>
      obtain ⟨i, c⟩ := ic
      have hro : m.refOut = true := by
        unfold Measure.l1 at ho
        by_cases hok : m.tolOk t = true
        · simp [hok] at ho
        simp only [hok, Bool.false_eq_true, ite_false] at ho
        repeat' (split at ho)
        all_goals simp_all [Measure.refOut]
      exact Tol.cell_of_codeNear hk (Nat.le_refl _) (Measure.eval_refOut hro g)
        (Measure.eval_refOut hro g') (Measure.l1_cell ho w hle henv hN)

end

/-! ## Groups in `M₁` -/

/-- A sum over a list without repeats, one entry raised by `a`. -/
theorem sum_raise {κ : Type} [DecidableEq κ] {k₀ : κ} (f : κ → Nat) (a : Nat) :
    ∀ {ks : List κ}, ks.Nodup → k₀ ∈ ks →
      (ks.map fun k => if k₀ = k then a + f k else f k).sum = a + (ks.map f).sum
  | [], _, hk => by cases hk
  | k :: ks, hn, hk => by
    simp only [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hn
    by_cases h : k₀ = k
    · subst h
      have : (ks.map fun k => if k₀ = k then a + f k else f k) = ks.map f :=
        List.map_congr_left fun k hk' => by
          have hne : ¬k₀ = k := fun e => hn.1 (by subst e; exact hk')
          simp only [hne, ↓reduceIte]
      simp only [ite_true, this]; omega
    · have hk' : k₀ ∈ ks := by simpa [h] using hk
      simp only [h, ↓reduceIte]; rw [sum_raise f a hn.2 hk']; omega

theorem sum_map_eq_zero {κ : Type} {f : κ → Nat} :
    ∀ {ks : List κ}, (∀ k ∈ ks, f k = 0) → (ks.map f).sum = 0
  | [], _ => rfl
  | k :: ks, h => by
    simp only [List.map_cons, List.sum_cons, h k (List.mem_cons_self ..),
      sum_map_eq_zero fun k' hk' => h k' (List.mem_cons_of_mem _ hk')]

theorem sum_map_add' {κ : Type} (f g : κ → Nat) :
    ∀ ks : List κ, (ks.map fun k => f k + g k).sum = (ks.map f).sum + (ks.map g).sum
  | [] => rfl
  | k :: ks => by simp only [List.map_cons, List.sum_cons, sum_map_add' f g ks]; omega

theorem sum_map_mul_const {κ : Type} (f : κ → Nat) (c : Nat) :
    ∀ ks : List κ, (ks.map fun k => f k * c).sum = (ks.map f).sum * c
  | [] => by simp
  | k :: ks => by simp only [List.map_cons, List.sum_cons, sum_map_mul_const f c ks, Nat.add_mul]

/-- **A matching split by an exact key**: each key's pairs form a matching
of their own, and the keys' budgets sum within the whole's, column by
column. -/
theorem PairsWithin.groups {T0 : Tol} {key : Row → Row}
    (hkey : ∀ (tr : Tol) (x y : Row), tr.Le T0 → tr.Rows x y → key x = key y) {ks : List Row}
    (hn : ks.Nodup) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → t.Le T0 → (∀ y ∈ p, key y ∈ ks) →
      ∃ ts : Row → Tol,
        (∀ k, PairsWithin (a.filter (key · == k)) (p.filter (key · == k)) (ts k)) ∧
        (∀ k, (ts k).Le t) ∧ ∀ c, (ks.map fun k => (ts k).val c).sum ≤ t.val c
  | [], [], _, _, _, _ =>
    ⟨fun _ => Tol.exact, fun _ => trivial, fun _ _ => trivial, fun c => by
      rw [sum_map_eq_zero (f := fun k => ((fun _ => Tol.exact) k).val c) fun _ _ => rfl]
      exact Nat.zero_le _⟩
  | x :: xs, y :: ys, t, ⟨tr, rest, r, h, le⟩, ht, hp => by
    have htr : tr.Le T0 := le.add_left_le.trans ht
    obtain ⟨ts, hw, hl, hs⟩ := PairsWithin.groups hkey hn h (le.add_right_le.trans ht)
      fun z hz => hp z (List.mem_cons_of_mem _ hz)
    have hxy := hkey tr x y htr r
    refine ⟨fun k => if key y = k then tr.add (ts k) else ts k, fun k => ?_, fun k => ?_, fun c => ?_⟩
    · by_cases hk : key y = k
      · simp only [List.filter_cons, hxy, hk, beq_self_eq_true, ite_true]
        exact ⟨tr, ts k, r, hw k, Tol.Le.refl _⟩
      · have hb : (key y == k) = false := by simpa using hk
        simp only [List.filter_cons, hxy, hb, hk, ite_false, Bool.false_eq_true]
        exact hw k
    · by_cases hk : key y = k
      · simp only [hk, ite_true]; exact (Tol.add_mono (Tol.Le.refl _) (hl k)).trans le
      · simp only [hk, ite_false]; exact (hl k).trans le.add_right_le
    · have hm : key y ∈ ks := hp y (List.mem_cons_self ..)
      have e : (ks.map fun k => (if key y = k then tr.add (ts k) else ts k).val c) =
          ks.map fun k => if key y = k then tr.val c + (ts k).val c else (ts k).val c :=
        List.map_congr_left fun k _ => by split <;> simp [Tol.val_add]
      rw [e, sum_raise (fun k => (ts k).val c) (tr.val c) hn hm]
      have := le.val c; rw [Tol.val_add] at this; have := hs c; omega
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => h.elim

/-- The groups' rows add up to the input's. -/
theorem sum_filter_length {key : Row → Row} {ks : List Row} (hn : ks.Nodup) :
    ∀ {p : List Row}, (∀ y ∈ p, key y ∈ ks) →
      (ks.map fun k => (p.filter (key · == k)).length).sum = p.length
  | [], _ => sum_map_eq_zero fun _ _ => rfl
  | y :: ys, hp => by
    have ih := sum_filter_length hn (p := ys) fun z hz => hp z (List.mem_cons_of_mem _ hz)
    have e : (ks.map fun k => ((y :: ys).filter (key · == k)).length) =
        ks.map fun k => if key y = k then 1 + (ys.filter (key · == k)).length
          else (ys.filter (key · == k)).length :=
      List.map_congr_left fun k _ => by
        by_cases hk : key y = k
        · simp [hk]; omega
        · have hb : (key y == k) = false := by simpa using hk
          simp [hb, hk]
    rw [e, sum_raise _ 1 hn (hp y (List.mem_cons_self ..)), ih]
    simp; omega

/-- **Rows paired one by one** form a matching within a budget that bounds
their sum in each column. -/
theorem PairsWithin.of_map {κ : Type} {f g : κ → Row} {O : κ → Tol} {F : Tol} :
    ∀ {ks : List κ}, (∀ k ∈ ks, (O k).Rows (f k) (g k)) →
      (∀ c, (∀ k ∈ ks, O k c = none) ∨
        ∃ e, F c = some e ∧ (ks.map fun k => (O k).val c).sum ≤ e) →
      PairsWithin (ks.map f) (ks.map g) F
  | [], _, _ => trivial
  | k :: ks, h, hF => by
    let R : Tol := fun c =>
      if ks.all (fun k => (O k c).isNone) then none else some ((ks.map fun k => (O k).val c).sum)
    have hRv : ∀ c, R.val c = (ks.map fun k => (O k).val c).sum := fun c => by
      simp only [R, Tol.val]
      split
      · rename_i ha
        refine (sum_map_eq_zero fun k' hk' => ?_).symm
        simp [Option.isNone_iff_eq_none.1 (List.all_eq_true.1 ha k' hk')]
      · rfl
    refine ⟨O k, R, h k (List.mem_cons_self ..),
      PairsWithin.of_map (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) (fun c => ?_),
      fun c => ?_⟩
    · by_cases ha : ks.all (fun k => (O k c).isNone) = true
      · left; intro k' hk'; simpa using List.all_eq_true.1 ha k' hk'
      · right; exact ⟨_, by simp only [R, ha, Bool.false_eq_true, ↓reduceIte], Nat.le_refl _⟩
    · rcases hF c with hn | ⟨e, he, hs⟩
      · have h1 : O k c = none := hn k (List.mem_cons_self ..)
        have h2 : R c = none := by
          have hall : (ks.all fun k => (O k c).isNone) = true :=
            List.all_eq_true.2 fun k' hk' => by simp [hn k' (List.mem_cons_of_mem _ hk')]
          simp only [R, hall, ↓reduceIte]
        simp [Tol.add, h1, h2, OLe]
      · rw [he]
        apply OLe.of_getD
        show (Tol.add (O k) R).val c ≤ e
        rw [Tol.val_add, hRv]
        simp only [List.map_cons, List.sum_cons] at hs
        exact hs

theorem Tol.add_exact (t : Tol) : (t.add Tol.exact).Le t := fun c => by
  simp only [Tol.add, Tol.exact]; cases t c <;> simp [OLe]

/-- **`GROUP BY` on exact keys in `M₁`**: the groups pair up, and each
measure column's budget is its argument's, plus its cost per input row. -/
theorem aggregateEval_nearL1 {t : Tol} {gs : List Expr} {ms : List Measure} {mask : Nat → Bool}
    {env : List AVal} {N : Option Nat} (hg : gs.all (fun g => t.exactOn g.cols) = true)
    (hls : (ms.map (·.l1 t mask env N)).all Option.isSome = true) {a p : Relation}
    (w : PairsWithin a p t) (henv : ∀ row ∈ p, EnvMem env row)
    (hN : ∀ n, N = some n → p.length ≤ n) :
    PairsWithin (aggregateEval gs ms a) (aggregateEval gs ms p)
      (Tol.cat gs.length Tol.exact (Tol.ofL1 (ms.map (·.l1 t mask env N)) t (N.getD 0))) := by
  have hkey : ∀ (tr : Tol) (x y : Row), tr.Le t → tr.Rows x y → groupKey gs x = groupKey gs y :=
    fun tr x y hle r => List.map_congr_left fun g hg' =>
      Expr.eval_rows (Tol.exactOn_of_le hle (List.all_eq_true.1 hg g hg')) r
  -- An entry that costs per row has a row bound, which `p` meets.
  have hent : ∀ j i c, (ms.map (·.l1 t mask env N)).getD j none = some (some (i, c)) →
      p.length ≤ N.getD 0 := by
    intro j i c hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hj
    cases hm : ms[j]? with
    | none => simp [hm] at hj
    | some m =>
      simp only [hm, Option.map_some, Option.getD_some] at hj
      obtain ⟨n, rfl⟩ := Measure.l1_rows hj
      exact hN n rfl
  unfold aggregateEval
  split
  · rename_i he
    have h0 : gs.length = 0 := by simpa using he
    have hr := Tol.rows_append (n := 0) (t := Tol.exact) (x := []) (x' := []) (Tol.rows_refl _ _)
      (measures_rowsL1 hls w (Tol.Le.refl _) henv hN) rfl
    simp only [List.nil_append] at hr
    rw [h0]
    refine ⟨_, Tol.exact, hr, trivial, (Tol.add_exact _).trans
      (Tol.cat_mono 0 (Tol.Le.refl _) fun k => ?_)⟩
    simp only [Tol.ofL1]
    split
    · rename_i i c hk
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hent k i c hk)) _
    · exact OLe.refl _
  · rw [(w.forall2 (Tol.Le.refl t)).map_eq fun x y r => hkey t x y (Tol.Le.refl _) r]
    -- Groups are classes of canonical keys: pair them up by the keys' canonical forms.
    have hnd : ((distinctRows (p.map (groupKey gs))).map Row.canon).Nodup :=
      List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr (canonReps_pairwise Row.leRaw_rawOrder _))
    have hks : ∀ y ∈ p, (groupKey gs y).canon ∈ (distinctRows (p.map (groupKey gs))).map Row.canon :=
      fun y hy => List.mem_map.2 ⟨_, classRep_mem_canonReps (List.mem_map_of_mem hy), classRep_canon _ _⟩
    have hkey' : ∀ (tr : Tol) (x y : Row), tr.Le t → tr.Rows x y →
        (groupKey gs x).canon = (groupKey gs y).canon := fun tr x y hle r => by rw [hkey tr x y hle r]
    obtain ⟨ts₀, hw, hl, hs⟩ := w.groups hkey' hnd (Tol.Le.refl _) hks
    have hcnt := sum_filter_length (key := fun x => (groupKey gs x).canon) hnd hks
    simp only [List.map_map] at hs hcnt
    let ts : Row → Tol := fun k => ts₀ k.canon
    replace hw : ∀ k, PairsWithin (groupRows gs a k) (groupRows gs p k) (ts k) := fun k => hw _
    replace hl : ∀ k, (ts k).Le t := fun k => hl _
    refine PairsWithin.of_map (O := fun k => Tol.cat gs.length Tol.exact
      (Tol.ofL1 (ms.map (·.l1 t mask env N)) (ts k) (groupRows gs p k).length))
      (fun k hk => ?_) (fun c => ?_)
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 (canonReps_sub hk)
      refine Tol.rows_append (Tol.rows_refl _ _) (measures_rowsL1 hls (hw _) (hl _) ?_ ?_)
        (by simp [groupKey])
      · exact fun row h => henv row (List.mem_filter.1 h).1
      · exact fun n hn => Nat.le_trans (List.length_filter_le _ _) (hN n hn)
    · by_cases hc : c < gs.length
      · left; intro k _; simp [Tol.cat, hc, Tol.exact]
      · cases hlc : (ms.map (·.l1 t mask env N)).getD (c - gs.length) none with
        | some o =>
          cases o with
          | some ic =>
            obtain ⟨i, cc⟩ := ic
            right
            refine ⟨t.val i + N.getD 0 * cc, by simp only [Tol.cat, hc, ↓reduceIte, Tol.ofL1, hlc], ?_⟩
            have e : ((distinctRows (p.map (groupKey gs))).map fun k => (Tol.cat gs.length Tol.exact
                (Tol.ofL1 (ms.map (·.l1 t mask env N)) (ts k) (groupRows gs p k).length)).val c) =
                (distinctRows (p.map (groupKey gs))).map fun k =>
                  (ts k).val i + (groupRows gs p k).length * cc :=
              List.map_congr_left fun k _ => by
                simp only [Tol.val, Tol.cat, hc, ↓reduceIte, Tol.ofL1, hlc, Option.getD_some]
            rw [e, sum_map_add', sum_map_mul_const]
            have h1 := hs i
            have h2 := hent _ i cc hlc
            have h3 : ((distinctRows (p.map (groupKey gs))).map fun k => (groupRows gs p k).length).sum =
                p.length := hcnt
            rw [h3]
            exact Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2)
          | none => left; intro k _; simp only [Tol.cat, hc, ↓reduceIte, Tol.ofL1, hlc]
        | none => left; intro k _; simp only [Tol.cat, hc, ↓reduceIte, Tol.ofL1, hlc]

/-- **The `M₁` budget of a plan's output**, each source `s` within `T s`. -/
def Rel.tol1 (cat : Catalog) (K : KnowledgeEnv) (T : String → Tol) : Rel → Option Tol
  | .read s => some (T s)
  | .values _ _ => some Tol.exact
  | .filter r c => (r.tol1 cat K T).bind fun t => if t.exactOn c.cols then some t else none
  | .project r es => (r.tol1 cat K T).bind fun t =>
      if es.all (fun e => (e.tol? t).isSome) then some (Tol.pull (projSrc (r.arity cat) es) t)
      else none
  | .emit r m => (r.tol1 cat K T).map (Tol.pull fun j => m[j]?)
  | .cross a b => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      (a.rowsK K).bind fun na => (b.rowsK K).map fun nb =>
        Tol.cat (a.arity cat) (Tol.scale nb ta) (Tol.scale na tb)
  | .join a b .inner on => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      (a.rowsK K).bind fun na => (b.rowsK K).bind fun nb =>
        let t := Tol.cat (a.arity cat) (Tol.scale nb ta) (Tol.scale na tb)
        if t.exactOn on.cols then some t else none
  | .unionAll a b => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).map fun tb => ta.add tb
  | .semi a b _ on => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some ta else none
  | .orderBy r _ => r.tol1 cat K T
  | .distinct r => (r.tol1 cat K T).bind fun t =>
      if t.exactBelow (r.arity cat) then some Tol.exact else none
  | .aggregate r gs ms => (r.tol1 cat K T).bind fun t =>
      let ls := ms.map (·.l1 t (r.refCols cat) (r.analyse cat K).cols (r.rowsK K))
      if gs.all (fun g => t.exactOn g.cols) && ls.all Option.isSome then
        some (Tol.cat gs.length Tol.exact (Tol.ofL1 ls t ((r.rowsK K).getD 0)))
      else none
  | .join _ _ .left _ | .fetch .. | .window .. | .unnest .. => none

theorem Relation.NearL1.nearT {t : Tol} {a b : Relation} (h : Relation.NearL1 t a b) :
    Relation.NearT t a b :=
  let ⟨p, w, hp⟩ := h; ⟨p, w.forall2 (Tol.Le.refl t), hp⟩

/-- **`plan_near` in `M₁` (#929)**: an engine's sources within `T` of the
reference's, budgets summed over matched rows, give a result within
`Rel.tol1 cat K T r` of the reference's. -/
theorem Rel.plan_nearL1 {cat cat' : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearL1 (T s) (cat' s).rows (cat s).rows) :
    ∀ {r : Rel} {t : Tol}, r.WF cat → r.tol1 cat K T = some t →
      Relation.NearL1 t (r.eval cat') (r.eval cat)
  | .read s, t, _, h => by
    simp only [Rel.tol1, Option.some.injEq] at h; subst h; exact hT s
  | .values _ _, t, _, h => by
    simp only [Rel.tol1, Option.some.injEq] at h; subst h; exact .refl _ _
  | .filter r c, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
      exact ⟨_, w.filter (Q := fun _ => True) (fun tr x y hle rxy _ => by
          rw [Expr.eval_rows (Tol.exactOn_of_le hle hc) rxy]) (Tol.Le.refl _) (fun _ _ => trivial),
        hp.filter _⟩
    · exact absurd h (by simp)
  | .project r es, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hes
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
      have hlen : ∀ y ∈ p, y.length = r.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      exact ⟨_, w.map (Q := fun y => y.length = r.arity cat)
          (fun tr x y hle rxy hy => Tol.rows_project hes hle rxy hy) (Tol.Le.refl _) hlen,
        hp.map _⟩
    · exact absurd h (by simp)
  | .emit r m, t, hwf, h => by
    simp only [Rel.tol1, Option.map_eq_some_iff] at h
    obtain ⟨t0, hr, rfl⟩ := h
    obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
    refine ⟨_, w.map (Q := fun _ => True) (fun tr x y _ rxy _ => ?_) (Tol.Le.refl _)
      (fun _ _ => trivial), hp.map _⟩
    have e : Tol.pull (fun j => m[j]?) tr = tr.emit m := by
      funext j; simp only [Tol.pull, Tol.emit]; cases m[j]? <;> rfl
    rw [e]; exact Tol.rows_emit rxy m
  | .cross a b, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, na, hna, nb, hnb, rfl⟩ := h
    obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
    obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2 htb
    have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
      Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
    have la : (a.eval cat').length ≤ na := by
      rw [wa.length_eq, hp.length_eq]; exact Rel.rowsK_sound hK hna
    have lb : (b.eval cat').length ≤ nb := by
      rw [wb.length_eq, hq.length_eq]; exact Rel.rowsK_sound hK hnb
    exact ⟨_, (wb.cross wa hlen).mono (Tol.cat_mono _ (Tol.scale_mono lb (Tol.Le.refl _))
      (Tol.scale_mono la (Tol.Le.refl _))), crossRows_perm hp hq⟩
  | .join a b .inner on, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, na, hna, nb, hnb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
      obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2.1 htb
      have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      have la : (a.eval cat').length ≤ na := by
        rw [wa.length_eq, hp.length_eq]; exact Rel.rowsK_sound hK hna
      have lb : (b.eval cat').length ≤ nb := by
        rw [wb.length_eq, hq.length_eq]; exact Rel.rowsK_sound hK hnb
      have wc := (wb.cross wa hlen).mono (Tol.cat_mono (a.arity cat)
        (Tol.scale_mono lb (Tol.Le.refl _)) (Tol.scale_mono la (Tol.Le.refl _)))
      refine ⟨_, wc.filter (Q := fun _ => True) (fun tr x y hle rxy _ => by
          rw [Expr.eval_rows (Tol.exactOn_of_le hle hon) rxy]) (Tol.Le.refl _) (fun _ _ => trivial),
        (crossRows_perm hp hq).filter _⟩
    · exact absurd h (by simp)
  | .join _ _ .left _, _, _, h | .fetch .., _, _, h | .window .., _, _, h | .unnest .., _, _, h => by
    simp [Rel.tol1] at h
  | .unionAll a b, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
    obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2.1 htb
    exact ⟨_, wa.append wb, hp.append hq⟩
  | .semi a b anti on, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
      obtain ⟨q, fq, hq⟩ := (plan_nearL1 hcat hK ha hT hwf.2.1 htb).nearT
      have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      refine ⟨_, wa.filter (Q := fun y => y.length = a.arity cat) (fun tr x y hle rxy hy => ?_)
        (Tol.Le.refl _) hlen, hp.filter _⟩
      simp only [hasMatch]
      rw [fq.any_eq (p' := fun v => (on.eval (y ++ v)).isTrue) fun u v ruv => by
        rw [Expr.eval_rows (Tol.exactOn_of_le (Tol.cat_mono _ hle (Tol.Le.refl _)) hon)
          (Tol.rows_append rxy ruv hy)], hq.any_eq]
    · exact absurd h (by simp)
  | .orderBy r _, t, hwf, h => by
    simp only [Rel.tol1] at h
    obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 h
    obtain ⟨p', hpp, w'⟩ := PairsWithin.perm (List.mergeSort_perm _ _).symm w
    exact ⟨p', w', hpp.symm.trans (hp.trans (List.mergeSort_perm _ _).symm)⟩
  | .distinct r, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      have hw : r.WF cat := hwf
      obtain ⟨p, fp, hp⟩ := (plan_nearL1 hcat hK ha hT hw hr).nearT.forall2_mem (Rel.eval_arity hcat hw)
      have : r.eval cat' = p := Forall2.eq (fp.imp fun x y rxy => Tol.rows_eq he rxy.1 rxy.2)
      simp only [Rel.eval, this]
      exact ⟨_, PairsWithin.refl _ _, canonReps_perm Row.leRaw_rawOrder hp⟩
    · exact absurd h (by simp)
  | .aggregate r gs ms, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
      have hof : ∀ m ∈ ms, m.orderFree = true := fun m hm => by
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1
          (List.all_eq_true.1 hok.2 _ (List.mem_map_of_mem hm))
        exact Measure.l1_orderFree ho
      have henv : ∀ row ∈ p, EnvMem (r.analyse cat K).cols row := fun row h' =>
        (Rel.analyse_sound hcat hK hwf.1 (sz := false) (by simp)).1 row (hp.mem_iff.1 h')
      have hN : ∀ n, r.rowsK K = some n → p.length ≤ n := fun n hn => by
        rw [hp.length_eq]; exact Rel.rowsK_sound hK hn
      simp only [Rel.eval]
      exact ⟨_, aggregateEval_nearL1 hok.1 hok.2 w henv hN, aggregateEval_perm hof hp⟩
    · exact absurd h (by simp)

/-! ## Examples

A table of three columns of at most 10 rows, the third a double with an
`M₁` budget of 8 codes. -/

private def exCat1 : Catalog := fun _ => ⟨3, []⟩
private def exK1 : KnowledgeEnv := fun _ => ⟨[], [], [], some 10⟩
private def exT1 : String → Tol := fun _ c => if c = 2 then some 8 else none
private def exB (r : Rel) : Option (List (Option Nat)) :=
  (r.tol1 exCat1 exK1 exT1).map fun t => (List.range 6).map t

-- A union adds the budgets; `M∞` would take the larger.
#guard exB (.unionAll (.read "t") (.read "t")) == some [none, none, some 16, none, none, none]
-- A cross counts each side's budget once per row of the other: 10 · 8.
#guard exB (.cross (.read "t") (.read "t")) == some [none, none, some 80, none, none, some 80]
-- A projection copies the budget of the column it reads.
#guard exB (.project (.read "t") [.field 2]) == some [none, none, some 8, some 8, none, none]
-- A filter on the double is refused, as in `M∞`.
#guard exB (.filter (.read "t") (.bin .lt (.field 2) (.lit (.int 5)))) == none

/-- The table's knowledge: at most 10 rows, the double in `[-10⁶, 10⁶]`. -/
private def exK1r : KnowledgeEnv := fun _ =>
  ⟨[AVal.top, AVal.top, AVal.num false ⟨some (FloatCode.ofFloat (-1.0e6)), some (FloatCode.ofFloat 1.0e6)⟩ .float],
    [], [], some 10⟩
private def exS (r : Rel) : Option (List Bool) :=
  (r.tol1 exCat1 exK1r exT1).map fun t => (List.range 4).map fun c => (t c).isSome

-- `SUM` and `AVG` of the double, grouped by an exact column, have a budget: the
-- column's once, plus a cost per input row (`sumCost1`, `avgCost1`).
#guard exS (.aggregate (.read "t") [.field 0] [{ fn := .fsum, arg := .field 2 }, { fn := .avg, arg := .field 2 }]) ==
  some [false, true, true, false]
#guard (Rel.tol1 exCat1 exK1r exT1 (.aggregate (.read "t") [] [{ fn := .fsum, arg := .field 2 }])).map (· 0) ==
  some (some (8 + 10 * sumCost1 10 8 (magOf (FloatCode.ofFloat (-1.0e6)) (FloatCode.ofFloat 1.0e6))))
-- Without a range, or of a `DISTINCT`, refused; `COUNT` is exact.
#guard exB (.aggregate (.read "t") [.field 0] [{ fn := .fsum, arg := .field 2 }]) == none
#guard exS (.aggregate (.read "t") [] [{ fn := .fsum, arg := .field 2, distinct := true }]) == none
#guard exB (.aggregate (.read "t") [.field 0] [{ fn := .count, arg := .lit (.int 1) }]) ==
  some [none, none, none, none, none, none]

end Substrait
