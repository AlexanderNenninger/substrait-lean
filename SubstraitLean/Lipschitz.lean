import SubstraitLean.Compose
import SubstraitLean.Ties
import SubstraitLean.Robust
import SubstraitLean.FloatNear
import SubstraitLean.Knowledge

/-!
# Tolerance composition along a plan (#929)

A result within `t c` codes of the reference in each double column `c`
(`Relation.Near`, #896) stays within a computed tolerance of it after every
operator the plan applies. This module gives the fold, its theorem and the
pipeline rule:

* `Rel.tol cat T r`: the tolerance of `r`'s output when each source `s` is
  within `T s` of the reference's: #929's table on its rows whose constant
  is `0` or `1`. Pass-through columns, emits, `UNION ALL` (the larger of its
  inputs'), crosses, joins and semi-joins on exact columns carry a tolerance
  with `M∞ = 1`; an expression of exact columns, a group key and an
  order-free measure of exact columns are exact. It is `none` where the plan
  compares a tolerated column (a filter, join or semi-join condition, a group
  key, a measure's argument or filter, `DISTINCT`): #929's discontinuity
  rows, the `rows_exact` rule of #568. `FETCH` and windows read an order the
  multiset observation does not fix, and `UNNEST` is not in the table yet.
* `Rel.plan_near`: **the theorem.** An engine's sources within `T` of the
  reference's give a result within `Rel.tol cat T r` of the reference's.
* `Relation.NearT.add`: the triangle rule, and `Rel.pipeline_near`, the
  pipeline rule `εₖ = Lₖ·εₖ₋₁ + rₖ`: a node's bound is the next node's
  source tolerance (`Triple.ε` of #929), and the node's own rounding `rₖ`
  adds to what its plan carries.
* `Relation.NearL1`: the `M₁` metric, rows matched so that each column's
  distances sum within a budget (what a downstream `SUM` sees), with
  reflexivity, symmetry and the triangle rule.
* `Measure.fsum_near`, `Measure.avg_near`: a `SUM` or `AVG` of a tolerated
  column on groups within a tolerance, the table's `g·ε + r` and `ε + r`
  (`floatSumCR_near`, `floatAvgCR_near` on the values), with finite values
  and results as named hypotheses.

The tolerance is in codes (`Tol`): a finite double's code is twice its
magnitude in units of `2⁻¹⁰⁷⁴`, plus one, with its sign (`FloatFormat`), so
codes measure absolute distance and a Lipschitz constant on codes is one on
values. The `SUM` and `AVG` rows enter `Rel.tol` once the fold reads group
sizes and ranges from `Knowledge` (after #923); the arithmetic rows (`c · x`,
`x · y`, `x / y`), `MIN`, `MAX` and the `M₁` fold follow (#929 step 5) and
extend `Expr.tol?` and `Measure.tolOk`.

A tolerance leaves its other columns exact, and compares them exactly:
`Tol.kind t` marks only the tolerated columns as doubles, so a filter on an
exact column reads one value on both sides (`Tol.cell_none`).
`Relation.NearT.near` gives `Relation.Near` under the plan's own column
kinds. -/

namespace Substrait

/-! ## Tolerances, cell by cell -/

/-- The observation of `Relation.Near`: rows as a multiset, doubles within
the plan's bound. -/
def nearObs : Obs := { rows := .multiset, floats := .within "plan" }

/-- Only the tolerated columns are doubles; the others are observed exactly. -/
def Tol.kind (t : Tol) : Nat → ColKind := fun c => if (t c).isSome then .double else .other

/-- The context of `t`, with `Tol.kind t`. -/
def Tol.ctx (t : Tol) : ObsCtx := ObsCtx.ofTol t.kind t

/-- The tolerance that leaves every column exact. -/
def Tol.exact : Tol := fun _ => none

/-- `a` no looser than `b`: exact, or both bounds with `a ≤ b`. -/
def OLe : Option Nat → Option Nat → Prop
  | none, _ => True
  | some a, some b => a ≤ b
  | some _, none => False

theorem OLe.refl : ∀ o, OLe o o
  | none => trivial
  | some a => Nat.le_refl a

/-- Two values of column `j` within `t`. -/
def Tol.Cell (t : Tol) (j : Nat) (v w : Value) : Prop := Value.Equiv nearObs t.ctx j v w

/-- Two rows within `t`: the same width, every column within `t`. -/
def Tol.Rows (t : Tol) (x y : Row) : Prop :=
  x.length = y.length ∧ ∀ j, t.Cell j (x.getD j .null) (y.getD j .null)

/-- **Two results within `t`**: a permutation, then row by row within `t`.
`Relation.Near` with `Tol.kind t` (`Relation.NearT_iff`). -/
def Relation.NearT (t : Tol) (a b : Relation) : Prop :=
  ∃ p, Forall2 t.Rows a p ∧ p.Perm b

section
variable {t t' : Tol}

theorem Tol.ctx_wf (t : Tol) : t.ctx.WF := ObsCtx.ofTol_wf _ _

theorem Tol.cell_refl (t : Tol) (j : Nat) (v : Value) : t.Cell j v v :=
  Value.Equiv.refl ((Tol.ctx_wf t).reflAt _) v

theorem Tol.cell_symm {j : Nat} {v w : Value} (h : t.Cell j v w) : t.Cell j w v :=
  Value.Equiv.symm (Tol.ctx_wf t) v w h

theorem Tol.cell_null (t : Tol) (j : Nat) : t.Cell j .null .null := trivial

theorem Tol.exactCol {j : Nat} (h : t j = none) : t.ctx.exactCol nearObs j = true := by
  simp [ObsCtx.exactCol, ObsCtx.colIgnores, Tol.ctx, ObsCtx.ofTol, Tol.kind, h, nearObs]

/-- **An exact column is compared exactly.** -/
theorem Tol.cell_none {j : Nat} (h : t j = none) {v w : Value} : t.Cell j v w ↔ v = w :=
  ⟨Value.Equiv.eq_of_exactCol (Tol.exactCol h) v w, fun e => e ▸ Tol.cell_refl t j v⟩

theorem IntEquiv.transfer {q : Obs} {c c' : ObsCtx} {i j : Nat} (hk : c.kind i = c'.kind j)
    (hn : ∀ n a b, c.near n i a b → c'.near n j a b) {a b : Int} (e : IntEquiv q c i a b) :
    IntEquiv q c' j a b := by
  unfold IntEquiv at *; rw [← hk]
  cases hc : c.kind i <;> simp only [hc] at e ⊢
  · cases hf : q.floats <;> simp only [hf] at e ⊢
    · exact e
    · exact hn _ _ _ e
  all_goals exact e

theorem StrEquiv.transfer {q : Obs} {c c' : ObsCtx} {i j : Nat} (hk : c.kind i = c'.kind j)
    (hs : ∀ s a b, c.strEq s a b → c'.strEq s a b) {a b : String} (e : StrEquiv q c i a b) :
    StrEquiv q c' j a b := by
  unfold StrEquiv Obs.stringsAt at *; rw [← hk]
  split <;> (rename_i h; simp only [h, ite_true, ite_false] at e) <;>
    cases hs' : q.strings <;> simp only [hs', StrEquivAt] at e ⊢ <;>
    first | exact e | exact hs _ _ _ e

mutual
/-- Equality up to `q` carries from column `i` of `c` to column `j` of `c'`
when `j` is the same kind with a looser tolerance. -/
theorem Value.Equiv.transfer {q : Obs} {c c' : ObsCtx} {i j : Nat} (hk : c.kind i = c'.kind j)
    (hn : ∀ n a b, c.near n i a b → c'.near n j a b) (hs : ∀ s a b, c.strEq s a b → c'.strEq s a b) :
    ∀ v w, Value.Equiv q c i v w → Value.Equiv q c' j v w
  | .null, w, e => by cases w <;> first | trivial | exact e.elim
  | .bool _, w, e => by cases w <;> first | exact e.elim | exact e
  | .int _, w, e | .float _, w, e | .date _, w, e | .ts _, w, e | .tod _, w, e => by
    cases w <;> first | exact e.elim | exact IntEquiv.transfer hk hn e
  | .dec _ _, w, e => by cases w <;> first | exact e.elim | exact ⟨e.1, IntEquiv.transfer hk hn e.2⟩
  | .str _, w, e => by cases w <;> first | exact e.elim | exact StrEquiv.transfer hk hs e
  | .list as, w, e | .struct as, w, e => by
    cases w <;> try exact e.elim
    all_goals
      rename_i bs
      unfold Value.Equiv at e ⊢
      cases hl : q.elements <;> simp only [hl] at e ⊢
      · exact Value.EquivList.transfer hk hn hs as bs e
      · obtain ⟨cs, hc, hp⟩ := e
        exact ⟨cs, Value.EquivList.transfer hk hn hs as cs hc, hp⟩

theorem Value.EquivList.transfer {q : Obs} {c c' : ObsCtx} {i j : Nat} (hk : c.kind i = c'.kind j)
    (hn : ∀ n a b, c.near n i a b → c'.near n j a b) (hs : ∀ s a b, c.strEq s a b → c'.strEq s a b) :
    ∀ as bs, Value.EquivList q c i as bs → Value.EquivList q c' j as bs
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨e, r⟩ =>
    ⟨Value.Equiv.transfer hk hn hs a b e, Value.EquivList.transfer hk hn hs as bs r⟩
  | [], _ :: _, e | _ :: _, [], e => e.elim
end

/-- **A cell within a tighter tolerance is within a looser one**, in any
column. -/
theorem Tol.cell_transfer {i j : Nat} (h : OLe (t i) (t' j)) {v w : Value} (e : t.Cell i v w) :
    t'.Cell j v w := by
  cases hi : t i with
  | none => rw [(Tol.cell_none hi).1 e]; exact Tol.cell_refl _ _ _
  | some a =>
    rw [hi] at h
    cases hj : t' j with
    | none => rw [hj] at h; exact h.elim
    | some b =>
      rw [hj] at h
      refine Value.Equiv.transfer (c := t.ctx) (c' := t'.ctx) ?_ ?_ (fun _ _ _ x => x) v w e
      · simp [Tol.ctx, ObsCtx.ofTol, Tol.kind, hi, hj]
      · intro _ x y hn
        change t.near i x y at hn; change t'.near j x y
        change a ≤ b at h
        unfold Tol.near at *; rw [hi] at hn; rw [hj]; simp only at hn ⊢; omega

end

/-! ## Rows -/

theorem Row.equivFrom_iff {q : Obs} {ctx : ObsCtx} :
    ∀ {i : Nat} {r r' : Row}, Row.EquivFrom q ctx i r r' ↔
      r.length = r'.length ∧ ∀ j, Value.Equiv q ctx (i + j) (r.getD j .null) (r'.getD j .null)
  | _, [], [] => by simp only [Row.EquivFrom, List.length_nil, List.getD_nil, true_and]; exact
      ⟨fun _ _ => trivial, fun _ => trivial⟩
  | _, [], _ :: _ => by simp [Row.EquivFrom]
  | _, _ :: _, [] => by simp [Row.EquivFrom]
  | i, a :: as, b :: bs => by
    rw [Row.EquivFrom, Row.equivFrom_iff (i := i + 1)]
    constructor
    · rintro ⟨e, hl, h⟩
      refine ⟨by simp [hl], fun j => ?_⟩
      cases j with
      | zero => simpa using e
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using h j
    · rintro ⟨hl, h⟩
      refine ⟨by simpa using h 0, by simpa using hl, fun j => ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j + 1)

theorem Tol.rows_iff {t : Tol} {x y : Row} : Row.Equiv nearObs t.ctx x y ↔ t.Rows x y := by
  simpa [Row.Equiv, Tol.Rows, Tol.Cell] using (Row.equivFrom_iff (q := nearObs) (ctx := t.ctx) (i := 0))

/-- `Relation.NearT` is `Relation.Near` with `Tol.kind t`. -/
theorem Relation.NearT_iff {t : Tol} {a b : Relation} :
    Relation.NearT t a b ↔ Relation.Near t.kind t a b := by
  show _ ↔ ∃ p, Forall2 (Row.Equiv nearObs t.ctx) a p ∧ p.Perm b
  constructor
  · rintro ⟨p, f, hp⟩; exact ⟨p, f.imp fun _ _ e => Tol.rows_iff.2 e, hp⟩
  · rintro ⟨p, f, hp⟩; exact ⟨p, f.imp fun _ _ e => Tol.rows_iff.1 e, hp⟩

/-! ## Pairwise lists -/

namespace Forall2
variable {α β γ δ : Type}

theorem append {R : α → β → Prop} : ∀ {a : List α} {b : List β} {a' : List α} {b' : List β},
    Forall2 R a b → Forall2 R a' b' → Forall2 R (a ++ a') (b ++ b')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r t, h => .cons r (append t h)

theorem map {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ a b, R a b → S (f a) (g b)) : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
      Forall2 S (l.map f) (l'.map g)
  | _, _, .nil => .nil
  | _, _, .cons r t => .cons (h _ _ r) (map h t)

theorem map_eq {R : α → β → Prop} {f : α → γ} {g : β → γ} (h : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → l.map f = l'.map g
  | _, _, .nil => rfl
  | _, _, .cons r t => by simp [h _ _ r, map_eq h t]

theorem filter {R : α → β → Prop} {p : α → Bool} {p' : β → Bool} (h : ∀ a b, R a b → p a = p' b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 R (l.filter p) (l'.filter p')
  | _, _, .nil => .nil
  | _, _, .cons (a := a) (b := b) r t => by
    simp only [List.filter_cons, h a b r]
    split
    · exact .cons r (filter h t)
    · exact filter h t

theorem flatMap {R : α → β → Prop} {S : γ → δ → Prop} {f : α → List γ} {g : β → List δ}
    (h : ∀ a b, R a b → Forall2 S (f a) (g b)) : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
      Forall2 S (l.flatMap f) (l'.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons r t => by simpa using append (h _ _ r) (flatMap h t)

theorem any_eq {R : α → β → Prop} {p : α → Bool} {p' : β → Bool} (h : ∀ a b, R a b → p a = p' b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → l.any p = l'.any p'
  | _, _, .nil => rfl
  | _, _, .cons r t => by simp [h _ _ r, any_eq h t]

end Forall2

/-! ## Results within a tolerance -/

namespace Relation.NearT
variable {t t' : Tol} {a b a' b' : Relation}

theorem refl (t : Tol) (a : Relation) : Relation.NearT t a a :=
  ⟨a, Forall2.refl fun _ _ => ⟨rfl, fun j => Tol.cell_refl t j _⟩, .refl a⟩

theorem perm_left (h : Relation.NearT t a b) (hp : a'.Perm a) : Relation.NearT t a' b := by
  obtain ⟨p, f, hpb⟩ := h
  obtain ⟨p', hpp, f'⟩ := Forall2.perm hp.symm f
  exact ⟨p', f', hpp.symm.trans hpb⟩

theorem perm_right (h : Relation.NearT t a b) (hp : b.Perm b') : Relation.NearT t a b' :=
  let ⟨p, f, hpb⟩ := h; ⟨p, f, hpb.trans hp⟩

theorem of_perm (hp : a.Perm b) : Relation.NearT t a b := (refl t a).perm_right hp

theorem length_eq (h : Relation.NearT t a b) : a.length = b.length :=
  let ⟨_, f, hp⟩ := h; f.length_eq.trans hp.length_eq

/-- Rows of the right side, with what holds of them, carried to the
matching. -/
theorem forall2_mem {P : Row → Prop} (h : Relation.NearT t a b) (hb : ∀ y ∈ b, P y) :
    ∃ p, Forall2 (fun x y => t.Rows x y ∧ P y) a p ∧ p.Perm b := by
  obtain ⟨p, f, hp⟩ := h
  have hP : ∀ y ∈ p, P y := fun y hy => hb y (hp.mem_iff.1 hy)
  refine ⟨p, ?_, hp⟩
  clear hp hb
  induction f with
  | nil => exact .nil
  | cons r _ ih =>
    exact .cons ⟨r, hP _ (List.mem_cons_self ..)⟩ (ih fun y hy => hP y (List.mem_cons_of_mem _ hy))

theorem mono (ht : ∀ j, OLe (t j) (t' j)) (h : Relation.NearT t a b) : Relation.NearT t' a b :=
  let ⟨p, f, hp⟩ := h
  ⟨p, f.imp fun _ _ r => ⟨r.1, fun j => Tol.cell_transfer (ht j) (r.2 j)⟩, hp⟩

theorem append (h : Relation.NearT t a b) (h' : Relation.NearT t a' b') :
    Relation.NearT t (a ++ a') (b ++ b') :=
  let ⟨p, f, hp⟩ := h
  let ⟨p', f', hp'⟩ := h'
  ⟨p ++ p', f.append f', hp.append hp'⟩

/-- A filter that reads the same on rows within `t`. -/
theorem filter {P P' : Row → Bool} (hP : ∀ x y, t.Rows x y → P x = P' y)
    (h : Relation.NearT t a b) : Relation.NearT t (a.filter P) (b.filter P') :=
  let ⟨p, f, hp⟩ := h
  ⟨p.filter P', f.filter hP, hp.filter P'⟩

/-- A map that takes rows within `t` to rows within `t'`. -/
theorem map {f g : Row → Row} (hf : ∀ x y, t.Rows x y → t'.Rows (f x) (g y))
    (h : Relation.NearT t a b) : Relation.NearT t' (a.map f) (b.map g) :=
  let ⟨p, fp, hp⟩ := h
  ⟨p.map g, fp.map hf, hp.map g⟩

/-- Pairs of rows within `R` whose images are within `t'`, concatenated. -/
theorem flatMap {R : Row → Row → Prop} {f g : Row → Relation}
    (hf : ∀ x y, R x y → Relation.NearT t' (f x) (g y)) :
    ∀ {l l' : Relation}, Forall2 R l l' → Relation.NearT t' (l.flatMap f) (l'.flatMap g)
  | _, _, .nil => refl t' []
  | _, _, .cons r tl => by simpa using (hf _ _ r).append (flatMap hf tl)

/-- `filter`, with what holds of the right side's rows. -/
theorem filter_of {P : Row → Prop} {Q Q' : Row → Bool} (h : Relation.NearT t a b) (hb : ∀ y ∈ b, P y)
    (hQ : ∀ x y, t.Rows x y → P y → Q x = Q' y) : Relation.NearT t (a.filter Q) (b.filter Q') :=
  let ⟨p, f, hp⟩ := h.forall2_mem hb
  ⟨p.filter Q', (f.filter fun x y r => hQ x y r.1 r.2).imp fun _ _ r => r.1, hp.filter Q'⟩

/-- `map`, with what holds of the right side's rows. -/
theorem map_of {P : Row → Prop} {f g : Row → Row} (h : Relation.NearT t a b) (hb : ∀ y ∈ b, P y)
    (hf : ∀ x y, t.Rows x y → P y → t'.Rows (f x) (g y)) : Relation.NearT t' (a.map f) (b.map g) :=
  let ⟨p, fp, hp⟩ := h.forall2_mem hb
  ⟨p.map g, fp.map fun x y r => hf x y r.1 r.2, hp.map g⟩

/-- Row by row, results within `t'` concatenated. -/
theorem bind_of {P : Row → Prop} {f g : Row → Relation} (h : Relation.NearT t a b)
    (hb : ∀ y ∈ b, P y) (hf : ∀ x y, t.Rows x y → P y → Relation.NearT t' (f x) (g y)) :
    Relation.NearT t' (a.flatMap f) (b.flatMap g) :=
  let ⟨_, fp, hp⟩ := h.forall2_mem hb
  (flatMap (fun x y r => hf x y r.1 r.2) fp).perm_right (hp.flatMap_right g)

end Relation.NearT

/-! ## The operators, row by row -/

/-- `t` leaves the columns `cols` exact. -/
def Tol.exactOn (t : Tol) (cols : List Nat) : Bool := cols.all fun i => (t i).isNone

/-- `t` leaves the first `n` columns exact. -/
def Tol.exactBelow (t : Tol) (n : Nat) : Bool := (List.range n).all fun i => (t i).isNone

/-- Columnwise the larger of two tolerances: what `UNION ALL` gives. -/
def Tol.max (t t' : Tol) : Tol := fun c =>
  match t c, t' c with
  | some a, some b => some (Nat.max a b)
  | some a, none | none, some a => some a
  | none, none => none

/-- The first `n` columns from `t`, the rest from `t'`: what a cross, join or
project gives. -/
def Tol.cat (n : Nat) (t t' : Tol) : Tol := fun j => if j < n then t j else t' (j - n)

/-- The columns `m` picks, by position. -/
def Tol.emit (t : Tol) (m : List Nat) : Tol := fun j =>
  match m[j]? with
  | some i => t i
  | none => none

theorem Tol.le_max_left (t t' : Tol) (c : Nat) : OLe (t c) (Tol.max t t' c) := by
  unfold Tol.max; cases t c <;> cases t' c <;> simp [OLe, Nat.le_max_left]

theorem Tol.le_max_right (t t' : Tol) (c : Nat) : OLe (t' c) (Tol.max t t' c) := by
  unfold Tol.max; cases t c <;> cases t' c <;> simp [OLe, Nat.le_max_right]

theorem Tol.exactOn_none {t : Tol} {cols : List Nat} (h : t.exactOn cols = true) {i : Nat}
    (hi : i ∈ cols) : t i = none := by
  simpa [Tol.exactOn] using List.all_eq_true.1 h i hi

/-- An expression reading exact columns has one value on rows within `t`. -/
theorem Expr.eval_rows {t : Tol} {e : Expr} (he : t.exactOn e.cols = true) {x y : Row}
    (h : t.Rows x y) : e.eval x = e.eval y :=
  Expr.eval_congr_cols e fun i hi => (Tol.cell_none (Tol.exactOn_none he hi)).1 (h.2 i)

theorem getD_append_split (x y : Row) (j : Nat) :
    (x ++ y).getD j .null = if j < x.length then x.getD j .null else y.getD (j - x.length) .null := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by assumption)]
  · rw [List.getElem?_append_right (by omega)]

/-- Rows side by side: the left one `n` wide. -/
theorem Tol.rows_append {n : Nat} {t t' : Tol} {x x' y y' : Row} (hx : t.Rows x x')
    (hy : t'.Rows y y') (hn : x'.length = n) : (Tol.cat n t t').Rows (x ++ y) (x' ++ y') := by
  refine ⟨by simp [hx.1, hy.1], fun j => ?_⟩
  rw [getD_append_split, getD_append_split, hx.1]
  by_cases hj : j < x'.length
  · simp only [hj, ite_true]
    exact Tol.cell_transfer (by simp [Tol.cat, hj, ← hn, OLe.refl]) (hx.2 j)
  · simp only [hj, ite_false]
    exact Tol.cell_transfer (by simp [Tol.cat, hj, ← hn, OLe.refl]) (hy.2 _)

theorem Tol.rows_emit {t : Tol} {x y : Row} (h : t.Rows x y) (m : List Nat) :
    (t.emit m).Rows (m.map (x.getD · .null)) (m.map (y.getD · .null)) := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hj : m[j]? with
  | none => exact Tol.cell_null _ _
  | some i =>
    simp only [Option.map_some, Option.getD_some]
    have hc : t.Cell i (x.getD i .null) (y.getD i .null) := h.2 i
    simp only [List.getD_eq_getElem?_getD] at hc
    exact Tol.cell_transfer (t := t) (i := i) (by simp only [Tol.emit, hj]; exact OLe.refl _) hc

/-! ## Expressions -/

/-- The tolerance of an expression's value, `none` where the table has no
row for it yet: a column passes its tolerance through (`M∞ = M₁ = 1`), an
expression of exact columns is exact. -/
def Expr.tol? (t : Tol) (e : Expr) : Option (Option Nat) :=
  match e with
  | .field i => some (t i)
  | e => if t.exactOn e.cols then some none else none

theorem Expr.tol?_sound {t : Tol} {e : Expr} {o : Option Nat} (he : e.tol? t = some o)
    {x y : Row} (h : t.Rows x y) {t' : Tol} {j : Nat} (ho : OLe o (t' j)) :
    t'.Cell j (e.eval x) (e.eval y) := by
  unfold Expr.tol? at he
  split at he
  · rename_i i
    simp only [Option.some.injEq] at he; subst he
    exact Tol.cell_transfer ho (h.2 i)
  · split at he
    · rw [Expr.eval_rows (by assumption) h]; exact Tol.cell_refl _ _ _
    · exact absurd he (by simp)

/-- The tolerances of a projection's expressions, by position. -/
def Tol.exprs (t : Tol) (es : List Expr) : Tol := fun k =>
  match es[k]? with
  | some e => (e.tol? t).getD none
  | none => none

theorem Tol.rows_exprs {t : Tol} {es : List Expr} (hes : es.all (fun e => (e.tol? t).isSome) = true)
    {x y : Row} (h : t.Rows x y) :
    (Tol.exprs t es).Rows (es.map (·.eval x)) (es.map (·.eval y)) := by
  refine ⟨by simp, fun k => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hk : es[k]? with
  | none => exact Tol.cell_null _ _
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    have hs := List.all_eq_true.1 hes e (List.mem_of_getElem? hk)
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hs
    exact Expr.tol?_sound ho h (by simp [Tol.exprs, hk, ho, OLe.refl])

theorem Tol.rows_refl (t : Tol) (x : Row) : t.Rows x x := ⟨rfl, fun j => Tol.cell_refl t j _⟩

/-- Rows within a tolerance exact on their columns are equal. -/
theorem Tol.rows_eq {t : Tol} {n : Nat} (he : t.exactBelow n = true) {x y : Row} (h : t.Rows x y)
    (hn : y.length = n) : x = y := by
  refine List.ext_getElem h.1 fun i h1 h2 => ?_
  have hi : t i = none := by
    simpa [Tol.exactBelow] using List.all_eq_true.1 he i (List.mem_range.2 (hn ▸ h2))
  have := (Tol.cell_none hi).1 (h.2 i)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this

/-! ## Aggregates over exact columns -/

/-- A measure the table carries: order-free, not sorting, its argument and
filter reading exact columns. Its value is then exact (`M∞ = M₁ = 0` from
the tolerated columns, which it does not read). -/
def Measure.tolOk (t : Tol) (m : Measure) : Bool :=
  m.orderFree && !m.fn.sorts && t.exactOn m.arg.cols && (m.filter.all fun c => t.exactOn c.cols)

theorem Measure.eval_rows {t : Tol} {m : Measure} (hm : m.tolOk t = true) {g g' : Relation}
    (f : Forall2 t.Rows g g') : m.eval g = m.eval g' := by
  simp only [Measure.tolOk, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨⟨⟨_, hs⟩, ha⟩, hf⟩ := hm
  rw [Measure.eval_eq hs, Measure.eval_eq hs]
  have hk : Forall2 t.Rows (m.kept g) (m.kept g') := by
    unfold Measure.kept
    cases hc : m.filter with
    | none => exact f
    | some c =>
      simp only [hc, Option.all_some] at hf
      exact f.filter fun x y r => by rw [Expr.eval_rows hf r]
  unfold Measure.inputs
  rw [hk.map_eq fun x y r => Expr.eval_rows ha r]

theorem aggregateEval_rows {t : Tol} {gs : List Expr} {ms : List Measure}
    (hg : gs.all (fun g => t.exactOn g.cols) = true) (hm : ms.all (·.tolOk t) = true)
    {a p : Relation} (f : Forall2 t.Rows a p) : aggregateEval gs ms a = aggregateEval gs ms p := by
  have hkey : ∀ x y, t.Rows x y → groupKey gs x = groupKey gs y := fun x y r =>
    List.map_congr_left fun g hg' => Expr.eval_rows (List.all_eq_true.1 hg g hg') r
  have hmeas : ∀ g g', Forall2 t.Rows g g' → ms.map (·.eval g) = ms.map (·.eval g') :=
    fun g g' f' => List.map_congr_left fun m hm' => Measure.eval_rows (List.all_eq_true.1 hm m hm') f'
  unfold aggregateEval
  split
  · rw [hmeas _ _ f]
  · rw [f.map_eq hkey]
    refine List.map_congr_left fun k _ => ?_
    unfold groupRows
    rw [hmeas _ _ (f.filter fun x y r => by rw [hkey x y r])]

open FloatCode

/-! ### A `SUM` or `AVG` measure over groups within a tolerance -/

theorem Forall2.and_mem {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → (∀ a ∈ l, P a) → (∀ b ∈ l', Q b) →
      Forall2 (fun a b => R a b ∧ P a ∧ Q b) l l'
  | _, _, .nil, _, _ => .nil
  | _, _, .cons r t, hp, hq =>
    .cons ⟨r, hp _ (List.mem_cons_self ..), hq _ (List.mem_cons_self ..)⟩
      (Forall2.and_mem t (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun b hb => hq b (List.mem_cons_of_mem _ hb)))

/-- The tolerance of every column, `e`. -/
def Tol.all (e : Nat) : Tol := fun _ => some e

/-- A cell within `e` codes holds a NULL where the other does. -/
theorem Tol.cell_null_iff {e : Nat} {v w : Value} (h : (Tol.all e).Cell 0 v w) :
    (v != .null) = (w != .null) := by
  cases v <;> cases w <;> first | rfl | exact h.elim

/-- Two finite doubles in a cell within `e` codes are within `e` codes. -/
theorem Tol.cell_codeNear {e : Nat} {v w : Value} (h : (Tol.all e).Cell 0 v w)
    (hv : ∀ c, v = .float c → IsFin c) (hw : ∀ c, w = .float c → IsFin c) : CodeNear e v w := by
  cases v <;> cases w
  case float.float a b =>
    change (Tol.all e).near 0 (fp64.canon a) (fp64.canon b) at h
    rw [show fp64.canon a = a from canon_of_bounds (hv a rfl),
      show fp64.canon b = b from canon_of_bounds (hw b rfl)] at h
    exact h
  all_goals first
    | exact h.elim | exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- **The values a `SUM` or `AVG` adds are paired within `e` codes**, on groups
within `t`: the argument within `e`, the filter on exact columns, no
`DISTINCT` (which compares the values). -/
theorem Measure.inputs_near {t : Tol} {m : Measure} {e : Nat} (hd : m.distinct = false)
    (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e)) {g g' : Relation}
    (f : Forall2 t.Rows g g') (hv : FinCodes (m.inputs g)) (hw : FinCodes (m.inputs g')) :
    Forall2 (CodeNear e) (m.inputs g) (m.inputs g') := by
  obtain ⟨o, ho, hle⟩ := ha
  have hk : Forall2 t.Rows (m.kept g) (m.kept g') := by
    unfold Measure.kept
    cases hc : m.filter with
    | none => exact f
    | some c =>
      simp only [hc, Option.all_some] at hf
      exact f.filter fun x y r => by rw [Expr.eval_rows hf r]
  have hm : Forall2 ((Tol.all e).Cell 0) ((m.kept g).map fun row => m.arg.eval row)
      ((m.kept g').map fun row => m.arg.eval row) :=
    hk.map (f := fun row => m.arg.eval row) (g := fun row => m.arg.eval row)
      fun x y r => Expr.tol?_sound ho r (t' := Tol.all e) (j := 0) hle
  have hn := hm.filter (p := (· != .null)) (p' := (· != .null)) fun v w h => Tol.cell_null_iff h
  unfold Measure.inputs at hv hw ⊢
  simp only [hd, Bool.false_eq_true, ite_false] at hv hw ⊢
  exact (hn.and_mem (P := fun v => ∀ c, v = .float c → IsFin c) (Q := fun w => ∀ c, w = .float c → IsFin c)
    (fun v hv' c hc => hv c (hc ▸ hv')) (fun w hw' c hc => hw c (hc ▸ hw'))).imp
    fun v w ⟨h, pv, pw⟩ => Tol.cell_codeNear h pv pw

/-- **A `SUM` of a tolerated column** on groups within `t`: the two values
are within `g·(e + 1) + ulp + ulp' + 4` codes, `g` the values added. -/
theorem Measure.fsum_near {t : Tol} {m : Measure} {e : Nat} (hfn : m.fn = .fsum)
    (hd : m.distinct = false) (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e)) {g g' : Relation}
    (f : Forall2 t.Rows g g') (hv : FinCodes (m.inputs g)) (hw : FinCodes (m.inputs g'))
    (rv : IsFin (ofExact (exactSum (m.inputs g)))) (rw' : IsFin (ofExact (exactSum (m.inputs g')))) :
    CodeNear ((m.inputs g).length * (e + 1) + ulpDiv (exactSum (m.inputs g)) 1 +
      ulpDiv (exactSum (m.inputs g')) 1 + 4) (m.eval g) (m.eval g') := by
  have hn := Measure.inputs_near hd hf ha f hv hw
  have hs : m.fn.sorts = false := by rw [hfn]; rfl
  rw [Measure.eval_eq hs, Measure.eval_eq hs, hfn]
  generalize m.inputs g = I at *
  generalize m.inputs g' = I' at *
  cases I with
  | nil =>
    cases hn
    exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | cons v vs =>
    cases I' with
    | nil => cases hn
    | cons w ws => exact floatSumCR_near hn hv hw rv rw'

/-- **An `AVG` of a tolerated column** on groups within `t`: the two values
are within `(e + 1) + ulp + ulp' + 4` codes. -/
theorem Measure.avg_near {t : Tol} {m : Measure} {e : Nat} (hfn : m.fn = .avg)
    (hd : m.distinct = false) (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e)) {g g' : Relation}
    (f : Forall2 t.Rows g g') (hv : FinCodes (m.inputs g)) (hw : FinCodes (m.inputs g'))
    (rv : IsFin (ofExactDiv (exactSum (m.inputs g)) (m.inputs g).length))
    (rw' : IsFin (ofExactDiv (exactSum (m.inputs g')) (m.inputs g').length)) :
    CodeNear ((e + 1) + ulpDiv (exactSum (m.inputs g)) (m.inputs g).length +
      ulpDiv (exactSum (m.inputs g')) (m.inputs g').length + 4) (m.eval g) (m.eval g') := by
  have hn := Measure.inputs_near hd hf ha f hv hw
  have hs : m.fn.sorts = false := by rw [hfn]; rfl
  rw [Measure.eval_eq hs, Measure.eval_eq hs, hfn]
  generalize m.inputs g = I at *
  generalize m.inputs g' = I' at *
  cases I with
  | nil =>
    cases hn
    exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | cons v vs =>
    cases I' with
    | nil => cases hn
    | cons w ws => exact floatAvgCR_near hn hv hw rv rw'


/-! ### Columns of reference codes

The tolerance compares codes after `canon`, so `-0.0` is within any
tolerance of `+0.0`. A `SUM` counts a code below `-∞` as `-∞` (`nonFinite`),
`-0.0`'s among them, so a `SUM` of a tolerated column needs the engine's codes
there to be the reference's (`IsRef`): `Relation.RefOn`. Sverify reads every
engine value canonical (`Relation.RefCodes` of the sources); `Rel.refCols`
follows the columns that keep it: copies of source columns, and `SUM` and
`AVG` results. -/

/-- The columns `mask` names hold reference codes. -/
def Relation.RefOn (mask : Nat → Bool) (rows : Relation) : Prop :=
  ∀ row ∈ rows, ∀ j c, mask j = true → row.getD j .null = .float c → IsRef c

/-- Every double of `rows` is a reference code. -/
def Relation.RefCodes (rows : Relation) : Prop := Relation.RefOn (fun _ => true) rows

/-- The first `n` columns from `a`, the rest from `b`. -/
def maskCat (n : Nat) (a b : Nat → Bool) : Nat → Bool := fun j => if j < n then a j else b (j - n)

/-- A copy of a column `mask` names. -/
def Expr.refCol (mask : Nat → Bool) : Expr → Bool
  | .field i => mask i
  | _ => false

/-- A measure whose value is a reference code or NULL: `SUM` and `AVG` of
doubles (`floatSumCR`, `floatAvgCR`). -/
def Measure.refOut (m : Measure) : Bool :=
  match m.fn with
  | .fsum | .avg => true
  | _ => false

/-- The output columns that hold reference codes when the sources do. -/
def Rel.refCols (cat : Catalog) : Rel → Nat → Bool
  | .read _ => fun _ => true
  | .values _ _ | .window .. | .unnest .. => fun _ => false
  | .filter r _ | .orderBy r _ | .distinct r | .fetch r _ _ => r.refCols cat
  | .project r es =>
      maskCat (r.arity cat) (r.refCols cat) fun k => (es[k]?).any (·.refCol (r.refCols cat))
  | .emit r m => fun j => (m[j]?).any (r.refCols cat)
  | .cross a b | .join a b _ _ => maskCat (a.arity cat) (a.refCols cat) (b.refCols cat)
  | .unionAll a b => fun j => a.refCols cat j && b.refCols cat j
  | .semi a _ _ _ => a.refCols cat
  | .aggregate r gs ms =>
      maskCat gs.length (fun k => (gs[k]?).any (·.refCol (r.refCols cat))) fun k => (ms[k]?).any Measure.refOut

theorem Rel.refCols_congr {c cat : Catalog} (h : ∀ t, (c t).arity = (cat t).arity) :
    ∀ r : Rel, r.refCols c = r.refCols cat
  | .read _ | .values _ _ | .window .. | .unnest .. => rfl
  | .filter r _ | .orderBy r _ | .distinct r | .fetch r _ _ => Rel.refCols_congr h r
  | .project r es => by simp only [Rel.refCols, Rel.refCols_congr h r, Rel.arity_congr h r]
  | .emit r m => by simp only [Rel.refCols, Rel.refCols_congr h r]
  | .cross a b | .join a b _ _ => by
    simp only [Rel.refCols, Rel.refCols_congr h a, Rel.refCols_congr h b, Rel.arity_congr h a]
  | .unionAll a b => by simp only [Rel.refCols, Rel.refCols_congr h a, Rel.refCols_congr h b]
  | .semi a _ _ _ => by simp only [Rel.refCols, Rel.refCols_congr h a]
  | .aggregate r gs ms => by simp only [Rel.refCols, Rel.refCols_congr h r]

theorem Relation.RefOn.mono {mask : Nat → Bool} {a b : Relation} (h : Relation.RefOn mask a)
    (hs : ∀ row ∈ b, row ∈ a) : Relation.RefOn mask b := fun row hr => h row (hs row hr)

theorem RefOn.cat {n : Nat} {ma mb : Nat → Bool} {x y : Row} (hx : x.length = n)
    (ha : ∀ j c, ma j = true → x.getD j .null = .float c → IsRef c)
    (hb : ∀ j c, mb j = true → y.getD j .null = .float c → IsRef c) :
    ∀ j c, maskCat n ma mb j = true → (x ++ y).getD j .null = .float c → IsRef c := by
  intro j c hm hc
  rw [getD_append_split, hx] at hc
  by_cases hj : j < n
  · simp only [maskCat, hj, ite_true] at hm hc; exact ha j c hm hc
  · simp only [maskCat, hj, ite_false] at hm hc; exact hb _ c hm hc

theorem Expr.refCol_sound {mask : Nat → Bool} {e : Expr} (he : e.refCol mask = true) {row : Row}
    (h : ∀ j c, mask j = true → row.getD j .null = .float c → IsRef c) {c : Int}
    (hc : e.eval row = .float c) : IsRef c := by
  cases e with
  | field i => exact h i c he hc
  | _ => simp [Expr.refCol] at he

theorem nonFinite_isRef {vs : List Value} {c : Int} (h : nonFinite vs = some c) : IsRef c := by
  have h1 := fp64.posInf_lt_nan; have h2 := fp64.negInf_lt_zero; have h3 := fp64.zero_lt_posInf
  have hp : IsRef fp64.posInf := ⟨by omega, by omega⟩
  have hn : IsRef fp64.negInf := ⟨by omega, by omega⟩
  have hN : IsRef fp64.nan := ⟨by omega, by omega⟩
  unfold nonFinite at h
  split at h
  · cases h; exact hN
  split at h
  · cases h; exact hp
  split at h
  · cases h; exact hn
  · cases h

theorem floatSumCR_isRef (vs : List Value) : IsRef (floatSumCR vs) := by
  unfold floatSumCR
  cases h : nonFinite vs with
  | none => exact isRef_ofExactDiv _ _
  | some c => exact nonFinite_isRef h

theorem floatAvgCR_isRef (vs : List Value) : IsRef (floatAvgCR vs) := by
  unfold floatAvgCR
  cases h : nonFinite vs with
  | none => exact isRef_ofExactDiv _ _
  | some c => exact nonFinite_isRef h

theorem Measure.refOut_sound {m : Measure} (hm : m.refOut = true) (rows : Relation) {c : Int}
    (hc : m.eval rows = .float c) : IsRef c := by
  unfold Measure.refOut at hm
  cases hfn : m.fn <;> simp only [hfn, Bool.false_eq_true] at hm
  all_goals
    have hs : m.fn.sorts = false := by rw [hfn]; rfl
    rw [Measure.eval_eq hs, hfn] at hc
    cases h : m.inputs rows <;> rw [h] at hc <;> simp only [AggFn.apply, reduceCtorEq, Value.float.injEq] at hc
  · rw [← hc]; exact floatSumCR_isRef _
  · rw [← hc]; exact floatAvgCR_isRef _

/-- **`Rel.refCols` is sound**: on sources of reference codes, the columns it
names hold reference codes. -/
theorem Rel.refOn {cat : Catalog} (hcat : cat.WF) (hR : ∀ s, (cat s).rows.RefCodes) :
    ∀ {r : Rel}, r.WF cat → Relation.RefOn (r.refCols cat) (r.eval cat)
  | .read s, _ => fun row hr j c _ hc => hR s row hr j c rfl hc
  | .values _ _, _ | .window .., _ | .unnest .., _ => fun _ _ _ _ h => by simp [Rel.refCols] at h
  | .filter r _, hwf => (Rel.refOn hcat hR hwf.1).mono fun _ h => (List.mem_filter.1 h).1
  | .orderBy r _, hwf => (Rel.refOn hcat hR hwf.1).mono fun _ h => (List.mergeSort_perm _ _).mem_iff.1 h
  | .distinct r, hwf => (Rel.refOn hcat hR (r := r) hwf).mono fun _ h => mem_dedup.1 h
  | .fetch r _ cnt, hwf => (Rel.refOn hcat hR (r := r) hwf).mono fun _ h => by
    simp only [Rel.eval] at h
    cases cnt with
    | none => exact List.mem_of_mem_drop h
    | some _ => exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  | .semi a _ _ _, hwf => (Rel.refOn hcat hR hwf.1).mono fun _ h => (List.mem_filter.1 h).1
  | .unionAll a b, hwf => fun row hr j c hm hc => by
    simp only [Rel.refCols, Bool.and_eq_true] at hm
    rcases List.mem_append.1 hr with h | h
    · exact Rel.refOn hcat hR hwf.1 row h j c hm.1 hc
    · exact Rel.refOn hcat hR hwf.2.1 row h j c hm.2 hc
  | .emit r m, hwf => fun row hr j c hm hc => by
    simp only [Rel.eval, List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    simp only [Rel.refCols] at hm
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hc
    cases hj : m[j]? with
    | none => simp [hj] at hm
    | some i =>
      simp only [hj, Option.any_some] at hm
      simp only [hj, Option.map_some, Option.getD_some] at hc
      exact Rel.refOn hcat hR hwf.1 x hx i c hm (by rw [List.getD_eq_getElem?_getD]; exact hc)
  | .project r es, hwf => fun row hr j c hm hc => by
    simp only [Rel.eval, List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    refine RefOn.cat (Rel.eval_arity hcat hwf.1 x hx) (Rel.refOn hcat hR hwf.1 x hx) ?_ j c hm hc
    intro k c' hk hc'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hc'
    cases he : es[k]? with
    | none => simp [he] at hc'
    | some e =>
      simp only [he, Option.any_some] at hk
      simp only [he, Option.map_some, Option.getD_some] at hc'
      exact Expr.refCol_sound hk (Rel.refOn hcat hR hwf.1 x hx) hc'
  | .cross a b, hwf => fun row hr j c hm hc => by
    simp only [Rel.eval, crossRows, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨x, hx, y, hy, rfl⟩ := hr
    exact RefOn.cat (Rel.eval_arity hcat hwf.1 x hx) (Rel.refOn hcat hR hwf.1 x hx)
      (Rel.refOn hcat hR hwf.2 y hy) j c hm hc
  | .join a b jt _, hwf => fun row hr j c hm hc => by
    have hA := Rel.refOn hcat hR hwf.1
    have hB := Rel.refOn hcat hR hwf.2.1
    cases jt with
    | inner =>
      simp only [Rel.eval, List.mem_filter, crossRows, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨⟨x, hx, y, hy, rfl⟩, -⟩ := hr
      exact RefOn.cat (Rel.eval_arity hcat hwf.1 x hx) (hA x hx) (hB y hy) j c hm hc
    | left =>
      simp only [Rel.eval, List.mem_flatMap] at hr
      obtain ⟨x, hx, hr⟩ := hr
      unfold leftJoinRow at hr
      simp only at hr
      split at hr
      · simp only [List.mem_singleton] at hr; subst hr
        refine RefOn.cat (Rel.eval_arity hcat hwf.1 x hx) (hA x hx) ?_ j c hm hc
        intro k c' _ h'
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate] at h'
        split at h' <;> simp at h'
      · simp only [List.mem_filter, List.mem_map] at hr
        obtain ⟨⟨y, hy, rfl⟩, -⟩ := hr
        exact RefOn.cat (Rel.eval_arity hcat hwf.1 x hx) (hA x hx) (hB y hy) j c hm hc
  | .aggregate r gs ms, hwf => fun row hr j c hm hc => by
    have hI := Rel.refOn hcat hR hwf.1
    have hms : ∀ (g : Relation) k c', (ms[k]?).any Measure.refOut = true →
        (ms.map (·.eval g)).getD k .null = .float c' → IsRef c' := by
      intro g k c' hk h'
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at h'
      cases he : ms[k]? with
      | none => simp [he] at h'
      | some m =>
        simp only [he, Option.any_some] at hk
        simp only [he, Option.map_some, Option.getD_some] at h'
        exact Measure.refOut_sound hk g h'
    simp only [Rel.eval, aggregateEval] at hr
    split at hr
    · rename_i hg
      simp only [List.mem_singleton] at hr; subst hr
      have : gs.length = 0 := by simpa using hg
      simp only [Rel.refCols, maskCat, this, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hm
      exact hms _ j c hm hc
    · simp only [List.mem_map] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_dedup.1 hk)
      refine RefOn.cat (by simp [groupKey]) ?_ (hms _) j c hm hc
      intro i c' hi h'
      simp only [groupKey, List.getD_eq_getElem?_getD, List.getElem?_map] at h'
      cases he : gs[i]? with
      | none => simp [he] at h'
      | some e =>
        simp only [he, Option.any_some] at hi
        simp only [he, Option.map_some, Option.getD_some] at h'
        exact Expr.refCol_sound hi (hI x hx) h'

/-! ## The fold and its theorem -/

/-- **The tolerance of a plan's output**, when each source `s` is within
`T s` of the reference's: the table of #929 on its constant-`1` rows. `none`
where the plan compares a tolerated column (a filter, join or semi-join
condition, a group key, a measure's argument, `DISTINCT`), and for the
operators whose rows depend on an order the multiset observation does not
fix (`FETCH`, windows) or not yet in the table (`UNNEST`). -/
def Rel.tol (cat : Catalog) (T : String → Tol) : Rel → Option Tol
  | .read s => some (T s)
  | .values _ _ => some Tol.exact
  | .filter r c => (r.tol cat T).bind fun t => if t.exactOn c.cols then some t else none
  | .project r es => (r.tol cat T).bind fun t =>
      if es.all (fun e => (e.tol? t).isSome) then some (Tol.cat (r.arity cat) t (Tol.exprs t es))
      else none
  | .emit r m => (r.tol cat T).map (Tol.emit · m)
  | .cross a b => (a.tol cat T).bind fun ta => (b.tol cat T).map fun tb => Tol.cat (a.arity cat) ta tb
  | .join a b _ on => (a.tol cat T).bind fun ta => (b.tol cat T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some (Tol.cat (a.arity cat) ta tb)
      else none
  | .fetch .. | .window .. | .unnest .. => none
  | .unionAll a b => (a.tol cat T).bind fun ta => (b.tol cat T).map fun tb => Tol.max ta tb
  | .semi a b _ on => (a.tol cat T).bind fun ta => (b.tol cat T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some ta else none
  | .orderBy r _ => r.tol cat T
  | .distinct r => (r.tol cat T).bind fun t =>
      if t.exactBelow (r.arity cat) then some Tol.exact else none
  | .aggregate r gs ms => (r.tol cat T).bind fun t =>
      if gs.all (fun g => t.exactOn g.cols) && ms.all (·.tolOk t) then some Tol.exact else none

/-- **`plan_near` (#929)**: an engine's sources within `T` of the
reference's give a result within `Rel.tol cat T r` of the reference's, rows
as a multiset. `cat'` is the engine's catalog, with the reference's arities;
the reference's catalog is well-formed. -/
theorem Rel.plan_near {cat cat' : Catalog} (hcat : cat.WF)
    (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearT (T s) (cat' s).rows (cat s).rows) :
    ∀ {r : Rel} {t : Tol}, r.WF cat → r.tol cat T = some t →
      Relation.NearT t (r.eval cat') (r.eval cat)
  | .read s, t, _, h => by
    simp only [Rel.tol, Option.some.injEq] at h; subst h; exact hT s
  | .values _ _, t, _, h => by
    simp only [Rel.tol, Option.some.injEq] at h; subst h; exact .refl _ _
  | .filter r c, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact (plan_near hcat ha hT hwf.1 hr).filter fun x y r => by rw [Expr.eval_rows (by assumption) r]
    · exact absurd h (by simp)
  | .project r es, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact (plan_near hcat ha hT hwf.1 hr).map_of (Rel.eval_arity hcat hwf.1) fun x y rxy hy =>
        Tol.rows_append rxy (Tol.rows_exprs (by assumption) rxy) hy
    · exact absurd h (by simp)
  | .emit r m, t, hwf, h => by
    simp only [Rel.tol, Option.map_eq_some_iff] at h
    obtain ⟨t0, hr, rfl⟩ := h
    exact (plan_near hcat ha hT hwf.1 hr).map fun x y rxy => Tol.rows_emit rxy m
  | .cross a b, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    have hb := plan_near hcat ha hT hwf.2 htb
    exact (plan_near hcat ha hT hwf.1 hta).bind_of (Rel.eval_arity hcat hwf.1) fun x y rxy hy =>
      hb.map fun u v ruv => Tol.rows_append rxy ruv hy
  | .join a b jt on, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      have hA := plan_near hcat ha hT hwf.1 hta
      have hb := plan_near hcat ha hT hwf.2.1 htb
      have hcross : ∀ x y, ta.Rows x y → y.length = a.arity cat →
          Relation.NearT (Tol.cat (a.arity cat) ta tb) ((b.eval cat').map (x ++ ·))
            ((b.eval cat).map (y ++ ·)) :=
        fun x y rxy hy => hb.map fun u v ruv => Tol.rows_append rxy ruv hy
      cases jt with
      | inner =>
        exact (hA.bind_of (Rel.eval_arity hcat hwf.1) hcross).filter fun x y r => by
          rw [Expr.eval_rows hon r]
      | left =>
        simp only [Rel.eval]
        rw [Rel.arity_congr ha b]
        refine hA.bind_of (Rel.eval_arity hcat hwf.1) fun x y rxy hy => ?_
        have hms := (hcross x y rxy hy).filter (P := fun row => (on.eval row).isTrue)
          (P' := fun row => (on.eval row).isTrue) fun u v r => by rw [Expr.eval_rows hon r]
        have hl := hms.length_eq
        unfold leftJoinRow
        simp only
        cases h1 : ((b.eval cat').map (x ++ ·)).filter (fun row => (on.eval row).isTrue) with
        | nil =>
          cases h2 : ((b.eval cat).map (y ++ ·)).filter (fun row => (on.eval row).isTrue) with
          | nil =>
            exact ⟨_, .cons (Tol.rows_append rxy (Tol.rows_refl tb _) hy) .nil, .refl _⟩
          | cons _ _ => rw [h1, h2] at hl; simp at hl
        | cons r rs =>
          cases h2 : ((b.eval cat).map (y ++ ·)).filter (fun row => (on.eval row).isTrue) with
          | nil => rw [h1, h2] at hl; simp at hl
          | cons _ _ => rw [h1, h2] at hms; exact hms
    · exact absurd h (by simp)
  | .fetch .., _, _, h | .window .., _, _, h | .unnest .., _, _, h => by simp [Rel.tol] at h
  | .unionAll a b, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    exact ((plan_near hcat ha hT hwf.1 hta).mono (Tol.le_max_left ta tb)).append
      ((plan_near hcat ha hT hwf.2.1 htb).mono (Tol.le_max_right ta tb))
  | .semi a b anti on, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := plan_near hcat ha hT hwf.2.1 htb
      refine (plan_near hcat ha hT hwf.1 hta).filter_of (Rel.eval_arity hcat hwf.1)
        fun x y rxy hy => ?_
      simp only [hasMatch]
      rw [fp.any_eq (p' := fun v => (on.eval (y ++ v)).isTrue) fun u v ruv => by
        rw [Expr.eval_rows hon (Tol.rows_append rxy ruv hy)], hp.any_eq]
    · exact absurd h (by simp)
  | .orderBy r _, t, hwf, h => by
    simp only [Rel.tol] at h
    exact ((plan_near hcat ha hT hwf.1 h).perm_left (List.mergeSort_perm _ _)).perm_right
      (List.mergeSort_perm _ _).symm
  | .distinct r, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      have hw : r.WF cat := hwf
      obtain ⟨p, fp, hp⟩ := (plan_near hcat ha hT hw hr).forall2_mem (Rel.eval_arity hcat hw)
      have : r.eval cat' = p := Forall2.eq (fp.imp fun x y rxy => Tol.rows_eq he rxy.1 rxy.2)
      simp only [Rel.eval, this]
      exact .of_perm (dedup_perm_of_mem fun z => hp.mem_iff)
    · exact absurd h (by simp)
  | .aggregate r gs ms, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := plan_near hcat ha hT hwf.1 hr
      have hof : ∀ m ∈ ms, m.orderFree = true := fun m hm => by
        have := List.all_eq_true.1 hok.2 m hm
        simp only [Measure.tolOk, Bool.and_eq_true] at this
        exact this.1.1.1
      simp only [Rel.eval]
      rw [aggregateEval_rows hok.1 hok.2 fp]
      exact .of_perm (aggregateEval_perm hof hp)
    · exact absurd h (by simp)

/-! ## The triangle rule and pipelines -/

theorem Tol.le_add_left (t₁ t₂ : Tol) (c : Nat) : OLe (t₁ c) (t₁.add t₂ c) := by
  unfold Tol.add; cases t₁ c <;> cases t₂ c <;> simp [OLe]

theorem Tol.le_add_right (t₁ t₂ : Tol) (c : Nat) : OLe (t₂ c) (t₁.add t₂ c) := by
  unfold Tol.add; cases t₁ c <;> cases t₂ c <;> simp [OLe]

/-- The context of `t` with every column a double. -/
def Tol.dctx (t : Tol) : ObsCtx := ObsCtx.ofTol (fun _ => .double) t

/-- **Cells add along a chain.** -/
theorem Tol.cell_trans {t₁ t₂ : Tol} {i : Nat} {v w z : Value} (h₁ : t₁.Cell i v w)
    (h₂ : t₂.Cell i w z) : (t₁.add t₂).Cell i v z := by
  cases hi : t₁ i with
  | none =>
    rw [(Tol.cell_none hi).1 h₁]; exact Tol.cell_transfer (Tol.le_add_right t₁ t₂ i) h₂
  | some e₁ =>
    cases hj : t₂ i with
    | none =>
      rw [← (Tol.cell_none hj).1 h₂]; exact Tol.cell_transfer (Tol.le_add_left t₁ t₂ i) h₁
    | some e₂ =>
      have hs : ∀ s a b, (fun (_ : StringObs) (a b : String) => a = b) s a b →
          (fun (_ : StringObs) (a b : String) => a = b) s a b := fun _ _ _ x => x
      have hadd : (t₁.add t₂) i = some (e₁ + e₂) := by simp [Tol.add, hi, hj]
      have d₁ : Value.Equiv nearObs t₁.dctx i v w :=
        Value.Equiv.transfer (c := t₁.ctx) (c' := t₁.dctx) (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hi])
          (fun _ _ _ x => x) hs v w h₁
      have d₂ : Value.Equiv nearObs t₂.dctx i w z :=
        Value.Equiv.transfer (c := t₂.ctx) (c' := t₂.dctx) (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hj])
          (fun _ _ _ x => x) hs w z h₂
      have d₃ : Value.Equiv nearObs (t₁.add t₂).dctx i v z :=
        Value.Equiv.trans (c₁ := t₁.dctx) (c₂ := t₂.dctx) (c₃ := (t₁.add t₂).dctx)
          ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ x y => (Tol.near_add x y : (t₁.add t₂).near _ _ _),
            fun _ _ _ _ (x : _ = _) y => x.trans y⟩ v w z d₁ d₂
      exact Value.Equiv.transfer (c := (t₁.add t₂).dctx) (c' := (t₁.add t₂).ctx)
        (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hadd]) (fun _ _ _ x => x) hs v z d₃

theorem Tol.rows_trans {t₁ t₂ : Tol} {x y z : Row} (h₁ : t₁.Rows x y) (h₂ : t₂.Rows y z) :
    (t₁.add t₂).Rows x z :=
  ⟨h₁.1.trans h₂.1, fun j => Tol.cell_trans (h₁.2 j) (h₂.2 j)⟩

/-- **The triangle rule**: tolerances add along a chain of results. -/
theorem Relation.NearT.add {t₁ t₂ : Tol} {a b d : Relation} (h₁ : Relation.NearT t₁ a b)
    (h₂ : Relation.NearT t₂ b d) : Relation.NearT (t₁.add t₂) a d := by
  obtain ⟨p, f₁, hp⟩ := h₁
  obtain ⟨q, f₂, hq⟩ := h₂
  obtain ⟨m, hm, fm⟩ := Forall2.perm hp.symm f₂
  exact ⟨m, Forall2.trans (R := t₁.Rows) (S := t₂.Rows) (T := (t₁.add t₂).Rows)
    (fun _ _ _ r s => Tol.rows_trans r s) f₁ fm, hm.symm.trans hq⟩

theorem Relation.NearT.symm {t : Tol} {a b : Relation} (h : Relation.NearT t a b) :
    Relation.NearT t b a := by
  obtain ⟨p, f, hp⟩ := h
  obtain ⟨m, hm, fm⟩ := Forall2.perm hp (f.flip.imp fun _ _ r => (⟨r.1.symm, fun j => Tol.cell_symm (r.2 j)⟩ : t.Rows _ _))
  exact ⟨m, fm, hm.symm⟩

/-- `NearT` gives `Relation.Near` under the plan's own column kinds, as long
as they call every tolerated column a double. -/
theorem Relation.NearT.near {t : Tol} {kind : Nat → ColKind}
    (hk : ∀ c, (t c).isSome → kind c = .double) {a b : Relation} (h : Relation.NearT t a b) :
    Relation.Near kind t a b := by
  obtain ⟨p, f, hp⟩ := h
  refine ⟨p, f.imp fun x y r => ?_, hp⟩
  refine (Row.equivFrom_iff (i := 0)).2 ⟨r.1, fun j => ?_⟩
  simp only [Nat.zero_add]
  cases hj : t j with
  | none =>
    rw [(Tol.cell_none hj).1 (r.2 j)]
    exact Value.Equiv.refl ((ObsCtx.ofTol_wf kind t).reflAt _) _
  | some e =>
    exact Value.Equiv.transfer (c := t.ctx) (c' := ObsCtx.ofTol kind t)
      (by show t.kind j = kind j; simp [Tol.kind, hj, hk j (by simp [hj])])
      (fun _ _ _ x => x) (fun _ _ _ x => x) _ _ (r.2 j)

/-- **A pipeline (#929 `Triple.ε`).** Node `g`'s engine output `Eg` is
within `tg` of its reference output `Rg`; node `f` reads it as table `x`.
The engine's output `Ef` of `f`, within `rf` of the reference's `f` on the
engine's inputs (its own rounding, `contract_sound_allowed`'s `ε`), is within
`rf + Rel.tol` of the reference pipeline's output: `εₖ = Lₖ·εₖ₋₁ + rₖ`, with
`g`'s bound as `x`'s source tolerance. -/
theorem Rel.pipeline_near {cat cat' : Catalog} (hcat : cat.WF)
    (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearT (T s) (cat' s).rows (cat s).rows)
    {x : String} {n : Nat} {Eg Rg : Relation} {tg : Tol} (hg : Relation.NearT tg Eg Rg)
    (hRg : ∀ row ∈ Rg, row.length = n)
    {f : Rel} (hf : f.WF (cat.bind x ⟨n, Rg⟩)) {tf : Tol}
    (htf : f.tol (cat.bind x ⟨n, Rg⟩) (fun s => if s = x then tg else T s) = some tf)
    {rf : Tol} {Ef : Relation} (hE : Relation.NearT rf Ef (f.eval (cat'.bind x ⟨n, Eg⟩))) :
    Relation.NearT (rf.add tf) Ef (f.eval (cat.bind x ⟨n, Rg⟩)) := by
  refine hE.add (Rel.plan_near (Catalog.bind_wf hcat hRg) (fun s => ?_) (fun s => ?_) hf htf)
  · unfold Catalog.bind; split <;> simp [ha]
  · unfold Catalog.bind
    by_cases h : s = x
    · simp only [h, ite_true]; exact hg
    · simp only [h, ite_false]; exact hT s

/-! ## `M₁`: a budget summed over the matching -/

/-- `t` at least as tight as `t'` in every column. -/
def Tol.Le (t t' : Tol) : Prop := ∀ c, OLe (t c) (t' c)

/-- Matched rows whose distances sum, per column, within the budget `t`:
the first pair is within `tr`, the others within `rest`, and `tr + rest`
within `t`. A column `t` leaves exact is exact in every pair. -/
def PairsWithin : List Row → List Row → Tol → Prop
  | [], [], _ => True
  | x :: xs, y :: ys, t => ∃ tr rest : Tol, tr.Rows x y ∧ PairsWithin xs ys rest ∧ (tr.add rest).Le t
  | _, _, _ => False

/-- **The `M₁` metric (#929)**: a permutation, then rows matched pairwise
whose distances in each double column sum to at most `t` of it. What a
downstream `SUM` over the column sees: its value moves by at most the sum. -/
def Relation.NearL1 (t : Tol) (a b : Relation) : Prop :=
  ∃ p, PairsWithin a p t ∧ p.Perm b

section
variable {t t' t₁ t₂ : Tol}

theorem Tol.Le.refl (t : Tol) : t.Le t := fun _ => OLe.refl _

theorem Tol.Le.trans {t₃ : Tol} (h₁ : t₁.Le t₂) (h₂ : t₂.Le t₃) : t₁.Le t₃ := fun c => by
  have a := h₁ c; have b := h₂ c
  revert a b; cases t₁ c <;> cases t₂ c <;> cases t₃ c <;> simp [OLe] <;> omega

theorem Tol.exact_add (t : Tol) : (Tol.exact.add t).Le t := fun c => by
  simp only [Tol.add, Tol.exact]; cases t c <;> simp [OLe]

/-- Budgets in a different order. -/
theorem Tol.add_swap (a b r : Tol) : (a.add (b.add r)).Le (b.add (a.add r)) := fun c => by
  simp only [Tol.add]; cases a c <;> cases b c <;> cases r c <;> simp [OLe] <;> omega

theorem Tol.add_mono {a b a' b' : Tol} (ha : a.Le a') (hb : b.Le b') : (a.add b).Le (a'.add b') :=
  fun c => by
    have x := ha c; have y := hb c
    revert x y; simp only [Tol.add]
    cases a c <;> cases b c <;> cases a' c <;> cases b' c <;> simp [OLe] <;> omega

/-- Two chains' budgets, pair by pair. -/
theorem Tol.add_four (a b c d : Tol) : ((a.add c).add (b.add d)).Le ((a.add b).add (c.add d)) :=
  fun k => by
    simp only [Tol.add]; cases a k <;> cases b k <;> cases c k <;> cases d k <;> simp [OLe] <;> omega

theorem PairsWithin.mono : ∀ {a p : List Row} {t t' : Tol}, PairsWithin a p t → t.Le t' →
    PairsWithin a p t'
  | [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _, _, ⟨tr, rest, r, h, le⟩, ht => ⟨tr, rest, r, h, le.trans ht⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem PairsWithin.refl : ∀ (a : List Row) (t : Tol), PairsWithin a a t
  | [], _ => trivial
  | x :: xs, t => ⟨Tol.exact, t, Tol.rows_refl _ x, PairsWithin.refl xs t, Tol.exact_add t⟩

theorem PairsWithin.symm : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → PairsWithin p a t
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, _, ⟨tr, rest, r, h, le⟩ =>
    ⟨tr, rest, ⟨r.1.symm, fun j => Tol.cell_symm (r.2 j)⟩, PairsWithin.symm h, le⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- A permutation of the left side carries over to the right. -/
theorem PairsWithin.perm {a a' : List Row} (hp : a.Perm a') :
    ∀ {p : List Row} {t : Tol}, PairsWithin a p t → ∃ p', p.Perm p' ∧ PairsWithin a' p' t := by
  induction hp with
  | nil => intro p t h; cases p with
    | nil => exact ⟨[], .nil, trivial⟩
    | cons _ _ => exact h.elim
  | cons x _ ih =>
    intro p t h
    cases p with
    | nil => exact h.elim
    | cons y ys =>
      obtain ⟨tr, rest, r, h, le⟩ := h
      obtain ⟨q, hq, h'⟩ := ih h
      exact ⟨y :: q, hq.cons y, tr, rest, r, h', le⟩
  | swap x₁ x₂ l =>
    intro p t h
    match p, h with
    | y₂ :: y₁ :: ys, ⟨tr₂, rest₂, r₂, ⟨tr₁, rest₁, r₁, h, le₁⟩, le₂⟩ =>
      exact ⟨y₁ :: y₂ :: ys, .swap _ _ _, tr₁, tr₂.add rest₁, r₁,
        ⟨tr₂, rest₁, r₂, h, Tol.Le.refl _⟩,
        (Tol.add_swap tr₁ tr₂ rest₁).trans ((Tol.add_mono (Tol.Le.refl tr₂) le₁).trans le₂)⟩
  | trans _ _ ih₁ ih₂ =>
    intro p t h
    obtain ⟨q₁, hq₁, h₁⟩ := ih₁ h
    obtain ⟨q₂, hq₂, h₂⟩ := ih₂ h₁
    exact ⟨q₂, hq₁.trans hq₂, h₂⟩

theorem PairsWithin.trans : ∀ {a b d : List Row} {t₁ t₂ : Tol}, PairsWithin a b t₁ →
    PairsWithin b d t₂ → PairsWithin a d (t₁.add t₂)
  | [], [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, _, ⟨tr₁, rest₁, r₁, h₁, le₁⟩, ⟨tr₂, rest₂, r₂, h₂, le₂⟩ =>
    ⟨tr₁.add tr₂, rest₁.add rest₂, Tol.rows_trans r₁ r₂, PairsWithin.trans h₁ h₂,
      (Tol.add_four tr₁ rest₁ tr₂ rest₂).trans (Tol.add_mono le₁ le₂)⟩
  | [], [], _ :: _, _, _, _, h | _ :: _, _ :: _, [], _, _, _, h => h.elim
  | [], _ :: _, _, _, _, h, _ | _ :: _, [], _, _, _, h, _ => h.elim

theorem Relation.NearL1.refl (t : Tol) (a : Relation) : Relation.NearL1 t a a :=
  ⟨a, PairsWithin.refl a t, .refl a⟩

theorem Relation.NearL1.symm {a b : Relation} (h : Relation.NearL1 t a b) : Relation.NearL1 t b a := by
  obtain ⟨p, hw, hp⟩ := h
  obtain ⟨q, hq, h'⟩ := PairsWithin.perm hp hw.symm
  exact ⟨q, h', hq.symm⟩

/-- **The triangle rule in `M₁`**: budgets add along a chain of results. -/
theorem Relation.NearL1.add {a b d : Relation} (h₁ : Relation.NearL1 t₁ a b)
    (h₂ : Relation.NearL1 t₂ b d) : Relation.NearL1 (t₁.add t₂) a d := by
  obtain ⟨p, w₁, hp⟩ := h₁
  obtain ⟨q, w₂, hq⟩ := h₂
  obtain ⟨q', hq', w₂'⟩ := PairsWithin.perm hp.symm w₂
  exact ⟨q', w₁.trans w₂', hq'.symm.trans hq⟩

theorem Relation.NearL1.mono (ht : t.Le t') {a b : Relation} (h : Relation.NearL1 t a b) :
    Relation.NearL1 t' a b :=
  let ⟨p, w, hp⟩ := h; ⟨p, w.mono ht, hp⟩

end

/-! ## Examples

A table `t` of three columns whose third, a double, is within 8 codes. -/

private def exCat : Catalog := fun _ => ⟨3, []⟩
private def exT : String → Tol := fun _ c => if c = 2 then some 8 else none
private def exCols (r : Rel) : Option (List (Option Nat)) :=
  (r.tol exCat exT).map fun t => (List.range 4).map t

-- Pass-through and emit carry the tolerance; an exact filter keeps it.
#guard exCols (.emit (.filter (.read "t") (.bin .lt (.field 0) (.lit (.int 5)))) [2, 0]) ==
  some [some 8, none, none, none]
-- A filter on the tolerated column is refused (#568, `rows_exact`).
#guard exCols (.filter (.read "t") (.bin .lt (.field 2) (.lit (.int 5)))) == none
-- A projection: the column passes through, an expression of exact columns is exact.
#guard exCols (.project (.read "t") [.field 2, .bin .add (.field 0) (.field 1)]) ==
  some [none, none, some 8, some 8]
-- `UNION ALL` takes the larger tolerance, a cross shifts the right side's.
#guard exCols (.unionAll (.read "t") (.emit (.read "t") [2, 2, 2])) == some [some 8, some 8, some 8, none]
#guard exCols (.cross (.read "t") (.read "t")) == some [none, none, some 8, none]
-- `COUNT` grouped by an exact column is exact; grouping by the double is refused.
#guard exCols (.aggregate (.read "t") [.field 0] [{ fn := .count, arg := .lit (.int 1) }]) ==
  some [none, none, none, none]
#guard exCols (.aggregate (.read "t") [.field 2] [{ fn := .count, arg := .lit (.int 1) }]) == none
-- `FETCH` reads an order the multiset observation does not fix.
#guard exCols (.fetch (.read "t") 0 (some 1)) == none

private def tie : Tol := fun c => if c = 0 then some 2 else none

/-- A near tie (#929 step 6): the doubles of two rows with the same exact
column swap order under a perturbation of 2 codes. Sorting both results and
comparing row by row pairs `"a"` with `"b"`; the matching pairs each row with
its own. `allows_rows` decides the same (`tests/test_ties.py`). -/
example : Relation.NearT tie
    [[.int 100, .str "a"], [.int 102, .str "b"]] [[.int 102, .str "a"], [.int 100, .str "b"]] := by
  have hc : ∀ (x y : Int) (s : String), tie.Rows [.int x, .str s] [.int y, .str s] ↔
      (fp64.canon x - fp64.canon y).natAbs ≤ 2 := by
    intro x y s
    refine ⟨fun h => h.2 0, fun h => ⟨rfl, fun j => ?_⟩⟩
    match j with
    | 0 => exact h
    | 1 => exact (Tol.cell_none (by simp [tie])).2 rfl
    | _ + 2 => exact Tol.cell_null _ _
  refine ⟨[[.int 102, .str "a"], [.int 100, .str "b"]],
    .cons ((hc _ _ _).2 ?_) (.cons ((hc _ _ _).2 ?_) .nil), .refl _⟩ <;>
    rw [fp64.canon_eq_self (by have := fp64.negZero_eq; have := fp64.negNan_eq; omega),
      fp64.canon_eq_self (by have := fp64.negZero_eq; have := fp64.negNan_eq; omega)] <;> decide

end Substrait
