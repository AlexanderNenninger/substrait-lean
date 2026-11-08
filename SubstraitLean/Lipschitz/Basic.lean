import SubstraitLean.Compose
import Sverify.Core.Ties
import Sverify.Core.Robust
import SubstraitLean.FloatNear
import SubstraitLean.Knowledge

/-!
# Tolerance composition: cells, rows and the operators (#929)

The metric of `Lipschitz.lean`: a tolerance in codes per column (`Tol`),
cells and rows within it (`Tol.Cell`, `Tol.Rows`), relations within it up to
a matching (`Relation.NearT`), how each operator carries a matching, and the
`SUM` and `AVG` of a tolerated column on paired groups.
-/

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

end Substrait
