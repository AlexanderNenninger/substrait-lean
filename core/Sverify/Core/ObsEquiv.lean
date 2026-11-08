import Sverify.Core.Forall2
import Sverify.Core.Observations
import Sverify.Core.Order

/-!
# Equal up to an observation (#896)

An observation `q` (D18, `Observations.lean`) names what a consumer looks at.
This module gives it a meaning: `Relation.Equiv q ctx`, an equivalence
relation on results, "equal up to `q`". `Obs.le q' q` (`q'` refines `q`) then
has a theorem behind it, `Relation.Equiv_mono`: equality up to `q'` implies
equality up to `q`.

The core has no reals and no Unicode normalisation, so what an observation
needs from outside the model is a parameter, `ObsCtx`: the root `ORDER BY`
keys (for ties), the kind of each column (a double's code, a timestamp's
microseconds or another value), the tolerance of a named float bound as a
relation on codes, and string equality up to NFC or case folding. Their
defaults make every component exact.

`Relation.Near` is the instance with a per-column tolerance in codes, an ulp
count (#85's bounds are stated so, `Epsilon.lean`), with the triangle rule
`Relation.Near_add`. -/

namespace Substrait

/-! ## The context -/

/-- What a column holds, as far as an observation tells values apart: a
double's code (`Float.lean`), a timestamp's microseconds, a string, a
decimal (an integer at the column's scale), or anything else (observed
exactly). -/
inductive ColKind | double | timestamp | string | decimal | other
  deriving Repr, DecidableEq

/-- What the plan and the engine fix for an observation: the root `ORDER BY`
keys (for `tiesPermuted`), the kind of each column, the tolerance of each
named float bound as a relation on codes per column (from `Epsilon`, or
`|x - y| ≤ ε` over the reals in `float-bounds`), and string equality up to
NFC or case folding. The defaults make every component exact. -/
structure ObsCtx where
  keys : List SortKey := []
  kind : Nat → ColKind := fun _ => .other
  near : String → Nat → Int → Int → Prop := fun _ _ a b => a = b
  strEq : StringObs → String → String → Prop := fun _ a b => a = b

/-- A context whose relations are what their names say: `near` reflexive
and symmetric (a tolerance), `strEq` an equivalence at each level, case
folding coarser than NFC. -/
structure ObsCtx.WF (ctx : ObsCtx) : Prop where
  near_refl : ∀ n c a, ctx.near n c a a
  near_symm : ∀ n c a b, ctx.near n c a b → ctx.near n c b a
  str_refl : ∀ s a, ctx.strEq s a a
  str_symm : ∀ s a b, ctx.strEq s a b → ctx.strEq s b a
  str_trans : ∀ s a b d, ctx.strEq s a b → ctx.strEq s b d → ctx.strEq s a d
  str_mono : ∀ a b, ctx.strEq .nfc a b → ctx.strEq .casefold a b

/-- Three contexts that compose: the same keys and kinds, and `c₁`'s
relations followed by `c₂`'s within `c₃`'s. `Comp ctx ctx ctx` is
transitivity; a tolerance `t₁` then `t₂` within `t₁ + t₂` is the triangle
rule (`Relation.Near_add`). -/
structure ObsCtx.Comp (c₁ c₂ c₃ : ObsCtx) : Prop where
  keys₁ : c₁.keys = c₃.keys
  keys₂ : c₂.keys = c₃.keys
  kind₁ : c₁.kind = c₃.kind
  kind₂ : c₂.kind = c₃.kind
  near : ∀ n c a b d, c₁.near n c a b → c₂.near n c b d → c₃.near n c a d
  str : ∀ s a b d, c₁.strEq s a b → c₂.strEq s b d → c₃.strEq s a d

theorem ObsCtx.WF.default : ObsCtx.WF {} where
  near_refl _ _ _ := rfl
  near_symm _ _ _ _ h := h.symm
  str_refl _ _ := rfl
  str_symm _ _ _ h := h.symm
  str_trans _ _ _ _ h₁ h₂ := h₁.trans h₂
  str_mono _ _ h := h

/-- A context composes with itself when its tolerances are transitive (the
default's equality is). -/
theorem ObsCtx.Comp.self {ctx : ObsCtx} (h : ctx.WF)
    (hn : ∀ n c a b d, ctx.near n c a b → ctx.near n c b d → ctx.near n c a d) :
    ObsCtx.Comp ctx ctx ctx :=
  ⟨rfl, rfl, rfl, rfl, hn, h.str_trans⟩

/-! ## Values -/

/-- Timestamps are microseconds: truncation to a nanosecond or microsecond
keeps them. -/
def TimeUnit.trunc : TimeUnit → Int → Int
  | .ns | .us => Time.trunc .microsecond
  | .ms => Time.trunc .millisecond
  | .s => Time.trunc .second

/-- Truncating to a finer unit first changes nothing. -/
theorem TimeUnit.trunc_trunc {u u' : TimeUnit} (h : u'.rank ≤ u.rank) (a : Int) :
    u.trunc (u'.trunc a) = u.trunc a := by
  cases u <;> cases u' <;>
    simp_all [TimeUnit.rank, TimeUnit.trunc, Time.trunc, Time.floorTo] <;> omega

/-- A double's code with its zeros and NaNs made one where `q` says so. Codes
of the model are canonical already (`FloatFormat.canon_of_isRef`): the
component exists so an engine row's `q` can name it. -/
def Obs.zeroNorm (q : Obs) (a : Int) : Int :=
  match q.zeros with
  | .exact => a
  | .canon => fp64.canon a

/-- Two integers of column `col` equal up to `q`: a double's codes up to
zeros and NaNs, or within the tolerance (which ignores the sign of a zero and
a NaN's payload), a timestamp's truncated to `q`'s unit, anything else
exactly. Decimals are integers at their column's scale, one per column in
the model, so `decimals := .value` relates what `.exact` does. -/
def IntEquiv (q : Obs) (ctx : ObsCtx) (col : Nat) (a b : Int) : Prop :=
  match ctx.kind col with
  | .double => match q.floats with
    | .exact => q.zeroNorm a = q.zeroNorm b
    | .within n => ctx.near n col (fp64.canon a) (fp64.canon b)
  | .timestamp => match q.times with
    | .exact => a = b
    | .truncated u => u.trunc a = u.trunc b
  | .string | .decimal | .other => a = b

/-- Two strings equal at the level `s`. -/
def StrEquivAt (s : StringObs) (ctx : ObsCtx) (a b : String) : Prop :=
  match s with
  | .exact => a = b
  | .nfc => ctx.strEq .nfc a b
  | .casefold => ctx.strEq .casefold a b

/-- How `q` observes the strings of column `col`: as it says in a string
column, exactly elsewhere. -/
def Obs.stringsAt (q : Obs) (ctx : ObsCtx) (col : Nat) : StringObs :=
  if ctx.kind col = .string then q.strings else .exact

/-- Two strings of column `col` equal up to `q`. -/
def StrEquiv (q : Obs) (ctx : ObsCtx) (col : Nat) (a b : String) : Prop :=
  StrEquivAt (q.stringsAt ctx col) ctx a b

theorem Obs.stringsAt_of_ne {q : Obs} {ctx : ObsCtx} {col : Nat}
    (h : q.stringsAt ctx col ≠ .exact) : q.stringsAt ctx col = q.strings := by
  unfold Obs.stringsAt at *; split at h
  · next hk => simp only [hk, ite_true]
  · exact absurd rfl h

theorem Obs.stringsAt_rank {q' q : Obs} {ctx : ObsCtx} {col : Nat}
    (h : q'.strings.rank ≤ q.strings.rank) :
    (q'.stringsAt ctx col).rank ≤ (q.stringsAt ctx col).rank := by
  unfold Obs.stringsAt; split
  · exact h
  · exact Nat.le_refl _

mutual
/-- **Two values of column `col` equal up to `q`**: the same constructor,
integers by `IntEquiv`, strings by `StrEquiv`, lists elementwise, or as a
multiset where `q.elements` is. -/
def Value.Equiv (q : Obs) (ctx : ObsCtx) (col : Nat) : Value → Value → Prop
  | .null, .null => True
  | .bool a, .bool b => a = b
  -- A number by its integer, as the column's kind reads it (#923).
  | .int a, .int b | .float a, .float b | .date a, .date b | .ts a, .ts b | .tod a, .tod b =>
    IntEquiv q ctx col a b
  | .dec s a, .dec t b => s = t ∧ IntEquiv q ctx col a b
  | .str a, .str b => StrEquiv q ctx col a b
  | .list as, .list bs | .struct as, .struct bs => match q.elements with
    | .sequence => Value.EquivList q ctx col as bs
    | .multiset => ∃ cs, Value.EquivList q ctx col as cs ∧ cs.Perm bs
  | _, _ => False

/-- Lists of values of column `col`, elementwise. -/
def Value.EquivList (q : Obs) (ctx : ObsCtx) (col : Nat) : List Value → List Value → Prop
  | [], [] => True
  | a :: as, b :: bs => Value.Equiv q ctx col a b ∧ Value.EquivList q ctx col as bs
  | _, _ => False
end

theorem Value.equivList_iff {q : Obs} {ctx : ObsCtx} {col : Nat} :
    ∀ {as bs : List Value}, Value.EquivList q ctx col as bs ↔ Forall2 (Value.Equiv q ctx col) as bs
  | [], [] => by simp only [Value.EquivList, true_iff]; exact .nil
  | [], _ :: _ => by simp only [Value.EquivList, false_iff]; intro h; cases h
  | _ :: _, [] => by simp only [Value.EquivList, false_iff]; intro h; cases h
  | _ :: _, _ :: _ => by
    simp only [Value.EquivList]
    exact ⟨fun ⟨h, t⟩ => .cons h (equivList_iff.1 t), fun h => by cases h with
      | cons h t => exact ⟨h, equivList_iff.2 t⟩⟩

/-- What reflexivity needs of the context at `q`: its tolerance and its
string equality reflexive where `q` reads them. -/
def ObsCtx.ReflAt (ctx : ObsCtx) (q : Obs) : Prop :=
  (∀ n, q.floats = .within n → ∀ c a, ctx.near n c a a) ∧
    (∀ s, q.strings = s → s ≠ .exact → ∀ a, ctx.strEq s a a)

theorem ObsCtx.WF.reflAt {ctx : ObsCtx} (h : ctx.WF) (q : Obs) : ctx.ReflAt q :=
  ⟨fun n _ => h.near_refl n, fun s _ _ => h.str_refl s⟩

theorem ObsCtx.reflAt_exact (ctx : ObsCtx) : ctx.ReflAt Obs.exact :=
  ⟨fun _ h => (nomatch h), fun _ h hne => absurd h.symm hne⟩

section
variable {q : Obs} {ctx : ObsCtx} {col : Nat}

theorem IntEquiv.refl (h : ctx.ReflAt q) (a : Int) : IntEquiv q ctx col a a := by
  unfold IntEquiv
  cases ctx.kind col <;> simp only
  · cases hf : q.floats <;> simp only
    · exact h.1 _ hf _ _
  · cases q.times <;> simp only

theorem StrEquiv.refl (h : ctx.ReflAt q) (a : String) : StrEquiv q ctx col a a := by
  unfold StrEquiv
  cases hs : q.stringsAt ctx col <;> simp only [StrEquivAt]
  all_goals exact h.2 _ ((Obs.stringsAt_of_ne (by simp [hs])).symm.trans hs) (by decide) a

mutual
theorem Value.Equiv.refl (h : ctx.ReflAt q) : ∀ v, Value.Equiv q ctx col v v
  | .null => trivial
  | .bool _ => rfl
  | .int a | .float a | .date a | .ts a | .tod a => IntEquiv.refl h a
  | .dec _ a => ⟨rfl, IntEquiv.refl h a⟩
  | .str a => StrEquiv.refl h a
  | .list as | .struct as => by
    unfold Value.Equiv
    split
    · exact Value.EquivList.refl h as
    · exact ⟨as, Value.EquivList.refl h as, .refl _⟩

theorem Value.EquivList.refl (h : ctx.ReflAt q) : ∀ vs, Value.EquivList q ctx col vs vs
  | [] => trivial
  | v :: vs => ⟨Value.Equiv.refl h v, Value.EquivList.refl h vs⟩
end

theorem IntEquiv.symm (h : ctx.WF) {a b : Int} (e : IntEquiv q ctx col a b) :
    IntEquiv q ctx col b a := by
  unfold IntEquiv at *
  cases hc3 : ctx.kind col <;> simp only [hc3] at e ⊢
  · cases hc4 : q.floats <;> simp only [hc4] at e ⊢
    · exact e.symm
    · exact h.near_symm _ _ _ _ e
  · cases hc5 : q.times <;> simp only [hc5] at e ⊢ <;> exact e.symm
  all_goals exact e.symm

theorem StrEquiv.symm (h : ctx.WF) {a b : String} (e : StrEquiv q ctx col a b) :
    StrEquiv q ctx col b a := by
  unfold StrEquiv StrEquivAt at *
  cases hc6 : q.stringsAt ctx col <;> simp only [hc6] at e ⊢
  · exact e.symm
  all_goals exact h.str_symm _ _ _ e

mutual
theorem Value.Equiv.symm (h : ctx.WF) : ∀ a b, Value.Equiv q ctx col a b → Value.Equiv q ctx col b a
  | .null, b, e => by cases b <;> first | trivial | exact e.elim
  | .bool _, b, e => by cases b <;> first | exact e.elim | exact Eq.symm e
  | .int _, b, e | .float _, b, e | .date _, b, e | .ts _, b, e | .tod _, b, e => by
    cases b <;> first | exact e.elim | exact IntEquiv.symm h e
  | .dec _ _, b, e => by cases b <;> first | exact e.elim | exact ⟨e.1.symm, IntEquiv.symm h e.2⟩
  | .str _, b, e => by cases b <;> first | exact e.elim | exact StrEquiv.symm h e
  | .list as, b, e | .struct as, b, e => by
    cases b <;> try exact e.elim
    all_goals
      rename_i bs
      unfold Value.Equiv at e ⊢
      cases hl : q.elements <;> simp only [hl] at e ⊢
      · exact Value.EquivList.symm h as bs e
      · obtain ⟨cs, hl, hp⟩ := e
        obtain ⟨ds, hd, hf⟩ :=
          Forall2.perm hp (Value.equivList_iff.1 (Value.EquivList.symm h as cs hl))
        exact ⟨ds, Value.equivList_iff.2 hf, hd.symm⟩

theorem Value.EquivList.symm (h : ctx.WF) :
    ∀ as bs, Value.EquivList q ctx col as bs → Value.EquivList q ctx col bs as
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨e, t⟩ => ⟨Value.Equiv.symm h a b e, Value.EquivList.symm h as bs t⟩
  | [], _ :: _, e | _ :: _, [], e => e.elim
end

end

section
variable {q : Obs} {c₁ c₂ c₃ : ObsCtx} {col : Nat}

theorem IntEquiv.trans (h : ObsCtx.Comp c₁ c₂ c₃) {a b d : Int} (e₁ : IntEquiv q c₁ col a b)
    (e₂ : IntEquiv q c₂ col b d) : IntEquiv q c₃ col a d := by
  unfold IntEquiv at *
  rw [h.kind₁] at e₁; rw [h.kind₂] at e₂
  cases hc7 : c₃.kind col <;> simp only [hc7] at e₁ e₂ ⊢
  · cases hc8 : q.floats <;> simp only [hc8] at e₁ e₂ ⊢
    · exact e₁.trans e₂
    · exact h.near _ _ _ _ _ e₁ e₂
  · cases hc9 : q.times <;> simp only [hc9] at e₁ e₂ ⊢ <;> exact e₁.trans e₂
  all_goals exact e₁.trans e₂

theorem StrEquiv.trans (h : ObsCtx.Comp c₁ c₂ c₃) {a b d : String} (e₁ : StrEquiv q c₁ col a b)
    (e₂ : StrEquiv q c₂ col b d) : StrEquiv q c₃ col a d := by
  unfold StrEquiv Obs.stringsAt at *
  rw [h.kind₁] at e₁; rw [h.kind₂] at e₂
  generalize (if c₃.kind col = .string then q.strings else .exact) = s at *
  unfold StrEquivAt at *
  cases hc10 : s <;> simp only [hc10] at e₁ e₂ ⊢
  · exact e₁.trans e₂
  all_goals exact h.str _ _ _ _ e₁ e₂

mutual
theorem Value.Equiv.trans (h : ObsCtx.Comp c₁ c₂ c₃) :
    ∀ a b d, Value.Equiv q c₁ col a b → Value.Equiv q c₂ col b d → Value.Equiv q c₃ col a d
  | .null, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    cases d <;> first | exact e₂.elim | trivial
  | .bool _, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    cases d <;> first | exact e₂.elim | exact Eq.trans e₁ e₂
  | .int _, b, d, e₁, e₂ | .float _, b, d, e₁, e₂ | .date _, b, d, e₁, e₂ | .ts _, b, d, e₁, e₂
  | .tod _, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    all_goals cases d <;> first | exact e₂.elim | exact IntEquiv.trans h e₁ e₂
  | .dec _ _, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    cases d <;> first | exact e₂.elim | exact ⟨e₁.1.trans e₂.1, IntEquiv.trans h e₁.2 e₂.2⟩
  | .str _, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    cases d <;> first | exact e₂.elim | exact StrEquiv.trans h e₁ e₂
  | .list as, b, d, e₁, e₂ | .struct as, b, d, e₁, e₂ => by
    cases b <;> try exact e₁.elim
    all_goals cases d <;> try exact e₂.elim
    all_goals
      rename_i bs ds
      unfold Value.Equiv at e₁ e₂ ⊢
      cases hc11 : q.elements <;> simp only [hc11] at e₁ e₂ ⊢
      · exact Value.EquivList.trans h as bs ds e₁ e₂
      · obtain ⟨cs, h₁, p₁⟩ := e₁
        obtain ⟨cs', h₂, p₂⟩ := e₂
        -- `as R cs ~ bs R cs' ~ ds`: move `cs ~ bs` past `bs R cs'`.
        obtain ⟨es, pe, fe⟩ := Forall2.perm p₁.symm (Value.equivList_iff.1 h₂)
        have := Value.EquivList.trans h as cs es h₁ (Value.equivList_iff.2 fe)
        exact ⟨es, this, pe.symm.trans p₂⟩

theorem Value.EquivList.trans (h : ObsCtx.Comp c₁ c₂ c₃) :
    ∀ as bs ds, Value.EquivList q c₁ col as bs → Value.EquivList q c₂ col bs ds →
      Value.EquivList q c₃ col as ds
  | [], [], [], _, _ => trivial
  | a :: as, b :: bs, d :: ds, ⟨e₁, t₁⟩, ⟨e₂, t₂⟩ =>
    ⟨Value.Equiv.trans h a b d e₁ e₂, Value.EquivList.trans h as bs ds t₁ t₂⟩
  | [], [], _ :: _, _, e | _ :: _, _ :: _, [], _, e => e.elim
  | [], _ :: _, _, e, _ | _ :: _, [], _, e, _ => e.elim
end

end

/-! ## Refinement: `Obs.le` gives coarser equalities -/

theorem Obs.le_parts {q' q : Obs} (h : q'.le q = true) :
    q'.rows.le q.rows = true ∧ q'.elements.le q.elements = true ∧ q'.floats.le q.floats = true ∧
      q'.zeros.le q.zeros = true ∧ q'.times.le q.times = true ∧
      q'.strings.rank ≤ q.strings.rank := by
  simp only [Obs.le, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

section
variable {q' q : Obs} {ctx : ObsCtx} {col : Nat}

theorem IntEquiv.mono (hc : ctx.WF) (h : q'.le q = true) {a b : Int} (e : IntEquiv q' ctx col a b) :
    IntEquiv q ctx col a b := by
  obtain ⟨-, -, hf, hz, ht, -⟩ := Obs.le_parts h
  unfold IntEquiv at *
  cases hc12 : ctx.kind col <;> simp only [hc12] at e ⊢
  · have hcz : ∀ x, fp64.canon (q'.zeroNorm x) = fp64.canon x := fun x => by
      unfold Obs.zeroNorm; split
      · rfl
      · exact fp64.canon_idem x
    cases hq' : q'.floats <;> cases hq : q.floats <;>
      simp only [hq', hq, FloatObs.le, beq_iff_eq, reduceCtorEq] at hf e ⊢
    · unfold Obs.zeroNorm at *
      cases hz' : q'.zeros <;> cases hz'' : q.zeros <;>
        simp only [hz', hz'', ZeroNaNObs.le, reduceCtorEq] at hz e ⊢
      · exact e
      · exact congrArg _ e
      · exact e
    · rw [← hcz a, ← hcz b, e]; exact hc.near_refl _ _ _
    · subst hf; exact e
  · cases hq' : q'.times <;> cases hq : q.times <;>
      simp only [hq', hq, TimeObs.le, decide_eq_true_eq, reduceCtorEq] at ht e ⊢
    all_goals first | exact e | exact congrArg _ e |
      rw [← TimeUnit.trunc_trunc ht a, ← TimeUnit.trunc_trunc ht b, e]
  all_goals exact e

theorem StrEquiv.mono (hc : ctx.WF) (h : q'.le q = true) {a b : String}
    (e : StrEquiv q' ctx col a b) : StrEquiv q ctx col a b := by
  obtain ⟨-, -, -, -, -, hs⟩ := Obs.le_parts h
  have hs := Obs.stringsAt_rank (ctx := ctx) (col := col) hs
  unfold StrEquiv StrEquivAt at *
  cases hq' : q'.stringsAt ctx col <;> cases hq : q.stringsAt ctx col <;>
    simp only [hq', hq, StringObs.rank] at hs e ⊢ <;> try omega
  all_goals first | exact e | (subst e; exact hc.str_refl _ _) | exact hc.str_mono _ _ e

mutual
theorem Value.Equiv.mono (hc : ctx.WF) (h : q'.le q = true) :
    ∀ a b, Value.Equiv q' ctx col a b → Value.Equiv q ctx col a b
  | .null, b, e => by cases b <;> first | trivial | exact e.elim
  | .bool _, b, e => by cases b <;> first | exact e.elim | exact e
  | .int _, b, e | .float _, b, e | .date _, b, e | .ts _, b, e | .tod _, b, e => by
    cases b <;> first | exact e.elim | exact IntEquiv.mono hc h e
  | .dec _ _, b, e => by cases b <;> first | exact e.elim | exact ⟨e.1, IntEquiv.mono hc h e.2⟩
  | .str _, b, e => by cases b <;> first | exact e.elim | exact StrEquiv.mono hc h e
  | .list as, b, e | .struct as, b, e => by
    cases b <;> try exact e.elim
    all_goals
      rename_i bs
      obtain ⟨-, hl, -⟩ := Obs.le_parts h
      unfold Value.Equiv at e ⊢
      cases hq' : q'.elements <;> cases hq : q.elements <;>
        simp only [hq', hq, ElemsObs.le, reduceCtorEq] at hl e ⊢
      · exact Value.EquivList.mono hc h as bs e
      · exact ⟨bs, Value.EquivList.mono hc h as bs e, .refl _⟩
      · obtain ⟨cs, hc', hp⟩ := e
        exact ⟨cs, Value.EquivList.mono hc h as cs hc', hp⟩

theorem Value.EquivList.mono (hc : ctx.WF) (h : q'.le q = true) :
    ∀ as bs, Value.EquivList q' ctx col as bs → Value.EquivList q ctx col as bs
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨e, t⟩ => ⟨Value.Equiv.mono hc h a b e, Value.EquivList.mono hc h as bs t⟩
  | [], _ :: _, e | _ :: _, [], e => e.elim
end

end

/-! ## Exact observations are equality -/

/-- `q` tells every two different values apart: its components on values
are all exact (its rows and errors may be anything). -/
def Obs.valExact (q : Obs) : Bool :=
  q.elements == .sequence && q.floats == .exact && q.zeros == .exact && q.times == .exact &&
    q.strings == .exact

theorem Obs.valExact_iff {q : Obs} : q.valExact = true ↔
    q.elements = .sequence ∧ q.floats = .exact ∧ q.zeros = .exact ∧ q.times = .exact ∧
      q.strings = .exact := by
  simp only [Obs.valExact, Bool.and_eq_true, beq_iff_eq, and_assoc]

section
variable {q : Obs} {ctx : ObsCtx} {col : Nat}

theorem ObsCtx.reflAt_of_valExact (ctx : ObsCtx) (hq : q.valExact = true) : ctx.ReflAt q := by
  obtain ⟨-, hf, -, -, hs⟩ := Obs.valExact_iff.1 hq
  exact ⟨fun _ h => (by rw [hf] at h; cases h), fun _ h hne => absurd (h.symm.trans hs) hne⟩

mutual
theorem Value.Equiv.eq_of_valExact (hq : q.valExact = true) :
    ∀ a b, Value.Equiv q ctx col a b → a = b
  | .null, b, e => by cases b <;> first | rfl | exact e.elim
  | .bool _, b, e => by cases b <;> first | exact e.elim | exact congrArg _ e
  | .int _, b, e | .float _, b, e | .date _, b, e | .ts _, b, e | .tod _, b, e => by
    cases b <;> try exact e.elim
    all_goals
      obtain ⟨-, hf, hz, ht, -⟩ := Obs.valExact_iff.1 hq
      change IntEquiv q ctx col _ _ at e
      unfold IntEquiv at e
      cases hk : ctx.kind col <;> simp only [hk, hf, Obs.zeroNorm, hz, ht] at e <;> exact congrArg _ e
  | .dec _ _, b, e => by
    cases b <;> try exact e.elim
    obtain ⟨-, hf, hz, ht, -⟩ := Obs.valExact_iff.1 hq
    obtain ⟨hs, e⟩ := e
    unfold IntEquiv at e
    cases hk : ctx.kind col <;> simp only [hk, hf, Obs.zeroNorm, hz, ht] at e <;> rw [hs, e]
  | .str _, b, e => by
    cases b <;> try exact e.elim
    obtain ⟨-, -, -, -, hs⟩ := Obs.valExact_iff.1 hq
    change StrEquiv q ctx col _ _ at e
    unfold StrEquiv StrEquivAt Obs.stringsAt at e; simp only [hs, ite_self] at e; exact congrArg _ e
  | .list as, b, e | .struct as, b, e => by
    cases b <;> try exact e.elim
    all_goals
      rename_i bs
      obtain ⟨hl, -⟩ := Obs.valExact_iff.1 hq
      unfold Value.Equiv at e; simp only [hl] at e
      exact congrArg _ (Value.EquivList.eq_of_valExact hq as bs e)

theorem Value.EquivList.eq_of_valExact (hq : q.valExact = true) :
    ∀ as bs, Value.EquivList q ctx col as bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, ⟨e, t⟩ => by
    rw [Value.Equiv.eq_of_valExact hq a b e, Value.EquivList.eq_of_valExact hq as bs t]
  | [], _ :: _, e | _ :: _, [], e => e.elim
end

theorem Value.equiv_iff_eq (hq : q.valExact = true) {a b : Value} :
    Value.Equiv q ctx col a b ↔ a = b :=
  ⟨Value.Equiv.eq_of_valExact hq a b, fun e => e ▸ Value.Equiv.refl (ctx.reflAt_of_valExact hq) a⟩

end

/-! ## Rows -/

/-- Rows from column `i` on, by position. -/
def Row.EquivFrom (q : Obs) (ctx : ObsCtx) : Nat → Row → Row → Prop
  | _, [], [] => True
  | i, a :: as, b :: bs => Value.Equiv q ctx i a b ∧ Row.EquivFrom q ctx (i + 1) as bs
  | _, _, _ => False

/-- **Two rows equal up to `q`**: the same width, each column's values by
`Value.Equiv`. -/
def Row.Equiv (q : Obs) (ctx : ObsCtx) : Row → Row → Prop := Row.EquivFrom q ctx 0

/-- Two rows agree, up to `q`, on the `ORDER BY` keys of `ctx`. -/
def Row.KeyEquiv (q : Obs) (ctx : ObsCtx) (r r' : Row) : Prop :=
  ∀ k ∈ ctx.keys, Value.Equiv q ctx k.col (r.getD k.col .null) (r'.getD k.col .null)

section
variable {q q' : Obs} {ctx c₁ c₂ c₃ : ObsCtx}

theorem Row.EquivFrom.refl (h : ctx.ReflAt q) : ∀ i r, Row.EquivFrom q ctx i r r
  | _, [] => trivial
  | _, a :: as => ⟨Value.Equiv.refl h a, Row.EquivFrom.refl h _ as⟩

theorem Row.EquivFrom.symm (h : ctx.WF) :
    ∀ i r r', Row.EquivFrom q ctx i r r' → Row.EquivFrom q ctx i r' r
  | _, [], [], _ => trivial
  | _, a :: as, b :: bs, ⟨e, t⟩ => ⟨Value.Equiv.symm h a b e, Row.EquivFrom.symm h _ as bs t⟩
  | _, [], _ :: _, e | _, _ :: _, [], e => e.elim

theorem Row.EquivFrom.trans (h : ObsCtx.Comp c₁ c₂ c₃) :
    ∀ i r r' r'', Row.EquivFrom q c₁ i r r' → Row.EquivFrom q c₂ i r' r'' → Row.EquivFrom q c₃ i r r''
  | _, [], [], [], _, _ => trivial
  | _, a :: as, b :: bs, d :: ds, ⟨e₁, t₁⟩, ⟨e₂, t₂⟩ =>
    ⟨Value.Equiv.trans h a b d e₁ e₂, Row.EquivFrom.trans h _ as bs ds t₁ t₂⟩
  | _, [], [], _ :: _, _, e | _, _ :: _, _ :: _, [], _, e => e.elim
  | _, [], _ :: _, _, e, _ | _, _ :: _, [], _, e, _ => e.elim

theorem Row.EquivFrom.mono (hc : ctx.WF) (h : q'.le q = true) :
    ∀ i r r', Row.EquivFrom q' ctx i r r' → Row.EquivFrom q ctx i r r'
  | _, [], [], _ => trivial
  | _, a :: as, b :: bs, ⟨e, t⟩ => ⟨Value.Equiv.mono hc h a b e, Row.EquivFrom.mono hc h _ as bs t⟩
  | _, [], _ :: _, e | _, _ :: _, [], e => e.elim

theorem Row.EquivFrom.eq_of_valExact (hq : q.valExact = true) :
    ∀ i r r', Row.EquivFrom q ctx i r r' → r = r'
  | _, [], [], _ => rfl
  | _, a :: as, b :: bs, ⟨e, t⟩ => by
    rw [Value.Equiv.eq_of_valExact hq a b e, Row.EquivFrom.eq_of_valExact hq _ as bs t]
  | _, [], _ :: _, e | _, _ :: _, [], e => e.elim

/-- Equal rows agree on every column, out of range too (both `NULL`). -/
theorem Row.EquivFrom.getD : ∀ {i : Nat} {r r' : Row}, Row.EquivFrom q ctx i r r' →
    ∀ j, Value.Equiv q ctx (i + j) (r.getD j .null) (r'.getD j .null)
  | _, [], [], _, _ => trivial
  | i, a :: as, b :: bs, ⟨e, t⟩, j => by
    cases j with
    | zero => simpa using e
    | succ j =>
      have := Row.EquivFrom.getD t j
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
  | _, [], _ :: _, e, _ | _, _ :: _, [], e, _ => e.elim

theorem Row.Equiv.keyEquiv {r r' : Row} (h : Row.Equiv q ctx r r') : Row.KeyEquiv q ctx r r' :=
  fun k _ => by simpa using Row.EquivFrom.getD h k.col

end

/-! ## Relations -/

/-- **Two results equal up to `q`.** Rows as a sequence: pairwise; as a
multiset: pairwise after a permutation; up to the order of ties: as a
multiset, with the `ORDER BY` keys of `ctx` the same, row by row, so only
rows that tie trade places. Errors are not results: `q.errors` is about
raising, and `Rel.Raises` speaks of it. -/
def Relation.Equiv (q : Obs) (ctx : ObsCtx) (a b : Relation) : Prop :=
  match q.rows with
  | .sequence => Forall2 (Row.Equiv q ctx) a b
  | .tiesPermuted =>
    (∃ p, Forall2 (Row.Equiv q ctx) a p ∧ p.Perm b) ∧ Forall2 (Row.KeyEquiv q ctx) a b
  | .multiset => ∃ p, Forall2 (Row.Equiv q ctx) a p ∧ p.Perm b

section
variable {q q' : Obs} {ctx c₁ c₂ c₃ : ObsCtx}

theorem Relation.Equiv.refl' (h : ctx.ReflAt q) (a : Relation) : Relation.Equiv q ctx a a := by
  have hr : Forall2 (Row.Equiv q ctx) a a := Forall2.refl fun r _ => Row.EquivFrom.refl h 0 r
  unfold Relation.Equiv
  split
  · exact hr
  · exact ⟨⟨a, hr, .refl _⟩, Forall2.refl fun r _ k _ => Value.Equiv.refl h _⟩
  · exact ⟨a, hr, .refl _⟩

theorem Relation.Equiv.refl (h : ctx.WF) (a : Relation) : Relation.Equiv q ctx a a :=
  Relation.Equiv.refl' (h.reflAt q) a

theorem Relation.Equiv.symm (h : ctx.WF) {a b : Relation} (e : Relation.Equiv q ctx a b) :
    Relation.Equiv q ctx b a := by
  have hs : ∀ r r', Row.Equiv q ctx r r' → Row.Equiv q ctx r' r :=
    fun r r' => Row.EquivFrom.symm h 0 r r'
  have hm : ∀ {a b : Relation}, (∃ p, Forall2 (Row.Equiv q ctx) a p ∧ p.Perm b) →
      ∃ p, Forall2 (Row.Equiv q ctx) b p ∧ p.Perm a := fun ⟨p, hf, hp⟩ => by
    obtain ⟨m, hm, hf'⟩ := Forall2.perm hp (hf.flip.imp fun x y e => hs y x e)
    exact ⟨m, hf', hm.symm⟩
  unfold Relation.Equiv at *
  cases hc13 : q.rows <;> simp only [hc13] at e ⊢
  · exact e.flip.imp fun x y e => hs y x e
  · exact ⟨hm e.1, e.2.flip.imp fun x y e k hk => Value.Equiv.symm h _ _ (e k hk)⟩
  · exact hm e

theorem Relation.Equiv.trans (h : ObsCtx.Comp c₁ c₂ c₃) {a b d : Relation}
    (e₁ : Relation.Equiv q c₁ a b) (e₂ : Relation.Equiv q c₂ b d) : Relation.Equiv q c₃ a d := by
  have ht : ∀ r r' r'', Row.Equiv q c₁ r r' → Row.Equiv q c₂ r' r'' → Row.Equiv q c₃ r r'' :=
    fun r r' r'' => Row.EquivFrom.trans h 0 r r' r''
  have hm : ∀ {a b d : Relation}, (∃ p, Forall2 (Row.Equiv q c₁) a p ∧ p.Perm b) →
      (∃ p, Forall2 (Row.Equiv q c₂) b p ∧ p.Perm d) →
      ∃ p, Forall2 (Row.Equiv q c₃) a p ∧ p.Perm d := fun ⟨p, f₁, p₁⟩ ⟨p', f₂, p₂⟩ => by
    -- `a R p ~ b R p' ~ d`: move `p ~ b` past `b R p'`.
    obtain ⟨m, hm, fm⟩ := Forall2.perm p₁.symm f₂
    exact ⟨m, Forall2.trans ht f₁ fm, hm.symm.trans p₂⟩
  unfold Relation.Equiv at *
  cases hc14 : q.rows <;> simp only [hc14] at e₁ e₂ ⊢
  · exact Forall2.trans ht e₁ e₂
  · refine ⟨hm e₁.1 e₂.1, Forall2.trans (fun x y z k₁ k₂ k hk => ?_) e₁.2 e₂.2⟩
    exact Value.Equiv.trans h _ _ _ (k₁ k (h.keys₁ ▸ hk)) (k₂ k (h.keys₂ ▸ hk))
  · exact hm e₁ e₂

/-- **`Obs.le` means what it says** (D18): equality up to a finer
observation is equality up to a coarser one. -/
theorem Relation.Equiv_mono (hc : ctx.WF) (h : q'.le q = true) {a b : Relation}
    (e : Relation.Equiv q' ctx a b) : Relation.Equiv q ctx a b := by
  obtain ⟨hr, -⟩ := Obs.le_parts h
  have hrow : ∀ r r', Row.Equiv q' ctx r r' → Row.Equiv q ctx r r' :=
    fun r r' => Row.EquivFrom.mono hc h 0 r r'
  have hm : ∀ {a b : Relation}, (∃ p, Forall2 (Row.Equiv q' ctx) a p ∧ p.Perm b) →
      ∃ p, Forall2 (Row.Equiv q ctx) a p ∧ p.Perm b :=
    fun ⟨p, f, hp⟩ => ⟨p, f.imp hrow, hp⟩
  unfold Relation.Equiv at *
  cases hq' : q'.rows <;> cases hq : q.rows <;>
    simp only [hq', hq, RowsObs.le, RowsObs.rank, decide_eq_true_eq] at hr e ⊢ <;> try omega
  · exact e.imp hrow
  · exact ⟨⟨b, e.imp hrow, .refl _⟩, e.imp fun r r' e => (hrow r r' e).keyEquiv⟩
  · exact ⟨b, e.imp hrow, .refl _⟩
  · exact ⟨hm e.1, e.2.imp fun _ _ e k hk => Value.Equiv.mono hc h _ _ (e k hk)⟩
  · exact hm e.1
  · exact hm e

/-- Rows equal up to a value-exact observation are equal. -/
theorem Row.equiv_iff_eq (hq : q.valExact = true) {r r' : Row} : Row.Equiv q ctx r r' ↔ r = r' :=
  ⟨Row.EquivFrom.eq_of_valExact hq 0 r r',
    fun e => e ▸ Row.EquivFrom.refl (ctx.reflAt_of_valExact hq) 0 r⟩

theorem forall2_rowEquiv_iff (hq : q.valExact = true) {a b : Relation} :
    Forall2 (Row.Equiv q ctx) a b ↔ a = b :=
  ⟨fun f => Forall2.eq (f.imp fun _ _ e => (Row.equiv_iff_eq hq).1 e),
    fun e => e ▸ Forall2.refl fun _ _ => (Row.equiv_iff_eq hq).2 rfl⟩

/-- **The identity observation is equality**, whatever the context. -/
theorem Relation.Equiv_exact {a b : Relation} : Relation.Equiv Obs.exact ctx a b ↔ a = b :=
  forall2_rowEquiv_iff rfl

/-- **Rows as a multiset, everything else exact, is `List.Perm`**: the old
`Rel.Refines`'s relation. -/
theorem Relation.Equiv_multiset_perm {a b : Relation} :
    Relation.Equiv { rows := .multiset } ctx a b ↔ a.Perm b := by
  show (∃ p, _ ∧ _) ↔ _
  constructor
  · rintro ⟨p, f, hp⟩; rw [(forall2_rowEquiv_iff rfl).1 f]; exact hp
  · intro hp; exact ⟨a, (forall2_rowEquiv_iff rfl).2 rfl, hp⟩

end

/-! ## Near: a tolerance in codes -/

/-- A per-column tolerance in codes, an ulp count (`none`: exact). -/
abbrev Tol := Nat → Option Nat

/-- Within `t` of each other in codes, or equal where `t` is `none`. -/
def Tol.near (t : Tol) (col : Nat) (a b : Int) : Prop :=
  match t col with
  | some e => (a - b).natAbs ≤ e
  | none => a = b

/-- Tolerances add columnwise; exact plus `e` is `e`. -/
def Tol.add (t₁ t₂ : Tol) : Tol := fun c =>
  match t₁ c, t₂ c with
  | some a, some b => some (a + b)
  | some a, none | none, some a => some a
  | none, none => none

/-- `t` at least as tight as `t'` on every column. -/
def Tol.le (t t' : Tol) : Prop := ∀ c, match t c, t' c with
  | none, _ => True
  | some a, some b => a ≤ b
  | some _, none => False

/-- The context of a tolerance: the double columns `kind` names, compared
within `t` (after making zeros and NaNs one), everything else exact. -/
def ObsCtx.ofTol (kind : Nat → ColKind) (t : Tol) : ObsCtx where
  kind := kind
  near := fun _ => t.near

/-- **`a` and `b` within `t` of each other**: rows as a multiset, each
double column within its tolerance in codes (the plan's bound, `"plan"`),
everything else exact. The metric of #929's tolerance composition. -/
def Relation.Near (kind : Nat → ColKind) (t : Tol) (a b : Relation) : Prop :=
  Relation.Equiv { rows := .multiset, floats := .within "plan" } (ObsCtx.ofTol kind t) a b

theorem ObsCtx.ofTol_wf (kind : Nat → ColKind) (t : Tol) : (ObsCtx.ofTol kind t).WF where
  near_refl _ c _ := by
    show t.near c _ _; unfold Tol.near; split <;> simp
  near_symm _ c a b h := by
    change t.near c a b at h; show t.near c b a
    unfold Tol.near at *
    cases ht : t c <;> simp only [ht] at h ⊢
    · exact h.symm
    · rw [← Int.natAbs_neg, Int.neg_sub]; exact h
  str_refl _ _ := rfl
  str_symm _ _ _ h := h.symm
  str_trans _ _ _ _ h₁ h₂ := h₁.trans h₂
  str_mono _ _ h := h

theorem Tol.near_add {t₁ t₂ : Tol} {c : Nat} {a b d : Int} (h₁ : t₁.near c a b) (h₂ : t₂.near c b d) :
    (t₁.add t₂).near c a d := by
  unfold Tol.near Tol.add at *
  revert h₁ h₂
  cases t₁ c <;> cases t₂ c <;> simp only <;> intro h₁ h₂ <;> omega

theorem Relation.Near.refl (kind : Nat → ColKind) (t : Tol) (a : Relation) :
    Relation.Near kind t a a :=
  Relation.Equiv.refl (ObsCtx.ofTol_wf kind t) a

theorem Relation.Near.symm {kind : Nat → ColKind} {t : Tol} {a b : Relation}
    (h : Relation.Near kind t a b) : Relation.Near kind t b a :=
  Relation.Equiv.symm (ObsCtx.ofTol_wf kind t) h

/-- **The triangle rule**: tolerances add along a chain of results. -/
theorem Relation.Near_add {kind : Nat → ColKind} {t₁ t₂ : Tol} {a b d : Relation}
    (h₁ : Relation.Near kind t₁ a b) (h₂ : Relation.Near kind t₂ b d) :
    Relation.Near kind (t₁.add t₂) a d :=
  Relation.Equiv.trans (c₁ := ObsCtx.ofTol kind t₁) (c₂ := ObsCtx.ofTol kind t₂)
    (c₃ := ObsCtx.ofTol kind (t₁.add t₂))
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ h₁ h₂ => Tol.near_add h₁ h₂,
      fun _ _ _ _ (h₁ : _ = _) h₂ => h₁.trans h₂⟩ h₁ h₂

/-- A tighter tolerance gives a closer pair. -/
theorem Relation.Near_mono {kind : Nat → ColKind} {t t' : Tol} (ht : t.le t') {a b : Relation}
    (h : Relation.Near kind t a b) : Relation.Near kind t' a b := by
  refine Relation.Equiv.trans (c₁ := ObsCtx.ofTol kind t) (c₂ := ObsCtx.ofTol kind fun _ => none)
    (c₃ := ObsCtx.ofTol kind t')
    ⟨rfl, rfl, rfl, rfl, fun _ c x y z h₁ h₂ => ?_, fun _ _ _ _ (h₁ : _ = _) h₂ => h₁.trans h₂⟩ h
    (Relation.Equiv.refl (ObsCtx.ofTol_wf kind _) b)
  change t.near c x y at h₁; change Tol.near (fun _ => none) c y z at h₂; show t'.near c x z
  unfold Tol.near at *; simp only at h₂; subst h₂
  have hl := ht c
  cases h1 : t c <;> cases h2 : t' c <;> simp only [h1, h2] at h₁ hl ⊢
  all_goals first | exact h₁ | (subst h₁; simp) | omega

/-! ## Examples -/

/-- Two rows in either order: equal as a multiset, not as a sequence. -/
example : Relation.Equiv { rows := .multiset } {} [[.int 1], [.int 2]] [[.int 2], [.int 1]] :=
  Relation.Equiv_multiset_perm.2 (.swap _ _ _)

example : ¬ Relation.Equiv {} {} [[.int 1], [.int 2]] [[.int 2], [.int 1]] := by
  rw [show ({} : Obs) = Obs.exact from rfl, Relation.Equiv_exact]; decide

/-- `-0.0` and `+0.0` in a double column: equal up to `.canon`, not exactly. -/
example : Value.Equiv { zeros := .canon } { kind := fun _ => .double } 0 (.int fp64.negZero) (.int 0) := by
  show fp64.canon fp64.negZero = fp64.canon 0
  rw [fp64.canon_negZero, fp64.canon_eq_self]
  have := fp64.negZero_eq; have := fp64.negNan_eq; omega

example : ¬ Value.Equiv {} { kind := fun _ => .double } 0 (.int fp64.negZero) (.int 0) := by
  show ¬ fp64.negZero = 0; have := fp64.negZero_eq; omega

/-- Two timestamps 400 µs apart in the same millisecond: equal up to
`.truncated .ms`, not up to `.truncated .us`. -/
example : Value.Equiv { times := .truncated .ms } { kind := fun _ => .timestamp } 0
    (.int 1_700_000_000_000_100) (.int 1_700_000_000_000_500) := by
  show Time.floorTo 1000 _ = Time.floorTo 1000 _; simp [Time.floorTo]

example : ¬ Value.Equiv { times := .truncated .us } { kind := fun _ => .timestamp } 0
    (.int 1_700_000_000_000_100) (.int 1_700_000_000_000_500) := by
  show ¬ Time.trunc .microsecond _ = Time.trunc .microsecond _; simp [Time.trunc]

end Substrait
