import Sverify.Core.Expr
import Sverify.Core.Dedup

/-!
# Orders on values and rows

The total preorders `ORDER BY`, window functions and `MIN`/`MAX` use:
`Value.le` on values, `SortKey.le` and `sortLe` on rows.
-/

namespace Substrait

/-! ## Total preorders -/

/-- `le` is a total preorder: transitive and total. -/
structure TotalPre {α : Type} (le : α → α → Bool) : Prop where
  trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  total : ∀ a b, (le a b || le b a) = true

theorem TotalPre.refl {α : Type} {le : α → α → Bool} (h : TotalPre le) (a : α) : le a a = true := by
  have := h.total a a; simpa using this

/-- Lexicographic combination: by `le₁`, ties broken by `le₂`. -/
def lexLe {α : Type} (le₁ le₂ : α → α → Bool) (a b : α) : Bool :=
  le₁ a b && (!le₁ b a || le₂ a b)

theorem TotalPre.lex {α : Type} {le₁ le₂ : α → α → Bool} (h₁ : TotalPre le₁) (h₂ : TotalPre le₂) :
    TotalPre (lexLe le₁ le₂) where
  trans a b c hab hbc := by
    simp only [lexLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
    refine ⟨h₁.trans a b c hab.1 hbc.1, ?_⟩
    rcases hab with ⟨hab, hba | hab₂⟩ <;> rcases hbc with ⟨hbc, hcb | hbc₂⟩
    · left; cases hca : le₁ c a
      · rfl
      · exact absurd (h₁.trans b c a hbc hca) (by simp [hba])
    · left; cases hca : le₁ c a
      · rfl
      · exact absurd (h₁.trans b c a hbc hca) (by simp [hba])
    · left; cases hca : le₁ c a
      · rfl
      · exact absurd (h₁.trans c a b hca hab) (by simp [hcb])
    · cases hca : le₁ c a
      · left; rfl
      · right; exact h₂.trans a b c hab₂ hbc₂
  total a b := by
    simp only [lexLe]
    have t₁ := h₁.total a b
    have t₂ := h₂.total a b
    cases hab : le₁ a b <;> cases hba : le₁ b a <;> simp_all

theorem lexLe_left {α : Type} {le₁ le₂ : α → α → Bool} {a b : α} (h : lexLe le₁ le₂ a b = true) :
    le₁ a b = true := by
  simp only [lexLe, Bool.and_eq_true] at h; exact h.1

/-- Mutual `lexLe` means mutual `le₁` and mutual `le₂`. -/
theorem lexLe_antisymm {α : Type} {le₁ le₂ : α → α → Bool} {a b : α}
    (hab : lexLe le₁ le₂ a b = true) (hba : lexLe le₁ le₂ b a = true) :
    le₁ a b = true ∧ le₁ b a = true ∧ le₂ a b = true ∧ le₂ b a = true := by
  simp only [lexLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab hba
  rcases hab with ⟨h₁, h₂ | h₂⟩
  · simp [hba.1] at h₂
  · rcases hba with ⟨h₃, h₄ | h₄⟩
    · simp [h₁] at h₄
    · exact ⟨h₁, h₃, h₂, h₄⟩

theorem TotalPre.comap {α β : Type} {le : α → α → Bool} (h : TotalPre le) (f : β → α) :
    TotalPre (fun a b => le (f a) (f b)) :=
  ⟨fun a b c => h.trans (f a) (f b) (f c), fun a b => h.total (f a) (f b)⟩

theorem TotalPre.flip {α : Type} {le : α → α → Bool} (h : TotalPre le) :
    TotalPre (fun a b => le b a) :=
  ⟨fun a b c hab hbc => h.trans c b a hbc hab, fun a b => h.total b a⟩

/-! ## Ordering values -/

def Value.tag : Value → Nat
  | .bool _ => 0 | .int _ => 1 | .float _ => 2 | .date _ => 3 | .ts _ => 4 | .tod _ => 5
  | .dec _ _ => 6 | .str _ => 7 | .list _ => 8 | .struct _ => 9 | .null => 10
/-- `Value.leRaw` on values that are not both lists or both structs. -/
def Value.leScalar : Value → Value → Bool
  | .bool a, .bool b => !a || b
  | .int a, .int b | .float a, .float b | .date a, .date b | .ts a, .ts b
  | .tod a, .tod b => decide (a ≤ b)
  -- One column has one scale; across scales, the scale first.
  | .dec s a, .dec t b => decide (s < t) || (decide (s = t) && decide (a ≤ b))
  | .str a, .str b => decide (a ≤ b)
  | a, b => decide (a.tag ≤ b.tag)
mutual
/-- A total order on values: each kind's own order (`false < true`, integers,
the raw float codes, dates and times numerically, decimals of one scale
numerically, strings by code point, which is UTF-8 byte order, lists and
structs lexicographically with a prefix first), kinds ordered as `Value.tag`
numbers them, NULL last. Within a column only one kind and NULL occur;
NULL's place only matters inside lists (`ORDER BY` places top-level NULLs
itself, and `MIN`/`MAX` skip them), where engines sort NULL elements last. -/
def Value.leRaw : Value → Value → Bool
  | .list as, .list bs | .struct as, .struct bs => Value.leListRaw as bs
  | a, b => Value.leScalar a b
  termination_by a b => sizeOf a + sizeOf b
/-- Lexicographic order on lists of values: the first element where they
differ decides, and a prefix comes first. -/
def Value.leListRaw : List Value → List Value → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Value.leRaw a b && (!Value.leRaw b a || Value.leListRaw as bs)
  termination_by as bs => sizeOf as + sizeOf bs
end
theorem Value.leRaw_def (a b : Value) : a.leRaw b = (match a, b with
    | .list as, .list bs | .struct as, .struct bs => Value.leListRaw as bs
    | a, b => Value.leScalar a b) := by
  cases a <;> cases b <;> rw [Value.leRaw] <;> simp

theorem Value.leListRaw_nil (bs : List Value) : Value.leListRaw [] bs = true := by
  cases bs <;> rw [Value.leListRaw]

theorem Value.leListRaw_cons_nil (a : Value) (as : List Value) : Value.leListRaw (a :: as) [] = false := by
  rw [Value.leListRaw]

theorem Value.leListRaw_cons (a b : Value) (as bs : List Value) :
    Value.leListRaw (a :: as) (b :: bs) = (a.leRaw b && (!b.leRaw a || Value.leListRaw as bs)) := by
  rw [Value.leListRaw]

mutual
theorem Value.leRaw_antisymm : ∀ {a b : Value}, a.leRaw b = true → b.leRaw a = true → a = b
  | .list as, .list bs, hab, hba => by
    simp only [Value.leRaw_def] at hab hba
    rw [Value.leListRaw_antisymm hab hba]
  | .struct as, .struct bs, hab, hba => by
    simp only [Value.leRaw_def] at hab hba
    rw [Value.leListRaw_antisymm hab hba]
  | .null, b, hab, hba | .bool _, b, hab, hba | .int _, b, hab, hba | .float _, b, hab, hba
  | .date _, b, hab, hba | .ts _, b, hab, hba | .tod _, b, hab, hba | .dec _ _, b, hab, hba
  | .str _, b, hab, hba | .list _, .null, hab, hba | .list _, .bool _, hab, hba
  | .list _, .int _, hab, hba | .list _, .float _, hab, hba | .list _, .date _, hab, hba
  | .list _, .ts _, hab, hba | .list _, .tod _, hab, hba | .list _, .dec _ _, hab, hba
  | .list _, .str _, hab, hba | .list _, .struct _, hab, hba | .struct _, .null, hab, hba
  | .struct _, .bool _, hab, hba | .struct _, .int _, hab, hba | .struct _, .float _, hab, hba
  | .struct _, .date _, hab, hba | .struct _, .ts _, hab, hba | .struct _, .tod _, hab, hba
  | .struct _, .dec _ _, hab, hba | .struct _, .str _, hab, hba | .struct _, .list _, hab, hba => by
    try cases b
    all_goals simp_all [Value.leRaw_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_antisymm hab hba
      | (rename_i x y; cases x <;> cases y <;> simp_all)
  termination_by a b => sizeOf a + sizeOf b

theorem Value.leListRaw_antisymm : ∀ {as bs : List Value},
    Value.leListRaw as bs = true → Value.leListRaw bs as = true → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h | _ :: _, [], h, _ => by simp [Value.leListRaw_cons_nil] at h
  | a :: as, b :: bs, hab, hba => by
    simp only [Value.leListRaw_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab hba
    have hb := Value.leRaw_antisymm hab.1 hba.1
    subst hb
    have h₁ : Value.leListRaw as bs = true := hab.2.resolve_left (by simp [hba.1])
    have h₂ : Value.leListRaw bs as = true := hba.2.resolve_left (by simp [hab.1])
    rw [Value.leListRaw_antisymm h₁ h₂]
  termination_by as bs => sizeOf as + sizeOf bs
end

mutual
theorem Value.leRaw_total : ∀ a b : Value, a.leRaw b = true ∨ b.leRaw a = true
  | .list as, .list bs | .struct as, .struct bs => by
    simp only [Value.leRaw_def]; exact Value.leListRaw_total as bs
  | .null, b | .bool _, b | .int _, b | .float _, b | .date _, b | .ts _, b | .tod _, b
  | .dec _ _, b | .str _, b | .list _, .null | .list _, .bool _ | .list _, .int _
  | .list _, .float _ | .list _, .date _ | .list _, .ts _ | .list _, .tod _ | .list _, .dec _ _
  | .list _, .str _ | .list _, .struct _ | .struct _, .null | .struct _, .bool _
  | .struct _, .int _ | .struct _, .float _ | .struct _, .date _ | .struct _, .ts _
  | .struct _, .tod _ | .struct _, .dec _ _ | .struct _, .str _ | .struct _, .list _ => by
    try cases b
    all_goals simp [Value.leRaw_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_total _ _
      | (rename_i x y; cases x <;> cases y <;> simp)
  termination_by a b => sizeOf a + sizeOf b

theorem Value.leListRaw_total : ∀ as bs : List Value,
    Value.leListRaw as bs = true ∨ Value.leListRaw bs as = true
  | [], _ => Or.inl (Value.leListRaw_nil _)
  | _ :: _, [] => Or.inr (Value.leListRaw_nil _)
  | a :: as, b :: bs => by
    simp only [Value.leListRaw_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    have := Value.leListRaw_total as bs
    rcases Value.leRaw_total a b with h | h <;> by_cases h' : (b.leRaw a = true) <;>
      by_cases h'' : (a.leRaw b = true) <;> simp_all
  termination_by as bs => sizeOf as + sizeOf bs
end

mutual
theorem Value.leRaw_trans : ∀ a b c : Value, a.leRaw b = true → b.leRaw c = true → a.leRaw c = true
  | .list as, .list bs, .list cs, hab, hbc | .struct as, .struct bs, .struct cs, hab, hbc => by
    simp only [Value.leRaw_def] at *
    exact Value.leListRaw_trans as bs cs hab hbc
  | .null, b, c, hab, hbc | .bool _, b, c, hab, hbc | .int _, b, c, hab, hbc
  | .float _, b, c, hab, hbc | .date _, b, c, hab, hbc | .ts _, b, c, hab, hbc
  | .tod _, b, c, hab, hbc | .dec _ _, b, c, hab, hbc | .str _, b, c, hab, hbc
  | .list _, .null, c, hab, hbc | .list _, .bool _, c, hab, hbc | .list _, .int _, c, hab, hbc
  | .list _, .float _, c, hab, hbc | .list _, .date _, c, hab, hbc | .list _, .ts _, c, hab, hbc
  | .list _, .tod _, c, hab, hbc | .list _, .dec _ _, c, hab, hbc | .list _, .str _, c, hab, hbc
  | .list _, .struct _, c, hab, hbc | .struct _, .null, c, hab, hbc
  | .struct _, .bool _, c, hab, hbc | .struct _, .int _, c, hab, hbc
  | .struct _, .float _, c, hab, hbc | .struct _, .date _, c, hab, hbc
  | .struct _, .ts _, c, hab, hbc | .struct _, .tod _, c, hab, hbc
  | .struct _, .dec _ _, c, hab, hbc | .struct _, .str _, c, hab, hbc
  | .struct _, .list _, c, hab, hbc | .list _, .list _, .null, hab, hbc
  | .list _, .list _, .bool _, hab, hbc | .list _, .list _, .int _, hab, hbc
  | .list _, .list _, .float _, hab, hbc | .list _, .list _, .date _, hab, hbc
  | .list _, .list _, .ts _, hab, hbc | .list _, .list _, .tod _, hab, hbc
  | .list _, .list _, .dec _ _, hab, hbc | .list _, .list _, .str _, hab, hbc
  | .list _, .list _, .struct _, hab, hbc | .struct _, .struct _, .null, hab, hbc
  | .struct _, .struct _, .bool _, hab, hbc | .struct _, .struct _, .int _, hab, hbc
  | .struct _, .struct _, .float _, hab, hbc | .struct _, .struct _, .date _, hab, hbc
  | .struct _, .struct _, .ts _, hab, hbc | .struct _, .struct _, .tod _, hab, hbc
  | .struct _, .struct _, .dec _ _, hab, hbc | .struct _, .struct _, .str _, hab, hbc
  | .struct _, .struct _, .list _, hab, hbc => by
    try cases b
    all_goals try cases c
    all_goals simp_all [Value.leRaw_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_trans hab hbc
      | (rename_i x y z; cases x <;> cases y <;> cases z <;> simp_all)
  termination_by a b c => sizeOf a + sizeOf b + sizeOf c

theorem Value.leListRaw_trans : ∀ as bs cs : List Value,
    Value.leListRaw as bs = true → Value.leListRaw bs cs = true → Value.leListRaw as cs = true
  | [], _, _, _, _ => Value.leListRaw_nil _
  | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], _, h => by simp [Value.leListRaw_cons_nil] at h
  | a :: as, b :: bs, c :: cs, hab, hbc => by
    simp only [Value.leListRaw_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
    have hac := Value.leRaw_trans a b c hab.1 hbc.1
    refine ⟨hac, ?_⟩
    by_cases hca : c.leRaw a = true
    · right
      have hba := Value.leRaw_trans b c a hbc.1 hca
      have hcb := Value.leRaw_trans c a b hca hab.1
      exact Value.leListRaw_trans as bs cs (hab.2.resolve_left (by simp [hba]))
        (hbc.2.resolve_left (by simp [hcb]))
    · left; simpa using hca
  termination_by as bs cs => sizeOf as + sizeOf bs + sizeOf cs
end

theorem Value.leRaw_totalPre : TotalPre Value.leRaw where
  trans := Value.leRaw_trans
  total a b := by rcases Value.leRaw_total a b with h | h <;> simp [h]

/-- The order `ORDER BY`, windows and `MIN`/`MAX` use: `Value.leRaw` on
canonical values. `ORDER BY` is an identity boundary (D31): `-0.0` ties with
`0.0`, and every NaN with the NaN, which sorts last. Tied rows take any order
(tie-order freedom, `Rel.OrderAllowed`). -/
def Value.le (a b : Value) : Bool := a.canonV.leRaw b.canonV

theorem Value.le_totalPre : TotalPre Value.le := Value.leRaw_totalPre.comap Value.canonV

theorem Value.le_total (a b : Value) : a.le b = true ∨ b.le a = true :=
  Value.leRaw_total a.canonV b.canonV

theorem Value.le_trans (a b c : Value) : a.le b = true → b.le c = true → a.le c = true :=
  Value.leRaw_trans a.canonV b.canonV c.canonV

/-- Values that sort both ways are equal up to `canonV`. -/
theorem Value.le_antisymm {a b : Value} (hab : a.le b = true) (hba : b.le a = true) :
    a.canonV = b.canonV :=
  Value.leRaw_antisymm hab hba

/-- `Value.le` on doubles compares canonical codes. -/
theorem Value.le_float (a b : Int) :
    (Value.float a).le (.float b) = decide (FloatCode.canon a ≤ FloatCode.canon b) := by
  simp only [Value.le, Value.canonV_float]
  rw [Value.leRaw_def]; rfl

theorem Value.leRaw_float (a b : Int) : (Value.float a).leRaw (.float b) = decide (a ≤ b) := by
  rw [Value.leRaw_def]; rfl

/-- `Value.le` reads values only up to `canonV`. -/
theorem Value.le_canon_right {a w w' : Value} (h : w.canonV = w'.canonV) : a.le w = a.le w' := by
  simp only [Value.le, h]

theorem Value.le_canon_left {a a' w : Value} (h : a.canonV = a'.canonV) : a.le w = a'.le w := by
  simp only [Value.le, h]

/-- `canonV` changes only doubles: a value canonical-equal to an integer is it. -/
theorem Value.eq_int_of_canonV {w : Value} {i : Int} (h : w.canonV = (Value.int i).canonV) :
    w = .int i := by
  cases w <;> simp_all [Value.canonV]

/-- `Value.le` with ties broken by the raw codes: a total order, so `-0.0`
comes right before `0.0`. `MIN`, `MAX` and the quantiles pick by it, which
keeps them independent of the order of their values; the reference leaves
the member of a tied class open (D31). -/
def Value.leT : Value → Value → Bool := lexLe Value.le Value.leRaw

theorem Value.leT_totalPre : TotalPre Value.leT := Value.le_totalPre.lex Value.leRaw_totalPre

/-- `Value.leT` of doubles: by canonical code, ties by raw code. -/
theorem Value.leT_float (a b : Int) : (Value.float a).leT (.float b) = true ↔
    FloatCode.canon a < FloatCode.canon b ∨ (FloatCode.canon a = FloatCode.canon b ∧ a ≤ b) := by
  simp only [Value.leT, lexLe, Value.le_float, Value.leRaw_float, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem Value.leT_antisymm {a b : Value} (hab : a.leT b = true) (hba : b.leT a = true) : a = b :=
  have h := lexLe_antisymm hab hba
  Value.leRaw_antisymm h.2.2.1 h.2.2.2

theorem Value.le_of_leT {a b : Value} (h : a.leT b = true) : a.le b = true := lexLe_left h

/-- `Value.le` reversed, ties broken by the raw codes as in `Value.leT`: `MAX`
picks by it, so a tied class gives its raw-least member, as `MIN` and
`DISTINCT` do. -/
def Value.geT : Value → Value → Bool := lexLe (fun a b => b.le a) Value.leRaw

theorem Value.geT_totalPre : TotalPre Value.geT := Value.le_totalPre.flip.lex Value.leRaw_totalPre

/-- `Value.geT` of doubles: by canonical code reversed, ties by raw code. -/
theorem Value.geT_float (a b : Int) : (Value.float a).geT (.float b) = true ↔
    FloatCode.canon b < FloatCode.canon a ∨ (FloatCode.canon a = FloatCode.canon b ∧ a ≤ b) := by
  simp only [Value.geT, lexLe, Value.le_float, Value.leRaw_float, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem Value.geT_antisymm {a b : Value} (hab : a.geT b = true) (hba : b.geT a = true) : a = b :=
  have h := lexLe_antisymm hab hba
  Value.leRaw_antisymm h.2.2.1 h.2.2.2

theorem Value.le_of_geT {a b : Value} (h : a.geT b = true) : b.le a = true :=
  lexLe_left (le₁ := fun (x y : Value) => y.le x) (le₂ := Value.leRaw) h

/-- One `ORDER BY` key: a column, ascending or descending, NULLs first or last. -/
structure SortKey where
  col : Nat
  desc : Bool := false
  nullsFirst : Bool := false
  /-- The plan left the NULL placement open (`SORT_DIRECTION_UNSPECIFIED`,
  D6): each profile picks one (`null_order`), the reference NULLs last (D8),
  whatever `nullsFirst` says. -/
  nullsOpen : Bool := false
  /-- `SORT_DIRECTION_CLUSTERED`: rows with equal keys adjacent, the groups in
  any order. `Rel.eval` sorts them in the key's direction, one such order. -/
  clustered : Bool := false
  deriving Repr, BEq, DecidableEq

/-- NULLs first: as the key states, last where it leaves it open. -/
def SortKey.firstNulls (k : SortKey) : Bool := k.nullsFirst && !k.nullsOpen

/-- Where NULLs go: before (`0`) or after (`1`) the other values. -/
def SortKey.nullRank (k : SortKey) : Value → Nat
  | .null => if k.firstNulls then 0 else 1
  | _ => if k.firstNulls then 1 else 0

def SortKey.valLe (k : SortKey) (a b : Value) : Bool :=
  if k.desc then b.le a else a.le b

def natLe (a b : Nat) : Bool := decide (a ≤ b)

theorem natLe_totalPre : TotalPre natLe :=
  ⟨fun a b c => by simp only [natLe, decide_eq_true_eq]; omega,
   fun a b => by simp only [natLe, Bool.or_eq_true, decide_eq_true_eq]; omega⟩

/-- Order rows by one key. -/
def SortKey.le (k : SortKey) : Row → Row → Bool :=
  lexLe (fun x y => natLe (k.nullRank (x.getD k.col .null)) (k.nullRank (y.getD k.col .null)))
    (fun x y => k.valLe (x.getD k.col .null) (y.getD k.col .null))

theorem SortKey.valLe_totalPre (k : SortKey) : TotalPre k.valLe := by
  unfold SortKey.valLe
  cases k.desc
  · exact Value.le_totalPre
  · exact Value.le_totalPre.flip

theorem SortKey.le_totalPre (k : SortKey) : TotalPre k.le :=
  (natLe_totalPre.comap _).lex (k.valLe_totalPre.comap fun x : Row => x.getD k.col .null)

/-- Order rows by a list of keys, lexicographically. -/
def sortLe : List SortKey → Row → Row → Bool
  | [] => fun _ _ => true
  | k :: ks => lexLe k.le (sortLe ks)

theorem sortLe_totalPre : ∀ ks, TotalPre (sortLe ks)
  | [] => ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | k :: ks => k.le_totalPre.lex (sortLe_totalPre ks)

/-! ## Orders a profile allows

A profile picks the NULL placement of an open key (`nf`), and the order of a
clustered key's groups: any total order of the values (`ValidCmp`), which
`Rel.eval` takes to be `Value.le`. -/

/-- NULLs before (`0`) or after (`1`) the other values, when `nf` puts them first. -/
def nullRankOf (nf : Bool) : Value → Nat
  | .null => if nf then 0 else 1
  | _ => if nf then 1 else 0

theorem nullRankOf_firstNulls (k : SortKey) : nullRankOf k.firstNulls = k.nullRank := by
  funext v; cases v <;> rfl

/-- A key's order on values, a clustered key's groups ordered by `cmp`. -/
def SortKey.valWith (k : SortKey) (cmp : Value → Value → Bool) (a b : Value) : Bool :=
  if k.clustered then (if k.desc then cmp b a else cmp a b) else k.valLe a b

theorem SortKey.valWith_le (k : SortKey) : k.valWith Value.le = k.valLe := by
  funext a b; unfold valWith valLe; cases k.clustered <;> cases k.desc <;> rfl

/-- Order rows by one key, NULLs first when `nf`. -/
def SortKey.leWith (cmp : Value → Value → Bool) (nf : Bool) (k : SortKey) : Row → Row → Bool :=
  lexLe (fun x y => natLe (nullRankOf nf (x.getD k.col .null)) (nullRankOf nf (y.getD k.col .null)))
    (fun x y => k.valWith cmp (x.getD k.col .null) (y.getD k.col .null))

/-- Order rows by keys with their NULL placements, lexicographically. -/
def sortLeWith (cmp : Value → Value → Bool) : List (SortKey × Bool) → Row → Row → Bool
  | [] => fun _ _ => true
  | (k, nf) :: ks => lexLe (k.leWith cmp nf) (sortLeWith cmp ks)

theorem sortLeWith_le : ∀ ks : List SortKey,
    sortLeWith Value.le (ks.map fun k => (k, k.firstNulls)) = sortLe ks
  | [] => rfl
  | k :: ks => by
    simp only [List.map_cons, sortLeWith, sortLe, sortLeWith_le ks, SortKey.leWith, SortKey.le,
      nullRankOf_firstNulls, SortKey.valWith_le]

/-- An order a clustered key's groups may take: total, and telling every
two values apart up to `canonV` (D31). -/
def ValidCmp (cmp : Value → Value → Bool) : Prop :=
  TotalPre cmp ∧ ∀ a b, cmp a b = true → cmp b a = true → a.canonV = b.canonV

theorem Value.le_validCmp : ValidCmp Value.le := ⟨Value.le_totalPre, fun _ _ => Value.le_antisymm⟩

/-- The orders the reference allows for `keys`: each key's NULL placement as
it states (last where open), each clustered key's groups in any order. -/
def SortAllowed (keys : List SortKey) (out : Relation) : Prop :=
  ∃ cmp, ValidCmp cmp ∧ out.Pairwise (sortLeWith cmp (keys.map fun k => (k, k.firstNulls)) · · = true)

theorem SortAllowed.of_sorted {keys : List SortKey} {out : Relation}
    (h : out.Pairwise (sortLe keys · · = true)) : SortAllowed keys out :=
  ⟨Value.le, Value.le_validCmp, by rw [sortLeWith_le]; exact h⟩

/-- Two numbers of one kind order by their integers (a decimal's scale is
part of its kind). -/
theorem Value.le_val (k : NumKind) {x y : Int} :
    (k.val x).le (k.val y) = true ↔ k.norm x ≤ k.norm y := by
  cases k <;> simp only [NumKind.val, Value.le, Value.canonV, Value.leRaw_def, Value.leScalar,
    NumKind.norm_float,
    NumKind.norm_int, NumKind.norm_date, NumKind.norm_ts, NumKind.norm_tod, NumKind.norm_dec,
    decide_eq_true_eq] <;> simp

theorem SortKey.le_val {k : SortKey} {x y : Row} {nk : NumKind} {u v : Int} (h : k.le y x = true)
    (hy : y.getD k.col .null = nk.val u) (hx : x.getD k.col .null = nk.val v) :
    if k.desc then nk.norm v ≤ nk.norm u else nk.norm u ≤ nk.norm v := by
  simp only [SortKey.le, lexLe, hy, hx, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have hr : k.nullRank (nk.val u) = k.nullRank (nk.val v) := by
    cases nk <;> simp [SortKey.nullRank, NumKind.val]
  rcases h with ⟨_, h | h⟩
  · simp [hr, natLe] at h
  · unfold SortKey.valLe at h
    cases hd : k.desc <;> simp_all [Value.le_val]

theorem SortKey.nullRank_of_ne_null (k : SortKey) {a : Value} (h : a ≠ .null) :
    k.nullRank a = if k.firstNulls then 1 else 0 := by
  cases a <;> first | exact absurd rfl h | rfl

/-- `SortKey.le_val` on the canonical values of the key (`RANGE` frames read
them, D31). -/
theorem SortKey.le_val_canon {k : SortKey} {x y : Row} {nk : NumKind} {u v : Int}
    (h : k.le y x = true) (hy : (y.getD k.col .null).canonV = nk.val u)
    (hx : (x.getD k.col .null).canonV = nk.val v) :
    if k.desc then v ≤ u else u ≤ v := by
  have hne : ∀ {a : Value} {i : Int}, a.canonV = nk.val i → a ≠ .null := fun he h0 => by
    rw [h0] at he; cases nk <;> simp [Value.canonV, NumKind.val] at he
  simp only [SortKey.le, lexLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rw [SortKey.nullRank_of_ne_null k (hne hy), SortKey.nullRank_of_ne_null k (hne hx)] at h
  rcases h with ⟨_, h | h⟩
  · simp [natLe] at h
  · unfold SortKey.valLe at h
    cases hd : k.desc <;> simp only [hd, Bool.false_eq_true, ↓reduceIte, Value.le, hy, hx] at h ⊢ <;>
      cases nk <;> simp_all [NumKind.val, Value.leRaw_def, Value.leScalar]

/-- Rows in sort order, by the first key: for non-NULL integers (and
timestamps, and float codes), ascending keys give `y ≤ x`. -/
theorem SortKey.le_int {k : SortKey} {x y : Row} {u v : Int} (h : k.le y x = true)
    (hy : y.getD k.col .null = .int u) (hx : x.getD k.col .null = .int v) :
    if k.desc then v ≤ u else u ≤ v := by
  simp only [SortKey.le, lexLe, hy, hx, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have hr : k.nullRank (.int u) = k.nullRank (.int v) := by simp [SortKey.nullRank]
  rcases h with ⟨_, h | h⟩
  · simp [hr, natLe] at h
  · unfold SortKey.valLe at h
    cases hd : k.desc <;> simp_all [Value.le, Value.canonV, Value.leRaw_def, Value.leScalar]

/-- Rows that sort both ways on a key agree on its column, up to `canonV`. -/
theorem SortKey.le_antisymm {k : SortKey} {x y : Row} (hxy : k.le x y = true) (hyx : k.le y x = true) :
    (x.getD k.col .null).canonV = (y.getD k.col .null).canonV := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := lexLe_antisymm hxy hyx
  simp only [natLe, decide_eq_true_eq] at h₁ h₂
  have hrank : k.nullRank (x.getD k.col .null) = k.nullRank (y.getD k.col .null) := by omega
  generalize x.getD k.col .null = a at *
  generalize y.getD k.col .null = b at *
  unfold SortKey.valLe at h₃ h₄
  cases hd : k.desc
  · simp only [hd] at h₃ h₄; exact Value.le_antisymm h₃ h₄
  · simp only [hd, ↓reduceIte] at h₃ h₄; exact Value.le_antisymm h₄ h₃

theorem sortLe_antisymm : ∀ {ks : List SortKey} {x y : Row},
    sortLe ks x y = true → sortLe ks y x = true →
      ks.map (fun k => (x.getD k.col .null).canonV) = ks.map (fun k => (y.getD k.col .null).canonV)
  | [], _, _, _, _ => rfl
  | k :: ks, _, _, hxy, hyx => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := lexLe_antisymm hxy hyx
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨SortKey.le_antisymm h₁ h₂, sortLe_antisymm h₃ h₄⟩


/-! ## Identity up to canonical codes

`DISTINCT`, `GROUP BY` and `COUNT(DISTINCT)` tell values and rows apart up to
`Value.canonV` (D31) and keep the raw-least member of each class
(`canonReps`). -/

theorem Value.leRaw_rawOrder : RawOrder Value.leRaw :=
  ⟨Value.leRaw_total, Value.leRaw_trans, fun _ _ => Value.leRaw_antisymm⟩

/-- A row with its doubles canonical. -/
def Row.canon (r : Row) : Row := r.map Value.canonV

/-- `v` is the one value of its class: no other value has its canonical
form. Values without doubles are (`Value.lone_of_ne`). -/
def Value.Lone (v : Value) : Prop := ∀ z : Value, z.canonV = v.canonV → z = v

theorem Value.lone_of_ne {v : Value} (hf : ∀ c, v ≠ .float c) (hl : ∀ vs, v ≠ .list vs)
    (hs : ∀ vs, v ≠ .struct vs) : v.Lone := by
  intro z hz
  have hv : v.canonV = v := by
    cases v with
    | float c => exact absurd rfl (hf c)
    | list vs => exact absurd rfl (hl vs)
    | struct vs => exact absurd rfl (hs vs)
    | _ => simp only [Value.canonV]
  rw [hv] at hz
  cases z with
  | float c => rw [Value.canonV_float] at hz; exact absurd hz.symm (hf _)
  | list vs => rw [Value.canonV_list] at hz; exact absurd hz.symm (hl _)
  | struct vs => rw [Value.canonV_struct] at hz; exact absurd hz.symm (hs _)
  | _ => simpa only [Value.canonV] using hz

theorem Row.length_of_canon {z r : Row} (h : z.canon = r.canon) : z.length = r.length := by
  simpa [Row.canon] using congrArg List.length h

/-- A column of rows equal up to canonical codes is equal up to them. -/
theorem getD_canonV_of_canon {a b : Row} (h : a.canon = b.canon) (c : Nat) :
    (a.getD c .null).canonV = (b.getD c .null).canonV := by
  have := congrArg (·[c]?) h
  simp only [Row.canon, List.getElem?_map] at this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases ha : a[c]? <;> cases hb : b[c]? <;> simp_all [Value.canonV]

/-- `r` is the one row of its class. -/
def Row.Lone (r : Row) : Prop := ∀ z : Row, z.canon = r.canon → z = r

theorem Row.lone_of_forall : ∀ {r : Row}, (∀ v ∈ r, v.Lone) → r.Lone
  | [], _, z, hz => by cases z with
    | nil => rfl
    | cons _ _ => simp [Row.canon] at hz
  | v :: vs, h, z, hz => by
    cases z with
    | nil => simp [Row.canon] at hz
    | cons w ws =>
      simp only [Row.canon, List.map_cons, List.cons.injEq] at hz
      rw [h v List.mem_cons_self w hz.1,
        Row.lone_of_forall (fun u hu => h u (List.mem_cons_of_mem _ hu)) ws hz.2]

/-- Rows in the raw order of their values, lexicographically. -/
def Row.leRaw (a b : Row) : Bool := Value.leListRaw a b

theorem Row.leRaw_rawOrder : RawOrder Row.leRaw :=
  ⟨Value.leListRaw_total, Value.leListRaw_trans, fun _ _ => Value.leListRaw_antisymm⟩

/-- `f` reads rows only up to canonical codes: it cannot tell a `-0.0` from a
`0.0`, or the negative NaN from the NaN. Groups and keys are classes up to
canonical codes (D31), so a function of a group's key is well defined on the
group when it respects them. -/
def RespectsCanon {β : Type} (f : Row → β) : Prop := ∀ k k' : Row, k.canon = k'.canon → f k = f k'

/-- `DISTINCT` of values, up to canonical codes. -/
def distinctVals (vs : List Value) : List Value := canonReps Value.canonV Value.leRaw vs

/-- `DISTINCT` of rows, up to canonical codes. -/
def distinctRows (rows : Relation) : Relation := canonReps Row.canon Row.leRaw rows

end Substrait
