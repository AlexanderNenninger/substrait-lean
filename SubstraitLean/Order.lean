import SubstraitLean.Expr

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
  | .bool _ => 0 | .int _ => 1 | .str _ => 2 | .list _ => 3 | .null => 4
/-- `Value.le` on values that are not both lists. -/
def Value.leScalar : Value → Value → Bool
  | .bool a, .bool b => !a || b
  | .int a, .int b => decide (a ≤ b)
  | .str a, .str b => decide (a ≤ b)
  | a, b => decide (a.tag ≤ b.tag)
mutual
/-- A total order on values: each type's own order (`false < true`, integers
and the float codes numerically, strings by code point, which is UTF-8 byte
order, lists lexicographically with a prefix first), types ordered booleans
< integers < strings < lists < NULL. Within a column only one type and NULL
occur; NULL's place only matters inside lists (`ORDER BY` places top-level
NULLs itself, and `MIN`/`MAX` skip them), where engines sort NULL elements
last. -/
def Value.le : Value → Value → Bool
  | .list as, .list bs => Value.leList as bs
  | a, b => Value.leScalar a b
  termination_by a b => sizeOf a + sizeOf b
/-- Lexicographic order on lists of values: the first element where they
differ decides, and a prefix comes first. -/
def Value.leList : List Value → List Value → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Value.le a b && (!Value.le b a || Value.leList as bs)
  termination_by as bs => sizeOf as + sizeOf bs
end
theorem Value.le_def (a b : Value) : a.le b = (match a, b with
    | .list as, .list bs => Value.leList as bs
    | a, b => Value.leScalar a b) := by
  cases a <;> cases b <;> rw [Value.le] <;> simp

theorem Value.leList_nil (bs : List Value) : Value.leList [] bs = true := by
  cases bs <;> rw [Value.leList]

theorem Value.leList_cons_nil (a : Value) (as : List Value) : Value.leList (a :: as) [] = false := by
  rw [Value.leList]

theorem Value.leList_cons (a b : Value) (as bs : List Value) :
    Value.leList (a :: as) (b :: bs) = (a.le b && (!b.le a || Value.leList as bs)) := by
  rw [Value.leList]

mutual
theorem Value.le_antisymm : ∀ {a b : Value}, a.le b = true → b.le a = true → a = b
  | .list as, .list bs, hab, hba => by
    simp only [Value.le_def] at hab hba
    rw [Value.leList_antisymm hab hba]
  | .null, b, hab, hba | .bool _, b, hab, hba | .int _, b, hab, hba | .str _, b, hab, hba
  | .list _, .null, hab, hba | .list _, .bool _, hab, hba | .list _, .int _, hab, hba
  | .list _, .str _, hab, hba => by
    try cases b
    all_goals simp_all [Value.le_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_antisymm hab hba
      | (rename_i x y; cases x <;> cases y <;> simp_all)
  termination_by a b => sizeOf a + sizeOf b

theorem Value.leList_antisymm : ∀ {as bs : List Value},
    Value.leList as bs = true → Value.leList bs as = true → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h | _ :: _, [], h, _ => by simp [Value.leList_cons_nil] at h
  | a :: as, b :: bs, hab, hba => by
    simp only [Value.leList_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab hba
    have hb := Value.le_antisymm hab.1 hba.1
    subst hb
    have h₁ : Value.leList as bs = true := hab.2.resolve_left (by simp [hba.1])
    have h₂ : Value.leList bs as = true := hba.2.resolve_left (by simp [hab.1])
    rw [Value.leList_antisymm h₁ h₂]
  termination_by as bs => sizeOf as + sizeOf bs
end

mutual
theorem Value.le_total : ∀ a b : Value, a.le b = true ∨ b.le a = true
  | .list as, .list bs => by simp only [Value.le_def]; exact Value.leList_total as bs
  | .null, b | .bool _, b | .int _, b | .str _, b
  | .list _, .null | .list _, .bool _ | .list _, .int _ | .list _, .str _ => by
    try cases b
    all_goals simp [Value.le_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_total _ _
      | (rename_i x y; cases x <;> cases y <;> simp)
  termination_by a b => sizeOf a + sizeOf b

theorem Value.leList_total : ∀ as bs : List Value,
    Value.leList as bs = true ∨ Value.leList bs as = true
  | [], _ => Or.inl (Value.leList_nil _)
  | _ :: _, [] => Or.inr (Value.leList_nil _)
  | a :: as, b :: bs => by
    simp only [Value.leList_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    have := Value.leList_total as bs
    rcases Value.le_total a b with h | h <;> by_cases h' : (b.le a = true) <;>
      by_cases h'' : (a.le b = true) <;> simp_all
  termination_by as bs => sizeOf as + sizeOf bs
end

mutual
theorem Value.le_trans : ∀ a b c : Value, a.le b = true → b.le c = true → a.le c = true
  | .list as, .list bs, .list cs, hab, hbc => by
    simp only [Value.le_def] at *
    exact Value.leList_trans as bs cs hab hbc
  | .null, b, c, hab, hbc | .bool _, b, c, hab, hbc | .int _, b, c, hab, hbc
  | .str _, b, c, hab, hbc | .list _, .null, c, hab, hbc | .list _, .bool _, c, hab, hbc
  | .list _, .int _, c, hab, hbc | .list _, .str _, c, hab, hbc
  | .list _, .list _, .null, hab, hbc | .list _, .list _, .bool _, hab, hbc
  | .list _, .list _, .int _, hab, hbc | .list _, .list _, .str _, hab, hbc => by
    try cases b
    all_goals try cases c
    all_goals simp_all [Value.le_def, Value.leScalar, Value.tag]
    all_goals first
      | omega
      | exact String.le_trans hab hbc
      | (rename_i x y z; cases x <;> cases y <;> cases z <;> simp_all)
  termination_by a b c => sizeOf a + sizeOf b + sizeOf c

theorem Value.leList_trans : ∀ as bs cs : List Value,
    Value.leList as bs = true → Value.leList bs cs = true → Value.leList as cs = true
  | [], _, _, _, _ => Value.leList_nil _
  | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], _, h => by simp [Value.leList_cons_nil] at h
  | a :: as, b :: bs, c :: cs, hab, hbc => by
    simp only [Value.leList_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
    have hac := Value.le_trans a b c hab.1 hbc.1
    refine ⟨hac, ?_⟩
    by_cases hca : c.le a = true
    · right
      have hba := Value.le_trans b c a hbc.1 hca
      have hcb := Value.le_trans c a b hca hab.1
      exact Value.leList_trans as bs cs (hab.2.resolve_left (by simp [hba]))
        (hbc.2.resolve_left (by simp [hcb]))
    · left; simpa using hca
  termination_by as bs cs => sizeOf as + sizeOf bs + sizeOf cs
end

theorem Value.le_totalPre : TotalPre Value.le where
  trans := Value.le_trans
  total a b := by rcases Value.le_total a b with h | h <;> simp [h]

/-- One `ORDER BY` key: a column, ascending or descending, NULLs first or last. -/
structure SortKey where
  col : Nat
  desc : Bool := false
  nullsFirst : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Where NULLs go: before (`0`) or after (`1`) the other values. -/
def SortKey.nullRank (k : SortKey) : Value → Nat
  | .null => if k.nullsFirst then 0 else 1
  | _ => if k.nullsFirst then 1 else 0

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
    cases hd : k.desc <;> simp_all [Value.le_def, Value.leScalar]

/-- Rows that sort both ways on a key agree on its column. -/
theorem SortKey.le_antisymm {k : SortKey} {x y : Row} (hxy : k.le x y = true) (hyx : k.le y x = true) :
    x.getD k.col .null = y.getD k.col .null := by
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
      ks.map (x.getD ·.col .null) = ks.map (y.getD ·.col .null)
  | [], _, _, _, _ => rfl
  | k :: ks, _, _, hxy, hyx => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := lexLe_antisymm hxy hyx
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨SortKey.le_antisymm h₁ h₂, sortLe_antisymm h₃ h₄⟩

end Substrait
