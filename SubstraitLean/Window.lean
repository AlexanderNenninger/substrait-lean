import SubstraitLean.Expr

/-!
# Window functions

`ROW_NUMBER`, `LAG` and `LEAD` over `PARTITION BY … ORDER BY …`. DataFusion
writes them as `windowFunction` expressions in a `ProjectRel`; here a window
is a relation of its own (`Rel.window`) that appends one column per function.

**Semantics.** The input is sorted by the sort keys with a stable merge sort.
Each row then sees the rows before and after it *in its own partition*
(rows that agree on the partition columns; NULLs group together, as in SQL).
`LAG(c, k, d)` is column `c` of the `k`-th row before, or `d` when there is
none; `LEAD` looks ahead; `ROW_NUMBER` counts from 1.

Rows that tie on every sort key may come out in any order, and then `LAG`
depends on the engine. `window_tiebreak` shows that it doesn't when the
partition and sort columns form a key: then any sorted arrangement gives the
same rows.
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
  | .null => 0 | .bool _ => 1 | .int _ => 2 | .str _ => 3

/-- A total order on values: each type's own order (`false < true`, integers
and the float codes numerically, strings by code point, which is UTF-8 byte
order), types ordered NULL < booleans < integers < strings. Within a column
only one type and NULL occur. -/
def Value.le : Value → Value → Bool
  | .bool a, .bool b => !a || b
  | .int a, .int b => decide (a ≤ b)
  | .str a, .str b => decide (a ≤ b)
  | a, b => decide (a.tag ≤ b.tag)

theorem Value.le_totalPre : TotalPre Value.le where
  trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [Value.le, Value.tag]
    all_goals first
      | omega
      | (intro h₁ h₂; exact String.le_trans h₁ h₂)
      | (rename_i x y z; cases x <;> cases y <;> cases z <;> simp)
  total a b := by
    cases a <;> cases b <;> simp [Value.le, Value.tag]
    all_goals first
      | omega
      | exact String.le_total _ _
      | (rename_i x y; cases x <;> cases y <;> simp)

theorem Value.le_antisymm {a b : Value} (hab : a.le b = true) (hba : b.le a = true) : a = b := by
  cases a <;> cases b <;> simp_all [Value.le, Value.tag]
  all_goals first
    | omega
    | exact String.le_antisymm hab hba
    | (rename_i x y; cases x <;> cases y <;> simp_all)

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
    cases hd : k.desc <;> simp_all [Value.le]

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

/-! ## Window functions -/

inductive WinFn where
  | rowNumber
  /-- Column `col` of the row `offset` rows earlier in the partition, else `default`. -/
  | lag (col offset : Nat) (default : Value)
  /-- Column `col` of the row `offset` rows later in the partition, else `default`. -/
  | lead (col offset : Nat) (default : Value)
  deriving Repr, BEq, DecidableEq

def WinFn.refsLt (n : Nat) : WinFn → Bool
  | .rowNumber => true
  | .lag c _ _ | .lead c _ _ => decide (c < n)

/-- Same partition: equal on every partition column (NULLs are equal). -/
def samePart (part : List Nat) (x y : Row) : Bool :=
  decide (part.map (x.getD · .null) = part.map (y.getD · .null))

/-- The value of a window function at row `x`, which comes after the rows
`before` and before the rows `after` in sort order. -/
def WinFn.value (part : List Nat) (before after : List Row) (x : Row) : WinFn → Value
  | .rowNumber => .int ((before.filter (samePart part x)).length + 1)
  | .lag c k d => ((x :: (before.filter (samePart part x)).reverse)[k]?).elim d (·.getD c .null)
  | .lead c k d => ((x :: after.filter (samePart part x))[k]?).elim d (·.getD c .null)

/-- Extend each row of a sorted list with its window values. -/
def windowRows (part : List Nat) (fns : List WinFn) : List Row → List Row → List Row
  | _, [] => []
  | before, x :: after =>
      (x ++ fns.map (·.value part before after x)) :: windowRows part fns (before ++ [x]) after

def windowEval (part : List Nat) (sort : List SortKey) (fns : List WinFn) (rows : Relation) :
    Relation :=
  windowRows part fns [] (rows.mergeSort (sortLe sort))

/-! ## Lemmas -/

theorem samePart_refl (part : List Nat) (x : Row) : samePart part x x = true := by
  simp [samePart]

theorem samePart_comm {part : List Nat} {x y : Row} (h : samePart part x y = true) :
    samePart part y x = true := by
  simp only [samePart, decide_eq_true_eq] at *; exact h.symm

/-- Each output row extends some row `x` of the sorted list with the window
values computed from the rows before and after it. -/
theorem mem_windowRows {part : List Nat} {fns : List WinFn} :
    ∀ {pre l : List Row} {row : Row}, row ∈ windowRows part fns pre l →
      ∃ b x a, pre ++ l = b ++ x :: a ∧ row = x ++ fns.map (·.value part b a x)
  | _, [], _, h => by simp [windowRows] at h
  | pre, x :: l, row, h => by
      simp only [windowRows, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨pre, x, l, rfl, rfl⟩
      · obtain ⟨b, y, a, he, rfl⟩ := mem_windowRows h
        exact ⟨b, y, a, by simpa using he, rfl⟩

theorem mem_windowEval {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {rows : Relation} {row : Row} (h : row ∈ windowEval part sort fns rows) :
    ∃ b x a, rows.mergeSort (sortLe sort) = b ++ x :: a ∧ x ∈ rows ∧
      row = x ++ fns.map (·.value part b a x) := by
  obtain ⟨b, x, a, he, rfl⟩ := mem_windowRows h
  rw [List.nil_append] at he
  have hx : x ∈ rows.mergeSort (sortLe sort) := by rw [he]; simp
  exact ⟨b, x, a, he, List.mem_mergeSort.mp hx, rfl⟩

/-- Around a row of the sorted input: the rows before sort no later, the
rows after no earlier, and all of them are input rows. -/
theorem sorted_split {sort : List SortKey} {rows : Relation} {b a : List Row} {x : Row}
    (he : rows.mergeSort (sortLe sort) = b ++ x :: a) :
    (∀ y ∈ b, sortLe sort y x = true) ∧ (∀ y ∈ a, sortLe sort x y = true) ∧
      ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → y ∈ rows := by
  have hs := List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total rows
  rw [he, List.pairwise_append, List.pairwise_cons] at hs
  refine ⟨fun y hy => hs.2.2 y hy x (by simp), fun y hy => hs.2.1.1 y hy, fun y hy => ?_⟩
  have : y ∈ rows.mergeSort (sortLe sort) := by rw [he]; rcases hy with rfl | hy | hy <;> simp [*]
  exact List.mem_mergeSort.mp this

theorem windowRows_length {part : List Nat} {fns : List WinFn} :
    ∀ {pre l : List Row}, (windowRows part fns pre l).length = l.length
  | _, [] => rfl
  | _, _ :: _ => by simp [windowRows, windowRows_length]

/-- The first `n` columns of the output are the input, in sorted order. -/
theorem windowRows_take {part : List Nat} {fns : List WinFn} {n : Nat} :
    ∀ {pre l : List Row}, (∀ x ∈ l, x.length = n) →
      (windowRows part fns pre l).map (·.take n) = l
  | _, [], _ => rfl
  | _, x :: l, h => by
      simp only [windowRows, List.map_cons, List.cons.injEq]
      refine ⟨?_, windowRows_take fun y hy => h y (by simp [hy])⟩
      rw [List.take_append_of_le_length (by simp [h x (by simp)]), List.take_of_length_le (by simp [h x (by simp)])]

/-- What a window value can be. `LAG` reads a row of the partition at or
before `x`; `LEAD` one at or after `x`. -/
theorem WinFn.value_lag {part : List Nat} {b a : List Row} {x : Row} {c k : Nat} {d : Value} :
    (WinFn.lag c k d).value part b a x = d ∨
      ∃ y, (y = x ∨ (y ∈ b ∧ samePart part x y = true)) ∧
        (WinFn.lag c k d).value part b a x = y.getD c .null := by
  simp only [WinFn.value]
  cases h : (x :: (b.filter (samePart part x)).reverse)[k]? with
  | none => simp
  | some y =>
    right
    refine ⟨y, ?_, rfl⟩
    have := List.mem_of_getElem? h
    simpa [List.mem_cons, List.mem_reverse, List.mem_filter] using this

theorem WinFn.value_lead {part : List Nat} {b a : List Row} {x : Row} {c k : Nat} {d : Value} :
    (WinFn.lead c k d).value part b a x = d ∨
      ∃ y, (y = x ∨ (y ∈ a ∧ samePart part x y = true)) ∧
        (WinFn.lead c k d).value part b a x = y.getD c .null := by
  simp only [WinFn.value]
  cases h : (x :: a.filter (samePart part x))[k]? with
  | none => simp
  | some y =>
    right
    refine ⟨y, ?_, rfl⟩
    have := List.mem_of_getElem? h
    simpa [List.mem_cons, List.mem_filter] using this

/-- As `value_lag`, but a row other than `x` itself needs offset `k ≥ 1`. -/
theorem WinFn.value_lag' {part : List Nat} {b a : List Row} {x : Row} {c k : Nat} {d : Value} :
    (WinFn.lag c k d).value part b a x = d ∨
      ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ b ∧ samePart part x y = true)) ∧
        (WinFn.lag c k d).value part b a x = y.getD c .null := by
  simp only [WinFn.value]
  cases h : (x :: (b.filter (samePart part x)).reverse)[k]? with
  | none => simp
  | some y =>
    right
    refine ⟨y, ?_, rfl⟩
    cases k with
    | zero => simp at h; exact .inl ⟨h.symm, rfl⟩
    | succ k =>
      have := List.mem_of_getElem? (by simpa using h)
      simp only [List.mem_reverse, List.mem_filter] at this
      exact .inr this

theorem WinFn.value_lead' {part : List Nat} {b a : List Row} {x : Row} {c k : Nat} {d : Value} :
    (WinFn.lead c k d).value part b a x = d ∨
      ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ a ∧ samePart part x y = true)) ∧
        (WinFn.lead c k d).value part b a x = y.getD c .null := by
  simp only [WinFn.value]
  cases h : (x :: a.filter (samePart part x))[k]? with
  | none => simp
  | some y =>
    right
    refine ⟨y, ?_, rfl⟩
    cases k with
    | zero => simp at h; exact .inl ⟨h.symm, rfl⟩
    | succ k =>
      have := List.mem_of_getElem? (by simpa using h)
      simp only [List.mem_filter] at this
      exact .inr this

end Substrait
