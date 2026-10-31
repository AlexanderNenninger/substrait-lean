import SubstraitLean.Window

/-!
# Aggregation

`AggregateRel` with one grouping set: the output has one row per distinct
value of the grouping expressions (in order of first occurrence), holding
those values followed by one value per measure. Without grouping
expressions there is exactly one output row, even for an empty input.

A measure is `COUNT`, `SUM`, `MIN`, `MAX`, `AVG` or `ARRAY_AGG` (`collect`,
whose rows may be ordered) of an expression, over the
rows that pass its `FILTER` (if any), skipping NULLs, and over distinct
values only for `COUNT(DISTINCT …)` and friends. On no values `COUNT` is 0
and the others are NULL. Checked against DataFusion 51:

* `SUM` of integers wraps around modulo 2⁶⁴; since wrapping addition is
  associative, the result is the true sum unless that leaves 64 bits.
  `SUM` here is the true sum, and `SubstraitLean/Safety.lean` warns.
* `SUM` and `AVG` of doubles round, in an order DataFusion does not promise;
  here they add in list order with native floats. `AVG` of integers is the
  `AVG` of their conversions to double, which the parser makes explicit.
* `MIN` and `MAX` use the same order as `ORDER BY` (`Value.le`). The parser
  refuses them on doubles: DataFusion's grouped `MIN` of a group of +∞ is
  the largest finite double, and it skips NaN next to other values.
* Grouping compares values exactly; doubles have one zero and one NaN
  (`SubstraitLean/Float.lean`), so -0.0 and 0.0 are one group, and NULLs
  group together.
-/

namespace Substrait

/-! ## Distinct elements -/

/-- The first occurrence of every element, in order (`n` bounds the length). -/
def dedupN {α : Type} [DecidableEq α] : Nat → List α → List α
  | 0, _ | _, [] => []
  | n + 1, x :: xs => x :: dedupN n (xs.filter (· != x))

def dedup {α : Type} [DecidableEq α] (l : List α) : List α := dedupN l.length l

theorem dedupN_spec {α : Type} [DecidableEq α] : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (∀ y, y ∈ dedupN n l ↔ y ∈ l) ∧ (dedupN n l).Sublist l ∧ (dedupN n l).Pairwise (· ≠ ·)
  | _, [], _ => by cases ‹Nat› <;> simp [dedupN]
  | 0, _ :: _, h => by simp at h
  | n + 1, x :: xs, h => by
    have hf : (xs.filter (· != x)).length ≤ n := by
      have := List.length_filter_le (· != x) xs; simp at h; omega
    obtain ⟨hm, hs, hp⟩ := dedupN_spec n _ hf
    simp only [dedupN]
    refine ⟨fun y => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, hm, List.mem_filter, bne_iff_ne, ne_eq]
      by_cases hy : y = x <;> simp [hy]
    · exact (hs.trans List.filter_sublist).cons_cons x
    · refine List.Pairwise.cons (fun y hy => ?_) hp
      have := (hm y).mp hy
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at this
      exact fun h => this.2 h.symm

theorem mem_dedup {α : Type} [DecidableEq α] {l : List α} {y : α} : y ∈ dedup l ↔ y ∈ l :=
  (dedupN_spec _ l (Nat.le_refl _)).1 y
theorem dedup_sublist {α : Type} [DecidableEq α] (l : List α) : (dedup l).Sublist l :=
  (dedupN_spec _ l (Nat.le_refl _)).2.1
theorem dedup_pairwise {α : Type} [DecidableEq α] (l : List α) : (dedup l).Pairwise (· ≠ ·) :=
  (dedupN_spec _ l (Nat.le_refl _)).2.2

/-! ## Measures -/

inductive AggFn where
  /-- `COUNT` of the non-NULL values (`COUNT(*)` counts a literal). -/
  | count
  /-- `SUM` of integers, exactly. -/
  | sum
  /-- `SUM` and `AVG` of doubles, with native floats. -/
  | fsum | avg
  /-- `MIN` and `MAX` by `Value.le`. -/
  | min | max
  /-- `ARRAY_AGG`: the list of the values, in the measure's `sort` order. -/
  | collect
  deriving Repr, DecidableEq

structure Measure where
  fn : AggFn
  arg : Expr
  /-- `fn(DISTINCT arg)` -/
  distinct : Bool := false
  /-- `fn(arg) FILTER (WHERE cond)` -/
  filter : Option Expr := none
  /-- `fn(arg ORDER BY …)`: the order of the rows, for `collect`. -/
  sort : List SortKey := []
  deriving Repr, DecidableEq

def Measure.refsLt (n : Nat) (m : Measure) : Prop :=
  m.arg.refsLt n ∧ ∀ c ∈ m.filter, c.refsLt n

/-- The expressions a measure evaluates (on every input row). -/
def Measure.exprs (m : Measure) : List Expr := m.arg :: m.filter.toList

/-- The rows a measure looks at: those passing its filter. -/
def Measure.kept (m : Measure) (rows : Relation) : Relation :=
  match m.filter with
  | none => rows
  | some c => rows.filter fun row => (c.eval row).isTrue

/-- The values a measure aggregates: its argument on the kept rows, without
NULLs, and without repetitions for `DISTINCT`. -/
def Measure.inputs (m : Measure) (rows : Relation) : List Value :=
  let vs := ((m.kept rows).map m.arg.eval).filter (· != .null)
  if m.distinct then dedup vs else vs

def intSum : List Value → Int
  | [] => 0
  | .int i :: vs => i + intSum vs
  | _ :: vs => intSum vs

def floatSum (vs : List Value) : Int :=
  vs.foldl (fun acc v => match v with
    | .int c => FloatCode.lift₂ (· + ·) acc c
    | _ => acc) (FloatCode.ofInt 0)

/-- The element `pick` keeps from each pair, from the left. -/
def pickFold (pick : Value → Value → Bool) (v : Value) (vs : List Value) : Value :=
  vs.foldl (fun a b => if pick a b then b else a) v

def AggFn.apply : AggFn → List Value → Value
  | .count, vs => .int vs.length
  | _, [] => .null
  | .sum, vs => .int (intSum vs)
  | .fsum, vs => .int (floatSum vs)
  | .avg, vs => .int (FloatCode.lift₂ (· / ·) (floatSum vs) (FloatCode.ofInt vs.length))
  | .min, v :: vs => pickFold (fun a b => !a.le b) v vs
  | .max, v :: vs => pickFold (fun a b => !b.le a) v vs
  | .collect, vs => .list vs

/-- `collect` takes the rows in its sort order (a stable sort, so without
one in list order: one of the orders an engine may choose). -/
def Measure.eval (rows : Relation) (m : Measure) : Value :=
  match m.fn with
  | .collect => AggFn.collect.apply (m.inputs (rows.mergeSort (sortLe m.sort)))
  | f => f.apply (m.inputs rows)

theorem Measure.eval_eq {m : Measure} (h : m.fn ≠ .collect) (rows : Relation) :
    m.eval rows = m.fn.apply (m.inputs rows) := by
  unfold Measure.eval; split <;> simp_all

/-! ## Groups -/

def groupKey (gs : List Expr) (row : Row) : Row := gs.map (·.eval row)

/-- The rows of the group with key `k`. -/
def groupRows (gs : List Expr) (rows : Relation) (k : Row) : Relation :=
  rows.filter fun row => groupKey gs row == k

def aggregateEval (gs : List Expr) (ms : List Measure) (rows : Relation) : Relation :=
  if gs.isEmpty then [ms.map (·.eval rows)]
  else (dedup (rows.map (groupKey gs))).map fun k => k ++ ms.map (·.eval (groupRows gs rows k))

/-- The groups, one per output row. -/
def aggGroups (gs : List Expr) (rows : Relation) : List Relation :=
  if gs.isEmpty then [rows] else (dedup (rows.map (groupKey gs))).map (groupRows gs rows)

/-! ## Lemmas -/

theorem pickFold_mem (pick : Value → Value → Bool) :
    ∀ (v : Value) (vs : List Value), pickFold pick v vs ∈ v :: vs
  | v, [] => by simp [pickFold]
  | v, w :: vs => by
    have := pickFold_mem pick (if pick v w then w else v) vs
    simp only [pickFold, List.foldl_cons, List.mem_cons] at this ⊢
    by_cases hp : pick v w = true
    · simp only [hp, ↓reduceIte] at this ⊢; rcases this with h | h <;> simp [h]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at this ⊢; rcases this with h | h <;> simp [h]

theorem Measure.mem_inputs {m : Measure} {rows : Relation} {v : Value} (h : v ∈ m.inputs rows) :
    v ≠ .null ∧ ∃ row ∈ rows, m.arg.eval row = v := by
  have h' : v ∈ ((m.kept rows).map m.arg.eval).filter (· != .null) := by
    unfold inputs at h; split at h
    · exact mem_dedup.mp h
    · exact h
  simp only [List.mem_filter, List.mem_map, bne_iff_ne, ne_eq] at h'
  obtain ⟨⟨row, hrow, rfl⟩, hn⟩ := h'
  refine ⟨hn, row, ?_, rfl⟩
  unfold kept at hrow; split at hrow
  · exact hrow
  · exact (List.mem_filter.mp hrow).1

/-- `MIN` and `MAX` give one of the values (or NULL). -/
theorem AggFn.apply_minmax {f : AggFn} (hf : f = .min ∨ f = .max) {vs : List Value} :
    f.apply vs = .null ∨ f.apply vs ∈ vs := by
  rcases hf with rfl | rfl <;> cases vs <;>
    first | (simp [apply]; done) | (simp only [apply]; exact .inr (pickFold_mem _ _ _))

theorem mem_aggregateEval {gs : List Expr} {ms : List Measure} {rows : Relation} {row : Row}
    (h : row ∈ aggregateEval gs ms rows) :
    ∃ k grp, row = k ++ ms.map (·.eval grp) ∧ (∀ y ∈ grp, y ∈ rows) ∧
      ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k = groupKey gs x) := by
  unfold aggregateEval at h
  split at h
  · rename_i hg
    simp only [List.mem_singleton] at h
    exact ⟨[], rows, by simp [h], fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩⟩
  · simp only [List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
    exact ⟨_, _, rfl, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, rfl⟩⟩

theorem aggregateEval_length {gs : List Expr} {ms : List Measure} {rows : Relation} {row : Row}
    (h : row ∈ aggregateEval gs ms rows) : row.length = gs.length + ms.length := by
  obtain ⟨k, grp, rfl, _, hk⟩ := mem_aggregateEval h
  rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]

end Substrait
