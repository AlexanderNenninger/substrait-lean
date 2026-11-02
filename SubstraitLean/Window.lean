import SubstraitLean.Aggregate

/-!
# Window functions

`ROW_NUMBER`, `LAG`, `LEAD`, the ranks (`RANK`, `DENSE_RANK`,
`PERCENT_RANK`, `CUME_DIST`, `NTILE`), and aggregates and `FIRST_VALUE`,
`LAST_VALUE` and `NTH_VALUE` over a frame, all over `PARTITION BY … ORDER BY
…`. DataFusion writes them as `windowFunction` expressions in a `ProjectRel`;
here a window is a relation of its own (`Rel.window`) that appends one column
per function.

**Semantics.** The input is sorted by the sort keys with a stable merge sort.
Each row then sees the rows before and after it *in its own partition*
(rows that agree on the partition columns; NULLs group together, as in SQL).
`LAG(c, k, d)` is column `c` of the `k`-th row before, or `d` when there is
none; `LEAD` looks ahead; `ROW_NUMBER` counts from 1.

Ranks, `CUME_DIST` and `RANGE` frames depend on the sort keys' values only
(tied rows are peers). Rows that tie on every sort key may come out in any
order, and then `LAG`, `NTILE` and `ROWS` frames depend on the engine. `window_tiebreak` shows that it doesn't when the
partition and sort columns form a key: then any sorted arrangement gives the
same rows.
-/

namespace Substrait

/-! ## Window functions -/

/-! ## Frames

A frame says which rows of the partition an aggregate (or `FIRST_VALUE`, …)
of row `x` sees. `ROWS` frames count rows; `RANGE` frames are a condition on
the sort keys: `CURRENT ROW` is `x`'s peers (rows that tie with it on every
key), and `k PRECEDING` / `k FOLLOWING` compare the one sort key's value
with `x`'s, shifted by `k` (in its own unit: microseconds for timestamps,
days for dates). A row whose key is NULL is `k` from no other row: it is in
the frame of a NULL `x` (its peers), and otherwise only where the bound on
its side is `UNBOUNDED`. -/

inductive FrameBound where
  | unboundedPreceding
  /-- `k PRECEDING`; `preceding 0` is `CURRENT ROW`. -/
  | preceding (k : Nat)
  | following (k : Nat)
  | unboundedFollowing
  deriving Repr, BEq, DecidableEq

structure Frame where
  /-- `RANGE` (by the sort keys' values) or `ROWS`. -/
  range : Bool
  lo : FrameBound
  hi : FrameBound
  deriving Repr, BEq, DecidableEq

/-- The whole partition. -/
def Frame.all : Frame := ⟨false, .unboundedPreceding, .unboundedFollowing⟩

/-- The signed offset of a bound, `none` if unbounded. -/
def FrameBound.offset : FrameBound → Option Int
  | .preceding k => some (-(k : Int))
  | .following k => some k
  | _ => none

/-- `y` comes at or after the point `d` units after `x` on the key `k` (for
`d = 0`: not before `x`'s peers). -/
def rangeFrom (k : SortKey) (d : Int) (x y : Row) : Bool :=
  match x.getD k.col .null, y.getD k.col .null with
  | .int vx, .int vy => if k.desc then decide (vy ≤ vx - d) else decide (vx + d ≤ vy)
  | .null, .null => true
  | a, b => decide (k.nullRank a < k.nullRank b)

/-- `y` comes at or before the point `d` units after `x` on the key `k`. -/
def rangeTo (k : SortKey) (d : Int) (x y : Row) : Bool :=
  match x.getD k.col .null, y.getD k.col .null with
  | .int vx, .int vy => if k.desc then decide (vx - d ≤ vy) else decide (vy ≤ vx + d)
  | .null, .null => true
  | a, b => decide (k.nullRank b < k.nullRank a)

/-- The rows of `x`'s partition in its frame, in sort order: `pb` are the
partition's rows before `x`, `pa` those after. -/
def Frame.rows (fr : Frame) (sort : List SortKey) (pb : List Row) (x : Row) (pa : List Row) :
    List Row :=
  let all := pb ++ x :: pa
  if fr.range then
    let lo (y : Row) : Bool := match fr.lo with
      | .unboundedPreceding => true
      | .unboundedFollowing => false
      | b => match b.offset, sort with
        | some 0, _ => sortLe sort x y
        | some d, k :: _ => rangeFrom k d x y
        | _, _ => false
    let hi (y : Row) : Bool := match fr.hi with
      | .unboundedFollowing => true
      | .unboundedPreceding => false
      | b => match b.offset, sort with
        | some 0, _ => sortLe sort y x
        | some d, k :: _ => rangeTo k d x y
        | _, _ => false
    all.filter fun y => lo y && hi y
  else
    let i : Int := pb.length
    let lo : Int := match fr.lo with
      | .unboundedPreceding => 0
      | .unboundedFollowing => all.length
      | b => i + (b.offset.getD 0)
    let hi : Int := match fr.hi with
      | .unboundedPreceding => -1
      | .unboundedFollowing => all.length
      | b => i + (b.offset.getD 0)
    (all.zipIdx.filter fun (_, j) => decide (lo ≤ j) && decide ((j : Int) ≤ hi)).map (·.1)

/-! ## Window functions -/

inductive WinFn where
  | rowNumber
  /-- Column `col` of the row `offset` rows earlier in the partition, else `default`. -/
  | lag (col offset : Nat) (default : Value)
  /-- Column `col` of the row `offset` rows later in the partition, else `default`. -/
  | lead (col offset : Nat) (default : Value)
  /-- `RANK()`: one more than the partition's rows before `x`'s peers. The
  sort keys are the window's (as are those of the functions below). -/
  | rank (sort : List SortKey)
  /-- `DENSE_RANK()`: one more than the distinct sort keys before `x`'s. -/
  | denseRank (sort : List SortKey)
  /-- `PERCENT_RANK()`: `(rank - 1) / (n - 1)` as a double, `0` for one row. -/
  | percentRank (sort : List SortKey)
  /-- `CUME_DIST()`: the share of the partition's rows up to `x`'s last peer. -/
  | cumeDist (sort : List SortKey)
  /-- `NTILE(k)` as DataFusion computes it: `⌊i · min(k, n) / n⌋ + 1` for the
  `i`-th row (from 0) of `n`, not the SQL standard's buckets. -/
  | ntile (k : Nat)
  /-- An aggregate over the frame. -/
  | agg (m : Measure) (sort : List SortKey) (frame : Frame)
  /-- Column `col` of the frame's first, last or `n`-th (from 1) row. -/
  | firstValue (col : Nat) (sort : List SortKey) (frame : Frame)
  | lastValue (col : Nat) (sort : List SortKey) (frame : Frame)
  | nthValue (col n : Nat) (sort : List SortKey) (frame : Frame)
  deriving Repr, BEq, DecidableEq

/-- `Expr.refsLt`, decided. -/
def Expr.refsLtB (n : Nat) : Expr → Bool
  | .lit _ => true
  | .field i => decide (i < n)
  | .un _ a => a.refsLtB n
  | .bin _ a b => a.refsLtB n && b.refsLtB n
  | .ifThen c t e => c.refsLtB n && t.refsLtB n && e.refsLtB n
  | .hof _ l _ => l.refsLtB n

def WinFn.refsLt (n : Nat) : WinFn → Bool
  | .rowNumber | .rank _ | .denseRank _ | .percentRank _ | .cumeDist _ | .ntile _ => true
  | .lag c _ _ | .lead c _ _ | .firstValue c _ _ | .lastValue c _ _ | .nthValue c _ _ _ => decide (c < n)
  | .agg m _ _ => m.arg.refsLtB n && m.filter.all (·.refsLtB n)

/-- Same partition: equal on every partition column (NULLs are equal). -/
def samePart (part : List Nat) (x y : Row) : Bool :=
  decide (part.map (x.getD · .null) = part.map (y.getD · .null))

/-- Ties with `x` on every sort key. -/
def peer (sort : List SortKey) (x y : Row) : Bool := sortLe sort y x && sortLe sort x y

/-- The double `a / b` of two integers. -/
def floatRatio (a b : Nat) : Value := .int (FloatCode.lift₂ (· / ·) (FloatCode.ofInt a) (FloatCode.ofInt b))

/-- DataFusion's `NTILE(k)` of the `i`-th of `n` rows: with fewer rows than
buckets, a bucket for each row. -/
def ntileOf (i k n : Nat) : Nat := i * min k n / n + 1

/-- A window function of `x`, from its partition's rows before (`pb`) and
after (`pa`) it in sort order. -/
def WinFn.valueIn (pb : List Row) (x : Row) (pa : List Row) : WinFn → Value
  | .rowNumber => .int (pb.length + 1)
  | .lag c k d => ((x :: pb.reverse)[k]?).elim d (·.getD c .null)
  | .lead c k d => ((x :: pa)[k]?).elim d (·.getD c .null)
  | .rank sort => .int ((pb.filter fun y => !peer sort x y).length + 1)
  | .denseRank sort =>
    .int ((dedup ((pb.filter fun y => !peer sort x y).map fun y => sort.map (y.getD ·.col .null))).length + 1)
  | .percentRank sort =>
    let n := pb.length + 1 + pa.length
    if n ≤ 1 then floatRatio 0 1 else floatRatio (pb.filter fun y => !peer sort x y).length (n - 1)
  | .cumeDist sort =>
    floatRatio (pb.length + 1 + (pa.filter (peer sort x)).length) (pb.length + 1 + pa.length)
  | .ntile k => .int (ntileOf pb.length k (pb.length + 1 + pa.length))
  | .agg m sort fr => m.eval (fr.rows sort pb x pa)
  | .firstValue c sort fr => ((fr.rows sort pb x pa).head?).elim .null (·.getD c .null)
  | .lastValue c sort fr => ((fr.rows sort pb x pa).getLast?).elim .null (·.getD c .null)
  | .nthValue c n sort fr => ((fr.rows sort pb x pa)[n - 1]?).elim .null (·.getD c .null)

/-- The value of a window function at row `x`, which comes after the rows
`before` and before the rows `after` in sort order. -/
def WinFn.value (part : List Nat) (before after : List Row) (x : Row) (f : WinFn) : Value :=
  f.valueIn (before.filter (samePart part x)) x (after.filter (samePart part x))

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
  simp only [WinFn.value, WinFn.valueIn]
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
  simp only [WinFn.value, WinFn.valueIn]
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
  simp only [WinFn.value, WinFn.valueIn]
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
  simp only [WinFn.value, WinFn.valueIn]
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
