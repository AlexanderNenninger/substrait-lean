import SubstraitLean.TableFormat
import SubstraitLean.Partition

/-!
# Pruning files and partitions (#81)

A Delta or Iceberg table is its data files' rows together, and each file
records statistics per column. `sverify.io` reads a source's rows on which a
condition `e` is TRUE (`DeltaSource(where=…)`, `IcebergSource(where=…)`, and
the predicates a pipeline implies on a base table), and skips a file whose
statistics show that `e` is TRUE on none of its rows. This module proves
that skipping these files changes no result.

* **Plans.** Shard the source by file: shard `f` holds the rows of file `f`
  on which `e` is TRUE. A skipped file's shard is empty, so dropping it keeps
  a `Sharding` of the same tables (`Sharding.prune`), and every plan linear
  in the source gives the same rows from the files read as from the whole
  table (`Rel.eval_pruned`, from `Rel.eval_sharded`). The rows themselves,
  in order, are `prune_sound` (`TableFormat.lean`).
* **The criterion.** A file may be skipped when the abstract evaluation of
  `e` on the file's statistics cannot be TRUE (`stats_prune`): each column's
  statistics give an abstract value (`ColStats.aval`: NULL unless the NULL
  count is 0, a number within the bounds unless every row is NULL), and
  `Expr.abs_sound` carries them to `e`. `sverify.io` asks the contract
  checker, which proves "`e` is not TRUE" from the same facts
  (`contract_sound`) and reasons more finely, through `refine` of
  conjunctions and disjunctions.
* **NaN in double statistics (#36).** Writers leave NaN out of a double
  column's minimum and maximum. NaN is the greatest code, so the minimum
  still bounds every value, and the maximum bounds them only when the file
  counts no NaN (`DoubleStats.colStats_correct`).
* **Truncated string bounds.** Delta and Iceberg write string bounds as
  prefixes: a minimum truncated to a prefix is still below every value, but
  a maximum truncated to a prefix is below the true maximum. What holds for
  either convention (a plain prefix, or Iceberg's incremented one) is that
  every value, cut to the maximum's length, is at most the maximum
  (`StrStats.Correct`). `StrStats.mayTrue` decides comparisons with string
  literals from that, and `strPrune_sound` proves it.
-/

namespace Substrait

/-! ## Pruned shards -/

theorem flatMap_filter_of_nil {α β : Type} (keep : α → Bool) (f : α → List β) :
    ∀ {l : List α}, (∀ a ∈ l, keep a = false → f a = []) →
      l.flatMap f = (l.filter keep).flatMap f
  | [], _ => rfl
  | a :: l, h => by
      have ih := flatMap_filter_of_nil keep f (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
      cases hk : keep a
      · simp [hk, h a List.mem_cons_self hk, ih]
      · simp [hk, ih]

/-- Dropping shards whose sharded tables are empty leaves a sharding of the
same tables. -/
theorem Sharding.prune {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) (keep : Catalog → Bool)
    (hempty : ∀ c ∈ cs, keep c = false → ∀ t, S t = true → (c t).rows = []) :
    Sharding S K cat (cs.filter keep) where
  wf c hc := hs.wf c (List.mem_filter.mp hc).1
  arity c hc := hs.arity c (List.mem_filter.mp hc).1
  split t ht := by
    rw [← flatMap_filter_of_nil keep (fun c => (c t).rows) fun c hc hk => hempty c hc hk t ht]
    exact hs.split t ht
  bcast t ht c hc := hs.bcast t ht c (List.mem_filter.mp hc).1
  keyLen c hc := hs.keyLen c (List.mem_filter.mp hc).1
  keyDisj := hs.keyDisj.sublist List.filter_sublist

variable [Boxes.Ambient]
/-- **Reading only the files not pruned.** A plan linear in the sharded
tables gives, up to order, the union of its results on the shards kept, when
every shard dropped holds no rows of a sharded table. -/
theorem Rel.eval_pruned {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.SoundAll cat)
    (keep : Catalog → Bool)
    (hempty : ∀ c ∈ cs, keep c = false → ∀ t, S t = true → (c t).rows = [])
    {r : Rel} (hw : r.WF cat) (hl : r.linear S K T cat = true) :
    (r.eval cat).Perm ((cs.filter keep).flatMap r.eval) :=
  Rel.eval_sharded (hs.prune keep hempty) hT hw hl

/-! ## The criterion from statistics -/

/-- What a file's statistics say about its rows, column by column: a column
without statistics may hold anything. -/
def fileEnv (cols : List (Option ColStats)) : List AVal :=
  cols.map fun (s : Option ColStats) => match s with
    | some s => s.aval
    | none => AVal.top

omit [Boxes.Ambient] in
theorem fileEnv_mem {cols : List (Option ColStats)} {row : Row}
    (h : ∀ i (s : ColStats), cols[i]? = some (some s) → s.aval.Mem (row.getD i .null)) :
    EnvMem (fileEnv cols) row := fun i => by
  simp only [fileEnv, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hc : cols[i]? with
  | none => exact AVal.mem_top _
  | some s =>
      cases s with
      | none => exact AVal.mem_top _
      | some s => exact h i s hc

/-- **Pruning by statistics.** If the abstract value of `e` on a file's
statistics cannot be TRUE, `e` is TRUE on none of the file's rows: the
file's shard of the source is empty. -/
theorem stats_prune {cols : List (Option ColStats)} {rows : Relation} (e : Expr)
    (hc : ∀ i (s : ColStats), cols[i]? = some (some s) → s.Correct i rows)
    (hnt : (e.abs (fileEnv cols)).tt = false) :
    rows.filter (fun r => (e.eval r).isTrue) = [] :=
  List.filter_eq_nil_iff.mpr fun row hr => by
    have hm := Expr.abs_sound (fileEnv_mem fun i s h => hc i s h row hr) e
    cases hv : e.eval row with
    | bool b => cases b <;> simp_all [AVal.Mem, Value.isTrue]
    | _ => simp [Value.isTrue]

/-! ## Doubles: NaN is left out of the bounds -/

/-- A double column's statistics as Parquet, Delta and Iceberg writers keep
them: the least and greatest code of the values that are not NaN, a NULL
count, and (Iceberg) a NaN count. -/
structure DoubleStats where
  lo : Option Int
  hi : Option Int
  nulls : Option Nat
  nans : Option Nat

/-- **Trusted:** what the writer's statistics mean for the column `c` of the
file's rows. Every value is NULL, NaN, or a code within the bounds, and a NaN
count of 0 means no NaN. Writers compare doubles as IEEE numbers, so the
bounds hold of canonical codes: `-0.0` is `0.0` (D31). A minimum is the code
of a double, so at most NaN's code. -/
structure DoubleStats.Correct (s : DoubleStats) (c : Nat) (rows : Relation) : Prop where
  vals : ∀ row ∈ rows, row.getD c .null = .null ∨
    (∃ x, row.getD c .null = .float x ∧ FloatCode.canon x = FloatCode.nan) ∨
    ∃ x, row.getD c .null = .float x ∧ (∀ l, s.lo = some l → l ≤ FloatCode.canon x) ∧
      (∀ h, s.hi = some h → FloatCode.canon x ≤ h)
  nulls : s.nulls = some 0 → ∀ row ∈ rows, row.getD c .null ≠ .null
  nans : s.nans = some 0 → ∀ row ∈ rows, ∀ x, row.getD c .null = .float x →
    FloatCode.canon x ≠ FloatCode.nan
  lo_le : ∀ l, s.lo = some l → l ≤ FloatCode.nan

/-- The bounds `sverify.io` takes from a double column: the minimum, and the
maximum only when the file counts no NaN (Delta counts none, so it never
takes Delta's double maxima). -/
def DoubleStats.colStats (s : DoubleStats) : ColStats :=
  ⟨s.lo, if s.nans = some 0 then s.hi else none, s.nulls, none⟩

omit [Boxes.Ambient] in
/-- **NaN and the bounds (#36).** The bounds `sverify.io` takes from a
double column's statistics are correct: NaN is above the minimum, and the
maximum is kept only where no NaN can exceed it. -/
theorem DoubleStats.colStats_correct {s : DoubleStats} {c : Nat} {rows : Relation}
    (h : s.Correct c rows) : s.colStats.Correct c rows := fun row hr => by
  have hnn := h.nulls
  simp only [ColStats.aval, colStats, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
    ite_false]
  rcases h.vals row hr with hv | hv | ⟨x, hv, hlo, hhi⟩
  · rw [hv]
    simp only [AVal.Mem, AVal.MemR]
    cases hn : s.nulls with
    | none => rfl
    | some n =>
        cases n with
        | zero => exact absurd hv (hnn hn row hr)
        | succ n => simp
  · obtain ⟨x, hv, hx⟩ := hv
    rw [hv]
    refine ⟨_, rfl, ⟨?_, ?_⟩, rfl⟩
    · intro l hl; rw [NumKind.norm_float, hx]; exact h.lo_le l hl
    · intro m hm
      split at hm
      · rename_i h0; exact absurd hx (h.nans h0 row hr x hv)
      · cases hm
  · rw [hv]
    refine ⟨_, rfl, ⟨hlo, ?_⟩, rfl⟩
    intro m hm
    split at hm
    · exact hhi m hm
    · cases hm

/-! ## Strings: bounds that may be prefixes -/

omit [Boxes.Ambient] in
theorem take_le_self : ∀ (l : List Char) (n : Nat), l.take n ≤ l
  | [], n => by simp
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
      simp only [List.take_succ_cons]
      exact List.cons_le_cons_iff.mpr (.inr ⟨rfl, take_le_self l n⟩)

omit [Boxes.Ambient] in
theorem take_mono : ∀ {a b : List Char} (n : Nat), a ≤ b → a.take n ≤ b.take n
  | [], b, n, _ => by simp
  | x :: a, [], n, h => by simp at h
  | x :: a, y :: b, 0, _ => by simp
  | x :: a, y :: b, n + 1, h => by
      simp only [List.take_succ_cons]
      rcases List.cons_le_cons_iff.mp h with h | ⟨rfl, h'⟩
      · exact List.le_of_lt (List.Lex.rel h)
      · exact List.cons_le_cons_iff.mpr (.inr ⟨rfl, take_mono n h'⟩)

/-- A string column's statistics: a minimum and a maximum, either of which
may be cut to a prefix. -/
structure StrStats where
  lo : Option String
  hi : Option String

/-- **Trusted:** what the statistics say about a string `x` of the column.
The minimum is at most `x`. The maximum is at least `x` cut to the
maximum's length: true of the greatest value, of any prefix of it (Delta's
truncation), and of anything above it (Iceberg increments a truncated
maximum). Strings compare by code point, which is UTF-8 byte order, the
order Parquet statistics use. -/
def StrStats.Correct (s : StrStats) (v : Value) : Prop :=
  ∀ x, v = .str x → (∀ l, s.lo = some l → l.toList ≤ x.toList) ∧
    (∀ h, s.hi = some h → x.toList.take h.toList.length ≤ h.toList)

/-- Whether some `x ≥ k` may be in the column. -/
def StrStats.mayGe (s : StrStats) (k : String) : Bool :=
  match s.hi with
  | some h => decide (k.toList.take h.toList.length ≤ h.toList)
  | none => true

/-- Whether some `x ≤ k` may be in the column. -/
def StrStats.mayLe (s : StrStats) (k : String) : Bool :=
  match s.lo with
  | some l => decide (l.toList ≤ k.toList)
  | none => true

/-- Whether some `x < k` may be in the column. -/
def StrStats.mayLt (s : StrStats) (k : String) : Bool :=
  match s.lo with
  | some l => decide (l.toList < k.toList)
  | none => true

omit [Boxes.Ambient] in
theorem StrStats.mayGe_sound {s : StrStats} {x k : String} (hs : s.Correct (.str x))
    (h : k.toList ≤ x.toList) : s.mayGe k = true := by
  unfold mayGe
  cases hh : s.hi with
  | none => rfl
  | some m =>
      exact decide_eq_true (List.le_trans (take_mono _ h) ((hs x rfl).2 m hh))

omit [Boxes.Ambient] in
theorem StrStats.mayLe_sound {s : StrStats} {x k : String} (hs : s.Correct (.str x))
    (h : x.toList ≤ k.toList) : s.mayLe k = true := by
  unfold mayLe
  cases hl : s.lo with
  | none => rfl
  | some l => exact decide_eq_true (List.le_trans ((hs x rfl).1 l hl) h)

omit [Boxes.Ambient] in
theorem StrStats.mayLt_sound {s : StrStats} {x k : String} (hs : s.Correct (.str x))
    (h : x.toList < k.toList) : s.mayLt k = true := by
  unfold mayLt
  cases hl : s.lo with
  | none => rfl
  | some l => exact decide_eq_true (List.lt_of_le_of_lt ((hs x rfl).1 l hl) h)

/-- The string bound of column `i`, if any. -/
def strAt (bs : Nat → Option StrStats) (i : Nat) (f : StrStats → Bool) : Bool :=
  match bs i with
  | some s => f s
  | none => true

/-- A comparison of column `i` with a string literal: whether the
statistics allow it to be TRUE. -/
def strCmp (bs : Nat → Option StrStats) : Expr → Bool
  | .bin .eq (.field i) (.lit (.str k)) => strAt bs i fun s => s.mayLe k && s.mayGe k
  | .bin .eq (.lit (.str k)) (.field i) => strAt bs i fun s => s.mayLe k && s.mayGe k
  | .bin .lt (.field i) (.lit (.str k)) => strAt bs i (·.mayLt k)
  | .bin .lt (.lit (.str k)) (.field i) => strAt bs i (·.mayGe k)
  | .un .not (.bin .lt (.field i) (.lit (.str k))) => strAt bs i (·.mayGe k)
  | .un .not (.bin .lt (.lit (.str k)) (.field i)) => strAt bs i (·.mayLe k)
  | _ => true

/-- Whether `e` may be TRUE on a row of a file with string bounds `bs`:
`AND` needs both sides, `OR` either, and a comparison of a column with a
string literal its bounds. -/
def StrStats.mayTrue (bs : Nat → Option StrStats) : Expr → Bool
  | .bin .and a b => mayTrue bs a && mayTrue bs b
  | .bin .or a b => mayTrue bs a || mayTrue bs b
  | e => strCmp bs e

omit [Boxes.Ambient] in
theorem strAt_sound {bs : Nat → Option StrStats} {row : Row}
    (hb : ∀ i s, bs i = some s → s.Correct (row.getD i .null)) {i : Nat} {f : StrStats → Bool}
    (h : ∀ s, s.Correct (row.getD i .null) → f s = true) : strAt bs i f = true := by
  unfold strAt
  cases hs : bs i with
  | none => rfl
  | some s => exact h s (hb i s hs)

omit [Boxes.Ambient] in
theorem isTrue_bool (b : Bool) : (Value.bool b).isTrue = b := by cases b <;> rfl

theorem eq_str_isTrue {v : Value} {k : String} (h : (BinFn.apply .eq v (.str k)).isTrue = true) :
    v = .str k := by
  cases v <;> simp only [BinFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

theorem str_eq_isTrue {v : Value} {k : String} (h : (BinFn.apply .eq (.str k) v).isTrue = true) :
    v = .str k := by
  cases v <;> simp only [BinFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

theorem lt_str_isTrue {v : Value} {k : String} (h : (BinFn.apply .lt v (.str k)).isTrue = true) :
    ∃ x, v = .str x ∧ x < k := by
  cases v <;> simp only [BinFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

theorem str_lt_isTrue {v : Value} {k : String} (h : (BinFn.apply .lt (.str k) v).isTrue = true) :
    ∃ x, v = .str x ∧ k < x := by
  cases v <;> simp only [BinFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

theorem not_lt_str_isTrue {v : Value} {k : String}
    (h : (UnFn.apply .not (BinFn.apply .lt v (.str k))).isTrue = true) :
    ∃ x, v = .str x ∧ ¬x < k := by
  cases v <;> simp only [BinFn.apply, UnFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

theorem not_str_lt_isTrue {v : Value} {k : String}
    (h : (UnFn.apply .not (BinFn.apply .lt (.str k) v)).isTrue = true) :
    ∃ x, v = .str x ∧ ¬k < x := by
  cases v <;> simp only [BinFn.apply, UnFn.apply, isTrue_bool] at h <;> simp_all [Value.isTrue]

omit [Boxes.Ambient] in
theorem string_not_lt {a b : String} (h : ¬a < b) : b.toList ≤ a.toList :=
  List.not_lt.mp fun h' => h (String.lt_iff.mpr h')

theorem strCmp_sound {bs : Nat → Option StrStats} {row : Row}
    (hb : ∀ i s, bs i = some s → s.Correct (row.getD i .null)) :
    ∀ e : Expr, (e.eval row).isTrue = true → strCmp bs e = true := by
  intro e ht
  unfold strCmp
  split
  · rename_i i k
    refine strAt_sound hb fun s hs => ?_
    have hv := eq_str_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    simp [StrStats.mayLe_sound hs (List.le_refl _), StrStats.mayGe_sound hs (List.le_refl _)]
  · rename_i k i
    refine strAt_sound hb fun s hs => ?_
    have hv := str_eq_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    simp [StrStats.mayLe_sound hs (List.le_refl _), StrStats.mayGe_sound hs (List.le_refl _)]
  · rename_i i k
    refine strAt_sound hb fun s hs => ?_
    obtain ⟨x, hv, hx⟩ := lt_str_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    exact StrStats.mayLt_sound hs (String.lt_iff.mp hx)
  · rename_i k i
    refine strAt_sound hb fun s hs => ?_
    obtain ⟨x, hv, hx⟩ := str_lt_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    exact StrStats.mayGe_sound hs (List.le_of_lt (String.lt_iff.mp hx))
  · rename_i i k
    refine strAt_sound hb fun s hs => ?_
    obtain ⟨x, hv, hx⟩ := not_lt_str_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    exact StrStats.mayGe_sound hs (string_not_lt hx)
  · rename_i k i
    refine strAt_sound hb fun s hs => ?_
    obtain ⟨x, hv, hx⟩ := not_str_lt_isTrue (v := row.getD i .null) ht
    rw [hv] at hs
    exact StrStats.mayLe_sound hs (string_not_lt hx)
  · rfl

/-- **Pruning by string bounds.** If `StrStats.mayTrue` says no, `e` is not
TRUE on the row. -/
theorem strPrune_sound {bs : Nat → Option StrStats} {row : Row}
    (hb : ∀ i s, bs i = some s → s.Correct (row.getD i .null)) :
    ∀ e : Expr, (e.eval row).isTrue = true → StrStats.mayTrue bs e = true
  | .lit _, ht | .field _, ht | .un _ _, ht | .ifThen _ _ _, ht | .hof _ _ _, ht => by
      simp only [StrStats.mayTrue]; exact strCmp_sound hb _ ht
  | .bin f a b, ht => by
      cases f
      case and =>
        simp only [Expr.eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
        simp [StrStats.mayTrue, strPrune_sound hb a ht.1, strPrune_sound hb b ht.2]
      case or =>
        simp only [Expr.eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht
        rcases ht with h | h
        · simp [StrStats.mayTrue, strPrune_sound hb a h]
        · simp [StrStats.mayTrue, strPrune_sound hb b h]
      all_goals (simp only [StrStats.mayTrue]; exact strCmp_sound hb _ ht)

/-- A file whose string bounds rule `e` out holds no row on which `e` is
TRUE. -/
theorem strStats_prune {bs : Nat → Option StrStats} {rows : Relation} (e : Expr)
    (hc : ∀ row ∈ rows, ∀ i s, bs i = some s → s.Correct (row.getD i .null))
    (hno : StrStats.mayTrue bs e = false) :
    rows.filter (fun r => (e.eval r).isTrue) = [] :=
  List.filter_eq_nil_iff.mpr fun row hr ht => by
    rw [strPrune_sound (hc row hr) e (by simpa using ht)] at hno
    cases hno

-- A maximum cut to a prefix: `'apple'` lies under `'app'` (it starts with
-- it), `'apq'` does not.
#guard (StrStats.mk none (some "app")).mayGe "apple"
#guard !(StrStats.mk none (some "app")).mayGe "apq"
-- `name = 'b'` in a file whose names lie in `'c'`…`'d…'` is ruled out, as is
-- `name < 'c'`; `name <= 'c'` is not.
#guard !StrStats.mayTrue (fun _ => some ⟨some "c", some "d"⟩)
    (.bin .eq (.field 0) (.lit (.str "b")))
#guard !StrStats.mayTrue (fun _ => some ⟨some "c", some "d"⟩)
    (.bin .lt (.field 0) (.lit (.str "c")))
#guard StrStats.mayTrue (fun _ => some ⟨some "c", some "d"⟩)
    (.un .not (.bin .lt (.lit (.str "c")) (.field 0)))

end Substrait
