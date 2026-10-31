import SubstraitLean.Compose

/-!
# Table formats: change feeds and file statistics

`sverify.io` reads Delta Lake and Iceberg tables. Two things it takes from
the table format are assumptions, stated here as explicit hypotheses:

* **Change feeds.** A Delta change data feed (or the files an Iceberg
  snapshot added) gives the change `Δ` between two versions of a table. The
  format is trusted to produce a `Δ` that turns the old snapshot into the new
  one: `(old ++ Δ).weight = new.weight` (`ChangeFeed`). Given that, the
  delta plans compute the change of every view (`Rel.cdf_sound`). When the
  feed is unavailable, `Δ = new - old` is computed from the two snapshots,
  and then the hypothesis is proved, not trusted (`ChangeFeed.of_diff`).
* **File statistics.** Each data file records per-column minimum, maximum,
  NULL count and row count. With correct statistics as a hypothesis
  (`ColStats.Correct`), the join of the files' bounds bounds the whole table
  (`stats_table`), and the bounds of the files an append added bound the
  appended rows. The facts stated from the join are `stats_bounds`,
  `stats_fact` and `stats_all_null`.

The views' results are compared by weight, not by `List.Perm`: a change feed
deletes and re-inserts rows, so `old ++ Δ` is not a permutation of `new`, but
it has the same weights, and Z-set evaluation only depends on the weights
(`Rel.zeval_weight_congr`).
-/

namespace Substrait

/-! ## Z-set evaluation only depends on weights -/

/-- `Σ g(row) · weight` over a Z-set. -/
def ZSet.lin (g : Row → Int) (z : ZSet) : Int := (List.map (fun x : Row × Int => g x.1 * x.2) z).sum

theorem ZSet.lin_nil (g : Row → Int) : ZSet.lin g [] = 0 := rfl

theorem ZSet.lin_cons (g : Row → Int) (x : Row × Int) (z : ZSet) :
    ZSet.lin g (x :: z) = g x.1 * x.2 + ZSet.lin g z := by
  simp [ZSet.lin]

theorem ZSet.lin_append (g : Row → Int) (a b : ZSet) :
    ZSet.lin g (a ++ b) = ZSet.lin g a + ZSet.lin g b := by
  simp [ZSet.lin]

theorem ZSet.weight_nil (r : Row) : ZSet.weight [] r = 0 := rfl

theorem ZSet.weight_cons (x : Row × Int) (z : ZSet) (r : Row) :
    ZSet.weight (x :: z) r = (if x.1 = r then x.2 else 0) + z.weight r := by
  simp only [ZSet.weight, List.filter_cons, beq_iff_eq]
  split <;> simp_all

theorem sum_map_add {L : List Row} (f h : Row → Int) :
    (L.map fun r => f r + h r).sum = (L.map f).sum + (L.map h).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_zero {L : List Row} : (L.map fun _ => (0 : Int)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

theorem sum_indicator_out {L : List Row} {a : Row} (ha : a ∉ L) (f : Row → Int) :
    (L.map fun r => if a = r then f r else 0).sum = 0 := by
  induction L with
  | nil => rfl
  | cons b L ih =>
      simp only [List.mem_cons, not_or] at ha
      simp [ha.1, ih ha.2]

theorem sum_indicator {L : List Row} (hL : L.Nodup) {a : Row} (ha : a ∈ L) (f : Row → Int) :
    (L.map fun r => if a = r then f r else 0).sum = f a := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
      rw [List.nodup_cons] at hL
      simp only [List.map_cons, List.sum_cons]
      by_cases h : a = b
      · subst h; simp [sum_indicator_out hL.1]
      · simp only [h, ite_false, Int.zero_add]
        exact ih hL.2 ((List.mem_cons.mp ha).resolve_left h)

/-- `lin g z` is a sum over any duplicate-free list of rows covering `z`. -/
theorem ZSet.lin_support (g : Row → Int) :
    ∀ (z : ZSet) {L : List Row}, L.Nodup → (∀ x ∈ z, x.1 ∈ L) →
      ZSet.lin g z = (L.map fun r => g r * ZSet.weight z r).sum
  | [], L, _, _ => by simp [ZSet.lin_nil, ZSet.weight_nil, sum_map_zero]
  | x :: z, L, hL, hz => by
      have hrest := ZSet.lin_support g z hL (fun y hy => hz y (List.mem_cons_of_mem _ hy))
      have hsplit : (L.map fun r => g r * ZSet.weight (x :: z) r) =
          L.map fun r => (if x.1 = r then g r * x.2 else 0) + g r * ZSet.weight z r := by
        refine List.map_congr_left fun r _ => ?_
        rw [ZSet.weight_cons]; split <;> simp [Int.mul_add]
      rw [ZSet.lin_cons, hsplit, sum_map_add, hrest,
        sum_indicator hL (hz x List.mem_cons_self) (fun r => g r * x.2)]

theorem nodup_eraseDups : ∀ (l : List Row), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.2 ⟨fun h => ?_, nodup_eraseDups _⟩
      rw [List.mem_eraseDups, List.mem_filter] at h
      simp at h
termination_by l => l.length
decreasing_by simp; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- **Linear functionals only see weights.** -/
theorem ZSet.lin_congr (g : Row → Int) {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r) :
    ZSet.lin g z = ZSet.lin g z' := by
  let L := (List.map (·.1) z ++ List.map (·.1) z').eraseDups
  have hL : L.Nodup := nodup_eraseDups _
  have hz : ∀ x ∈ z, x.1 ∈ L := fun x hx => by
    simp only [L, List.mem_eraseDups, List.mem_append, List.mem_map]; exact .inl ⟨x, hx, rfl⟩
  have hz' : ∀ x ∈ z', x.1 ∈ L := fun x hx => by
    simp only [L, List.mem_eraseDups, List.mem_append, List.mem_map]; exact .inr ⟨x, hx, rfl⟩
  rw [ZSet.lin_support g z hL hz, ZSet.lin_support g z' hL hz']
  exact congrArg List.sum (List.map_congr_left fun r _ => by rw [h r])

theorem ZSet.weight_eq_lin (z : ZSet) (r : Row) :
    z.weight r = ZSet.lin (fun s => if s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih => rw [ZSet.weight_cons, ZSet.lin_cons, ih]; split <;> simp

theorem ZSet.weight_perm {z z' : ZSet} (h : z.Perm z') (r : Row) : z.weight r = z'.weight r := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [ZSet.weight_cons, ZSet.weight_cons, ih]
  | swap x y z => rw [ZSet.weight_cons, ZSet.weight_cons, ZSet.weight_cons, ZSet.weight_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem ZSet.weight_filter (p : Row → Bool) (z : ZSet) (r : Row) :
    (ZSet.filter p z).weight r = ZSet.lin (fun s => if p s ∧ s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      simp only [ZSet.filter, List.filter_cons] at ih ⊢
      rw [ZSet.lin_cons, ← ih]
      by_cases hp : p x.1 <;> simp only [hp, ite_true, ZSet.weight_cons] <;> split <;>
        simp_all

theorem ZSet.weight_map (f : Row → Row) (z : ZSet) (r : Row) :
    (ZSet.map f z).weight r = ZSet.lin (fun s => if f s = r then 1 else 0) z := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      simp only [ZSet.map, List.map_cons] at ih ⊢
      rw [ZSet.weight_cons, ZSet.lin_cons, ← ih]; split <;> simp

theorem ZSet.weight_cross (a b : ZSet) (r : Row) :
    (ZSet.cross a b).weight r =
      ZSet.lin (fun xa => ZSet.lin (fun xb => if xa ++ xb = r then 1 else 0) b) a := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      simp only [ZSet.cross, List.flatMap_cons] at ih ⊢
      rw [ZSet.weight_append, ih, ZSet.lin_cons]
      congr 1
      clear ih
      induction b with
      | nil => simp [ZSet.weight_nil, ZSet.lin_nil]
      | cons y b ihb =>
          rw [List.map_cons, ZSet.weight_cons, ihb, ZSet.lin_cons]
          split <;> simp [Int.mul_add, Int.mul_comm]

theorem ZSet.weight_mergeSort (le : Row × Int → Row × Int → Bool) (z : ZSet) (r : Row) :
    ZSet.weight (z.mergeSort le) r = z.weight r :=
  ZSet.weight_perm (List.mergeSort_perm z le) r

/-- Two Z-catalogs agree on a table when the table's rows have the same weights. -/
def ZCatalog.SameWeights (cat cat' : ZCatalog) (ts : List String) : Prop :=
  ∀ t ∈ ts, ∀ row, (cat t).weight row = (cat' t).weight row

/-- **Views only depend on weights.** On the incremental fragment, Z-set
evaluation on catalogs whose tables have the same weights gives results
with the same weights. -/
theorem Rel.zeval_weight_congr {cat cat' : ZCatalog} :
    ∀ {r : Rel}, r.Incremental → cat.SameWeights cat' r.tables →
      ∀ row, (r.zeval cat).weight row = (r.zeval cat').weight row
  | .read t, _, h, row => h t (by simp [tables]) row
  | .values _ _, _, _, _ => rfl
  | .filter r c, hr, h, row => by
      simp only [zeval, ZSet.weight_filter]
      exact ZSet.lin_congr _ (zeval_weight_congr (r := r) hr h)
  | .project r es, hr, h, row => by
      simp only [zeval, ZSet.weight_map]
      exact ZSet.lin_congr _ (zeval_weight_congr (r := r) hr h)
  | .emit r m, hr, h, row => by
      simp only [zeval, ZSet.weight_map]
      exact ZSet.lin_congr _ (zeval_weight_congr (r := r) hr h)
  | .orderBy r keys, hr, h, row => by
      rw [zeval, zeval, ZSet.weight_mergeSort, ZSet.weight_mergeSort]
      exact zeval_weight_congr (r := r) hr h row
  | .unionAll a b, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [zeval, ZSet.weight_append, zeval_weight_congr hr.1 ha, zeval_weight_congr hr.2 hb]
  | .cross a b, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [zeval, ZSet.weight_cross]
      rw [ZSet.lin_congr _ (zeval_weight_congr hr.1 ha)]
      exact congrArg List.sum (List.map_congr_left fun x _ => by
        simp only []; rw [ZSet.lin_congr _ (zeval_weight_congr hr.2 hb)])
  | .join a b .inner on, hr, h, row => by
      have ha : cat.SameWeights cat' a.tables := fun t ht => h t (by simp [tables, ht])
      have hb : cat.SameWeights cat' b.tables := fun t ht => h t (by simp [tables, ht])
      simp only [zeval, ZSet.weight_filter]
      refine ZSet.lin_congr _ fun s => ?_
      simp only [ZSet.weight_cross]
      rw [ZSet.lin_congr _ (zeval_weight_congr hr.1 ha)]
      exact congrArg List.sum (List.map_congr_left fun x _ => by
        simp only []; rw [ZSet.lin_congr _ (zeval_weight_congr hr.2 hb)])
  | .join _ _ .left _, hr, _, _ => hr.elim
  | .fetch _ _ _, hr, _, _ | .window _ _ _ _, hr, _, _ | .semi _ _ _ _, hr, _, _
  | .distinct _, hr, _, _ => hr.elim

/-! ## Change feeds -/

/-- What the table format is trusted to deliver: a change `Δ` that turns
the old snapshot of every table into the new one, up to weights (a change
feed may delete and re-insert a row). -/
def ChangeFeed (old Δ new : ZCatalog) (ts : List String) : Prop :=
  (old + Δ).SameWeights new ts

/-- The fallback when the feed is unavailable: the difference of the two
snapshots is a correct change, so `ChangeFeed` is then proved. -/
theorem ChangeFeed.of_diff (old new : ZCatalog) (ts : List String) :
    ChangeFeed old (fun t => new t ++ (old t).neg) new ts :=
  fun t _ row => by rw [ZCatalog.add_apply]; exact ZSet.diff_correct _ _ row

/-- **Maintaining a view from a change feed.** If the feed is correct
(`ChangeFeed`, trusted for Delta CDF and Iceberg appends) and the engine
catalog `C` holds the old tables and the feed as change tables (`hδ` of
`Rel.delta_correct`), then the old view plus the output of the delta plan
has the weights of the view on the new snapshot. -/
theorem Rel.cdf_sound {C old Δ new : ZCatalog} {δ : String → String} {V : Rel}
    (hV : V.Incremental) (hfeed : ChangeFeed old Δ new V.tables)
    (hold : ∀ t ∈ V.tables, C t = old t) (hδ : ∀ t ∈ V.tables, C (δ t) = Δ t) (row : Row) :
    (V.zeval new).weight row = (V.zeval old ++ (V.delta δ).zeval C).weight row := by
  rw [← zeval_weight_congr hV hfeed row]
  exact ZSet.weight_perm (Rel.incremental_sound hV hold hδ) row

/-! ## File statistics -/

/-- One data file's statistics for one column: minimum and maximum (of the
integer codes of numbers, doubles, dates and timestamps), NULL count and row
count; `none` is unknown. -/
structure ColStats where
  lo : Option Int
  hi : Option Int
  nulls : Option Nat
  rows : Option Nat := none

/-- What the statistics say about a value of the column: NULL unless the
NULL count is 0, and a number between the bounds unless every row is NULL. -/
def ColStats.aval (s : ColStats) : AVal :=
  ⟨s.nulls != some 0, if s.rows.isSome && s.nulls == s.rows then none else some ⟨s.lo, s.hi⟩,
   false, false, false⟩

/-- **Trusted:** the statistics describe column `c` of the file's rows. (A
format that truncates maxima, like Delta for timestamps, is correct only
after the maximum is widened by the truncated amount.)

Statistics that describe a *superset* of the rows are still correct: a file
with Delta deletion vectors or Iceberg delete files keeps the statistics of
all its physical rows. Every property here is preserved by removing rows
(the bounds still bound, a NULL count of 0 stays 0, a column whose physical
rows are all NULL stays all NULL), as long as the row count and the NULL
count describe the same rows.

Doubles: the writers leave NaN out of minimum and maximum, and NaN is the
greatest code (`FloatCode`), so a minimum stays correct with NaNs in the file
but a maximum only if the file has none (Iceberg's NaN count; Delta has none,
so `sverify.io` leaves Delta's double maxima out). -/
def ColStats.Correct (s : ColStats) (c : Nat) (rows : Relation) : Prop :=
  ∀ row ∈ rows, s.aval.Mem (row.getD c .null)

/-- The table's bound for a column: the join of its files' bounds. -/
def tableStats (files : List (Relation × ColStats)) : AVal :=
  files.foldr (fun f a => f.2.aval.join a) AVal.bot

/-- **Per-file bounds bound the table**: with correct statistics for every
file, every row of the table (the files' rows together) lies in the join of
the files' bounds. -/
theorem stats_table {c : Nat} :
    ∀ {files : List (Relation × ColStats)}, (∀ f ∈ files, f.2.Correct c f.1) →
      ∀ row ∈ files.flatMap (·.1), (tableStats files).Mem (row.getD c .null)
  | [], _, row, h => by simp at h
  | f :: fs, hc, row, h => by
      simp only [List.flatMap_cons, List.mem_append] at h
      simp only [tableStats, List.foldr_cons]
      rcases h with h | h
      · exact AVal.mem_join_left (hc f List.mem_cons_self row h)
      · exact AVal.mem_join_right
          (stats_table (fun g hg => hc g (List.mem_cons_of_mem _ hg)) row h)

/-- **Appends**: rows an append inserted lie in the files it added, so the
added files' bounds bound them, whatever the old files say. -/
theorem stats_append {c : Nat} {added : List (Relation × ColStats)} {ins : Relation}
    (hc : ∀ f ∈ added, f.2.Correct c f.1) (hins : ∀ row ∈ ins, row ∈ added.flatMap (·.1)) :
    ∀ row ∈ ins, (tableStats added).Mem (row.getD c .null) :=
  fun row h => stats_table hc row (hins row h)

/-- The facts `sverify.io` states from the table's bound: a column without
NULLs whose files all have both bounds is a non-NULL integer between the
least minimum and the greatest maximum. -/
theorem stats_bounds {a : AVal} {lo hi : Int} {v : Value}
    (hnull : a.null = false) (hint : a.int = some ⟨some lo, some hi⟩)
    (hb : a.tt = false ∧ a.ff = false ∧ a.str = false) (hm : a.Mem v) :
    ∃ i, v = .int i ∧ lo ≤ i ∧ i ≤ hi := by
  cases v with
  | null => simp_all [AVal.Mem]
  | int i =>
      obtain ⟨b, hb', hmem⟩ := hm
      rw [hint] at hb'; cases hb'
      simp only [Bound.Mem] at hmem
      exact ⟨i, rfl, hmem.1 lo rfl, hmem.2 hi rfl⟩
  | bool b => cases b <;> simp_all [AVal.Mem]
  | str _ => simp_all [AVal.Mem]

/-- The fact `sverify.io` states from a table's bound in general: a value is
NULL (only if some file has NULLs) or a number within the bound `b`, each side
of which may be missing (a minimum or maximum some file lacks, a double's
maximum where NaN may occur). With NULLs this is the fact
`c IS NULL OR (c >= lo AND c <= hi)`, which the checker reads as one column
description (`Expr.refine` of `IS NULL` and of `OR`). -/
theorem stats_fact {a : AVal} {b : Bound} {v : Value}
    (hint : a.int = some b) (hb : a.tt = false ∧ a.ff = false ∧ a.str = false) (hm : a.Mem v) :
    (v = .null ∧ a.null = true) ∨ ∃ i, v = .int i ∧ b.Mem i := by
  cases v with
  | null => exact .inl ⟨rfl, hm⟩
  | int i =>
      obtain ⟨b', hb', hmem⟩ := hm
      rw [hint] at hb'; cases hb'
      exact .inr ⟨i, rfl, hmem⟩
  | bool b => cases b <;> simp_all [AVal.Mem]
  | str _ => simp_all [AVal.Mem]

/-- A column whose files are all entirely NULL (NULL count = row count) is
NULL: the fact `c IS NULL`. -/
theorem stats_all_null {a : AVal} {v : Value}
    (hint : a.int = none) (hb : a.tt = false ∧ a.ff = false ∧ a.str = false) (hm : a.Mem v) :
    v = .null := by
  cases v with
  | null => rfl
  | int i => obtain ⟨_, h, _⟩ := hm; simp [hint] at h
  | bool b => cases b <;> simp_all [AVal.Mem]
  | str _ => simp_all [AVal.Mem]

-- The join of known bounds is the least minimum and the greatest maximum.
#guard tableStats [([], ⟨some 3, some 9, some 0, none⟩), ([], ⟨some 1, some 5, some 0, none⟩)] ==
    ⟨false, some ⟨some 1, some 9⟩, false, false, false⟩
-- A file of NULLs adds NULL and no bound; a file without a maximum loses it.
#guard tableStats [([], ⟨some 3, some 9, some 0, none⟩), ([], ⟨none, none, some 4, some 4⟩)] ==
    ⟨true, some ⟨some 3, some 9⟩, false, false, false⟩
#guard tableStats [([], ⟨some 3, some 9, some 1, some 5⟩), ([], ⟨some 1, none, some 0, none⟩)] ==
    ⟨true, some ⟨some 1, none⟩, false, false, false⟩

end Substrait
