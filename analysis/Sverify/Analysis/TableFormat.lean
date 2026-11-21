import Sverify.Analysis.Compose

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
  and then the hypothesis is proved, not trusted (`ChangeFeed.of_diff`); on
  Iceberg, only from the files that changed (`ChangeFeed.of_changed_files`).
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

variable [Boxes.Ambient]

/-! ## Change feeds -/

/-- What the table format is trusted to deliver: a change `Δ` that turns
the old snapshot of every table into the new one, up to weights (a change
feed may delete and re-insert a row). -/
def ChangeFeed (old Δ new : ZCatalog) (ts : List String) : Prop :=
  (old + Δ).SameWeights new ts

omit [Boxes.Ambient] in
/-- The fallback when the feed is unavailable: the difference of the two
snapshots is a correct change, so `ChangeFeed` is then proved. -/
theorem ChangeFeed.of_diff (old new : ZCatalog) (ts : List String) :
    ChangeFeed old (fun t => new t ++ (old t).neg) new ts :=
  fun t _ row => by rw [ZCatalog.add_apply]; exact ZSet.diff_correct _ _ row

omit [Boxes.Ambient] in
/-- The Iceberg reader's diff of only the changed files: if both snapshots
consist of the same unchanged files `U` (same weights) plus the files that
changed (`A` before, `B` after), then `B - A` is a correct change. Reading
`B` and `A` is all it takes. Trusted: a data file with the same path and the
same delete files has the same rows in both snapshots (Iceberg files are
immutable). -/
theorem ChangeFeed.of_changed_files {old new U A B : ZCatalog} {ts : List String}
    (hold : ∀ t ∈ ts, ∀ r, (old t).weight r = (U t ++ A t).weight r)
    (hnew : ∀ t ∈ ts, ∀ r, (new t).weight r = (U t ++ B t).weight r) :
    ChangeFeed old (fun t => B t ++ (A t).neg) new ts := fun t ht r => by
  rw [ZCatalog.add_apply, WSet.weight_append, hold t ht r, hnew t ht r]
  simp only [WSet.weight_append, ZSet.weight_neg]
  omega

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
  exact WSet.weight_perm (Rel.incremental_sound hV hold hδ) row

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
  { null := s.nulls != some 0,
    int := if s.rows.isSome && s.nulls == s.rows then none else some ⟨s.lo, s.hi⟩ }

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

omit [Boxes.Ambient] in
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

omit [Boxes.Ambient] in
/-- **Appends**: rows an append inserted lie in the files it added, so the
added files' bounds bound them, whatever the old files say. -/
theorem stats_append {c : Nat} {added : List (Relation × ColStats)} {ins : Relation}
    (hc : ∀ f ∈ added, f.2.Correct c f.1) (hins : ∀ row ∈ ins, row ∈ added.flatMap (·.1)) :
    ∀ row ∈ ins, (tableStats added).Mem (row.getD c .null) :=
  fun row h => stats_table hc row (hins row h)

omit [Boxes.Ambient] in
/-- The facts `sverify.io` states from the table's bound: a column without
NULLs whose files all have both bounds is a non-NULL number between the
least minimum and the greatest maximum. -/
theorem stats_bounds {a : AVal} {lo hi : Int} {v : Value}
    (hnull : a.null = false) (hint : a.int = some ⟨some lo, some hi⟩)
    (hb : a.intsOnly = true) (hm : a.Mem v) :
    ∃ (k : NumKind) (i : Int), v = k.val i ∧ lo ≤ k.norm i ∧ k.norm i ≤ hi := by
  simp only [AVal.intsOnly, AVal.nested, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff] at hb
  rcases AVal.mem_cases hm with ⟨_, hn⟩ | ⟨k, i, b, rfl, hb', hmem, -⟩ | ⟨_, ht⟩ | ⟨_, hf⟩ |
      ⟨_, _, hs, _⟩ | ⟨_, _, ht⟩
  · simp_all
  · rw [hint] at hb'; cases hb'
    exact ⟨k, i, rfl, hmem.1 lo rfl, hmem.2 hi rfl⟩
  all_goals simp_all [AVal.nested]

omit [Boxes.Ambient] in
/-- The fact `sverify.io` states from a table's bound in general: a value is
NULL (only if some file has NULLs) or a number within the bound `b`, each side
of which may be missing (a minimum or maximum some file lacks, a double's
maximum where NaN may occur). With NULLs this is the fact
`c IS NULL OR (c >= lo AND c <= hi)`, which the checker reads as one column
description (`Expr.refine` of `IS NULL` and of `OR`). -/
theorem stats_fact {a : AVal} {b : Bound} {v : Value}
    (hint : a.int = some b) (hb : a.intsOnly = true) (hm : a.Mem v) :
    (v = .null ∧ a.null = true) ∨ ∃ (k : NumKind) (i : Int), v = k.val i ∧ b.Mem (k.norm i) := by
  simp only [AVal.intsOnly, AVal.nested, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff] at hb
  rcases AVal.mem_cases hm with ⟨rfl, hn⟩ | ⟨k, i, b', rfl, hb', hmem, -⟩ | ⟨_, ht⟩ | ⟨_, hf⟩ |
      ⟨_, _, hs, _⟩ | ⟨_, _, ht⟩
  · exact .inl ⟨rfl, hn⟩
  · rw [hint] at hb'; cases hb'
    exact .inr ⟨k, i, rfl, hmem⟩
  all_goals simp_all [AVal.nested]

omit [Boxes.Ambient] in
/-- A column whose files are all entirely NULL (NULL count = row count) is
NULL: the fact `c IS NULL`. -/
theorem stats_all_null {a : AVal} {v : Value}
    (hint : a.int = none) (hb : a.intsOnly = true) (hm : a.Mem v) :
    v = .null := by
  simp only [AVal.intsOnly, AVal.nested, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff] at hb
  rcases AVal.mem_cases hm with ⟨rfl, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨_, ht⟩ | ⟨_, hf⟩ |
      ⟨_, _, hs, _⟩ | ⟨_, _, ht⟩
  · rfl
  all_goals simp_all [AVal.nested]

/-! ## Pruning files -/

/-- **Pruning files by their statistics.** A table is its files' rows
together. Mark each file `true` to read it; a file may be skipped only if no
row of it makes the filter `e` TRUE. `sverify.io` skips a file when the
contract checker proves "`e` is not TRUE" from the facts the file's
statistics give (`contract_sound`, with `stats_table` for one file). Then
filtering only the files read gives the same rows, in the same order, as
filtering the whole table. -/
theorem prune_sound (e : Expr) :
    ∀ {files : List (Relation × Bool)},
      (∀ f ∈ files, f.2 = false → ∀ row ∈ f.1, (e.eval row).isTrue = false) →
      (files.flatMap (·.1)).filter (fun r => (e.eval r).isTrue) =
        ((files.filter (·.2)).flatMap (·.1)).filter (fun r => (e.eval r).isTrue)
  | [], _ => rfl
  | f :: fs, h => by
      have ih := prune_sound e (files := fs) fun g hg => h g (List.mem_cons_of_mem _ hg)
      cases hf : f.2
      · have hnone : f.1.filter (fun r => (e.eval r).isTrue) = [] :=
          List.filter_eq_nil_iff.mpr fun row hr => by
            simp [h f List.mem_cons_self hf row hr]
        simp [hf, List.filter_append, hnone, ih]
      · simp [hf, List.filter_append, ih]

-- The join of known bounds is the least minimum and the greatest maximum.
#guard tableStats [([], ⟨some 3, some 9, some 0, none⟩), ([], ⟨some 1, some 5, some 0, none⟩)] ==
    { int := some ⟨some 1, some 9⟩ }
-- A file of NULLs adds NULL and no bound; a file without a maximum loses it.
#guard tableStats [([], ⟨some 3, some 9, some 0, none⟩), ([], ⟨none, none, some 4, some 4⟩)] ==
    { null := true, int := some ⟨some 3, some 9⟩ }
#guard tableStats [([], ⟨some 3, some 9, some 1, some 5⟩), ([], ⟨some 1, none, some 0, none⟩)] ==
    { null := true, int := some ⟨some 1, none⟩ }

end Substrait
