import SubstraitLean.Partition
import SubstraitLean.Time

/-!
# Retention: bounded state for time buckets (#294)

An incremental view that groups by a time bucket, such as
`GROUP BY date_trunc('hour', ts)`, keeps a row per bucket it has seen. With a
bound on how late rows arrive (`sv.arrives_within("ts", hours=2)`: a changed
row's `ts` is at least the watermark, the largest `ts` seen so far minus the
lateness), a bucket that ends at or before the watermark is **final**: no
later batch changes it. The view drops a final bucket's rows from its state,
and they stay in the sink.

* `aggregateEval_filter_key`: an aggregate's output rows whose group key
  satisfies `p` are the aggregate of the input rows whose key satisfies `p`.
* `final_unchanged`: under the lateness precondition, the output rows of the
  final buckets are the same before and after a batch, for every measure:
  their delta is empty.
* `retention_sound`: the final rows kept in the sink, plus the open rows
  recomputed after the batch, are the full recomputation.
* `final_stable`: the same over any stream of admissible batches.
* `expiry_sound`: a batch may also delete rows of final buckets, the
  source's own retention; the sink keeps them, and the open rows are as
  without those deletes.
* `open_buckets_le`: at most `⌈lateness / width⌉ + 1` buckets are open, the
  bound #219's state bound builds on.

Time is an integer (microseconds, as `Time.trunc` takes it), `ts` gives an
input row's time, and the view reads its bucket from the group key
(`bucketOf`): the `W`-wide bucket of `ts` counted from an origin
(`Time.bucket`, which is `date_bin`), or `date_trunc` to a microsecond,
millisecond, second, minute, hour or day (`trunc_eq_bucket`).

The Python glue (`sverify._retention`) recognises such views, checks the
precondition on every batch, and drops the final buckets' rows from the
state once every sink has written them.
-/

namespace Substrait
namespace Retention

/-! ## Fixed-width buckets -/

open Time (floorTo bucket trunc TimeUnit)

theorem floorTo_le {W : Int} (hW : 0 < W) (t : Int) : floorTo W t ≤ t := by
  have h1 := Int.emod_def t W
  have h2 := Int.emod_nonneg t (Int.ne_of_gt hW)
  unfold floorTo
  rw [Int.mul_comm]
  omega

theorem lt_floorTo_add {W : Int} (hW : 0 < W) (t : Int) : t < floorTo W t + W := by
  have h1 := Int.emod_def t W
  have h2 := Int.emod_lt_of_pos t hW
  unfold floorTo
  rw [Int.mul_comm]
  omega

theorem bucket_le {W : Int} (hW : 0 < W) (o t : Int) : bucket W.toNat o t ≤ t := by
  have := floorTo_le hW (t - o)
  simp only [bucket, Int.toNat_of_nonneg (Int.le_of_lt hW)]; omega

theorem lt_bucket_add {W : Int} (hW : 0 < W) (o t : Int) : t < bucket W.toNat o t + W := by
  have := lt_floorTo_add hW (t - o)
  simp only [bucket, Int.toNat_of_nonneg (Int.le_of_lt hW)]; omega

/-- The width of the units `date_trunc` truncates to without a calendar. -/
def width : TimeUnit → Option Nat
  | .microsecond => some 1 | .millisecond => some 1000 | .second => some 1_000_000
  | .minute => some 60_000_000 | .hour => some 3_600_000_000 | .day => some 86_400_000_000
  | .week | .month | .quarter | .year => none

/-- `date_trunc` to such a unit is a bucket from 1970-01-01. -/
theorem trunc_eq_bucket {u : TimeUnit} {w : Nat} (h : width u = some w) (t : Int) :
    trunc u t = bucket w 0 t := by
  cases u <;> simp only [width, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [trunc, bucket, floorTo, Time.usPerDay]

/-- A bucket starting at `b` ends at or before the watermark `wm`. -/
def final (W wm b : Int) : Bool := decide (b + W ≤ wm)

/-- A later watermark leaves a final bucket final. -/
theorem final_mono {W wm wm' b : Int} (h : wm ≤ wm') (hf : final W wm b = true) :
    final W wm' b = true := by
  simp only [final, decide_eq_true_eq] at *; omega

/-! ## Aggregates restricted to some groups -/

theorem groupKey_length (gs : List Expr) (row : Row) : (groupKey gs row).length = gs.length := by
  simp [groupKey]

theorem dedup_filter_perm {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) :
    (dedup (l.filter p)).Perm ((dedup l).filter p) :=
  (List.perm_ext_iff_of_nodup (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise _))
    ((List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l)).filter p)).mpr fun y => by
      simp only [mem_dedup, List.mem_filter]

/-- **Groups are independent**: the output rows of an aggregate whose group
key satisfies `p` are the aggregate of the input rows whose key does. -/
theorem aggregateEval_filter_key {gs : List Expr} (hg : gs ≠ []) (ms : List Measure)
    (p : Row → Bool) (rows : Relation) :
    ((aggregateEval gs ms rows).filter fun out => p (out.take gs.length)).Perm
      (aggregateEval gs ms (rows.filter fun r => p (groupKey gs r))) := by
  have hge : gs.isEmpty = false := by simpa using hg
  simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_map]
  have hkeys : ((rows.filter fun r => p (groupKey gs r)).map (groupKey gs)) =
      (rows.map (groupKey gs)).filter p := by
    rw [List.filter_map]; rfl
  rw [hkeys]
  refine List.Perm.trans ?_ ((dedup_filter_perm p _).map _).symm
  refine .of_eq ?_
  rw [List.filter_congr (p := (fun out : Row => p (out.take gs.length)) ∘
      (fun k => k ++ ms.map (·.eval (groupRows gs rows k)))) (q := p) ?_]
  · refine List.map_congr_left fun k hk => ?_
    have hpk := (List.mem_filter.mp hk).2
    congr 2
    funext m
    congr 1
    simp only [groupRows, List.filter_filter]
    refine List.filter_congr fun r _ => ?_
    by_cases he : groupKey gs r = k
    · subst he; simp [hpk]
    · simp [he]
  · intro k hk
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
    simp [List.take_left' (groupKey_length gs r)]

/-! ## Batches that respect the lateness -/

/-- A batch: deletes (one copy each) and inserts. -/
def applyBatch (rows dels ins : Relation) : Relation := dels.foldl List.erase rows ++ ins

/-- Every row the batch inserts or deletes is at or after the watermark. -/
def Admissible (ts : Row → Int) (wm : Int) (dels ins : Relation) : Prop :=
  ∀ r ∈ dels ++ ins, wm ≤ ts r

theorem filter_erase_of_false {p : Row → Bool} {a : Row} (ha : p a = false) :
    ∀ l : Relation, (l.erase a).filter p = l.filter p
  | [] => rfl
  | x :: xs => by
    by_cases hx : x = a
    · subst hx; simp [ha]
    · have : (x == a) = false := by simpa using hx
      simp only [List.erase_cons, this, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      rw [filter_erase_of_false ha xs]

theorem filter_foldl_erase {p : Row → Bool} :
    ∀ (dels : Relation) (rows : Relation), (∀ d ∈ dels, p d = false) →
      (dels.foldl List.erase rows).filter p = rows.filter p
  | [], _, _ => rfl
  | d :: ds, rows, h => by
    simp only [List.foldl_cons]
    rw [filter_foldl_erase ds _ fun x hx => h x (.tail _ hx),
      filter_erase_of_false (h d (.head _))]

/-- An admissible batch leaves the rows before the watermark as they were. -/
theorem early_unchanged {ts : Row → Int} {wm : Int} {rows dels ins : Relation}
    (h : Admissible ts wm dels ins) :
    (applyBatch rows dels ins).filter (fun r => decide (ts r < wm)) =
      rows.filter (fun r => decide (ts r < wm)) := by
  have hd : ∀ d ∈ dels, decide (ts d < wm) = false := fun d hd => by
    have := h d (List.mem_append_left _ hd); simp; omega
  have hi : ins.filter (fun r => decide (ts r < wm)) = [] :=
    List.filter_eq_nil_iff.mpr fun r hr => by
      have := h r (List.mem_append_right _ hr); simp; omega
  simp only [applyBatch, List.filter_append, hi, List.append_nil]
  exact filter_foldl_erase dels rows hd

/-! ## Final buckets do not change -/

variable {gs : List Expr} {ms : List Measure} {ts : Row → Int} {bucketOf : Row → Int}
  {W o wm : Int}

/-- The output rows of the final buckets (`keep = true`), or of the open ones. -/
def rowsOf (gs : List Expr) (bucketOf : Row → Int) (W wm : Int) (keep : Bool)
    (out : Relation) : Relation :=
  out.filter fun o => final W wm (bucketOf (o.take gs.length)) == keep

/-- The bucket of every input row is the `W`-wide bucket of its time,
counted from `o` (`date_bin`, or `date_trunc` by `trunc_eq_bucket`). -/
def Tumbling (gs : List Expr) (ts : Row → Int) (bucketOf : Row → Int) (W o : Int) : Prop :=
  ∀ r, bucketOf (groupKey gs r) = bucket W.toNat o (ts r)

/-- **The delta of a final bucket is empty**: under the lateness
precondition, the aggregate's rows for the buckets that are final at the
watermark are the same after the batch, for every measure. -/
theorem final_unchanged (hg : gs ≠ []) (hW : 0 < W) (ht : Tumbling gs ts bucketOf W o)
    {rows dels ins : Relation} (h : Admissible ts wm dels ins) :
    (rowsOf gs bucketOf W wm true (aggregateEval gs ms (applyBatch rows dels ins))).Perm
      (rowsOf gs bucketOf W wm true (aggregateEval gs ms rows)) := by
  let p : Row → Bool := fun k => final W wm (bucketOf k) == true
  refine (aggregateEval_filter_key hg ms p _).trans
    (List.Perm.trans (.of_eq ?_) (aggregateEval_filter_key hg ms p rows).symm)
  -- A row of a final bucket is before the watermark.
  have hq : ∀ r, p (groupKey gs r) = true → decide (ts r < wm) = true := fun r hr => by
    simp only [p, final, ht r, beq_iff_eq, decide_eq_true_eq] at hr
    have := lt_bucket_add hW o (ts r)
    simp; omega
  have hsplit : ∀ xs : Relation, xs.filter (fun r => p (groupKey gs r)) =
      (xs.filter fun r => decide (ts r < wm)).filter (fun r => p (groupKey gs r)) := by
    intro xs
    rw [List.filter_filter]
    refine List.filter_congr fun r _ => ?_
    by_cases hp : p (groupKey gs r) = true
    · simp [hp, hq r hp]
    · simp [hp]
  rw [hsplit, hsplit rows, early_unchanged h]

/-- **Dropping final buckets is sound**: the final rows, kept in the sink
from before the batch, and the open rows recomputed after it are the full
recomputation after the batch. -/
theorem retention_sound (hg : gs ≠ []) (hW : 0 < W) (ht : Tumbling gs ts bucketOf W o)
    {rows dels ins : Relation} (h : Admissible ts wm dels ins) :
    (aggregateEval gs ms (applyBatch rows dels ins)).Perm
      (rowsOf gs bucketOf W wm true (aggregateEval gs ms rows) ++
        rowsOf gs bucketOf W wm false (aggregateEval gs ms (applyBatch rows dels ins))) := by
  refine List.Perm.trans ?_ ((final_unchanged (ms := ms) hg hW ht h).append_right _)
  unfold rowsOf
  refine List.Perm.trans (List.filter_append_perm
    (fun o => final W wm (bucketOf (o.take gs.length)) == true) _).symm (.of_eq ?_)
  congr 1

/-- **Final stays final**: over a stream of batches, each admissible at its
own watermark, and the watermarks never below `wm`, the final rows at `wm`
never change. -/
theorem final_stable (hg : gs ≠ []) (hW : 0 < W) (ht : Tumbling gs ts bucketOf W o) :
    ∀ (batches : List (Int × Relation × Relation)) (rows : Relation),
      (∀ b ∈ batches, wm ≤ b.1 ∧ Admissible ts b.1 b.2.1 b.2.2) →
      (rowsOf gs bucketOf W wm true (aggregateEval gs ms
          (batches.foldl (fun acc b => applyBatch acc b.2.1 b.2.2) rows))).Perm
        (rowsOf gs bucketOf W wm true (aggregateEval gs ms rows))
  | [], _, _ => .refl _
  | b :: bs, rows, h => by
    simp only [List.foldl_cons]
    refine (final_stable hg hW ht bs _ fun c hc => h c (.tail _ hc)).trans ?_
    obtain ⟨hwm, hadm⟩ := h b (.head _)
    exact final_unchanged hg hW ht fun r hr => Int.le_trans hwm (hadm r hr)

/-! ## Expiries: the source's own retention -/

theorem foldl_erase_erase (d : Row) :
    ∀ (ds rows : Relation), ds.foldl List.erase (rows.erase d) = (ds.foldl List.erase rows).erase d
  | [], _ => rfl
  | x :: xs, rows => by
    simp only [List.foldl_cons]
    rw [List.erase_comm d x, foldl_erase_erase d xs]

/-- On the rows in `p`, deletes act as the deletes in `p` alone. -/
theorem filter_foldl_erase_filter {p : Row → Bool} :
    ∀ (dels rows : Relation),
      (dels.foldl List.erase rows).filter p = ((dels.filter p).foldl List.erase rows).filter p
  | [], _ => rfl
  | d :: ds, rows => by
    by_cases hd : p d = true
    · simp only [List.foldl_cons, List.filter_cons, hd, ↓reduceIte]
      exact filter_foldl_erase_filter ds _
    · have hd' : p d = false := by simpa using hd
      simp only [List.foldl_cons, List.filter_cons, hd', Bool.false_eq_true, ↓reduceIte]
      rw [filter_foldl_erase_filter ds, foldl_erase_erase, filter_erase_of_false hd']

/-- Deleting rows of final buckets leaves the open buckets' rows as they
were: the open rows after a batch that also deletes `expired` are those
after the batch without them. -/
theorem open_unchanged_by_expiry (hg : gs ≠ []) {rows expired dels ins : Relation}
    (he : ∀ e ∈ expired, final W wm (bucketOf (groupKey gs e)) = true) :
    (rowsOf gs bucketOf W wm false
        (aggregateEval gs ms (applyBatch rows (expired ++ dels) ins))).Perm
      (rowsOf gs bucketOf W wm false (aggregateEval gs ms (applyBatch rows dels ins))) := by
  let p : Row → Bool := fun k => final W wm (bucketOf k) == false
  let q : Row → Bool := fun r => p (groupKey gs r)
  have hq : expired.filter q = [] :=
    List.filter_eq_nil_iff.mpr fun e he' => by simp [q, p, he e he']
  have key : (applyBatch rows (expired ++ dels) ins).filter q =
      (applyBatch rows dels ins).filter q := by
    simp only [applyBatch, List.filter_append]
    rw [filter_foldl_erase_filter (expired ++ dels), List.filter_append, hq, List.nil_append,
      ← filter_foldl_erase_filter]
  exact (aggregateEval_filter_key hg ms p _).trans
    (List.Perm.trans (.of_eq (by rw [key])) (aggregateEval_filter_key hg ms p _).symm)

/-- **Expiries are sound**: a batch admissible but for `expired`, deletes of
rows in final buckets (a source's retention, such as a Flight log's floor
or a Delta `VACUUM`). The final rows kept in the sink and the open rows
recomputed after the whole batch are the full recomputation after the batch
without the expiries: the sink keeps the history the source forgot. Over a
stream, the source then differs from that history only in rows of buckets
final at an earlier watermark, which stay final (`final_mono`), so the
argument repeats batch by batch. -/
theorem expiry_sound (hg : gs ≠ []) (hW : 0 < W) (ht : Tumbling gs ts bucketOf W o)
    {rows expired dels ins : Relation} (h : Admissible ts wm dels ins)
    (he : ∀ e ∈ expired, final W wm (bucketOf (groupKey gs e)) = true) :
    (aggregateEval gs ms (applyBatch rows dels ins)).Perm
      (rowsOf gs bucketOf W wm true (aggregateEval gs ms rows) ++
        rowsOf gs bucketOf W wm false
          (aggregateEval gs ms (applyBatch rows (expired ++ dels) ins))) :=
  (retention_sound hg hW ht h).trans ((open_unchanged_by_expiry hg he).symm.append_left _)

/-! ## How many buckets are open -/

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, h, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun a ha b hb => h a (.tail _ ha) b (.tail _ hb)) hn.2⟩
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    exact hn.1 (h y (.tail _ hy) x (.head _) he ▸ hy)

theorem nodup_nat_length_le : ∀ {l : List Nat} (N : Nat), l.Nodup → (∀ i ∈ l, i < N) →
    l.length ≤ N
  | [], _, _, _ => Nat.zero_le _
  | l@(_ :: _), 0, _, h => absurd (h _ (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | l, N + 1, hn, h => by
    -- Remove `N` (if present); the rest is below `N`.
    have hsub : (l.erase N).Nodup := hn.erase N
    have hlt : ∀ i ∈ l.erase N, i < N := fun i hi => by
      have hi' := (List.Nodup.mem_erase_iff hn).mp hi
      have := h i hi'.2; omega
    have ih := nodup_nat_length_le N hsub hlt
    by_cases hm : N ∈ l
    · rw [List.length_erase_of_mem hm] at ih; omega
    · rw [List.erase_of_not_mem hm] at ih; omega

/-- **The open buckets are bounded**: with every row's time at most `M` and
lateness `L ≥ 0`, the distinct buckets `floorTo W t` (of a time `t ≤ M`) that
are not final at the watermark `M - L` are at most `⌈L / W⌉ + 1`, written
`(L + W - 1) / W + 1`. -/
theorem open_buckets_le₀ {W M L : Int} (hW : 0 < W) (hL : 0 ≤ L) {bs : List Int}
    (hn : bs.Nodup) (hb : ∀ b ∈ bs, ∃ t ≤ M, b = floorTo W t)
    (ho : ∀ b ∈ bs, final W (M - L) b = false) :
    (bs.length : Int) ≤ (L + W - 1) / W + 1 := by
  -- Bucket `b` gets the index `(M - b) / W`: distinct, and at most `(L + W - 1) / W`.
  let idx : Int → Nat := fun b => ((M - b) / W).toNat
  have hq : ∀ b ∈ bs, b = b / W * W := fun b hbs => by
    obtain ⟨t, _, rfl⟩ := hb b hbs
    unfold floorTo; rw [Int.mul_ediv_cancel _ (Int.ne_of_gt hW)]
  have hrange : ∀ b ∈ bs, 0 ≤ (M - b) / W ∧ (M - b) / W ≤ (L + W - 1) / W := fun b hbs => by
    obtain ⟨t, htM, rfl⟩ := hb b hbs
    have hle := floorTo_le hW t
    have hof := ho _ hbs
    simp only [final, decide_eq_false_iff_not] at hof
    exact ⟨Int.ediv_nonneg (by omega) (Int.le_of_lt hW), Int.ediv_le_ediv hW (by omega)⟩
  have hinj : ∀ a ∈ bs, ∀ b ∈ bs, idx a = idx b → a = b := fun a ha b hb' he => by
    have ra := hrange a ha; have rb := hrange b hb'
    have : (M - a) / W = (M - b) / W := by
      simp only [idx] at he; omega
    have ea := hq a ha; have eb := hq b hb'
    have h1 : (M - a) / W = M / W - a / W := by
      conv => lhs; rw [ea]
      rw [Int.sub_eq_add_neg, ← Int.neg_mul, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hW)]
      omega
    have h2 : (M - b) / W = M / W - b / W := by
      conv => lhs; rw [eb]
      rw [Int.sub_eq_add_neg, ← Int.neg_mul, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hW)]
      omega
    rw [ea, eb]; congr 1; omega
  have hnd : (bs.map idx).Nodup := nodup_map_on hinj hn
  have hlt : ∀ i ∈ bs.map idx, i < ((L + W - 1) / W + 1).toNat := fun i hi => by
    obtain ⟨b, hbs, rfl⟩ := List.mem_map.mp hi
    have := hrange b hbs
    simp only [idx]; omega
  have := nodup_nat_length_le _ hnd hlt
  rw [List.length_map] at this
  have h0 : 0 ≤ (L + W - 1) / W := Int.ediv_nonneg (by omega) (Int.le_of_lt hW)
  omega

/-- `open_buckets_le₀` for buckets counted from any origin `o`. -/
theorem open_buckets_le {W M L o : Int} (hW : 0 < W) (hL : 0 ≤ L) {bs : List Int}
    (hn : bs.Nodup) (hb : ∀ b ∈ bs, ∃ t ≤ M, b = bucket W.toNat o t)
    (ho : ∀ b ∈ bs, final W (M - L) b = false) :
    (bs.length : Int) ≤ (L + W - 1) / W + 1 := by
  have h := open_buckets_le₀ (M := M - o) hW hL (bs := bs.map (· - o))
    (nodup_map_on (fun a _ b _ (e : a - o = b - o) => by omega) hn)
    (fun b' hb' => by
      obtain ⟨b, hbs, rfl⟩ := List.mem_map.mp hb'
      obtain ⟨t, htM, rfl⟩ := hb b hbs
      exact ⟨t - o, by omega, by simp [bucket, Int.toNat_of_nonneg (Int.le_of_lt hW)]⟩)
    (fun b' hb' => by
      obtain ⟨b, hbs, rfl⟩ := List.mem_map.mp hb'
      have := ho b hbs
      simp only [final, decide_eq_false_iff_not] at this ⊢; omega)
  rwa [List.length_map] at h

end Retention
end Substrait
