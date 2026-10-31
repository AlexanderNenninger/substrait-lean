import SubstraitLean.Weighted
import SubstraitLean.Safety
import SubstraitLean.Keys

/-!
# Sharded evaluation

A table can be stored in pieces (shards): Delta or Iceberg partitions, files,
or rows spread over workers. This module proves when a plan can run on each
shard on its own, with the results combined afterwards.

* `Rel.eval_sharded`: a plan that is **linear** in the sharded tables
  (`Rel.linear`) gives the union of its results on the shards:
  `Q(D₁ ⊎ … ⊎ Dₙ) ~ Q(D₁) ⊎ … ⊎ Q(Dₙ)`. Filters, projections, sorts and
  unions are linear; a join, semi or anti join is linear when one side reads
  only broadcast tables (a copy on every shard).
* **Split keys.** When rows with equal values on some columns of each sharded
  table are always on the same shard (`Sharding.keyDisj`: a Delta or
  Iceberg partition column, or a hash of it), more is linear: an aggregate
  whose `GROUP BY` contains the key, with any measure but the
  order-dependent `SUM`/`AVG` of doubles, and a `DISTINCT` whose columns
  contain it (`Rel.keyCols` follows the key through the plan).
* `twoPhase_correct`: `COUNT`, `SUM` of integers, `MIN` and `MAX` aggregate
  in two phases. Every shard aggregates its rows by the grouping keys; the
  partial rows are then grouped again by the keys and combined (`COUNT` by
  `SUM`, the others by themselves). Both phases skip NULLs, so a group a
  shard lacks, or whose values are all NULL, changes nothing. `MIN` and
  `MAX` may be `DISTINCT` (it changes nothing); `COUNT` and `SUM` may be
  when their argument is the whole split key, so that no value is on two
  shards (`Measure.SplitOk`).
* `Rel.shardSplit_sound`: `Rel.shardSplit` turns a plan into the plan each
  shard runs and the plan that combines their outputs, with filters,
  projections and sorts above the aggregate moved to the combining plan.

Refused, because the result depends on how the rows are split:

* `SUM` and `AVG` of doubles: floating-point addition is not associative,
  so a different split rounds differently (`floatSum` adds in list order).
  `Rel.splitAgg` with `floats` splits them anyway (`floatCombine`), with no
  theorem: `--shard` reports the result as not proved.
* `COUNT(DISTINCT x)` and `SUM(DISTINCT x)` unless `x` is the split key: a
  value in two shards counts once in the whole and twice in the parts.
* `DISTINCT` without the split key, windows and `FETCH`: they look at rows
  of other shards.

In this model integer sums are exact. Engines compute them in 64 bits, so
a partial sum may leave 64 bits when the total does not (a shard of large
positive values next to one of large negative values). The SQL each dialect
writes raises instead of wrapping (`Dialect.int_sum`), so two-phase
evaluation either gives the right answer or fails; `inI64_partial` shows
that it cannot fail spuriously when all values have the same sign.
-/

namespace Substrait

/-! ## List lemmas -/

theorem flatMap_perm_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih fun b hb => h b (by simp [hb]))

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap f ++ l.flatMap g).Perm (l.flatMap fun a => f a ++ g a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact (List.perm_append_comm_assoc _ _ _).trans (List.Perm.append_left _ ih)

theorem crossRows_append_right (xs ys zs : Relation) :
    (crossRows xs (ys ++ zs)).Perm (crossRows xs ys ++ crossRows xs zs) := by
  simp only [crossRows, List.map_append]
  exact (flatMap_append_perm xs _ _).symm

theorem crossRows_perm_right {xs ys ys' : Relation} (h : ys.Perm ys') :
    (crossRows xs ys).Perm (crossRows xs ys') :=
  flatMap_perm_congr fun _ _ => h.map _

theorem crossRows_flatMap_right {α : Type} (xs : Relation) (l : List α) (f : α → Relation) :
    (crossRows xs (l.flatMap f)).Perm (l.flatMap fun a => crossRows xs (f a)) := by
  induction l with
  | nil => simp [crossRows]
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (crossRows_append_right _ _ _).trans (List.Perm.append_left _ ih)

theorem flatMap_eq_flatten_map {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = (l.map f).flatten := List.flatMap_def

theorem dedup_perm_of_mem {α : Type} [DecidableEq α] {l l' : List α} (h : ∀ y, y ∈ l ↔ y ∈ l') :
    (dedup l).Perm (dedup l') :=
  (List.perm_ext_iff_of_nodup (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l))
    (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l'))).mpr fun y => by
      rw [mem_dedup, mem_dedup]; exact h y

theorem dedup_append_disjoint {α : Type} [DecidableEq α] {A B : List α}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) : (dedup (A ++ B)).Perm (dedup A ++ dedup B) :=
  (List.perm_ext_iff_of_nodup (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise _))
    (List.nodup_append.mpr ⟨List.nodup_iff_pairwise_ne.mpr (dedup_pairwise _),
      List.nodup_iff_pairwise_ne.mpr (dedup_pairwise _),
      fun a ha b hb => h a (mem_dedup.mp ha) b (mem_dedup.mp hb)⟩)).mpr fun y => by
    simp only [mem_dedup, List.mem_append]

/-- `DISTINCT` of parts with no row in common: the parts' `DISTINCT`s. -/
theorem dedup_flatten_disjoint {α : Type} [DecidableEq α] :
    ∀ {L : List (List α)}, L.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, a ≠ b) →
      (dedup L.flatten).Perm (L.map dedup).flatten
  | [], _ => by simp [dedup, dedupN]
  | A :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatten_cons, List.map_cons]
    refine (dedup_append_disjoint fun a ha b hb => ?_).trans
      (List.Perm.append_left _ (dedup_flatten_disjoint h.2))
    obtain ⟨B, hB, hb⟩ := List.mem_flatten.mp hb
    exact h.1 B hB a ha b hb

/-- The first position of `a` in `l`. -/
def posOf {α : Type} [DecidableEq α] (a : α) : List α → Option Nat
  | [] => none
  | b :: l => if b = a then some 0 else (posOf a l).map (· + 1)

/-- The positions of `ks` in `l`, if all occur. -/
def posAll {α : Type} [DecidableEq α] (l : List α) : List α → Option (List Nat)
  | [] => some []
  | k :: ks => (posOf k l).bind fun p => (posAll l ks).map (p :: ·)

theorem posOf_spec {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α} {p : Nat}, posOf a l = some p → p < l.length ∧ ∀ d, l.getD p d = a
  | [], _, h => by simp [posOf] at h
  | b :: l, p, h => by
    simp only [posOf] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp, fun d => by simp [hb]⟩
    · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := posOf_spec hq
      exact ⟨by simp; omega, fun d => by simp only [List.getD_cons_succ]; exact h2 d⟩

theorem posAll_spec {α : Type} [DecidableEq α] {l : List α} :
    ∀ {ks : List α} {ps : List Nat}, posAll l ks = some ps →
      (∀ p ∈ ps, p < l.length) ∧ ∀ d, ps.map (l.getD · d) = ks
  | [], ps, h => by
    simp only [posAll, Option.some.injEq] at h
    subst h
    simp
  | k :: ks, ps, h => by
    simp only [posAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, qs, hqs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := posOf_spec hp
    obtain ⟨h3, h4⟩ := posAll_spec hqs
    refine ⟨fun x hx => ?_, fun d => by simp only [List.map_cons, List.cons.injEq]; exact ⟨h2 d, h4 d⟩⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h1
    · exact h3 x hx

theorem keyOf_append {k : List Nat} {x : Row} (y : Row) (h : ∀ i ∈ k, i < x.length) :
    keyOf k (x ++ y) = keyOf k x :=
  List.map_congr_left fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (h i hi)]

theorem leftJoinRow_prefix {on : Expr} {n : Nat} {ys : Relation} {x row : Row}
    (h : row ∈ leftJoinRow on n ys x) : ∃ z, row = x ++ z := by
  unfold leftJoinRow at h
  simp only [] at h
  split at h
  · exact ⟨_, List.mem_singleton.mp h⟩
  · simp only [List.mem_filter, List.mem_map] at h
    obtain ⟨⟨y, _, rfl⟩, _⟩ := h
    exact ⟨y, rfl⟩

/-! ## Plans depend only on the tables they read -/

theorem Rel.arity_congr {c cat : Catalog} (h : ∀ t, (c t).arity = (cat t).arity) :
    ∀ r : Rel, r.arity c = r.arity cat
  | .read t => h t
  | .values _ _ | .emit _ _ | .aggregate _ _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unionAll r _ | .semi r _ _ _ => by
      simp only [arity, arity_congr h r]
  | .project r _ | .window r _ _ _ => by simp only [arity, arity_congr h r]
  | .cross a b | .join a b _ _ => by simp only [arity, arity_congr h a, arity_congr h b]

theorem Rel.eval_congr {c cat : Catalog} (ha : ∀ t, (c t).arity = (cat t).arity) :
    ∀ {r : Rel}, (∀ t ∈ r.tables, (c t).rows = (cat t).rows) → r.eval c = r.eval cat
  | .read t, h => h t (by simp [tables])
  | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .fetch r _ _, h | .window r _ _ _, h
  | .orderBy r _, h | .distinct r, h | .aggregate r _ _, h => by
      simp only [eval, eval_congr ha (r := r) h]
  | .cross a b, h | .unionAll a b, h | .semi a b _ _, h => by
      simp only [tables, List.mem_append] at h
      simp only [eval, eval_congr ha (r := a) (fun t ht => h t (.inl ht)),
        eval_congr ha (r := b) (fun t ht => h t (.inr ht))]
  | .join a b ty _, h => by
      simp only [tables, List.mem_append] at h
      cases ty <;> simp only [eval, arity_congr ha b, eval_congr ha (r := a) (fun t ht => h t (.inl ht)),
        eval_congr ha (r := b) (fun t ht => h t (.inr ht))]

/-! ## Values of decomposable aggregates -/

theorem intSum_append : ∀ (vs ws : List Value), intSum (vs ++ ws) = intSum vs + intSum ws
  | [], _ => by simp [intSum]
  | .int i :: vs, ws => by simp only [List.cons_append, intSum, intSum_append vs ws]; omega
  | .null :: vs, ws | .bool _ :: vs, ws | .str _ :: vs, ws | .list _ :: vs, ws => by
      simp only [List.cons_append, intSum, intSum_append vs ws]

theorem intSum_cons (v : Value) (vs : List Value) : intSum (v :: vs) = intSum [v] + intSum vs :=
  intSum_append [v] vs

theorem intSum_perm {vs ws : List Value} (h : vs.Perm ws) : intSum vs = intSum ws := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [intSum_cons, ih, ← intSum_cons]
  | swap x y l =>
    rw [intSum_cons y (x :: l), intSum_cons x l, intSum_cons x (y :: l), intSum_cons y l]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `m` is the least element of `l` in the order `le`. -/
def IsLeast {α : Type} (le : α → α → Bool) (m : α) (l : List α) : Prop :=
  m ∈ l ∧ ∀ w ∈ l, le m w = true

theorem pickFold_least {le : Value → Value → Bool} (hle : TotalPre le) :
    ∀ (v : Value) (vs : List Value), IsLeast le (pickFold (fun a b => !le a b) v vs) (v :: vs)
  | v, [] => ⟨by simp [pickFold], fun w hw => by simp at hw; subst hw; exact hle.refl _⟩
  | v, w :: vs => by
    show IsLeast le (pickFold (fun a b => !le a b) (if (!le v w) = true then w else v) vs) (v :: w :: vs)
    by_cases hp : le v w = true
    · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hm, hl⟩ := pickFold_least hle v vs
      refine ⟨?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hm with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact hl _ (by simp)
        · exact hle.trans _ _ _ (hl v (by simp)) hp
        · exact hl x (by simp [hx])
    · have hwv : le w v = true := by
        have := hle.total v w; simp only [hp, Bool.false_or] at this; exact this
      have hp' : le v w = false := by simpa using hp
      simp only [hp', Bool.not_false, ↓reduceIte]
      obtain ⟨hm, hl⟩ := pickFold_least hle w vs
      refine ⟨List.mem_cons_of_mem _ hm, fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hle.trans _ _ _ (hl w (by simp)) hwv
      · exact hl _ (by simp)
      · exact hl x (by simp [hx])

theorem IsLeast.unique {α : Type} {le : α → α → Bool} (anti : ∀ a b, le a b = true → le b a = true → a = b)
    {m m' : α} {l : List α} (h : IsLeast le m l) (h' : IsLeast le m' l) : m = m' :=
  anti _ _ (h.2 _ h'.1) (h'.2 _ h.1)

/-- The order `MIN` (`max = false`) or `MAX` (`max = true`) picks the least element of. -/
def minMaxLe (max : Bool) (a b : Value) : Bool := if max then b.le a else a.le b

theorem minMaxLe_totalPre (max : Bool) : TotalPre (minMaxLe max) := by
  cases max
  · exact Value.le_totalPre
  · exact Value.le_totalPre.flip

theorem minMaxLe_antisymm (max : Bool) (a b : Value) (h : minMaxLe max a b = true)
    (h' : minMaxLe max b a = true) : a = b := by
  cases max
  · exact Value.le_antisymm h h'
  · exact Value.le_antisymm h' h

/-- `MIN` and `MAX` of a non-empty list: its least element. -/
theorem AggFn.apply_minMax {f : AggFn} {max : Bool} (hf : f = (if max then .max else .min)) :
    ∀ {vs : List Value}, vs ≠ [] → IsLeast (minMaxLe max) (f.apply vs) vs
  | [], h => (h rfl).elim
  | v :: vs, _ => by
    have := pickFold_least (minMaxLe_totalPre max) v vs
    cases max <;> subst hf <;> exact this

def AggFn.decomposable : AggFn → Bool
  | .count | .sum | .min | .max => true
  | .fsum | .avg => false

theorem AggFn.apply_nil_of_ne_count {f : AggFn} (hf : f ≠ .count) : f.apply [] = .null := by
  cases f <;> first | rfl | exact (hf rfl).elim

/-- `MIN` and `MAX` only depend on which values occur. -/
theorem AggFn.apply_minMax_mem {f : AggFn} {max : Bool} (hf : f = (if max then .max else .min))
    {vs ws : List Value} (h : ∀ v, v ∈ vs ↔ v ∈ ws) : f.apply vs = f.apply ws := by
  by_cases hv : vs = []
  · have hw : ws = [] := List.eq_nil_iff_forall_not_mem.mpr fun w hw => by
      have := (h w).mpr hw; simp [hv] at this
    rw [hv, hw]
  · have hw : ws ≠ [] := fun hw => hv (List.eq_nil_iff_forall_not_mem.mpr fun v hv' => by
      have := (h v).mp hv'; simp [hw] at this)
    have hl := apply_minMax hf hv
    exact IsLeast.unique (minMaxLe_antisymm max)
      ⟨(h _).mp hl.1, fun w hw' => hl.2 w ((h w).mpr hw')⟩ (apply_minMax hf hw)

theorem AggFn.apply_minMax_perm {f : AggFn} {max : Bool} (hf : f = (if max then .max else .min))
    {vs ws : List Value} (h : vs.Perm ws) : f.apply vs = f.apply ws :=
  apply_minMax_mem hf fun _ => h.mem_iff

/-- Decomposable aggregates do not depend on the order of their values. -/
theorem AggFn.apply_perm {f : AggFn} (hf : f.decomposable = true) {vs ws : List Value}
    (h : vs.Perm ws) : f.apply vs = f.apply ws := by
  cases f
  · simp [apply, h.length_eq]
  · cases vs with
    | nil => rw [← h.nil_eq]
    | cons v vs =>
      cases ws with
      | nil => exact absurd h.eq_nil (by simp)
      | cons w ws => simp only [apply, intSum_perm h]
  · simp [decomposable] at hf
  · simp [decomposable] at hf
  · exact apply_minMax_perm (max := false) rfl h
  · exact apply_minMax_perm (max := true) rfl h

theorem AggFn.apply_sum_cons (v : Value) (vs : List Value) :
    AggFn.sum.apply (v :: vs) = .int (intSum (v :: vs)) := rfl

/-- Partial sums, without the NULLs of empty parts, add up to the total. -/
theorem sum_partials : ∀ L : List (List Value),
    intSum ((L.map AggFn.sum.apply).filter (· != .null)) = intSum L.flatten ∧
      (((L.map AggFn.sum.apply).filter (· != .null)) = [] ↔ L.flatten = [])
  | [] => by simp [intSum]
  | [] :: L => by
    have := sum_partials L
    simpa [AggFn.apply] using this
  | (v :: vs) :: L => by
    obtain ⟨h₁, _⟩ := sum_partials L
    have hf : (((v :: vs) :: L).map AggFn.sum.apply).filter (· != .null) =
        .int (intSum (v :: vs)) :: (L.map AggFn.sum.apply).filter (· != .null) := by
      simp [AggFn.apply_sum_cons]
    rw [hf, List.flatten_cons]
    refine ⟨?_, by simp⟩
    rw [show intSum (Value.int (intSum (v :: vs)) :: (L.map AggFn.sum.apply).filter (· != .null)) =
      intSum (v :: vs) + intSum ((L.map AggFn.sum.apply).filter (· != .null)) from rfl, h₁,
      intSum_append]

theorem intSum_map_length : ∀ L : List (List Value),
    intSum (L.map fun vs => Value.int vs.length) = (L.flatten.length : Int)
  | [] => rfl
  | vs :: L => by
    simp only [List.map_cons, intSum, intSum_map_length L, List.flatten_cons, List.length_append]
    omega

theorem minMax_combine {f : AggFn} {max : Bool} (hf : f = (if max then .max else .min))
    {L : List (List Value)} (hnn : ∀ vs ∈ L, ∀ v ∈ vs, v ≠ .null) :
    f.apply ((L.map f.apply).filter (· != .null)) = f.apply L.flatten := by
  have hcount : f ≠ .count := by cases max <;> simp [hf]
  have hnil := AggFn.apply_nil_of_ne_count hcount
  by_cases hF : L.flatten = []
  · rw [hF, hnil]
    have : (L.map f.apply).filter (· != .null) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp ha
      rw [List.flatten_eq_nil_iff.mp hF vs hvs, hnil]
      simp
    rw [this, hnil]
  · -- Every non-empty part's least value is a partial result, and they are not NULL.
    have hpart : ∀ vs ∈ L, vs ≠ [] → f.apply vs ∈ (L.map f.apply).filter (· != .null) := by
      intro vs hvs hne
      have hl := AggFn.apply_minMax hf hne
      simp only [List.mem_filter, List.mem_map, bne_iff_ne, ne_eq]
      exact ⟨⟨vs, hvs, rfl⟩, hnn vs hvs _ hl.1⟩
    have hP : (L.map f.apply).filter (· != .null) ≠ [] := by
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hF
      obtain ⟨vs, hvs, hv⟩ := List.mem_flatten.mp hv
      exact List.ne_nil_of_mem (hpart vs hvs (List.ne_nil_of_mem hv))
    have hM := AggFn.apply_minMax hf hP
    have hle := minMaxLe_totalPre max
    refine IsLeast.unique (minMaxLe_antisymm max) ⟨?_, fun w hw => ?_⟩ (AggFn.apply_minMax hf hF)
    · obtain ⟨hm, hn⟩ := List.mem_filter.mp hM.1
      obtain ⟨vs, hvs, he⟩ := List.mem_map.mp hm
      have hne : vs ≠ [] := by
        rintro rfl; rw [hnil] at he; rw [← he] at hn; simp at hn
      exact List.mem_flatten.mpr ⟨vs, hvs, he ▸ (AggFn.apply_minMax hf hne).1⟩
    · obtain ⟨vs, hvs, hw⟩ := List.mem_flatten.mp hw
      have hne := List.ne_nil_of_mem hw
      exact hle.trans _ _ _ (hM.2 _ (hpart vs hvs hne)) ((AggFn.apply_minMax hf hne).2 w hw)

/-- What the combining phase uses in place of each aggregate. -/
def AggFn.combine : AggFn → AggFn
  | .count => .sum
  | f => f

/-- **Combining partial aggregates**: the combining aggregate of the partial
results, NULLs skipped, is the aggregate of all the values. -/
theorem AggFn.combine_apply {f : AggFn} (hf : f.decomposable = true) {L : List (List Value)}
    (hne : L ≠ []) (hnn : ∀ vs ∈ L, ∀ v ∈ vs, v ≠ .null) :
    f.combine.apply ((L.map f.apply).filter (· != .null)) = f.apply L.flatten := by
  cases f
  · obtain ⟨l, L', rfl⟩ := List.exists_cons_of_ne_nil hne
    have : ((l :: L').map AggFn.count.apply).filter (· != .null) =
        (l :: L').map fun vs => Value.int vs.length :=
      List.filter_eq_self.mpr fun a ha => by
        obtain ⟨vs, _, rfl⟩ := List.mem_map.mp ha; simp [apply]
    rw [this]
    simp only [combine]
    rw [List.map_cons, apply_sum_cons, ← List.map_cons (f := fun vs : List Value => Value.int vs.length),
      intSum_map_length]
    rfl
  · obtain ⟨h₁, h₂⟩ := sum_partials L
    simp only [combine]
    by_cases hF : L.flatten = []
    · rw [h₂.mpr hF, hF]
    · obtain ⟨a, l, ha⟩ := List.exists_cons_of_ne_nil (mt h₂.mp hF)
      obtain ⟨b, l', hb⟩ := List.exists_cons_of_ne_nil hF
      rw [ha, hb, apply_sum_cons, apply_sum_cons, ← ha, ← hb, h₁]
  · simp [decomposable] at hf
  · simp [decomposable] at hf
  · exact minMax_combine (max := false) rfl hnn
  · exact minMax_combine (max := true) rfl hnn

/-! ## Measures that combine -/

/-- The value depends only on the bag of rows: not `SUM` or `AVG` of
doubles, which add in row order. -/
def Measure.orderFree (m : Measure) : Bool := m.fn.decomposable

/-- Combines in two phases whatever the split: `DISTINCT` only for `MIN` and
`MAX`, where it changes nothing. -/
def Measure.decomposable (m : Measure) : Bool :=
  m.fn.decomposable && (!m.distinct || m.fn == .min || m.fn == .max)

/-- The values a measure aggregates, repeats included. -/
def Measure.vals (m : Measure) (rows : Relation) : List Value :=
  ((m.kept rows).map m.arg.eval).filter (· != .null)

theorem Measure.inputs_eq (m : Measure) (rows : Relation) :
    m.inputs rows = if m.distinct then dedup (m.vals rows) else m.vals rows := rfl

theorem Measure.kept_perm (m : Measure) {xs ys : Relation} (h : xs.Perm ys) :
    (m.kept xs).Perm (m.kept ys) := by
  unfold kept; split
  · exact h
  · exact h.filter _

theorem Measure.kept_append (m : Measure) (xs ys : Relation) :
    m.kept (xs ++ ys) = m.kept xs ++ m.kept ys := by
  unfold kept; split <;> simp [List.filter_append]

theorem Measure.vals_perm (m : Measure) {xs ys : Relation} (h : xs.Perm ys) :
    (m.vals xs).Perm (m.vals ys) := ((m.kept_perm h).map _).filter _

theorem Measure.vals_nil (m : Measure) : m.vals [] = [] := by
  unfold vals kept; cases m.filter <;> simp

theorem Measure.vals_append (m : Measure) (xs ys : Relation) :
    m.vals (xs ++ ys) = m.vals xs ++ m.vals ys := by
  simp only [vals, kept_append, List.map_append, List.filter_append]

theorem Measure.vals_flatten (m : Measure) :
    ∀ ss : List Relation, m.vals ss.flatten = (ss.map m.vals).flatten
  | [] => m.vals_nil
  | s :: ss => by simp only [List.flatten_cons, List.map_cons, vals_append, vals_flatten m ss]

theorem Measure.mem_vals {m : Measure} {rows : Relation} {v : Value} (h : v ∈ m.vals rows) :
    v ≠ .null ∧ ∃ row ∈ rows, m.arg.eval row = v := by
  simp only [vals, List.mem_filter, List.mem_map, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨row, hrow, rfl⟩, hn⟩ := h
  refine ⟨hn, row, ?_, rfl⟩
  unfold kept at hrow; split at hrow
  · exact hrow
  · exact (List.mem_filter.mp hrow).1

theorem Measure.eval_perm {m : Measure} (hm : m.orderFree = true) {xs ys : Relation}
    (h : xs.Perm ys) : m.eval xs = m.eval ys := by
  simp only [eval, inputs_eq]
  refine AggFn.apply_perm hm ?_
  split
  · exact dedup_perm_of_mem fun _ => (m.vals_perm h).mem_iff
  · exact m.vals_perm h

/-- Rows of different parts give `e` different values. -/
def ValDisjoint (e : Expr) (A B : Relation) : Prop := ∀ a ∈ A, ∀ b ∈ B, e.eval a ≠ e.eval b

/-- What combining `m` needs of the parts: for `COUNT(DISTINCT x)` and
`SUM(DISTINCT x)`, that no value of `x` is in two of them. -/
def Measure.SplitOk (m : Measure) (ss : List Relation) : Prop :=
  m.distinct = true → m.fn ≠ .min → m.fn ≠ .max → ss.Pairwise (ValDisjoint m.arg)

theorem Measure.splitOk_of_decomposable {m : Measure} (hm : m.decomposable = true)
    (ss : List Relation) : m.SplitOk ss := fun hd h₁ h₂ => by
  simp [decomposable, hd, h₁, h₂] at hm

theorem Measure.SplitOk.filter_map {m : Measure} {ss : List Relation} (h : m.SplitOk ss)
    (p : Relation → Bool) (f : Relation → Relation) (hf : ∀ s, ∀ x ∈ f s, x ∈ s) :
    m.SplitOk ((ss.filter p).map f) := fun hd h₁ h₂ =>
  List.pairwise_map.mpr (((h hd h₁ h₂).filter p).imp fun hab a ha b hb =>
    hab a (hf _ a ha) b (hf _ b hb))

/-- The combining aggregate of a measure's results on the parts is its result
on the whole. -/
theorem Measure.combine_eval {m : Measure} (hm : m.orderFree = true) {ss : List Relation}
    (hne : ss ≠ []) (hs : m.SplitOk ss) :
    m.fn.combine.apply ((ss.map m.eval).filter (· != .null)) = m.eval ss.flatten := by
  have hL : ss.map m.inputs ≠ [] := by simpa using hne
  have hnn : ∀ vs ∈ ss.map m.inputs, ∀ v ∈ vs, v ≠ .null := fun vs hvs v hv => by
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hvs
    exact (mem_inputs hv).1
  have hmap : ss.map m.eval = (ss.map m.inputs).map m.fn.apply := by
    simp [eval, Function.comp_def]
  rw [hmap, AggFn.combine_apply hm hL hnn]
  simp only [eval]
  by_cases hd : m.distinct = true
  · have hdd : ss.map m.inputs = (ss.map m.vals).map dedup := by
      simp [inputs_eq, hd, Function.comp_def]
    rw [hdd, inputs_eq]
    simp only [hd, ↓reduceIte]
    rw [vals_flatten]
    have hmem : ∀ v, v ∈ ((ss.map m.vals).map dedup).flatten ↔ v ∈ dedup (ss.map m.vals).flatten := by
      intro v
      simp only [mem_dedup, List.mem_flatten, List.mem_map]
      constructor
      · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩; exact ⟨l, hl, mem_dedup.mp hv⟩
      · rintro ⟨l, hl, hv⟩; exact ⟨_, ⟨l, hl, rfl⟩, mem_dedup.mpr hv⟩
    by_cases hmin : m.fn = .min
    · exact AggFn.apply_minMax_mem (max := false) (by simp [hmin]) hmem
    by_cases hmax : m.fn = .max
    · exact AggFn.apply_minMax_mem (max := true) (by simp [hmax]) hmem
    refine AggFn.apply_perm hm (dedup_flatten_disjoint (List.pairwise_map.mpr
      ((hs hd hmin hmax).imp fun hab a ha b hb => ?_))).symm
    obtain ⟨_, x, hx, rfl⟩ := mem_vals ha
    obtain ⟨_, y, hy, rfl⟩ := mem_vals hb
    exact hab x hx y hy
  · have hdd : ss.map m.inputs = ss.map m.vals := by simp [inputs_eq, hd]
    rw [hdd, inputs_eq]
    simp only [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    rw [vals_flatten]

/-! ## Aggregates do not depend on the order of their input -/

theorem groupRows_perm {gs : List Expr} {xs ys : Relation} (h : xs.Perm ys) (k : Row) :
    (groupRows gs xs k).Perm (groupRows gs ys k) := h.filter _

theorem aggregateEval_perm {gs : List Expr} {ms : List Measure}
    (hms : ∀ m ∈ ms, m.orderFree = true) {xs ys : Relation} (h : xs.Perm ys) :
    (aggregateEval gs ms xs).Perm (aggregateEval gs ms ys) := by
  unfold aggregateEval
  split
  · exact .of_eq (by rw [List.map_congr_left fun m hm => Measure.eval_perm (hms m hm) h])
  · refine ((dedup_perm_of_mem fun k => ?_).map _).trans (.of_eq (List.map_congr_left fun k _ => ?_))
    · simp only [List.mem_map]
      exact ⟨fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.mp hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.mpr hx, e⟩⟩
    · congr 1
      exact List.map_congr_left fun m hm => Measure.eval_perm (hms m hm) (groupRows_perm h k)

/-! ## Aggregates of parts with no group in common -/

theorem aggregateEval_append_disjoint {gs : List Expr} {ms : List Measure} (hg : gs ≠ [])
    {A B : Relation} (h : ∀ a ∈ A, ∀ b ∈ B, groupKey gs a ≠ groupKey gs b) :
    (aggregateEval gs ms (A ++ B)).Perm (aggregateEval gs ms A ++ aggregateEval gs ms B) := by
  have hge : gs.isEmpty = false := by simpa using hg
  simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte, List.map_append]
  refine ((dedup_append_disjoint fun ka hka kb hkb => ?_).map _).trans (.of_eq ?_)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hka
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hkb
    exact h a ha b hb
  · rw [List.map_append]
    congr 1
    · refine List.map_congr_left fun k hk => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
      have : groupRows gs B (groupKey gs a) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb he =>
          h a ha b hb (by simpa using he : groupKey gs b = groupKey gs a).symm
      simp only [groupRows, List.filter_append] at this ⊢
      rw [this, List.append_nil]
    · refine List.map_congr_left fun k hk => ?_
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
      have : groupRows gs A (groupKey gs b) = [] :=
        List.filter_eq_nil_iff.mpr fun a ha he =>
          h a ha b hb (by simpa using he : groupKey gs a = groupKey gs b)
      simp only [groupRows, List.filter_append] at this ⊢
      rw [this, List.nil_append]

/-- **Groups within parts**: when no group spans two parts, aggregating the
whole is aggregating each part, for every measure. -/
theorem aggregateEval_flatten_disjoint {gs : List Expr} {ms : List Measure} (hg : gs ≠ []) :
    ∀ {ss : List Relation},
      ss.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, groupKey gs a ≠ groupKey gs b) →
        (aggregateEval gs ms ss.flatten).Perm (ss.flatMap (aggregateEval gs ms))
  | [], _ => by
    have hge : gs.isEmpty = false := by simpa using hg
    simp [aggregateEval, hge, dedup, dedupN]
  | s :: ss, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatten_cons, List.flatMap_cons]
    refine (aggregateEval_append_disjoint hg fun a ha b hb => ?_).trans
      (List.Perm.append_left _ (aggregateEval_flatten_disjoint hg h.2))
    obtain ⟨B, hB, hb⟩ := List.mem_flatten.mp hb
    exact h.1 B hB a ha b hb

theorem groupKey_eq_mem : ∀ {gs : List Expr} {a b : Row}, groupKey gs a = groupKey gs b →
    ∀ e ∈ gs, e.eval a = e.eval b
  | [], _, _, _, e, he => by simp at he
  | g :: gs, a, b, h, e, he => by
    simp only [groupKey, List.map_cons, List.cons.injEq] at h
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact groupKey_eq_mem (gs := gs) h.2 e he

theorem keyOf_eq_of_groupKey {gs : List Expr} {kc : List Nat} {a b : Row}
    (hkc : ∀ c ∈ kc, gs.contains (.field c) = true) (h : groupKey gs a = groupKey gs b) :
    keyOf kc a = keyOf kc b :=
  List.map_congr_left fun c hc => by
    have := groupKey_eq_mem h (.field c) (by simpa using hkc c hc)
    simpa [Expr.eval] using this

/-! ## Two-phase aggregation -/

/-- The grouping keys of the combining phase: the first `k` columns. -/
def keyFields (k : Nat) : List Expr := (List.range k).map .field

/-- The measures of the combining phase: measure `i` combines column `k + i`
of the partial rows. -/
def combineMeasures (k : Nat) (ms : List Measure) : List Measure :=
  ms.mapIdx fun i m => { fn := m.fn.combine, arg := .field (k + i) }

theorem groupKey_length (gs : List Expr) (row : Row) : (groupKey gs row).length = gs.length := by
  simp [groupKey]

theorem groupKey_keyFields {key vals : Row} :
    groupKey (keyFields key.length) (key ++ vals) = key := by
  simp only [groupKey, keyFields, List.map_map, Function.comp_def, Expr.eval]
  rw [map_range_getD _ _ (by simp)]
  exact List.take_left' rfl

theorem length_of_mem_keys {gs : List Expr} {s : Relation} {k : Row}
    (h : k ∈ dedup (s.map (groupKey gs))) : k.length = gs.length := by
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp (mem_dedup.mp h)
  exact groupKey_length gs x

theorem combineMeasures_eval {k : Nat} {ms : List Measure} {i : Nat} (hi : i < ms.length)
    (rows : Relation) :
    ((combineMeasures k ms)[i]'(by simpa [combineMeasures] using hi)).eval rows =
      ms[i].fn.combine.apply ((rows.map (·.getD (k + i) .null)).filter (· != .null)) := by
  simp [combineMeasures, Measure.eval, Measure.inputs, Measure.kept, Expr.eval]

theorem filter_beq_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α} (h : l.Pairwise (· ≠ ·))
    (k : α) : l.filter (· == k) = if k ∈ l then [k] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    rw [List.filter_cons, ih h.2]
    by_cases hak : a = k
    · subst hak
      have : a ∉ l := fun hm => h.1 a hm rfl
      simp [this]
    · have : (a == k) = false := by simpa using hak
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.mem_cons, Ne.symm hak, false_or]

theorem flatMap_ite_singleton {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    l.flatMap (fun a => if p a then [f a] else []) = (l.filter fun a => decide (p a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem flatten_map_filter {α β : Type} (l : List α) (p : α → Bool) (f : α → List β)
    (h : ∀ a, p a = false → f a = []) : (l.map f).flatten = ((l.filter p).map f).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a
    · simp [hp, ih]
    · simp [hp, ih, h a (by simpa using hp)]

/-- One shard's partial row for the group `k`, if it has that group. -/
theorem aggregateEval_filter_key {gs : List Expr} {ms : List Measure} (hg : gs ≠ []) (s : Relation)
    (k : Row) :
    (aggregateEval gs ms s).filter (fun row => groupKey (keyFields gs.length) row == k) =
      if k ∈ s.map (groupKey gs) then [k ++ ms.map (·.eval (groupRows gs s k))] else [] := by
  have hge : gs.isEmpty = false := by simpa using hg
  simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte, List.filter_map]
  rw [List.filter_congr (q := (· == k)) fun j hj => by
    simp only [Function.comp_apply]
    rw [← length_of_mem_keys hj, groupKey_keyFields]]
  rw [filter_beq_nodup (dedup_pairwise _)]
  by_cases hk : k ∈ s.map (groupKey gs) <;> simp [hk, mem_dedup]

theorem aggregateEval_keys {gs : List Expr} {ms : List Measure} (hg : gs ≠ []) (s : Relation) :
    (aggregateEval gs ms s).map (groupKey (keyFields gs.length)) = dedup (s.map (groupKey gs)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte, List.map_map]
  conv => rhs; rw [← List.map_id (dedup _)]
  exact List.map_congr_left fun j hj => by
    simp only [Function.comp_apply, id]
    rw [← length_of_mem_keys hj, groupKey_keyFields]

/-- **Two-phase aggregation**: aggregating each part, then combining the
partial rows grouped by their keys, gives the aggregate of the whole. -/
theorem twoPhase_correct {gs : List Expr} {ms : List Measure}
    (hms : ∀ m ∈ ms, m.orderFree = true) {ss : List Relation} (hne : ss ≠ [])
    (hs : ∀ m ∈ ms, m.SplitOk ss) :
    (aggregateEval (keyFields gs.length) (combineMeasures gs.length ms)
      (ss.flatMap (aggregateEval gs ms))).Perm (aggregateEval gs ms ss.flatten) := by
  have hlen : ∀ k, (combineMeasures k ms).length = ms.length := fun k => by simp [combineMeasures]
  by_cases hg : gs = []
  · subst hg
    have hP : ss.flatMap (aggregateEval [] ms) = ss.map fun s => ms.map (·.eval s) := by
      clear hs hne
      induction ss with
      | nil => rfl
      | cons s ss ih => cases ss <;> simp_all [aggregateEval]
    simp only [aggregateEval, keyFields, List.length_nil, List.range_zero, List.map_nil,
      List.isEmpty_nil, ↓reduceIte, hP]
    refine .of_eq (congrArg (fun x => [x]) (List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_))
    simp only [List.length_map] at h₂
    simp only [List.getElem_map]
    rw [combineMeasures_eval h₂, ← Measure.combine_eval (hms _ (List.getElem_mem h₂)) hne
      (hs _ (List.getElem_mem h₂))]
    simp [Function.comp_def, List.getD, Nat.zero_add, h₂]
  · have hk : (keyFields gs.length).isEmpty = false := by
      cases gs with
      | nil => exact (hg rfl).elim
      | cons _ _ => simp [keyFields, List.range_succ_eq_map]
    have hge : gs.isEmpty = false := by simpa using hg
    simp only [aggregateEval, hk, hge, Bool.false_eq_true, ↓reduceIte]
    rw [show (ss.flatMap (aggregateEval gs ms)).map (groupKey (keyFields gs.length)) =
        ss.flatMap fun s => dedup (s.map (groupKey gs)) by
      rw [List.map_flatMap]; exact flatMap_congr fun s _ => aggregateEval_keys hg s]
    refine ((dedup_perm_of_mem fun k => ?_).map _).trans (.of_eq (List.map_congr_left fun k hk => ?_))
    · simp only [List.mem_flatMap, mem_dedup, List.mem_map, List.mem_flatten]
      constructor
      · rintro ⟨s, hs, x, hx, rfl⟩; exact ⟨x, ⟨s, hs, hx⟩, rfl⟩
      · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩; exact ⟨s, hs, x, hx, rfl⟩
    · -- The partial rows of group `k`: one from each shard that has it.
      let p : Relation → Bool := fun s => decide (k ∈ s.map (groupKey gs))
      have hkl : k.length = gs.length := length_of_mem_keys hk
      have hQ : groupRows (keyFields gs.length) (ss.flatMap (aggregateEval gs ms)) k =
          (ss.filter p).map fun s => k ++ ms.map (·.eval (groupRows gs s k)) := by
        simp only [groupRows, List.filter_flatMap]
        rw [flatMap_congr fun s _ => aggregateEval_filter_key hg s k]
        exact flatMap_ite_singleton _ (fun s : Relation => k ∈ s.map (groupKey gs)) _
      have hG : groupRows gs ss.flatten k = ((ss.filter p).map (groupRows gs · k)).flatten := by
        simp only [groupRows, List.filter_flatten]
        refine flatten_map_filter _ p _ fun s hs => List.filter_eq_nil_iff.mpr fun x hx he => ?_
        simp only [p, decide_eq_false_iff_not, List.mem_map, not_exists, not_and] at hs
        exact hs x hx (by simpa using he)
      have hne' : (ss.filter p).map (groupRows gs · k) ≠ [] := by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
        obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hx
        have : s ∈ ss.filter p := List.mem_filter.mpr ⟨hs, by simpa [p] using ⟨x, hxs, rfl⟩⟩
        simpa using List.ne_nil_of_mem this
      rw [hQ, hG]
      congr 1
      refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
      simp only [List.length_map] at h₂
      simp only [List.getElem_map]
      rw [combineMeasures_eval h₂, ← Measure.combine_eval (hms _ (List.getElem_mem h₂)) hne'
        ((hs _ (List.getElem_mem h₂)).filter_map p (groupRows gs · k)
          fun _ _ hx => (List.mem_filter.mp hx).1),
        List.map_map, List.map_map]
      congr 2
      refine List.map_congr_left fun s _ => ?_
      simp only [Function.comp_apply, List.getD_eq_getElem?_getD, ← hkl,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_map, List.getElem?_eq_getElem h₂, Option.map_some, Option.getD_some]

/-! ## Shards -/

/-- Where `ProjectRel`'s output has column `c` of its `n`-column input: its
first copy among `es`, else `c` itself. -/
def copyPos (n : Nat) (es : List Expr) (c : Nat) : Nat :=
  match posOf (.field c) es with
  | some i => n + i
  | none => c

theorem getD_append_lt {x y : Row} {i : Nat} (h : i < x.length) :
    (x ++ y).getD i .null = x.getD i .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len {x y : Row} (j : Nat) : (x ++ y).getD (x.length + j) .null = y.getD j .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- Column pairs a condition equates: its `$i = $j` conjuncts. -/
def Expr.eqFields : Expr → List (Nat × Nat)
  | .bin f a b =>
    if f = .and then a.eqFields ++ b.eqFields
    else if f = .eq then
      match a, b with
      | .field i, .field j => [(i, j)]
      | _, _ => []
    else []
  | _ => []

theorem Value.isTrue_iff {v : Value} : v.isTrue = true ↔ v = .bool true := by
  cases v with
  | bool b => cases b <;> simp [Value.isTrue]
  | _ => simp [Value.isTrue]

theorem eq_of_isTrue_eq {v w : Value} (h : (BinFn.apply .eq v w).isTrue = true) : v = w := by
  rw [Value.isTrue_iff] at h
  cases v <;> cases w <;> simp_all [BinFn.apply]

theorem Expr.eqFields_sound {row : Row} : ∀ {e : Expr}, (e.eval row).isTrue = true →
    ∀ p ∈ e.eqFields, row.getD p.1 .null = row.getD p.2 .null
  | .lit _, _, _, hp | .field _, _, _, hp | .un _ _, _, _, hp | .ifThen _ _ _, _, _, hp => by
    simp [eqFields] at hp
  | .bin f a b, h, p, hp => by
    unfold eqFields at hp
    split at hp
    · rename_i hf
      subst hf
      simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at h
      rcases List.mem_append.mp hp with hp | hp
      · exact eqFields_sound h.1 p hp
      · exact eqFields_sound h.2 p hp
    · split at hp
      · rename_i hf
        subst hf
        split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          simp only [eval] at h
          exact eq_of_isTrue_eq h
        · simp at hp
      · simp at hp

/-- A join of two linear plans, split on keys `ka` and `kb`, whose condition
equates them (left columns `ka`, right columns `n + kb` of the joined row,
`n` the left arity): no row of one shard matches a row of another. -/
def coCond (la lb : Bool) (ka kb : Option (List Nat)) (n : Nat) (on : Expr) : Bool :=
  la && lb && match ka, kb with
    | some ka, some kb => ka.length == kb.length && (ka.zip kb).all fun (i, j) =>
        on.eqFields.contains (i, n + j) || on.eqFields.contains (n + j, i)
    | _, _ => false

theorem coCond_linear {la lb : Bool} {ka kb : Option (List Nat)} {n : Nat} {on : Expr}
    (h : coCond la lb ka kb n on = true) : la = true ∧ lb = true := by
  simp only [coCond, Bool.and_eq_true] at h
  exact h.1

/-- Under a co-partitioning condition, matching rows agree on the key. -/
theorem coCond_keys {la lb : Bool} {ka kb : List Nat} {n : Nat} {on : Expr}
    (h : coCond la lb (some ka) (some kb) n on = true) {x y : Row} (hx : x.length = n)
    (hka : ∀ i ∈ ka, i < x.length) (hon : (on.eval (x ++ y)).isTrue = true) :
    keyOf ka x = keyOf kb y := by
  simp only [coCond, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨_, hlen, hall⟩ := h
  apply List.ext_getElem (by simp [keyOf, hlen])
  intro idx h₁ h₂
  have hi : idx < ka.length := by simpa only [keyOf, List.length_map] using h₁
  have hj : idx < kb.length := by omega
  have hzl : idx < (ka.zip kb).length := by simp only [List.length_zip]; omega
  have hz : (ka[idx], kb[idx]) ∈ ka.zip kb := by
    have := List.getElem_mem hzl
    simpa [List.getElem_zip] using this
  have hc := hall _ hz
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
  simp only [keyOf, List.getElem_map]
  have hlt := hka _ (List.getElem_mem hi)
  rcases hc with hc | hc
  · have := Expr.eqFields_sound hon _ hc
    simp only at this
    rwa [getD_append_lt hlt, ← hx, getD_append_len] at this
  · have := Expr.eqFields_sound hon _ hc
    simp only at this
    rwa [getD_append_lt hlt, ← hx, getD_append_len, eq_comm] at this

/-! ### Rows of different shards that never match -/

theorem cross_filter_diag {α : Type} {p : Row → Bool} (f g : α → Relation) : ∀ {L : List α},
    L.Pairwise (fun c c' => (∀ x ∈ f c, ∀ y ∈ g c', p (x ++ y) = false) ∧
      (∀ x ∈ f c', ∀ y ∈ g c, p (x ++ y) = false)) →
    ((crossRows (L.flatMap f) (L.flatMap g)).filter p).Perm
      (L.flatMap fun c => (crossRows (f c) (g c)).filter p)
  | [], _ => by simp [crossRows]
  | c :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatMap_cons]
    have e₁ : crossRows (f c ++ L.flatMap f) (g c ++ L.flatMap g) =
        crossRows (f c) (g c ++ L.flatMap g) ++ crossRows (L.flatMap f) (g c ++ L.flatMap g) := by
      simp [crossRows, List.flatMap_append]
    rw [e₁, List.filter_append]
    have z₁ : (crossRows (f c) (L.flatMap g)).filter p = [] := List.filter_eq_nil_iff.mpr fun r hr => by
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp hr
      obtain ⟨c', hc', hy⟩ := List.mem_flatMap.mp hy
      simp [(h.1 c' hc').1 x hx y hy]
    have z₂ : (crossRows (L.flatMap f) (g c)).filter p = [] := List.filter_eq_nil_iff.mpr fun r hr => by
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp hr
      obtain ⟨c', hc', hx⟩ := List.mem_flatMap.mp hx
      simp [(h.1 c' hc').2 x hx y hy]
    have p₁ : ((crossRows (f c) (g c ++ L.flatMap g)).filter p).Perm ((crossRows (f c) (g c)).filter p) := by
      have := (crossRows_append_right (f c) (g c) (L.flatMap g)).filter p
      rwa [List.filter_append, z₁, List.append_nil] at this
    have p₂ : ((crossRows (L.flatMap f) (g c ++ L.flatMap g)).filter p).Perm
        (L.flatMap fun c => (crossRows (f c) (g c)).filter p) := by
      have := (crossRows_append_right (L.flatMap f) (g c) (L.flatMap g)).filter p
      rw [List.filter_append, z₂, List.nil_append] at this
      exact this.trans (cross_filter_diag f g h.2)
    exact p₁.append p₂

/-- Row by row, where each row's result only sees the rows of `ys` it matches. -/
theorem flatMap_rowwise {α : Type} {m : Row → Row → Bool} (f g : α → Relation)
    (G : Relation → Row → Relation)
    (hG : ∀ x ys zs, (∀ y ∈ zs, m x y = false) → G (ys ++ zs) x = G ys x ∧ G (zs ++ ys) x = G ys x) :
    ∀ {L : List α}, L.Pairwise (fun c c' => (∀ x ∈ f c, ∀ y ∈ g c', m x y = false) ∧
      (∀ x ∈ f c', ∀ y ∈ g c, m x y = false)) →
    (L.flatMap f).flatMap (G (L.flatMap g)) = L.flatMap fun c => (f c).flatMap (G (g c))
  | [], _ => by simp
  | c :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatMap_cons, List.flatMap_append]
    congr 1
    · exact flatMap_congr fun x hx => (hG x (g c) (L.flatMap g) fun y hy => by
        obtain ⟨c', hc', hy⟩ := List.mem_flatMap.mp hy
        exact (h.1 c' hc').1 x hx y hy).1
    · rw [← flatMap_rowwise f g G hG h.2]
      exact flatMap_congr fun x hx => (hG x (L.flatMap g) (g c) fun y hy => by
        obtain ⟨c', hc', hx⟩ := List.mem_flatMap.mp hx
        exact (h.1 c' hc').2 x hx y hy).2

theorem filter_rowwise {α : Type} {m : Row → Row → Bool} (f g : α → Relation)
    (P : Relation → Row → Bool)
    (hP : ∀ x ys zs, (∀ y ∈ zs, m x y = false) → P (ys ++ zs) x = P ys x ∧ P (zs ++ ys) x = P ys x) :
    ∀ {L : List α}, L.Pairwise (fun c c' => (∀ x ∈ f c, ∀ y ∈ g c', m x y = false) ∧
      (∀ x ∈ f c', ∀ y ∈ g c, m x y = false)) →
    (L.flatMap f).filter (P (L.flatMap g)) = L.flatMap fun c => (f c).filter (P (g c))
  | [], _ => by simp
  | c :: L, h => by
    rw [List.pairwise_cons] at h
    simp only [List.flatMap_cons, List.filter_append]
    congr 1
    · exact List.filter_congr fun x hx => (hP x (g c) (L.flatMap g) fun y hy => by
        obtain ⟨c', hc', hy⟩ := List.mem_flatMap.mp hy
        exact (h.1 c' hc').1 x hx y hy).1
    · rw [← filter_rowwise f g P hP h.2]
      exact List.filter_congr fun x hx => (hP x (L.flatMap g) (g c) fun y hy => by
        obtain ⟨c', hc', hx⟩ := List.mem_flatMap.mp hx
        exact (h.1 c' hc').2 x hx y hy).2

theorem leftJoinRow_append_nomatch {on : Expr} {n : Nat} (x : Row) (ys zs : Relation)
    (h : ∀ y ∈ zs, (on.eval (x ++ y)).isTrue = false) :
    leftJoinRow on n (ys ++ zs) x = leftJoinRow on n ys x ∧
      leftJoinRow on n (zs ++ ys) x = leftJoinRow on n ys x := by
  have hz : ((zs.map (x ++ ·)).filter fun row => (on.eval row).isTrue) = [] :=
    List.filter_eq_nil_iff.mpr fun r hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      simp [h y hy]
  constructor <;> simp only [leftJoinRow, List.map_append, List.filter_append, hz,
    List.append_nil, List.nil_append]

theorem hasMatch_append_nomatch {on : Expr} (x : Row) (ys zs : Relation)
    (h : ∀ y ∈ zs, (on.eval (x ++ y)).isTrue = false) :
    hasMatch on (ys ++ zs) x = hasMatch on ys x ∧ hasMatch on (zs ++ ys) x = hasMatch on ys x := by
  have hz : hasMatch on zs x = false := by
    simp only [hasMatch, List.any_eq_false]
    exact fun y hy => by simp [h y hy]
  simp only [hasMatch] at hz ⊢
  constructor <;> simp [List.any_append, hz]

theorem leftJoinRow_perm {on : Expr} {n : Nat} {ys ys' : Relation} (x : Row) (h : ys.Perm ys') :
    (leftJoinRow on n ys x).Perm (leftJoinRow on n ys' x) := by
  have hm := (h.map (x ++ ·)).filter fun row => (on.eval row).isTrue
  have he : ((ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue).isEmpty =
      ((ys'.map (x ++ ·)).filter fun row => (on.eval row).isTrue).isEmpty := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff, hm.length_eq]
  unfold leftJoinRow
  simp only []
  rw [he]
  split
  · exact .refl _
  · exact hm

theorem hasMatch_perm {on : Expr} {ys ys' : Relation} (x : Row) (h : ys.Perm ys') :
    hasMatch on ys x = hasMatch on ys' x := by
  unfold hasMatch
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, h.mem_iff.mp hy, e⟩, fun ⟨y, hy, e⟩ => ⟨y, h.mem_iff.mpr hy, e⟩⟩

/-! ### Windows over parts with no partition in common -/

/-- `x`'s partition-mates in parts with no partition in common: those of its part. -/
theorem filter_flatten_single {p : Row → Row → Bool} (hrefl : ∀ x, p x x = true)
    (hsym : ∀ x y, p x y = true → p y x = true) : ∀ {L : List Relation},
    L.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, p a b = false) →
      ∀ A ∈ L, ∀ x ∈ A, L.flatten.filter (p x) = A.filter (p x)
  | [], _, _, hA, _, _ => by simp at hA
  | B :: L, h, A, hA, x, hx => by
    rw [List.pairwise_cons] at h
    simp only [List.flatten_cons, List.filter_append]
    rcases List.mem_cons.mp hA with rfl | hA
    · have : L.flatten.filter (p x) = [] := List.filter_eq_nil_iff.mpr fun b hb => by
        obtain ⟨B', hB', hb⟩ := List.mem_flatten.mp hb
        simp [h.1 B' hB' x hx b hb]
      rw [this, List.append_nil]
    · have hB : B.filter (p x) = [] := List.filter_eq_nil_iff.mpr fun b hb hpx => by
        have := h.1 A hA b hb x hx
        rw [hsym x b hpx] at this
        exact absurd this (by simp)
      rw [hB, List.nil_append]
      exact filter_flatten_single hrefl hsym h.2 A hA x hx

/-- **Windows by part**: with no ties on its partition and sort columns, a
window over parts with no partition in common is the window of each part. -/
theorem windowEval_sharded {part : List Nat} {sort : List SortKey} {fns : List WinFn} {α : Type}
    {cs : List α} {f : α → Relation} {rows : Relation} (hp : rows.Perm (cs.flatMap f))
    (hk : KeyOn (part ++ sort.map (·.col)) rows)
    (hd : (cs.map f).Pairwise fun A B => ∀ a ∈ A, ∀ b ∈ B, samePart part a b = false) :
    (windowEval part sort fns rows).Perm (cs.flatMap fun c => windowEval part sort fns (f c)) := by
  have hTP := sortLe_totalPre sort
  have hsorted : ∀ l : Relation, (l.mergeSort (sortLe sort)).Pairwise (sortLe sort · · = true) :=
    fun l => List.pairwise_mergeSort hTP.trans hTP.total l
  have hkF : KeyOn _ (cs.flatMap f) := hk.perm hp fun h => Ne.symm h
  have hkc : ∀ c ∈ cs, KeyOn (part ++ sort.map (·.col)) (f c) := fun c hc =>
    (List.pairwise_flatMap.mp hkF).1 c hc
  have hkS : KeyOn _ (rows.mergeSort (sortLe sort)) :=
    hk.perm (List.mergeSort_perm rows _).symm fun h => Ne.symm h
  have hkcS : ∀ c ∈ cs, KeyOn (part ++ sort.map (·.col)) ((f c).mergeSort (sortLe sort)) :=
    fun c hc => (hkc c hc).perm (List.mergeSort_perm _ _).symm fun h => Ne.symm h
  have hpart : ∀ c ∈ cs, ∀ x ∈ f c, (rows.mergeSort (sortLe sort)).filter (samePart part x) =
      ((f c).mergeSort (sortLe sort)).filter (samePart part x) := by
    intro c hc x hx
    have hsingle := filter_flatten_single (samePart_refl part) (fun _ _ => samePart_comm) hd
      (f c) (List.mem_map.mpr ⟨c, hc, rfl⟩) x hx
    rw [← flatMap_eq_flatten_map] at hsingle
    apply eq_of_perm_of_pairwise
    · refine (((List.mergeSort_perm rows _).trans hp).filter _).trans ?_
      rw [hsingle]
      exact ((List.mergeSort_perm (f c) _).symm).filter _
    · exact (hsorted _).filter _
    · exact (hsorted _).filter _
    · intro y hy z hz hyz hzy
      simp only [List.mem_filter] at hy hz
      apply KeyOn.eq_of_keyOf hkS hy.1 hz.1
      simp only [keyOf, List.map_append, List.map_map]
      have h₁ := hy.2
      have h₂ := hz.2
      simp only [samePart, decide_eq_true_eq] at h₁ h₂
      rw [← h₁, ← h₂]
      congr 1
      simpa [Function.comp_def] using sortLe_antisymm hyz hzy
  unfold windowEval
  rw [windowRows_eq_map hkS.nodup (List.nil_append _)]
  rw [flatMap_congr fun c hc => windowRows_eq_map (hkcS c hc).nodup (List.nil_append _)]
  refine ((((List.mergeSort_perm rows _).trans hp).trans
    (flatMap_perm_congr fun c _ => (List.mergeSort_perm (f c) (sortLe sort)).symm)).map _).trans ?_
  rw [List.map_flatMap]
  exact .of_eq (flatMap_congr fun c hc => List.map_congr_left fun x hx => by
    simp only [winRow, hpart c hc x (List.mem_mergeSort.mp hx)])

theorem keyOf_eq_of_samePart {part kc : List Nat} {a b : Row} (hkc : ∀ c ∈ kc, c ∈ part)
    (h : samePart part a b = true) : keyOf kc a = keyOf kc b := by
  simp only [samePart, decide_eq_true_eq, List.map_inj_left] at h
  simp only [keyOf, List.map_inj_left]
  exact fun c hc => h c (hkc c hc)

theorem Rel.wf_congr {c cat : Catalog} (h : ∀ t, (c t).arity = (cat t).arity) :
    ∀ {r : Rel}, r.WF cat → r.WF c
  | .read _, _ => trivial
  | .values _ _, hw => hw
  | .fetch r _ _, hw | .distinct r, hw => wf_congr h (r := r) hw
  | .filter r _, hw | .project r _, hw | .emit r _, hw | .window r _ _ _, hw
  | .orderBy r _, hw | .aggregate r _ _, hw =>
    ⟨wf_congr h (r := r) hw.1, by rw [arity_congr h r]; exact hw.2⟩
  | .cross a b, hw => ⟨wf_congr h (r := a) hw.1, wf_congr h (r := b) hw.2⟩
  | .join a b _ _, hw | .semi a b _ _, hw | .unionAll a b, hw =>
    ⟨wf_congr h (r := a) hw.1, wf_congr h (r := b) hw.2.1,
      by rw [arity_congr h a, arity_congr h b]; exact hw.2.2⟩

/-- `cs` splits the tables `S` of `cat` into shards: every shard has the same
schemas, the rows of a sharded table are spread over the shards, and every
other table is copied to each shard (broadcast). A split key `K t` of a
sharded table names columns that rows of different shards never agree on,
across all keyed tables (`keyDisj`): all rows with the same key are on one
shard. With no keys (`K = fun _ => none`) the last two fields say nothing. -/
structure Sharding (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog)
    (cs : List Catalog) : Prop where
  wf : ∀ c ∈ cs, c.WF
  arity : ∀ c ∈ cs, ∀ t, (c t).arity = (cat t).arity
  split : ∀ t, S t = true → (cat t).rows.Perm (cs.flatMap fun c => (c t).rows)
  bcast : ∀ t, S t = false → ∀ c ∈ cs, (c t).rows = (cat t).rows
  keyLen : ∀ c ∈ cs, ∀ t kt, S t = true → K t = some kt → ∀ x ∈ (c t).rows, ∀ i ∈ kt, i < x.length
  keyDisj : cs.Pairwise fun c c' => ∀ t t' kt kt', S t = true → S t' = true → K t = some kt →
    K t' = some kt' → ∀ x ∈ (c t).rows, ∀ y ∈ (c' t').rows, keyOf kt x ≠ keyOf kt' y

/-- Reads no sharded table. -/
def Rel.const (S : String → Bool) (r : Rel) : Bool := r.tables.all (!S ·)

mutual
/-- Linear in the sharded tables: the result on a union of shards is the union
of the results. Aggregates and `DISTINCT` are, when the split key is among
their grouping columns. -/
def Rel.linear (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog) :
    Rel → Bool
  | .read t => S t
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => r.linear S K T cat
  | .unionAll a b => a.linear S K T cat && b.linear S K T cat
  | .cross a b => (a.linear S K T cat && b.const S) || (a.const S && b.linear S K T cat)
  | .join a b .inner on =>
      (a.linear S K T cat && b.const S) || (a.const S && b.linear S K T cat) ||
        coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat) (b.keyCols S K T cat)
          (a.arity cat) on
  | .join a b .left on | .semi a b _ on =>
      (a.linear S K T cat && b.const S) ||
        coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat) (b.keyCols S K T cat)
          (a.arity cat) on
  | .window r part sort _ => r.linear S K T cat && T r part sort &&
      match r.keyCols S K T cat with
      | some kc => kc.all (· ∈ part)
      | none => false
  | .distinct r => r.linear S K T cat && (r.keyCols S K T cat).isSome
  | .aggregate r gs ms => r.linear S K T cat && !gs.isEmpty && ms.all (·.orderFree) &&
      match r.keyCols S K T cat with
      | some kc => kc.all fun c => gs.contains (.field c)
      | none => false
  -- A literal table would be repeated on every shard.
  | .values _ _ | .fetch _ _ _ => false

/-- Where the split key is in the output of a linear plan (`Rel.keyRows`). -/
def Rel.keyCols (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog) :
    Rel → Option (List Nat)
  | .read t => if S t then K t else none
  | .filter r _ | .orderBy r _ | .distinct r | .semi r _ _ _ | .join r _ .left _
  | .window r _ _ _ => r.keyCols S K T cat
  -- A key column the projection copies: the copy (an emit may keep only it).
  | .project r es => (r.keyCols S K T cat).map (·.map (copyPos (r.arity cat) es))
  | .emit r m => (r.keyCols S K T cat).bind (posAll m)
  | .cross a b => if a.linear S K T cat && b.const S then a.keyCols S K T cat else none
  | .join a b .inner on =>
      if (a.linear S K T cat && b.const S) ||
          coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat) (b.keyCols S K T cat)
            (a.arity cat) on then a.keyCols S K T cat
      else none
  | .unionAll a b => if a.keyCols S K T cat == b.keyCols S K T cat then a.keyCols S K T cat else none
  | .aggregate r gs _ => (r.keyCols S K T cat).bind fun kc => posAll gs (kc.map .field)
  | .values _ _ | .fetch _ _ _ => none
end

theorem Sharding.const_eval {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} (h : r.const S = true) :
    ∀ c ∈ cs, r.eval c = r.eval cat :=
  fun c hc => Rel.eval_congr (hs.arity c hc) fun t ht => by
    simp only [Rel.const, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact hs.bcast t (h t ht) c hc

theorem Sharding.cross {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {a b : Rel}
    (ha : a.linear S K T cat = true → (a.eval cat).Perm (cs.flatMap a.eval))
    (hb : b.linear S K T cat = true → (b.eval cat).Perm (cs.flatMap b.eval))
    (h : (a.linear S K T cat && b.const S || a.const S && b.linear S K T cat) = true) :
    (crossRows (a.eval cat) (b.eval cat)).Perm
      (cs.flatMap fun c => crossRows (a.eval c) (b.eval c)) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hl, hc⟩ | ⟨hc, hl⟩
  · refine ((ha hl).flatMap_right _).trans ?_
    rw [List.flatMap_assoc]
    exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval hc c hm]; rfl)
  · refine (crossRows_perm_right (hb hl)).trans ((crossRows_flatMap_right _ _ _).trans ?_)
    exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval hc c hm])

/-- A row's split key (at `kc`) is that of a row of a sharded table on the
same shard. -/
def KeyFrom (S : String → Bool) (K : String → Option (List Nat)) (c : Catalog) (kc : List Nat)
    (row : Row) : Prop :=
  (∀ i ∈ kc, i < row.length) ∧
    ∃ t kt, S t = true ∧ K t = some kt ∧ ∃ x ∈ (c t).rows, keyOf kc row = keyOf kt x

theorem KeyFrom.append {S : String → Bool} {K : String → Option (List Nat)} {c : Catalog}
    {kc : List Nat} {x : Row} (h : KeyFrom S K c kc x) (y : Row) : KeyFrom S K c kc (x ++ y) := by
  obtain ⟨hl, t, kt, h₁, h₂, x', hx', he⟩ := h
  refine ⟨fun i hi => ?_, t, kt, h₁, h₂, x', hx', by rw [keyOf_append y hl, he]⟩
  have := hl i hi
  simp only [List.length_append]
  omega

/-- On each shard, the rows of a linear plan with a split key carry the key
of a row of that shard. -/
theorem Rel.keyRows {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {c : Catalog} (hc : c ∈ cs) :
    ∀ {r : Rel} {kc : List Nat}, r.WF cat → r.linear S K T cat = true →
      r.keyCols S K T cat = some kc → ∀ row ∈ r.eval c, KeyFrom S K c kc row
  | .read t, kc, _, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols, hl, ↓reduceIte] at hk
    exact ⟨fun i hi => hs.keyLen c hc t kc hl hk row h i hi, t, kc, hl, hk, row, h, rfl⟩
  | .values _ _, _, _, hl, _, _, _ | .fetch _ _ _, _, _, hl, _, _, _ => by
    simp [linear] at hl
  | .window r _ _ _, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    obtain ⟨_, x, _, _, hx, rfl⟩ := mem_windowEval h
    exact (keyRows hs hc (r := r) hw.1 hl.1.1 hk x hx).append _
  | .filter r _, kc, hw, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols] at hk
    simp only [eval, List.mem_filter] at h
    exact keyRows hs hc (r := r) hw.1 hl hk row h.1
  | .orderBy r _, kc, hw, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols] at hk
    simp only [eval, List.mem_mergeSort] at h
    exact keyRows hs hc (r := r) hw.1 hl hk row h
  | .semi r _ _ _, kc, hw, hl, hk, row, h => by
    have hl' : r.linear S K T cat = true := by
      simp only [linear, Bool.or_eq_true, Bool.and_eq_true] at hl
      rcases hl with hl | hl
      · exact hl.1
      · exact (coCond_linear hl).1
    simp only [keyCols] at hk
    simp only [eval, List.mem_filter] at h
    exact keyRows hs hc (r := r) hw.1 hl' hk row h.1
  | .distinct r, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    simp only [eval, mem_dedup] at h
    exact keyRows hs hc (r := r) hw hl.1 hk row h
  | .project r es, kc, hw, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols, Option.map_eq_some_iff] at hk
    obtain ⟨kc₀, hk₀, rfl⟩ := hk
    simp only [eval, List.mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨hlt, t, kt, h₁, h₂, x', hx', he⟩ := keyRows hs hc (r := r) hw.1 hl hk₀ x hx
    have hxl : x.length = r.arity cat := by
      rw [eval_arity (hs.wf c hc) (wf_congr (hs.arity c hc) hw.1) x hx, arity_congr (hs.arity c hc)]
    -- Each key column, at its copy or in place, holds the same value.
    have hcol : ∀ k ∈ kc₀, copyPos (r.arity cat) es k < (x ++ es.map (·.eval x)).length ∧
        (x ++ es.map (·.eval x)).getD (copyPos (r.arity cat) es k) .null = x.getD k .null := by
      intro k hk
      unfold copyPos
      split
      · rename_i i hi
        obtain ⟨hil, hes⟩ := posOf_spec hi
        have hes' : es[i] = .field k := by
          have := hes (.lit .null); rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil,
            Option.getD_some] at this
        refine ⟨by simp; omega, ?_⟩
        rw [← hxl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [List.getElem?_eq_getElem hil, hes', Expr.eval]
      · exact ⟨by simp; have := hlt k hk; omega, by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlt k hk),
            ← List.getD_eq_getElem?_getD]⟩
    refine ⟨fun i hi => ?_, t, kt, h₁, h₂, x', hx', ?_⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      exact (hcol k hk).1
    · rw [← he]
      simp only [keyOf, List.map_map]
      exact List.map_congr_left fun k hk => (hcol k hk).2
  | .emit r m, kc, hw, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols, Option.bind_eq_some_iff] at hk
    obtain ⟨kc₀, hk₀, hp⟩ := hk
    simp only [eval, List.mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨_, t, kt, h₁, h₂, x', hx', he⟩ := keyRows hs hc (r := r) hw.1 hl hk₀ x hx
    obtain ⟨hlt, hmap⟩ := posAll_spec hp
    refine ⟨fun i hi => by simpa using hlt i hi, t, kt, h₁, h₂, x', hx', ?_⟩
    rw [← he, ← hmap 0]
    simp only [keyOf, List.map_map]
    exact List.map_congr_left fun p hp => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (hlt p hp)]
  | .cross a b, kc, hw, hl, hk, row, h => by
    simp only [keyCols] at hk
    split at hk
    · rename_i hab
      simp only [Bool.and_eq_true] at hab
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, _, rfl⟩ := h
      exact (keyRows hs hc (r := a) hw.1 hab.1 hk x hx).append y
    · simp at hk
  | .join a b .inner _, kc, hw, hl, hk, row, h => by
    simp only [keyCols] at hk
    split at hk
    · rename_i hab
      have ha : a.linear S K T cat = true := by
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hab
        rcases hab with hab | hab
        · exact hab.1
        · exact (coCond_linear hab).1
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, _, rfl⟩, _⟩ := h
      exact (keyRows hs hc (r := a) hw.1 ha hk x hx).append y
    · simp at hk
  | .join a b .left _, kc, hw, hl, hk, row, h => by
    have ha : a.linear S K T cat = true := by
      simp only [linear, Bool.or_eq_true, Bool.and_eq_true] at hl
      rcases hl with hl | hl
      · exact hl.1
      · exact (coCond_linear hl).1
    simp only [keyCols] at hk
    simp only [eval, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨z, rfl⟩ := leftJoinRow_prefix h
    exact (keyRows hs hc (r := a) hw.1 ha hk x hx).append z
  | .unionAll a b, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    split at hk
    · rename_i hab
      have hb : b.keyCols S K T cat = some kc := by rw [← beq_iff_eq.mp hab]; exact hk
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact keyRows hs hc (r := a) hw.1 hl.1 hk row h
      · exact keyRows hs hc (r := b) hw.2.1 hl.2 hb row h
    · simp at hk
  | .aggregate r gs ms, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    obtain ⟨⟨⟨hl, hg⟩, _⟩, _⟩ := hl
    have hg' : gs ≠ [] := by intro he; simp [he] at hg
    simp only [keyCols, Option.bind_eq_some_iff] at hk
    obtain ⟨kc₀, hk₀, hp⟩ := hk
    obtain ⟨k, grp, rfl, _, hkx⟩ := mem_aggregateEval h
    rcases hkx with ⟨hgs, _⟩ | ⟨x, hx, rfl⟩
    · exact absurd hgs hg'
    obtain ⟨_, t, kt, h₁, h₂, x', hx', he⟩ := keyRows hs hc (r := r) hw.1 hl hk₀ x hx
    obtain ⟨hlt, hmap⟩ := posAll_spec hp
    have hlen : ∀ i ∈ kc, i < (groupKey gs x).length := fun i hi => by
      rw [groupKey_length]; exact hlt i hi
    refine ⟨fun i hi => by have := hlen i hi; simp only [List.length_append]; omega,
      t, kt, h₁, h₂, x', hx', ?_⟩
    rw [keyOf_append _ hlen, ← he]
    have hm := hmap (.lit .null)
    calc keyOf kc (groupKey gs x)
        = (kc.map (gs.getD · (.lit .null))).map (·.eval x) := by
          simp only [keyOf, groupKey, List.map_map]
          exact List.map_congr_left fun p hp => by
            simp [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem (hlt p hp)]
      _ = keyOf kc₀ x := by rw [hm]; simp [keyOf, Expr.eval]

/-- Rows of a linear plan on different shards differ on the split key. -/
theorem Sharding.rows_disjoint {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} {kc : List Nat} (hw : r.WF cat)
    (hl : r.linear S K T cat = true) (hk : r.keyCols S K T cat = some kc) :
    (cs.map r.eval).Pairwise fun A B => ∀ a ∈ A, ∀ b ∈ B, keyOf kc a ≠ keyOf kc b :=
  List.pairwise_map.mpr (hs.keyDisj.imp_of_mem fun hc hc' hd a ha b hb he => by
    obtain ⟨_, t, kt, h₁, h₂, x, hx, ex⟩ := Rel.keyRows hs hc hw hl hk a ha
    obtain ⟨_, t', kt', h₁', h₂', y, hy, ey⟩ := Rel.keyRows hs hc' hw hl hk b hb
    exact hd t t' kt kt' h₁ h₁' h₂ h₂' x hx y hy (by rw [← ex, ← ey, he]))

/-- Under a co-partitioning condition, no row of one shard matches a row of
another. -/
theorem Sharding.coDisjoint {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) {a b : Rel} {on : Expr}
    (hwa : a.WF cat) (hwb : b.WF cat)
    (h : coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat) (b.keyCols S K T cat)
      (a.arity cat) on = true) :
    cs.Pairwise fun c c' =>
      (∀ x ∈ a.eval c, ∀ y ∈ b.eval c', (on.eval (x ++ y)).isTrue = false) ∧
        (∀ x ∈ a.eval c', ∀ y ∈ b.eval c, (on.eval (x ++ y)).isTrue = false) := by
  obtain ⟨hla, hlb⟩ := coCond_linear h
  cases hka : a.keyCols S K T cat with
  | none => simp [coCond, hka] at h
  | some ka =>
  cases hkb : b.keyCols S K T cat with
  | none => simp [coCond, hka, hkb] at h
  | some kb =>
  rw [hka, hkb] at h
  have key : ∀ c ∈ cs, ∀ x ∈ a.eval c, ∀ y, (on.eval (x ++ y)).isTrue = true →
      keyOf ka x = keyOf kb y := fun c hc x hx y hon => by
    have hxl : x.length = a.arity cat := by
      rw [Rel.eval_arity (hs.wf c hc) (Rel.wf_congr (hs.arity c hc) hwa) x hx,
        Rel.arity_congr (hs.arity c hc)]
    exact coCond_keys h hxl (Rel.keyRows hs hc hwa hla hka x hx).1 hon
  refine hs.keyDisj.imp_of_mem fun {c c'} hc hc' hd => ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · cases hon : (on.eval (x ++ y)).isTrue
    · rfl
    obtain ⟨_, t, kt, h₁, h₂, x', hx', ex⟩ := Rel.keyRows hs hc hwa hla hka x hx
    obtain ⟨_, t', kt', h₁', h₂', y', hy', ey⟩ := Rel.keyRows hs hc' hwb hlb hkb y hy
    exact absurd (by rw [← ex, ← ey]; exact key c hc x hx y hon) (hd t t' kt kt' h₁ h₁' h₂ h₂' x' hx' y' hy')
  · cases hon : (on.eval (x ++ y)).isTrue
    · rfl
    obtain ⟨_, t, kt, h₁, h₂, x', hx', ex⟩ := Rel.keyRows hs hc' hwa hla hka x hx
    obtain ⟨_, t', kt', h₁', h₂', y', hy', ey⟩ := Rel.keyRows hs hc hwb hlb hkb y hy
    exact absurd (by rw [← ey, ← ex]; exact (key c' hc' x hx y hon).symm)
      (hd t' t kt' kt h₁' h₁ h₂' h₂ y' hy' x' hx')

/-- **Sharded evaluation**: a linear plan's result on the whole tables is the
union of its results on the shards. -/
theorem Rel.eval_sharded {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) :
    ∀ {r : Rel}, r.WF cat → r.linear S K T cat = true → (r.eval cat).Perm (cs.flatMap r.eval)
  | .read t, _, h => hs.split t h
  | .values _ _, _, h | .fetch _ _ _, _, h => by
      simp [linear] at h
  | .window r part sort fns, hw, h => by
      simp only [linear, Bool.and_eq_true] at h
      obtain ⟨⟨hl, hTw⟩, hkm⟩ := h
      cases hk : r.keyCols S K T cat with
      | none => simp [hk] at hkm
      | some kc =>
        simp only [hk, List.all_eq_true, decide_eq_true_eq] at hkm
        simp only [eval]
        exact windowEval_sharded (eval_sharded hs hT hw.1 hl) (hT r part sort hTw hw.1)
          ((hs.rows_disjoint hw.1 hl hk).imp fun hab a ha b hb => by
            cases hsp : samePart part a b
            · rfl
            · exact absurd (keyOf_eq_of_samePart hkm hsp) (hab a ha b hb))
  | .filter r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact ((eval_sharded hs hT (r := r) hw.1 h).filter _).trans (.of_eq List.filter_flatMap)
  | .project r _, hw, h | .emit r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact ((eval_sharded hs hT (r := r) hw.1 h).map _).trans (.of_eq List.map_flatMap)
  | .orderBy r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((eval_sharded hs hT (r := r) hw.1 h).trans
        (flatMap_perm_congr fun _ _ => (List.mergeSort_perm _ _).symm))
  | .unionAll a b, hw, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      exact ((eval_sharded hs hT (r := a) hw.1 h.1).append (eval_sharded hs hT (r := b) hw.2.1 h.2)).trans
        (flatMap_append_perm _ _ _)
  | .cross a b, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact hs.cross (eval_sharded hs hT (r := a) hw.1) (eval_sharded hs hT (r := b) hw.2) h
  | .join a b .inner on, hw, h => by
      simp only [linear] at h
      simp only [eval]
      by_cases hc : (a.linear S K T cat && b.const S || a.const S && b.linear S K T cat) = true
      · exact ((hs.cross (eval_sharded hs hT (r := a) hw.1) (eval_sharded hs hT (r := b) hw.2.1)
          hc).filter _).trans (.of_eq List.filter_flatMap)
      · have hco : coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat)
            (b.keyCols S K T cat) (a.arity cat) on = true := by simpa [hc] using h
        obtain ⟨hla, hlb⟩ := coCond_linear hco
        exact ((((eval_sharded hs hT (r := a) hw.1 hla).flatMap_right _).trans
          (crossRows_perm_right (eval_sharded hs hT (r := b) hw.2.1 hlb))).filter _).trans
          (cross_filter_diag a.eval b.eval (hs.coDisjoint hw.1 hw.2.1 hco))
  | .join a b .left on, hw, h => by
      simp only [linear] at h
      simp only [eval]
      by_cases hc : (a.linear S K T cat && b.const S) = true
      · simp only [Bool.and_eq_true] at hc
        refine ((eval_sharded hs hT (r := a) hw.1 hc.1).flatMap_right _).trans ?_
        rw [List.flatMap_assoc]
        exact .of_eq (flatMap_congr fun c hm => by
          rw [hs.const_eval hc.2 c hm, arity_congr (hs.arity c hm) b])
      · have hco : coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat)
            (b.keyCols S K T cat) (a.arity cat) on = true := by simpa [hc] using h
        obtain ⟨hla, hlb⟩ := coCond_linear hco
        refine (((eval_sharded hs hT (r := a) hw.1 hla).flatMap_right _).trans
          (flatMap_perm_congr fun x _ => leftJoinRow_perm x
            (eval_sharded hs hT (r := b) hw.2.1 hlb))).trans (.of_eq ?_)
        rw [flatMap_rowwise (m := fun x y => (on.eval (x ++ y)).isTrue) a.eval b.eval
          (leftJoinRow on (b.arity cat)) (fun x ys zs h => leftJoinRow_append_nomatch x ys zs h)
          (hs.coDisjoint hw.1 hw.2.1 hco)]
        exact flatMap_congr fun c hm => by rw [arity_congr (hs.arity c hm) b]
  | .semi a b anti on, hw, h => by
      simp only [linear] at h
      simp only [eval]
      by_cases hc : (a.linear S K T cat && b.const S) = true
      · simp only [Bool.and_eq_true] at hc
        refine ((eval_sharded hs hT (r := a) hw.1 hc.1).filter _).trans ?_
        rw [List.filter_flatMap]
        exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval hc.2 c hm])
      · have hco : coCond (a.linear S K T cat) (b.linear S K T cat) (a.keyCols S K T cat)
            (b.keyCols S K T cat) (a.arity cat) on = true := by simpa [hc] using h
        obtain ⟨hla, hlb⟩ := coCond_linear hco
        refine ((eval_sharded hs hT (r := a) hw.1 hla).filter _).trans (.of_eq ?_)
        rw [List.filter_congr fun x _ => by rw [hasMatch_perm (on := on) x
          (eval_sharded hs hT (r := b) hw.2.1 hlb)]]
        exact filter_rowwise (m := fun x y => (on.eval (x ++ y)).isTrue) a.eval b.eval
          (fun ys x => hasMatch on ys x != anti) (fun x ys zs h => by
            obtain ⟨h₁, h₂⟩ := hasMatch_append_nomatch (on := on) x ys zs h
            exact ⟨by rw [h₁], by rw [h₂]⟩)
          (hs.coDisjoint hw.1 hw.2.1 hco)
  | .distinct r, hw, h => by
      simp only [linear, Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨hl, kc, hk⟩ := h
      simp only [eval]
      refine (dedup_perm_of_mem fun _ => (eval_sharded hs hT (r := r) hw hl).mem_iff).trans ?_
      rw [flatMap_eq_flatten_map]
      refine (dedup_flatten_disjoint ((hs.rows_disjoint (r := r) hw hl hk).imp
        fun hab a ha b hb he => hab a ha b hb (by rw [he]))).trans (.of_eq ?_)
      simp [flatMap_eq_flatten_map, Function.comp_def]
  | .aggregate r gs ms, hw, h => by
      simp only [linear] at h
      cases hk : r.keyCols S K T cat with
      | none => simp [hk] at h
      | some kc =>
        simp only [hk, Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨⟨⟨hl, hg⟩, hms⟩, hkc⟩ := h
        have hg' : gs ≠ [] := by intro he; simp [he] at hg
        simp only [eval]
        refine (aggregateEval_perm hms (eval_sharded hs hT hw.1 hl)).trans ?_
        rw [flatMap_eq_flatten_map]
        refine (aggregateEval_flatten_disjoint hg' ((hs.rows_disjoint hw.1 hl hk).imp
          fun hab a ha b hb he => hab a ha b hb (keyOf_eq_of_groupKey hkc he))).trans (.of_eq ?_)
        simp [flatMap_eq_flatten_map, Function.comp_def]

/-! ## Plans -/

/-- `m` combines in two phases over the shards of a plan whose split key is
at `kc`: `COUNT`/`SUM(DISTINCT x)` too when `x` is the whole split key. -/
def Measure.twoPhase (kc : Option (List Nat)) (m : Measure) : Bool :=
  m.decomposable || (m.orderFree && match kc with
    | some [c] => m.arg == .field c
    | _ => false)

theorem Measure.orderFree_of_twoPhase {kc : Option (List Nat)} {m : Measure}
    (h : m.twoPhase kc = true) : m.orderFree = true := by
  simp only [twoPhase, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨h, _⟩
  · simp only [decomposable, Bool.and_eq_true] at h; exact h.1
  · exact h

theorem Measure.splitOk_of_twoPhase {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} (hw : r.WF cat)
    (hl : r.linear S K T cat = true) {m : Measure} (hm : m.twoPhase (r.keyCols S K T cat) = true) :
    m.SplitOk (cs.map r.eval) := by
  intro hd h₁ h₂
  simp only [twoPhase, Bool.or_eq_true, Bool.and_eq_true] at hm
  rcases hm with hm | ⟨_, hm⟩
  · exact splitOk_of_decomposable hm _ hd h₁ h₂
  · split at hm
    · rename_i c hk
      have harg : m.arg = .field c := by simpa using hm
      exact (hs.rows_disjoint hw hl hk).imp fun hab a ha b hb he =>
        hab a ha b hb (by
          simp only [harg, Expr.eval] at he
          show [a.getD c .null] = [b.getD c .null]
          rw [he])
    · simp at hm

/-- **Two-phase aggregation over shards**: aggregate each shard, then combine. -/
theorem Rel.eval_twoPhase {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) (hne : cs ≠ []) {r : Rel} {gs : List Expr}
    {ms : List Measure} (hw : r.WF cat) (hr : r.linear S K T cat = true) (hms : ∀ m ∈ ms, m.twoPhase (r.keyCols S K T cat) = true) :
    (aggregateEval gs ms (r.eval cat)).Perm
      (aggregateEval (keyFields gs.length) (combineMeasures gs.length ms)
        (cs.flatMap fun c => aggregateEval gs ms (r.eval c))) := by
  have hof := fun m hm => Measure.orderFree_of_twoPhase (hms m hm)
  refine (aggregateEval_perm hof (eval_sharded hs hT hw hr)).trans ?_
  have := twoPhase_correct (gs := gs) hof (ss := cs.map r.eval) (by simpa using hne)
    fun m hm => Measure.splitOk_of_twoPhase hs hw hr (hms m hm)
  rw [List.flatMap_map] at this
  rw [flatMap_eq_flatten_map]
  exact this.symm

/-! ### Doubles, unproved -/

/-- The partial measures for splitting `SUM`/`AVG` of doubles: `AVG` as a
`SUM` and a `COUNT`. -/
def floatPartial (m : Measure) : List Measure :=
  if m.fn = .avg then [{ m with fn := .fsum }, { m with fn := .count }] else [m]

/-- Splits with `floatCombine`: the measures of `Measure.twoPhase`, and
`SUM`/`AVG` of doubles (not `DISTINCT`). -/
def Measure.floatSplittable (kc : Option (List Nat)) (m : Measure) : Bool :=
  m.twoPhase kc || ((m.fn == .fsum || m.fn == .avg) && !m.distinct)

/-- Combine the partial rows of `floatPartial` (keys first): `SUM` of the
partial sums, and an `AVG` as the sum of its sums over the sum of its
counts. There is no theorem: the rounding of the sums depends on the split. -/
def floatCombine (k : Nat) (ms : List Measure) (input : Rel) : Rel :=
  let widths := ms.map fun m => if m.fn = .avg then 2 else 1
  let offs := (List.range ms.length).map fun i => (widths.take i).sum
  let total := widths.sum
  let cms := (ms.zip offs).flatMap fun (m, o) =>
    if m.fn = .avg then
      [{ fn := .fsum, arg := .field (k + o) }, { fn := .sum, arg := .field (k + o + 1) : Measure }]
    else [{ fn := m.fn.combine, arg := .field (k + o) }]
  let avgs := (ms.zip offs).filter (·.1.fn = .avg)
  let divs := avgs.map fun (_, o) => Expr.bin .fdiv (.field (k + o)) (.un .itof (.field (k + o + 1)))
  let out := (ms.zip offs).map fun (m, o) =>
    if m.fn = .avg then k + total + avgs.findIdx (·.2 == o) else k + o
  .emit (.project (.aggregate input (keyFields k) cms) divs) (List.range k ++ out)

/-- The aggregate below the filters, projections and sorts at the top of a plan,
split into the plan each shard runs and the plan that combines their
results, which reads them from the table `P`. With `floats`, `SUM` and `AVG`
of doubles split too (`floatCombine`, unproved). -/
def Rel.splitAgg (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog)
    (P : String)
    (floats : Bool) : Rel → Option (Rel × Rel)
  | .aggregate r gs ms =>
      if r.linear S K T cat && ms.all (·.twoPhase (r.keyCols S K T cat)) then
        some (.aggregate r gs ms,
          .aggregate (.read P) (keyFields gs.length) (combineMeasures gs.length ms))
      else if floats && r.linear S K T cat && ms.all (·.floatSplittable (r.keyCols S K T cat)) then
        some (.aggregate r gs (ms.flatMap floatPartial), floatCombine gs.length ms (.read P))
      else none
  | .filter r c => (r.splitAgg S K T cat P floats).map fun pq => (pq.1, .filter pq.2 c)
  | .project r es => (r.splitAgg S K T cat P floats).map fun pq => (pq.1, .project pq.2 es)
  | .emit r m => (r.splitAgg S K T cat P floats).map fun pq => (pq.1, .emit pq.2 m)
  | .orderBy r keys => (r.splitAgg S K T cat P floats).map fun pq => (pq.1, .orderBy pq.2 keys)
  | _ => none

/-- Sharded evaluation of `r`: the plan each shard runs, and the plan that
combines their results (read from the table `P`). A linear plan's results
are just concatenated. -/
def Rel.shardSplit (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog)
    (P : String)
    (floats : Bool) (r : Rel) : Option (Rel × Rel) :=
  if r.linear S K T cat then some (r, .read P) else r.splitAgg S K T cat P floats

theorem Rel.splitAgg_sound {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) (hne : cs ≠ []) {C : Catalog} :
    ∀ {r p q : Rel}, r.WF cat → r.splitAgg S K T cat P false = some (p, q) →
      (C P).rows = cs.flatMap p.eval → (r.eval cat).Perm (q.eval C)
  | .aggregate r gs ms, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval, hC]
      exact eval_twoPhase hs hT hne hw.1 hc.1 hc.2
    · split at h
      · rename_i hc; simp at hc
      · simp at h
  | .filter r c, p, q, hw, h, hC | .project r c, p, q, hw, h, hC | .emit r c, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K T cat P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := splitAgg_sound hs hT hne (r := r) hw.1 hr hC
      simp only [eval]
      first | exact ih.filter _ | exact ih.map _
  | .orderBy r keys, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K T cat P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((splitAgg_sound hs hT hne (r := r) hw.1 hr hC).trans
        (List.mergeSort_perm _ _).symm)
  | .read _, _, _, _, h, _ | .values _ _, _, _, _, h, _ | .cross _ _, _, _, _, h, _
  | .join _ _ _ _, _, _, _, h, _ | .fetch _ _ _, _, _, _, h, _ | .unionAll _ _, _, _, _, h, _
  | .window _ _ _ _, _, _, _, h, _ | .semi _ _ _ _, _, _, _, h, _ | .distinct _, _, _, _, h, _ => by
    simp [splitAgg] at h

/-- **Sharded evaluation is sound**: run `p` on every shard, put the results
in table `P`, and `q` gives the plan's result. -/
theorem Rel.shardSplit_sound {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) (hne : cs ≠ []) {C : Catalog}
    {r p q : Rel} (hw : r.WF cat) (h : r.shardSplit S K T cat P false = some (p, q))
    (hC : (C P).rows = cs.flatMap p.eval) : (r.eval cat).Perm (q.eval C) := by
  unfold shardSplit at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval, hC]
    exact eval_sharded hs hT hw hl
  · exact splitAgg_sound hs hT hne hw h hC

/-! ## 64-bit partial sums -/

theorem intSum_flatten_split {L : List (List Value)} {vs : List Value} (hvs : vs ∈ L) :
    ∃ s t : List (List Value), (s ⊆ L ∧ t ⊆ L) ∧
      intSum L.flatten = intSum s.flatten + intSum vs + intSum t.flatten := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hvs
  refine ⟨s, t, ⟨fun x hx => by simp [hx], fun x hx => by simp [hx]⟩, ?_⟩
  simp only [List.flatten_append, List.flatten_cons, intSum_append]
  omega

/-- **No spurious overflow**: when no value is negative (or none is
positive), every partial sum lies between 0 and the total, so it fits in 64
bits whenever the total does. -/
theorem inI64_partial {L : List (List Value)}
    (h : (∀ vs ∈ L, ∀ i, .int i ∈ vs → 0 ≤ i) ∨ (∀ vs ∈ L, ∀ i, .int i ∈ vs → i ≤ 0))
    (ht : inI64 (intSum L.flatten) = true) : ∀ vs ∈ L, inI64 (intSum vs) = true := by
  intro vs hvs
  obtain ⟨s, t, ⟨hs, htl⟩, he⟩ := intSum_flatten_split hvs
  have flat {P : Int → Prop} (hP : ∀ vs ∈ L, ∀ i, .int i ∈ vs → P i) {s : List (List Value)}
      (hs : s ⊆ L) : ∀ i, .int i ∈ s.flatten → P i := fun i hi => by
    obtain ⟨l, hl, hi⟩ := List.mem_flatten.mp hi; exact hP l (hs hl) i hi
  rw [he] at ht
  simp only [inI64, Bool.and_eq_true, FloatCode.minI64, FloatCode.maxI64] at ht ⊢
  have ht₁ := of_decide_eq_true ht.1
  have ht₂ := of_decide_eq_true ht.2
  have : 0 ≤ intSum vs ∧ intSum vs ≤ intSum s.flatten + intSum vs + intSum t.flatten ∨
      intSum vs ≤ 0 ∧ intSum s.flatten + intSum vs + intSum t.flatten ≤ intSum vs := by
    rcases h with h | h
    · have := intSum_nonneg (h vs hvs)
      have := intSum_nonneg (flat h hs)
      have := intSum_nonneg (flat h htl)
      omega
    · have := intSum_nonpos (h vs hvs)
      have := intSum_nonpos (flat h hs)
      have := intSum_nonpos (flat h htl)
      omega
  exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩

end Substrait

