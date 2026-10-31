import SubstraitLean.Weighted
import SubstraitLean.Safety

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
  | .null :: vs, ws | .bool _ :: vs, ws | .str _ :: vs, ws => by
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
def Rel.linear (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog) : Rel → Bool
  | .read t => S t
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => r.linear S K cat
  | .unionAll a b => a.linear S K cat && b.linear S K cat
  | .cross a b | .join a b .inner _ =>
      (a.linear S K cat && b.const S) || (a.const S && b.linear S K cat)
  | .join a b .left _ | .semi a b _ _ => a.linear S K cat && b.const S
  | .distinct r => r.linear S K cat && (r.keyCols S K cat).isSome
  | .aggregate r gs ms => r.linear S K cat && !gs.isEmpty && ms.all (·.orderFree) &&
      match r.keyCols S K cat with
      | some kc => kc.all fun c => gs.contains (.field c)
      | none => false
  -- A literal table would be repeated on every shard.
  | .values _ _ | .fetch _ _ _ | .window _ _ _ _ => false

/-- Where the split key is in the output of a linear plan (`Rel.keyRows`). -/
def Rel.keyCols (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog) :
    Rel → Option (List Nat)
  | .read t => if S t then K t else none
  | .filter r _ | .orderBy r _ | .distinct r | .semi r _ _ _ | .join r _ .left _ =>
      r.keyCols S K cat
  -- A key column the projection copies: the copy (an emit may keep only it).
  | .project r es => (r.keyCols S K cat).map (·.map (copyPos (r.arity cat) es))
  | .emit r m => (r.keyCols S K cat).bind (posAll m)
  | .cross a b | .join a b .inner _ =>
      if a.linear S K cat && b.const S then a.keyCols S K cat else none
  | .unionAll a b => if a.keyCols S K cat == b.keyCols S K cat then a.keyCols S K cat else none
  | .aggregate r gs _ => (r.keyCols S K cat).bind fun kc => posAll gs (kc.map .field)
  | .values _ _ | .fetch _ _ _ | .window _ _ _ _ => none
end

theorem Sharding.const_eval {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} (h : r.const S = true) :
    ∀ c ∈ cs, r.eval c = r.eval cat :=
  fun c hc => Rel.eval_congr (hs.arity c hc) fun t ht => by
    simp only [Rel.const, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact hs.bcast t (h t ht) c hc

theorem Sharding.cross {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {a b : Rel}
    (ha : a.linear S K cat = true → (a.eval cat).Perm (cs.flatMap a.eval))
    (hb : b.linear S K cat = true → (b.eval cat).Perm (cs.flatMap b.eval))
    (h : (a.linear S K cat && b.const S || a.const S && b.linear S K cat) = true) :
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
theorem Rel.keyRows {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {c : Catalog} (hc : c ∈ cs) :
    ∀ {r : Rel} {kc : List Nat}, r.WF cat → r.linear S K cat = true →
      r.keyCols S K cat = some kc → ∀ row ∈ r.eval c, KeyFrom S K c kc row
  | .read t, kc, _, hl, hk, row, h => by
    simp only [linear] at hl
    simp only [keyCols, hl, ↓reduceIte] at hk
    exact ⟨fun i hi => hs.keyLen c hc t kc hl hk row h i hi, t, kc, hl, hk, row, h, rfl⟩
  | .values _ _, _, _, hl, _, _, _ | .fetch _ _ _, _, _, hl, _, _, _
  | .window _ _ _ _, _, _, hl, _, _, _ => by
    simp [linear] at hl
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
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    simp only [eval, List.mem_filter] at h
    exact keyRows hs hc (r := r) hw.1 hl.1 hk row h.1
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
      simp only [Bool.and_eq_true] at hab
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, _, rfl⟩, _⟩ := h
      exact (keyRows hs hc (r := a) hw.1 hab.1 hk x hx).append y
    · simp at hk
  | .join a b .left _, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    simp only [eval, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨z, rfl⟩ := leftJoinRow_prefix h
    exact (keyRows hs hc (r := a) hw.1 hl.1 hk x hx).append z
  | .unionAll a b, kc, hw, hl, hk, row, h => by
    simp only [linear, Bool.and_eq_true] at hl
    simp only [keyCols] at hk
    split at hk
    · rename_i hab
      have hb : b.keyCols S K cat = some kc := by rw [← beq_iff_eq.mp hab]; exact hk
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
theorem Sharding.rows_disjoint {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} {kc : List Nat} (hw : r.WF cat)
    (hl : r.linear S K cat = true) (hk : r.keyCols S K cat = some kc) :
    (cs.map r.eval).Pairwise fun A B => ∀ a ∈ A, ∀ b ∈ B, keyOf kc a ≠ keyOf kc b :=
  List.pairwise_map.mpr (hs.keyDisj.imp_of_mem fun hc hc' hd a ha b hb he => by
    obtain ⟨_, t, kt, h₁, h₂, x, hx, ex⟩ := Rel.keyRows hs hc hw hl hk a ha
    obtain ⟨_, t', kt', h₁', h₂', y, hy, ey⟩ := Rel.keyRows hs hc' hw hl hk b hb
    exact hd t t' kt kt' h₁ h₁' h₂ h₂' x hx y hy (by rw [← ex, ← ey, he]))

/-- **Sharded evaluation**: a linear plan's result on the whole tables is the
union of its results on the shards. -/
theorem Rel.eval_sharded {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) :
    ∀ {r : Rel}, r.WF cat → r.linear S K cat = true → (r.eval cat).Perm (cs.flatMap r.eval)
  | .read t, _, h => hs.split t h
  | .values _ _, _, h | .fetch _ _ _, _, h | .window _ _ _ _, _, h => by
      simp [linear] at h
  | .filter r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact ((eval_sharded hs (r := r) hw.1 h).filter _).trans (.of_eq List.filter_flatMap)
  | .project r _, hw, h | .emit r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact ((eval_sharded hs (r := r) hw.1 h).map _).trans (.of_eq List.map_flatMap)
  | .orderBy r _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((eval_sharded hs (r := r) hw.1 h).trans
        (flatMap_perm_congr fun _ _ => (List.mergeSort_perm _ _).symm))
  | .unionAll a b, hw, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      exact ((eval_sharded hs (r := a) hw.1 h.1).append (eval_sharded hs (r := b) hw.2.1 h.2)).trans
        (flatMap_append_perm _ _ _)
  | .cross a b, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact hs.cross (eval_sharded hs (r := a) hw.1) (eval_sharded hs (r := b) hw.2) h
  | .join a b .inner _, hw, h => by
      simp only [linear] at h
      simp only [eval]
      exact ((hs.cross (eval_sharded hs (r := a) hw.1) (eval_sharded hs (r := b) hw.2.1) h).filter
        _).trans (.of_eq List.filter_flatMap)
  | .join a b .left on, hw, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      refine ((eval_sharded hs (r := a) hw.1 h.1).flatMap_right _).trans ?_
      rw [List.flatMap_assoc]
      exact .of_eq (flatMap_congr fun c hm => by
        rw [hs.const_eval h.2 c hm, arity_congr (hs.arity c hm) b])
  | .semi a b _ _, hw, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      refine ((eval_sharded hs (r := a) hw.1 h.1).filter _).trans ?_
      rw [List.filter_flatMap]
      exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval h.2 c hm])
  | .distinct r, hw, h => by
      simp only [linear, Bool.and_eq_true, Option.isSome_iff_exists] at h
      obtain ⟨hl, kc, hk⟩ := h
      simp only [eval]
      refine (dedup_perm_of_mem fun _ => (eval_sharded hs (r := r) hw hl).mem_iff).trans ?_
      rw [flatMap_eq_flatten_map]
      refine (dedup_flatten_disjoint ((hs.rows_disjoint (r := r) hw hl hk).imp
        fun hab a ha b hb he => hab a ha b hb (by rw [he]))).trans (.of_eq ?_)
      simp [flatMap_eq_flatten_map, Function.comp_def]
  | .aggregate r gs ms, hw, h => by
      simp only [linear] at h
      cases hk : r.keyCols S K cat with
      | none => simp [hk] at h
      | some kc =>
        simp only [hk, Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨⟨⟨hl, hg⟩, hms⟩, hkc⟩ := h
        have hg' : gs ≠ [] := by intro he; simp [he] at hg
        simp only [eval]
        refine (aggregateEval_perm hms (eval_sharded hs hw.1 hl)).trans ?_
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

theorem Measure.splitOk_of_twoPhase {S : String → Bool} {K : String → Option (List Nat)}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) {r : Rel} (hw : r.WF cat)
    (hl : r.linear S K cat = true) {m : Measure} (hm : m.twoPhase (r.keyCols S K cat) = true) :
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
theorem Rel.eval_twoPhase {S : String → Bool} {K : String → Option (List Nat)} {cat : Catalog}
    {cs : List Catalog} (hs : Sharding S K cat cs) (hne : cs ≠ []) {r : Rel} {gs : List Expr}
    {ms : List Measure} (hw : r.WF cat) (hr : r.linear S K cat = true) (hms : ∀ m ∈ ms, m.twoPhase (r.keyCols S K cat) = true) :
    (aggregateEval gs ms (r.eval cat)).Perm
      (aggregateEval (keyFields gs.length) (combineMeasures gs.length ms)
        (cs.flatMap fun c => aggregateEval gs ms (r.eval c))) := by
  have hof := fun m hm => Measure.orderFree_of_twoPhase (hms m hm)
  refine (aggregateEval_perm hof (eval_sharded hs hw hr)).trans ?_
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
def Rel.splitAgg (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog) (P : String)
    (floats : Bool) : Rel → Option (Rel × Rel)
  | .aggregate r gs ms =>
      if r.linear S K cat && ms.all (·.twoPhase (r.keyCols S K cat)) then
        some (.aggregate r gs ms,
          .aggregate (.read P) (keyFields gs.length) (combineMeasures gs.length ms))
      else if floats && r.linear S K cat && ms.all (·.floatSplittable (r.keyCols S K cat)) then
        some (.aggregate r gs (ms.flatMap floatPartial), floatCombine gs.length ms (.read P))
      else none
  | .filter r c => (r.splitAgg S K cat P floats).map fun pq => (pq.1, .filter pq.2 c)
  | .project r es => (r.splitAgg S K cat P floats).map fun pq => (pq.1, .project pq.2 es)
  | .emit r m => (r.splitAgg S K cat P floats).map fun pq => (pq.1, .emit pq.2 m)
  | .orderBy r keys => (r.splitAgg S K cat P floats).map fun pq => (pq.1, .orderBy pq.2 keys)
  | _ => none

/-- Sharded evaluation of `r`: the plan each shard runs, and the plan that
combines their results (read from the table `P`). A linear plan's results
are just concatenated. -/
def Rel.shardSplit (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog) (P : String)
    (floats : Bool) (r : Rel) : Option (Rel × Rel) :=
  if r.linear S K cat then some (r, .read P) else r.splitAgg S K cat P floats

theorem Rel.splitAgg_sound {S : String → Bool} {K : String → Option (List Nat)} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hne : cs ≠ []) {C : Catalog} :
    ∀ {r p q : Rel}, r.WF cat → r.splitAgg S K cat P false = some (p, q) →
      (C P).rows = cs.flatMap p.eval → (r.eval cat).Perm (q.eval C)
  | .aggregate r gs ms, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval, hC]
      exact eval_twoPhase hs hne hw.1 hc.1 hc.2
    · split at h
      · rename_i hc; simp at hc
      · simp at h
  | .filter r c, p, q, hw, h, hC | .project r c, p, q, hw, h, hC | .emit r c, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K cat P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := splitAgg_sound hs hne (r := r) hw.1 hr hC
      simp only [eval]
      first | exact ih.filter _ | exact ih.map _
  | .orderBy r keys, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K cat P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((splitAgg_sound hs hne (r := r) hw.1 hr hC).trans
        (List.mergeSort_perm _ _).symm)
  | .read _, _, _, _, h, _ | .values _ _, _, _, _, h, _ | .cross _ _, _, _, _, h, _
  | .join _ _ _ _, _, _, _, h, _ | .fetch _ _ _, _, _, _, h, _ | .unionAll _ _, _, _, _, h, _
  | .window _ _ _ _, _, _, _, h, _ | .semi _ _ _ _, _, _, _, h, _ | .distinct _, _, _, _, h, _ => by
    simp [splitAgg] at h

/-- **Sharded evaluation is sound**: run `p` on every shard, put the results
in table `P`, and `q` gives the plan's result. -/
theorem Rel.shardSplit_sound {S : String → Bool} {K : String → Option (List Nat)} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hne : cs ≠ []) {C : Catalog}
    {r p q : Rel} (hw : r.WF cat) (h : r.shardSplit S K cat P false = some (p, q))
    (hC : (C P).rows = cs.flatMap p.eval) : (r.eval cat).Perm (q.eval C) := by
  unfold shardSplit at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval, hC]
    exact eval_sharded hs hw hl
  · exact splitAgg_sound hs hne hw h hC

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

