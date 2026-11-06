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
* `Rel.eval_algebraic`: algebraic aggregates, a final expression over
  distributive partials (#245), split the same way, and the final
  expressions run after combining. The integer `AVG` is a `SUM` and a
  `COUNT` per shard, then `SUM / COUNT`, when its argument is an integer
  (`IntArgs`).
* `Rel.shardSplit_sound`: `Rel.shardSplit` turns a plan into the plan each
  shard runs and the plan that combines their outputs, with filters,
  projections and sorts above the aggregate moved to the combining plan.

Refused, because the result depends on how the rows are split:

* `SUM` and `AVG` of doubles: each shard's sum is rounded, so a split rounds
  differently from the whole's one rounding (D25, `floatSumCR`).
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
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unionAll r _ | .semi r _ _ _
  | .unnest r _ => by
      simp only [arity, arity_congr h r]
  | .project r _ | .window r _ _ _ => by simp only [arity, arity_congr h r]
  | .cross a b | .join a b _ _ => by simp only [arity, arity_congr h a, arity_congr h b]

theorem Rel.eval_congr {c cat : Catalog} (ha : ∀ t, (c t).arity = (cat t).arity) :
    ∀ {r : Rel}, (∀ t ∈ r.tables, (c t).rows = (cat t).rows) → r.eval c = r.eval cat
  | .read t, h => h t (by simp [tables])
  | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .fetch r _ _, h | .window r _ _ _, h
  | .orderBy r _, h | .distinct r, h | .aggregate r _ _, h | .unnest r _, h => by
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
  | .fsum | .avg | .iavg | .collect | .bit _ | .var _ _ | .pick _ | .cov _ | .corr | .concat _ =>
    false
  -- A black box's laws say nothing of its partial results.
  | .bbox _ => false
  -- A quantile or mode needs every value of the group (#53).
  | .quantile _ _ _ | .mode => false

theorem AggFn.ne_collect {f : AggFn} (h : f.decomposable = true) : f.sorts = false := by
  cases f <;> simp_all [decomposable, sorts]

/-- The value depends on the multiset of values only: the decomposable
aggregates, and a `SUM` or `AVG` of doubles, which is the exact sum rounded
once (D25, `floatSumCR_perm`). The doubles' sums do not combine in two phases:
their partial results are rounded. -/
def AggFn.orderFree (f : AggFn) : Bool := f.decomposable || f == .fsum || f == .avg

theorem AggFn.orderFree_of_decomposable {f : AggFn} (h : f.decomposable = true) :
    f.orderFree = true := by
  simp [orderFree, h]

theorem AggFn.ne_collect_of_orderFree {f : AggFn} (h : f.orderFree = true) : f.sorts = false := by
  cases f <;> simp_all [orderFree, decomposable, sorts]

theorem AggFn.apply_nil_of_ne_count {f : AggFn} (hf : f ≠ .count) (hb : ∀ n, f ≠ .bbox n) :
    f.apply [] = .null := by
  cases f <;> first | rfl | exact (hf rfl).elim | exact (hb _ rfl).elim

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
  -- The rest are not decomposable.
  all_goals simp [decomposable] at hf

/-- Order-free aggregates do not depend on the order of their values. -/
theorem AggFn.apply_perm_of_orderFree {f : AggFn} (hf : f.orderFree = true) {vs ws : List Value}
    (h : vs.Perm ws) : f.apply vs = f.apply ws := by
  by_cases hd : f.decomposable = true
  · exact apply_perm hd h
  · have hf' : f = .fsum ∨ f = .avg := by cases f <;> simp_all [orderFree, decomposable]
    cases vs with
    | nil => rw [← h.nil_eq]
    | cons v vs =>
      cases ws with
      | nil => exact absurd h.eq_nil (by simp)
      | cons w ws =>
        rcases hf' with rfl | rfl
        · simp only [apply, floatSumCR_perm h]
        · simp only [apply, floatAvgCR_perm h]

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
  have hnil := AggFn.apply_nil_of_ne_count hcount (by cases max <;> simp [hf])
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
  -- The rest are not decomposable.
  all_goals simp [decomposable] at hf

/-! ## Measures that combine -/

/-- The value depends only on the bag of rows (`AggFn.orderFree`). -/
def Measure.orderFree (m : Measure) : Bool := m.fn.orderFree

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
  rw [eval_eq (AggFn.ne_collect_of_orderFree hm), eval_eq (AggFn.ne_collect_of_orderFree hm)]
  simp only [inputs_eq]
  refine AggFn.apply_perm_of_orderFree hm ?_
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
theorem Measure.combine_eval {m : Measure} (hm : m.fn.decomposable = true) {ss : List Relation}
    (hne : ss ≠ []) (hs : m.SplitOk ss) :
    m.fn.combine.apply ((ss.map m.eval).filter (· != .null)) = m.eval ss.flatten := by
  have hL : ss.map m.inputs ≠ [] := by simpa using hne
  have hnn : ∀ vs ∈ ss.map m.inputs, ∀ v ∈ vs, v ≠ .null := fun vs hvs v hv => by
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hvs
    exact (mem_inputs hv).1
  have hc := AggFn.ne_collect (f := m.fn) hm
  have hmap : ss.map m.eval = (ss.map m.inputs).map m.fn.apply := by
    simp [eval_eq hc, Function.comp_def]
  rw [hmap, AggFn.combine_apply hm hL hnn]
  rw [eval_eq hc]
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
  have hsort : rows.mergeSort (sortLe []) = rows :=
    List.mergeSort_of_pairwise (List.pairwise_iff_forall_sublist.mpr fun _ => by simp [sortLe])
  unfold Measure.eval
  split <;> simp_all [combineMeasures, Measure.inputs, Measure.kept, Expr.eval]

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
    (hms : ∀ m ∈ ms, m.fn.decomposable = true) {ss : List Relation} (hne : ss ≠ [])
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
  | .orderBy r _, hw | .aggregate r _ _, hw | .unnest r _, hw =>
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
  | .values _ _ | .fetch _ _ _ | .unnest _ _ => false

/-- Where the split key is in the output of a linear plan (`Rel.keyRows`). -/
def Rel.keyCols (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog) :
    Rel → Option (List Nat)
  | .read t => if S t then K t else none
  | .filter r _ | .orderBy r _ | .distinct r | .semi r _ _ _ | .join r _ .left _
  | .window r _ _ _ | .unnest r _ => r.keyCols S K T cat
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
  m.decomposable || (m.fn.decomposable && match kc with
    | some [c] => m.arg == .field c
    | _ => false)

theorem Measure.fnDecomposable_of_twoPhase {kc : Option (List Nat)} {m : Measure}
    (h : m.twoPhase kc = true) : m.fn.decomposable = true := by
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
  have hdec := fun m hm => Measure.fnDecomposable_of_twoPhase (hms m hm)
  have hof : ∀ m ∈ ms, m.orderFree = true := fun m hm => AggFn.orderFree_of_decomposable (hdec m hm)
  refine (aggregateEval_perm hof (eval_sharded hs hT hw hr)).trans ?_
  have := twoPhase_correct (gs := gs) hdec (ss := cs.map r.eval) (by simpa using hne)
    fun m hm => Measure.splitOk_of_twoPhase hs hw hr (hms m hm)
  rw [List.flatMap_map] at this
  rw [flatMap_eq_flatten_map]
  exact this.symm

/-! ## Algebraic aggregates

An aggregate is algebraic when a final expression computes it from a tuple
of distributive partial aggregates (#245): each shard computes the partials,
the combining phase combines each of them (`combineMeasures`), and the final
expression gives the result. The theorem is `Rel.eval_algebraic`, for any
measure with partials (`Measure.part`, `Measure.part₂`) and a final
expression (`algFinal`) for which `Measure.final_eval` holds.

The instance is the integer `AVG` (`AggFn.iavg`): the `SUM` of its values and
their `COUNT`, and the final `SUM / COUNT` (`BinFn.idiv`: truncated toward
zero, NULL without values). It is exact, but the model's `iavg` clamps the
mean between the smallest and largest integer (`clampInts`), which changes
nothing only when every value is an integer. `IntArgs` vouches for that, from
the tables' column types (`IntArgs.ofTypes`). -/

def Value.intOrNull : Value → Bool
  | .null | .int _ => true
  | _ => false

/-- Expressions that give only integers or NULL on the rows of a plan. -/
abbrev IntArgs := Rel → Expr → Bool

def IntArgs.Sound (I : IntArgs) (cat : Catalog) : Prop :=
  ∀ r e, I r e = true → r.WF cat → ∀ row ∈ r.eval cat, (e.eval row).intOrNull = true

/-- `IntArgs` from the tables' column types `A`, by abstract evaluation. -/
def IntArgs.ofTypes (cat : Catalog) (A : String → List AVal) : IntArgs := fun r e =>
  let a := e.absD (r.aeval cat A (fun _ => []) WindowKeys.none) []
  !a.tt && !a.ff && !a.str

theorem AVal.intOrNull_of_mem {a : AVal} {v : Value} (h : a.Mem v) (ht : a.tt = false)
    (hf : a.ff = false) (hs : a.str = false) : v.intOrNull = true := by
  cases v with
  | null => rfl
  | int _ => rfl
  | bool b => cases b <;> simp_all [AVal.Mem]
  | str _ => simp_all [AVal.Mem]
  | list _ => simp_all [AVal.Mem]

/-- Sound for rows of the declared types. -/
theorem IntArgs.ofTypes_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row) : (IntArgs.ofTypes cat A).Sound cat := by
  intro r e h hw row hrow
  simp only [ofTypes, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hm := Rel.aeval_sound hcat hA (F := fun _ => []) (fun _ _ _ => by simp [FactsHold])
    (T := WindowKeys.none) (fun _ _ _ h _ => by simp [WindowKeys.none] at h) (sz := false) hw
    (by simp) row hrow
  exact AVal.intOrNull_of_mem
    (Expr.absD_sound hm (by simp [FactsHold]) (by simp [KsHold]) e) h.1.1 h.1.2 h.2

theorem ediv_mean_between {lo hi s n : Int} (hn : 0 < n) (h₁ : n * lo ≤ s) (h₂ : s ≤ n * hi) :
    lo ≤ s / n ∧ s / n ≤ hi :=
  ⟨Int.le_ediv_of_mul_le hn (by rw [Int.mul_comm]; exact h₁),
    Int.ediv_le_of_le_mul hn (by rw [Int.mul_comm]; exact h₂)⟩

/-- A truncated mean lies between the bounds of the values. -/
theorem tdiv_mean_between {lo hi s n : Int} (hn : 0 < n) (h₁ : n * lo ≤ s) (h₂ : s ≤ n * hi) :
    lo ≤ s.tdiv n ∧ s.tdiv n ≤ hi := by
  rcases Int.le_total 0 s with hs | hs
  · rw [Int.tdiv_eq_ediv_of_nonneg hs]; exact ediv_mean_between hn h₁ h₂
  · have : s.tdiv n = -((-s).tdiv n) := by rw [Int.neg_tdiv, Int.neg_neg]
    rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have := ediv_mean_between (lo := -hi) (hi := -lo) (s := -s) hn
      (by rw [Int.mul_neg]; omega) (by rw [Int.mul_neg]; omega)
    omega

theorem intSum_between {lo hi : Int} : ∀ {vs : List Value},
    (∀ v ∈ vs, ∃ i, v = .int i ∧ lo ≤ i ∧ i ≤ hi) →
      (vs.length : Int) * lo ≤ intSum vs ∧ intSum vs ≤ (vs.length : Int) * hi
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    obtain ⟨i, rfl, h₁, h₂⟩ := h v (by simp)
    have ih := intSum_between (vs := vs) fun w hw => h w (by simp [hw])
    simp only [intSum, List.length_cons, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

/-- Of integers, the truncated mean needs no clamping. -/
theorem clampInts_mean {vs : List Value} (h : ∀ v ∈ vs, ∃ i, v = .int i) (hne : vs ≠ []) :
    clampInts vs ((intSum vs).tdiv vs.length) = (intSum vs).tdiv vs.length := by
  unfold clampInts
  split
  · rename_i hx
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨i, rfl⟩ := h v hv
    have : i ∈ intsOf vs := mem_intsOf.mpr hv
    simp [hx] at this
  · rename_i x xs hx
    have hb : ∀ v ∈ vs, ∃ i, v = .int i ∧ xs.foldl min x ≤ i ∧ i ≤ xs.foldl max x := by
      intro v hv
      obtain ⟨i, rfl⟩ := h v hv
      have hi : i ∈ x :: xs := by rw [← hx]; exact mem_intsOf.mpr hv
      exact ⟨i, rfl, foldl_min_le x xs i hi, foldl_max_ge x xs i hi⟩
    have hn : (0 : Int) < vs.length := by
      cases vs with
      | nil => exact absurd rfl hne
      | cons _ _ => simp only [List.length_cons]; omega
    obtain ⟨h₁, h₂⟩ := intSum_between hb
    obtain ⟨h₃, h₄⟩ := tdiv_mean_between hn h₁ h₂
    rw [Int.max_eq_left h₃, Int.min_eq_left h₄]

/-- The partial measure in `m`'s own column: the `SUM` of an integer `AVG`. -/
def Measure.part (m : Measure) : Measure := if m.fn = .iavg then { m with fn := .sum } else m

/-- The second partial measure, of an integer `AVG` only: its `COUNT`. -/
def Measure.part₂ (m : Measure) : Option Measure :=
  if m.fn = .iavg then some { m with fn := .count } else none

/-- The partial measures of `ms`: one per measure, then the `COUNT`s of the
integer `AVG`s. -/
def algParts (ms : List Measure) : List Measure := ms.map Measure.part ++ ms.filterMap Measure.part₂

/-- Where the second partial of measure `i` is among `algParts ms`. -/
def algPos₂ (ms : List Measure) (i : Nat) : Nat :=
  ms.length + ((ms.take i).filterMap Measure.part₂).length

/-- The final expressions over a combined row, whose first `k` columns are
the keys and the rest the partials: `SUM / COUNT` for an integer `AVG`, the
partial itself for the others. -/
def algFinal (k : Nat) (ms : List Measure) : List Expr :=
  ms.mapIdx fun i m =>
    if m.fn = .iavg then .bin .idiv (.field (k + i)) (.field (k + algPos₂ ms i)) else .field (k + i)

/-- The columns of the result among the combined row and its final values:
the keys, then the final values. -/
def algOut (k : Nat) (ms : List Measure) : List Nat :=
  List.range k ++ (List.range ms.length).map (k + (algParts ms).length + ·)

/-- Combine the partial rows of `algParts` (keys first), then compute the
final values. -/
def algCombine (k : Nat) (ms : List Measure) (input : Rel) : Rel :=
  .emit (.project (.aggregate input (keyFields k) (combineMeasures k (algParts ms))) (algFinal k ms))
    (algOut k ms)

/-- What `algCombine` does to each combined row. -/
def algFinish (k : Nat) (ms : List Measure) (row : Row) : Row :=
  (algOut k ms).map ((row ++ (algFinal k ms).map (·.eval row)).getD · .null)

theorem algCombine_eval (k : Nat) (ms : List Measure) (input : Rel) (C : Catalog) :
    (algCombine k ms input).eval C =
      (aggregateEval (keyFields k) (combineMeasures k (algParts ms)) (input.eval C)).map
        (algFinish k ms) := by
  simp only [algCombine, Rel.eval, List.map_map]
  rfl

/-- **The final step**: `SUM / COUNT` of an integer `AVG`'s values is the
`AVG`, when they are integers. -/
theorem Measure.final_eval {m : Measure} (hm : m.fn = .iavg) {rows : Relation}
    (hint : ∀ row ∈ rows, (m.arg.eval row).intOrNull = true) :
    BinFn.idiv.apply (({ m with fn := .sum } : Measure).eval rows)
      (({ m with fn := .count } : Measure).eval rows) = m.eval rows := by
  have hs : ({ m with fn := .sum } : Measure).eval rows = AggFn.sum.apply (m.inputs rows) :=
    Measure.eval_eq rfl rows
  have hc : ({ m with fn := .count } : Measure).eval rows = AggFn.count.apply (m.inputs rows) :=
    Measure.eval_eq rfl rows
  have he : m.eval rows = AggFn.iavg.apply (m.inputs rows) := by
    rw [Measure.eval_eq (by rw [hm]; rfl), hm]
  have hi : ∀ v ∈ m.inputs rows, ∃ i, v = .int i := by
    intro v hv
    obtain ⟨hn, row, hrow, rfl⟩ := Measure.mem_inputs hv
    have := hint row hrow
    revert hn this
    cases m.arg.eval row <;> simp [Value.intOrNull]
  rw [hs, hc, he]
  generalize m.inputs rows = vs at hi
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [AggFn.apply, BinFn.apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp; omega)), clampInts_mean hi (List.cons_ne_nil _ _)]

theorem filterMap_getD_take {α β : Type} (f : α → Option β) (l : List α) {i : Nat}
    (hi : i < l.length) {b : β} (hb : f l[i] = some b) (d : β) :
    (l.filterMap f).getD ((l.take i).filterMap f).length d = b := by
  have hl : l.filterMap f = (l.take i).filterMap f ++ b :: (l.drop (i + 1)).filterMap f := by
    conv => lhs; rw [← List.take_append_drop i l, List.drop_eq_getElem_cons hi]
    rw [List.filterMap_append, List.filterMap_cons_some hb]
  rw [hl]
  simp [List.getD_eq_getElem?_getD]

theorem algParts_length_ge (ms : List Measure) : ms.length ≤ (algParts ms).length := by
  simp [algParts]

/-- `algFinish` turns a group's partials into its result. -/
theorem algFinish_eval {k : Nat} {ms : List Measure} {key : Row} (hk : key.length = k)
    {g : Relation} (hint : ∀ m ∈ ms, m.fn = .iavg → ∀ row ∈ g, (m.arg.eval row).intOrNull = true) :
    algFinish k ms (key ++ (algParts ms).map (·.eval g)) = key ++ ms.map (·.eval g) := by
  subst hk
  generalize hrow : key ++ (algParts ms).map (·.eval g) = row
  have hlen : row.length = key.length + (algParts ms).length := by rw [← hrow]; simp
  -- The partials of measure `i`.
  have hp : ∀ i (hi : i < ms.length), row.getD (key.length + i) .null = ms[i].part.eval g := by
    intro i hi
    rw [← hrow, getD_append_len, algParts, List.map_append, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  have hp₂ : ∀ i (hi : i < ms.length), ms[i].fn = .iavg →
      row.getD (key.length + algPos₂ ms i) .null = ({ ms[i] with fn := .count } : Measure).eval g := by
    intro i hi hf
    have e : ∀ l : List Measure, l.filterMap (fun m => (Measure.part₂ m).map (·.eval g)) =
        (l.filterMap Measure.part₂).map (·.eval g) := fun l => (List.map_filterMap ..).symm
    have key := filterMap_getD_take (fun m => (Measure.part₂ m).map (·.eval g)) ms hi
      (b := ({ ms[i] with fn := .count } : Measure).eval g) (by simp [Measure.part₂, hf]) .null
    rw [e, e, List.length_map, List.getD_eq_getElem?_getD] at key
    rw [← hrow, getD_append_len, algParts, List.map_append, algPos₂, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_map, List.length_map,
      Nat.add_sub_cancel_left]
    exact key
  unfold algFinish algOut
  rw [List.map_append]
  congr 1
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hlen]; omega), ← hrow,
      List.getElem?_append_left h₁]
    simp [List.getElem?_eq_getElem h₁]
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_map] at h₂
    simp only [List.getElem_map, List.getElem_range]
    rw [show key.length + (algParts ms).length + i = row.length + i by rw [hlen], getD_append_len,
      algFinal, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_mapIdx,
      List.getElem?_eq_getElem h₂]
    simp only [Option.map_some, Option.getD_some]
    by_cases hf : ms[i].fn = .iavg
    · simp only [hf, ↓reduceIte, Expr.eval, BinFn.apply]
      rw [hp i h₂, hp₂ i h₂ hf, Measure.part, ite_eq_left_of_eq_true _ _ (eq_true hf)]
      exact Measure.final_eval hf (hint _ (List.getElem_mem h₂) hf)
    · simp only [hf, ↓reduceIte, Expr.eval]
      rw [hp i h₂, Measure.part, ite_eq_right_of_eq_false _ _ (eq_false hf)]

/-- `m` splits over the shards of `r`, whose split key is at `kc`, as a
distributive aggregate or an algebraic one. -/
def Measure.algebraic (I : IntArgs) (r : Rel) (kc : Option (List Nat)) (m : Measure) : Bool :=
  if m.fn = .iavg then
    I r m.arg && m.part.twoPhase kc && ({ m with fn := .count } : Measure).twoPhase kc
  else m.twoPhase kc

theorem algParts_twoPhase {I : IntArgs} {r : Rel} {kc : Option (List Nat)} {ms : List Measure}
    (h : ∀ m ∈ ms, m.algebraic I r kc = true) : ∀ p ∈ algParts ms, p.twoPhase kc = true := by
  intro p hp
  simp only [algParts, List.mem_append, List.mem_map, List.mem_filterMap] at hp
  rcases hp with ⟨m, hm, rfl⟩ | ⟨m, hm, he⟩
  · have := h m hm
    unfold Measure.algebraic at this
    unfold Measure.part
    split
    · rename_i hf
      rw [ite_eq_left_of_eq_true _ _ (eq_true hf)] at this
      simp only [Bool.and_eq_true] at this
      have h' := this.1.2
      rw [Measure.part, ite_eq_left_of_eq_true _ _ (eq_true hf)] at h'
      exact h'
    · rename_i hf
      rwa [ite_eq_right_of_eq_false _ _ (eq_false hf)] at this
  · have := h m hm
    unfold Measure.part₂ at he
    split at he
    · rename_i hf
      rw [Option.some.injEq] at he
      subst he
      rw [Measure.algebraic, ite_eq_left_of_eq_true _ _ (eq_true hf)] at this
      simp only [Bool.and_eq_true] at this
      exact this.2
    · simp at he

theorem aggregateEval_algFinish {gs : List Expr} {ms : List Measure} {rows : Relation}
    (hint : ∀ m ∈ ms, m.fn = .iavg → ∀ row ∈ rows, (m.arg.eval row).intOrNull = true) :
    (aggregateEval gs (algParts ms) rows).map (algFinish gs.length ms) = aggregateEval gs ms rows := by
  unfold aggregateEval
  split
  · rename_i hg
    have : gs = [] := List.isEmpty_iff.mp hg
    subst this
    have := algFinish_eval (k := 0) (key := []) rfl hint
    simpa using this
  · rw [List.map_map]
    refine List.map_congr_left fun key hk => ?_
    exact algFinish_eval (length_of_mem_keys hk) fun m hm hf row hrow => by
      simp only [groupRows, List.mem_filter] at hrow
      exact hint m hm hf row hrow.1

/-- **Algebraic aggregation over shards**: every shard computes the partials,
then they are combined and the final expressions give the aggregate. -/
theorem Rel.eval_algebraic {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) {I : IntArgs}
    (hI : I.Sound cat) (hne : cs ≠ []) {r : Rel} {gs : List Expr} {ms : List Measure}
    (hw : r.WF cat) (hr : r.linear S K T cat = true)
    (hms : ∀ m ∈ ms, m.algebraic I r (r.keyCols S K T cat) = true) :
    (aggregateEval gs ms (r.eval cat)).Perm
      ((aggregateEval (keyFields gs.length) (combineMeasures gs.length (algParts ms))
        (cs.flatMap fun c => aggregateEval gs (algParts ms) (r.eval c))).map
          (algFinish gs.length ms)) := by
  have hint : ∀ m ∈ ms, m.fn = .iavg → ∀ row ∈ r.eval cat, (m.arg.eval row).intOrNull = true := by
    intro m hm hf row hrow
    have := hms m hm
    rw [Measure.algebraic, ite_eq_left_of_eq_true _ _ (eq_true hf)] at this
    simp only [Bool.and_eq_true] at this
    exact hI r m.arg this.1.1 hw row hrow
  rw [← aggregateEval_algFinish hint]
  exact (eval_twoPhase hs hT hne hw hr (algParts_twoPhase hms)).map _

/-! ### Doubles, within a proved bound (#428)

A double `SUM` or `AVG` split over shards rounds each shard's exact sum,
then the exact sum of the partials (`floatCombine`), so it can differ from
the reference's one rounding of the whole (D25, `floatSumCR`). Its distance
from `Rel.eval`'s value is bounded by what the partial rows report: each
shard's `COUNT(x)` and rounded `SUM(|x|)` (`floatBoundParts`), and a bound on
the values from its `MAX(|x|)` (`floatSplit_sum`, `floatSplit_avg`). The
bound is proved here on integers (`twoPhaseSum_near`), with the native
division of a split `AVG` by `FloatCode.div_scaled_err`.
`float-bounds/FloatBounds/Shard.lean` bounds an engine's own two-phase sum,
in any order, over the reals (`shardTolScaled`). -/

/-- The partial measures for splitting `SUM`/`AVG` of doubles: `AVG` as a
`SUM` and a `COUNT`. -/
def floatPartial (m : Measure) : List Measure :=
  if m.fn = .avg then [{ m with fn := .fsum }, { m with fn := .count }] else [m]

/-- `|x|` of a double: `CASE WHEN x < 0 THEN -x ELSE x END`, which the writer
writes as `abs`. -/
def fabsExpr (e : Expr) : Expr := .ifThen (.bin .lt e (.lit (.int 0))) (.un .fneg e) e

/-- `|x|` of a double's code. -/
def fabsCode (c : Int) : Int := if c < 0 then FloatCode.neg c else c

/-- The partial measures that bound a split double `SUM`/`AVG`'s rounding:
`SUM(|x|)`, `COUNT(x)` and `MAX(|x|)`, under the measure's `FILTER`. The
shards compute them after all of `floatPartial`'s, so that the columns
`floatCombine` reads stay where they are. -/
def floatBoundParts (m : Measure) : List Measure :=
  if m.fn = .fsum ∨ m.fn = .avg then
    [{ m with fn := .fsum, arg := fabsExpr m.arg }, { m with fn := .count },
      { m with fn := .max, arg := fabsExpr m.arg }]
  else []

/-- The partial measures of a split with doubles: `floatPartial`'s, then
`floatBoundParts`'. -/
def floatParts (ms : List Measure) : List Measure :=
  ms.flatMap floatPartial ++ ms.flatMap floatBoundParts

theorem fabsExpr_eval_int {e : Expr} {row : Row} {c : Int} (h : e.eval row = .int c) :
    (fabsExpr e).eval row = .int (fabsCode c) := by
  by_cases hc : c < 0 <;>
    simp [fabsExpr, fabsCode, Expr.eval, h, hc, BinFn.apply, UnFn.apply, Value.isTrue]

theorem fabsExpr_eval_null {e : Expr} {row : Row} (h : e.eval row = .null) :
    (fabsExpr e).eval row = .null := by
  simp [fabsExpr, Expr.eval, h, BinFn.apply, Value.isTrue]

namespace FloatCode

/-- How far a `SUM` of `n` doubles split over `k` shards of at most `m`
values, added in two phases, may be from the sequential sum (#428), scaled and
rounded up: `(γ (m + k) + γ n) · ((As + n·2⁵²) / (1 − γ m) + k·2⁵²)`, where
`As` is the shards' rounded `SUM(|x|)`s added up, scaled. Proved as
`shardTol_le` in `float-bounds/FloatBounds/Shard.lean`, which defines it the
same way. -/
def shardTolScaled (n m k As : Nat) : Nat :=
  ceilDiv (((m + k) * (2 * tolK - n) + n * (2 * tolK - (m + k)))
      * ((As + n * tolK) * (2 * tolK - m) + k * tolK * (2 * tolK - 2 * m)))
    ((2 * tolK - (m + k)) * (2 * tolK - n) * (2 * tolK - 2 * m))

/-- The same for an `AVG` (`shardAvgTol_le`):
`(γ (m + k + 2) + γ (n + 2)) · ((As + n·2⁵²) / (1 − γ m) + k·2⁵²) / n`. -/
def shardAvgTolScaled (n m k As : Nat) : Nat :=
  ceilDiv (((m + k + 2) * (2 * tolK - (n + 2)) + (n + 2) * (2 * tolK - (m + k + 2)))
      * ((As + n * tolK) * (2 * tolK - m) + k * tolK * (2 * tolK - 2 * m)))
    ((2 * tolK - (m + k + 2)) * (2 * tolK - (n + 2)) * (2 * tolK - 2 * m) * n)

-- Values `tests/test_partition.py` checks `sverify.partition`'s tolerances against.
#guard shardTolScaled 1 1 1 (2 ^ 1074) == 67413492557336866498252040001792083644064068193411786531149605887081928532333886566701038482448840821900724330384915087144207634933861773577164331784294401633577121524395968318874061263280622488211236594736130271757351694344563999121533190951991288203883650243640759293072526056456325657897929556720248422404
#guard shardTolScaled 0 0 0 0 == 0 && shardTolScaled 1000 300 4 (3 * 2 ^ 1080) == 5626060434865814519377634568766342819539498336233903602149647411948472027538064859444302092589296235927817399957868020457369097473388832809740992849461669965051209421312108807948812976879003456552646490394455402784343550113726544845934856238575391015941000106817583154524955705780959472494085466161306660841885962
#guard shardAvgTolScaled 1 1 1 (2 ^ 1074) == 157298149300452721759926585582868137649289714382442711829028535830801688179297746064987341784686588694594554020274915259614718763013975228832063467876356333860872815878791493048999295455246832822541941495387249176775796037410021292909345537243087575131230673626119989627886476299927251434926118482253965721620

end FloatCode

/-- The sum of the codes `L`'s shards, each rounded once, then rounded once
more: what `floatCombine` computes from the partial sums (D25). -/
def twoPhaseSum (L : List (List Int)) : Int :=
  floatSumCR (L.map fun l => Value.int (floatSumCR (l.map .int)))

/-- A shard's `SUM(|x|)`, rounded once. -/
def absSum (l : List Int) : Int := floatSumCR (l.map fun c => .int (fabsCode c))

/-- The shards' `SUM(|x|)`s, scaled, added up exactly. -/
def absTotal (L : List (List Int)) : Nat :=
  (L.map fun l => (FloatCode.scaled (absSum l)).toNat).sum

namespace FloatCode

/-- How far a split double `SUM` may be from the whole one (D25), scaled:
`As / 2⁵⁰`, with `As` the shards' `SUM(|x|)`s added up, scaled. Each of
the three roundings (per shard, of the partials, of the whole) is within
`2⁻⁵³` of what it rounds, relatively (`twoPhaseSum_near`). -/
def shardTolCR (As : Nat) : Nat := As / 2 ^ 50

/-- The same for an `AVG` of `n` values, whose partial sum is divided natively:
`As / (n · 2⁴⁷) + 1` (`twoPhaseAvg_near`). -/
def shardAvgTolCR (n As : Nat) : Nat := As / (n * 2 ^ 47) + 1

end FloatCode

/-! #### The proofs, on integers

`T` is the exact `Σ |x|` (`absExact`), scaled. Every rounding is within
`2⁻⁵³` of its argument relatively (`FloatCode.ofExact_rel`), so the
partials' exact sum is within `T / 2⁵³` of the whole's, and the two final
roundings add `|S| / 2⁵³` each. `As` is within `T / 2⁵³` of `T`. -/

/-- `Σ |x|` of the codes, scaled. -/
def absExact (cs : List Int) : Nat := (cs.map fun c => (FloatCode.scaled c).natAbs).sum

theorem absExact_append (a b : List Int) : absExact (a ++ b) = absExact a + absExact b := by
  simp [absExact, List.sum_append]

theorem absExact_flatten : ∀ L : List (List Int), absExact L.flatten = (L.map absExact).sum
  | [] => rfl
  | l :: L => by simp [absExact_append, absExact_flatten L]

theorem absExact_perm {a b : List Int} (h : a.Perm b) : absExact a = absExact b := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [absExact, List.map_cons, List.sum_cons] at ih ⊢; omega
  | swap x y l => simp only [absExact, List.map_cons, List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem absExact_le {cs : List Int} {Bs : Nat} (h : ∀ c ∈ cs, (FloatCode.scaled c).natAbs ≤ Bs) :
    absExact cs ≤ cs.length * Bs := by
  induction cs with
  | nil => simp [absExact]
  | cons c cs ih =>
    have := h c (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [absExact, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    rw [Nat.succ_mul]; omega

theorem exactSum_append (a b : List Value) : exactSum (a ++ b) = exactSum a + exactSum b := by
  induction a with
  | nil => simp [exactSum]
  | cons v a ih => cases v <;> simp [exactSum, ih] <;> omega

theorem exactSum_natAbs_le (cs : List Int) : (exactSum (cs.map .int)).natAbs ≤ absExact cs := by
  induction cs with
  | nil => simp [exactSum, absExact]
  | cons c cs ih =>
    simp only [absExact, List.map_cons, List.sum_cons, exactSum, FloatCode.exact] at ih ⊢
    omega

theorem isFin_of_scaled_le {c : Int} (h : (FloatCode.scaled c).natAbs ≤ FloatCode.maxMag) :
    FloatCode.IsFin c := by
  have := FloatCode.posInf_eq; have := FloatCode.negInf_eq
  unfold FloatCode.scaled at h; unfold FloatCode.IsFin
  split at h <;> omega

set_option exponentiation.threshold 2100 in
/-- Codes of scaled magnitude at most `2²⁰⁹⁶` add up to their exact sum,
rounded once. -/
theorem floatSumCR_of_le {cs : List Int} (h : ∀ c ∈ cs, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096) :
    floatSumCR (cs.map .int) = FloatCode.ofExact (exactSum (cs.map .int)) := by
  have hm : 2 ^ 2096 ≤ FloatCode.maxMag := FloatCode.pow_le_maxMag (by omega)
  simp only [floatSumCR, nonFinite_of_fin fun c hc => isFin_of_scaled_le (by
    have := h c hc; omega), Option.getD_none]

theorem scaled_fabsCode (c : Int) : FloatCode.scaled (fabsCode c) = (FloatCode.scaled c).natAbs := by
  by_cases hc : c < 0 <;> simp only [fabsCode, FloatCode.neg, hc, ↓reduceIte] <;>
    unfold FloatCode.scaled <;> split <;> omega

set_option exponentiation.threshold 2100 in
/-- The shards' exact sums against their rounded ones: within `T / 2⁵³`. -/
theorem partials_near {L : List (List Int)} (h : ∀ c ∈ L.flatten, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096)
    (hT : absExact L.flatten ≤ 2 ^ 2096) :
    2 ^ 53 * (exactSum (L.map fun l => Value.int (floatSumCR (l.map .int)))
      - exactSum (L.flatten.map .int)).natAbs ≤ absExact L.flatten ∧
    ∀ l ∈ L, FloatCode.IsFin (floatSumCR (l.map .int)) := by
  induction L with
  | nil => simp [exactSum]
  | cons l L ih =>
    simp only [List.flatten_cons, List.mem_append] at h hT
    rw [absExact_append] at hT
    have hl : ∀ c ∈ l, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096 := fun c hc => h c (.inl hc)
    obtain ⟨ih1, ih2⟩ := ih (fun c hc => h c (.inr hc)) (by omega)
    have hS := exactSum_natAbs_le l
    obtain ⟨hfin, hrel⟩ := FloatCode.ofExact_rel (S := exactSum (l.map .int)) (by omega)
    rw [← floatSumCR_of_le hl] at hfin hrel
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, exactSum, List.flatten_cons, List.map_append, exactSum_append,
        absExact_append, FloatCode.exact]
      omega
    · intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact hfin
      · exact ih2 l' hl'

set_option exponentiation.threshold 2100 in
/-- `As` against `T`: `(2⁵³ − 1) T ≤ 2⁵³ As`. -/
theorem absTotal_ge {L : List (List Int)} (h : ∀ c ∈ L.flatten, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096)
    (hT : absExact L.flatten ≤ 2 ^ 2096) :
    (2 ^ 53 - 1) * absExact L.flatten ≤ 2 ^ 53 * absTotal L := by
  induction L with
  | nil => simp [absExact, absTotal]
  | cons l L ih =>
    simp only [List.flatten_cons, List.mem_append] at h hT
    rw [absExact_append] at hT
    have ih' := ih (fun c hc => h c (.inr hc)) (by omega)
    have hl : ∀ c ∈ l, (FloatCode.scaled (fabsCode c)).natAbs ≤ 2 ^ 2096 := fun c hc => by
      rw [scaled_fabsCode]; have := h c (.inl hc); omega
    have hmap : (l.map fun c => Value.int (fabsCode c)) = (l.map fabsCode).map .int := by simp
    have he : exactSum ((l.map fabsCode).map .int) = absExact l := by
      clear hl hmap ih' ih h hT
      induction l with
      | nil => simp [exactSum, absExact]
      | cons c l ihl =>
        simp only [List.map_cons, exactSum, FloatCode.exact, scaled_fabsCode, absExact,
          List.sum_cons] at ihl ⊢
        omega
    have hle : absExact l ≤ 2 ^ 2097 := by omega
    obtain ⟨-, hrel⟩ := FloatCode.ofExact_rel (S := (absExact l : Int))
      (by rw [Int.natAbs_natCast]; exact hle)
    have hA : absSum l = FloatCode.ofExact (absExact l) := by
      unfold absSum; rw [hmap, floatSumCR_of_le (by simpa using hl), he]
    simp only [absTotal, List.map_cons, List.sum_cons] at ih' ⊢
    rw [List.flatten_cons, absExact_append]
    rw [hA]
    omega

set_option exponentiation.threshold 2100 in
/-- **A split double `SUM` (D25)**: `k` shards of the codes `ws`, each rounded
once, then rounded once more, are within `shardTolCR As` of `ws` rounded
once. -/
theorem twoPhaseSum_near {L : List (List Int)} {ws : List Int} {Bs : Nat}
    (hp : ws.Perm L.flatten) (hB : ∀ c ∈ ws, (FloatCode.scaled c).natAbs ≤ Bs)
    (hov : ws.length * Bs ≤ 2 ^ 2096) :
    (FloatCode.scaled (twoPhaseSum L) - FloatCode.scaled (floatSumCR (ws.map .int))).natAbs
      ≤ FloatCode.shardTolCR (absTotal L) := by
  have hT : absExact ws ≤ 2 ^ 2096 := Nat.le_trans (absExact_le hB) hov
  have hBs : ∀ c ∈ ws, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096 := fun c hc => by
    have := hB c hc
    have : Bs ≤ 2 ^ 2096 := by
      cases ws with
      | nil => simp at hc
      | cons => simp only [List.length_cons] at hov; rw [Nat.succ_mul] at hov; omega
    omega
  have hBL : ∀ c ∈ L.flatten, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096 :=
    fun c hc => hBs c (hp.mem_iff.mpr hc)
  have hTL : absExact L.flatten = absExact ws := (absExact_perm hp).symm
  obtain ⟨hnear, hfin⟩ := partials_near hBL (by omega)
  have hAs := absTotal_ge hBL (by omega)
  have hSeq : exactSum (L.flatten.map .int) = exactSum (ws.map .int) :=
    (exactSum_perm (hp.map _)).symm
  have hS := exactSum_natAbs_le ws
  -- The partials are finite: their list rounds its exact sum `P` once.
  have hR : twoPhaseSum L =
      FloatCode.ofExact (exactSum (L.map fun l => Value.int (floatSumCR (l.map .int)))) := by
    have : L.map (fun l => Value.int (floatSumCR (l.map .int))) =
        (L.map fun l => floatSumCR (l.map .int)).map .int := by simp
    rw [twoPhaseSum, this]
    show (nonFinite _).getD _ = _
    rw [nonFinite_of_fin (by
      intro c hc; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc; exact hfin l hl)]
    rfl
  rw [hR, floatSumCR_of_le hBs]
  rw [hSeq, hTL] at hnear
  rw [hTL] at hAs
  generalize exactSum (L.map fun l => Value.int (floatSumCR (l.map .int))) = P at hnear ⊢
  generalize exactSum (ws.map .int) = S at hnear hS ⊢
  obtain ⟨-, h1⟩ := FloatCode.ofExact_rel (S := P) (by omega)
  obtain ⟨-, h2⟩ := FloatCode.ofExact_rel (S := S) (by omega)
  unfold FloatCode.shardTolCR
  omega

set_option exponentiation.threshold 2100 in
/-- The scaled value of an integer's exact code. -/
theorem scaled_exactCode (n : Nat) : FloatCode.scaled (FloatCode.exactCode n) = n * 2 ^ 1074 := by
  simp only [FloatCode.exactCode, FloatFormat.exactCode, fp64_scale, Int.natAbs_natCast]
  unfold FloatCode.scaled
  by_cases h0 : n = 0
  · subst h0; simp
  · simp only [show (n : Int) ≠ 0 by omega, show ¬ (n : Int) < 0 by omega, ↓reduceIte]
    split <;> omega

/-- `2⁵¹ |Q n K − R K| ≤ 2 |R| K + 2⁵⁰ n K` without the scale `K`. -/
theorem cancel_scale {Q Rs K : Int} {n : Nat} (hK : 0 < K)
    (h : 2 ^ 51 * (Q * (n * K) - Rs * K).natAbs ≤
      2 * Rs.natAbs * K.natAbs + 2 ^ 50 * ((n : Int) * K).natAbs) :
    2 ^ 51 * (Q * n - Rs).natAbs ≤ 2 * Rs.natAbs + 2 ^ 50 * n := by
  have e1 : Q * (n * K) - Rs * K = (Q * n - Rs) * K := by
    rw [Int.sub_mul, Int.mul_assoc]
  rw [e1, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at h
  have e2 : 2 * Rs.natAbs * K.natAbs + 2 ^ 50 * (n * K.natAbs) =
      (2 * Rs.natAbs + 2 ^ 50 * n) * K.natAbs := by
    rw [Nat.add_mul, Nat.mul_assoc (2 ^ 50)]
  rw [e2, ← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (by omega)

/-- The arithmetic of `twoPhaseAvg_near`: the native quotient `Q`, the
reference's mean `C`, the rounded partials' sum `Rs`, their exact sum `P`, the
exact sum `S` and `Σ |x| = T`, all scaled, against `As`. -/
theorem avg_arith {P S Rs Q C : Int} {n X T As : Nat}
    (hnear : 2 ^ 53 * (P - S).natAbs ≤ T) (hS : S.natAbs ≤ T)
    (h1 : 2 ^ 53 * (Rs - P).natAbs ≤ P.natAbs)
    (hdiv : 2 ^ 51 * (Q * n - Rs).natAbs ≤ 2 * Rs.natAbs + 2 ^ 50 * n)
    (hC : 2 ^ 53 * ((n : Int) * C - S).natAbs ≤ S.natAbs + 2 ^ 52 * n)
    (hX : n * X = (Q * n - n * C).natAbs)
    (hAs : (2 ^ 53 - 1) * T ≤ 2 ^ 53 * As) (hn0 : 0 < n) :
    X ≤ As / (n * 2 ^ 47) + 1 := by
  have hP : P.natAbs ≤ 2 * T := by omega
  have hRs : Rs.natAbs ≤ 4 * T := by omega
  have hT2 : T ≤ 2 * As := by omega
  have hmain : 2 ^ 53 * (n * X) ≤ 40 * T + 2 ^ 53 * n := by omega
  have hZ : n * (X - 1) = n * X - n := Nat.mul_sub_one n X
  have hZ2 : (X - 1) * (n * 2 ^ 47) = n * (X - 1) * 2 ^ 47 := by
    rw [Nat.mul_comm n (X - 1), Nat.mul_assoc]
  have hlt : (X - 1) * (n * 2 ^ 47) ≤ As := by
    rw [hZ2, hZ]; omega
  have hD : 0 < n * 2 ^ 47 := Nat.mul_pos hn0 (Nat.two_pow_pos 47)
  have := (Nat.le_div_iff_mul_le hD).2 hlt
  omega

set_option exponentiation.threshold 2100 in
/-- **A split double `AVG` (D25)**: the split sum divided natively by the
count is within `shardAvgTolCR n As` of the mean of `ws` rounded once. -/
theorem twoPhaseAvg_near {L : List (List Int)} {ws : List Int} {Bs : Nat} (hne : ws ≠ [])
    (hp : ws.Perm L.flatten) (hB : ∀ c ∈ ws, (FloatCode.scaled c).natAbs ≤ Bs)
    (h32 : ws.length ≤ 2 ^ 32) (hov : ws.length * Bs ≤ 2 ^ 2096) :
    (FloatCode.scaled (FloatCode.lift₂ (· / ·) (twoPhaseSum L) (FloatCode.ofInt ws.length))
        - FloatCode.scaled (floatAvgCR (ws.map .int))).natAbs
      ≤ FloatCode.shardAvgTolCR ws.length (absTotal L) := by
  have hn0 : 0 < ws.length := List.length_pos_iff.mpr hne
  have hT : absExact ws ≤ 2 ^ 2096 := Nat.le_trans (absExact_le hB) hov
  have hBs : ∀ c ∈ ws, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096 := fun c hc => by
    have := hB c hc
    have : Bs ≤ 2 ^ 2096 := Nat.le_trans (Nat.le_mul_of_pos_left _ hn0) hov
    omega
  have hBL : ∀ c ∈ L.flatten, (FloatCode.scaled c).natAbs ≤ 2 ^ 2096 :=
    fun c hc => hBs c (hp.mem_iff.mpr hc)
  have hTL : absExact L.flatten = absExact ws := (absExact_perm hp).symm
  obtain ⟨hnear, hfin⟩ := partials_near hBL (by omega)
  have hAs := absTotal_ge hBL (by omega)
  have hSeq : exactSum (L.flatten.map .int) = exactSum (ws.map .int) :=
    (exactSum_perm (hp.map _)).symm
  have hS := exactSum_natAbs_le ws
  have hR : twoPhaseSum L =
      FloatCode.ofExact (exactSum (L.map fun l => Value.int (floatSumCR (l.map .int)))) := by
    have : L.map (fun l => Value.int (floatSumCR (l.map .int))) =
        (L.map fun l => floatSumCR (l.map .int)).map .int := by simp
    rw [twoPhaseSum, this]
    show (nonFinite _).getD _ = _
    rw [nonFinite_of_fin (by
      intro c hc; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc; exact hfin l hl)]
    rfl
  have hC : floatAvgCR (ws.map .int) = FloatCode.ofExactDiv (exactSum (ws.map .int)) ws.length := by
    have hm : 2 ^ 2096 ≤ FloatCode.maxMag := FloatCode.pow_le_maxMag (by omega)
    simp only [floatAvgCR, nonFinite_of_fin fun c hc => isFin_of_scaled_le (by
      have := hBs c hc; omega), Option.getD_none, List.length_map]
  -- The count as a double is exact.
  have hcount : FloatCode.ofInt ws.length = FloatCode.exactCode ws.length :=
    FloatCode.ofInt_exact (by
      rw [Int.natAbs_natCast]; exact Nat.le_trans h32 (Nat.pow_le_pow_right (by omega) (by omega)))
  have hsc : FloatCode.scaled (FloatCode.exactCode ws.length) = ws.length * 2 ^ 1074 :=
    scaled_exactCode ws.length
  have hfinN : FloatCode.IsFin (FloatCode.exactCode ws.length) := isFin_of_scaled_le (by
    rw [hsc]
    have : ws.length * 2 ^ 1074 ≤ 2 ^ 32 * 2 ^ 1074 := Nat.mul_le_mul_right _ h32
    rw [← Nat.pow_add] at this
    have := FloatCode.pow_le_maxMag (k := 32 + 1074) (by omega)
    omega)
  rw [hR, hC, hcount]
  rw [hSeq, hTL] at hnear
  rw [hTL] at hAs
  generalize exactSum (L.map fun l => Value.int (floatSumCR (l.map .int))) = P at hnear ⊢
  generalize exactSum (ws.map .int) = S at hnear hS ⊢
  obtain ⟨hRfin, h1⟩ := FloatCode.ofExact_rel (S := P) (by omega)
  generalize hRd : FloatCode.ofExact P = R at hRfin h1
  -- The native division, within `core_div`'s error.
  have hKabs : ((2 : Int) ^ 1074).natAbs = 2 ^ 1074 := by rw [Int.natAbs_pow]; rfl
  have hKpos : (0 : Int) < 2 ^ 1074 := Int.pow_pos (by decide)
  have hRle : (FloatCode.scaled R).natAbs ≤ 2 ^ 2097 := by omega
  obtain ⟨-, hdiv⟩ := FloatCode.div_scaled_err hRfin hfinN
    (by rw [hsc]; exact Int.mul_ne_zero (by omega) (Int.ne_of_gt hKpos)) (by
      rw [hsc, Int.natAbs_mul, Int.natAbs_natCast, hKabs]
      calc (FloatCode.scaled R).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ hRle
        _ ≤ 2 ^ 2097 * (ws.length * 2 ^ 1074) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hn0))
  rw [hsc, ← hKabs] at hdiv
  generalize FloatCode.scaled (FloatCode.lift₂ (· / ·) R (FloatCode.exactCode ws.length)) = Q at hdiv ⊢
  generalize FloatCode.scaled R = Rs at h1 hdiv hRle
  have hdiv' := cancel_scale hKpos hdiv
  -- The reference's mean, within half an ulp.
  have hfinC := FloatCode.ofExactDiv_fin (v := S) hn0 (by
    have := Nat.le_mul_of_pos_left (2 ^ 2097) hn0; omega)
  have hw := FloatCode.ofExactDiv_within hn0 hfinC
  have hu := FloatCode.ulpDiv_le S hn0
  generalize FloatCode.scaled (FloatCode.ofExactDiv S ws.length) = C at hw ⊢
  generalize FloatCode.ulpDiv S ws.length = U at hw hu
  generalize hn : ws.length = n at *
  have hCrel : 2 ^ 53 * ((n : Int) * C - S).natAbs ≤ S.natAbs + 2 ^ 52 * n := by
    by_cases hsmall : S.natAbs ≤ n * 2 ^ 52
    · have : n * 2 ^ 52 * U ≤ n * 2 ^ 52 * 1 := by rw [Nat.mul_one]; omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      have hnU : n * U ≤ n := by
        calc n * U ≤ n * 1 := Nat.mul_le_mul_left _ this
          _ = n := Nat.mul_one _
      omega
    · have e : n * 2 ^ 52 * U = 2 ^ 52 * (n * U) := by
        rw [Nat.mul_comm n, Nat.mul_assoc]
      omega
  -- Multiply out `n · |Q − C|`.
  have hY : (n : Int) * (Q - C) = Q * n - n * C := by
    rw [Int.mul_sub, Int.mul_comm]
  have hX : n * (Q - C).natAbs = (Q * n - n * C).natAbs := by
    rw [← hY, Int.natAbs_mul, Int.natAbs_natCast]
  generalize hXd : (Q - C).natAbs = X
  rw [hXd] at hX
  exact avg_arith hnear hS h1 hdiv' hCrel hX hAs hn0

/-- Two results agree up to `τ` (scaled): two doubles within `τ`, anything
else equal. -/
def Value.Near (τ : Nat) : Value → Value → Prop
  | .int a, .int b => (FloatCode.scaled a - FloatCode.scaled b).natAbs ≤ τ
  | a, b => a = b

theorem length_le_flatten : ∀ {L : List (List Int)}, (∀ l ∈ L, l ≠ []) → L.length ≤ L.flatten.length
  | [], _ => by simp
  | l :: L, h => by
    have := length_le_flatten (L := L) fun l' hl' => h l' (by simp [hl'])
    have hl : 0 < l.length := List.length_pos_iff.mpr (h l (by simp))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem flatten_filter_ne_nil {α : Type} : ∀ L : List (List α),
    (L.filter fun l => !l.isEmpty).flatten = L.flatten
  | [] => rfl
  | [] :: L => by simp [flatten_filter_ne_nil L]
  | (a :: l) :: L => by simp [flatten_filter_ne_nil L]

theorem fsum_apply_ints : ∀ l : List Int,
    AggFn.fsum.apply (l.map .int) = if l.isEmpty then .null else .int (floatSumCR (l.map .int))
  | [] => rfl
  | _ :: _ => rfl

theorem partialSums_eq : ∀ Ls : List (List Int),
    (Ls.map fun l => AggFn.fsum.apply (l.map .int)).filter (· != .null) =
      (Ls.filter fun l => !l.isEmpty).map fun l => .int (floatSumCR (l.map .int))
  | [] => rfl
  | l :: Ls => by
    rw [List.map_cons, List.filter_cons, fsum_apply_ints, partialSums_eq Ls]
    cases l <;> simp

/-- **A split double `SUM`**: shards with the codes `Ls`, against the same
codes `ws` in one pass. `fsum` of the shards' non-NULL partial sums is
`floatCombine`'s; it is within `shardTolCR` of the whole's (D25). -/
theorem fsum_twoPhase_near {Ls : List (List Int)} {ws : List Int} {Bs : Nat}
    (hp : ws.Perm Ls.flatten) (hB : ∀ c ∈ ws, (FloatCode.scaled c).natAbs ≤ Bs)
    (hov : ws.length * Bs ≤ 2 ^ 2096) :
    let L := Ls.filter fun l => !l.isEmpty
    Value.Near (FloatCode.shardTolCR (absTotal L))
      (AggFn.fsum.apply ((Ls.map fun l => AggFn.fsum.apply (l.map .int)).filter (· != .null)))
      (AggFn.fsum.apply (ws.map .int)) := by
  intro L
  have hpL : ws.Perm L.flatten := by rw [flatten_filter_ne_nil]; exact hp
  have hne : ∀ l ∈ L, l ≠ [] := fun l hl => by
    have := (List.mem_filter.mp hl).2; simpa using this
  rw [partialSums_eq]
  by_cases hL0 : L = []
  · have hpL' : ws.Perm [] := by rw [hL0] at hpL; exact hpL
    have : ws = [] := List.Perm.eq_nil hpL'
    subst this
    show Value.Near _ (AggFn.fsum.apply (L.map _)) _
    rw [hL0]
    exact rfl
  · have hkn : L.length ≤ ws.length := Nat.le_trans (length_le_flatten hne) (Nat.le_of_eq hpL.length_eq.symm)
    have hws : ws ≠ [] := by
      have := List.length_pos_iff.mpr hL0
      exact List.length_pos_iff.mp (by omega)
    have h := twoPhaseSum_near hpL hB hov
    obtain ⟨l, L', hLc⟩ := List.exists_cons_of_ne_nil hL0
    obtain ⟨c, ws', hwc⟩ := List.exists_cons_of_ne_nil hws
    show Value.Near _ (AggFn.fsum.apply (L.map fun l => .int (floatSumCR (l.map .int)))) _
    rw [hLc] at h ⊢
    rw [hwc] at h ⊢
    simpa [AggFn.apply, Value.Near, twoPhaseSum] using h

theorem intsOf_flatten (L : List (List Value)) : intsOf L.flatten = (L.map intsOf).flatten :=
  List.filterMap_flatten ..

theorem sum_apply_ne_nil {vs : List Value} (h : vs ≠ []) : AggFn.sum.apply vs = .int (intSum vs) := by
  cases vs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem Measure.inputs_eq_vals {m : Measure} (hd : m.distinct = false) (rows : Relation) :
    m.inputs rows = m.vals rows := by simp [Measure.inputs_eq, hd]

theorem Measure.inputs_flatten_perm {m : Measure} (hd : m.distinct = false) {ss : List Relation}
    {ws : Relation} (hp : ws.Perm ss.flatten) : (m.inputs ws).Perm (ss.map m.inputs).flatten := by
  have hss : ss.map m.inputs = ss.map m.vals :=
    List.map_congr_left fun s _ => Measure.inputs_eq_vals hd s
  rw [hss, Measure.inputs_eq_vals hd, ← Measure.vals_flatten]; exact m.vals_perm hp

/-- The codes a group's measure adds, on its shards and on the whole, with
what the bound needs of them. -/
structure SplitCodes (m : Measure) (ss : List Relation) (ws : Relation) (mx Bs : Nat) : Prop where
  perm : ws.Perm ss.flatten
  codes : ∀ v ∈ m.inputs ws, ∃ c, v = .int c ∧ (FloatCode.scaled c).natAbs ≤ Bs
  shard : ∀ s ∈ ss, (m.inputs s).length ≤ mx
  le : mx ≤ (m.inputs ws).length
  small : (m.inputs ws).length ≤ 2 ^ 32
  far : (m.inputs ws).length * (Bs + 2 * FloatCode.tolK) ≤ 2 ^ 2096

theorem SplitCodes.ints {m : Measure} {ss : List Relation} {ws : Relation} {mx Bs : Nat}
    (hd : m.distinct = false) (h : SplitCodes m ss ws mx Bs) :
    (∀ v ∈ m.inputs ws, ∃ c, v = .int c) ∧ ∀ s ∈ ss, ∀ v ∈ m.inputs s, ∃ c, v = .int c := by
  have hint : ∀ v ∈ m.inputs ws, ∃ c, v = .int c := fun v hv =>
    (h.codes v hv).imp fun _ h => h.1
  refine ⟨hint, fun s hs v hv => hint v ?_⟩
  exact (Measure.inputs_flatten_perm hd h.perm).mem_iff.mpr
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨s, hs, rfl⟩, hv⟩)

/-- The shards' codes, those with values. -/
def SplitCodes.parts (m : Measure) (ss : List Relation) : List (List Int) :=
  (ss.map fun s => intsOf (m.inputs s)).filter fun l => !l.isEmpty

theorem SplitCodes.apply {m : Measure} {ss : List Relation} {ws : Relation} {mx Bs : Nat}
    (hd : m.distinct = false) (h : SplitCodes m ss ws mx Bs) :
    let ws' := intsOf (m.inputs ws)
    let Ls := ss.map fun s => intsOf (m.inputs s)
    m.inputs ws = ws'.map .int ∧ (∀ s ∈ ss, m.inputs s = (intsOf (m.inputs s)).map .int) ∧
      ws'.Perm Ls.flatten ∧ (∀ l ∈ Ls, l.length ≤ mx) ∧ mx ≤ ws'.length ∧ ws'.length ≤ 2 ^ 32 ∧
      (∀ c ∈ ws', (FloatCode.scaled c).natAbs ≤ Bs) ∧
      ws'.length * (Bs + 2 * FloatCode.tolK) ≤ 2 ^ 2096 := by
  intro ws' Ls
  obtain ⟨hint, hints⟩ := h.ints hd
  have hws : m.inputs ws = ws'.map .int := ints_map_intsOf hint
  have hlen : ws'.length = (m.inputs ws).length := by rw [hws, List.length_map]
  refine ⟨hws, fun s hs => ints_map_intsOf (hints s hs), ?_, ?_, hlen ▸ h.le, hlen ▸ h.small,
    ?_, hlen ▸ h.far⟩
  · have h1 : (intsOf (m.inputs ws)).Perm (intsOf (ss.map m.inputs).flatten) :=
      (Measure.inputs_flatten_perm hd h.perm).filterMap _
    rw [intsOf_flatten, List.map_map] at h1; exact h1
  · intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact Nat.le_trans (List.length_filterMap_le _ _) (h.shard s hs)
  · intro c hc
    obtain ⟨c', hc', hb⟩ := h.codes _ (mem_intsOf.mp hc)
    cases hc'; exact hb

/-- **A split double `SUM`, measured** (#428): the measure's `SUM` on each
shard (`floatPartial`), their non-NULL ones added up (`floatCombine`), is within
`shardTolCR As` of its value on the whole group, where `As` adds up the
shards' `SUM(|x|)`, scaled (`floatBoundParts`, `absPart_eval`). -/
theorem floatSplit_sum {m : Measure} (hf : m.fn = .fsum) (hd : m.distinct = false)
    {ss : List Relation} {ws : Relation} {mx Bs : Nat} (h : SplitCodes m ss ws mx Bs) :
    let L := SplitCodes.parts m ss
    Value.Near (FloatCode.shardTolCR (absTotal L))
      (AggFn.fsum.apply ((ss.map m.eval).filter (· != .null))) (m.eval ws) := by
  intro L
  have hsort : m.fn.sorts = false := by rw [hf]; rfl
  have hev : ∀ rows, m.eval rows = AggFn.fsum.apply (m.inputs rows) := fun rows => by
    rw [Measure.eval_eq hsort, hf]
  obtain ⟨hws, hss, hp, hm, hmn, h32, hB, hov⟩ := h.apply hd
  have hmap : ss.map m.eval = (ss.map fun s => intsOf (m.inputs s)).map
      fun l => AggFn.fsum.apply (l.map .int) := by
    simp only [List.map_map]
    exact List.map_congr_left fun s hs => by simp [hev, ← hss s hs]
  rw [hmap, hev ws, hws]
  exact fsum_twoPhase_near hp hB (by unfold FloatCode.tolK at hov; rw [Nat.mul_add] at hov; omega)

/-- **A split double `AVG`, measured**: the measure's `SUM`s and `COUNT`s on
each shard (`floatPartial`), divided as `floatCombine` divides them, are within
`shardAvgTolCR n As` of its value on the whole group, `n` the shards'
`COUNT(x)`s added up. -/
theorem floatSplit_avg {m : Measure} (hf : m.fn = .avg) (hd : m.distinct = false)
    {ss : List Relation} {ws : Relation} {mx Bs : Nat} (h : SplitCodes m ss ws mx Bs) :
    let L := SplitCodes.parts m ss
    Value.Near (FloatCode.shardAvgTolCR (m.inputs ws).length (absTotal L))
      (BinFn.apply .fdiv
        (AggFn.fsum.apply ((ss.map ({ m with fn := .fsum } : Measure).eval).filter (· != .null)))
        (UnFn.apply .itof
          (AggFn.sum.apply ((ss.map ({ m with fn := .count } : Measure).eval).filter (· != .null)))))
      (m.eval ws) := by
  intro L
  obtain ⟨hws, hss, hp, hm, hmn, h32, hB, hov⟩ := h.apply hd
  have hsum : ∀ rows, ({ m with fn := .fsum } : Measure).eval rows =
      AggFn.fsum.apply (m.inputs rows) := fun rows => by rw [Measure.eval_eq rfl]; rfl
  have hcount : ∀ rows, ({ m with fn := .count } : Measure).eval rows =
      .int (m.inputs rows).length := fun rows => by rw [Measure.eval_eq rfl]; rfl
  have hev : m.eval ws = AggFn.avg.apply ((intsOf (m.inputs ws)).map .int) := by
    rw [Measure.eval_eq (by rw [hf]; rfl), hf]
    exact congrArg _ hws
  have hmap : ss.map ({ m with fn := .fsum } : Measure).eval =
      (ss.map fun s => intsOf (m.inputs s)).map fun l => AggFn.fsum.apply (l.map .int) := by
    rw [List.map_map]
    exact List.map_congr_left fun s hs => by
      show _ = AggFn.fsum.apply ((intsOf (m.inputs s)).map .int)
      rw [hsum, ← hss s hs]
  have hcounts : (ss.map ({ m with fn := .count } : Measure).eval).filter (· != .null) =
      (ss.map fun s => intsOf (m.inputs s)).map fun l => .int l.length := by
    rw [List.filter_eq_self.mpr (fun v hv => by
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv; rw [hcount]; rfl), List.map_map]
    exact List.map_congr_left fun s hs => by
      show _ = Value.int (intsOf (m.inputs s)).length
      rw [hcount, (congrArg List.length (hss s hs)).trans (List.length_map ..)]
  have hlen : (m.inputs ws).length = (intsOf (m.inputs ws)).length :=
    (congrArg List.length hws).trans (List.length_map ..)
  rw [hmap, partialSums_eq, hcounts, hev, hlen]
  have hn : ∀ Ls : List (List Int), intSum (Ls.map fun l => Value.int l.length) = Ls.flatten.length := by
    intro Ls; induction Ls with
    | nil => rfl
    | cons l Ls ih => simp only [List.map_cons, intSum, ih, List.flatten_cons, List.length_append]; omega
  have hne : ∀ l ∈ L, l ≠ [] := fun l hl => by
    have := (List.mem_filter.mp hl).2; simpa using this
  have hpL : (intsOf (m.inputs ws)).Perm L.flatten := by
    have := flatten_filter_ne_nil (ss.map fun s => intsOf (m.inputs s))
    show (intsOf (m.inputs ws)).Perm (SplitCodes.parts m ss).flatten
    unfold SplitCodes.parts; rw [this]; exact hp
  show Value.Near _ (BinFn.apply .fdiv (AggFn.fsum.apply (L.map fun l => .int (floatSumCR (l.map .int))))
    (UnFn.apply .itof (AggFn.sum.apply ((ss.map fun s => intsOf (m.inputs s)).map
      fun l => .int l.length)))) _
  have hNs := hn (ss.map fun s => intsOf (m.inputs s))
  rw [← hp.length_eq] at hNs
  generalize intsOf (m.inputs ws) = W at *
  by_cases hw0 : W = []
  · -- no values: every result is NULL
    subst hw0
    have hL : L = [] := by
      cases hL : L with
      | nil => rfl
      | cons l L' =>
        rw [hL] at hpL
        have := List.Perm.nil_eq hpL
        simp at this; exact absurd this.1 (hne l (by rw [hL]; simp))
    rw [hL]
    generalize UnFn.apply .itof _ = y
    cases y <;> rfl
  · have hkn : L.length ≤ W.length :=
      Nat.le_trans (length_le_flatten hne) (Nat.le_of_eq hpL.length_eq.symm)
    have hL0 : L ≠ [] := by
      intro hL; rw [hL] at hpL; exact hw0 (List.Perm.eq_nil hpL)
    have h := twoPhaseAvg_near (L := L) hw0 hpL hB h32
      (by unfold FloatCode.tolK at hov; rw [Nat.mul_add] at hov; omega)
    have hLs : (ss.map fun s => intsOf (m.inputs s)).map (fun l => Value.int l.length) ≠ [] := by
      intro h
      rw [List.map_eq_nil_iff] at h
      rw [h] at hp; exact hw0 (List.Perm.eq_nil hp)
    have hsumapp : AggFn.sum.apply ((ss.map fun s => intsOf (m.inputs s)).map
        fun l => Value.int l.length) = .int W.length := by
      rw [sum_apply_ne_nil hLs, hNs]
    rw [hsumapp]
    obtain ⟨l, L', hLc⟩ := List.exists_cons_of_ne_nil hL0
    obtain ⟨c, W', hwc⟩ := List.exists_cons_of_ne_nil hw0
    rw [hLc] at h ⊢
    rw [hwc] at h ⊢
    simpa [AggFn.apply, BinFn.apply, UnFn.apply, Value.Near, twoPhaseSum] using h

/-- `|v|` of a double's code; other values unchanged. -/
def absValue : Value → Value
  | .int c => .int (fabsCode c)
  | v => v

theorem filter_map_absValue : ∀ vs : List Value,
    (vs.map absValue).filter (· != .null) = (vs.filter (· != .null)).map absValue
  | [] => rfl
  | v :: vs => by
    rw [List.map_cons, List.filter_cons, List.filter_cons, filter_map_absValue vs]
    cases v <;> simp [absValue]

/-- What a shard's `SUM(|x|)` partial (`floatBoundParts`) holds: its codes'
`absSum`, `NULL` without values. -/
theorem absPart_eval {m : Measure} (hd : m.distinct = false) {s : Relation}
    (hi : ∀ v ∈ m.inputs s, ∃ c, v = .int c) :
    ({ m with fn := .fsum, arg := fabsExpr m.arg } : Measure).eval s =
      AggFn.fsum.apply ((intsOf (m.inputs s)).map fun c => .int (fabsCode c)) := by
  have hrow : ∀ row ∈ m.kept s, (fabsExpr m.arg).eval row = absValue (m.arg.eval row) := by
    intro row hrow
    cases hv : m.arg.eval row with
    | null => exact fabsExpr_eval_null hv
    | int c => exact fabsExpr_eval_int hv
    | _ =>
      exfalso
      have hmem : m.arg.eval row ∈ m.inputs s := by
        rw [Measure.inputs_eq_vals hd]
        simp only [Measure.vals, List.mem_filter, List.mem_map, bne_iff_ne, ne_eq]
        exact ⟨⟨row, hrow, rfl⟩, by rw [hv]; simp⟩
      obtain ⟨c, hc⟩ := hi _ hmem
      rw [hv] at hc; cases hc
  have hin : ({ m with fn := .fsum, arg := fabsExpr m.arg } : Measure).inputs s =
      (m.inputs s).map absValue := by
    rw [Measure.inputs_eq_vals hd,
      Measure.inputs_eq_vals (m := { m with fn := .fsum, arg := fabsExpr m.arg }) hd]
    show ((m.kept s).map (fabsExpr m.arg).eval).filter (· != .null) =
      (((m.kept s).map m.arg.eval).filter (· != .null)).map absValue
    rw [List.map_congr_left hrow, ← filter_map_absValue, List.map_map]
    rfl
  rw [Measure.eval_eq rfl]
  show AggFn.fsum.apply _ = _
  rw [hin]
  have h2 := congrArg (List.map absValue) (ints_map_intsOf hi)
  rw [h2, List.map_map]
  rfl

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
results, which reads them from the table `P`. Integer `AVG`s whose argument
`I` vouches for split as algebraic aggregates (`algCombine`). With `floats`,
`SUM` and `AVG` of doubles split too (`floatCombine`, unproved). -/
def Rel.splitAgg (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog)
    (I : IntArgs) (P : String)
    (floats : Bool) : Rel → Option (Rel × Rel)
  | .aggregate r gs ms =>
      if r.linear S K T cat && ms.all (·.twoPhase (r.keyCols S K T cat)) then
        some (.aggregate r gs ms,
          .aggregate (.read P) (keyFields gs.length) (combineMeasures gs.length ms))
      else if r.linear S K T cat && ms.all (·.algebraic I r (r.keyCols S K T cat)) then
        some (.aggregate r gs (algParts ms), algCombine gs.length ms (.read P))
      else if floats && r.linear S K T cat && ms.all (·.floatSplittable (r.keyCols S K T cat)) then
        some (.aggregate r gs (floatParts ms), floatCombine gs.length ms (.read P))
      else none
  | .filter r c => (r.splitAgg S K T cat I P floats).map fun pq => (pq.1, .filter pq.2 c)
  | .project r es => (r.splitAgg S K T cat I P floats).map fun pq => (pq.1, .project pq.2 es)
  | .emit r m => (r.splitAgg S K T cat I P floats).map fun pq => (pq.1, .emit pq.2 m)
  | .orderBy r keys => (r.splitAgg S K T cat I P floats).map fun pq => (pq.1, .orderBy pq.2 keys)
  | _ => none

/-- Sharded evaluation of `r`: the plan each shard runs, and the plan that
combines their results (read from the table `P`). A linear plan's results
are just concatenated. -/
def Rel.shardSplit (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog)
    (I : IntArgs) (P : String)
    (floats : Bool) (r : Rel) : Option (Rel × Rel) :=
  if r.linear S K T cat then some (r, .read P) else r.splitAgg S K T cat I P floats

theorem Rel.splitAgg_sound {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) {I : IntArgs}
    (hI : I.Sound cat) (hne : cs ≠ []) {C : Catalog} :
    ∀ {r p q : Rel}, r.WF cat → r.splitAgg S K T cat I P false = some (p, q) →
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
      · rename_i hc
        simp only [Bool.and_eq_true, List.all_eq_true] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [algCombine_eval]
        simp only [eval, hC]
        exact eval_algebraic hs hT hI hne hw.1 hc.1 hc.2
      · split at h
        · rename_i hc; simp at hc
        · simp at h
  | .filter r c, p, q, hw, h, hC | .project r c, p, q, hw, h, hC | .emit r c, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K T cat I P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := splitAgg_sound hs hT hI hne (r := r) hw.1 hr hC
      simp only [eval]
      first | exact ih.filter _ | exact ih.map _
  | .orderBy r keys, p, q, hw, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S K T cat I P false with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((splitAgg_sound hs hT hI hne (r := r) hw.1 hr hC).trans
        (List.mergeSort_perm _ _).symm)
  | .read _, _, _, _, h, _ | .values _ _, _, _, _, h, _ | .cross _ _, _, _, _, h, _
  | .join _ _ _ _, _, _, _, h, _ | .fetch _ _ _, _, _, _, h, _ | .unionAll _ _, _, _, _, h, _
  | .window _ _ _ _, _, _, _, h, _ | .semi _ _ _ _, _, _, _, h, _ | .distinct _, _, _, _, h, _ => by
    simp [splitAgg] at h

/-- **Sharded evaluation is sound**: run `p` on every shard, put the results
in table `P`, and `q` gives the plan's result. -/
theorem Rel.shardSplit_sound {S : String → Bool} {K : String → Option (List Nat)} {T : WindowKeys} {P : String}
    {cat : Catalog} {cs : List Catalog} (hs : Sharding S K cat cs) (hT : T.Sound cat) {I : IntArgs}
    (hI : I.Sound cat) (hne : cs ≠ []) {C : Catalog}
    {r p q : Rel} (hw : r.WF cat) (h : r.shardSplit S K T cat I P false = some (p, q))
    (hC : (C P).rows = cs.flatMap p.eval) : (r.eval cat).Perm (q.eval C) := by
  unfold shardSplit at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval, hC]
    exact eval_sharded hs hT hw hl
  · exact splitAgg_sound hs hT hI hne hw h hC

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
  simp only [inI64, between, Bool.and_eq_true, FloatCode.minI64, FloatCode.maxI64] at ht ⊢
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

