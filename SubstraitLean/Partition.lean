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
  only broadcast tables (a copy on every shard). A join of two sharded
  tables is not: it needs co-partitioning on the join key.
* `twoPhase_correct`: `COUNT`, `SUM` of integers, `MIN` and `MAX` (without
  `DISTINCT`) aggregate in two phases. Every shard aggregates its rows by the
  grouping keys; the partial rows are then grouped again by the keys and
  combined (`COUNT` by `SUM`, the others by themselves). Both phases skip
  NULLs, so a group a shard lacks, or whose values are all NULL, changes
  nothing.
* `Rel.shardSplit_sound`: `Rel.shardSplit` turns a plan into the plan each
  shard runs and the plan that combines their outputs, with filters,
  projections and sorts above the aggregate moved to the combining plan.

Refused, because the result depends on how the rows are split:

* `SUM` and `AVG` of doubles: floating-point addition is not associative,
  so a different split rounds differently (`floatSum` adds in list order).
* `COUNT(DISTINCT …)` and friends: a value in two shards counts once in the
  whole and twice in the parts.
* `DISTINCT`, windows and `FETCH`: they look at rows of other shards.

In this model integer sums are exact. Engines compute them in 64 bits, so
a partial sum may leave 64 bits when the total does not (a shard of large
positive values next to one of large negative values). The SQL each dialect
writes raises instead of wrapping (`Dialect.int_sum`), so two-phase
evaluation either gives the right answer or fails; `intSum_partial_le`
shows that it cannot fail spuriously when all values have the same sign.
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

/-! ## Shards -/

/-- `cs` splits the tables `S` of `cat` into shards: every shard has the same
schemas, the rows of a sharded table are spread over the shards, and every
other table is copied to each shard (broadcast). -/
structure Sharding (S : String → Bool) (cat : Catalog) (cs : List Catalog) : Prop where
  arity : ∀ c ∈ cs, ∀ t, (c t).arity = (cat t).arity
  split : ∀ t, S t = true → (cat t).rows.Perm (cs.flatMap fun c => (c t).rows)
  bcast : ∀ t, S t = false → ∀ c ∈ cs, (c t).rows = (cat t).rows

/-- Reads no sharded table. -/
def Rel.const (S : String → Bool) (r : Rel) : Bool := r.tables.all (!S ·)

/-- Linear in the sharded tables: the result on a union of shards is the union
of the results. -/
def Rel.linear (S : String → Bool) : Rel → Bool
  | .read t => S t
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => r.linear S
  | .unionAll a b => a.linear S && b.linear S
  | .cross a b | .join a b .inner _ =>
      (a.linear S && b.const S) || (a.const S && b.linear S)
  | .join a b .left _ | .semi a b _ _ => a.linear S && b.const S
  -- A literal table would be repeated on every shard.
  | .values _ _ | .fetch _ _ _ | .window _ _ _ _ | .distinct _ | .aggregate _ _ _ => false

theorem Sharding.const_eval {S : String → Bool} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) {r : Rel} (h : r.const S = true) : ∀ c ∈ cs, r.eval c = r.eval cat :=
  fun c hc => Rel.eval_congr (hs.arity c hc) fun t ht => by
    simp only [Rel.const, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact hs.bcast t (h t ht) c hc

theorem Sharding.cross {S : String → Bool} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) {a b : Rel}
    (ha : a.linear S = true → (a.eval cat).Perm (cs.flatMap a.eval))
    (hb : b.linear S = true → (b.eval cat).Perm (cs.flatMap b.eval))
    (h : (a.linear S && b.const S || a.const S && b.linear S) = true) :
    (crossRows (a.eval cat) (b.eval cat)).Perm
      (cs.flatMap fun c => crossRows (a.eval c) (b.eval c)) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hl, hc⟩ | ⟨hc, hl⟩
  · refine ((ha hl).flatMap_right _).trans ?_
    rw [List.flatMap_assoc]
    exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval hc c hm]; rfl)
  · refine (crossRows_perm_right (hb hl)).trans ((crossRows_flatMap_right _ _ _).trans ?_)
    exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval hc c hm])

/-- **Sharded evaluation**: a linear plan's result on the whole tables is the
union of its results on the shards. -/
theorem Rel.eval_sharded {S : String → Bool} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) : ∀ {r : Rel}, r.linear S = true → (r.eval cat).Perm (cs.flatMap r.eval)
  | .read t, h => hs.split t h
  | .values _ _, h | .fetch _ _ _, h | .window _ _ _ _, h | .distinct _, h | .aggregate _ _ _, h => by
      simp [linear] at h
  | .filter r _, h => by
      simp only [eval]
      exact ((eval_sharded hs (r := r) h).filter _).trans (.of_eq List.filter_flatMap)
  | .project r _, h | .emit r _, h => by
      simp only [eval]
      exact ((eval_sharded hs (r := r) h).map _).trans (.of_eq List.map_flatMap)
  | .orderBy r _, h => by
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((eval_sharded hs (r := r) h).trans
        (flatMap_perm_congr fun _ _ => (List.mergeSort_perm _ _).symm))
  | .unionAll a b, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      exact ((eval_sharded hs (r := a) h.1).append (eval_sharded hs (r := b) h.2)).trans
        (flatMap_append_perm _ _ _)
  | .cross a b, h => by
      simp only [eval]
      exact hs.cross (eval_sharded hs (r := a)) (eval_sharded hs (r := b)) h
  | .join a b .inner _, h => by
      simp only [eval]
      exact ((hs.cross (eval_sharded hs (r := a)) (eval_sharded hs (r := b)) h).filter _).trans
        (.of_eq List.filter_flatMap)
  | .join a b .left on, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      refine ((eval_sharded hs (r := a) h.1).flatMap_right _).trans ?_
      rw [List.flatMap_assoc]
      exact .of_eq (flatMap_congr fun c hm => by
        rw [hs.const_eval h.2 c hm, arity_congr (hs.arity c hm) b])
  | .semi a b _ _, h => by
      simp only [linear, Bool.and_eq_true] at h
      simp only [eval]
      refine ((eval_sharded hs (r := a) h.1).filter _).trans ?_
      rw [List.filter_flatMap]
      exact .of_eq (flatMap_congr fun c hm => by rw [hs.const_eval h.2 c hm])

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

theorem AggFn.apply_minMax_perm {f : AggFn} {max : Bool} (hf : f = (if max then .max else .min))
    {vs ws : List Value} (h : vs.Perm ws) : f.apply vs = f.apply ws := by
  by_cases hv : vs = []
  · subst hv; rw [← h.nil_eq]
  · have hw : ws ≠ [] := fun hw => hv (h.trans (by rw [hw])).eq_nil
    have hl := apply_minMax hf hv
    exact IsLeast.unique (minMaxLe_antisymm max)
      ⟨h.mem_iff.mp hl.1, fun w hw' => hl.2 w (h.mem_iff.mpr hw')⟩ (apply_minMax hf hw)

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

/-! ## Decomposable measures -/

def Measure.decomposable (m : Measure) : Bool := m.fn.decomposable && !m.distinct

theorem Measure.kept_perm (m : Measure) {xs ys : Relation} (h : xs.Perm ys) :
    (m.kept xs).Perm (m.kept ys) := by
  unfold kept; split
  · exact h
  · exact h.filter _

theorem Measure.kept_append (m : Measure) (xs ys : Relation) :
    m.kept (xs ++ ys) = m.kept xs ++ m.kept ys := by
  unfold kept; split <;> simp [List.filter_append]

theorem Measure.inputs_nil (m : Measure) : m.inputs [] = [] := by
  unfold inputs kept; cases m.filter <;> cases m.distinct <;> simp [dedup, dedupN]

theorem Measure.inputs_append {m : Measure} (hd : m.distinct = false) (xs ys : Relation) :
    m.inputs (xs ++ ys) = m.inputs xs ++ m.inputs ys := by
  simp only [inputs, hd, Bool.false_eq_true, ↓reduceIte, kept_append, List.map_append,
    List.filter_append]

theorem Measure.inputs_flatten {m : Measure} (hd : m.distinct = false) :
    ∀ ss : List Relation, m.inputs ss.flatten = (ss.map m.inputs).flatten
  | [] => inputs_nil m
  | s :: ss => by simp only [List.flatten_cons, inputs_append hd, inputs_flatten hd ss, List.map_cons]

theorem Measure.decomposable_iff {m : Measure} :
    m.decomposable = true ↔ m.fn.decomposable = true ∧ m.distinct = false := by
  simp [decomposable]

theorem Measure.eval_perm {m : Measure} (hm : m.decomposable = true) {xs ys : Relation}
    (h : xs.Perm ys) : m.eval xs = m.eval ys := by
  obtain ⟨hf, hd⟩ := decomposable_iff.mp hm
  simp only [eval]
  refine AggFn.apply_perm hf ?_
  simp only [inputs, hd, Bool.false_eq_true, ↓reduceIte]
  exact ((m.kept_perm h).map _).filter _

/-- The combining aggregate of a measure's results on the parts is its result
on the whole. -/
theorem Measure.combine_eval {m : Measure} (hm : m.decomposable = true) {ss : List Relation}
    (hne : ss ≠ []) :
    m.fn.combine.apply ((ss.map m.eval).filter (· != .null)) = m.eval ss.flatten := by
  obtain ⟨hf, hd⟩ := decomposable_iff.mp hm
  have : ss.map m.eval = (ss.map m.inputs).map m.fn.apply := by simp [eval, Function.comp_def]
  rw [this, AggFn.combine_apply hf (by simpa using hne) fun vs hvs v hv => ?_]
  · simp only [eval, inputs_flatten hd]
  · obtain ⟨s, _, rfl⟩ := List.mem_map.mp hvs
    exact (mem_inputs hv).1

/-! ## Aggregates do not depend on the order of their input -/

theorem dedup_perm_of_mem {α : Type} [DecidableEq α] {l l' : List α} (h : ∀ y, y ∈ l ↔ y ∈ l') :
    (dedup l).Perm (dedup l') :=
  (List.perm_ext_iff_of_nodup (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l))
    (List.nodup_iff_pairwise_ne.mpr (dedup_pairwise l'))).mpr fun y => by
      rw [mem_dedup, mem_dedup]; exact h y

theorem groupRows_perm {gs : List Expr} {xs ys : Relation} (h : xs.Perm ys) (k : Row) :
    (groupRows gs xs k).Perm (groupRows gs ys k) := h.filter _

theorem aggregateEval_perm {gs : List Expr} {ms : List Measure}
    (hms : ∀ m ∈ ms, m.decomposable = true) {xs ys : Relation} (h : xs.Perm ys) :
    (aggregateEval gs ms xs).Perm (aggregateEval gs ms ys) := by
  unfold aggregateEval
  split
  · exact .of_eq (by rw [List.map_congr_left fun m hm => Measure.eval_perm (hms m hm) h])
  · refine ((dedup_perm_of_mem fun k => ?_).map _).trans (.of_eq (List.map_congr_left fun k _ => ?_))
    · simp only [List.mem_map]
      exact ⟨fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.mp hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, h.mem_iff.mpr hx, e⟩⟩
    · congr 1
      exact List.map_congr_left fun m hm => Measure.eval_perm (hms m hm) (groupRows_perm h k)

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
    (hms : ∀ m ∈ ms, m.decomposable = true) {ss : List Relation} (hne : ss ≠ []) :
    (aggregateEval (keyFields gs.length) (combineMeasures gs.length ms)
      (ss.flatMap (aggregateEval gs ms))).Perm (aggregateEval gs ms ss.flatten) := by
  have hlen : ∀ k, (combineMeasures k ms).length = ms.length := fun k => by simp [combineMeasures]
  by_cases hg : gs = []
  · subst hg
    have hP : ss.flatMap (aggregateEval [] ms) = ss.map fun s => ms.map (·.eval s) := by
      induction ss with
      | nil => rfl
      | cons s ss ih => cases ss <;> simp_all [aggregateEval]
    simp only [aggregateEval, keyFields, List.length_nil, List.range_zero, List.map_nil,
      List.isEmpty_nil, ↓reduceIte, hP]
    refine .of_eq (congrArg (fun x => [x]) (List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_))
    simp only [List.length_map] at h₂
    simp only [List.getElem_map]
    rw [combineMeasures_eval h₂, ← Measure.combine_eval (hms _ (List.getElem_mem h₂)) hne]
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
      rw [combineMeasures_eval h₂, ← Measure.combine_eval (hms _ (List.getElem_mem h₂)) hne',
        List.map_map, List.map_map]
      congr 2
      refine List.map_congr_left fun s _ => ?_
      simp only [Function.comp_apply, List.getD_eq_getElem?_getD, ← hkl,
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_map, List.getElem?_eq_getElem h₂, Option.map_some, Option.getD_some]

/-! ## Plans -/

theorem flatMap_eq_flatten_map {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = (l.map f).flatten := List.flatMap_def

/-- **Two-phase aggregation over shards**: aggregate each shard, then combine. -/
theorem Rel.eval_twoPhase {S : String → Bool} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) (hne : cs ≠ []) {r : Rel} {gs : List Expr} {ms : List Measure}
    (hr : r.linear S = true) (hms : ∀ m ∈ ms, m.decomposable = true) :
    (aggregateEval gs ms (r.eval cat)).Perm
      (aggregateEval (keyFields gs.length) (combineMeasures gs.length ms)
        (cs.flatMap fun c => aggregateEval gs ms (r.eval c))) := by
  refine (aggregateEval_perm hms (eval_sharded hs hr)).trans ?_
  have := twoPhase_correct (gs := gs) hms (ss := cs.map r.eval) (by simpa using hne)
  rw [List.flatMap_map] at this
  rw [flatMap_eq_flatten_map]
  exact this.symm

/-- The aggregate below the filters, projections and sorts at the top of a plan,
split into the plan each shard runs and the plan that combines their
results, which reads them from the table `P`. -/
def Rel.splitAgg (S : String → Bool) (P : String) : Rel → Option (Rel × Rel)
  | .aggregate r gs ms =>
      if r.linear S && ms.all (·.decomposable) then
        some (.aggregate r gs ms,
          .aggregate (.read P) (keyFields gs.length) (combineMeasures gs.length ms))
      else none
  | .filter r c => (r.splitAgg S P).map fun pq => (pq.1, .filter pq.2 c)
  | .project r es => (r.splitAgg S P).map fun pq => (pq.1, .project pq.2 es)
  | .emit r m => (r.splitAgg S P).map fun pq => (pq.1, .emit pq.2 m)
  | .orderBy r keys => (r.splitAgg S P).map fun pq => (pq.1, .orderBy pq.2 keys)
  | _ => none

/-- Sharded evaluation of `r`: the plan each shard runs, and the plan that
combines their results (read from the table `P`). A linear plan's results
are just concatenated. -/
def Rel.shardSplit (S : String → Bool) (P : String) (r : Rel) : Option (Rel × Rel) :=
  if r.linear S then some (r, .read P) else r.splitAgg S P

theorem Rel.splitAgg_sound {S : String → Bool} {P : String} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) (hne : cs ≠ []) {C : Catalog} :
    ∀ {r p q : Rel}, r.splitAgg S P = some (p, q) → (C P).rows = cs.flatMap p.eval →
      (r.eval cat).Perm (q.eval C)
  | .aggregate r gs ms, p, q, h, hC => by
    simp only [splitAgg] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval, hC]
      exact eval_twoPhase hs hne hc.1 hc.2
    · simp at h
  | .filter r c, p, q, h, hC | .project r c, p, q, h, hC | .emit r c, p, q, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S P with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ih := splitAgg_sound hs hne (r := r) hr hC
      simp only [eval]
      first | exact ih.filter _ | exact ih.map _
  | .orderBy r keys, p, q, h, hC => by
    simp only [splitAgg] at h
    cases hr : r.splitAgg S P with
    | none => simp [hr] at h
    | some pq =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [eval]
      exact (List.mergeSort_perm _ _).trans ((splitAgg_sound hs hne (r := r) hr hC).trans
        (List.mergeSort_perm _ _).symm)
  | .read _, _, _, h, _ | .values _ _, _, _, h, _ | .cross _ _, _, _, h, _
  | .join _ _ _ _, _, _, h, _ | .fetch _ _ _, _, _, h, _ | .unionAll _ _, _, _, h, _
  | .window _ _ _ _, _, _, h, _ | .semi _ _ _ _, _, _, h, _ | .distinct _, _, _, h, _ => by
    simp [splitAgg] at h

/-- **Sharded evaluation is sound**: run `p` on every shard, put the results
in table `P`, and `q` gives the plan's result. -/
theorem Rel.shardSplit_sound {S : String → Bool} {P : String} {cat : Catalog} {cs : List Catalog}
    (hs : Sharding S cat cs) (hne : cs ≠ []) {C : Catalog} {r p q : Rel}
    (h : r.shardSplit S P = some (p, q)) (hC : (C P).rows = cs.flatMap p.eval) :
    (r.eval cat).Perm (q.eval C) := by
  unfold shardSplit at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [eval, hC]
    exact eval_sharded hs hl
  · exact splitAgg_sound hs hne h hC

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
