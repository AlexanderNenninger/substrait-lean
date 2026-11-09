import SubstraitLean.IncrementalAgg

/-!
# Delta rules for `MIN`, `MAX` and exact `AVG` (#248, stage 2)

## `MIN` and `MAX`

`MIN` and `MAX` are not linear: when a batch deletes a group's extreme,
the next one is among the group's other values, which the state does not
hold. They are linear under inserts, though: the `MIN` of a group's old
values and the values a batch inserts is the `MIN` of the two `MIN`s
(`minMax_combine`). So a view keeps, per group, the state of `LinearAgg`
(the number of rows, and each measure's number of values and sum) and each
`MIN` or `MAX` measure's extreme, and a batch

* adds the state of what it inserts to the groups it only inserts into
  (`merge`), and
* recomputes the groups it deletes from on the new input, like touched-group
  recompute (`TouchedGroups.touched_sound`), but only those.

* `done_merge`: the merged state of two bags finishes to the aggregate's row
  of their union, for `COUNT`, `SUM`, `MIN` and `MAX`.
* `extreme_maintained`: after a batch, the old rows of the groups it does
  not touch, the aggregate of the new input's rows in the groups it deletes
  from, and the merged state of the others are an aggregate the reference
  allows (one key of each class of keys, D31). This is what
  `sverify._linear` computes.

## Exact `AVG`

`AVG` of exact types is a `SUM` and a `COUNT` and a final division (#245):

* a `DECIMAL` `AVG` is, in the model, an aggregate with the `SUM` and the
  `COUNT`, then a projection that divides them (`decimalAvgs`). Maintaining
  the aggregate maintains the view: `map_maintained` carries a maintained
  aggregate through any projection of its rows that keeps the keys.
* an integer `AVG` with an integer result (`AggFn.iavg`) is `SUM / COUNT`
  truncated (`Measure.final_eval`), when its values are integers:
  `finish_iavg` finishes it from the state of `LinearAgg`.
-/

namespace Substrait
namespace ExtremeAgg

open LinearAgg
open Retention (applyBatch filter_foldl_erase)

/-- A measure the state keeps: `COUNT`, integer `SUM`, `MIN` or `MAX`,
without `DISTINCT`. -/
def Kept (m : Measure) : Prop :=
  (m.fn = .count ∨ m.fn = .sum ∨ m.fn = .min ∨ m.fn = .max) ∧ m.distinct = false

def extreme (m : Measure) : Bool := m.fn == .min || m.fn == .max

/-- A measure's state in a group: its number of values (`n`), their sum
(`s`), and their extreme (`e`, the measure's value: NULL without values). -/
structure St where
  n : Int
  s : Int
  e : Value

/-- Measure `m`'s state in group `k` of the bag `rows`. -/
def st (gs : List Expr) (m : Measure) (rows : Relation) (k : Row) : St :=
  ⟨valuesIn gs m k (ZSet.lift rows), sumIn gs m k (ZSet.lift rows), m.eval (groupRows gs rows k)⟩

/-- The state of two bags together: counts and sums add up, and the
extreme is the extreme of the two extremes, NULLs skipped. -/
def merge (m : Measure) (a b : St) : St :=
  ⟨a.n + b.n, a.s + b.s, m.fn.apply ([a.e, b.e].filter (· != .null))⟩

/-- The measure's value from its state; `sc` is a `SUM`'s scale (`finish`). -/
def done (m : Measure) (sc : Option Nat) (x : St) : Value :=
  if extreme m then x.e else finish m sc x.n x.s

theorem lift_append (a b : Relation) : ZSet.lift (a ++ b) = ZSet.lift a ++ ZSet.lift b :=
  List.map_append

theorem groupRows_append (gs : List Expr) (a b : Relation) (k : Row) :
    groupRows gs (a ++ b) k = groupRows gs a k ++ groupRows gs b k := by
  simp [groupRows, List.filter_append]

/-- **`MIN` and `MAX` under inserts**: the extreme of two bags is the
extreme of their extremes. -/
theorem eval_append_minMax {m : Measure} (hm : m.fn = .min ∨ m.fn = .max) (hd : m.distinct = false)
    (g₁ g₂ : Relation) :
    m.fn.apply ([m.eval g₁, m.eval g₂].filter (· != .null)) = m.eval (g₁ ++ g₂) := by
  have hs : m.fn.sorts = false := by rcases hm with h | h <;> simp [h, AggFn.sorts]
  have hf : m.fn = if m.fn == .max then .max else .min := by rcases hm with h | h <;> simp [h]
  rw [Measure.eval_eq hs, Measure.eval_eq hs, Measure.eval_eq hs]
  have hnn : ∀ vs ∈ [m.inputs g₁, m.inputs g₂], ∀ v ∈ vs, v ≠ .null := by
    intro vs hvs v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvs
    rcases hvs with rfl | rfl <;> exact (Measure.mem_inputs hv).1
  have h := minMax_combine hf hnn
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at h
  rw [h, inputs_eq hd, inputs_eq hd, inputs_eq hd, List.filter_append, List.map_append]

/-- **The merged state finishes to the aggregate's row** of the two bags
together, for `COUNT`, `SUM`, `MIN` and `MAX`. -/
theorem done_merge {gs : List Expr} {m : Measure} (hm : Kept m) {sc : Option Nat} {a b : Relation}
    (hsc : ArgScale sc m (a ++ b)) (k : Row) :
    done m sc (merge m (st gs m a k) (st gs m b k)) = m.eval (groupRows gs (a ++ b) k) := by
  rcases hm with ⟨hf, hd⟩
  rcases hf with h | h | h | h
  · have he : extreme m = false := by simp [extreme, h]
    simp only [done, he, merge, st, Bool.false_eq_true, ↓reduceIte]
    rw [← valuesIn_append, ← sumIn_append, ← lift_append]
    exact finish_eval ⟨Or.inl h, hd⟩ hsc k
  · have he : extreme m = false := by simp [extreme, h]
    simp only [done, he, merge, st, Bool.false_eq_true, ↓reduceIte]
    rw [← valuesIn_append, ← sumIn_append, ← lift_append]
    exact finish_eval ⟨Or.inr h, hd⟩ hsc k
  · have he : extreme m = true := by simp [extreme, h]
    simp only [done, he, merge, st, ↓reduceIte]
    rw [groupRows_append]
    exact eval_append_minMax (Or.inl h) hd _ _
  · have he : extreme m = true := by simp [extreme, h]
    simp only [done, he, merge, st, ↓reduceIte]
    rw [groupRows_append]
    exact eval_append_minMax (Or.inr h) hd _ _

variable {gs : List Expr} {ms : List Measure}

/-- **Maintaining `COUNT`, `SUM`, `MIN` and `MAX` per group.** A batch
deletes `dels` and inserts `ins`, touching only classes of keys in `K`, and
deletes only from classes in `D`. Then an output the reference allows after
the batch is

* the rows of an old output the reference allows of the groups outside `K`,
* the aggregate of the new input's rows in the groups in `K` and `D`
  (recomputed), and
* for one key of each class in `K` but not `D` that has rows (`ks`), the
  merged state of the old rows and the inserted ones. -/
theorem extreme_maintained (hg : gs ≠ []) (hms : ∀ m ∈ ms, Kept m) {sc : Measure → Option Nat}
    {rows dels ins : Relation} (hsc : ∀ m ∈ ms, ArgScale (sc m) m (rows ++ ins))
    {K D : Row → Bool} (hKc : RespectsCanon K) (hDc : RespectsCanon D)
    (hT : TouchedGroups.Touches gs K dels ins)
    (hD : ∀ r ∈ dels, D (groupKey gs r) = true) {old : Relation} (hold : aggAllowed gs ms rows old)
    {ks : List Row} (hks : ks.Pairwise fun a b => a.canon ≠ b.canon)
    (hpos : ∀ k ∈ ks, K k = true ∧ D k = false ∧
      0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k (ZSet.lift ins))
    (hcov : ∀ k, K k = true → D k = false →
      0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k (ZSet.lift ins) → ∃ k' ∈ ks, k'.canon = k.canon) :
    aggAllowed gs ms (applyBatch rows dels ins)
      (old.filter (fun o => !K (o.take gs.length)) ++
        (aggregateEval gs ms ((applyBatch rows dels ins).filter
          fun r => K (groupKey gs r) && D (groupKey gs r)) ++
        ks.map fun k => k ++ ms.map fun m =>
          done m (sc m) (merge m (st gs m rows k) (st gs m ins k)))) := by
  have hge : gs.isEmpty = false := by simpa using hg
  let new := applyBatch rows dels ins
  have hnK : RespectsCanon fun k => !K k := fun k k' he => by simp only [hKc k k' he]
  refine aggAllowed_append hg hnK ?_ ?_
  · -- The untouched groups: their rows are as they were.
    have hu := TouchedGroups.filter_untouched (q := fun r => K (groupKey gs r)) (rows := rows) hT
    rw [hu]
    exact aggAllowed_filter_key hg hnK hold
  · -- The touched groups, split by `D`.
    have e : ∀ q : Row → Bool, (new.filter fun r => !!K (groupKey gs r)).filter q =
        new.filter fun r => K (groupKey gs r) && q r := fun q => by
      rw [List.filter_filter]; exact List.filter_congr fun r _ => by simp [Bool.and_comm]
    refine aggAllowed_append hg hDc ?_ ?_
    · rw [e]
      exact aggregateEval_allowed gs ms _
    · -- The groups the batch only inserts into: old rows and inserted ones.
      let q : Row → Bool := fun r => K (groupKey gs r) && !D (groupKey gs r)
      have hx : new.filter (fun r => K (groupKey gs r) && !D (groupKey gs r)) =
          (rows ++ ins).filter q := by
        simp only [new, applyBatch, List.filter_append]
        congr 1
        exact filter_foldl_erase dels rows fun d hd => by simp [q, hD d hd]
      rw [e, hx]
      have hq : ∀ k, K k = true → D k = false → ∀ r, (groupKey gs r).canon = k.canon → q r = true :=
        fun k hK hD' r he => by simp [q, hKc _ _ he, hDc _ _ he, hK, hD']
      unfold aggAllowed
      simp only [hge, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ks, ⟨hks, fun k hk => ?_, fun x hx' => ?_⟩, forall₂_map_self ks fun k hk => ⟨_, rfl, ?_⟩⟩
      · obtain ⟨hK, hD', hp⟩ := hpos k hk
        rw [← rowsIn_append, ← lift_append] at hp
        obtain ⟨r, hr, he⟩ := rowsIn_lift_pos.mp hp
        exact ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, hq k hK hD' r he⟩), he.symm⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx'
        obtain ⟨hr, hqr⟩ := List.mem_filter.mp hr
        simp only [q, Bool.and_eq_true, Bool.not_eq_true'] at hqr
        refine hcov _ hqr.1 hqr.2 ?_
        rw [← rowsIn_append, ← lift_append]
        exact rowsIn_lift_pos.mpr ⟨r, hr, rfl⟩
      · obtain ⟨hK, hD', -⟩ := hpos k hk
        have hg' : groupRows gs ((rows ++ ins).filter q) k = groupRows gs (rows ++ ins) k := by
          simp only [groupRows, List.filter_filter]
          exact List.filter_congr fun r _ => by
            by_cases he : ((groupKey gs r).canon == k.canon) = true
            · simp [he, hq k hK hD' r (by simpa using he)]
            · simp [he]
        rw [hg']
        rw [show (ms.map fun m => done m (sc m) (merge m (st gs m rows k) (st gs m ins k))) =
          ms.map (·.eval (groupRows gs (rows ++ ins) k)) from
          List.map_congr_left fun m hm => done_merge (hms m hm) (hsc m hm) k]
        exact forall₂_map_self ms fun m _ => Measure.eval_allowed m _

/-! ## Exact `AVG` -/

/-- **A projection of a maintained aggregate is maintained.** If the
aggregate after a batch is the old rows outside `K` and some rows `L`, then
any map of its rows that keeps the keys (a projection that finishes an
`AVG` from its `SUM` and `COUNT`, as `decimalAvgs` does) is the old mapped
rows outside `K` and `L` mapped. -/
theorem map_maintained {new old L : Relation} {K : Row → Bool} {f : Row → Row}
    (hf : ∀ o ∈ old, (f o).take gs.length = o.take gs.length)
    (h : new.Perm (old.filter (fun o => !K (o.take gs.length)) ++ L)) :
    (new.map f).Perm ((old.map f).filter (fun o => !K (o.take gs.length)) ++ L.map f) := by
  refine (h.map f).trans (.of_eq ?_)
  rw [List.map_append, List.filter_map]
  congr 1
  refine congrArg _ (List.filter_congr fun o ho => ?_)
  simp [hf o ho]

/-- **Integer `AVG` from the state**: `SUM / COUNT` truncated, NULL without
values, when the values are integers. -/
def finishAvg (n s : Int) : Value := if n = 0 then .null else .int (s.tdiv n)

theorem finish_iavg {gs : List Expr} {m : Measure} (hm : m.fn = .iavg) (hd : m.distinct = false)
    {rows : Relation} (hint : ∀ row ∈ rows, (m.arg.eval row).intOrNull = true) (k : Row) :
    finishAvg (valuesIn gs m k (ZSet.lift rows)) (sumIn gs m k (ZSet.lift rows)) =
      m.eval (groupRows gs rows k) := by
  have hint' : ∀ row ∈ groupRows gs rows k, (m.arg.eval row).intOrNull = true :=
    fun row hr => hint row (List.mem_filter.mp hr).1
  rw [← Measure.final_eval hm hint']
  -- Integer values: a `SUM` of them is an integer (`ArgScale none`).
  have hsc : ArgScale none { m with fn := .sum } rows := fun _ row hr => by
    have := hint row hr
    simp only [scaleKind]
    cases h : m.arg.eval row <;> simp_all [Value.intOrNull, Value.hasKind]
  have hsum := finish_eval (gs := gs) (m := { m with fn := .sum }) ⟨Or.inr rfl, hd⟩ hsc k
  have hcnt := finish_eval (gs := gs) (m := { m with fn := .count }) ⟨Or.inl rfl, hd⟩
    (sc := none) (rows := rows) (fun h => by simp at h) k
  -- The state does not depend on the function.
  have hv : ∀ f : AggFn, valuesIn gs { m with fn := f } k (ZSet.lift rows) =
      valuesIn gs m k (ZSet.lift rows) := fun _ => rfl
  have hs : ∀ f : AggFn, sumIn gs { m with fn := f } k (ZSet.lift rows) =
      sumIn gs m k (ZSet.lift rows) := fun _ => rfl
  rw [← hsum, ← hcnt, hv, hs, hv, hs]
  simp only [finish, finishAvg, BinFn.apply]
  split <;> simp_all
