import Sverify.Core.Rel

/-!
# Aggregates whose value does not depend on the order of their rows

Which aggregates combine from parts (`AggFn.decomposable`) and which ignore
the order of their values (`AggFn.orderFree`, `Measure.orderFree`), with
`Measure.eval_perm`: such a measure gives the same value on any permutation
of its rows. `Rel.Allowed` (`SubstraitLean/Allowed.lean`) and sharded
evaluation (`SubstraitLean/Partition.lean`) both use them.
-/

namespace Substrait

/-! ## Values of decomposable aggregates -/

theorem intSum_append : ∀ (vs ws : List Value), intSum (vs ++ ws) = intSum vs + intSum ws
  | [], _ => by simp [intSum]
  | v :: vs, ws => by
    rw [List.cons_append, intSum_cons, intSum_cons, intSum_append vs ws]; omega

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
def AggFn.orderFree (f : AggFn) : Bool :=
  f.decomposable || f == .fsum || f == .avg ||
    match f with
    | .var _ _ | .cov _ | .corr => true
    | _ => false

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
      | cons w ws => simp only [apply, sumOf_perm h]
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
  · cases vs with
    | nil => rw [← h.nil_eq]
    | cons v vs =>
      cases ws with
      | nil => exact absurd h.eq_nil (by simp)
      | cons w ws =>
        cases f <;> simp_all [orderFree, decomposable, apply, floatSumCR_perm h,
          floatAvgCR_perm h, varOf_perm _ _ h, covOf_perm _ h, corrOf_perm h]

theorem AggFn.apply_sum_cons (v : Value) (vs : List Value) :
    AggFn.sum.apply (v :: vs) = sumOf (v :: vs) := rfl

/-- Partial sums, without the NULLs of empty parts, add up to the total, and
are decimals of a scale where all values are. -/
theorem sum_partials : ∀ L : List (List Value),
    intSum ((L.map AggFn.sum.apply).filter (· != .null)) = intSum L.flatten ∧
      (((L.map AggFn.sum.apply).filter (· != .null)) = [] ↔ L.flatten = []) ∧
      ∀ s, ((L.map AggFn.sum.apply).filter (· != .null)).all (Value.isDecOf s) =
        L.flatten.all (Value.isDecOf s)
  | [] => by simp [intSum]
  | [] :: L => by
    have := sum_partials L
    simpa [AggFn.apply] using this
  | (v :: vs) :: L => by
    obtain ⟨h₁, _, h₃⟩ := sum_partials L
    have hf : (((v :: vs) :: L).map AggFn.sum.apply).filter (· != .null) =
        sumOf (v :: vs) :: (L.map AggFn.sum.apply).filter (· != .null) := by
      simp [AggFn.apply_sum_cons]
    rw [hf, List.flatten_cons]
    refine ⟨?_, by simp, fun s => ?_⟩
    · rw [intSum_cons, sumOf_unscaled_eq, Option.getD_some, h₁, intSum_append]
    · rw [List.all_cons, h₃ s, List.all_append, isDecOf_sumOf (by simp) s]

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
    rw [List.map_cons, apply_sum_cons, ← List.map_cons (f := fun vs : List Value => Value.int vs.length)]
    rcases sumOf_cases ((l :: L').map fun vs : List Value => Value.int vs.length) with
      ⟨s, h1, _⟩ | ⟨_, e⟩
    · exfalso
      simp only [allDecOf, Bool.and_eq_true, List.all_map, List.all_cons] at h1
      simp [Function.comp_def, Value.isDecOf] at h1
    · rw [e, intSum_map_length]; rfl
  · obtain ⟨h₁, h₂, h₃⟩ := sum_partials L
    simp only [combine]
    by_cases hF : L.flatten = []
    · rw [h₂.mpr hF, hF]
    · obtain ⟨a, l, ha⟩ := List.exists_cons_of_ne_nil (mt h₂.mp hF)
      obtain ⟨b, l', hb⟩ := List.exists_cons_of_ne_nil hF
      rw [ha, hb, apply_sum_cons, apply_sum_cons, ← ha, ← hb]
      refine sumOf_eq_of h₁ fun s => ?_
      simp only [allDecOf, ha, hb, List.isEmpty_cons, Bool.not_false, Bool.true_and]
      rw [← ha, ← hb]; exact h₃ s
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

end Substrait
