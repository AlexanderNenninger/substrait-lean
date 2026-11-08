import SubstraitLean.IncrementalAgg

/-!
# Delta rules for `SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` and `CORR` of doubles, exactly (#918 Part B)

Since D25 a `SUM` of doubles is the exact sum rounded once (`floatSumCR`),
and an `AVG` the exact sum over the count rounded once (`floatAvgCR`). Both
are functions of linear sums over the group's values: the count, the exact
sum (an integer in units of `2⁻¹⁰⁷⁴`, `exactSum`), and how many values are
NaN, `+∞` and `-∞` (`nonFinite`). So a view keeps these five integers per
group, adds a batch's to them, and rounds once when it finishes:
`floatState` is that state, and `floatState_sound` says it finishes to the
aggregate (`LinState.Sound`).

* `LinearAgg.aggregate_maintained` then maintains `SUM` and `AVG` of
  doubles beside `COUNT` and integer `SUM`.
* `no_drift`: after any sequence of batches whose weights add up to the
  current rows, a sound state finishes to the aggregate of those rows; for
  `SUM` of doubles `floatSumCR` of the group's values (`fsum_no_drift`,
  `Measure.eval_fsum`). It holds whatever the order or number of batches: a
  delete cancels its insert exactly, so nothing drifts.
* D30 makes `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` functions of exact
  moments, linear too: `varState_sound`, `covState_sound` and
  `corrState_sound` finish them as `varOf`, `covOf` and `corrOf` do.

The engine keeps the exact sum as a sum of mantissas per binary exponent
(`python/src/sverify/_linear.py`), which is this integer written in pieces.
-/

namespace Substrait
namespace LinearAgg

open FloatCode

set_option exponentiation.threshold 2200

/-- `1` for a double whose code satisfies `p`, else `0`. -/
def codeCount (p : Int → Bool) : Value → Int
  | .float c => if p c then 1 else 0
  | _ => 0

/-- A double's exact value in units of `2⁻¹⁰⁷⁴`, `0` for anything else. -/
def exactOf : Value → Int
  | .float c => exact c
  | _ => 0

/-- The predicates `nonFinite` reads: NaN, `+∞`, `-∞`. -/
def isNanCode (c : Int) : Bool := decide (nan ≤ c)
def isPosInfCode (c : Int) : Bool := decide (posInf ≤ c ∧ c < nan)
def isNegInfCode (c : Int) : Bool := decide (c ≤ negInf)

/-- `nonFinite` from the counts of NaN, `+∞` and `-∞` codes. -/
def nonFiniteOf (a b d : Int) : Option Int :=
  if 0 < a || (0 < b && 0 < d) then some nan
  else if 0 < b then some posInf
  else if 0 < d then some negInf
  else none

/-- The state of a `SUM` (`avg = false`) or `AVG` of doubles: the count,
the exact sum, and the counts of NaN, `+∞` and `-∞`. -/
def floatState (avg : Bool) : LinState where
  feats := [fun _ => 1, exactOf, codeCount isNanCode, codeCount isPosInfCode,
    codeCount isNegInfCode]
  fin l :=
    let n := l.getD 0 0
    if n = 0 then .null else
      .float ((nonFiniteOf (l.getD 2 0) (l.getD 3 0) (l.getD 4 0)).getD
        (if avg then ofExactDiv (l.getD 1 0) n.toNat else ofExact (l.getD 1 0)))

theorem exactSum_eq_sum : ∀ vs : List Value, exactSum vs = (vs.map exactOf).sum
  | [] => rfl
  | v :: vs => by cases v <;> simp [exactSum, exactOf, exactSum_eq_sum vs]

theorem codeCount_nonneg (p : Int → Bool) : ∀ vs : List Value, 0 ≤ (vs.map (codeCount p)).sum
  | [] => by simp
  | v :: vs => by
    have := codeCount_nonneg p vs
    cases v <;> simp only [codeCount, List.map_cons, List.sum_cons] <;> try split
    all_goals omega

/-- On a list (weights `1`), a code satisfies `p` iff its count is positive. -/
theorem anyCode_eq (p : Int → Bool) :
    ∀ vs : List Value, anyCode p vs = decide (0 < (vs.map (codeCount p)).sum)
  | [] => by simp [anyCode]
  | v :: vs => by
    have ih := anyCode_eq p vs
    have h0 := codeCount_nonneg p vs
    simp only [anyCode, List.any_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    cases v <;> simp only [codeCount, Bool.false_or] <;> try split
    all_goals simp_all <;> omega

theorem nonFinite_eq (vs : List Value) :
    nonFinite vs = nonFiniteOf ((vs.map (codeCount isNanCode)).sum)
      ((vs.map (codeCount isPosInfCode)).sum) ((vs.map (codeCount isNegInfCode)).sum) := by
  have h1 := anyCode_eq isNanCode vs
  have h2 := anyCode_eq isPosInfCode vs
  have h3 := anyCode_eq isNegInfCode vs
  unfold nonFinite nonFiniteOf
  rw [show (fun c : Int => decide (nan ≤ c)) = isNanCode from rfl,
    show (fun c : Int => decide (posInf ≤ c ∧ c < nan)) = isPosInfCode from rfl,
    show (fun c : Int => decide (c ≤ negInf)) = isNegInfCode from rfl, h1, h2, h3]
  simp only [decide_eq_true_eq]

/-- **The exact state finishes to `SUM` and `AVG` of doubles.** -/
theorem floatState_sound {m : Measure} (hf : m.fn = .fsum ∨ m.fn = .avg)
    (hd : m.distinct = false) : (floatState (m.fn == .avg)).Sound m := by
  refine ⟨hd, by rcases hf with h | h <;> simp [h, AggFn.sorts], fun vs _ => ?_⟩
  simp only [floatState, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    sum_one, ← exactSum_eq_sum, ← nonFinite_eq]
  cases vs with
  | nil => rcases hf with h | h <;> simp [h, AggFn.apply]
  | cons a l =>
    have hn : ((a :: l).length : Int) ≠ 0 := by simp; omega
    rcases hf with h | h <;> simp only [h, hn, ite_false, AggFn.apply] <;>
      simp [floatSumCR, floatAvgCR]

/-- `SUM` of doubles is `floatSumCR` of the group's values, NULL without any. -/
theorem Measure.eval_fsum {m : Measure} (hf : m.fn = .fsum) (rows : Relation) :
    m.eval rows = if m.inputs rows = [] then .null else .float (floatSumCR (m.inputs rows)) := by
  rw [Measure.eval_eq (by simp [hf, AggFn.sorts]), hf]
  cases m.inputs rows <;> rfl

/-- **No drift**, for any measure with a sound state: after any sequence of
batches `Δs` (inserts and deletes, in any order and number) whose weights add
up to the bag `rows`, the summed state finishes, for every group `k`, to the
aggregate of the group's current rows. -/
theorem no_drift {gs : List Expr} {m : Measure} {L : LinState} (hL : L.Sound m) {rows : Relation}
    (hg : L.Good m rows) (Δs : List ZSet)
    (hw : ∀ r, WSet.weight Δs.flatten r = (ZSet.lift rows).weight r) (k : Row) :
    L.fin (L.feats.map fun f => (Δs.map (featIn gs m f k)).sum) = m.eval (groupRows gs rows k) := by
  have hc : ∀ f, featIn gs m f k Δs.flatten = featIn gs m f k (ZSet.lift rows) :=
    fun _ => featIn_congr hw
  simp only [featIn_flatten, hc]
  exact fin_eval hL hg k

/-- **No drift for `SUM` and `AVG` of doubles**: the maintained value is the
aggregate of the current rows, for `SUM` `floatSumCR` of the group's values
(`Measure.eval_fsum`). -/
theorem fsum_no_drift {gs : List Expr} {m : Measure} (hf : m.fn = .fsum ∨ m.fn = .avg)
    (hd : m.distinct = false) {rows : Relation} (Δs : List ZSet)
    (hw : ∀ r, WSet.weight Δs.flatten r = (ZSet.lift rows).weight r) (k : Row) :
    (floatState (m.fn == .avg)).fin ((floatState (m.fn == .avg)).feats.map fun f =>
      (Δs.map (featIn gs m f k)).sum) = m.eval (groupRows gs rows k) :=
  no_drift (floatState_sound hf hd) (fun _ _ _ => trivial) Δs hw k

/-! ## `VAR`, `STDDEV`, `COVAR` and `CORR` of doubles

D30 makes each a function of exact moments: the count, `Σx`, `Σx²` (and for
pairs `Σy`, `Σxy`, `Σy²`) in units of `2⁻¹⁰⁷⁴` and `2⁻²¹⁴⁸`, and the counts of
NaN and infinities among the values. Each is linear, so a view keeps them per
group, and `varState`, `covState`, `corrState` finish them as `varOf`, `covOf`
and `corrOf` do. -/

/-- A double's `x²`, in units of `2⁻²¹⁴⁸`; `0` for anything else. -/
def sqOf : Value → Int
  | .float c => scaled c * scaled c
  | _ => 0

/-- The pair a `COVAR` or `CORR` adds up (`BinFn.pair`), if `v` is one. -/
def pairOf : Value → Option (Int × Int)
  | .list [.float a, .float b] => some (a, b)
  | _ => none

/-- `f` of the pair `v` is, `0` for anything else. -/
def pairFeat (f : Int × Int → Int) (v : Value) : Int := ((pairOf v).map f).getD 0

/-- The non-finite codes of the pair `v` that satisfy `p`. -/
def pairCount (p : Int → Bool) (v : Value) : Int :=
  pairFeat (fun q => (if p q.1 then 1 else 0) + (if p q.2 then 1 else 0)) v

theorem foldr_add_eq_sum (xs : List Int) : xs.foldr (· + ·) 0 = xs.sum := rfl

theorem scaledSum_floatsOf : ∀ vs : List Value, scaledSum (floatsOf vs) = (vs.map exactOf).sum
  | [] => rfl
  | v :: vs => by
    have ih := scaledSum_floatsOf vs
    cases v <;> simp_all [floatsOf, scaledSum, exactOf, foldr_add_eq_sum]

theorem sqSumOf_floatsOf : ∀ vs : List Value, sqSumOf (floatsOf vs) = (vs.map sqOf).sum
  | [] => rfl
  | v :: vs => by
    have ih := sqSumOf_floatsOf vs
    cases v <;> simp_all [floatsOf, sqSumOf, sqOf, foldr_add_eq_sum]

theorem floatsOf_length : ∀ {vs : List Value}, (∀ v ∈ vs, ∃ c, v = .float c) →
    (floatsOf vs).length = vs.length
  | [], _ => rfl
  | v :: vs, h => by
    obtain ⟨c, rfl⟩ := h v List.mem_cons_self
    have := floatsOf_length fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp_all [floatsOf]

theorem pairsOf_eq (vs : List Value) : pairsOf vs = vs.filterMap pairOf := by
  unfold pairsOf
  congr 1

/-- A sum over the pairs is the sum of its feature over the values. -/
theorem pairs_sum (f : Int × Int → Int) : ∀ vs : List Value,
    ((pairsOf vs).map f).sum = (vs.map (pairFeat f)).sum
  | [] => rfl
  | v :: vs => by
    have ih := pairs_sum f vs
    rw [pairsOf_eq] at ih ⊢
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons, pairFeat]
    cases pairOf v <;> simp [ih]

theorem pairs_length : ∀ vs : List Value,
    ((pairsOf vs).length : Int) = (vs.map (pairFeat fun _ => 1)).sum
  | [] => rfl
  | v :: vs => by
    have ih := pairs_length vs
    rw [pairsOf_eq] at ih ⊢
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons, pairFeat]
    cases pairOf v <;> simp [ih] <;> omega

theorem pairCodes_count (p : Int → Bool) : ∀ ps : List (Int × Int),
    ((pairCodes ps).map (codeCount p)).sum =
      (ps.map fun q => (if p q.1 then 1 else 0) + (if p q.2 then 1 else 0)).sum
  | [] => rfl
  | q :: ps => by
    have := pairCodes_count p ps
    simp only [pairCodes, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, codeCount] at this ⊢
    rw [this]; omega

theorem nonFinite_pairs (vs : List Value) :
    nonFinite (pairCodes (pairsOf vs)) = nonFiniteOf ((vs.map (pairCount isNanCode)).sum)
      ((vs.map (pairCount isPosInfCode)).sum) ((vs.map (pairCount isNegInfCode)).sum) := by
  rw [nonFinite_eq]
  simp only [pairCodes_count, pairs_sum]
  rfl

/-- The state of `VAR_*` (`sqrt = false`) or `STDDEV_*`: the count, `Σx`,
`Σx²`, and the counts of NaN, `+∞` and `-∞`. -/
def varState (sample sqrt : Bool) : LinState where
  feats := [fun _ => 1, exactOf, sqOf, codeCount isNanCode, codeCount isPosInfCode,
    codeCount isNegInfCode]
  fin l :=
    let n := l.getD 0 0
    if n = 0 then .null else if sample = true ∧ n = 1 then .null else
      match nonFiniteOf (l.getD 3 0) (l.getD 4 0) (l.getD 5 0) with
      | some _ => .float nan
      | none =>
        let d := if sample then n.toNat - 1 else n.toNat
        let N := n * l.getD 2 0 - l.getD 1 0 * l.getD 1 0
        if sqrt then .float (posCode (sqrtMag N.toNat (n.toNat * d)))
        else .float (ofExactDiv N (n.toNat * d * 2 ^ 1074))
  good v := ∃ c, v = .float c

theorem varState_sound {m : Measure} {sample sqrt : Bool} (hf : m.fn = .var sample sqrt)
    (hd : m.distinct = false) : (varState sample sqrt).Sound m := by
  refine ⟨hd, by simp [hf, AggFn.sorts], fun vs hvs => ?_⟩
  have hfl := floatsOf_length fun v hv => (hvs v hv).2
  simp only [varState, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    sum_one, ← scaledSum_floatsOf, ← sqSumOf_floatsOf, ← nonFinite_eq, hf]
  cases vs with
  | nil => simp [AggFn.apply]
  | cons a l =>
    have hn : ((a :: l).length : Int) ≠ 0 := by simp; omega
    simp only [hn, ite_false, AggFn.apply, varOf, hfl]
    by_cases h1 : sample = true ∧ (a :: l).length = 1
    · have h2 : ((a :: l).length : Int) = 1 := by exact_mod_cast h1.2
      simp [h1.1, h1.2]
    · have h2 : ¬(sample = true ∧ ((a :: l).length : Int) = 1) :=
        fun h => h1 ⟨h.1, by exact_mod_cast h.2⟩
      have h3 : (sample && (a :: l).length == 1) = false := by cases sample <;> simp_all
      simp only [h2, h3, ite_false, Bool.false_eq_true]
      cases nonFinite (a :: l) with
      | some _ => rfl
      | none => simp [comomentNum, hfl]

/-- The state of `COVAR_*`: the number of pairs, `Σx`, `Σy`, `Σxy`, and the
counts of NaN, `+∞` and `-∞` on either side. -/
def covState (sample : Bool) : LinState where
  feats := [pairFeat fun _ => 1, pairFeat fun q => scaled q.1, pairFeat fun q => scaled q.2,
    pairFeat fun q => scaled q.1 * scaled q.2, pairCount isNanCode, pairCount isPosInfCode,
    pairCount isNegInfCode]
  fin l :=
    let n := l.getD 0 0
    if n = 0 ∨ (sample = true ∧ n = 1) then .null else
      match nonFiniteOf (l.getD 4 0) (l.getD 5 0) (l.getD 6 0) with
      | some _ => .float nan
      | none =>
        let d := if sample then n.toNat - 1 else n.toNat
        .float (ofExactDiv (n * l.getD 3 0 - l.getD 1 0 * l.getD 2 0) (n.toNat * d * 2 ^ 1074))

/-- The state of `CORR`: `covState`'s, with `Σx²` and `Σy²`. -/
def corrState : LinState where
  feats := [pairFeat fun _ => 1, pairFeat fun q => scaled q.1, pairFeat fun q => scaled q.2,
    pairFeat fun q => scaled q.1 * scaled q.2, pairFeat fun q => scaled q.1 * scaled q.1,
    pairFeat fun q => scaled q.2 * scaled q.2, pairCount isNanCode, pairCount isPosInfCode,
    pairCount isNegInfCode]
  fin l :=
    let n := l.getD 0 0
    let nx := n * l.getD 4 0 - l.getD 1 0 * l.getD 1 0
    let ny := n * l.getD 5 0 - l.getD 2 0 * l.getD 2 0
    if n < 2 ∨ nx = 0 ∨ ny = 0 then .null else
      match nonFiniteOf (l.getD 6 0) (l.getD 7 0) (l.getD 8 0) with
      | some _ => .float nan
      | none =>
        let c := n * l.getD 3 0 - l.getD 1 0 * l.getD 2 0
        let mg := min (sqrtMag (c.natAbs * c.natAbs * 2 ^ 2148) (nx * ny).toNat) (2 ^ 1074)
        .float (if c < 0 then -posCode mg else posCode mg)

theorem sum_map_one {α : Type} : ∀ xs : List α, (xs.map fun _ => (1 : Int)).sum = xs.length
  | [] => rfl
  | _ :: xs => by rw [List.map_cons, List.sum_cons, sum_map_one xs, List.length_cons]; omega

theorem scaledSum_fst (ps : List (Int × Int)) :
    scaledSum (ps.map (·.1)) = (ps.map fun q => scaled q.1).sum := by
  simp [scaledSum, List.map_map, Function.comp_def, foldr_add_eq_sum]

theorem scaledSum_snd (ps : List (Int × Int)) :
    scaledSum (ps.map (·.2)) = (ps.map fun q => scaled q.2).sum := by
  simp [scaledSum, List.map_map, Function.comp_def, foldr_add_eq_sum]

theorem sqSumOf_fst (ps : List (Int × Int)) :
    sqSumOf (ps.map (·.1)) = (ps.map fun q => scaled q.1 * scaled q.1).sum := by
  simp [sqSumOf, List.map_map, Function.comp_def, foldr_add_eq_sum]

theorem sqSumOf_snd (ps : List (Int × Int)) :
    sqSumOf (ps.map (·.2)) = (ps.map fun q => scaled q.2 * scaled q.2).sum := by
  simp [sqSumOf, List.map_map, Function.comp_def, foldr_add_eq_sum]

theorem prodSumOf_eq (ps : List (Int × Int)) :
    prodSumOf ps = (ps.map fun q => scaled q.1 * scaled q.2).sum := rfl

/-- The apply of a pair aggregate at no values is its function's at no pairs. -/
theorem covOf_nil (sample : Bool) : AggFn.apply (.cov sample) [] = covOf sample [] := rfl

theorem corrOf_nil : AggFn.apply .corr [] = corrOf [] := rfl

/-- **The exact state finishes to `COVAR_*`** (`covOf`). -/
theorem covState_sound {m : Measure} {sample : Bool} (hf : m.fn = .cov sample)
    (hd : m.distinct = false) : (covState sample).Sound m := by
  refine ⟨hd, by simp [hf, AggFn.sorts], fun vs _ => ?_⟩
  have happ : AggFn.apply (.cov sample) vs = covOf sample vs := by
    cases vs with
    | nil => rfl
    | cons _ _ => rfl
  simp only [covState, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    ← pairs_sum, sum_map_one, ← nonFinite_pairs, hf, happ, covOf]
  generalize pairsOf vs = ps
  by_cases h1 : ps.length = 0 ∨ (sample = true ∧ ps.length = 1)
  · have h2 : (ps.length : Int) = 0 ∨ (sample = true ∧ (ps.length : Int) = 1) := by
      rcases h1 with h | ⟨hs, h⟩
      · exact .inl (by omega)
      · exact .inr ⟨hs, by omega⟩
    have h3 : (ps.isEmpty || (sample && ps.length == 1)) = true := by
      rcases h1 with h | h
      · simp [List.isEmpty_iff_length_eq_zero.mpr h]
      · simp [h.1, h.2]
    simp only [h2, h3, ite_true]
  · have h2 : ¬((ps.length : Int) = 0 ∨ (sample = true ∧ (ps.length : Int) = 1)) := by
      rintro (h | ⟨hs, h⟩)
      · exact h1 (.inl (by omega))
      · exact h1 (.inr ⟨hs, by omega⟩)
    have h3 : (ps.isEmpty || (sample && ps.length == 1)) = false := by
      have : ps.isEmpty = false := by
        cases ps with
        | nil => simp at h1
        | cons _ _ => rfl
      cases sample <;> simp_all
    simp only [h2, h3, ite_false, Bool.false_eq_true]
    cases nonFinite (pairCodes ps) with
    | some _ => rfl
    | none => simp [coComomentNum, prodSumOf_eq, scaledSum_fst, scaledSum_snd]

/-- **The exact state finishes to `CORR`** (`corrOf`). -/
theorem corrState_sound {m : Measure} (hf : m.fn = .corr) (hd : m.distinct = false) :
    corrState.Sound m := by
  refine ⟨hd, by simp [hf, AggFn.sorts], fun vs _ => ?_⟩
  have happ : AggFn.apply .corr vs = corrOf vs := by
    cases vs with
    | nil => rfl
    | cons _ _ => rfl
  simp only [corrState, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    ← pairs_sum, sum_map_one, ← nonFinite_pairs, hf, happ, corrOf]
  generalize pairsOf vs = ps
  have hx : comomentNum (ps.map (·.1)) = ps.length * (ps.map fun q => scaled q.1 * scaled q.1).sum -
      (ps.map fun q => scaled q.1).sum * (ps.map fun q => scaled q.1).sum := by
    simp [comomentNum, sqSumOf_fst, scaledSum_fst]
  have hy : comomentNum (ps.map (·.2)) = ps.length * (ps.map fun q => scaled q.2 * scaled q.2).sum -
      (ps.map fun q => scaled q.2).sum * (ps.map fun q => scaled q.2).sum := by
    simp [comomentNum, sqSumOf_snd, scaledSum_snd]
  rw [← hx, ← hy]
  by_cases h1 : ps.length < 2 ∨ comomentNum (ps.map (·.1)) = 0 ∨ comomentNum (ps.map (·.2)) = 0
  · have h2 : (ps.length : Int) < 2 ∨ comomentNum (ps.map (·.1)) = 0 ∨
        comomentNum (ps.map (·.2)) = 0 := by
      rcases h1 with h | h | h
      · exact .inl (by omega)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    have h3 : (decide (ps.length < 2) || comomentNum (ps.map (·.1)) == 0 ||
        comomentNum (ps.map (·.2)) == 0) = true := by
      rcases h1 with h | h | h <;> simp [h]
    simp only [h2, h3, ite_true]
  · have h2 : ¬((ps.length : Int) < 2 ∨ comomentNum (ps.map (·.1)) = 0 ∨
        comomentNum (ps.map (·.2)) = 0) := by
      rintro (h | h | h)
      · exact h1 (.inl (by omega))
      · exact h1 (.inr (.inl h))
      · exact h1 (.inr (.inr h))
    have h3 : (decide (ps.length < 2) || comomentNum (ps.map (·.1)) == 0 ||
        comomentNum (ps.map (·.2)) == 0) = false := by
      simp only [not_or] at h1; simp [h1.1, h1.2.1, h1.2.2]
    simp only [h2, h3, ite_false, Bool.false_eq_true]
    cases nonFinite (pairCodes ps) with
    | some _ => rfl
    | none => simp [coComomentNum, prodSumOf_eq, scaledSum_fst, scaledSum_snd]

end LinearAgg
end Substrait
