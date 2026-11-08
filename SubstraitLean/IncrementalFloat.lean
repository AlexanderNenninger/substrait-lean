import SubstraitLean.IncrementalAgg

/-!
# Delta rules for `SUM` and `AVG` of doubles, exactly (#918 Part B)

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
* `fsum_no_drift`: after any sequence of batches whose weights add up to the
  current rows, the summed state finishes to the aggregate of those rows,
  `floatSumCR` of the group's values (`Measure.eval_fsum`). It holds whatever
  the order or number of batches: a delete cancels its insert exactly, so
  nothing drifts.

The engine keeps the exact sum as a sum of mantissas per binary exponent
(`python/src/sverify/_linear.py`), which is this integer written in pieces.
-/

namespace Substrait
namespace LinearAgg

open FloatCode

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

/-- **No drift.** After any sequence of batches `Δs` (inserts and deletes,
in any order and number) whose weights add up to the bag `rows`, the summed
state of a `SUM` or `AVG` of doubles finishes, for every group `k`, to the
aggregate of the group's current rows: for `SUM`, `floatSumCR` of its
values (`Measure.eval_fsum`). -/
theorem fsum_no_drift {gs : List Expr} {m : Measure} (hf : m.fn = .fsum ∨ m.fn = .avg)
    (hd : m.distinct = false) {rows : Relation} (Δs : List ZSet)
    (hw : ∀ r, WSet.weight Δs.flatten r = (ZSet.lift rows).weight r) (k : Row) :
    (floatState (m.fn == .avg)).fin ((floatState (m.fn == .avg)).feats.map fun f =>
      (Δs.map (featIn gs m f k)).sum) = m.eval (groupRows gs rows k) := by
  have hc : ∀ f, featIn gs m f k Δs.flatten = featIn gs m f k (ZSet.lift rows) :=
    fun _ => featIn_congr hw
  simp only [featIn_flatten, hc]
  exact fin_eval (floatState_sound hf hd) (fun _ _ _ => trivial) k

end LinearAgg
end Substrait
