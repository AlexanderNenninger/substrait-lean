import Sverify.Core.AllowedP
import Sverify.Core.FloatArith

/-!
# The range of an engine's double `SUM` (D35)

`SumOrder` bounds every non-`EXACT` summation order by `SumBound`: the sum is
finite, and within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact sum.
`SumOrder.bound` reads it as a range the abstract domain can compute: from
the inputs' range `[lo, hi]` (in units of `2⁻¹⁰⁷⁴`) and a row bound `N`, the
sum is finite and in `[sumLo N lo hi, sumHi N lo hi]` whenever `sumSafe`
holds. The range is crude (the error term `N · (M + 2⁵²)` takes `γₙ + u ≤ 1`);
its use is finiteness and the cases of an operation it cuts (#925, D34).
`EXACT`, the reference's order, has the round-once range of
`floatSumCR_mem`.
-/

namespace Substrait

open FloatCode

/-- The larger magnitude of a range's ends. -/
def rangeMag (lo hi : Int) : Nat := max lo.natAbs hi.natAbs

set_option exponentiation.threshold 2100 in
/-- `N` values in `[lo, hi]` keep their sum's bound below the largest double. -/
def sumSafe (N : Nat) (lo hi : Int) : Bool := 2 * (N * (rangeMag lo hi + 2 ^ 52)) ≤ maxMag

/-- The least an engine's `SUM` of `N` values in `[lo, hi]` may be. -/
def sumLo (N : Nat) (lo hi : Int) : Int := min lo (N * lo) - (N * (rangeMag lo hi + 2 ^ 52) : Nat)

/-- The most an engine's `SUM` of `N` values in `[lo, hi]` may be. -/
def sumHi (N : Nat) (lo hi : Int) : Int := max hi (N * hi) + (N * (rangeMag lo hi + 2 ^ 52) : Nat)

theorem scaledAbsSum_le {lo hi : Int} :
    ∀ {cs : List Int}, (∀ c ∈ cs, lo ≤ scaled c ∧ scaled c ≤ hi) →
      scaledAbsSum (cs.map .float) ≤ cs.length * rangeMag lo hi
  | [], _ => by simp [scaledAbsSum]
  | c :: cs, h => by
    have ih := scaledAbsSum_le (cs := cs) fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ⟨h1, h2⟩ := h c (List.mem_cons_self ..)
    have : (scaled c).natAbs ≤ rangeMag lo hi := by unfold rangeMag; omega
    simp only [List.map_cons, scaledAbsSum, List.length_cons, Nat.succ_mul]
    omega

/-- `min lo (N · lo) ≤ k · lo` for `1 ≤ k ≤ N`. -/
theorem min_le_mul {lo : Int} {k N : Nat} (hk : 1 ≤ k) (hkN : k ≤ N) :
    min lo (N * lo) ≤ k * lo := by
  rcases Int.le_total 0 lo with h | h
  · have : lo ≤ k * lo := by
      have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ k by omega) h
      simpa using this
    omega
  · have : (N : Int) * lo ≤ k * lo := Int.mul_le_mul_of_nonpos_right (by omega) h
    omega

/-- `k · hi ≤ max hi (N · hi)` for `1 ≤ k ≤ N`. -/
theorem mul_le_max {hi : Int} {k N : Nat} (hk : 1 ≤ k) (hkN : k ≤ N) :
    k * hi ≤ max hi (N * hi) := by
  rcases Int.le_total 0 hi with h | h
  · have : (k : Int) * hi ≤ N * hi := Int.mul_le_mul_of_nonneg_right (by omega) h
    omega
  · have : k * hi ≤ hi := by
      have := Int.mul_le_mul_of_nonpos_right (show (1 : Int) ≤ k by omega) h
      simpa using this
    omega

set_option exponentiation.threshold 2100 in
/-- **An engine's double `SUM` is finite and in range (D35).** Under a
non-`EXACT` behaviour, the sum of `1 ≤ n ≤ N ≤ 2³²` finite doubles in
`[lo, hi]` is finite and in `[sumLo N lo hi, sumHi N lo hi]`, where `sumSafe`
holds. -/
theorem SumOrder.bound {b : Behaviour} {cs : List Int} {c : Int} {N : Nat} {lo hi : Int}
    (hb : b ≠ "EXACT") (h : SumOrder b (cs.map .float) c) (hne : cs ≠ []) (hN : cs.length ≤ N)
    (h32 : N ≤ 2 ^ 32) (hr : ∀ x ∈ cs, IsFin x ∧ lo ≤ scaled x ∧ scaled x ≤ hi)
    (hsafe : sumSafe N lo hi = true) :
    IsFin c ∧ sumLo N lo hi ≤ scaled c ∧ scaled c ≤ sumHi N lo hi := by
  simp only [SumOrder, hb, ↓reduceIte] at h
  have hb' : ∀ x ∈ cs, lo ≤ scaled x ∧ scaled x ≤ hi := fun x hx => (hr x hx).2
  have hA := scaledAbsSum_le hb'
  have hlen : (cs.map Value.float).length = cs.length := List.length_map _
  have hsafe' := of_decide_eq_true hsafe
  have hn1 : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  have hmag : scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 ≤ N * (rangeMag lo hi + 2 ^ 52) := by
    have : cs.length * rangeMag lo hi ≤ N * rangeMag lo hi := Nat.mul_le_mul_right _ hN
    have : cs.length * 2 ^ 52 ≤ N * 2 ^ 52 := Nat.mul_le_mul_right _ hN
    rw [Nat.mul_add]; omega
  obtain ⟨hfin, hineq⟩ := h.1
    (fun x hx => by
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hx
      injection e with e; subst e; exact (hr _ hy).1)
    (by rw [hlen]; omega)
    (by rw [hlen]; omega)
  rw [hlen] at hineq
  refine ⟨hfin, ?_⟩
  -- `γₙ + u ≤ 1` for `n ≤ 2³²`: the distance is at most the magnitude.
  generalize hd : (scaled c - exactSum (cs.map .float)).natAbs = d at hineq
  generalize hQ : scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 = Q at hineq hmag
  have hF : cs.length * 2 ^ 53 + (2 ^ 53 - cs.length) ≤ 2 ^ 53 * (2 ^ 53 - cs.length) := by omega
  have hD : 0 < 2 ^ 53 * (2 ^ 53 - cs.length) := by omega
  have hdq : d ≤ Q := by
    have : d * (2 ^ 53 * (2 ^ 53 - cs.length)) ≤ (2 ^ 53 * (2 ^ 53 - cs.length)) * Q :=
      Nat.le_trans hineq (Nat.mul_le_mul_right _ hF)
    rw [Nat.mul_comm] at this
    exact Nat.le_of_mul_le_mul_left this hD
  have ⟨s1, s2⟩ := exactSum_bounds (cs := cs) (lo := lo) (hi := hi) fun x hx => by
    rw [FloatCode.canon_of_bounds (hr x hx).1]; exact hb' x hx
  have l1 := min_le_mul (lo := lo) hn1 hN
  have l2 := mul_le_max (hi := hi) hn1 hN
  unfold sumLo sumHi
  have : (d : Int) ≤ (N * (rangeMag lo hi + 2 ^ 52) : Nat) := by omega
  constructor <;> omega

end Substrait
