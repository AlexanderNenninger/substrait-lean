import Sverify.Core.AllowedP
import Sverify.Core.FloatArith
import Sverify.Core.FloatDbl

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
  obtain ⟨hfin, hineq⟩ := h.1.1
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

/-! ## The canonical clause of `SumBound` for the shaped orders (ruling 242) -/

/-- A sequential sum from an accumulator equal up to `canon`, over the
canonical values, is the same sum up to `canon`. -/
theorem foldl_fadd_canonV (ws : List Value) {a a' : Int} (e : canon a' = canon a) :
    canon ((ws.map Value.canonV).foldl (fun acc v => match v with
      | .float c => fadd acc c | _ => acc) a') =
    canon (ws.foldl (fun acc v => match v with | .float c => fadd acc c | _ => acc) a) := by
  induction ws generalizing a a' with
  | nil => exact e
  | cons w ws ih =>
    apply ih
    cases w <;> simp only [Value.canonV]
    case float c => rw [← fadd_canon, canon_idem, e, fadd_canon]
    all_goals exact e

/-- **A sum `FloatSums` allows is, up to `canon`, one it allows of the
canonical values** (ruling 242): IEEE addition reads `-0.0` as `+0.0` but for
the sign of a zero result (`fadd_canon`), so the same order over the canonical
values gives the same sum up to `canon`. -/
theorem FloatSums.canonV {vs : List Value} {c : Int} (h : FloatSums vs c) :
    ∃ c', FloatSums (vs.map Value.canonV) c' ∧ canon c' = canon c := by
  induction h with
  | @seq vs ws hp =>
    exact ⟨floatSum (ws.map Value.canonV), .seq (hp.map _), foldl_fadd_canonV ws rfl⟩
  | @split vs xs ys a b hp _ _ iha ihb =>
    obtain ⟨a', ha, ea⟩ := iha
    obtain ⟨b', hb, eb⟩ := ihb
    refine ⟨fadd a' b', .split (by rw [← List.map_append]; exact hp.map _) ha hb, ?_⟩
    rw [← fadd_canon, ea, eb, fadd_canon]

/-- `SumBoundRaw` of a sum `c'` bounds every `c` equal to it up to `canon`, as
its canonical code: a finite `c'` is canonical. -/
theorem SumBoundRaw.canon_of {vs : List Value} {c c' : Int} (h : SumBoundRaw vs c')
    (e : canon c' = canon c) : SumBoundRaw vs (canon c) := by
  intro hf hl ho
  obtain ⟨hfin, hb⟩ := h hf hl ho
  have hc : canon c' = c' := fp64.canon_eq_self ⟨hfin.ne.2.2.2.2, hfin.ne.2.1⟩
  rw [← e, hc]; exact ⟨hfin, hb⟩

/-- **`SumBound` from `SumBoundRaw`**, for any sums `P` that keep their
shape over the canonical values up to `canon`: the canonical clause is the raw
one of the canonical sum. -/
theorem SumBound.of_raw {P : List Value → Int → Prop}
    (hcanon : ∀ {vs : List Value} {c : Int}, P vs c →
      ∃ c', P (vs.map Value.canonV) c' ∧ canon c' = canon c)
    (hraw : ∀ {vs : List Value} {c : Int}, P vs c → SumBoundRaw vs c)
    {vs : List Value} {c : Int} (h : P vs c) : SumBound vs c := by
  obtain ⟨c', h', e⟩ := hcanon h
  exact ⟨hraw h, (hraw h').canon_of e⟩

/-- `SumBound` of every sum `FloatSums` allows, from `SumBoundRaw` of them:
the canonical clause follows from `FloatSums.canonV`. -/
theorem FloatSums.sumBound_of_raw (hraw : ∀ {vs : List Value} {c : Int}, FloatSums vs c → SumBoundRaw vs c)
    {vs : List Value} {c : Int} (h : FloatSums vs c) : SumBound vs c :=
  SumBound.of_raw FloatSums.canonV hraw h

/-! ## Kahan's sum and constant runs on codes (#1196)

The two orders whose `SumOrder` clause is a bound and no shape, written as the
engines compute them. `float-bounds/FloatBridge/Orders.lean` proves that each
meets `SumOrder`: Kahan's sum in any order (`COMPENSATED`, polars-sum-float)
and a tree of sums with constant runs (`SCALED_CONSTANT`, duckdb-sum-double). -/

/-- One step of Kahan's compensated sum on codes: from the running sum and
the compensation `(s, c)`, a double `x` takes `y = x − c`, `t = s + y`, and
the compensation `(t − s) − y` (`KahanSum::add_assign` in polars-utils). -/
def kahanStep (p : Int × Int) : Value → Int × Int
  | .float x =>
    let y := fsub x p.2
    let t := fadd p.1 y
    (t, fsub (fsub t p.1) y)
  | _ => p

/-- **Kahan's compensated sum** of the doubles among `ws`, in list order, from
`(+0.0, +0.0)`: the running sum at the end. -/
def kahanSum (ws : List Value) : Int := (ws.foldl kahanStep (0, 0)).1

/-- Kahan's sums of `vs`, doubles' codes (`Dbl`, ruling 268): one per order
of its values. -/
def KahanSums (vs : List Value) (c : Int) : Prop :=
  (∀ x, Value.float x ∈ vs → Dbl x) ∧ ∃ ws, ws.Perm vs ∧ c = kahanSum ws

/-- **Sums with constant runs**: `FloatSums`' shapes, and a run of `k ≥ 1`
copies of one double added as one product `k · x`, rounded once
(`SCALED_CONSTANT`: DuckDB's `AddConstant`). The run's value is a double's
code (`Dbl`, ruling 268): the codes `-1` and `-2`, of magnitude zero, are no
double's, and their product is `-0.0`. -/
inductive FloatSumsK : List Value → Int → Prop
  | seq {vs ws : List Value} : ws.Perm vs → FloatSumsK vs (floatSum ws)
  | split {vs xs ys : List Value} {a b : Int} : vs.Perm (xs ++ ys) → FloatSumsK xs a →
      FloatSumsK ys b → FloatSumsK vs (fadd a b)
  | const (k : Nat) (x : Int) : 1 ≤ k → Dbl x →
      FloatSumsK (List.replicate k (.float x)) (fmul (ofInt k) x)

/-- Kahan's steps over the canonical values, from a state equal up to `canon`,
end in a state equal up to `canon`. -/
theorem foldl_kahanStep_canonV (ws : List Value) {p p' : Int × Int}
    (e1 : canon p'.1 = canon p.1) (e2 : canon p'.2 = canon p.2) :
    canon ((ws.map Value.canonV).foldl kahanStep p').1 = canon (ws.foldl kahanStep p).1 := by
  induction ws generalizing p p' with
  | nil => exact e1
  | cons w ws ih =>
    apply ih
    all_goals cases w <;> simp only [Value.canonV, kahanStep]
    all_goals first | exact e1 | exact e2 | skip
    all_goals rename_i x
    · have ey : canon (fsub (canon x) p'.2) = canon (fsub x p.2) := by
        rw [← fsub_canon, canon_idem, e2, fsub_canon]
      rw [← fadd_canon, e1, ey, fadd_canon]
    · have ey : canon (fsub (canon x) p'.2) = canon (fsub x p.2) := by
        rw [← fsub_canon, canon_idem, e2, fsub_canon]
      have et : canon (fadd p'.1 (fsub (canon x) p'.2)) = canon (fadd p.1 (fsub x p.2)) := by
        rw [← fadd_canon, e1, ey, fadd_canon]
      have ed : canon (fsub (fadd p'.1 (fsub (canon x) p'.2)) p'.1) =
          canon (fsub (fadd p.1 (fsub x p.2)) p.1) := by
        rw [← fsub_canon, et, e1, fsub_canon]
      rw [← fsub_canon, ed, ey, fsub_canon]

/-- **A Kahan's sum is, up to `canon`, one of the canonical values** (ruling
242): IEEE arithmetic reads `-0.0` as `+0.0` but for the sign of a zero
result. -/
theorem KahanSums.canonV {vs : List Value} {c : Int} (h : KahanSums vs c) :
    ∃ c', KahanSums (vs.map Value.canonV) c' ∧ canon c' = canon c := by
  obtain ⟨hd, ws, hp, rfl⟩ := h
  refine ⟨kahanSum (ws.map Value.canonV), ⟨fun y hy => ?_, _, hp.map _, rfl⟩,
    foldl_kahanStep_canonV ws rfl rfl⟩
  obtain ⟨v, hv, e⟩ := List.mem_map.mp hy
  cases v <;> simp only [Value.canonV, Value.float.injEq, reduceCtorEq] at e
  rw [← e]; exact dbl_canon (hd _ hv)

/-- **A sum with constant runs is, up to `canon`, one of the canonical values**
(ruling 242). -/
theorem FloatSumsK.canonV {vs : List Value} {c : Int} (h : FloatSumsK vs c) :
    ∃ c', FloatSumsK (vs.map Value.canonV) c' ∧ canon c' = canon c := by
  induction h with
  | @seq vs ws hp =>
    exact ⟨floatSum (ws.map Value.canonV), .seq (hp.map _), foldl_fadd_canonV ws rfl⟩
  | @split vs xs ys a b hp _ _ iha ihb =>
    obtain ⟨a', ha, ea⟩ := iha
    obtain ⟨b', hb, eb⟩ := ihb
    refine ⟨fadd a' b', .split (by rw [← List.map_append]; exact hp.map _) ha hb, ?_⟩
    rw [← fadd_canon, ea, eb, fadd_canon]
  | const k x hk hx =>
    refine ⟨fmul (ofInt k) (canon x), ?_, ?_⟩
    · rw [List.map_replicate, Value.canonV]
      exact .const k (canon x) hk (dbl_canon hx)
    · rw [← fmul_canon, canon_idem, fmul_canon]

end Substrait
