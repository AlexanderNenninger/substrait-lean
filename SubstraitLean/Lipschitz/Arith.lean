import SubstraitLean.Lipschitz.Measures

/-!
# Tolerance composition: arithmetic, `MIN`, `MAX` and groups (#929)

The arithmetic rows (`Expr.arithTol`, `Expr.tolA`), the `MIN` and `MAX`
rows (`Measure.minMaxOut`), a group's measures (`aggregateEval_near`) and
the sources' row bound (`Rel.rowsK`).
-/

namespace Substrait

open FloatCode

/-! ### The arithmetic rows (#929 step C)

D31 makes `+ - * /` of doubles the exact result rounded once, so their
distances are provable: an operand within `e` codes moves the exact result
by at most `e + 1` halves of its unit times the other operand's magnitude,
and each side's rounding by half an ulp. An operand (`Expr.atom?`) is a
column of doubles in reference codes (`mask`), whose range the analysis
bounds finitely `e` codes beyond each end, or a finite double literal.

Each operand carries its own perturbation: `x - x` counts the column's twice,
so the rule is conservative there. -/

/-- An operand of an arithmetic row: its tolerance, and the reference's range
of codes. -/
def Expr.atom? (t : Tol) (mask : Nat → Bool) (env : List AVal) : Expr → Option (Nat × Int × Int)
  | .field k =>
    match colRange env k with
    | some (lo, hi) =>
      if mask k && (env.getD k AVal.top).kindOnly .float &&
          decide (negInf < lo - ((t k).getD 0 : Nat)) && decide (hi + ((t k).getD 0 : Nat) < posInf) then
        some ((t k).getD 0, lo, hi)
      else none
    | none => none
  | .lit (.float c) => if decide (negInf < c) && decide (c < posInf) then some (0, c, c) else none
  | _ => none

/-- An operand's values on two paired rows: both NULL, or two finite doubles
within its tolerance, the reference's in its range. -/
theorem Expr.atom?_sound {t : Tol} {mask : Nat → Bool} {env : List AVal} {e : Expr}
    {ε : Nat} {lo hi : Int} (h : e.atom? t mask env = some (ε, lo, hi)) {x y : Row}
    (r : t.Rows x y) (hx : ∀ j c, mask j = true → x.getD j .null = .float c → IsRef c)
    (hy : EnvMem env y) :
    (e.eval x = .null ∧ e.eval y = .null) ∨
      ∃ a b, e.eval x = .float a ∧ e.eval y = .float b ∧ (a - b).natAbs ≤ ε ∧ lo ≤ b ∧ b ≤ hi ∧
        IsFin a ∧ IsFin b := by
  cases e with
  | lit v =>
    cases v with
    | float c =>
      simp only [Expr.atom?, Bool.and_eq_true, decide_eq_true_eq] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .inr ⟨c, c, rfl, rfl, by simp, Int.le_refl _, Int.le_refl _, hc, hc⟩
      · cases h
    | _ => simp [Expr.atom?] at h
  | field k =>
    simp only [Expr.atom?] at h
    cases hcr : colRange env k with
    | none => simp [hcr] at h
    | some rg =>
      obtain ⟨lo', hi'⟩ := rg
      simp only [hcr] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hm, hko⟩, hlo⟩, hhi⟩ := hc
        simp only [Expr.eval]
        have hmem := hy k
        have hcell := r.2 k
        cases hv : y.getD k .null with
        | null =>
          rw [hv] at hcell
          left; refine ⟨?_, rfl⟩
          cases hxv : x.getD k .null <;> rw [hxv] at hcell <;> first | rfl | exact hcell.elim
        | float b =>
          rw [hv] at hmem hcell
          obtain ⟨b', bd, hvb, hb, hbm⟩ := AVal.kindOnly_mem hko hmem (by simp)
          have hbb : b = b' := by simpa [NumKind.val] using hvb
          subst hbb
          right
          unfold colRange at hcr
          split at hcr
          · rename_i lo'' hi'' hint
            simp only [Option.some.injEq, Prod.mk.injEq] at hcr
            obtain ⟨rfl, rfl⟩ := hcr
            rw [hint] at hb; cases hb
            have hb1 := hbm.1 _ rfl; have hb2 := hbm.2 _ rfl
            have fb : IsFin b := ⟨by omega, by omega⟩
            cases hxv : x.getD k .null with
            | float a =>
              rw [hxv] at hcell
              have ha := hx k a hm hxv
              have hab : (a - b).natAbs ≤ (t k).getD 0 := by
                cases htk : t k with
                | none =>
                  have := (Tol.cell_none htk).1 hcell
                  cases this; simp
                | some ε =>
                  have hn := Tol.cell_float_iff' htk hcell
                  rw [show fp64.canon a = a from canon_of_isRef ha,
                    show fp64.canon b = b from canon_of_isRef (isRef_of_bounds fb)] at hn
                  simpa using hn
              exact ⟨a, b, rfl, rfl, hab, hb1, hb2, ⟨by omega, by omega⟩, fb⟩
            | _ => all_goals (rw [hxv] at hcell; exact hcell.elim)
          · cases hcr
        | _ =>
          all_goals
            rw [hv] at hmem
            obtain ⟨b', bd, hvb, -, -⟩ := AVal.kindOnly_mem hko hmem (by simp)
            simp [NumKind.val] at hvb
      · cases h
  | _ => simp [Expr.atom?] at h

/-- Two roundings by `n` of exact values `N₁`, `N₂`: within their distance
divided by `n`, both ulps and the codes' slack. -/
theorem round_pair {N₁ N₂ : Int} {n : Nat} (hn : 0 < n) (f₁ : IsFin (ofExactDiv N₁ n))
    (f₂ : IsFin (ofExactDiv N₂ n)) :
    (ofExactDiv N₁ n - ofExactDiv N₂ n).natAbs ≤
      4 + ulpDiv N₁ n + ulpDiv N₂ n + (2 * (N₁ - N₂).natAbs + n - 1) / n := by
  have w₁ := ofExactDiv_within hn f₁
  have w₂ := ofExactDiv_within hn f₂
  have c₁ := code_sub_scaled (ofExactDiv N₁ n)
  have c₂ := code_sub_scaled (ofExactDiv N₂ n)
  generalize ofExactDiv N₁ n = r₁ at *
  generalize ofExactDiv N₂ n = r₂ at *
  generalize ulpDiv N₁ n = u₁ at *
  generalize ulpDiv N₂ n = u₂ at *
  generalize scaled r₁ = s₁ at *
  generalize scaled r₂ = s₂ at *
  have key : (n : Int) * (s₁ - s₂) = ((n : Int) * s₁ - N₁) + (N₁ - N₂) + (N₂ - (n : Int) * s₂) := by
    rw [Int.mul_sub]; omega
  have t := natAbs_add3_le ((n : Int) * s₁ - N₁) (N₁ - N₂) (N₂ - (n : Int) * s₂)
  rw [← key, Int.natAbs_mul, Int.natAbs_natCast] at t
  have hs₂ : (N₂ - (n : Int) * s₂).natAbs = ((n : Int) * s₂ - N₂).natAbs := by
    rw [← Int.natAbs_neg, Int.neg_sub]
  rw [hs₂] at t
  generalize ((n : Int) * s₁ - N₁).natAbs = E₁ at *
  generalize ((n : Int) * s₂ - N₂).natAbs = E₂ at *
  generalize (N₁ - N₂).natAbs = D at *
  -- `2 · n · |s₁ - s₂| ≤ n (u₁ + u₂) + 2 D`.
  have hA : (2 * (s₁ - s₂).natAbs - (u₁ + u₂)) * n ≤ 2 * D + n - 1 := by
    rw [Nat.sub_mul, Nat.mul_assoc, Nat.mul_comm (s₁ - s₂).natAbs n, Nat.add_mul,
      Nat.mul_comm u₁ n, Nat.mul_comm u₂ n]
    generalize n * (s₁ - s₂).natAbs = X at *
    omega
  have := (Nat.le_div_iff_mul_le hn).2 hA
  have e : r₁ - r₂ = (r₁ - 2 * s₁) + 2 * (s₁ - s₂) + (2 * s₂ - r₂) := by omega
  have hc₂ : (2 * s₂ - r₂).natAbs = (r₂ - 2 * s₂).natAbs := by rw [← Int.natAbs_neg, Int.neg_sub]
  have t2 := natAbs_add3_le (r₁ - 2 * s₁) (2 * (s₁ - s₂)) (2 * s₂ - r₂)
  rw [← e, Int.natAbs_mul, hc₂] at t2
  have : (2 : Int).natAbs = 2 := rfl
  rw [this] at t2
  omega

theorem scaled_neg' (c : Int) : scaled (-c) = -scaled c := by
  unfold scaled; split <;> split <;> omega

theorem IsFin.neg {c : Int} (h : IsFin c) : IsFin (-c) := by
  have := posInf_eq; have := negInf_eq; obtain ⟨h1, h2⟩ := h; exact ⟨by omega, by omega⟩

/-- An engine operand's magnitude: the reference's range's, plus its
tolerance. -/
theorem atom_mag {e : Nat} {lo hi a b : Int} (hab : (a - b).natAbs ≤ e) (hb1 : lo ≤ b) (hb2 : b ≤ hi) :
    (scaled a).natAbs ≤ magOf lo hi + e ∧ (scaled b).natAbs ≤ magOf lo hi := by
  have hs := scaled_sub_le a b
  have hm := scaled_natAbs_le hb1 hb2
  refine ⟨?_, hm⟩
  have := Int.natAbs_add_le (scaled a - scaled b) (scaled b)
  rw [Int.sub_add_cancel] at this
  omega

theorem fadd_eq_sumCR {a b : Int} (ha : IsFin a) (hb : IsFin b) :
    fadd a b = floatSumCR [.float a, .float b] := by
  have hf : FinCodes [.float a, .float b] := fun c hc => by
    simp only [List.mem_cons, Value.float.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  rw [fadd_fin ha hb]
  simp [floatSumCR, nonFinite_of_finCodes hf, exactSum]

/-- **`x + y`**: two finite operands within `e` codes each, of magnitudes at
most `M` together: within `2 (e + 1)` codes and both roundings. -/
theorem fadd_near {e M : Nat} {a₁ a₂ b₁ b₂ : Int} (f₁ : IsFin a₁) (f₂ : IsFin a₂) (g₁ : IsFin b₁)
    (g₂ : IsFin b₂) (h₁ : (a₁ - b₁).natAbs ≤ e) (h₂ : (a₂ - b₂).natAbs ≤ e)
    (hM : (scaled a₁).natAbs + (scaled a₂).natAbs ≤ M) (hM' : (scaled b₁).natAbs + (scaled b₂).natAbs ≤ M)
    (hbig : M ≤ 2 ^ 2097) :
    (fadd a₁ a₂ - fadd b₁ b₂).natAbs ≤ 2 * (e + 1) + 2 * ulpDiv (M : Int) 1 + 4 := by
  rw [fadd_eq_sumCR f₁ f₂, fadd_eq_sumCR g₁ g₂]
  have hfin : ∀ {x y : Int}, IsFin x → IsFin y → FinCodes [.float x, .float y] := fun hx hy c hc => by
    simp only [List.mem_cons, Value.float.injEq, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  have hS : ∀ {x y : Int}, (exactSum [.float x, .float y]).natAbs ≤ (scaled x).natAbs + (scaled y).natAbs :=
    fun {x y} => by simpa [exactSum] using Int.natAbs_add_le (scaled x) (scaled y)
  have hfS : ∀ {x y : Int}, (scaled x).natAbs + (scaled y).natAbs ≤ M →
      IsFin (ofExact (exactSum [.float x, .float y])) := fun {x y} h =>
    ofExactDiv_fin (n := 1) (by omega) (by have := hS (x := x) (y := y); omega)
  have hc := floatSumCR_near (e := e) (.cons (show CodeNear e (.float a₁) (.float b₁) from h₁)
    (.cons (show CodeNear e (.float a₂) (.float b₂) from h₂) .nil)) (hfin f₁ f₂) (hfin g₁ g₂)
    (hfS hM) (hfS hM')
  have u₁ := ulpDiv_mono (v := exactSum [.float a₁, .float a₂]) (w := (M : Int)) 1
    (by rw [Int.natAbs_natCast]; exact Nat.le_trans hS hM)
  have u₂ := ulpDiv_mono (v := exactSum [.float b₁, .float b₂]) (w := (M : Int)) 1
    (by rw [Int.natAbs_natCast]; exact Nat.le_trans hS hM')
  simp only [List.length_cons, List.length_nil] at hc
  omega

theorem fsub_eq_fadd {a b : Int} (ha : IsFin a) (hb : IsFin b) : fsub a b = fadd a (-b) := by
  rw [fsub_fin ha hb, fadd_fin ha (IsFin.neg hb), scaled_neg', Int.sub_eq_add_neg]

set_option exponentiation.threshold 3200 in
/-- **`x · y`**: the exact products within `(Mx (ey + 1) + My (ex + 1)) / 2`,
then both roundings. -/
theorem fmul_near {ex ey Mx My : Nat} {a₁ a₂ b₁ b₂ : Int} (f₁ : IsFin a₁) (f₂ : IsFin a₂)
    (g₁ : IsFin b₁) (g₂ : IsFin b₂) (h₁ : (a₁ - b₁).natAbs ≤ ex) (h₂ : (a₂ - b₂).natAbs ≤ ey)
    (ma₁ : (scaled a₁).natAbs ≤ Mx) (ma₂ : (scaled a₂).natAbs ≤ My)
    (mb₁ : (scaled b₁).natAbs ≤ Mx) (mb₂ : (scaled b₂).natAbs ≤ My) (hbig : Mx * My ≤ 2 ^ 3171) :
    (fmul a₁ a₂ - fmul b₁ b₂).natAbs ≤
      4 + 2 * ulpDiv ((Mx * My : Nat) : Int) unitK + (Mx * (ey + 1) + My * (ex + 1) + unitK - 1) / unitK := by
  rw [fmul_fin f₁ f₂, fmul_fin g₁ g₂]
  have hK : 0 < unitK := Nat.two_pow_pos _
  have hP : ∀ {x y : Int}, (scaled x).natAbs ≤ Mx → (scaled y).natAbs ≤ My →
      (scaled x * scaled y).natAbs ≤ Mx * My := fun hx hy => by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx hy
  have hcap : Mx * My ≤ unitK * 2 ^ 2097 := by
    refine Nat.le_trans hbig (Nat.le_of_eq ?_); unfold unitK; rw [← Nat.pow_add]
  have r := round_pair hK (ofExactDiv_fin hK (Nat.le_trans (hP ma₁ ma₂) hcap))
    (ofExactDiv_fin hK (Nat.le_trans (hP mb₁ mb₂) hcap))
  have u₁ := ulpDiv_mono (v := scaled a₁ * scaled a₂) (w := ((Mx * My : Nat) : Int)) unitK
    (by rw [Int.natAbs_natCast]; exact hP ma₁ ma₂)
  have u₂ := ulpDiv_mono (v := scaled b₁ * scaled b₂) (w := ((Mx * My : Nat) : Int)) unitK
    (by rw [Int.natAbs_natCast]; exact hP mb₁ mb₂)
  -- `2 |P - P'| ≤ Mx (ey + 1) + My (ex + 1)`.
  have hD : 2 * (scaled a₁ * scaled a₂ - scaled b₁ * scaled b₂).natAbs ≤ Mx * (ey + 1) + My * (ex + 1) := by
    have e : scaled a₁ * scaled a₂ - scaled b₁ * scaled b₂ =
        scaled a₁ * (scaled a₂ - scaled b₂) + scaled b₂ * (scaled a₁ - scaled b₁) := by
      rw [Int.mul_sub, Int.mul_sub]; rw [Int.mul_comm (scaled b₂) (scaled a₁), Int.mul_comm (scaled b₂)]
      omega
    rw [e]
    have t := Int.natAbs_add_le (scaled a₁ * (scaled a₂ - scaled b₂)) (scaled b₂ * (scaled a₁ - scaled b₁))
    rw [Int.natAbs_mul, Int.natAbs_mul] at t
    have s₁ := scaled_sub_le a₁ b₁
    have s₂ := scaled_sub_le a₂ b₂
    have k₁ : (scaled a₁).natAbs * (2 * (scaled a₂ - scaled b₂).natAbs) ≤ Mx * (ey + 1) :=
      Nat.mul_le_mul ma₁ (by omega)
    have k₂ : (scaled b₂).natAbs * (2 * (scaled a₁ - scaled b₁).natAbs) ≤ My * (ex + 1) :=
      Nat.mul_le_mul mb₂ (by omega)
    rw [Nat.mul_left_comm] at k₁ k₂
    omega
  have hq := Nat.div_le_div_right (c := unitK) (Nat.add_le_add_right (Nat.add_le_add_right hD unitK) 0)
  simp only [Nat.add_zero] at hq
  have hq' : (2 * (scaled a₁ * scaled a₂ - scaled b₁ * scaled b₂).natAbs + unitK - 1) / unitK ≤
      (Mx * (ey + 1) + My * (ex + 1) + unitK - 1) / unitK :=
    Nat.div_le_div_right (by omega)
  omega

/-- `a ≤ n · ⌈a / n⌉`. -/
theorem le_mul_ceilDiv {a n : Nat} (hn : 0 < n) : a ≤ n * ((a + n - 1) / n) := by
  have := Nat.div_add_mod (a + n - 1) n
  have := Nat.mod_lt (a + n - 1) hn
  rw [Nat.mul_comm] at *
  omega

set_option exponentiation.threshold 3200 in
/-- **`x / c`** for a finite non-zero literal `c`: one division by `|c|` on
both sides. -/
theorem fdiv_lit_near {e Mx : Nat} {a b c : Int} (fa : IsFin a) (fb : IsFin b) (fc : IsFin c)
    (hc0 : scaled c ≠ 0) (h : (a - b).natAbs ≤ e) (ma : (scaled a).natAbs ≤ Mx)
    (mb : (scaled b).natAbs ≤ Mx)
    (hbig : (Mx * unitK + (scaled c).natAbs - 1) / (scaled c).natAbs ≤ 2 ^ 2097) :
    (fdiv a c - fdiv b c).natAbs ≤
      4 + 2 * ulpDiv (((Mx * unitK + (scaled c).natAbs - 1) / (scaled c).natAbs : Nat) : Int) 1 +
        (unitK * (e + 1) + (scaled c).natAbs - 1) / (scaled c).natAbs := by
  rw [fdiv_fin fa fc hc0, fdiv_fin fb fc hc0]
  generalize hn : (scaled c).natAbs = n at *
  have hn0 : 0 < n := by rw [← hn]; exact Int.natAbs_pos.2 hc0
  generalize hB : (Mx * unitK + n - 1) / n = B at *
  have hNB : ∀ {x : Int}, (scaled x).natAbs ≤ Mx →
      ((if scaled c < 0 then -scaled x else scaled x) * (unitK : Int)).natAbs ≤ n * B := by
    intro x hx
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have : (if scaled c < 0 then -scaled x else scaled x).natAbs = (scaled x).natAbs := by
      split <;> simp [Int.natAbs_neg]
    rw [this, ← hB]
    exact Nat.le_trans (Nat.mul_le_mul_right _ hx) (le_mul_ceilDiv hn0)
  have hfin : ∀ {x : Int}, (scaled x).natAbs ≤ Mx →
      IsFin (ofExactDiv ((if scaled c < 0 then -scaled x else scaled x) * (unitK : Int)) n) :=
    fun hx => ofExactDiv_fin hn0 (Nat.le_trans (hNB hx) (Nat.mul_le_mul_left _ hbig))
  have r := round_pair hn0 (hfin ma) (hfin mb)
  have u₁ := ulpDiv_le_of_mean (hNB ma)
  have u₂ := ulpDiv_le_of_mean (hNB mb)
  have hD : 2 * ((if scaled c < 0 then -scaled a else scaled a) * (unitK : Int) -
      (if scaled c < 0 then -scaled b else scaled b) * (unitK : Int)).natAbs ≤ unitK * (e + 1) := by
    rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have : ((if scaled c < 0 then -scaled a else scaled a) - (if scaled c < 0 then -scaled b else scaled b)).natAbs =
        (scaled a - scaled b).natAbs := by
      split
      · rw [show -scaled a - -scaled b = -(scaled a - scaled b) by omega, Int.natAbs_neg]
      · rfl
    rw [this, Nat.mul_comm unitK (e + 1), ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right unitK (by have := scaled_sub_le a b; omega)
  have hq : (2 * ((if scaled c < 0 then -scaled a else scaled a) * (unitK : Int) -
      (if scaled c < 0 then -scaled b else scaled b) * (unitK : Int)).natAbs + n - 1) / n ≤
      (unitK * (e + 1) + n - 1) / n := Nat.div_le_div_right (by omega)
  omega

/-- Every code within `e` of `[lo, hi]` has one sign and magnitude at least
`m > 0`: a divisor's range clear of zero (#929 row 5). -/
def ClearOfZero (lo hi : Int) (e m : Nat) : Prop :=
  0 < m ∧ ((m : Int) ≤ scaled (lo - e) ∨ scaled (hi + e) ≤ -(m : Int))

/-- `m`, when the range is clear of zero. -/
def clearOfZero? (lo hi : Int) (e : Nat) : Option Nat :=
  if 0 < scaled (lo - e) then some (scaled (lo - e)).toNat
  else if scaled (hi + e) < 0 then some (-scaled (hi + e)).toNat
  else none

theorem clearOfZero?_sound {lo hi : Int} {e m : Nat} (h : clearOfZero? lo hi e = some m) :
    ClearOfZero lo hi e m := by
  unfold clearOfZero? at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; refine ⟨by omega, .inl (by omega)⟩
  split at h
  · simp only [Option.some.injEq] at h; subst h; refine ⟨by omega, .inr (by omega)⟩
  · cases h

/-- Two codes in a range clear of zero: the same sign, magnitudes at least `m`. -/
theorem ClearOfZero.pair {lo hi : Int} {e m : Nat} (hz : ClearOfZero lo hi e m) {a b : Int}
    (ha₁ : lo - e ≤ a) (ha₂ : a ≤ hi + e) (hb₁ : lo - e ≤ b) (hb₂ : b ≤ hi + e) :
    (0 < scaled a ∧ 0 < scaled b ∨ scaled a < 0 ∧ scaled b < 0) ∧
      m ≤ (scaled a).natAbs ∧ m ≤ (scaled b).natAbs := by
  obtain ⟨hm, h | h⟩ := hz
  · have := scaled_mono ha₁; have := scaled_mono hb₁; omega
  · have := scaled_mono ha₂; have := scaled_mono hb₂; omega

/-- **Two roundings by different divisors**: `ofExactDiv N₁ n₁` and
`ofExactDiv N₂ n₂` within the distance of `N₁ / n₁` and `N₂ / n₂`, both
ulps and the codes' slack. `round_pair` is the case `n₁ = n₂`. -/
theorem round_pair₂ {N₁ N₂ : Int} {n₁ n₂ : Nat} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (f₁ : IsFin (ofExactDiv N₁ n₁)) (f₂ : IsFin (ofExactDiv N₂ n₂)) :
    (ofExactDiv N₁ n₁ - ofExactDiv N₂ n₂).natAbs ≤
      4 + ulpDiv N₁ n₁ + ulpDiv N₂ n₂ +
        (2 * ((n₂ : Int) * N₁ - (n₁ : Int) * N₂).natAbs + n₁ * n₂ - 1) / (n₁ * n₂) := by
  have w₁ := ofExactDiv_within h₁ f₁
  have w₂ := ofExactDiv_within h₂ f₂
  have c₁ := code_sub_scaled (ofExactDiv N₁ n₁)
  have c₂ := code_sub_scaled (ofExactDiv N₂ n₂)
  generalize ofExactDiv N₁ n₁ = r₁ at *
  generalize ofExactDiv N₂ n₂ = r₂ at *
  generalize ulpDiv N₁ n₁ = u₁ at *
  generalize ulpDiv N₂ n₂ = u₂ at *
  generalize scaled r₁ = s₁ at *
  generalize scaled r₂ = s₂ at *
  have key : (n₂ : Int) * ((n₁ : Int) * s₁ - N₁) - (n₁ : Int) * ((n₂ : Int) * s₂ - N₂) +
      ((n₂ : Int) * N₁ - (n₁ : Int) * N₂) = ((n₁ * n₂ : Nat) : Int) * (s₁ - s₂) := by
    simp only [Int.mul_sub, Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm (n₂ : Int) (n₁ : Int)]
    omega
  have t := Int.natAbs_add_le ((n₂ : Int) * ((n₁ : Int) * s₁ - N₁) - (n₁ : Int) * ((n₂ : Int) * s₂ - N₂))
    ((n₂ : Int) * N₁ - (n₁ : Int) * N₂)
  have t' := Int.natAbs_sub_le ((n₂ : Int) * ((n₁ : Int) * s₁ - N₁)) ((n₁ : Int) * ((n₂ : Int) * s₂ - N₂))
  rw [key, Int.natAbs_mul, Int.natAbs_natCast] at t
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at t'
  generalize ((n₁ : Int) * s₁ - N₁).natAbs = E₁ at *
  generalize ((n₂ : Int) * s₂ - N₂).natAbs = E₂ at *
  generalize ((n₂ : Int) * N₁ - (n₁ : Int) * N₂).natAbs = D at *
  have k₁ := Nat.mul_le_mul_left n₂ w₁
  have k₂ := Nat.mul_le_mul_left n₁ w₂
  have hP : 0 < n₁ * n₂ := Nat.mul_pos h₁ h₂
  -- `2 · n₁n₂ · |s₁ - s₂| ≤ n₁n₂ (u₁ + u₂) + 2 D`.
  have e₁ : n₂ * (n₁ * u₁) = (n₁ * n₂) * u₁ := by rw [Nat.mul_left_comm, Nat.mul_assoc]
  have e₂ : n₁ * (n₂ * u₂) = (n₁ * n₂) * u₂ := by rw [Nat.mul_assoc]
  have e₃ : n₂ * (2 * E₁) = 2 * (n₂ * E₁) := Nat.mul_left_comm _ _ _
  have e₄ : n₁ * (2 * E₂) = 2 * (n₁ * E₂) := Nat.mul_left_comm _ _ _
  rw [e₁, e₃] at k₁; rw [e₂, e₄] at k₂
  generalize n₁ * n₂ = P at *
  have hA : (2 * (s₁ - s₂).natAbs - (u₁ + u₂)) * P ≤ 2 * D + P - 1 := by
    rw [Nat.sub_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (s₁ - s₂).natAbs P,
      Nat.mul_comm u₁ P, Nat.mul_comm u₂ P]
    generalize P * (s₁ - s₂).natAbs = X at *
    generalize n₂ * E₁ = Y₁ at *
    generalize n₁ * E₂ = Y₂ at *
    omega
  have := (Nat.le_div_iff_mul_le hP).2 hA
  have e : r₁ - r₂ = (r₁ - 2 * s₁) + 2 * (s₁ - s₂) + (2 * s₂ - r₂) := by omega
  have hc₂ : (2 * s₂ - r₂).natAbs = (r₂ - 2 * s₂).natAbs := by rw [← Int.natAbs_neg, Int.neg_sub]
  have t2 := natAbs_add3_le (r₁ - 2 * s₁) (2 * (s₁ - s₂)) (2 * s₂ - r₂)
  rw [← e, Int.natAbs_mul, hc₂] at t2
  have : (2 : Int).natAbs = 2 := rfl
  rw [this] at t2
  omega

/-- `⌈X / P⌉ ≤ c` when `X ≤ P c`. -/
theorem ceilDiv_le_of {X P c : Nat} (hP : 0 < P) (h : X ≤ P * c) : (X + P - 1) / P ≤ c := by
  have : (X + P - 1) / P < c + 1 := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.succ_mul, Nat.mul_comm c P]; omega
  omega

set_option exponentiation.threshold 3200 in
/-- **`x / y`** with `y`'s range clear of zero (`ClearOfZero`): the exact
quotients' distance over `n₁ n₂ ≥ m²`, then both roundings. `Mx`, `My` are the
reference ranges' magnitudes, `Mx + ex` the engine's `x`'s. -/
theorem fdiv_near {ex ey Mx My m : Nat} {lo hi a₁ a₂ b₁ b₂ : Int} (f₁ : IsFin a₁) (f₂ : IsFin a₂)
    (g₁ : IsFin b₁) (g₂ : IsFin b₂) (h₁ : (a₁ - b₁).natAbs ≤ ex) (h₂ : (a₂ - b₂).natAbs ≤ ey)
    (ma₁ : (scaled a₁).natAbs ≤ Mx + ex) (mb₁ : (scaled b₁).natAbs ≤ Mx) (mb₂ : (scaled b₂).natAbs ≤ My)
    (hz : ClearOfZero lo hi ey m) (ha₂ : lo - ey ≤ a₂ ∧ a₂ ≤ hi + ey) (hb₂ : lo ≤ b₂ ∧ b₂ ≤ hi)
    (hbig : ((Mx + ex) * unitK + m - 1) / m ≤ 2 ^ 2097) :
    (fdiv a₁ a₂ - fdiv b₁ b₂).natAbs ≤
      4 + 2 * ulpDiv ((((Mx + ex) * unitK + m - 1) / m : Nat) : Int) 1 +
        (unitK * (My * (ex + 1) + Mx * (ey + 1)) + m * m - 1) / (m * m) := by
  obtain ⟨hsign, hma, hmb⟩ := hz.pair (a := a₂) (b := b₂) ha₂.1 ha₂.2 (by have := hb₂.1; omega)
    (by have := hb₂.2; omega)
  have hm : 0 < m := hz.1
  have ha0 : scaled a₂ ≠ 0 := by omega
  have hb0 : scaled b₂ ≠ 0 := by omega
  rw [fdiv_fin f₁ f₂ ha0, fdiv_fin g₁ g₂ hb0]
  generalize hB : ((Mx + ex) * unitK + m - 1) / m = B at *
  have hK : 0 < unitK := Nat.two_pow_pos _
  -- Numerators and divisors.
  have hnum : ∀ {x y : Int} {M : Nat}, (scaled x).natAbs ≤ M → M ≤ Mx + ex → m ≤ (scaled y).natAbs →
      ((if scaled y < 0 then -scaled x else scaled x) * (unitK : Int)).natAbs ≤ (scaled y).natAbs * B := by
    intro x y M hx hM hy
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have : (if scaled y < 0 then -scaled x else scaled x).natAbs = (scaled x).natAbs := by
      split <;> simp [Int.natAbs_neg]
    rw [this, ← hB]
    refine Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_trans hx hM)) ?_
    exact Nat.le_trans (le_mul_ceilDiv hm) (Nat.mul_le_mul_right _ hy)
  have hfin : ∀ {x y : Int} {M : Nat}, (scaled x).natAbs ≤ M → M ≤ Mx + ex → m ≤ (scaled y).natAbs →
      IsFin (ofExactDiv ((if scaled y < 0 then -scaled x else scaled x) * (unitK : Int)) (scaled y).natAbs) :=
    fun hx hM hy => ofExactDiv_fin (by omega) (Nat.le_trans (hnum hx hM hy) (Nat.mul_le_mul_left _ hbig))
  have r := round_pair₂ (by omega) (by omega) (hfin ma₁ (Nat.le_refl _) hma) (hfin mb₁ (by omega) hmb)
  have u₁ := ulpDiv_le_of_mean (hnum ma₁ (Nat.le_refl _) hma)
  have u₂ := ulpDiv_le_of_mean (hnum mb₁ (by omega) hmb)
  -- The cross term: `|n₂ N₁ - n₁ N₂| = K |sa₁ sb₂ - sb₁ sa₂|`.
  have hcross : (((scaled b₂).natAbs : Int) * ((if scaled a₂ < 0 then -scaled a₁ else scaled a₁) * (unitK : Int)) -
      ((scaled a₂).natAbs : Int) * ((if scaled b₂ < 0 then -scaled b₁ else scaled b₁) * (unitK : Int))).natAbs =
      unitK * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂).natAbs := by
    rcases hsign with ⟨pa, pb⟩ | ⟨na, nb⟩
    · rw [Int.natAbs_of_nonneg (by omega : (0 : Int) ≤ scaled b₂),
        Int.natAbs_of_nonneg (by omega : (0 : Int) ≤ scaled a₂)]
      have q₁ : ¬ scaled a₂ < 0 := by omega
      have q₂ : ¬ scaled b₂ < 0 := by omega
      simp only [q₁, q₂, ite_false]
      rw [show scaled b₂ * (scaled a₁ * (unitK : Int)) - scaled a₂ * (scaled b₁ * (unitK : Int)) =
          (unitK : Int) * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂) by
        simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]]
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    · rw [Int.ofNat_natAbs_of_nonpos (by omega : scaled b₂ ≤ 0),
        Int.ofNat_natAbs_of_nonpos (by omega : scaled a₂ ≤ 0)]
      simp only [na, nb, ite_true]
      rw [show -scaled b₂ * (-scaled a₁ * (unitK : Int)) - -scaled a₂ * (-scaled b₁ * (unitK : Int)) =
          (unitK : Int) * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂) by
        simp only [Int.mul_sub, Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_assoc, Int.mul_comm,
          Int.mul_left_comm]]
      rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [hcross] at r
  -- `2 |sa₁ sb₂ - sb₁ sa₂| ≤ My (ex + 1) + Mx (ey + 1)`.
  have hD : 2 * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂).natAbs ≤ My * (ex + 1) + Mx * (ey + 1) := by
    have e : scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂ =
        scaled b₂ * (scaled a₁ - scaled b₁) - scaled b₁ * (scaled a₂ - scaled b₂) := by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_comm (scaled b₂) (scaled a₁),
        Int.mul_comm (scaled b₂) (scaled b₁)]; omega
    rw [e]
    have t := Int.natAbs_sub_le (scaled b₂ * (scaled a₁ - scaled b₁)) (scaled b₁ * (scaled a₂ - scaled b₂))
    rw [Int.natAbs_mul, Int.natAbs_mul] at t
    have s₁ := scaled_sub_le a₁ b₁
    have s₂ := scaled_sub_le a₂ b₂
    have k₁ : (scaled b₂).natAbs * (2 * (scaled a₁ - scaled b₁).natAbs) ≤ My * (ex + 1) :=
      Nat.mul_le_mul mb₂ (by omega)
    have k₂ : (scaled b₁).natAbs * (2 * (scaled a₂ - scaled b₂).natAbs) ≤ Mx * (ey + 1) :=
      Nat.mul_le_mul mb₁ (by omega)
    rw [Nat.mul_left_comm] at k₁ k₂
    omega
  -- The divisors' product is at least `m²`.
  have hP : m * m ≤ (scaled a₂).natAbs * (scaled b₂).natAbs := Nat.mul_le_mul hma hmb
  have hq : (2 * (unitK * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂).natAbs) +
      (scaled a₂).natAbs * (scaled b₂).natAbs - 1) / ((scaled a₂).natAbs * (scaled b₂).natAbs) ≤
      (unitK * (My * (ex + 1) + Mx * (ey + 1)) + m * m - 1) / (m * m) := by
    apply ceilDiv_le_of (Nat.mul_pos (by omega) (by omega))
    have hc := le_mul_ceilDiv (a := unitK * (My * (ex + 1) + Mx * (ey + 1))) (Nat.mul_pos hm hm)
    have h2 : 2 * (unitK * (scaled a₁ * scaled b₂ - scaled b₁ * scaled a₂).natAbs) ≤
        unitK * (My * (ex + 1) + Mx * (ey + 1)) := by
      rw [Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ hD
    exact Nat.le_trans h2 (Nat.le_trans hc (Nat.mul_le_mul_right _ hP))
  omega

set_option exponentiation.threshold 3200 in
/-- **The arithmetic rows' bounds**: `x ± y`, `x · y` (`c · x` with a literal
operand) and `x / c`, of operands `Expr.atom?` takes. `M` is an operand's
magnitude bound: its range's, plus its tolerance. -/
def Expr.arithTol (t : Tol) (mask : Nat → Bool) (env : List AVal) : Expr → Option Nat
  | .bin f x y =>
    match x.atom? t mask env, y.atom? t mask env with
    | some (ex, lx, hx), some (ey, ly, hy) =>
      let Mx := magOf lx hx + ex
      let My := magOf ly hy + ey
      match f with
      | .fadd | .fsub =>
        if Mx + My ≤ 2 ^ 2097 then some (2 * (max ex ey + 1) + 2 * ulpDiv ((Mx + My : Nat) : Int) 1 + 4)
        else none
      | .fmul =>
        if Mx * My ≤ 2 ^ 3171 then
          some (4 + 2 * ulpDiv ((Mx * My : Nat) : Int) unitK + (Mx * (ey + 1) + My * (ex + 1) + unitK - 1) / unitK)
        else none
      | .fdiv =>
        match y with
        | .lit (.float c) =>
          let n := (scaled c).natAbs
          if scaled c ≠ 0 ∧ (Mx * unitK + n - 1) / n ≤ 2 ^ 2097 then
            some (4 + 2 * ulpDiv (((Mx * unitK + n - 1) / n : Nat) : Int) 1 + (unitK * (ex + 1) + n - 1) / n)
          else none
        | _ =>
          -- `x / y` of a divisor clear of zero (#929 row 5).
          match clearOfZero? ly hy ey with
          | some m =>
            if (Mx * unitK + m - 1) / m ≤ 2 ^ 2097 then
              some (4 + 2 * ulpDiv (((Mx * unitK + m - 1) / m : Nat) : Int) 1 +
                (unitK * (magOf ly hy * (ex + 1) + magOf lx hx * (ey + 1)) + m * m - 1) / (m * m))
            else none
          | none => none
      | _ => none
    | _, _ => none
  | _ => none

theorem binFloat_null_l (f : BinFn) (hf : f = .fadd ∨ f = .fsub ∨ f = .fmul ∨ f = .fdiv) (v : Value) :
    BinFn.apply f .null v = .null := by
  rcases hf with rfl | rfl | rfl | rfl <;> cases v <;> rfl

theorem binFloat_null_r (f : BinFn) (hf : f = .fadd ∨ f = .fsub ∨ f = .fmul ∨ f = .fdiv) (v : Value) :
    BinFn.apply f v .null = .null := by
  rcases hf with rfl | rfl | rfl | rfl <;> cases v <;> rfl

set_option exponentiation.threshold 3200 in
/-- **The arithmetic rows are sound**: on paired rows, both NULL, or two
reference codes within the row's bound. -/
theorem Expr.arithTol_sound {t : Tol} {mask : Nat → Bool} {env : List AVal} {e : Expr} {B : Nat}
    (h : e.arithTol t mask env = some B) {x y : Row} (r : t.Rows x y)
    (hx : ∀ j c, mask j = true → x.getD j .null = .float c → IsRef c) (hy : EnvMem env y) :
    (e.eval x = .null ∧ e.eval y = .null) ∨
      ∃ a b, e.eval x = .float a ∧ e.eval y = .float b ∧ (a - b).natAbs ≤ B ∧ IsRef a ∧ IsRef b := by
  cases e with
  | bin f x' y' =>
    simp only [Expr.arithTol] at h
    cases hax : x'.atom? t mask env with
    | none => simp [hax] at h
    | some ax =>
    cases hay : y'.atom? t mask env with
    | none => simp [hax, hay] at h
    | some ay =>
    obtain ⟨ex, lx, hx'⟩ := ax
    obtain ⟨ey, ly, hy'⟩ := ay
    simp only [hax, hay] at h
    have hf : f = .fadd ∨ f = .fsub ∨ f = .fmul ∨ f = .fdiv := by
      cases f <;> simp_all
    simp only [Expr.eval]
    rcases Expr.atom?_sound hax r hx hy with ⟨n₁, n₁'⟩ | ⟨a₁, b₁, ea₁, eb₁, d₁, l₁, u₁, fa₁, fb₁⟩
    · left; rw [n₁, n₁', binFloat_null_l f hf, binFloat_null_l f hf]; exact ⟨rfl, rfl⟩
    rcases Expr.atom?_sound hay r hx hy with ⟨n₂, n₂'⟩ | ⟨a₂, b₂, ea₂, eb₂, d₂, l₂, u₂, fa₂, fb₂⟩
    · left; rw [n₂, n₂', binFloat_null_r f hf, binFloat_null_r f hf]; exact ⟨rfl, rfl⟩
    right
    rw [ea₁, eb₁, ea₂, eb₂]
    obtain ⟨ma₁, mb₁⟩ := atom_mag d₁ l₁ u₁
    obtain ⟨ma₂, mb₂⟩ := atom_mag d₂ l₂ u₂
    rcases hf with rfl | rfl | rfl | rfl
    · simp only at h; split at h
      · rename_i hbig
        simp only [Option.some.injEq] at h; subst h
        refine ⟨_, _, rfl, rfl, fadd_near fa₁ fa₂ fb₁ fb₂ (Nat.le_trans d₁ (Nat.le_max_left _ _))
          (Nat.le_trans d₂ (Nat.le_max_right _ _)) (by omega) (by omega) hbig, fadd_isRef _ _,
          fadd_isRef _ _⟩
      · cases h
    · simp only at h; split at h
      · rename_i hbig
        simp only [Option.some.injEq] at h; subst h
        refine ⟨_, _, rfl, rfl, ?_, fsub_isRef _ _, fsub_isRef _ _⟩
        rw [fsub_eq_fadd fa₁ fa₂, fsub_eq_fadd fb₁ fb₂]
        have : (-a₂ - -b₂).natAbs = (a₂ - b₂).natAbs := by
          rw [show -a₂ - -b₂ = -(a₂ - b₂) by omega, Int.natAbs_neg]
        refine fadd_near fa₁ (IsFin.neg fa₂) fb₁ (IsFin.neg fb₂)
          (Nat.le_trans d₁ (Nat.le_max_left _ _)) (by rw [this]; exact Nat.le_trans d₂ (Nat.le_max_right _ _))
          ?_ ?_ hbig
        · rw [scaled_neg', Int.natAbs_neg]; omega
        · rw [scaled_neg', Int.natAbs_neg]; omega
      · cases h
    · simp only at h; split at h
      · rename_i hbig
        simp only [Option.some.injEq] at h; subst h
        exact ⟨_, _, rfl, rfl, fmul_near fa₁ fa₂ fb₁ fb₂ d₁ d₂ ma₁ ma₂ (by omega) (by omega) hbig,
          fmul_isRef _ _, fmul_isRef _ _⟩
      · cases h
    · simp only at h
      cases y' with
      | lit v =>
        cases v with
        | float c =>
          simp only at h
          split at h
          · rename_i hc
            simp only [Option.some.injEq] at h; subst h
            -- The literal is the same on both sides.
            simp only [Expr.eval] at ea₂ eb₂
            cases ea₂; cases eb₂
            exact ⟨_, _, rfl, rfl, fdiv_lit_near fa₁ fb₁ fa₂ hc.1 d₁ ma₁ (by omega) hc.2,
              fdiv_isRef _ _, fdiv_isRef _ _⟩
          · cases h
        | _ => simp [Expr.atom?] at hay
      | _ =>
        all_goals
          simp only at h
          cases hcz : clearOfZero? ly hy' ey with
          | none => simp [hcz] at h
          | some m =>
            simp only [hcz] at h
            split at h
            · rename_i hbig
              simp only [Option.some.injEq] at h; subst h
              exact ⟨_, _, rfl, rfl, fdiv_near fa₁ fa₂ fb₁ fb₂ d₁ d₂ ma₁ mb₁ mb₂ (clearOfZero?_sound hcz)
                ⟨by omega, by omega⟩ ⟨l₂, u₂⟩ hbig, fdiv_isRef _ _, fdiv_isRef _ _⟩
            · cases h
  | _ => simp [Expr.arithTol] at h

/-- **An expression's tolerance**: `Expr.tol?`'s, or an arithmetic row's. -/
def Expr.tolA (t : Tol) (mask : Nat → Bool) (env : List AVal) (e : Expr) : Option (Option Nat) :=
  (e.tol? t).or ((e.arithTol t mask env).map some)

theorem Expr.tolA_sound {t : Tol} {mask : Nat → Bool} {env : List AVal} {e : Expr}
    {o : Option Nat} (he : e.tolA t mask env = some o) {x y : Row} (h : t.Rows x y)
    (hx : ∀ j c, mask j = true → x.getD j .null = .float c → IsRef c) (hy : EnvMem env y)
    {t' : Tol} {j : Nat} (ho : OLe o (t' j)) : t'.Cell j (e.eval x) (e.eval y) := by
  unfold Expr.tolA at he
  cases h1 : e.tol? t with
  | some o' =>
    rw [h1] at he; simp only [Option.some_or, Option.some.injEq] at he; subst he
    exact Expr.tol?_sound h1 h ho
  | none =>
    rw [h1] at he; simp only [Option.none_or, Option.map_eq_some_iff] at he
    obtain ⟨B, hB, rfl⟩ := he
    cases htj : t' j with
    | none => rw [htj] at ho; exact ho.elim
    | some B' =>
      rw [htj] at ho
      rcases Expr.arithTol_sound hB h hx hy with ⟨n, n'⟩ | ⟨a, b, ea, eb, d, ra, rb⟩
      · rw [n, n']; exact Tol.cell_null _ _
      · rw [ea, eb]
        refine Tol.cell_float htj ?_
        rw [show fp64.canon a = a from canon_of_isRef ra, show fp64.canon b = b from canon_of_isRef rb]
        exact Nat.le_trans d ho

/-- The tolerances of a projection's expressions. -/
def Tol.exprsA (t : Tol) (mask : Nat → Bool) (env : List AVal) (es : List Expr) : Tol := fun k =>
  match es[k]? with
  | some e => (e.tolA t mask env).getD none
  | none => none

theorem Tol.rows_exprsA {t : Tol} {mask : Nat → Bool} {env : List AVal} {es : List Expr}
    (hes : es.all (fun e => (e.tolA t mask env).isSome) = true) {x y : Row} (h : t.Rows x y)
    (hx : ∀ j c, mask j = true → x.getD j .null = .float c → IsRef c) (hy : EnvMem env y) :
    (Tol.exprsA t mask env es).Rows (es.map (·.eval x)) (es.map (·.eval y)) := by
  refine ⟨by simp, fun k => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hk : es[k]? with
  | none => exact Tol.cell_null _ _
  | some e =>
    simp only [Option.map_some, Option.getD_some]
    have hs := List.all_eq_true.1 hes e (List.mem_of_getElem? hk)
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hs
    exact Expr.tolA_sound ho h hx hy (by simp [Tol.exprsA, hk, ho, OLe.refl])

/-! ### The `MIN` and `MAX` rows (#929 step 2)

`MIN` and `MAX` pick one of their values by code (`Value.leScalar`): with
the values paired within `e` codes, the picks are within `e` codes, the
table's `M∞ = 1` with no rounding. Codes order doubles as their values only
where they are the reference's (`IsRef`; `-0.0`'s code lies below `-∞`'s):
the engine's column is one of `Rel.refCols`, and the analysis gives the
reference's column doubles only, in a range of reference codes. -/

/-- **A `MIN`'s or `MAX`'s output tolerance**, its input within `t`: the
argument's, for a tolerated column of doubles in reference codes. -/
def Measure.minMaxOut (t : Tol) (mask : Nat → Bool) (env : List AVal) (m : Measure) :
    Option (Option Nat) :=
  match m.fn, m.arg with
  | .min, .field i | .max, .field i =>
    match t i, colRange env i with
    | some e, some (lo, hi) =>
      if !m.distinct && (m.filter.all fun c => t.exactOn c.cols) && mask i &&
          (env.getD i AVal.top).kindOnly .float && decide (negInf ≤ lo) && decide (hi ≤ nan) then
        some (some e)
      else none
    | _, _ => none
  | _, _ => none

/-- A measure's output tolerance: `SUM`, `AVG`, or `MIN` and `MAX`. -/
def Measure.outTol (t : Tol) (mask : Nat → Bool) (env : List AVal) (N : Option Nat)
    (m : Measure) : Option (Option Nat) :=
  (m.tolOut t mask env N).or (m.minMaxOut t mask env)

theorem foldl_min_near {e : Nat} :
    ∀ {a b : Int} {xs ys : List Int}, (a - b).natAbs ≤ e →
      Forall2 (fun x y => (x - y).natAbs ≤ e) xs ys → (xs.foldl min a - ys.foldl min b).natAbs ≤ e
  | _, _, [], [], h, .nil => h
  | a, b, x :: _, y :: _, h, .cons hxy t => by
    simp only [List.foldl_cons]
    refine foldl_min_near ?_ t
    rw [Int.min_def, Int.min_def]; split <;> split <;> omega

theorem foldl_max_near {e : Nat} :
    ∀ {a b : Int} {xs ys : List Int}, (a - b).natAbs ≤ e →
      Forall2 (fun x y => (x - y).natAbs ≤ e) xs ys → (xs.foldl max a - ys.foldl max b).natAbs ≤ e
  | _, _, [], [], h, .nil => h
  | a, b, x :: _, y :: _, h, .cons hxy t => by
    simp only [List.foldl_cons]
    refine foldl_max_near ?_ t
    rw [Int.max_def, Int.max_def]; split <;> split <;> omega

theorem foldl_min_bounds {L U : Int} : ∀ {a : Int} {xs : List Int}, L ≤ a → a ≤ U →
    (∀ x ∈ xs, L ≤ x ∧ x ≤ U) → L ≤ xs.foldl min a ∧ xs.foldl min a ≤ U
  | _, [], h1, h2, _ => ⟨h1, h2⟩
  | a, x :: xs, h1, h2, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    exact foldl_min_bounds (by rw [Int.min_def]; split <;> omega) (by rw [Int.min_def]; split <;> omega)
      fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem foldl_max_bounds {L U : Int} : ∀ {a : Int} {xs : List Int}, L ≤ a → a ≤ U →
    (∀ x ∈ xs, L ≤ x ∧ x ≤ U) → L ≤ xs.foldl max a ∧ xs.foldl max a ≤ U
  | _, [], h1, h2, _ => ⟨h1, h2⟩
  | a, x :: xs, h1, h2, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    exact foldl_max_bounds (by rw [Int.max_def]; split <;> omega) (by rw [Int.max_def]; split <;> omega)
      fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem pickFold_min_float (x : Int) :
    ∀ cs : List Int, pickFold (fun a b => !a.le b) (.float x) (cs.map .float) = .float (cs.foldl min x)
  | [] => rfl
  | c :: cs => by
    have : pickFold (fun a b => !a.le b) (.float x) ((c :: cs).map .float) =
        pickFold (fun a b => !a.le b) (.float (min x c)) (cs.map .float) := by
      simp only [pickFold, List.map_cons, List.foldl_cons, Value.le_def, Value.leScalar]
      congr 1
      rw [Int.min_def]; by_cases h : x ≤ c <;> simp [h]
    rw [this, pickFold_min_float (min x c) cs, List.foldl_cons]

theorem pickFold_max_float (x : Int) :
    ∀ cs : List Int, pickFold (fun a b => !b.le a) (.float x) (cs.map .float) = .float (cs.foldl max x)
  | [] => rfl
  | c :: cs => by
    have : pickFold (fun a b => !b.le a) (.float x) ((c :: cs).map .float) =
        pickFold (fun a b => !b.le a) (.float (max x c)) (cs.map .float) := by
      simp only [pickFold, List.map_cons, List.foldl_cons, Value.le_def, Value.leScalar]
      congr 1
      rw [Int.max_def]; by_cases h : c ≤ x <;> by_cases h' : x ≤ c <;> simp [h, h'] <;> omega
    rw [this, pickFold_max_float (max x c) cs, List.foldl_cons]

/-- Values paired as doubles within `e` codes: two lists of codes. -/
theorem Forall2.floats {e : Nat} {lo hi : Int} :
    ∀ {vs ws : List Value}, Forall2 (fun v w => ∃ a b, v = .float a ∧ w = .float b ∧
      (a - b).natAbs ≤ e ∧ IsRef a ∧ lo ≤ b ∧ b ≤ hi) vs ws →
      ∃ as bs, vs = as.map .float ∧ ws = bs.map .float ∧
        Forall2 (fun x y => (x - y).natAbs ≤ e) as bs ∧ (∀ a ∈ as, IsRef a) ∧ ∀ b ∈ bs, lo ≤ b ∧ b ≤ hi
  | [], [], .nil => ⟨[], [], rfl, rfl, .nil, by simp, by simp⟩
  | _, _, .cons ⟨a, b, rfl, rfl, h, ra, hb1, hb2⟩ t => by
    obtain ⟨as, bs, rfl, rfl, f, has, hbs⟩ := Forall2.floats t
    refine ⟨a :: as, b :: bs, rfl, rfl, .cons h f, fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ra
      · exact has x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hb1, hb2⟩
      · exact hbs x hx

theorem Measure.minMaxOut_cell {t : Tol} {mask : Nat → Bool} {env : List AVal} {m : Measure}
    {o : Option Nat} (h : m.minMaxOut t mask env = some o) {g g' : Relation}
    (f : Forall2 t.Rows g g') (henv : ∀ row ∈ g', EnvMem env row) (hR : Relation.RefOn mask g)
    {tm : Tol} {j : Nat} (hj : tm j = o) : tm.Cell j (m.eval g) (m.eval g') := by
  unfold Measure.minMaxOut at h
  -- The shape: `MIN` or `MAX` of `field i`.
  obtain ⟨i, hfn, harg⟩ : ∃ i, (m.fn = .min ∨ m.fn = .max) ∧ m.arg = .field i := by
    split at h
    · rename_i i hf ha; exact ⟨i, .inl hf, ha⟩
    · rename_i i hf ha; exact ⟨i, .inr hf, ha⟩
    · cases h
  have hs : m.fn.sorts = false := by rcases hfn with hf | hf <;> rw [hf] <;> rfl
  cases hti : t i with
  | none => rcases hfn with hf | hf <;> simp [hf, harg, hti] at h
  | some e =>
  cases hcr : colRange env i with
  | none => rcases hfn with hf | hf <;> simp [hf, harg, hti, hcr] at h
  | some r =>
  obtain ⟨lo, hi⟩ := r
  have hc : (!m.distinct && (m.filter.all fun c => t.exactOn c.cols) && mask i &&
      (env.getD i AVal.top).kindOnly .float && decide (negInf ≤ lo) && decide (hi ≤ nan)) = true ∧
      o = some e := by
    rcases hfn with hf | hf <;> simp only [hf, harg, hti, hcr] at h <;> split at h <;>
      simp_all
  obtain ⟨hc, rfl⟩ := hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hd, hf⟩, hmask⟩, hko⟩, hlo⟩, hhi⟩ := hc
  have ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e) :=
    ⟨some e, by simp [harg, Expr.tol?, hti], by simp [OLe]⟩
  have hcells := Measure.inputs_cells hd hf ha f
  have hP : ∀ v ∈ m.inputs g, ∀ c, v = .float c → IsRef c := by
    intro v hv c hc
    obtain ⟨-, row, hr, rfl⟩ := Measure.mem_inputs hv
    rw [harg] at hc
    exact hR row hr i c hmask hc
  have hQ : ∀ w ∈ m.inputs g', ∃ b, w = .float b ∧ lo ≤ b ∧ b ≤ hi := by
    intro w hw
    obtain ⟨hn, row, hr, rfl⟩ := Measure.mem_inputs hw
    have hm := henv row hr i
    rw [harg]
    obtain ⟨b, bd, hv, hb, hbm⟩ := AVal.kindOnly_mem hko hm (by rw [harg] at hn; exact hn)
    refine ⟨b, hv, ?_⟩
    unfold colRange at hcr
    split at hcr
    · rename_i lo' hi' hint
      simp only [Option.some.injEq, Prod.mk.injEq] at hcr
      obtain ⟨rfl, rfl⟩ := hcr
      rw [hint] at hb; cases hb
      exact ⟨hbm.1 _ rfl, hbm.2 _ rfl⟩
    · cases hcr
  have hpairs := (hcells.and_mem hP hQ).imp (S := fun v w => ∃ a b, v = .float a ∧ w = .float b ∧
      (a - b).natAbs ≤ e ∧ IsRef a ∧ lo ≤ b ∧ b ≤ hi) fun v w hx => by
    obtain ⟨hcell, pv, b, rfl, hb1, hb2⟩ := hx
    cases v with
    | float a =>
      have ra := pv a rfl
      have rb : IsRef b := ⟨(show negInf ≤ b by omega), (show b ≤ nan by omega)⟩
      have hn := Tol.cell_float_iff.1 hcell
      rw [show fp64.canon a = a from canon_of_isRef ra, show fp64.canon b = b from canon_of_isRef rb] at hn
      exact ⟨a, b, rfl, rfl, hn, ra, hb1, hb2⟩
    | _ => exact hcell.elim
  obtain ⟨as, bs, has, hbs, fab, ras, rbs⟩ := Forall2.floats hpairs
  rw [Measure.eval_eq hs, Measure.eval_eq hs, has, hbs]
  have hL : ∀ a ∈ as, negInf ≤ a ∧ a ≤ nan := fun a h => ras a h
  have hL' : ∀ b ∈ bs, negInf ≤ b ∧ b ≤ nan := fun b h => by have := rbs b h; omega
  cases fab with
  | nil => rcases hfn with hf | hf <;> rw [hf] <;> exact Tol.cell_null _ _
  | cons hab fab' =>
    rename_i a b as' bs'
    have ba := hL a (List.mem_cons_self ..)
    have bb := hL' b (List.mem_cons_self ..)
    have hL1 : ∀ x ∈ as', negInf ≤ x ∧ x ≤ nan := fun x h => hL x (List.mem_cons_of_mem _ h)
    have hL2 : ∀ x ∈ bs', negInf ≤ x ∧ x ≤ nan := fun x h => hL' x (List.mem_cons_of_mem _ h)
    rcases hfn with hf | hf <;> rw [hf] <;>
      simp only [List.map_cons, AggFn.apply]
    · rw [pickFold_min_float, pickFold_min_float]
      have r1 := foldl_min_bounds ba.1 ba.2 hL1
      have r2 := foldl_min_bounds bb.1 bb.2 hL2
      refine Tol.cell_float hj ?_
      rw [show fp64.canon (as'.foldl min a) = _ from canon_of_isRef r1,
        show fp64.canon (bs'.foldl min b) = _ from canon_of_isRef r2]
      exact foldl_min_near hab fab'
    · rw [pickFold_max_float, pickFold_max_float]
      have r1 := foldl_max_bounds ba.1 ba.2 hL1
      have r2 := foldl_max_bounds bb.1 bb.2 hL2
      refine Tol.cell_float hj ?_
      rw [show fp64.canon (as'.foldl max a) = _ from canon_of_isRef r1,
        show fp64.canon (bs'.foldl max b) = _ from canon_of_isRef r2]
      exact foldl_max_near hab fab'

theorem Measure.outTol_cell {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {o : Option Nat} (h : m.outTol t mask env N = some o) {g g' : Relation}
    (f : Forall2 t.Rows g g') (henv : ∀ row ∈ g', EnvMem env row)
    (hN : ∀ n, N = some n → g'.length ≤ n) (hR : Relation.RefOn mask g) {tm : Tol} {j : Nat}
    (hj : tm j = o) : tm.Cell j (m.eval g) (m.eval g') := by
  unfold Measure.outTol at h
  cases h1 : m.tolOut t mask env N with
  | some o' =>
    rw [h1] at h; simp only [Option.some_or, Option.some.injEq] at h; subst h
    exact Measure.tolOut_cell h1 f henv hN hj
  | none =>
    rw [h1] at h; simp only [Option.none_or] at h
    exact Measure.minMaxOut_cell h f henv hR hj

theorem Measure.outTol_orderFree {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {o : Option Nat} (h : m.outTol t mask env N = some o) : m.orderFree = true := by
  unfold Measure.outTol at h
  cases h1 : m.tolOut t mask env N with
  | some o' => exact Measure.tolOut_orderFree h1
  | none =>
    rw [h1] at h; simp only [Option.none_or] at h
    unfold Measure.minMaxOut at h
    unfold Measure.orderFree
    split at h
    · rename_i hf _; rw [hf]; rfl
    · rename_i hf _; rw [hf]; rfl
    · cases h

theorem measures_rows {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {ms : List Measure} (hos : (ms.map (·.outTol t mask env N)).all Option.isSome = true)
    {g g' : Relation} (f : Forall2 t.Rows g g') (henv : ∀ row ∈ g', EnvMem env row)
    (hN : ∀ n, N = some n → g'.length ≤ n) (hR : Relation.RefOn mask g) :
    (Tol.ofOuts (ms.map (·.outTol t mask env N))).Rows (ms.map (·.eval g)) (ms.map (·.eval g')) := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hj : ms[j]? with
  | none => exact Tol.cell_null _ _
  | some m =>
    simp only [Option.map_some, Option.getD_some]
    have hm : m ∈ ms := List.mem_of_getElem? hj
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1
      (List.all_eq_true.1 hos _ (List.mem_map_of_mem (f := (·.outTol t mask env N)) hm))
    exact Measure.outTol_cell ho f henv hN hR
      (by simp [Tol.ofOuts, List.getD_eq_getElem?_getD, List.getElem?_map, hj, ho])

/-- **`GROUP BY` on exact keys with measures the fold bounds**: the groups
pair up, and each output row is within the measures' tolerances. -/
theorem aggregateEval_near {t : Tol} {gs : List Expr} {ms : List Measure} {mask : Nat → Bool}
    {env : List AVal} {N : Option Nat} (hg : gs.all (fun g => t.exactOn g.cols) = true)
    (hos : (ms.map (·.outTol t mask env N)).all Option.isSome = true) {a p : Relation}
    (f : Forall2 t.Rows a p) (henv : ∀ row ∈ p, EnvMem env row)
    (hN : ∀ n, N = some n → p.length ≤ n) (hR : Relation.RefOn mask a) :
    Forall2 (Tol.cat gs.length Tol.exact (Tol.ofOuts (ms.map (·.outTol t mask env N)))).Rows
      (aggregateEval gs ms a) (aggregateEval gs ms p) := by
  have hkey : ∀ x y, t.Rows x y → groupKey gs x = groupKey gs y := fun x y r =>
    List.map_congr_left fun g hg' => Expr.eval_rows (List.all_eq_true.1 hg g hg') r
  unfold aggregateEval
  split
  · rename_i he
    have h0 : gs.length = 0 := by simpa using he
    refine .cons ?_ .nil
    have := Tol.rows_append (n := 0) (t := Tol.exact) (x := []) (x' := []) (Tol.rows_refl _ _)
      (measures_rows hos f henv hN hR) rfl
    rw [h0]; simpa using this
  · rw [f.map_eq hkey]
    have hl : Forall2 (fun k k' => k = k' ∧ k ∈ dedup (p.map (groupKey gs)))
        (dedup (p.map (groupKey gs))) (dedup (p.map (groupKey gs))) := Forall2.refl fun k hk => ⟨rfl, hk⟩
    refine hl.map fun k k' ⟨hkk, hk⟩ => ?_
    subst hkk
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 (mem_dedup.1 hk)
    have fg : Forall2 t.Rows (groupRows gs a (groupKey gs y)) (groupRows gs p (groupKey gs y)) :=
      f.filter fun x y' r => by rw [hkey x y' r]
    refine Tol.rows_append (Tol.rows_refl _ _) (measures_rows hos fg ?_ ?_ ?_) (by simp [groupKey])
    · exact fun row h => henv row (List.mem_filter.1 h).1
    · exact fun n hn => Nat.le_trans (List.length_filter_le _ _) (hN n hn)
    · exact hR.mono fun row h => (List.mem_filter.1 h).1

/-- The engine's catalog is well-formed when its tables are within a
tolerance of the reference's well-formed ones, with the same arities. -/
theorem Catalog.wf_of_near {cat cat' : Catalog} (hcat : cat.WF)
    (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearT (T s) (cat' s).rows (cat s).rows) : cat'.WF := fun s row hr => by
  obtain ⟨p, fp, hp⟩ := hT s
  obtain ⟨y, hy, rxy⟩ := fp.mem_left hr
  rw [rxy.1, hcat s y (hp.mem_iff.1 hy), ha]

/-- **A bound on a plan's rows** from the knowledge of its sources: `Rel.maxRows`
with each table's own cap (`Knowledge.rows`). A `SUM`'s group is at most its
input. -/
def Rel.rowsK (K : KnowledgeEnv) : Rel → Option Nat
  | .read s => (K s).rows
  | .values _ rows => some rows.length
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r | .semi r _ _ _ =>
      r.rowsK K
  | .fetch r _ cnt => match cnt, r.rowsK K with
    | some k, some n => some (min k n)
    | some k, none => some k
    | none, n => n
  | .cross a b | .join a b .inner _ => (a.rowsK K).bind fun n => (b.rowsK K).map (n * ·)
  | .unionAll a b => (a.rowsK K).bind fun n => (b.rowsK K).map (n + ·)
  | .aggregate r gs _ => if gs.isEmpty then some 1 else r.rowsK K
  | .join _ _ .left _ | .window .. | .unnest .. => none

theorem Rel.rowsK_sound {cat : Catalog} {K : KnowledgeEnv} (hK : K.Sound cat) :
    ∀ {r : Rel} {n : Nat}, r.rowsK K = some n → (r.eval cat).length ≤ n
  | .read s, _, h => (hK s).2.2.2 _ h
  | .values _ _, _, h => by simp only [Rel.rowsK, Option.some.injEq] at h; simp [Rel.eval, h]
  | .filter r _, _, h | .semi r _ _ _, _, h => by
    simp only [Rel.rowsK] at h
    exact Nat.le_trans (List.length_filter_le _ _) (Rel.rowsK_sound hK (r := r) h)
  | .project r _, _, h | .emit r _, _, h => by
    simp only [Rel.rowsK] at h; simp only [Rel.eval, List.length_map]
    exact Rel.rowsK_sound hK (r := r) h
  | .orderBy r _, _, h => by
    simp only [Rel.rowsK] at h; simp only [Rel.eval, List.length_mergeSort]
    exact Rel.rowsK_sound hK (r := r) h
  | .distinct r, _, h => by
    simp only [Rel.rowsK] at h
    exact Nat.le_trans (dedup_length_le _) (Rel.rowsK_sound hK (r := r) h)
  | .fetch r _ cnt, n, h => by
    simp only [Rel.eval]
    cases cnt with
    | none =>
      simp only [Rel.rowsK] at h
      have := Rel.rowsK_sound hK (r := r) h
      simp only [List.length_drop]; omega
    | some k =>
      cases hr : r.rowsK K with
      | none =>
        simp only [Rel.rowsK, hr, Option.some.injEq] at h
        subst h; simp only [List.length_take]; exact Nat.min_le_left _ _
      | some m =>
        simp only [Rel.rowsK, hr, Option.some.injEq] at h
        subst h
        have := Rel.rowsK_sound hK hr
        simp only [List.length_take, List.length_drop]; omega
  | .cross a b, n, h => by
    simp only [Rel.rowsK, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    simp only [Rel.eval, length_crossRows]
    exact Nat.mul_le_mul (Rel.rowsK_sound hK ha) (Rel.rowsK_sound hK hb)
  | .join a b .inner _, n, h => by
    simp only [Rel.rowsK, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    simp only [Rel.eval]
    exact Nat.le_trans (List.length_filter_le _ _)
      (by rw [length_crossRows]; exact Nat.mul_le_mul (Rel.rowsK_sound hK ha) (Rel.rowsK_sound hK hb))
  | .unionAll a b, n, h => by
    simp only [Rel.rowsK, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    simp only [Rel.eval, List.length_append]
    exact Nat.add_le_add (Rel.rowsK_sound hK ha) (Rel.rowsK_sound hK hb)
  | .aggregate r gs _, n, h => by
    simp only [Rel.rowsK] at h
    simp only [Rel.eval, aggregateEval]
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp [hg]
    · rename_i hg
      simp only [hg, Bool.false_eq_true, ite_false, List.length_map]
      exact Nat.le_trans (dedup_length_le _) (by simpa using Rel.rowsK_sound hK (r := r) h)
  | .join _ _ .left _, _, h | .window .., _, h | .unnest .., _, h => by simp [Rel.rowsK] at h

end Substrait
