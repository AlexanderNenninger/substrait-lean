import Sverify.Core.AllowedP

/-!
# A finite double sum has finite addends (#1608 item 7, #1787)

IEEE 754 addition keeps a NaN and an infinity: `NaN + x` is NaN, `±∞ + x` is
`±∞` or NaN. So wherever an engine's `SUM` of doubles is finite, in whatever
order it added them, no value it added is NaN or `±∞`.

The writer's double `SUM` and `AVG` guard the reference's non-finite cases
with aggregates of their own (`MAX` of the values that are not NaN, `MIN`, and
`MAX` of their magnitudes): both infinities among the values raise a domain
error, and finite values whose sum is `±∞` raise the overflow. Neither fires
for a group whose engine `SUM` is finite. The two-stage form computes those
aggregates only for the groups whose `SUM` is not finite; this module is the
fact it rests on, for the summation shapes the core models:

* `FloatCode.addI_isFinCode`: `a + b` finite gives `a` and `b` finite;
* `floatSum_isFinCode`: the same for a sequential sum (`SEQUENTIAL`);
* `FloatSums.isFinCode`: and for a tree of sums in any order (`ANY`,
  `PAIRWISE`, a two-phase sum);
* `floatSumCR_isFinCode`: and for the exact sum rounded once (`EXACT`);
* `SumOrder.isFinCode`, the one the rewrite reads (ruling 212, A1): for each
  of those `sum_order` behaviours.

A constant run added as one product (DuckDB's `SCALED_CONSTANT`) and Kahan's
compensated sum (Polars's `COMPENSATED`) have no shape in `SumOrder`; for
them the statement is a probed engine fact (ruling 212, A2).

Finite here is a code that is neither NaN nor an infinity (`IsFinCode`), so
`-0.0`, whose code lies below `-∞`'s, is finite.
-/

namespace Substrait

namespace FloatCode

/-- A code that is neither NaN nor an infinity. -/
def IsFinCode (c : Int) : Prop := isNanCode c = false ∧ isInfCode c = false

/-- **`a + b` finite: `a` and `b` are.** NaN and the infinities propagate. -/
theorem addI_isFinCode {a b : Int} (h : IsFinCode (addI a b)) : IsFinCode a ∧ IsFinCode b := by
  obtain ⟨h1, h2⟩ := h
  have hN : isNanCode nan = true := by simp [isNanCode]
  have hP : isInfCode posInf = true := by simp [isInfCode]
  have hM : isInfCode negInf = true := by simp [isInfCode]
  by_cases hn : (isNanCode a || isNanCode b) = true
  · rw [addI, ite_eq_left hn, hN] at h1; cases h1
  obtain ⟨ha, hb⟩ : isNanCode a = false ∧ isNanCode b = false := by simpa using hn
  by_cases hpa : a = posInf
  · rw [addI, ite_eq_right hn, ite_eq_left hpa] at h1 h2
    split at h1 <;> simp_all
  by_cases hma : a = negInf
  · rw [addI, ite_eq_right hn, ite_eq_right hpa, ite_eq_left hma] at h1 h2
    split at h1 <;> simp_all
  by_cases hib : isInfCode b = true
  · rw [addI, ite_eq_right hn, ite_eq_right hpa, ite_eq_right hma, ite_eq_left hib, hib] at h2; cases h2
  exact ⟨⟨ha, by simp [isInfCode, hpa, hma]⟩, hb, by simpa using hib⟩

end FloatCode

open FloatCode

/-- A sequential sum from `acc` that is finite starts from a finite `acc` and
adds finite doubles only. -/
theorem foldl_isFinCode (ws : List Value) (acc : Int)
    (h : IsFinCode (ws.foldl (fun acc v => match v with
      | .float c => fadd acc c
      | _ => acc) acc)) :
    IsFinCode acc ∧ ∀ c, Value.float c ∈ ws → IsFinCode c := by
  induction ws generalizing acc with
  | nil => exact ⟨h, by simp⟩
  | cons w ws ih =>
    rw [List.foldl_cons] at h
    obtain ⟨hacc, hws⟩ := ih _ h
    cases w with
    | float c =>
      obtain ⟨ha, hc⟩ := addI_isFinCode hacc
      refine ⟨ha, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with hx | hx
      · cases hx; exact hc
      · exact hws x hx
    | _ =>
      refine ⟨hacc, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with hx | hx
      · cases hx
      · exact hws x hx

/-- **A finite sequential sum adds finite doubles only** (`SEQUENTIAL`). -/
theorem floatSum_isFinCode {ws : List Value} (h : IsFinCode (floatSum ws)) :
    ∀ c, Value.float c ∈ ws → IsFinCode c :=
  (foldl_isFinCode ws _ h).2

/-- **A finite sum in any order adds finite doubles only** (`ANY`,
`PAIRWISE`: a tree of sequential sums of a permutation, `FloatSums`). -/
theorem FloatSums.isFinCode {vs : List Value} {s : Int} (h : FloatSums vs s)
    (hs : IsFinCode s) : ∀ c, Value.float c ∈ vs → IsFinCode c := by
  induction h with
  | seq hp => exact fun c hc => floatSum_isFinCode hs c (hp.symm.subset hc)
  | split hp _ _ iha ihb =>
    obtain ⟨ha, hb⟩ := addI_isFinCode hs
    intro c hc
    rcases List.mem_append.1 (hp.subset hc) with hx | hx
    · exact iha ha c hx
    · exact ihb hb c hx

/-- `nonFinite` gives NaN or an infinity. -/
theorem nonFinite_some {vs : List Value} {y : Int} (h : nonFinite vs = some y) :
    y = nan ∨ y = posInf ∨ y = negInf := by
  unfold nonFinite at h
  repeat' split at h
  all_goals simp_all

/-- **The exact sum rounded once, finite, adds finite doubles only**
(`EXACT`). -/
theorem floatSumCR_isFinCode {vs : List Value} (h : IsFinCode (floatSumCR vs)) :
    ∀ c, Value.float c ∈ vs → IsFinCode c := by
  intro c hc
  unfold floatSumCR at h
  cases hn : nonFinite vs with
  | some y =>
    exfalso
    rw [hn, Option.getD_some] at h
    rcases nonFinite_some hn with rfl | rfl | rfl <;> simp [IsFinCode, FloatCode.isNanCode, FloatCode.isInfCode] at h
  | none =>
    have := posInf_eq; have := negInf_eq; have := nan_eq; have := negNan_eq'
    have any (p : Int → Bool) (hp : p (canon c) = true) : anyCode p vs = true :=
      List.any_eq_true.2 ⟨.float c, hc, hp⟩
    unfold IsFinCode
    by_cases hnan : FloatCode.isNanCode c = true
    · have hcn : canon c = nan := by
        rcases (by simpa [FloatCode.isNanCode] using hnan : c = nan ∨ c = negNan) with rfl | rfl
        · exact canon_nan
        · exact fp64.canon_negNan
      have := any (fun c => decide (nan ≤ c)) (by simp [hcn])
      unfold nonFinite at hn; simp [this] at hn
    by_cases hinf : FloatCode.isInfCode c = true
    · rcases (by simpa [FloatCode.isInfCode] using hinf : c = posInf ∨ c = negInf) with rfl | rfl
      · have := any (fun c => decide (posInf ≤ c ∧ c < nan)) (by simp [canon_posInf]; omega)
        unfold nonFinite at hn
        repeat' split at hn
        all_goals simp_all
      · have := any (fun c => decide (c ≤ negInf)) (by simp [canon_negInf])
        unfold nonFinite at hn
        repeat' split at hn
        all_goals simp_all
    exact ⟨by simpa using hnan, by simpa using hinf⟩

/-- **A finite `SUM` adds finite doubles only**, under each `sum_order`
behaviour with a shape (ruling 212, A1): a finite engine sum means no NaN and
no infinity among its values, so the writer's guard of both infinities cannot
fire for that group. -/
theorem SumOrder.isFinCode {b : Behaviour} {vs : List Value} {c : Int}
    (hb : b ∈ ["ANY", "PAIRWISE", "SEQUENTIAL", "EXACT"]) (h : SumOrder b vs c)
    (hc : IsFinCode c) : ∀ x, Value.float x ∈ vs → IsFinCode x := by
  unfold SumOrder at h
  by_cases h1 : b = "EXACT"
  · rw [ite_eq_left h1] at h; subst h; exact floatSumCR_isFinCode hc
  rw [ite_eq_right h1] at h
  by_cases h2 : b = "ANY" ∨ b = "PAIRWISE"
  · rw [ite_eq_left h2] at h; exact h.2.isFinCode hc
  rw [ite_eq_right h2] at h
  by_cases h3 : b = "SEQUENTIAL"
  · rw [ite_eq_left h3] at h
    obtain ⟨ws, hp, rfl⟩ := h.2
    exact fun x hx => floatSum_isFinCode hc x (hp.symm.subset hx)
  simp at hb; simp_all

end Substrait
