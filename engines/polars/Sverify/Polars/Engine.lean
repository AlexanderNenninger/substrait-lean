import Sverify.Polars.Profile
import Sverify.Polars.Lowering
import Sverify.Polars.LoweringLemmas
import Sverify.Engines.LoweringRaises
import Sverify.Polars.Tables
import Sverify.Engines.Sound

/-!
# Polars's Engine value (#900)

`Engine.polars` runs the plan lowered by the generated table
(`Lowering.polars`, #271) with Polars's functions, `Polars.impl`:
`Profile.polars`'s value wherever the profile gives one, and Polars's own
result where the profile keeps the reference's raise (ruling 255): a wrapped
integer, `NULL` for a zero divisor, NaN. `Polars.impl_within` proves those
within Polars's table, and `Engine.polars_sound` that the run is sound under
guard elimination's side condition (`Engine.GuardFreeSide`), by
`Rel.polars_sound`.
-/

namespace Substrait

/-- The options at which `Polars.impl_within` uses Polars's table. -/
def Profile.polarsExtras : List (Functions.Ctor × String) :=
  [(.bin .add, "overflow"), (.bin .sub, "overflow"), (.bin .mul, "overflow"),
   (.bin .idiv, "on_division_by_zero"), (.bin .imod, "on_division_by_zero"),
   (.bin .idiv, "division_type"), (.bin .imod, "division_type"),
   (.bin .fpow, "on_domain_error"), (.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"),
   (.bin .fmul, "nan_creation"), (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation")]

theorem Profile.polars_extras :
    (Profile.polarsExtras.all fun p => extraAtB Profile.polars.table p.1 p.2) = true := by
  decide

variable [Boxes.Ambient]

namespace Polars

/-- **Polars's own result where its profile raises** (D21: `Profile.polars`
keeps the reference's raise there): integer `+ - *` wrap around
(polars-int-arith), integer `//` and `%` by zero are `NULL`
(polars-int-divide, polars-int-modulus), and double operations are IEEE's, NaN
for `∞ - ∞`, `0 · ∞`, `∞ / ∞` and `power`'s domain (polars-double-arith).
Elsewhere the reference's function: no call reaches it where the profile
gives a value. -/
def errBin : BinFn → Value → Value → Value
  | .add, .int a, .int b => .int (wrap64 (a + b))
  | .sub, .int a, .int b => .int (wrap64 (a - b))
  | .mul, .int a, .int b => .int (wrap64 (a * b))
  | .idiv, .int a, .int b => if b = 0 then .null else BinFn.apply .idiv (.int a) (.int b)
  | .imod, .int a, .int b => if b = 0 then .null else BinFn.apply .imod (.int a) (.int b)
  | f, .float a, .float b =>
    if nanCase f a b then .float FloatCode.nan else f.apply (.float a) (.float b)
  | f, v, w => f.apply v w

/-- Polars's functions on the error side: `errBin`, and the reference's unary
ones. -/
def errImpl : Impl := ⟨UnFn.apply, errBin⟩

end Polars

/-- **Polars's functions**: `Profile.polars`'s value wherever the profile gives
one, Polars's own (`Polars.errImpl`) where it raises (ruling 255). The value
side is stated once, in the profile. -/
def Polars.impl : Impl := Profile.polars.okImplOr Polars.errImpl

/-- **Polars's own results on the error side are within its table**: wrapping
`+ - *` past 64 bits (`overflow`), `//` and `%` by zero
(`on_division_by_zero`), and NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞`
(`nan_creation`), each in its option's scope (D34). -/
theorem Polars.errBin_within (f : BinFn) (v w : Value) :
    Polars.errBin f v w = f.apply v w ∨ CallExtra Profile.polars.table (.bin f) [v, w] := by
  have ovf : ∀ {f : BinFn} {a b : Int}, f.issue (.int a) (.int b) = some .wraps →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int b] := fun hi hx =>
    callExtra_of_at hx (by simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
  have zero : ∀ {f : BinFn} {a : Int}, extraAtB Profile.polars.table (.bin f)
      "on_division_by_zero" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int 0] := fun hx =>
    callExtra_of_at hx (by simp [optionScope, divisorZero])
  have wrap : ∀ {f : BinFn} {a b r : Int}, f.apply (.int a) (.int b) = .int r →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      f.issue (.int a) (.int b) = wrapIf r →
      Value.int (Polars.wrap64 r) = f.apply (.int a) (.int b) ∨
        CallExtra Profile.polars.table (.bin f) [.int a, .int b] := by
    intro f a b r hr hx hi
    by_cases h64 : inI64 r = true
    · exact .inl (by rw [hr, Polars.wrap64_of_inI64 h64])
    · exact .inr (ovf (by rw [hi]; simp [wrapIf, h64]) hx)
  unfold Polars.errBin
  split
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · exact .inl rfl
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · exact .inl rfl
  · rename_i a b
    split
    · rename_i hn
      -- IEEE division's NaN is its own value (D39).
      by_cases hi : f = .fdivIeee
      · subst hi; left; simp only [BinFn.apply, fdiv_of_nanCase_ieee hn]
      right
      -- `power` has no `nan_creation`: its NaN is a domain error's.
      by_cases hp : f = .fpow
      · subst hp
        refine callExtra_of_at (o := "on_domain_error") (extraAt_of_all Profile.polars_extras (by decide)) ?_
        have : BinFn.issue .fpow (.float a) (.float b) = some .domain := by
          simp only [BinFn.issue, nanIssue, hn]; split <;> rfl
        simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, this]
      · refine callExtra_of_at (o := "nan_creation") ?_ (by simp [optionScope, hn])
        cases f <;> simp [nanCase] at hn <;> first | exact extraAt_of_all Profile.polars_extras (by decide) | exact absurd rfl hp | exact absurd rfl hi
    · exact .inl rfl
  · exact .inl rfl

/-- **`Profile.polars`'s unary functions are within Polars's table** (S1,
ruling 235): each is the reference's, but `round` and `ceil`'s IEEE `-0.0`
for a negative value that rounds to zero, in the scope of `round_zero_sign`,
which Polars's table allows (`IEEE`, D34). -/
theorem Profile.polars_un_within (f : UnFn) (v w : Value) (h : Profile.polars.un f v = .ok w) :
    w = f.apply v ∨ CallExtra Profile.polars.table (.un f) [v] := by
  have hx : ∀ g : UnFn, g = .fround ∨ g = .fceil →
      extraAtB Profile.polars.table (.un g) "round_zero_sign" = true := by
    rintro g (rfl | rfl) <;> decide
  cases hf : f.polarsTmpl with
  | none => simp only [Profile.polars, hf] at h; exact .inl (raiseIf_ok h)
  | some t =>
    have hfc : f = .fround ∨ f = .fceil := by
      cases f <;> simp only [UnFn.polarsTmpl, reduceCtorEq] at hf <;> simp
    rcases hfc with rfl | rfl
    · cases v
      case float c =>
        rw [Profile.polars_un_negZero (f := .fround) rfl (fun _ => rfl) FloatCode.round_negZero
          FloatCode.round_negNan (fun _ h => FloatCode.canon_round h)] at h
        by_cases hc : c < 0 ∧ FloatCode.round c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inl rfl)) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)).symm.trans h))
    · cases v
      case float c =>
        rw [Profile.polars_un_negZero (f := .fceil) rfl (fun _ => rfl) FloatCode.ceil_negZero
          FloatCode.ceil_negNan (fun _ h => FloatCode.canon_ceil h)] at h
        by_cases hc : c < 0 ∧ FloatCode.ceil c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inr rfl)) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)).symm.trans h))

/-! ## `Profile.polars`'s binary functions are within Polars's table (S1) -/

/-- Where a profile function with a template gives a value, it is the
template's value in Lean's functions. -/
theorem Profile.polars_bin_ok {f : BinFn} {t : Expr} (ht : f.polarsTmpl = some t) {x y v : Value}
    (h : Profile.polars.bin f x y = .ok v) : v = t.eval [x, y] := by
  simp only [Profile.polars, ht] at h
  exact Expr.evalP_reference_ok h

omit [Boxes.Ambient] in
theorem Polars.tdiv_of_dvd {a b : Int} (h : b ∣ a) : a.tdiv b = a.fdiv b := by
  rw [Int.tdiv_eq_ediv_of_dvd h, Int.fdiv_eq_ediv_of_dvd h]

omit [Boxes.Ambient] in
theorem Polars.tmod_of_dvd {a b : Int} (h : b ∣ a) : a.tmod b = a.fmod b := by
  rw [(Int.dvd_iff_tmod_eq_zero ..).mp h, (Int.dvd_iff_fmod_eq_zero ..).mp h]

/-- The floored quotient of integers, in Lean's functions: `NULL` by zero, else
`fdiv`. -/
theorem Polars.floorDivT_eval (a b : Int) :
    Polars.floorDivT.eval [.int a, .int b] = if b = 0 then .null else .int (a.fdiv b) := by
  sorry

/-- The floored remainder of integers, in Lean's functions. -/
theorem Polars.floorModT_eval (a b : Int) :
    Polars.floorModT.eval [.int a, .int b] = if b = 0 then .null else .int (a.fmod b) := by
  sorry

/-- A floored quotient or remainder is the truncated one, or the call is in
`division_type`'s scope (`floorDiffers`: the signs differ and the division is
not exact). -/
theorem Polars.floor_or_differs {a b : Int} (hb : b ≠ 0) (h : ¬floorDiffers [.int a, .int b]) :
    a.fdiv b = a.tdiv b ∧ a.fmod b = a.tmod b := by
  sorry

/-- **`Profile.polars`'s binary functions are within Polars's table** (S1,
ruling 235): the reference's, but the floored `//` and `%` of integers whose
signs differ (`division_type`, `FLOOR`). -/
theorem Profile.polars_bin_within (f : BinFn) (v w x : Value) (h : Profile.polars.bin f v w = .ok x) :
    x = f.apply v w ∨ CallExtra Profile.polars.table (.bin f) [v, w] := by
  cases hf : f.polarsTmpl with
  | none => simp only [Profile.polars, hf] at h; exact .inl (raiseIf_ok h)
  | some t =>
    have hx := Profile.polars_bin_ok hf h
    have hfc : f = .idiv ∨ f = .imod ∨ f = .fmod := by
      cases f <;> simp only [BinFn.polarsTmpl, reduceCtorEq] at hf <;> simp
    rcases hfc with rfl | rfl | rfl
    · simp only [BinFn.polarsTmpl, Option.some.injEq] at hf; subst hf
      cases v
      case int a =>
        cases w
        case int b =>
          rw [Polars.floorDivT_eval] at hx; subst hx
          by_cases hb : b = 0
          · subst hb; exact .inl rfl
          by_cases hd : floorDiffers [.int a, .int b]
          · exact .inr (callExtra_of_at (o := "division_type")
              (extraAt_of_all Profile.polars_extras (by decide)) (by simp [optionScope, hd]))
          · left; simp only [hb, ↓reduceIte, BinFn.apply, (Polars.floor_or_differs hb hd).1]
        all_goals
          rw [Polars.polars_idiv_notInt (.inr fun _ h => by cases h)] at h
          cases h; exact .inl (raiseIf_ok (Polars.ref_idiv_notInt (.inr fun _ h => by cases h))).symm
      all_goals
        rw [Polars.polars_idiv_notInt (.inl fun _ h => by cases h)] at h
        cases h; exact .inl (raiseIf_ok (Polars.ref_idiv_notInt (.inl fun _ h => by cases h))).symm
    · simp only [BinFn.polarsTmpl, Option.some.injEq] at hf; subst hf
      cases v
      case int a =>
        cases w
        case int b =>
          rw [Polars.floorModT_eval] at hx; subst hx
          by_cases hb : b = 0
          · subst hb; exact .inl rfl
          by_cases hd : floorDiffers [.int a, .int b]
          · exact .inr (callExtra_of_at (o := "division_type")
              (extraAt_of_all Profile.polars_extras (by decide)) (by simp [optionScope, hd]))
          · left; simp only [hb, ↓reduceIte, BinFn.apply, (Polars.floor_or_differs hb hd).2]
        all_goals
          rw [Polars.polars_imod_notInt (.inr fun _ h => by cases h)] at h
          exact .inl (raiseIf_ok h)
      all_goals
        rw [Polars.polars_imod_notInt (.inl fun _ h => by cases h)] at h
        exact .inl (raiseIf_ok h)
    · sorry

/-- **`Polars.impl` is within Polars's table**: where the profile gives a
value, the profile's (`Profile.polars_un_within`, `Profile.polars_bin_within`),
and Polars's own elsewhere (`Polars.errBin_within`). -/
theorem Polars.impl_within : Polars.impl.Within Profile.polars.table := by
  refine ⟨fun f v => ?_, fun f v w => ?_⟩
  · show (match Profile.polars.un f v with | .ok w => w | .error _ => UnFn.apply f v) = _ ∨ _
    cases hu : Profile.polars.un f v with
    | ok w => exact Profile.polars_un_within f v w hu
    | error _ => exact .inl rfl
  · show (match Profile.polars.bin f v w with | .ok x => x | .error _ => Polars.errBin f v w) = _ ∨ _
    cases hb : Profile.polars.bin f v w with
    | ok x => exact Profile.polars_bin_within f v w x hb
    | error _ => exact Polars.errBin_within f v w

/-- **A verified plan runs on Polars.** When `Rel.mayIssues` reports nothing
but assumed issues (whose guards the translation keeps), on every catalog
that satisfies the preconditions, the plan lowered by Polars's table, run
with Polars's functions and without its other guards, gives `Rel.eval`'s
rows. The reference raises nowhere (`Rel.not_raises_of_assumed`), so the
lowered plan raises nowhere under Polars's profile
(`Lowering.lowerRel?_raises`), where `Polars.impl` is the profile's
(`Expr.evalOkOr_of_evalP`) and the lowering exact (`Lowering.lowerRel?_sound`). -/
theorem Rel.polars_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r r' : Rel} (hr : Lowering.polars.lowerRel? r = .ok r') (hwf : r.WF cat)
    (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r'.eval cat Polars.impl = r.eval cat := by
  have h0 := Rel.not_raises_of_assumed hcat hA hF hT hwf hsmall hs hm
  have h1 : ¬r'.Raises Profile.polars cat := fun h =>
    h0 (Lowering.lowerRel?_raises Lowering.polars_allExact Lowering.polars_noneOnDbl hr h)
  rw [Rel.eval_congr_ok Expr.evalOkOr_of_evalP h1]
  exact Lowering.lowerRel?_sound Lowering.polars_noneOnDbl hr h1

/-- Polars: the plan lowered by `Lowering.polars`, run with `Polars.impl`. -/
def Engine.polars : Engine where
  name := "polars"
  profile := Profile.polars
  table := Profile.polars.table
  obs := Profile.polars.obs
  lower r := (Lowering.polars.lowerRel? r).toOption
  impl := Polars.impl
  within := Polars.impl_within

theorem Engine.polars_lower {r r' : Rel} (h : Engine.polars.lower r = some r') :
    Lowering.polars.lowerRel? r = .ok r' := by
  simp only [Engine.polars] at h
  cases hr : Lowering.polars.lowerRel? r <;> simp_all [Except.toOption]

/-- Polars under guard elimination's side condition: the lowered plan's
functions compute `Rel.eval` (`Rel.polars_sound`). -/
theorem Engine.polars_sound : Engine.polars.Sound Engine.GuardFreeSide := by
  intro cat r r' hl ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  show r.Allowed cat (r'.eval cat Polars.impl)
  rw [Rel.polars_sound hcat hA hF hT (Engine.polars_lower hl) hwf hsmall hs hm]
  exact r.eval_allowed cat

end Substrait

namespace Substrait
section Example
attribute [local instance] Engine.exampleBoxes

/-- Polars on the example of `Sound.lean`: `Engine.contract_sound`'s hypotheses
hold (`Engine.example_contract`), so the postcondition holds on the rows
Polars's functions compute. -/
theorem Engine.polars_contract_example :
    ∀ row ∈ postRows Engine.examplePost [2]
        (Engine.examplePlan.eval Engine.exampleCat Engine.polars.impl),
      ∀ v ∈ row, v = .bool true := by
  exact Engine.example_contract Engine.polars_sound (T' := Engine.examplePlan) (by decide)
    Engine.guardFreeSide_example

end Example

end Substrait
