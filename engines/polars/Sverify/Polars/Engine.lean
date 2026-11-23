import Sverify.Polars.Profile
import Sverify.Polars.Lowering
import Sverify.Polars.Tables
import Sverify.Engines.Sound

/-!
# Polars's Engine value (#900)

`Engine.polars` runs the plan as the translation writes it, with the
functions of the written plan (`Polars.written`). `Polars.written_within`
proves those within Polars's table, and `Engine.polars_sound` that the run is
sound under guard elimination's side condition (`Engine.GuardFreeSide`), by
`Rel.polars_sound`.
-/

namespace Substrait

/-- The options at which `Polars.written_within` uses Polars's table. -/
def Profile.polarsExtras : List (Functions.Ctor × String) :=
  [(.bin .add, "overflow"), (.bin .sub, "overflow"), (.bin .mul, "overflow"),
   (.bin .idiv, "on_division_by_zero"), (.bin .imod, "on_division_by_zero"),
   (.bin .fpow, "on_domain_error"), (.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"),
   (.bin .fmul, "nan_creation"), (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation")]

theorem Profile.polars_extras :
    (Profile.polarsExtras.all fun p => extraAtB Profile.polars.table p.1 p.2) = true := by
  decide

variable [Boxes.Ambient]

/-- **The written Polars plan's functions are within Polars's table**:
wrapping `+ - *` past 64 bits (`overflow`), `//` and `%` by zero
(`on_division_by_zero`), and NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞`
(`nan_creation`), each in its option's scope (D34). -/
theorem Polars.written_within : Polars.written.Within Profile.polars.table := by
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
  refine ⟨fun _ _ => .inl rfl, fun f v w => ?_⟩
  show Polars.bin f v w = f.apply v w ∨ _
  unfold Polars.bin
  split
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_div_trunc a hb]
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_mod_trunc a hb]
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
  have hx : ∀ g : UnFn, g = .fround ∨ g = .froundEven ∨ g = .fceil →
      extraAtB Profile.polars.table (.un g) "round_zero_sign" = true := by
    rintro g (rfl | rfl | rfl) <;> decide
  cases hf : f.polarsTmpl with
  | none => simp only [Profile.polars, hf] at h; exact .inl (raiseIf_ok h)
  | some t =>
    have hfc : f = .fround ∨ f = .froundEven ∨ f = .fceil := by
      cases f <;> simp only [UnFn.polarsTmpl, reduceCtorEq] at hf <;> simp
    rcases hfc with rfl | rfl | rfl
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
        rw [Profile.polars_un_negZero (f := .froundEven) rfl (fun _ => rfl) FloatCode.roundEven_negZero
          FloatCode.roundEven_negNan (fun _ h => FloatCode.canon_roundEven h)] at h
        by_cases hc : c < 0 ∧ FloatCode.roundEven c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inr (.inl rfl))) (by
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
          exact .inr (callExtra_of_at (hx _ (.inr (.inr rfl))) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)).symm.trans h))

/-- Polars, as the translation writes the plan (`Polars.written`). -/
def Engine.polars : Engine where
  name := "polars"
  profile := Profile.polars
  table := Profile.polars.table
  obs := Profile.polars.obs
  lower := some
  impl := Polars.written
  within := Polars.written_within

/-- Polars under guard elimination's side condition: the written plan's
functions compute `Rel.eval` (`Rel.polars_sound`). -/
theorem Engine.polars_sound : Engine.polars.Sound Engine.GuardFreeSide := by
  intro cat r r' hl ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  show r.Allowed cat (r.eval cat Polars.written)
  rw [Rel.polars_sound hcat hA hF hT hwf hsmall hs hm]; exact r.eval_allowed cat

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
  exact Engine.example_contract Engine.polars_sound (T' := Engine.examplePlan) rfl
    Engine.guardFreeSide_example

end Example

end Substrait
