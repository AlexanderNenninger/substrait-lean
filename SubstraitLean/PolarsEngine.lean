import SubstraitLean.PolarsProfile
import SubstraitLean.PolarsTables
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
  intro cat r r' hl _ ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  show r.Allowed cat (r.eval cat Polars.written)
  rw [Rel.polars_sound hcat hA hF hT hwf hsmall hs hm]; exact r.eval_allowed cat

end Substrait
