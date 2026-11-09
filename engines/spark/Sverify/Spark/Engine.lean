import Sverify.Spark.Profile
import Sverify.Spark.Tables
import Sverify.Engines.Sound

/-!
# Spark's Engine value (#900)

`Engine.spark` runs the plan as the writer writes it under ANSI, with its
profile's functions where they do not raise (`Profile.sparkWritten`).
`Profile.spark_withinOk` and `Profile.sparkWritten_withinOk` prove those
within Spark's table, `Profile.sparkWritten_okImpl_faithful` that they agree
with the reference where it reports no issue, and `Engine.spark_sound` that
the run is sound under guard elimination's side condition
(`Engine.GuardFreeSide`).
-/

namespace Substrait

/-- The options at which `Profile.spark_withinOk` uses Spark's table. -/
def Profile.sparkExtras : List (Functions.Ctor × String) :=
  FMath.all.map (fun g => (.un (.fmath g), "on_domain_error")) ++
    [(.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"), (.bin .fmul, "nan_creation"),
     (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation"), (.bin .fpow, "on_domain_error"),
     (.bin .fpow, "pow_one_inf"), (.un .ffloor, "float_to_int"), (.un .fceil, "float_to_int"),
     (.bin .fatan2, "on_domain_error"), (.bin .fatan2, "zero_sign"),
     (.bin (.bit .shl), "shift_range"), (.bin (.bit .shr), "shift_range")]

theorem Profile.spark_extras :
    (Profile.sparkExtras.all fun p => extraAtB Profile.spark.table p.1 p.2) = true := by
  decide +kernel

variable [Boxes.Ambient]

/-- **Spark's functions are within its table**: each value `sparkBin` and
`sparkUn` change is in the scope of an option Spark's table allows another
behaviour: a created NaN (`nan_creation`), a domain error's NaN or NULL, or
an out-of-range shift's masked count (`on_domain_error`). -/
theorem Profile.spark_withinOk : Profile.spark.WithinOk Profile.spark.table := by
  refine ⟨fun f v w h => ?_, fun f v w x h => ?_⟩
  · simp only [Profile.spark] at h
    cases hs : sparkUn f v with
    | none => rw [hs] at h; exact .inl (raiseIf_ok h)
    | some o =>
      rw [hs] at h
      right
      -- `sparkUn`'s arms: an elementary function, `floor`, `ceil`, the rest.
      unfold sparkUn at hs
      split at hs
      case h_1 g c =>
        split at hs
        · rename_i hc
          refine callExtra_of_at (o := "on_domain_error")
            (by cases g <;> exact extraAt_of_all Profile.spark_extras (by decide)) ?_
          simp [optionScope, Functions.Ctor.issue, UnFn.issueAll, UnFn.issue, domainIssue, hc]
        · cases hs
      -- `floor` and `ceil`: NaN is `0` (`float_to_int`), or they overflow.
      case h_2 | h_3 =>
        split at hs
        · exact callExtra_of_at (o := "float_to_int") (extraAt_of_all Profile.spark_extras (by decide))
            (by simp [optionScope])
        · split at hs <;> cases hs; cases h
      all_goals cases hs
  · simp only [Profile.spark] at h
    cases hs : sparkBin f v w with
    | none => rw [hs] at h; exact .inl (raiseIf_ok h)
    | some o =>
      rw [hs] at h
      have nanC : ∀ {g : BinFn} {a b : Int}, nanCase g a b = true →
          extraAtB Profile.spark.table (.bin g) "nan_creation" = true →
          CallExtra Profile.spark.table (.bin g) [.float a, .float b] :=
        fun hn hx => callExtra_of_at hx (by simp [optionScope, hn])
      have dom : ∀ {g : BinFn} {v w : Value}, g.issue v w = some .domain →
          extraAtB Profile.spark.table (.bin g) "on_domain_error" = true →
          CallExtra Profile.spark.table (.bin g) [v, w] :=
        fun hi hx => callExtra_of_at hx (by
          simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
      -- `sparkBin`'s arms, in order: `+ - * / %` of doubles, IEEE `/`, `power`,
      -- `<<`, `>>`, the rest.
      unfold sparkBin at hs
      split at hs
      case h_1 | h_2 | h_3 | h_4 | h_5 =>
        split at hs
        · exact .inr (nanC (by assumption) (extraAt_of_all Profile.spark_extras (by decide)))
        · cases hs
      case h_6 a b =>
        split at hs
        · cases hs; cases h
        · split at hs
          · rename_i _ hn
            -- `∞ / ∞`: IEEE division's own NaN.
            have : nanCase .fdivIeee a b = true := by
              simp only [nanCase, Bool.or_eq_true] at hn ⊢; exact .inl hn
            cases hs; cases h
            exact .inl (by simp only [BinFn.apply, fdiv_of_nanCase_ieee this])
          · cases hs
      case h_7 a b =>
        simp only [sparkPow] at hs
        split at hs
        · rename_i hn
          exact .inr (dom (by simp [BinFn.issue, hn]) (extraAt_of_all Profile.spark_extras (by decide)))
        · split at hs
          · rename_i hn' hn
            exact .inr (dom (by simp [BinFn.issue, nanIssue, hn, Bool.not_eq_true _ |>.mp hn'])
              (extraAt_of_all Profile.spark_extras (by decide)))
          · split at hs
            · rename_i hp
              exact .inr (callExtra_of_at (o := "pow_one_inf")
                (extraAt_of_all Profile.spark_extras (by decide)) (by simp [optionScope, hp]))
            · cases hs
      case h_8 a b =>
        split at hs
        · rename_i hz
          exact .inr (dom (by simp [BinFn.issue, domainIssue, atan2?, hz.1, hz.2]) (extraAt_of_all Profile.spark_extras (by decide)))
        · split at hs
          · rename_i hz
            refine .inr (callExtra_of_at (o := "zero_sign") (extraAt_of_all Profile.spark_extras (by decide)) ?_)
            rcases hz with rfl | rfl <;>
              simp [optionScope, Value.anyZero, Value.hasZero, FloatCode.isZeroCode]
          · cases hs
      case h_9 | h_10 =>
        split at hs
        · cases hs
        · exact .inr (callExtra_of_at (o := "shift_range") (extraAt_of_all Profile.spark_extras (by decide)) (by simp [optionScope]))
      case h_11 => cases hs

/-- **Spark as the writer writes it is within its table**: the reference's
functions where the writer shims or refuses (`Profile.sparkWritten`), Spark's
elsewhere (`Profile.spark_withinOk`). -/
theorem Profile.sparkWritten_withinOk : Profile.sparkWritten.WithinOk Profile.spark.table := by
  refine ⟨fun f v w h => ?_, fun f v w x h => ?_⟩
  · simp only [Profile.sparkWritten] at h
    split at h
    · exact .inl (raiseIf_ok h)
    · exact Profile.spark_withinOk.1 f v w h
  · simp only [Profile.sparkWritten] at h
    split at h
    · exact .inl (raiseIf_ok h)
    · exact Profile.spark_withinOk.2 f v w x h

/-- **Spark as the writer writes it is faithful where it does not raise**:
wherever the reference reports no issue, the written plan gives the
reference's value or raises (IEEE division by a zero, `floor` past 64 bits),
and `okImpl` then takes the reference's. Spark's own values there (`floor`
of NaN, `power(1, ∞)`) are the writer's to shim or refuse
(`Profile.sparkWritten`); every other value of its own is where the
reference raises. -/
theorem Profile.sparkWritten_okImpl_faithful : Profile.sparkWritten.okImpl.Faithful := by
  refine ⟨fun f v h => ?_, fun f v w h => ?_⟩
  · show (match Profile.sparkWritten.un f v with | .ok w => w | .error _ => f.apply v) = f.apply v
    by_cases hw : f.sparkWritten = true
    · simp [Profile.sparkWritten, hw, Profile.reference, h, raiseIf]
    simp only [Profile.sparkWritten, hw, Bool.false_eq_true, ↓reduceIte, Profile.spark,
      Profile.reference, h, raiseIf]
    cases hs : sparkUn f v with
    | none => rfl
    | some o =>
      simp only [Option.getD]
      unfold sparkUn at hs
      split at hs
      case h_1 g c =>
        split at hs
        · rename_i hc; simp [UnFn.issue, domainIssue, hc] at h
        · cases hs
      case h_2 | h_3 => simp [UnFn.sparkWritten] at hw
      all_goals cases hs
  · show (match Profile.sparkWritten.bin f v w with | .ok x => x | .error _ => f.apply v w) =
      f.apply v w
    by_cases hw : f.sparkWritten = true
    · simp [Profile.sparkWritten, hw, Profile.reference, h, raiseIf]
    simp only [Profile.sparkWritten, hw, Bool.false_eq_true, ↓reduceIte, Profile.spark,
      Profile.reference, h, raiseIf]
    cases hs : sparkBin f v w with
    | none => rfl
    | some o =>
      simp only [Option.getD]
      unfold sparkBin at hs
      split at hs
      case h_1 | h_2 | h_3 | h_4 | h_5 =>
        split at hs
        · rename_i hn
          -- `/` and `%` report a zero divisor first, a domain issue else.
          simp [BinFn.issue, nanIssue, hn] at h <;> split at h <;> simp at h
        · cases hs
      case h_6 a b =>
        split at hs
        · cases hs; rfl
        · split at hs
          · rename_i _ hn
            have : nanCase .fdivIeee a b = true := by
              simp only [nanCase, Bool.or_eq_true] at hn ⊢; exact .inl hn
            cases hs; simp only [BinFn.apply, fdiv_of_nanCase_ieee this]
          · cases hs
      case h_7 | h_8 => simp [BinFn.sparkWritten] at hw
      case h_9 | h_10 =>
        split at hs
        · cases hs
        · rename_i hr; simp [BinFn.issue, domainIssue, BitOp.apply, hr] at h
      case h_11 => cases hs

/-- Spark under ANSI, as the writer writes it: its profile's functions where
they do not raise (`Profile.sparkWritten`), its own choices. -/
def Engine.spark : Engine where
  name := "spark"
  profile := Profile.spark
  table := Profile.spark.table
  obs := Profile.spark.obs
  lower := some
  impl := Profile.sparkWritten.okImpl
  within := Profile.okImpl_within Profile.sparkWritten_withinOk

/-- Spark: its profile's functions where they do not raise give the
reference's value wherever the reference reports no issue
(`Profile.sparkWritten_okImpl_faithful`), so guard elimination applies. -/
theorem Engine.spark_sound : Engine.spark.Sound Engine.GuardFreeSide := by
  intro cat r r' hl _ ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  exact Rel.guardFree_allowed hcat hA hF hT hwf hsmall hs hm Profile.sparkWritten_okImpl_faithful

end Substrait
