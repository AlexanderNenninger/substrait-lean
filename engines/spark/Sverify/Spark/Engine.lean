import Sverify.Spark.Profile
import Sverify.Spark.Tables
import Sverify.Spark.Lowering
import Sverify.Engines.LoweringRaises
import Sverify.Engines.Sound

/-!
# Spark's Engine value (#900, #271)

`Engine.spark` runs the plan Spark's generated lowering writes
(`Lowering.spark`, `Spark/Lowering.lean`) with its profile's functions where
they do not raise (`Spark.impl`, within Spark's table by
`Profile.spark_withinOk`). Its soundness has two branches (ruling 277), on a
catalog of doubles for a plan whose constants are doubles:

* `Rel.spark_sound`: a plan every expression of which the table lowers exactly
  (`Rel.ExactOnB`, false exactly where it calls IEEE division), under guard
  elimination's side condition (ruling 256 A).
* `Rel.spark_sound_or_raises`: any plan the table lowers, every guard kept,
  where Spark does not raise (ruling 256 B), as for DuckDB (`Engine.NoRaiseSide`).

`Engine.spark_sound` joins them under `Engine.SparkSide`.
-/
namespace Substrait

/-- The options at which `Profile.spark_withinOk` uses Spark's table. -/
def Profile.sparkExtras : List (Functions.Ctor × String) :=
  FMath.all.map (fun g => (.un (.fmath g), "on_domain_error")) ++
    [(.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"), (.bin .fmul, "nan_creation"),
     (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation"), (.bin .fpow, "on_domain_error"),
     (.bin .fpow, "pow_one_inf"), (.un .ffloor, "float_to_int"), (.un .fceil, "float_to_int"),
     (.bin .fatan2, "on_domain_error"), (.bin .fatan2, "zero_sign"),
     (.bin (.bit .shl), "shift_range"), (.bin (.bit .shr), "shift_range"),
     (.bin .dateAdd, "date_range"), (.un (.ftod 0), "decimal_rescale")]

theorem Profile.spark_extras :
    (Profile.sparkExtras.all fun p => extraAtB Profile.spark.table p.1 p.2) = true := by
  decide +kernel

variable [Boxes.Ambient]

/-- **Spark's functions are within its table**: each value `sparkBin` and
`sparkUn` change is in the scope of an option Spark's table allows another
behaviour: a created NaN (`nan_creation`), a domain error's NaN or NULL, an
out-of-range shift's masked count (`on_domain_error`), or a double cast to a
decimal (`decimal_rescale`). `date_add`'s wrap
at 2³¹ days (SP-2) is in the scope of `date_range`, which the table leaves
uncharacterized (`Profile.spark.table` has no row for it, so it allows
`COMPUTE`). -/
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
      -- A double to a decimal: every one is in `decimal_rescale`'s scope.
      case h_4 s _ =>
        have hd : extraAtB Profile.spark.table (.un (.ftod s)) "decimal_rescale" = true :=
          (show extraAtB Profile.spark.table (.un (.ftod 0)) "decimal_rescale" = true from
            extraAt_of_all Profile.spark_extras (by decide))
        exact callExtra_of_at hd (by simp [optionScope])
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
              simp [optionScope, zeroSignReads, Value.anyZero, Value.hasZero, FloatCode.isZeroCode]
          · cases hs
      case h_9 | h_10 =>
        split at hs
        · cases hs
        · exact .inr (callExtra_of_at (o := "shift_range") (extraAt_of_all Profile.spark_extras (by decide)) (by simp [optionScope]))
      -- `date_add` wraps the sum at 2³¹ days: the reference's value inside its
      -- date range, a value of `date_range`'s scope past it.
      case h_11 a b =>
        split at hs
        · cases hs; cases h
          by_cases hr : rangeIssue Time.dayMin Time.dayMax a (a + b) = none
          · left
            simp only [rangeIssue] at hr
            split at hr
            · rename_i hbt
              simp only [between, Bool.and_eq_true, decide_eq_true_eq] at hbt
              have h1 : Time.dayMin = -719162 := rfl
              have h2 : Time.dayMax = 2932896 := rfl
              simp only [BinFn.apply]
              rw [Spark.wrap32_of_small (by omega) (by omega)]
            · cases hr
          · right
            refine callExtra_of_at (o := "date_range")
              (extraAt_of_all Profile.spark_extras (by decide)) ?_
            simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, BinFn.issue]
            left
            simp only [rangeIssue] at hr ⊢
            split at hr <;> simp_all
        · cases hs
      case h_12 => cases hs

/-- Spark's functions: its profile's values where they do not raise. Where
the profile raises, Spark's run stops (ANSI). -/
def Spark.impl : Impl := Profile.spark.okImpl

/-- **A verified plan runs on Spark, guards dropped** (ruling 277, the first
branch; ruling 256 A). When `Rel.mayIssues` reports nothing but assumed
issues (whose guards the writer keeps), on every catalog of doubles that
satisfies the preconditions, a plan whose constants are doubles and whose
expressions Spark's table lowers exactly (no IEEE division) gives `Rel.eval`'s
rows lowered (`Lowering.spark.lowerRel?`, every template guard kept). The
lowered plan raises only where the reference does
(`Lowering.lowerRel?_raises_dbl`), and the reference does not raise here. -/
theorem Rel.spark_sound {cat : Catalog} (hcat : cat.WF) (hdbl : cat.Dbl) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) (hc : r.ConstsDbl)
    (hx : r.ExactOnB Lowering.spark = true) {r' : Rel} (hr : Lowering.spark.lowerRel? r = .ok r') :
    r'.eval cat Spark.impl = r.eval cat := by
  have h0 := Rel.not_raises_of_assumed hcat hA hF hT hwf hsmall hs hm
  have h1 : ¬r'.Raises Profile.spark cat := fun h =>
    h0 (Lowering.lowerRel?_raises_dbl hdbl hc (Rel.exactOn_of_exactOnB hx) hr h)
  rw [Spark.impl, Rel.eval_okImpl h1]
  exact Lowering.lowerRel?_sound_dbl hdbl hc hr h1

/-- **A plan Spark's table lowers runs correctly on Spark, or raises**
(ruling 277, the second branch; ruling 256 B): on a catalog of doubles, for a
plan whose constants are doubles, with every guard kept, the lowered plan
gives `Rel.eval`'s rows where Spark does not raise. It covers IEEE division,
whose entry raises at a zero divisor of either sign where IEEE gives `±∞`:
Spark raises there under ANSI (spark-double-divide; #1130's obligation 2;
`spark.sql.ansi.enabled` in `sverify_spark.dialect.SPARK_CONF`), which stops
the run, and gives no wrong value. -/
theorem Rel.spark_sound_or_raises {cat : Catalog} (hdbl : cat.Dbl) {r r' : Rel}
    (hc : r.ConstsDbl) (hr : Lowering.spark.lowerRel? r = .ok r')
    (h : ¬r'.Raises Profile.spark cat) : r'.eval cat Spark.impl = r.eval cat := by
  rw [Spark.impl, Rel.eval_okImpl h]
  exact Rel.spark_lowered_sound hdbl hc hr h

/-- Spark under ANSI, as its generated lowering writes the plan: its profile's
functions where they do not raise. -/
def Engine.spark : Engine where
  name := "spark"
  profile := Profile.spark
  table := Profile.spark.table
  obs := Profile.spark.obs
  lower r := (Lowering.spark.lowerRel? r).toOption
  impl := Spark.impl
  within := Profile.okImpl_within Profile.spark_withinOk

theorem Engine.spark_lower {r r' : Rel} (h : Engine.spark.lower r = some r') :
    Lowering.spark.lowerRel? r = .ok r' := by
  simp only [Engine.spark] at h
  cases hr : Lowering.spark.lowerRel? r <;> simp_all [Except.toOption]

/-- **Spark's side condition** (ruling 277): a catalog of doubles and a plan
whose constants are doubles, and either the first branch's (no IEEE division,
`Engine.GuardFreeSide`) or the second's (Spark does not raise on the lowered
plan, every guard kept). -/
def Engine.SparkSide (cat : Catalog) (r : Rel) : Prop :=
  cat.Dbl ∧ r.ConstsDbl ∧
    ((r.ExactOnB Lowering.spark = true ∧ Engine.GuardFreeSide cat r) ∨ Engine.spark.NoRaiseSide cat r)

/-- **Spark's run is sound** under `Engine.SparkSide`: `Rel.spark_sound` on
the first branch, `Rel.spark_sound_or_raises` on the second. -/
theorem Engine.spark_sound : Engine.spark.Sound Engine.SparkSide := by
  intro cat r r' hl ⟨hdbl, hc, hb⟩
  have hr := Engine.spark_lower hl
  show r.Allowed cat (r'.eval cat Spark.impl)
  rcases hb with ⟨hx, _, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩ | hn
  · rw [Rel.spark_sound hcat hdbl hA hF hT hwf hsmall hs hm hc hx hr]; exact r.eval_allowed cat
  · rw [Rel.spark_sound_or_raises hdbl hc hr (hn r' hl)]; exact r.eval_allowed cat

end Substrait

namespace Substrait
section Example
attribute [local instance] Engine.exampleBoxes

/-- Spark on the example of `Sound.lean`: `Engine.contract_sound`'s hypotheses
hold (`Engine.example_contract`), so the postcondition holds on the rows
Spark's functions compute. -/
theorem Engine.spark_contract_example :
    ∀ row ∈ postRows Engine.examplePost [2]
        (Engine.examplePlan.eval Engine.exampleCat Engine.spark.impl),
      ∀ v ∈ row, v = .bool true := by
  refine Engine.example_contract Engine.spark_sound (T' := Engine.examplePlan) rfl
    ⟨fun t row h v hv => ?_, ⟨rfl, fun e he => ?_⟩, .inl ⟨rfl, Engine.guardFreeSide_example⟩⟩
  · simp only [Engine.exampleCat] at h
    split at h <;> simp at h
    rcases h with rfl | rfl <;> simp at hv <;> subst hv <;> rfl
  · simp [Engine.examplePlan, Rel.mappedExprs] at he
    subst he; rfl

end Example

-- Every function the generated lowering writes natively reads the reference's
-- behaviour from the table at each of its options (`nativeOffReference`, ruling
-- 278's addendum), but at the pending functions and options listed. Ruling 282 (F282)
-- accepts the list: it only shrinks (the guard fails on a new entry and on a fixed
-- one), and a pending function stays on the hand-written translation path until
-- its entry is resolved. The check reads options per function (C1) and skips those
-- the observation row absorbs (C2, C3); Spark has none left.
#guard letI := Boxes.Ambient.none
  nativeOffIs Profile.spark.table Profile.spark.obs Lowering.spark.nativeUn Lowering.spark.nativeBin
    []

end Substrait
