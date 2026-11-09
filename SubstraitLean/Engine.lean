import SubstraitLean.Obligations
import SubstraitLean.PolarsShims
import SubstraitLean.SparkShims
import SubstraitLean.PolarsProfile
import SubstraitLean.SparkProfile
import Sverify.Engines.Engine
import SubstraitLean.EngineTables

/-!
# The engines' Engine values (#900)

DuckDB's, Polars's and Spark's `Engine` values (the structure is
engines-common, `engines/Sverify/Engines/Engine.lean`), with the proofs that
their functions are within their tables:

* `Engine.spark` takes Lean's functions (`Profile.spark` is the reference);
  `Engine.duckdb` (IEEE operations, `ieee_floating_point_ops` on, the
  default) takes `impl := profile.okImpl` (`Profile.duckdb_withinOk`);
  `Engine.polars` takes the functions of the written plan (`Polars.written`,
  `Polars.written_within`).
-/

namespace Substrait

/-- **DuckDB's functions are within its table**, with IEEE operations on:
each value `duckBin` and `duckUn` change is in the scope of an option the
table allows another behaviour (D34): a domain error's NaN, a zero divisor's
`±∞` or NaN or NULL, a created NaN, a shift out of range. With
`ieee_floating_point_ops` off, `(-∞) ^ y` has no row (#900). -/
theorem Profile.duckdb_withinOk {s : DuckDBSettings} (hs : s.ieeeOps = true) :
    (Profile.duckdb s).WithinOk (Profile.duckdb.table s) := by
  obtain ⟨e, i⟩ := s
  simp only at hs; subst hs
  refine ⟨fun f v w h => ?_, fun f v w x h => ?_⟩
  · simp only [Profile.duckdb] at h
    cases v with
    | float a =>
      simp only at h
      cases hd : duckUn ⟨e, true⟩ f a with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        right
        cases f <;> simp only [duckUn, reduceCtorEq] at hd
        rename_i g
        split at hd
        · rename_i hc
          refine callExtra_of_at (o := "on_domain_error") (by cases e <;> cases g <;> decide) ?_
          simp [optionScope, Functions.Ctor.issue, UnFn.issueAll, UnFn.issue, domainIssue, hc.2]
        · cases hd
    | _ => exact .inl (raiseIf_ok h)
  · -- Each deviation, with the option whose scope it is in.
    have hfl : ∀ {a b : Int}, f.onFloats = true →
        (duckBin ⟨e, true⟩ f a b).getD (Profile.reference.bin f (.float a) (.float b)) = .ok x →
        x = f.apply (.float a) (.float b) ∨
          CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.float a, .float b] := by
      intro a b hf h
      cases hd : duckBin ⟨e, true⟩ f a b with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        right
        have nanC : nanCase f a b = true → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "nan_creation" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.float a, .float b] := fun hn hx => callExtra_of_at hx (by simp [optionScope, hn])
        have dom : (f.issue (.float a) (.float b)) = some .domain → extraAtB
            (Profile.duckdb.table ⟨e, true⟩) (.bin f) "on_domain_error" = true →
            CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.float a, .float b] :=
          fun hi hx => callExtra_of_at hx (by
            simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
        have zero : FloatCode.canon b = 0 → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "on_division_by_zero" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.float a, .float b] := fun hb hx => callExtra_of_at hx (by
            simp [optionScope, divisorZero, hb])
        cases f <;> simp only [BinFn.onFloats, Bool.false_eq_true] at hf <;>
          simp only [duckBin] at hd
        case fadd | fsub | fmul =>
          split at hd
          · exact nanC (by assumption) (by cases e <;> decide)
          · cases hd
        case fdiv =>
          split at hd
          · exact zero (by assumption) (by cases e <;> decide)
          · split at hd
            · exact nanC (by assumption) (by cases e <;> decide)
            · cases hd
        case fmod =>
          split at hd
          · rename_i hb
            exact callExtra_of_at (o := "nan_creation") (by cases e <;> decide)
              (by simp [optionScope, hb])
          · split at hd
            · exact nanC (by assumption) (by cases e <;> decide)
            · cases hd
        case fpow =>
          split at hd
          · exact dom (by simp_all [BinFn.issue]) (by cases e <;> decide)
          · split at hd
            · rename_i hn hn'
              exact dom (by simp [BinFn.issue, nanIssue, hn', Bool.not_eq_true _ |>.mp hn])
                (by cases e <;> decide)
            · cases hd
        case fatan2 =>
          split at hd
          · rename_i hz
            obtain ⟨rfl, rfl⟩ := hz
            exact dom (by simp [BinFn.issue, domainIssue, atan2?, FloatCode.canon_zero])
              (by cases e <;> decide)
          · split at hd
            · rename_i _ hz
              exact dom (by simp [BinFn.issue, domainIssue, atan2?, hz.1, hz.2]) (by cases e <;> decide)
            · cases hd
    have hint : ∀ {a b : Int}, f.onFloats = false →
        (duckBin ⟨e, true⟩ f a b).getD (Profile.reference.bin f (.int a) (.int b)) = .ok x →
        x = f.apply (.int a) (.int b) ∨
          CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f) [.int a, .int b] := by
      intro a b hnf h
      cases hd : duckBin ⟨e, true⟩ f a b with
      | none => rw [hd] at h; exact .inl (raiseIf_ok h)
      | some o =>
        rw [hd] at h
        simp only [Option.getD] at h
        have zero : b = 0 → extraAtB (Profile.duckdb.table ⟨e, true⟩) (.bin f)
            "on_division_by_zero" = true → CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin f)
              [.int a, .int b] := fun hb hx => callExtra_of_at hx (by
            subst hb; simp [optionScope, divisorZero])
        cases f
        case idiv =>
          simp only [duckBin] at hd
          split at hd
          · rename_i hb
            cases hd; cases e <;> simp only [duckZero, reduceCtorEq, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at h
            exact .inr (zero hb (by decide))
          · cases hd
        case imod =>
          simp only [duckBin] at hd
          split at hd
          · rename_i hb
            cases hd; cases e <;> simp only [duckZero, reduceCtorEq, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at h
            exact .inr (zero hb (by decide))
          · split at hd
            · cases hd; simp at h
            · cases hd
        case bit g =>
          have sh : CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] →
              x = (BinFn.bit g).apply (.int a) (.int b) ∨
                CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] := .inr
          cases g with
          | shl => exact sh (callExtra_of_at (o := "shift_range") (by cases e <;> decide)
              (by simp [optionScope]))
          | shr => exact sh (callExtra_of_at (o := "shift_range") (by cases e <;> decide)
              (by simp [optionScope]))
          | _ => simp [duckBin] at hd
        all_goals first
          | (simp [BinFn.onFloats] at *; done)
          | simp [duckBin] at hd
    simp only [Profile.duckdb] at h
    cases v <;> cases w <;> simp only at h <;> try exact .inl (raiseIf_ok h)
    case float.float a b =>
      split at h
      · exact hfl (by assumption) h
      · exact .inl (raiseIf_ok h)
    case int.int a b =>
      split at h
      · exact .inl (raiseIf_ok h)
      · exact hint (by simp_all) h

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
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (by decide) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (by decide))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_div_trunc a hb]
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (by decide))
    · rename_i hb; left; simp only [BinFn.apply, hb, ↓reduceIte]; rw [Polars.int_mod_trunc a hb]
  · rename_i a b
    split
    · rename_i hn
      right
      -- `power` has no `nan_creation`: its NaN is a domain error's.
      by_cases hp : f = .fpow
      · subst hp
        refine callExtra_of_at (o := "on_domain_error") (by decide) ?_
        have : BinFn.issue .fpow (.float a) (.float b) = some .domain := by
          simp only [BinFn.issue, nanIssue, hn]; split <;> rfl
        simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, this]
      · refine callExtra_of_at (o := "nan_creation") ?_ (by simp [optionScope, hn])
        cases f <;> simp [nanCase] at hn <;> first | decide | exact absurd rfl hp
    · exact .inl rfl
  · exact .inl rfl

/-- DuckDB with IEEE operations (`ieee_floating_point_ops`, the default),
through its lowering (`Lowering.duckdb`, written for the default settings). -/
def Engine.duckdb (s : DuckDBSettings) (hs : s.ieeeOps = true) : Engine where
  name := "duckdb"
  profile := Profile.duckdb s
  table := Profile.duckdb.table s
  obs := Profile.duckdb.obs
  lower r := some (Lowering.duckdb.lowerRel r)
  impl := (Profile.duckdb s).okImpl
  within := Profile.okImpl_within (Profile.duckdb_withinOk hs)

/-- Polars, as the translation writes the plan (`Polars.written`). -/
def Engine.polars : Engine where
  name := "polars"
  profile := Profile.polars
  table := Profile.polars.table
  obs := Profile.polars.obs
  lower := some
  impl := Polars.written
  within := Polars.written_within

/-- Spark under ANSI: the reference's functions (`Profile.spark`), its own
choices. -/
def Engine.spark : Engine where
  name := "spark"
  profile := Profile.spark
  table := Profile.spark.table
  obs := Profile.spark.obs
  lower := some
  impl := Impl.lean
  within := Impl.lean_within _

-- No engine's certificate is empty: each but the reference has rows that
-- are not theorems (so `Refines` is a real hypothesis, which `#print axioms`
-- cannot show).
#guard !(Engine.duckdb {} rfl).testedRows.isEmpty && !Engine.polars.testedRows.isEmpty &&
  !Engine.spark.testedRows.isEmpty && Engine.reference.testedRows.isEmpty

end Substrait
