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

* `Engine.spark` takes its profile's functions where they do not raise
  (`Profile.spark_withinOk`), as DuckDB's does;
  `Engine.duckdb` (IEEE operations, `ieee_floating_point_ops` on, the
  default) takes `impl := profile.okImpl` (`Profile.duckdb_withinOk`);
  `Engine.polars` takes the functions of the written plan (`Polars.written`,
  `Polars.written_within`).
-/

namespace Substrait

/-- `extraAtB t c o` for a pair of `ps`, from one check of them all. Each
`decide` of `extraAtB` evaluates the table anew, so a proof that needs many
pairs decides its list once (`Profile.duckdb_extras`). -/
theorem extraAt_of_all {t : ProfileTable} {ps : List (Functions.Ctor × String)}
    (h : (ps.all fun p => extraAtB t p.1 p.2) = true) {c : Functions.Ctor} {o : String}
    (hm : (c, o) ∈ ps) : extraAtB t c o = true :=
  List.all_eq_true.mp h _ hm

/-- The options at which `Profile.duckdb_withinOk` uses DuckDB's table. -/
def Profile.duckdbExtras : List (Functions.Ctor × String) :=
  FMath.all.map (fun g => (.un (.fmath g), "on_domain_error")) ++
    [(.un .fround, "round_zero_sign"), (.un .fceil, "round_zero_sign"),
     (.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"), (.bin .fmul, "nan_creation"),
     (.bin .fdiv, "on_division_by_zero"), (.bin .fdiv, "nan_creation"),
     (.bin .fmod, "nan_creation"), (.bin .fpow, "on_domain_error"),
     (.bin .fatan2, "on_domain_error"), (.bin (.bit .shl), "shift_range"),
     (.bin (.bit .shr), "shift_range")]

theorem Profile.duckdb_extras (e : Bool) :
    (Profile.duckdbExtras.all fun p => extraAtB (Profile.duckdb.table ⟨e, true⟩) p.1 p.2) = true := by
  cases e <;> decide

/-- The options at which `Polars.written_within` uses Polars's table. -/
def Profile.polarsExtras : List (Functions.Ctor × String) :=
  [(.bin .add, "overflow"), (.bin .sub, "overflow"), (.bin .mul, "overflow"),
   (.bin .idiv, "on_division_by_zero"), (.bin .imod, "on_division_by_zero"),
   (.bin .fpow, "on_domain_error"), (.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"),
   (.bin .fmul, "nan_creation"), (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation")]

theorem Profile.polars_extras :
    (Profile.polarsExtras.all fun p => extraAtB Profile.polars.table p.1 p.2) = true := by
  decide

/-- The options at which `Profile.spark_withinOk` uses Spark's table. -/
def Profile.sparkExtras : List (Functions.Ctor × String) :=
  FMath.all.map (fun g => (.un (.fmath g), "on_domain_error")) ++
    [(.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"), (.bin .fmul, "nan_creation"),
     (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation"), (.bin .fpow, "on_domain_error"),
     (.bin .fpow, "pow_one_inf"), (.un .ffloor, "float_to_int"), (.un .fceil, "float_to_int"),
     (.bin (.bit .shl), "shift_range"), (.bin (.bit .shr), "shift_range")]

theorem Profile.spark_extras :
    (Profile.sparkExtras.all fun p => extraAtB Profile.spark.table p.1 p.2) = true := by
  decide


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
        case fmath g =>
          split at hd
          · rename_i hc
            refine callExtra_of_at (o := "on_domain_error") (by cases g <;> exact extraAt_of_all (Profile.duckdb_extras _) (by decide)) ?_
            simp [optionScope, Functions.Ctor.issue, UnFn.issueAll, UnFn.issue, domainIssue, hc.2]
          · cases hd
        -- IEEE's `-0.0` where the reference's result is a zero (`round_zero_sign`).
        case fround | fceil =>
          split at hd
          · rename_i hc
            refine callExtra_of_at (o := "round_zero_sign") (extraAt_of_all (Profile.duckdb_extras _) (by decide)) ?_
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero, hc.2]
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
        -- IEEE division's NaN is its own value (D39).
        by_cases hi : f = .fdivIeee
        · subst hi; left
          simp only [duckBin] at h hd
          split at h
          · rename_i hn; cases h; simp only [BinFn.apply, fdiv_of_nanCase_ieee hn]
          · rename_i hn; simp [hn] at hd
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
        case fdivIeee => exact absurd rfl hi
        case fadd | fsub | fmul =>
          split at hd
          · exact nanC (by assumption) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
          · cases hd
        case fdiv =>
          split at hd
          · exact zero (by assumption) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
          · split at hd
            · exact nanC (by assumption) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
            · cases hd
        case fmod =>
          split at hd
          · rename_i hb
            exact callExtra_of_at (o := "nan_creation") (extraAt_of_all (Profile.duckdb_extras _) (by decide))
              (by simp [optionScope, hb])
          · split at hd
            · exact nanC (by assumption) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
            · cases hd
        case fpow =>
          split at hd
          · exact dom (by simp_all [BinFn.issue]) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
          · split at hd
            · rename_i hn hn'
              exact dom (by simp [BinFn.issue, nanIssue, hn', Bool.not_eq_true _ |>.mp hn])
                (extraAt_of_all (Profile.duckdb_extras _) (by decide))
            · cases hd
        case fatan2 =>
          split at hd
          · rename_i hz
            obtain ⟨rfl, rfl⟩ := hz
            exact dom (by simp [BinFn.issue, domainIssue, atan2?, FloatCode.canon_zero])
              (extraAt_of_all (Profile.duckdb_extras _) (by decide))
          · split at hd
            · rename_i _ hz
              exact dom (by simp [BinFn.issue, domainIssue, atan2?, hz.1, hz.2]) (extraAt_of_all (Profile.duckdb_extras _) (by decide))
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
            -- NULL for a zero divisor only with `error_on_division_by_zero` off.
            exact .inr (zero hb (by decide))
          · cases hd
        case imod =>
          simp only [duckBin] at hd
          split at hd
          · rename_i hb
            cases hd; cases e <;> simp only [duckZero, reduceCtorEq, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at h
            -- NULL for a zero divisor only with `error_on_division_by_zero` off.
            exact .inr (zero hb (by decide))
          · split at hd
            · cases hd; simp at h
            · cases hd
        case bit g =>
          have sh : CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] →
              x = (BinFn.bit g).apply (.int a) (.int b) ∨
                CallExtra (Profile.duckdb.table ⟨e, true⟩) (.bin (.bit g)) [.int a, .int b] := .inr
          cases g with
          | shl => exact sh (callExtra_of_at (o := "shift_range") (extraAt_of_all (Profile.duckdb_extras _) (by decide))
              (by simp [optionScope]))
          | shr => exact sh (callExtra_of_at (o := "shift_range") (extraAt_of_all (Profile.duckdb_extras _) (by decide))
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
      case h_8 | h_9 =>
        split at hs
        · cases hs
        · exact .inr (callExtra_of_at (o := "shift_range") (extraAt_of_all Profile.spark_extras (by decide)) (by simp [optionScope]))
      case h_10 => cases hs

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
      case h_7 => simp [BinFn.sparkWritten] at hw
      case h_8 | h_9 =>
        split at hs
        · cases hs
        · rename_i hr; simp [BinFn.issue, domainIssue, BitOp.apply, hr] at h
      case h_10 => cases hs

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

-- No engine's certificate is empty: each but the reference has rows that
-- are not theorems (so `Refines` is a real hypothesis, which `#print axioms`
-- cannot show).
#guard letI := Boxes.Ambient.none; !(Engine.duckdb {} rfl).testedRows.isEmpty && !Engine.polars.testedRows.isEmpty &&
  !Engine.spark.testedRows.isEmpty && Engine.reference.testedRows.isEmpty

end Substrait
