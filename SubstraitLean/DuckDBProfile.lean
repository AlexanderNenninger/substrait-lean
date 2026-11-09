import SubstraitLean.ProfileImpl
import SubstraitLean.Knowledge

/-!
# DuckDB's profile (#185)

What DuckDB's scalar functions give, under its settings, as a diff against
the reference (`Profile.duckdb`, from `characterization/duckdb/facts/`), the
profile as the SQL printer writes it (`Profile.duckdbWritten`), and the
soundness of running a verified plan on it (`Rel.duckdb_sound`). Polars's
and Spark's profiles have their own modules (`PolarsProfile.lean`,
`SparkProfile.lean`); the core (`Profile.lean`, `Allowed`, `AllowedNear`)
does not import this one.
-/

namespace Substrait

/-- The DuckDB settings its profile depends on. -/
structure DuckDBSettings where
  /-- `error_on_division_by_zero`, on by default since DuckDB 2.0: integer
  `//` and `%` by zero raise, else give NULL (`characterization/duckdb/facts/`,
  R2, R3). Doubles follow it only with `ieeeOps` off. -/
  errorOnDivZero : Bool := true
  /-- `ieee_floating_point_ops`, on by default: doubles follow IEEE 754, so
  `x / 0.0` is `±∞` or NaN, `x % 0.0` NaN, and the elementary functions are NaN
  outside their domains (R5, R15). Off, these raise. -/
  ieeeOps : Bool := true

/-- Integer `//` and `%`, and double `/` and `%`. -/
def BinFn.divides : BinFn → Bool
  | .idiv | .imod | .fdiv | .fmod => true
  | _ => false

/-- `x / 0.0` in IEEE arithmetic: NaN for `0.0` and NaN, else ±∞ by the
dividend's sign. -/
def ieeeDivZero (x : Int) : Int :=
  if x = 0 ∨ x = FloatCode.nan then FloatCode.nan
  else if 0 < x then FloatCode.posInf else FloatCode.negInf

/-- DuckDB's `/` of doubles, IEEE 754's: by zero `±∞` by the dividend's
sign, NaN for `0` and NaN (R5, `ieeeDivZero`); `±∞ / ±∞` is NaN. The NaN
cases are stated, not left to native floats, so that proofs can see them. -/
def duckDivide (x y : Int) : Int :=
  if y = 0 then ieeeDivZero x
  else if isInfCode x && isInfCode y then FloatCode.nan
  else FloatCode.fdiv x y

/-- DuckDB's `%` of doubles: NaN by zero (R4) and for an infinite dividend,
else C's `fmod`. -/
def duckMod (x y : Int) : Int :=
  if y = 0 ∨ isInfCode x then FloatCode.nan else FloatCode.fmod x y

/-- A logarithm (`ln`, `log10`, `log2`)? -/
def FMath.isLog : FMath → Bool
  | .ln | .log10 | .log2 => true
  | _ => false

/-- DuckDB's elementary function of a double (DuckDB 2.0): the function in its
domain (`FMath.apply`); outside it, `-∞` for a logarithm of zero and NaN
otherwise (`sqrt(-1)`, `asin(2)`, `sin(±∞)`). -/
def duckElementary (f : FMath) (x : Int) : Int :=
  match f.apply x with
  | some r => r
  | none => if f.isLog ∧ x = 0 then FloatCode.negInf else FloatCode.nan

/-- DuckDB's `power(-∞, y)` for a finite `y` that is not an integer
(`negInfPow`): IEEE 754's `+∞` for `y > 0` and `0` for `y < 0`, under any
`ieee_floating_point_ops` (probed on DuckDB 2.0.0, fact duckdb-R15-power-neginf). -/
def duckNegInfPow (y : Int) : Int := if 0 < y then FloatCode.posInf else 0

/-- DuckDB's `power` of doubles: NaN where IEEE 754 gives it (a negative
finite base to a finite power that is not an integer, `nanCase`), else the
native power (`0 ^ -1` is `∞`). -/
def duckPower (x y : Int) : Int :=
  if negInfPow x y then duckNegInfPow y
  else if nanCase .fpow x y then FloatCode.nan else FloatCode.lift₂ Float.pow x y

/-- A zero divisor under `error_on_division_by_zero` (integers) or with
`ieeeOps` off (doubles): an error, or NULL. -/
def duckZero (s : DuckDBSettings) : Outcome :=
  if s.errorOnDivZero then .error .divByZero else .ok .null

/-- DuckDB's `<<` (R15): a negative shift or a negative operand raises, a shift
of 64 or more is `0` for `0` and raises otherwise, and so does shifting out a
bit; Substrait's `shift_left` drops them. -/
def duckShl (a b : Int) : Outcome :=
  if b < 0 ∨ a < 0 then .error .domain
  else if 64 ≤ b then (if a = 0 then .ok (.int 0) else .error .domain)
  else if 2 ^ 63 ≤ a * 2 ^ b.toNat then .error .overflow
  else .ok (.int (a * 2 ^ b.toNat))

/-- The functions of doubles among `duckBin`'s; the others take integers. -/
def BinFn.onFloats : BinFn → Bool
  | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow | .fatan2 => true
  | _ => false

/-- **DuckDB's binary functions** on non-NULL arguments where they differ from
the reference (`none`: as the reference), from the probes of
`characterization/duckdb/probes.json` (FACTS R15). -/
def duckBin (s : DuckDBSettings) : BinFn → Int → Int → Option Outcome
  | .idiv, _, b => if b = 0 then some (duckZero s) else none
  -- `MIN % -1` overflows in DuckDB, as `MIN // -1` does (R3).
  | .imod, a, b =>
    if b = 0 then some (duckZero s)
    else if b = -1 ∧ a = -2 ^ 63 then some (.error .overflow) else none
  -- `∞ - ∞`, `0 · ∞`, `∞ / ∞`: NaN under any setting.
  | .fadd, a, b => if nanCase .fadd a b then some (.ok (.float FloatCode.nan)) else none
  | .fsub, a, b => if nanCase .fsub a b then some (.ok (.float FloatCode.nan)) else none
  | .fmul, a, b => if nanCase .fmul a b then some (.ok (.float FloatCode.nan)) else none
  | .fdiv, a, b =>
    if b = 0 then some (if s.ieeeOps then .ok (.float (ieeeDivZero a)) else duckZero s)
    else if nanCase .fdiv a b then some (.ok (.float FloatCode.nan)) else none
  | .fmod, a, b =>
    if b = 0 then some (if s.ieeeOps then .ok (.float FloatCode.nan) else duckZero s)
    else if nanCase .fmod a b then some (.ok (.float FloatCode.nan)) else none
  -- `(-∞) ^ y` for a finite `y` that is not an integer: IEEE's `+∞` or `0`,
  -- under any setting, where the reference raises (`negInfPow`).
  | .fpow, a, b =>
    if negInfPow a b then some (.ok (.float (duckNegInfPow b)))
    else if s.ieeeOps then (if nanCase .fpow a b then some (.ok (.float FloatCode.nan)) else none)
    -- Without IEEE operations `0 ^ y` raises for a negative `y` (the reference: `∞`).
    else if a = 0 ∧ b < 0 then some (.error .domain) else none
  | .fatan2, a, b => if a = 0 ∧ b = 0 then some (.ok (.float 0)) else none
  | .bit .shl, a, b => some (duckShl a b)
  | .bit .shr, _, b => if b < 0 ∨ 64 ≤ b then some (.ok (.int 0)) else none
  | _, _, _ => none

/-- **DuckDB's unary functions** where they differ from the reference: with
`ieeeOps`, an elementary function outside its domain is NaN, or `-∞` for a
logarithm of zero (R15). -/
def duckUn (s : DuckDBSettings) : UnFn → Int → Option Outcome
  | .fmath f, x =>
    if s.ieeeOps ∧ f.apply x = none then some (.ok (.float (duckElementary f x))) else none
  | _, _ => none

/-- **DuckDB's profile**, as a diff against the reference (`duckBin`,
`duckUn`): what DuckDB 2.0 computes under the settings `s`, as probed
(`sverify_dev.probe`). Functions not probed are taken to be the reference's. -/
def Profile.duckdb (s : DuckDBSettings) : Profile where
  un f v := match v with
    | .float x => (duckUn s f x).getD (Profile.reference.un f v)
    | _ => Profile.reference.un f v
  bin f v w := match v, w with
    | .float x, .float y =>
      if f.onFloats then (duckBin s f x y).getD (Profile.reference.bin f v w)
      else Profile.reference.bin f v w
    | .int x, .int y =>
      if f.onFloats then Profile.reference.bin f v w
      else (duckBin s f x y).getD (Profile.reference.bin f v w)
    | _, _ => Profile.reference.bin f v w

/-- DuckDB's `%` by a positive divisor is the reference's (the wrap-around
schema computes with it, `LoweringSearch.duckdbSchemas`). -/
theorem Profile.duckdb_imod_pos (s : DuckDBSettings) (a m : Int) (hm : 0 < m) :
    (Profile.duckdb s).bin .imod (.int a) (.int m) = Profile.reference.bin .imod (.int a) (.int m) := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ -1 := by omega
  simp [Profile.duckdb, duckBin, BinFn.onFloats, h0, h1]

/-- Where DuckDB raises though the reference gives a value (R15): `MIN % -1`,
and `<<` of a negative number or shifting out a bit. Even without guards, the
SQL printer writes these out (`sverify.sql.duckdb`: `int_mod`, `bitwise`). -/
def BinFn.duckdbWritten : BinFn → Bool
  | .imod | .bit .shl => true
  | _ => false

/-- DuckDB's profile with the functions of `BinFn.duckdbWritten` as the SQL
printer writes them: the reference's. -/
def Profile.duckdbWritten (s : DuckDBSettings) : Profile where
  un := (Profile.duckdb s).un
  bin f := if f.duckdbWritten then Profile.reference.bin f else (Profile.duckdb s).bin f

/-- **DuckDB, as the SQL printer writes it, agrees with the reference
wherever the reference does not raise**, with IEEE operations on (DuckDB's
default). Elsewhere it differs only where the reference raises: `∞ - ∞` is
NaN, `x / 0.0` is `±∞`, `sqrt(-1)` NaN. (Without IEEE operations, `0 ^ -1`
raises in DuckDB and is `∞` in the reference.) -/
theorem Profile.duckdbWritten_faithful (s : DuckDBSettings) (hs : s.ieeeOps = true) :
    (Profile.duckdbWritten s).impl.Faithful := by
  refine ⟨fun f v h => ?_, fun f v w h => ?_⟩
  · have hr := Profile.reference_faithful.1 f v h
    simp only [Profile.impl, Profile.duckdbWritten, Profile.duckdb] at hr ⊢
    split
    · rename_i x
      cases f <;> simp only [duckUn] <;> (try split) <;> simp_all [UnFn.issue, domainIssue]
    · exact hr
  · have hr := Profile.reference_faithful.2 f v w h
    simp only [Profile.impl, Profile.duckdbWritten] at hr ⊢
    split
    · exact hr
    · rename_i hw
      simp only [Profile.duckdb]
      split
      case h_3 => exact hr
      all_goals
        cases f <;> simp only [duckBin, BinFn.duckdbWritten, BinFn.onFloats, Bool.false_eq_true,
          ite_true, ite_false] at hw ⊢ <;>
          (try split) <;> (try split) <;> (try split) <;>
          simp_all [BinFn.issue, nanIssue, domainIssue, BitOp.apply, atan2?, FloatCode.canon_zero] <;>
          first | omega | (split at h <;> simp at h)

/-- **A verified plan runs correctly on DuckDB.** When `Rel.mayIssues` reports
nothing but integer `SUM`s that may wrap (which keep their check), on every
catalog that satisfies the preconditions `A`, `F`, evaluating the plan with
DuckDB's functions gives `Rel.eval`'s rows, under DuckDB's IEEE operations
(the default), provided the plan's windows read fewer than `2⁶²` rows (the
size hypothesis, `Rel.Small`). Trusted: that `Profile.duckdb` is DuckDB's
(probed: `characterization/duckdb/probes.json`), that the SQL printer is
faithful, writing out `MIN % -1` and `<<` (`Profile.duckdbWritten`), and that
DuckDB's aggregates are Lean's (`AggFn.apply`): a profile gives only the
scalar functions. For a double `SUM` or `AVG` that last part does not hold in
general: DuckDB merges partial sums in finishing order and adds a constant
vector as one `fl(k · x)` (#633), so on those the conclusion holds of the
model, and what DuckDB gives is within #85's bound of it (`Profile.duckdb.table`'s
`sum_order` row, `approx`, proved in `float-bounds` as `StdModel.epsilon_sum_cr`
against the reference's correctly rounded sum, D25). -/
theorem Rel.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat (Profile.duckdbWritten s).impl = r.eval cat :=
  Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm (Profile.duckdbWritten_faithful s hieee)

/-- `Rel.duckdb_sound` on one hypothesis. -/
theorem Knowledge.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat) {r : Rel} (hwf : r.WF cat)
    (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat K.cols K.facts (K.windows cat) false).all (·.1.assumed) = true) :
    r.eval cat (Profile.duckdbWritten s).impl = r.eval cat :=
  Rel.duckdb_sound s hieee hcat hK.cols hK.facts (hK.windows hcat) hwf hsmall hs hm

end Substrait
