import SubstraitLean.Profile

/-!
# What DuckDB's SQL means (#268)

The SQL lift (`sverify.sql_lift`) reads DuckDB SQL into a Substrait plan, with
DuckDB's own semantics (`semantics="duckdb"`) or the reference's
(`semantics="reference"`). This file states, for each DuckDB function at one
signature (`DuckFn`), what it means under each: the **target** the lift's
generator (`SubstraitLean/LiftSearch.lean`) searches towards. For each, it
finds a Substrait expression that the parser (`Parse.parseExpr`) reads as the
same function, and proves it.

`Profile.duckdb` is a different thing: how DuckDB evaluates the *canonical*
functions. This is how DuckDB's *SQL surface* reads: `/` on integers divides
as doubles, `log` is base 10.

Trusted, as a profile is: that this is what DuckDB computes. It follows
`characterization/duckdb/FACTS.md` and the choices of `sql_lift.py`'s
hand-written `DUCKDB` profile it replaces; oracle A (#242) tests it against
the engine. With `semantics="reference"` a function means the reference's
function at the same types (an error where DuckDB would give `±∞` or NaN).

This first slice covers `/`, `%` of doubles and `log`.
-/

namespace Substrait

/-- Whose semantics a lifted plan has (`sv.sql(..., semantics=...)`). -/
inductive Semantics where
  | duckdb | reference
  deriving Repr, DecidableEq, Inhabited

def Semantics.name : Semantics → String
  | .duckdb => "duckdb" | .reference => "reference"

/-- A DuckDB SQL type of the lifted functions' arguments and results. -/
inductive DuckType where
  | bigint | double
  deriving Repr, DecidableEq, Inhabited

/-- Values of the type: `NULL` or an integer (for a `DOUBLE`, its code,
`SubstraitLean/Float.lean`). -/
def DuckType.Has : DuckType → Value → Prop
  | _, .null => True
  | _, .int _ => True
  | _, _ => False

/-- Values of the types, one each. -/
def DuckType.HaveAll : List DuckType → List Value → Prop
  | [], [] => True
  | t :: ts, x :: xs => t.Has x ∧ HaveAll ts xs
  | _, _ => False

/-- The Substrait type. -/
def DuckType.substrait : DuckType → String
  | .bigint => "i64" | .double => "fp64"

/-- A DuckDB SQL function at one signature. -/
inductive DuckFn where
  /-- `a / b` of `BIGINT`s, a `DOUBLE`: DuckDB divides as doubles (F1). -/
  | divInt
  /-- `a / b` of `DOUBLE`s. -/
  | divDouble
  /-- `a % b` of `DOUBLE`s: C's `fmod` (R4). -/
  | modDouble
  /-- `log(x)` of a `DOUBLE`: the logarithm to base 10. -/
  | log
  deriving Repr, DecidableEq, Inhabited

/-- The function as DuckDB writes it, with its argument types. -/
def DuckFn.sql : DuckFn → String
  | .divInt => "BIGINT / BIGINT" | .divDouble => "DOUBLE / DOUBLE"
  | .modDouble => "DOUBLE % DOUBLE" | .log => "log(DOUBLE)"

def DuckFn.args : DuckFn → List DuckType
  | .divInt => [.bigint, .bigint]
  | .divDouble | .modDouble => [.double, .double]
  | .log => [.double]

def DuckFn.result : DuckFn → DuckType
  | _ => .double

/-! The special codes' order, which the generated proofs compare with. -/

theorem FloatCode.negInf_lt_zero : FloatCode.negInf < 0 := by
  have := FloatCode.maxMag_pos
  simp [FloatCode.negInf, FloatCode.ofMag, FloatCode.infMag, FloatCode.nanMag]
  omega

theorem FloatCode.zero_lt_posInf : 0 < FloatCode.posInf := by
  have := FloatCode.maxMag_pos
  simp [FloatCode.posInf, FloatCode.ofMag, FloatCode.infMag]
  omega

theorem FloatCode.posInf_lt_nan : FloatCode.posInf < FloatCode.nan := by
  have := FloatCode.maxMag_pos
  simp [FloatCode.posInf, FloatCode.nan, FloatCode.ofMag, FloatCode.infMag, FloatCode.nanMag]

theorem FloatCode.ofInt_ne_posInf (i : Int) : FloatCode.ofInt i ≠ FloatCode.posInf := by
  have := FloatCode.ofInt_bounds i; omega

theorem FloatCode.ofInt_ne_negInf (i : Int) : FloatCode.ofInt i ≠ FloatCode.negInf := by
  have := FloatCode.ofInt_bounds i; omega

/-! Lemmas the generated proofs compute with (`generate_lift … using`). -/

theorem DuckDBSQL.ref_itof (i : Int) :
    Profile.reference.un .itof (.int i) = .ok (.int (FloatCode.ofInt i)) := rfl

theorem DuckDBSQL.ref_fmath_int (f : FMath) (c : Int) :
    Profile.reference.un (.fmath f) (.int c) =
      match f.apply c with | some r => .ok (.int r) | none => .error .domain := by
  cases h : f.apply c <;>
    simp [Profile.reference, raiseIf, UnFn.issue, UnFn.apply, domainIssue, h, Issue.isError]

theorem DuckDBSQL.ref_fmath_null (f : FMath) : Profile.reference.un (.fmath f) .null = .ok .null := rfl

theorem DuckDBSQL.ite_or {α} {p q : Prop} [Decidable p] [Decidable q] (a b : α) :
    (if p ∨ q then a else b) = if p then a else if q then a else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- A double divided by zero in DuckDB: `±∞` by the dividend's sign, NaN for
`0` and NaN (R5, `ieeeDivZero`). -/
def duckDivide (x y : Int) : Int :=
  if y = 0 then ieeeDivZero x else FloatCode.lift₂ (· / ·) x y

/-- DuckDB's `%` of doubles: NaN by zero (R4), else C's `fmod`. -/
def duckMod (x y : Int) : Int :=
  if y = 0 then FloatCode.nan else FloatCode.fmod x y

/-- DuckDB's `log`: `-∞` at zero, NaN below it, else base 10. -/
def duckLog (x : Int) : Int :=
  match FMath.apply .log10 x with
  | some r => r
  | none => if x = 0 then FloatCode.negInf else FloatCode.nan

/-- What the function gives for its arguments, under the semantics. `NULL`
in, `NULL` out. -/
def DuckFn.eval : Semantics → DuckFn → List Value → Outcome
  | .duckdb, .divInt, [.int a, .int b] =>
    .ok (.int (duckDivide (FloatCode.ofInt a) (FloatCode.ofInt b)))
  | .duckdb, .divDouble, [.int a, .int b] => .ok (.int (duckDivide a b))
  | .duckdb, .modDouble, [.int a, .int b] => .ok (.int (duckMod a b))
  | .duckdb, .log, [.int a] => .ok (.int (duckLog a))
  | .reference, .divInt, [.int a, .int b] =>
    Profile.reference.bin .fdiv (.int (FloatCode.ofInt a)) (.int (FloatCode.ofInt b))
  | .reference, .divDouble, [a, b] => Profile.reference.bin .fdiv a b
  | .reference, .modDouble, [a, b] => Profile.reference.bin .fmod a b
  | .reference, .log, [a] => Profile.reference.un (.fmath .log10) a
  | _, _, _ => .ok .null

end Substrait
