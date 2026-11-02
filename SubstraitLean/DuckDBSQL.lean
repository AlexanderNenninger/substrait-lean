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

Covered so far: `/`, `%` of doubles, `log`, `sign`, `greatest` and `least`,
casts between `BIGINT` and `DOUBLE`, and the aggregate `avg` of `BIGINT`s
(`DuckAgg`). A function the model cannot state
under a semantics is refused (`DuckFn.refused`), with the reason.
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
  | bigint | double | tinyint
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
  | .bigint => "i64" | .double => "fp64" | .tinyint => "i8"

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
  /-- `sign(x)` of a `BIGINT` or a `DOUBLE`: a `TINYINT`, `-1`, `0` or `1`;
  `0` for NaN. -/
  | signBigint | signDouble
  /-- `greatest(x, y)` and `least(x, y)`: DuckDB skips `NULL`s. -/
  | greatestBigint | leastBigint | greatestDouble | leastDouble
  /-- `CAST(x AS BIGINT)` of a `DOUBLE`, and `CAST(x AS DOUBLE)` of a `BIGINT`. -/
  | castDoubleBigint | castBigintDouble
  deriving Repr, DecidableEq, Inhabited

def DuckFn.all : List DuckFn :=
  [.divInt, .divDouble, .modDouble, .log, .signBigint, .signDouble, .greatestBigint, .leastBigint,
   .greatestDouble, .leastDouble, .castDoubleBigint, .castBigintDouble]

theorem DuckFn.mem_all (f : DuckFn) : f ∈ DuckFn.all := by cases f <;> decide

/-- The function as DuckDB writes it, with its argument types. -/
def DuckFn.sql : DuckFn → String
  | .divInt => "BIGINT / BIGINT" | .divDouble => "DOUBLE / DOUBLE"
  | .modDouble => "DOUBLE % DOUBLE" | .log => "log(DOUBLE)"
  | .signBigint => "sign(BIGINT)" | .signDouble => "sign(DOUBLE)"
  | .greatestBigint => "greatest(BIGINT, BIGINT)" | .leastBigint => "least(BIGINT, BIGINT)"
  | .greatestDouble => "greatest(DOUBLE, DOUBLE)" | .leastDouble => "least(DOUBLE, DOUBLE)"
  | .castDoubleBigint => "CAST(DOUBLE AS BIGINT)" | .castBigintDouble => "CAST(BIGINT AS DOUBLE)"

def DuckFn.args : DuckFn → List DuckType
  | .divInt | .greatestBigint | .leastBigint => [.bigint, .bigint]
  | .divDouble | .modDouble | .greatestDouble | .leastDouble => [.double, .double]
  | .log | .signDouble | .castDoubleBigint => [.double]
  | .signBigint | .castBigintDouble => [.bigint]

def DuckFn.result : DuckFn → DuckType
  | .signBigint | .signDouble => .tinyint
  | .greatestBigint | .leastBigint | .castDoubleBigint => .bigint
  | _ => .double

/-- Functions the model cannot state under the semantics, and why: the lift
refuses them (`sverify.sql_lift` raises `Unsupported`). -/
def DuckFn.refused : Semantics → DuckFn → Option String
  | .duckdb, .castDoubleBigint => some "DuckDB rounds half to even, which the model's casts \
      (they truncate) cannot state; use semantics='reference', or round() first"
  | _, _ => none

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

theorem DuckDBSQL.ref_itof_null : Profile.reference.un .itof .null = .ok .null := rfl

theorem FloatCode.ofInt_ne_nan (i : Int) : FloatCode.ofInt i ≠ FloatCode.nan := by
  have := FloatCode.ofInt_bounds i; have := FloatCode.posInf_lt_nan; omega

theorem DuckDBSQL.ref_fdiv_int (a b : Int) :
    Profile.reference.bin .fdiv (.int a) (.int b) =
      if b = 0 then .error .divByZero else if nanCase .fdiv a b then .error .domain
      else .ok (.int (FloatCode.lift₂ (· / ·) a b)) := by
  by_cases hb : b = 0 <;> by_cases hn : nanCase .fdiv a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hb, hn, Issue.isError]

theorem DuckDBSQL.ref_fmod_int (a b : Int) :
    Profile.reference.bin .fmod (.int a) (.int b) =
      if b = 0 then .error .divByZero else if nanCase .fmod a b then .error .domain
      else .ok (.int (FloatCode.fmod a b)) := by
  by_cases hb : b = 0 <;> by_cases hn : nanCase .fmod a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hb, hn, Issue.isError]

theorem DuckDBSQL.ref_fdiv_null_l (y : Value) : Profile.reference.bin .fdiv .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fdiv_null_r (x : Value) : Profile.reference.bin .fdiv x .null = .ok .null := by
  cases x <;> rfl
theorem DuckDBSQL.ref_fmod_null_l (y : Value) : Profile.reference.bin .fmod .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fmod_null_r (x : Value) : Profile.reference.bin .fmod x .null = .ok .null := by
  cases x <;> rfl

theorem DuckDBSQL.apply_eq_int (a b : Int) : BinFn.apply .eq (.int a) (.int b) = .bool (decide (a = b)) := rfl
theorem DuckDBSQL.apply_lt_int (a b : Int) : BinFn.apply .lt (.int a) (.int b) = .bool (decide (a < b)) := rfl
theorem DuckDBSQL.apply_eq_null_l (y : Value) : BinFn.apply .eq .null y = .null := by cases y <;> rfl
theorem DuckDBSQL.apply_eq_null_r (x : Value) : BinFn.apply .eq x .null = .null := by cases x <;> rfl
theorem DuckDBSQL.apply_lt_null_l (y : Value) : BinFn.apply .lt .null y = .null := by cases y <;> rfl
theorem DuckDBSQL.apply_lt_null_r (x : Value) : BinFn.apply .lt x .null = .null := by cases x <;> rfl

theorem DuckDBSQL.ite_or {α} {p q : Prop} [Decidable p] [Decidable q] (a b : α) :
    (if p ∨ q then a else b) = if p then a else if q then a else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- DuckDB's `/` of doubles, IEEE 754's: by zero `±∞` by the dividend's
sign, NaN for `0` and NaN (R5, `ieeeDivZero`); `±∞ / ±∞` is NaN. The NaN
cases are stated, not left to native floats, so that proofs can see them. -/
def duckDivide (x y : Int) : Int :=
  if y = 0 then ieeeDivZero x
  else if isInfCode x && isInfCode y then FloatCode.nan
  else FloatCode.lift₂ (· / ·) x y

/-- DuckDB's `%` of doubles: NaN by zero (R4) and for an infinite dividend,
else C's `fmod`. -/
def duckMod (x y : Int) : Int :=
  if y = 0 ∨ isInfCode x then FloatCode.nan else FloatCode.fmod x y

/-- DuckDB's `log`: `-∞` at zero, NaN below it, else base 10. -/
def duckLog (x : Int) : Int :=
  match FMath.apply .log10 x with
  | some r => r
  | none => if x = 0 then FloatCode.negInf else FloatCode.nan

/-- `sign` of an integer, or of a double's code (codes are ordered as their
doubles; NaN's is the largest, and its sign is `0`). -/
def duckSign (x : Int) : Int := if x < 0 then -1 else if 0 < x then 1 else 0

/-- What the function gives for its arguments, under the semantics. `NULL`
in, `NULL` out, but for `greatest` and `least`, which skip `NULL`s. -/
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
  | _, .signBigint, [.int a] => .ok (.int (duckSign a))
  | _, .signDouble, [.int a] => .ok (.int (if a = FloatCode.nan then 0 else duckSign a))
  | _, .greatestBigint, [x, y] | _, .greatestDouble, [x, y] => .ok (match x, y with
    | .int a, .int b => .int (if a < b then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  | _, .leastBigint, [x, y] | _, .leastDouble, [x, y] => .ok (match x, y with
    | .int a, .int b => .int (if b < a then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  | .reference, .castDoubleBigint, [a] => Profile.reference.un .ftoi a
  | _, .castBigintDouble, [.int a] => .ok (.int (FloatCode.ofInt a))
  | _, _, _ => .ok .null

/-! ## Aggregates -/

/-- A DuckDB aggregate at one signature. -/
inductive DuckAgg where
  /-- `avg(x)` of a `BIGINT`: a `DOUBLE`. -/
  | avgBigint
  deriving Repr, DecidableEq, Inhabited

def DuckAgg.all : List DuckAgg := [.avgBigint]

def DuckAgg.sql : DuckAgg → String
  | .avgBigint => "avg(BIGINT)"

def DuckAgg.arg : DuckAgg → DuckType
  | .avgBigint => .bigint

def DuckAgg.result : DuckAgg → DuckType
  | .avgBigint => .double

/-- What the aggregate gives for its argument's values on a group's rows,
under the semantics. DuckDB's `avg` of integers sums them exactly (in 128
bits), then divides the sum, as a double, by their count: no rounding before
the end. The reference's is Substrait's `avg` of their conversions to doubles
(`AggFn.avg`), which rounds as it sums. Both are `NULL` without values. -/
def DuckAgg.eval : Semantics → DuckAgg → List Value → Value
  | .duckdb, .avgBigint, vs =>
    match vs.filter (· != .null) with
    | [] => .null
    | xs => .int (FloatCode.lift₂ (· / ·) (FloatCode.ofInt (intSum xs)) (FloatCode.ofInt xs.length))
  | .reference, .avgBigint, vs => AggFn.apply .avg ((vs.map (UnFn.apply .itof)).filter (· != .null))

end Substrait
