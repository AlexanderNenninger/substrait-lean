import SubstraitLean.DuckDBProfile

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
`characterization/duckdb/facts/` and the choices of `sql_lift`'s
hand-written `DUCKDB` profile it replaces; oracle A (#242) tests it against
the engine. With `semantics="reference"` a function means the reference's
function at the same types (an error where DuckDB would give `±∞` or NaN).

Covered so far: `+`, `-`, `*`, `/`, `%` of doubles, the elementary functions (`sqrt`, `exp`,
the logarithms, trigonometry) and `power`, `sign`, `greatest` and `least`,
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

/-- Values of the type: `NULL` or an integer; for a `DOUBLE`, a double, whose code is (`core/Sverify/Core/Float.lean`): between `-∞`'s and `+∞`'s, or NaN's. -/
def DuckType.Has : DuckType → Value → Prop
  | _, .null => True
  -- Every double: `-0.0` and the negative NaN too, which a plan can make
  -- (`0.0 * -1.0`) or a table hold (D31).
  | .double, .float c => ((FloatCode.negInf ≤ c ∧ c ≤ FloatCode.posInf) ∨ c = FloatCode.nan) ∨
      c = FloatCode.negZero ∨ c = FloatCode.negNan
  | .bigint, .int _ | .tinyint, .int _ => True
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
  /-- `a + b`, `a - b` and `a * b` of `DOUBLE`s: IEEE 754's, NaN for
  `∞ - ∞` and `0 · ∞` (`nanCase`), where the reference raises. -/
  | addDouble | subDouble | mulDouble
  /-- `sqrt`, `exp`, `ln`, `log10` (DuckDB's `log(x)`), `log2` and the
  trigonometric functions of a `DOUBLE` (`FMath`). -/
  | elementary (f : FMath)
  /-- `power(x, y)` of `DOUBLE`s. -/
  | power
  /-- `sign(x)` of a `BIGINT` or a `DOUBLE`: a `TINYINT`, `-1`, `0` or `1`;
  `0` for NaN. -/
  | signBigint | signDouble
  /-- `greatest(x, y)` and `least(x, y)`: DuckDB skips `NULL`s. -/
  | greatestBigint | leastBigint | greatestDouble | leastDouble
  /-- `CAST(x AS BIGINT)` of a `DOUBLE`, and `CAST(x AS DOUBLE)` of a `BIGINT`. -/
  | castDoubleBigint | castBigintDouble
  deriving Repr, DecidableEq, Inhabited

def DuckFn.all : List DuckFn :=
  [.divInt, .divDouble, .modDouble, .addDouble, .subDouble, .mulDouble] ++ FMath.all.map .elementary ++ [.power, .signBigint, .signDouble, .greatestBigint, .leastBigint,
   .greatestDouble, .leastDouble, .castDoubleBigint, .castBigintDouble]

theorem DuckFn.mem_all (f : DuckFn) : f ∈ DuckFn.all := by
  cases f
  case elementary f => cases f <;> decide
  all_goals decide

/-- The function as DuckDB writes it, with its argument types. -/
def DuckFn.sql : DuckFn → String
  | .divInt => "BIGINT / BIGINT" | .divDouble => "DOUBLE / DOUBLE"
  | .modDouble => "DOUBLE % DOUBLE"
  | .addDouble => "DOUBLE + DOUBLE" | .subDouble => "DOUBLE - DOUBLE"
  | .mulDouble => "DOUBLE * DOUBLE"
  -- DuckDB's `log(x)` is `log10(x)`; the lift (`sverify.sql_lift`) looks it up
  -- under DuckDB's name.
  | .elementary .log10 => "log(DOUBLE)"
  | .elementary f => s!"{f.name}(DOUBLE)"
  | .power => "power(DOUBLE, DOUBLE)"
  | .signBigint => "sign(BIGINT)" | .signDouble => "sign(DOUBLE)"
  | .greatestBigint => "greatest(BIGINT, BIGINT)" | .leastBigint => "least(BIGINT, BIGINT)"
  | .greatestDouble => "greatest(DOUBLE, DOUBLE)" | .leastDouble => "least(DOUBLE, DOUBLE)"
  | .castDoubleBigint => "CAST(DOUBLE AS BIGINT)" | .castBigintDouble => "CAST(BIGINT AS DOUBLE)"

def DuckFn.args : DuckFn → List DuckType
  | .divInt | .greatestBigint | .leastBigint => [.bigint, .bigint]
  | .divDouble | .modDouble | .addDouble | .subDouble | .mulDouble | .greatestDouble | .leastDouble | .power => [.double, .double]
  | .elementary _ | .signDouble | .castDoubleBigint => [.double]
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

theorem FloatCode.ofInt_ne_posInf (i : Int) : FloatCode.ofInt i ≠ FloatCode.posInf := by
  have := FloatCode.ofInt_bounds i; omega

theorem FloatCode.ofInt_ne_negInf (i : Int) : FloatCode.ofInt i ≠ FloatCode.negInf := by
  have := FloatCode.ofInt_bounds i; omega

/-! Lemmas the generated proofs compute with (`generate_lift … using`). -/

variable [Boxes.Ambient]
theorem DuckDBSQL.ref_itof (i : Int) :
    Profile.reference.un .itof (.int i) = .ok (.float (FloatCode.ofInt i)) := rfl

theorem DuckDBSQL.ref_fmath_float (f : FMath) (c : Int) :
    Profile.reference.un (.fmath f) (.float c) =
      match f.apply c with | some r => .ok (.float r) | none => .error .domain := by
  cases h : f.apply c <;>
    simp [Profile.reference, raiseIf, UnFn.issue, UnFn.apply, domainIssue, h, Issue.isError]

theorem DuckDBSQL.ref_fmath_null (f : FMath) : Profile.reference.un (.fmath f) .null = .ok .null := rfl

theorem DuckDBSQL.ref_itof_null : Profile.reference.un .itof .null = .ok .null := rfl

omit [Boxes.Ambient] in
theorem FloatCode.ofInt_ne_nan (i : Int) : FloatCode.ofInt i ≠ FloatCode.nan := by
  have := FloatCode.ofInt_bounds i; have := FloatCode.posInf_lt_nan; omega

omit [Boxes.Ambient] in
/-- Division of or by either NaN code is the NaN. -/
theorem DuckDBSQL.fdiv_nan_r (a : Int) : FloatCode.fdiv a FloatCode.nan = FloatCode.nan := by
  simp only [FloatCode.fdiv, FloatCode.divI, FloatCode.isNanCode_nans, Bool.or_true, ite_true]

omit [Boxes.Ambient] in
theorem DuckDBSQL.fdiv_negNan_r (a : Int) : FloatCode.fdiv a FloatCode.negNan = FloatCode.nan := by
  simp only [FloatCode.fdiv, FloatCode.divI, FloatCode.isNanCode_nans, Bool.or_true, ite_true]

omit [Boxes.Ambient] in
theorem DuckDBSQL.fdiv_nan_l (b : Int) : FloatCode.fdiv FloatCode.nan b = FloatCode.nan := by
  simp only [FloatCode.fdiv, FloatCode.divI, FloatCode.isNanCode_nans, Bool.true_or, ite_true]

omit [Boxes.Ambient] in
theorem DuckDBSQL.fdiv_negNan_l (b : Int) : FloatCode.fdiv FloatCode.negNan b = FloatCode.nan := by
  simp only [FloatCode.fdiv, FloatCode.divI, FloatCode.isNanCode_nans, Bool.true_or, ite_true]

theorem DuckDBSQL.ref_fdiv_float (a b : Int) :
    Profile.reference.bin .fdiv (.float a) (.float b) =
      if FloatCode.canon b = 0 then .error .divByZero else if nanCase .fdiv a b then .error .domain
      else .ok (.float (FloatCode.fdiv a (FloatCode.canon b))) := by
  by_cases hb : FloatCode.canon b = 0 <;> by_cases hn : nanCase .fdiv a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hb, hn, Issue.isError]

theorem DuckDBSQL.ref_fmod_float (a b : Int) :
    Profile.reference.bin .fmod (.float a) (.float b) =
      if FloatCode.canon b = 0 then .error .divByZero else if nanCase .fmod a b then .error .domain
      else .ok (.float (FloatCode.fmod a b)) := by
  by_cases hb : FloatCode.canon b = 0 <;> by_cases hn : nanCase .fmod a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hb, hn, Issue.isError]

theorem DuckDBSQL.ref_fdiv_null_l (y : Value) : Profile.reference.bin .fdiv .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fdiv_null_r (x : Value) : Profile.reference.bin .fdiv x .null = .ok .null := by
  cases x <;> rfl
theorem DuckDBSQL.ref_fmod_null_l (y : Value) : Profile.reference.bin .fmod .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fmod_null_r (x : Value) : Profile.reference.bin .fmod x .null = .ok .null := by
  cases x <;> rfl

/-! The reference's `+`, `-` and `*` of doubles: a domain error for `∞ - ∞`
and `0 · ∞`. -/

theorem DuckDBSQL.ref_fadd_float (a b : Int) :
    Profile.reference.bin .fadd (.float a) (.float b) =
      if nanCase .fadd a b then .error .domain else .ok (.float (FloatCode.fadd a b)) := by
  by_cases hn : nanCase .fadd a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hn, Issue.isError]
theorem DuckDBSQL.ref_fadd_null_l (y : Value) : Profile.reference.bin .fadd .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fadd_null_r (x : Value) : Profile.reference.bin .fadd x .null = .ok .null := by
  cases x <;> rfl
theorem DuckDBSQL.ref_fsub_float (a b : Int) :
    Profile.reference.bin .fsub (.float a) (.float b) =
      if nanCase .fsub a b then .error .domain else .ok (.float (FloatCode.fsub a b)) := by
  by_cases hn : nanCase .fsub a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hn, Issue.isError]
theorem DuckDBSQL.ref_fsub_null_l (y : Value) : Profile.reference.bin .fsub .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fsub_null_r (x : Value) : Profile.reference.bin .fsub x .null = .ok .null := by
  cases x <;> rfl
theorem DuckDBSQL.ref_fmul_float (a b : Int) :
    Profile.reference.bin .fmul (.float a) (.float b) =
      if nanCase .fmul a b then .error .domain else .ok (.float (FloatCode.fmul a b)) := by
  by_cases hn : nanCase .fmul a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hn, Issue.isError]
theorem DuckDBSQL.ref_fmul_null_l (y : Value) : Profile.reference.bin .fmul .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fmul_null_r (x : Value) : Profile.reference.bin .fmul x .null = .ok .null := by
  cases x <;> rfl

theorem DuckDBSQL.ref_fpow_float (a b : Int) :
    Profile.reference.bin .fpow (.float a) (.float b) =
      if negInfPow a b || nanCase .fpow a b then .error .domain
      else .ok (.float (FloatCode.lift₂ Float.pow a b)) := by
  by_cases hi : negInfPow a b <;> by_cases hn : nanCase .fpow a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hi, hn, Issue.isError]
theorem DuckDBSQL.ref_fpow_null_l (y : Value) : Profile.reference.bin .fpow .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fpow_null_r (x : Value) : Profile.reference.bin .fpow x .null = .ok .null := by
  cases x <;> rfl
theorem DuckDBSQL.ref_ffloor_float (c : Int) :
    Profile.reference.un .ffloor (.float c) = .ok (.float (FloatCode.floor c)) := rfl
theorem DuckDBSQL.ref_ffloor_null : Profile.reference.un .ffloor .null = .ok .null := rfl

omit [Boxes.Ambient] in
/-- A `SUM` of integers is an integer (`sumOf`). -/
theorem DuckDBSQL.sumOf_int_vals {vs : List Value} (h : ∀ v ∈ vs, ∃ i, v = .int i) :
    sumOf vs = .int (intSum vs) := by
  rcases sumOf_cases vs with ⟨s, h1, _⟩ | ⟨_, e⟩
  · exfalso
    simp only [allDecOf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h1
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil vs h1.1
    have hd := List.all_eq_true.mp h1.2 w hw
    obtain ⟨i, rfl⟩ := h w hw
    simp [Value.isDecOf] at hd
  · exact e

theorem DuckDBSQL.apply_eq_int (a b : Int) : BinFn.apply .eq (.int a) (.int b) = .bool (decide (a = b)) := rfl
theorem DuckDBSQL.apply_lt_int (a b : Int) : BinFn.apply .lt (.int a) (.int b) = .bool (decide (a < b)) := rfl
theorem DuckDBSQL.apply_eq_float (a b : Int) :
    BinFn.apply .eq (.float a) (.float b) =
      .bool (decide (FloatCode.canon a = FloatCode.canon b)) := by
  simp only [BinFn.apply]; rfl
theorem DuckDBSQL.apply_lt_float (a b : Int) :
    BinFn.apply .lt (.float a) (.float b) =
      .bool (decide (FloatCode.canon a < FloatCode.canon b)) := by
  simp only [BinFn.apply]
theorem DuckDBSQL.apply_eq_null_l (y : Value) : BinFn.apply .eq .null y = .null := by cases y <;> rfl
theorem DuckDBSQL.apply_eq_null_r (x : Value) : BinFn.apply .eq x .null = .null := by cases x <;> rfl
theorem DuckDBSQL.apply_lt_null_l (y : Value) : BinFn.apply .lt .null y = .null := by cases y <;> rfl
theorem DuckDBSQL.apply_lt_null_r (x : Value) : BinFn.apply .lt x .null = .null := by cases x <;> rfl

omit [Boxes.Ambient] in
theorem DuckDBSQL.canon_nan : FloatCode.canon FloatCode.nan = FloatCode.nan :=
  FloatCode.canon_of_isRef FloatCode.isRef_nan

omit [Boxes.Ambient] in
theorem DuckDBSQL.canon_one : FloatCode.canon FloatCode.one = FloatCode.one :=
  FloatCode.canon_of_bounds ⟨by have := FloatCode.negInf_lt_zero; have := FloatCode.zero_lt_one; omega,
    FloatCode.one_lt_posInf⟩

omit [Boxes.Ambient] in
theorem DuckDBSQL.canon_negOne : FloatCode.canon FloatCode.negOne = FloatCode.negOne :=
  FloatCode.canon_of_bounds ⟨by
    have := FloatCode.one_lt_posInf; have := FloatCode.zero_lt_one; have := FloatCode.negInf_eq
    have := FloatCode.posInf_eq; show _ < -FloatCode.one; omega,
    by have := FloatCode.zero_lt_one; have := FloatCode.zero_lt_posInf; show -FloatCode.one < _; omega⟩

omit [Boxes.Ambient] in
theorem DuckDBSQL.negOne_eq : FloatCode.negOne = -FloatCode.one := rfl

omit [Boxes.Ambient] in
/-- A double of `DuckType.double`'s range is canonical. -/
theorem DuckDBSQL.canon_of_has {c : Int}
    (h : (FloatCode.negInf ≤ c ∧ c ≤ FloatCode.posInf) ∨ c = FloatCode.nan) : FloatCode.canon c = c :=
  FloatCode.canon_of_isRef (by
    rcases h with ⟨h1, h2⟩ | rfl
    · exact ⟨h1, Int.le_trans h2 (Int.le_of_lt FloatCode.posInf_lt_nan)⟩
    · exact FloatCode.isRef_nan)

/-- The floor of a canonical double is canonical (`power`'s guard reads it). -/
theorem DuckDBSQL.canon_floor_of_has {c : Int}
    (h : (FloatCode.negInf ≤ c ∧ c ≤ FloatCode.posInf) ∨ c = FloatCode.nan) :
    FloatCode.canon (FloatCode.floor c) = FloatCode.floor c :=
  FloatCode.canon_floor (DuckDBSQL.canon_of_has h)

omit [Boxes.Ambient] in
theorem DuckDBSQL.canon_negZero : FloatCode.canon FloatCode.negZero = 0 := fp64.canon_negZero

omit [Boxes.Ambient] in
theorem DuckDBSQL.canon_negNan : FloatCode.canon FloatCode.negNan = FloatCode.nan := fp64.canon_negNan

omit [Boxes.Ambient] in
theorem DuckDBSQL.nan_eq : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq

omit [Boxes.Ambient] in
/-- The special codes against the other constants, for the lift's proofs:
`decide` would compare their huge numerals. -/
theorem DuckDBSQL.zero_ne_negZero : ¬ ((0 : Int) = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_zero : ¬ (FloatCode.negZero = (0 : Int)) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.zero_ne_negNan : ¬ ((0 : Int) = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_zero : ¬ (FloatCode.negNan = (0 : Int)) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.posInf_ne_negZero : ¬ (FloatCode.posInf = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_posInf : ¬ (FloatCode.negZero = FloatCode.posInf) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.posInf_ne_negNan : ¬ (FloatCode.posInf = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_posInf : ¬ (FloatCode.negNan = FloatCode.posInf) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negInf_ne_negZero : ¬ (FloatCode.negInf = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_negInf : ¬ (FloatCode.negZero = FloatCode.negInf) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negInf_ne_negNan : ¬ (FloatCode.negInf = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_negInf : ¬ (FloatCode.negNan = FloatCode.negInf) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.nan_ne_negZero : ¬ (FloatCode.nan = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_nan : ¬ (FloatCode.negZero = FloatCode.nan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.nan_ne_negNan : ¬ (FloatCode.nan = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_nan : ¬ (FloatCode.negNan = FloatCode.nan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.one_ne_negZero : ¬ (FloatCode.one = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_one : ¬ (FloatCode.negZero = FloatCode.one) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.one_ne_negNan : ¬ (FloatCode.one = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_one : ¬ (FloatCode.negNan = FloatCode.one) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negOne_ne_negZero : ¬ (FloatCode.negOne = FloatCode.negZero) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negZero_ne_negOne : ¬ (FloatCode.negZero = FloatCode.negOne) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negOne_ne_negNan : ¬ (FloatCode.negOne = FloatCode.negNan) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.negNan_ne_negOne : ¬ (FloatCode.negNan = FloatCode.negOne) := by
  have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
  have := FloatCode.posInf_eq; have := DuckDBSQL.nan_eq; have := FloatCode.zero_lt_one
  have := FloatCode.one_lt_posInf; have := DuckDBSQL.negOne_eq
  omega

omit [Boxes.Ambient] in
/-- IEEE division by a zero (D39) is DuckDB's: `±∞` by the two signs, NaN for a
zero or NaN dividend. -/
theorem DuckDBSQL.fdiv_of_canon_zero {a b : Int} (hb : FloatCode.canon b = 0) :
    FloatCode.fdiv a b = ieeeDivZero a b := by
  have h1 := FloatCode.negZero_eq'; have h2 := FloatCode.negNan_eq'
  have h3 : FloatCode.posInf = 2 * (FloatCode.maxMag : Int) + 3 := FloatCode.posInf_eq
  have h4 : FloatCode.negInf = -(2 * (FloatCode.maxMag : Int) + 3) := FloatCode.negInf_eq
  have h5 := DuckDBSQL.nan_eq
  have hb' : b = 0 ∨ b = FloatCode.negZero := by
    by_cases h : b = FloatCode.negZero
    · exact .inr h
    · by_cases h' : b = FloatCode.negNan
      · subst h'; rw [DuckDBSQL.canon_negNan] at hb; omega
      · left
        have e0 : ¬ b = fp64.negZero := h
        have e1 : ¬ b = fp64.negNan := h'
        simpa [FloatCode.canon, FloatFormat.canon, e0, e1] using hb
  have hca : ∀ c, FloatCode.canon c = 0 ↔ c = 0 ∨ c = FloatCode.negZero := fun c => by
    constructor
    · intro hc
      by_cases h : c = FloatCode.negZero
      · exact .inr h
      · by_cases h' : c = FloatCode.negNan
        · subst h'; rw [DuckDBSQL.canon_negNan] at hc; omega
        · left
          have e0 : ¬ c = fp64.negZero := h
          have e1 : ¬ c = fp64.negNan := h'
          simpa [FloatCode.canon, FloatFormat.canon, e0, e1] using hc
    · rintro (rfl | rfl)
      · exact FloatCode.canon_zero
      · exact DuckDBSQL.canon_negZero
  have hcn : ∀ c, FloatCode.canon c = FloatCode.nan ↔ c = FloatCode.nan ∨ c = FloatCode.negNan := fun c => by
    constructor
    · intro hc
      by_cases h : c = FloatCode.negZero
      · subst h; rw [DuckDBSQL.canon_negZero] at hc; omega
      · by_cases h' : c = FloatCode.negNan
        · exact .inr h'
        · left
          have e0 : ¬ c = fp64.negZero := h
          have e1 : ¬ c = fp64.negNan := h'
          simpa [FloatCode.canon, FloatFormat.canon, e0, e1] using hc
    · rintro (rfl | rfl)
      · exact DuckDBSQL.canon_nan
      · exact DuckDBSQL.canon_negNan
  unfold FloatCode.fdiv FloatCode.divI ieeeDivZero
  simp only [hca, hcn, FloatCode.isZeroCode, FloatCode.isInfCode, FloatCode.isNanCode,
    FloatCode.infOf, FloatCode.zeroOf, Bool.or_eq_true, beq_iff_eq]
  rcases hb' with rfl | rfl <;>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_decide] <;>
    (repeat' split) <;> first | rfl | omega | (simp_all <;> omega) | simp_all

omit [Boxes.Ambient] in
theorem DuckDBSQL.ofInt_zero : FloatCode.ofInt 0 = 0 := by
  rw [FloatCode.ofInt_exact (by decide)]; simp [FloatCode.exactCode, FloatFormat.exactCode]

omit [Boxes.Ambient] in
/-- An integer's double has the integer's sign. -/
theorem DuckDBSQL.ofInt_pos (i : Int) : (0 < FloatCode.ofInt i) = (0 < i) := by
  have h0 := DuckDBSQL.ofInt_zero
  apply propext; constructor
  · intro h
    if hi : 0 < i then exact hi
    else have := FloatCode.ofInt_mono (show i ≤ 0 by omega); omega
  · intro h
    have := FloatCode.ofInt_mono (show 0 ≤ i by omega)
    have := FloatCode.ofInt_ne_zero (show i ≠ 0 by omega); omega

omit [Boxes.Ambient] in
theorem DuckDBSQL.ofInt_eq_zero (i : Int) : (FloatCode.ofInt i = 0) = (i = 0) := by
  apply propext; constructor
  · intro h
    if hi : i = 0 then exact hi else exact absurd h (FloatCode.ofInt_ne_zero hi)
  · rintro rfl; exact DuckDBSQL.ofInt_zero

theorem DuckDBSQL.ref_fdivIeee_float (a b : Int) :
    Profile.reference.bin .fdivIeee (.float a) (.float b) =
      if nanCase .fdivIeee a b then .error .domain else .ok (.float (FloatCode.fdiv a b)) := by
  by_cases hn : nanCase .fdivIeee a b <;>
    simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, BinFn.apply, hn, Issue.isError]
theorem DuckDBSQL.ref_fdivIeee_null_l (y : Value) : Profile.reference.bin .fdivIeee .null y = .ok .null := by
  cases y <;> rfl
theorem DuckDBSQL.ref_fdivIeee_null_r (x : Value) : Profile.reference.bin .fdivIeee x .null = .ok .null := by
  cases x <;> rfl

omit [Boxes.Ambient] in
theorem DuckDBSQL.ite_or {α} {p q : Prop} [Decidable p] [Decidable q] (a b : α) :
    (if p ∨ q then a else b) = if p then a else if q then a else b := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-! What DuckDB's profile gives for the functions the lift reads, computed
from `Profile.duckdb` (the lift's proofs rewrite with them). -/

theorem DuckDBSQL.duck_fdiv_float (a b : Int) :
    (Profile.duckdb {}).bin .fdiv (.float a) (.float b) =
      .ok (.float (if FloatCode.canon b = 0 then ieeeDivZero a b
        else if nanCase .fdiv a b then FloatCode.nan else FloatCode.fdiv a (FloatCode.canon b))) := by
  by_cases hb : FloatCode.canon b = 0 <;> by_cases hn : nanCase .fdiv a b <;>
    simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue, nanIssue,
      BinFn.apply, hb, hn, Issue.isError]

omit [Boxes.Ambient] in
/-- `fmod` of an infinite dividend is NaN, whatever the divisor. -/
theorem DuckDBSQL.fmod_of_inf {a : Int} (b : Int) (h : isInfCode a = true) :
    FloatCode.fmod a b = FloatCode.nan := by
  have hp := FloatCode.posInf_eq; have hn := FloatCode.negInf_eq
  have hi : FloatCode.infMag = FloatCode.maxMag + 1 := rfl
  simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at h
  unfold FloatCode.fmod FloatCode.finiteParts
  have hz := FloatCode.negZero_eq'
  have ha : a ≠ fp64.negZero := by
    show a ≠ FloatCode.negZero
    rcases h with rfl | rfl <;> omega
  have hm : FloatCode.infMag ≤ (a.natAbs - 1) / 2 := by
    rcases h with rfl | rfl <;> omega
  simp [ha, hm]

theorem DuckDBSQL.duck_fmod_float (a b : Int) :
    (Profile.duckdb {}).bin .fmod (.float a) (.float b) =
      .ok (.float (if FloatCode.canon b = 0 ∨ isInfCode a then FloatCode.nan
        else FloatCode.fmod a b)) := by
  by_cases hb : FloatCode.canon b = 0
  · simp [Profile.duckdb, BinFn.onFloats, duckBin, hb]
  · by_cases hi : isInfCode a = true
    · by_cases hn : nanCase .fmod a b
      · simp [Profile.duckdb, BinFn.onFloats, duckBin, hb, hn, hi]
      · simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue,
          nanIssue, BinFn.apply, hb, hn, hi, DuckDBSQL.fmod_of_inf b hi]
    · have hn : nanCase .fmod a b = false := by simp [nanCase, hi]
      simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue,
        nanIssue, BinFn.apply, hb, hn, hi]

theorem DuckDBSQL.duck_arith_float (f : BinFn) (hf : f = .fadd ∨ f = .fsub ∨ f = .fmul) (a b : Int) :
    (Profile.duckdb {}).bin f (.float a) (.float b) =
      .ok (if nanCase f a b then .float FloatCode.nan else f.apply (.float a) (.float b)) := by
  by_cases hn : nanCase f a b <;> rcases hf with rfl | rfl | rfl <;>
    simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue, nanIssue,
      hn, Issue.isError]

theorem DuckDBSQL.duck_fadd_float (a b : Int) : (Profile.duckdb {}).bin .fadd (.float a) (.float b) =
    .ok (if nanCase .fadd a b then .float FloatCode.nan else BinFn.apply .fadd (.float a) (.float b)) :=
  DuckDBSQL.duck_arith_float .fadd (.inl rfl) a b
theorem DuckDBSQL.duck_fsub_float (a b : Int) : (Profile.duckdb {}).bin .fsub (.float a) (.float b) =
    .ok (if nanCase .fsub a b then .float FloatCode.nan else BinFn.apply .fsub (.float a) (.float b)) :=
  DuckDBSQL.duck_arith_float .fsub (.inr (.inl rfl)) a b
theorem DuckDBSQL.duck_fmul_float (a b : Int) : (Profile.duckdb {}).bin .fmul (.float a) (.float b) =
    .ok (if nanCase .fmul a b then .float FloatCode.nan else BinFn.apply .fmul (.float a) (.float b)) :=
  DuckDBSQL.duck_arith_float .fmul (.inr (.inr rfl)) a b

theorem DuckDBSQL.duck_fpow_float (a b : Int) :
    (Profile.duckdb {}).bin .fpow (.float a) (.float b) = .ok (.float (if negInfPow a b then
      duckNegInfPow b else if nanCase .fpow a b then FloatCode.nan
      else FloatCode.lift₂ Float.pow a b)) := by
  by_cases hi : negInfPow a b <;> by_cases hn : nanCase .fpow a b <;>
    simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue, nanIssue,
      BinFn.apply, hi, hn, Issue.isError]

theorem DuckDBSQL.duck_fmath_float (f : FMath) (a : Int) :
    (Profile.duckdb {}).un (.fmath f) (.float a) = .ok (.float (duckElementary f a)) := by
  cases h : f.apply a <;>
    simp [Profile.duckdb, duckUn, duckElementary, Profile.reference, raiseIf, UnFn.issue, UnFn.apply,
      domainIssue, h]

theorem DuckDBSQL.duck_bin_null_l (f : BinFn) (y : Value) :
    (Profile.duckdb {}).bin f .null y = Profile.reference.bin f .null y := by
  cases y <;> rfl

theorem DuckDBSQL.duck_bin_null_r (f : BinFn) (x : Value) :
    (Profile.duckdb {}).bin f x .null = Profile.reference.bin f x .null := by
  cases x <;> rfl

theorem DuckDBSQL.duck_un_null (f : UnFn) : (Profile.duckdb {}).un f .null = Profile.reference.un f .null :=
  rfl

theorem DuckDBSQL.duck_itof (v : Value) : (Profile.duckdb {}).un .itof v = Profile.reference.un .itof v := by
  cases v <;> rfl

/-- `sign` of an integer, or of a double's code (codes are ordered as their
doubles; NaN's is the largest, and its sign is `0`). -/
def duckSign (x : Int) : Int := if x < 0 then -1 else if 0 < x then 1 else 0

/-- The profile a semantics evaluates DuckDB's functions with: DuckDB's own
(`Profile.duckdb`, default settings), or the reference. -/
def Semantics.profile : Semantics → Profile
  | .duckdb => Profile.duckdb {}
  | .reference => Profile.reference

/-- **What a DuckDB function means, in the model's functions**, for those whose
DuckDB side is a model function under DuckDB's profile: `/` of integers divides
their doubles (F1), DuckDB's `log(x)` is `log10`. Under either semantics the
function is this expression under `Semantics.profile`, so what DuckDB computes
is stated once, by `Profile.duckdb`. The others (`sign`, `greatest`, `least`,
the casts) mean the same under both and are stated in `DuckFn.eval`. -/
def DuckFn.meaning : DuckFn → Option Expr
  | .divInt => some (.bin .fdiv (.un .itof (.field 0)) (.un .itof (.field 1)))
  | .divDouble => some (.bin .fdiv (.field 0) (.field 1))
  | .modDouble => some (.bin .fmod (.field 0) (.field 1))
  | .addDouble => some (.bin .fadd (.field 0) (.field 1))
  | .subDouble => some (.bin .fsub (.field 0) (.field 1))
  | .mulDouble => some (.bin .fmul (.field 0) (.field 1))
  | .elementary f => some (.un (.fmath f) (.field 0))
  | .power => some (.bin .fpow (.field 0) (.field 1))
  | _ => none

/-- What the functions without a meaning in the model's functions give: the
same under both semantics, but for the reference's cast to `BIGINT`. -/
def DuckFn.evalOwn : Semantics → DuckFn → List Value → Outcome
  | _, .signBigint, [.int a] => .ok (.int (duckSign a))
  -- `x > 0 ? 1 : x < 0 ? -1 : 0`: `-0.0` and every NaN give 0 (D31).
  | _, .signDouble, [.float a] =>
    .ok (.int (if FloatCode.canon a = FloatCode.nan then 0 else duckSign (FloatCode.canon a)))
  | _, .greatestBigint, [x, y] => .ok (match x, y with
    | .int a, .int b => .int (if a < b then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  -- Compared as DuckDB orders doubles, one zero and every NaN greatest, the
  -- first argument kept among equals (duckdb-float-signs, D31).
  | _, .greatestDouble, [x, y] => .ok (match x, y with
    | .float a, .float b => .float (if FloatCode.canon a < FloatCode.canon b then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  | _, .leastBigint, [x, y] => .ok (match x, y with
    | .int a, .int b => .int (if b < a then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  | _, .leastDouble, [x, y] => .ok (match x, y with
    | .float a, .float b => .float (if FloatCode.canon b < FloatCode.canon a then b else a)
    | .null, v | v, .null => v
    | _, _ => .null)
  | .reference, .castDoubleBigint, [a] => Profile.reference.un .ftoi a
  | _, .castBigintDouble, [.int a] => .ok (.float (FloatCode.ofInt a))
  | _, _, _ => .ok .null

/-- What the function gives for its arguments, under the semantics: its
meaning under the semantics' profile, else `DuckFn.evalOwn`. `NULL` in, `NULL`
out, but for `greatest` and `least`, which skip `NULL`s. -/
def DuckFn.eval (s : Semantics) (f : DuckFn) (xs : List Value) : Outcome :=
  match f.meaning with
  | some e => e.evalP s.profile xs
  | none => DuckFn.evalOwn s f xs

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
    | xs => .float (FloatCode.fdiv (FloatCode.ofInt (intSum xs)) (FloatCode.ofInt xs.length))
  | .reference, .avgBigint, vs => AggFn.apply .avg ((vs.map (UnFn.apply .itof)).filter (· != .null))

end Substrait
