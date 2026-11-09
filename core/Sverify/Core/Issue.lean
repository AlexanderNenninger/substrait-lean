import Sverify.Core.Rel

/-!
# The issue model

What goes wrong when a function runs on a row (`Issue`, `UnFn.issue`,
`BinFn.issue`, `Expr.issues`): where the reference raises, and an error
allows any engine's answer. Which rows an engine evaluates an expression on,
and the analysis that over-approximates the issues of a plan
(`Rel.HasIssue`, `Rel.mayIssues`), are in `analysis/Sverify/Analysis/Safety.lean`.
-/

namespace Substrait
variable [Boxes.Ambient]

open FloatCode (minI64 maxI64 castLo castHi)

inductive Issue where
  /-- Integer division or remainder by zero, or a double divided by zero. -/
  | divByZero
  /-- A result that leaves its type: outside 64 bits (`MIN / -1`, `POWER`), a
  `repeat` beyond `Text.repeatMax` bytes, a decimal of more digits than its
  precision (`UnFn.decimal`), or a calendar value outside `Time.lean`'s
  ranges. -/
  | overflow
  /-- `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value. -/
  | badCast
  /-- `POWER` of integers with a negative exponent. -/
  | negExponent
  /-- A regular expression outside `Text.simpleRegex`, which may not compile. -/
  | badRegex
  /-- `+`, `-`, `*` or negation whose result does not fit its declared width:
  64 bits, or narrower integers (`UnFn.wrap`). With `overflow` omitted or
  `ERROR`, the reference raises (#202), as DuckDB and Spark do
  (duckdb-int-narrow, spark-int-arith); Polars wraps around instead
  (polars-int-arith), which an error allows (a refinement). -/
  | wraps
  /-- A `SUM` leaving its type (`Measure.sumOk`): 64 bits for integers, the
  result's precision for decimals (#316). The reference raises, and so does
  the SQL sverify writes, which keeps its check while the job runs (DuckDB
  raises on a decimal `SUM` that leaves 38 digits). An error like any other:
  a plan that may raise is not proved, unless the input's rows and the
  argument's range bound the sum (`Measure.sumFits`). Kept apart from
  `wraps` because it comes from a group's rows, not from one row:
  `analysis/Sverify/Analysis/Guards.lean` drops row-level checks, never this one. -/
  | sumWraps
  /-- An argument outside a function's domain (`core/Sverify/Core/Numeric.lean`):
  `sqrt` of a negative, a logarithm of zero or a negative, `asin` or `acos`
  outside `[-1, 1]`, `atan2(0, 0)`, `logb` to a base that is not positive or
  is 1, a shift count outside `0`–`63`, a `substring` offset outside
  `[-2³², 2³²)` or length of `2³²` or more (`Text.substrInRange`, #336,
  where DuckDB raises too). The reference raises (Substrait's
  `on_domain_error` = ERROR); an engine that gives NaN, ±∞ or a wrapped
  shift instead refines it (epic #185). -/
  | domain
  /-- Raised by a shim's guard (`UnFn.raise`, #185), where an engine would
  answer while the reference raises. Plans `verify` checks have none. -/
  | raised
  /-- An operation on finite doubles whose result is `±∞` (#575): `+`, `-`,
  `*`, `/` and `power` that overflow (or `0 ^ -1`), `exp` past `709.78`, and a
  `SUM`, `AVG` or statistical aggregate of finite values that overflows. An
  error of the reference: it raises there. As for a `SUM` that leaves its
  type, verification rules it out by an inferred precondition, proved from the
  bounds where they do it (`Measure.abs`) and otherwise checked on the data
  while the job runs (`Issue.assumed`, `Report.assumed`). `Rel.eval` and
  `Profile.reference` keep the IEEE value, `±∞`, on the rows the precondition
  excludes (`Issue.isError` is false for it), so the lift of DuckDB's SQL and
  the lowering state DuckDB's result exactly. -/
  | infinite
  deriving Repr, DecidableEq

def Issue.name : Issue → String
  | .divByZero => "division by zero"
  | .overflow => "overflow"
  | .badCast => "cast out of range"
  | .negExponent => "negative exponent"
  | .badRegex => "invalid regular expression"
  | .wraps => "overflow"
  | .sumWraps => "SUM overflow"
  | .domain => "domain error"
  | .raised => "raised by a guard"
  | .infinite => "overflow to infinity"

/-- The aggregates among a list of window functions. -/
def WinFn.aggs (fns : List WinFn) : List Measure :=
  fns.filterMap fun
    | .agg m _ _ => some m
    | _ => none

/-- Whether `Profile.reference` gives an error outcome for the issue (`raiseIf`).
Every issue raises in the reference and a proof must rule each out. An
overflow to `±∞` (#575) keeps its IEEE value in `Rel.eval` and
`Profile.reference`: its precondition (`Issue.assumed`) rules it out, so no
verified run reaches that value. -/
def Issue.isError : Issue → Bool
  | .infinite => false
  | _ => true

/-- The errors ruled out by an inferred precondition, inferred like #244's
bounds and checked on the data while the job runs where the bounds do not
prove it (`Report.assumed`): a `SUM` that leaves its type, an overflow to
`±∞`. -/
def Issue.assumed : Issue → Bool
  | .sumWraps | .infinite => true
  | _ => false

def inI64 : Int → Bool := between minI64 maxI64

def wrapIf (i : Int) : Option Issue := if inI64 i then none else some .wraps

/-- `wraps` for a number outside 64 bits. -/
def wrapNum (v : Value) : Option Issue :=
  match v.numOf? with
  | some (_, i) => wrapIf i
  | none => none

/-- A domain error where a partial function has no result. -/
def domainIssue (r : Option Int) : Option Issue := if r.isSome then none else some .domain

/-- `overflow` unless the argument `x` and the result `y` are in `[lo, hi]`:
the reference's dates or timestamps (#251, D32). -/
def rangeIssue (lo hi x y : Int) : Option Issue :=
  if between lo hi x && between lo hi y then none else some .overflow

/-! ## What goes wrong on a row -/

def UnFn.issue : UnFn → Value → Option Issue
  -- A black box that may raise, where it does (#325).
  | .bbox n, v => if BlackBox.raisesOn Boxes.Ambient.boxes n [v] then some .domain else none
  | .neg, .int i => wrapIf (-i)
  | .ftoi, .float c => match FloatCode.toInt? (FloatCode.canon c) with
    | some x => if inI64 x then none else some .badCast
    | none => some .badCast
  | .narrow n, .int i => if fitsBits n i then none else some .badCast
  | .wrap n, .int i => if fitsBits n i then none else some .wraps
  -- The pattern is compiled whatever the input.
  | .regexMatch p, _ => if Text.simpleRegex p then none else some .badRegex
  | .dateTrunc u, .ts ts | .dateTrunc u, .tod ts =>
    if u.calendar then
      if ts ≤ Time.tsMax ∧ Time.tsMin ≤ Time.trunc u ts then none else some .overflow
    else wrapIf (Time.trunc u ts)
  | .dayTrunc u, .date d => rangeIssue Time.dayMin Time.dayMax d (Time.truncDay u d)
  | .addMonths m false, .date d => rangeIssue Time.dayMin Time.dayMax d (Time.addMonths m d)
  -- The reference's dates (#807); DuckDB raises past its timestamps' years.
  | .dateTime, .date d => rangeIssue Time.dayMin Time.dayMax d d
  -- The calendar on the reference's timestamps (D32).
  | .addMonths m true, .ts ts => rangeIssue Time.tsMin Time.tsMax ts (Time.addMonthsUs m ts)
  | .timeOfDay, .ts ts | .timeOfDay, .tod ts | .strftime _, .ts ts | .datePart _, .ts ts =>
    rangeIssue Time.tsMin Time.tsMax ts ts
  | .dayPart _, .date d => rangeIssue Time.dayMin Time.dayMax d d
  | .bucket k o, .ts ts => rangeIssue Time.tsMin Time.tsMax ts (Time.bucket k o ts)
  | .fmath f, .float c => domainIssue (f.apply c)
  | .decimal p _, v => match v.unscaled? with
    | some i => if fitsDigits p i then none else some .overflow
    | none => none
  -- NaN and ±∞ have no decimal.
  | .ftod s, .float c =>
    if (FloatCode.toDecimal? (FloatCode.canon c) s).isSome then none else some .badCast
  | .raise _, _ => some .raised
  | _, _ => none

/-- Is `c` the code of `+∞` or `-∞`? -/
def isInfCode (c : Int) : Bool := c == FloatCode.posInf || c == FloatCode.negInf

/-- The inputs on which IEEE 754 makes a double operation's result NaN though
neither input is NaN (#257): `∞ - ∞`, `0 · ∞`, `∞ / ∞` (`0 / 0` is a division
by zero), a power of a finite negative number to a finite exponent that is
not an integer, and `fmod` of `±∞`. The reference never creates a NaN, so
these raise (a domain error). -/
def nanCase : BinFn → Int → Int → Bool
  | .fadd, a, b => (a == FloatCode.posInf && b == FloatCode.negInf) ||
      (a == FloatCode.negInf && b == FloatCode.posInf)
  | .fsub, a, b => (a == FloatCode.posInf && b == FloatCode.posInf) ||
      (a == FloatCode.negInf && b == FloatCode.negInf)
  | .fmul, a, b => ((a == 0 || a == FloatCode.negZero) && isInfCode b) ||
      (isInfCode a && (b == 0 || b == FloatCode.negZero))
  | .fdiv, a, b => isInfCode a && isInfCode b
  -- IEEE division (D39) also creates a NaN at `0 / 0`, which raises (D37).
  | .fdivIeee, a, b => (isInfCode a && isInfCode b) ||
      (FloatCode.canon a == 0 && FloatCode.canon b == 0)
  | .fmod, a, b => isInfCode a && b != FloatCode.nan && b != FloatCode.negNan
  | .fpow, a, b => decide (FloatCode.negInf < a) && decide (a < 0) &&
      decide (FloatCode.negInf < b) && decide (b < FloatCode.posInf) && FloatCode.floor b != b
  | _, _, _ => false

def nanIssue (f : BinFn) (a b : Int) : Option Issue := if nanCase f a b then some .domain else none

omit [Boxes.Ambient] in
/-- Where IEEE division's NaN case holds (`∞ / ∞`, `0 / 0`), IEEE division
gives the NaN itself: an engine computing IEEE's `/` needs no option there. -/
theorem fdiv_of_nanCase_ieee {a b : Int} (h : nanCase .fdivIeee a b = true) :
    FloatCode.fdiv a b = FloatCode.nan := by
  have hP := FloatCode.posInf_eq; have hN := FloatCode.negInf_eq
  have hZ := FloatCode.negZero_eq'; have hY := FloatCode.negNan_eq'
  have hQ : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  have hinf : ∀ c, isInfCode c = FloatCode.isInfCode c := fun _ => rfl
  simp only [nanCase, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, hinf] at h
  unfold FloatCode.fdiv FloatCode.divI
  split
  · rfl
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [ha, hb]
  · have zero : ∀ {c : Int}, FloatCode.canon c = 0 →
        FloatCode.isZeroCode c = true ∧ FloatCode.isInfCode c = false := by
      intro c hc
      have hz : c = 0 ∨ c = FloatCode.negZero := by
        rcases FloatCode.canon_cases c with ⟨h', _⟩ | ⟨_, h'⟩ | h'
        · exact .inr h'
        · omega
        · exact .inl (h'.symm.trans hc)
      simp only [FloatCode.isZeroCode, FloatCode.isInfCode, Bool.or_eq_true, beq_iff_eq,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      omega
    obtain ⟨za, ia⟩ := zero ha
    obtain ⟨zb, ib⟩ := zero hb
    simp [za, zb, ia, ib]

/-- `power(-∞, y)` for a finite `y` that is not an integer. IEEE 754 gives
`+∞` for `y > 0` and `0` for `y < 0`, as DuckDB does, but Polars's `** 0.5`
is a square root, NaN. The reference raises (a domain error, as for a finite
negative base), so a verified plan never meets it and no engine needs a shim. -/
def negInfPow (a b : Int) : Bool :=
  decide (a = FloatCode.negInf) && decide (FloatCode.negInf < b) && decide (b < FloatCode.posInf) &&
    FloatCode.floor b != b

/-- `power(±1, ±∞)` or `power(1, NaN)`: `1` by C's `pow`, NaN by IEEE 754's
`powr` and Java's `StrictMath.pow` (`pow_one_inf`, D40). -/
def powOneInf (a b : Int) : Bool :=
  ((FloatCode.canon a == FloatCode.one || FloatCode.canon a == FloatCode.negOne) && isInfCode b) ||
    (FloatCode.canon a == FloatCode.one && FloatCode.canon b == FloatCode.nan)

def BinFn.issue : BinFn → Value → Value → Option Issue
  | .bbox2 n, v, w => if BlackBox.raisesOn Boxes.Ambient.boxes n [v, w] then some .domain else none
  -- Integers, and timestamps, times of day and dates moved by an interval.
  | .add, v, w => wrapNum (BinFn.add.apply v w)
  | .sub, v, w => wrapNum (BinFn.sub.apply v w)
  | .mul, v, w => wrapNum (BinFn.mul.apply v w)
  | .dateAdd, .date a, .int b => rangeIssue Time.dayMin Time.dayMax a (a + b)
  | .idiv, .int a, .int b =>
    if b = 0 then some .divByZero else if inI64 (a.tdiv b) then none else some .overflow
  | .imod, .int _, .int b | .imod, .tod _, .int b => if b = 0 then some .divByZero else none
  -- A double divided by zero, `0.0` or `-0.0` (the one zero of `ONE_ZERO`,
  -- D31): Substrait's `on_division_by_zero` = ERROR. The parser writes the
  -- other options as a `CASE` around this (`Parse.divByZero`).
  | .fdiv, .float a, .float b =>
    if FloatCode.canon b = 0 then some .divByZero else nanIssue .fdiv a b
  -- IEEE by a zero (D39); `±∞ / ±∞` and `0 / 0` create a NaN and raise (D37).
  | .fdivIeee, .float a, .float b => nanIssue .fdivIeee a b
  | .fmod, .float a, .float b =>
    if FloatCode.canon b = 0 then some .divByZero else nanIssue .fmod a b
  | .fadd, .float a, .float b => nanIssue .fadd a b
  | .fsub, .float a, .float b => nanIssue .fsub a b
  | .fmul, .float a, .float b => nanIssue .fmul a b
  | .fpow, .float a, .float b => if negInfPow a b then some .domain else nanIssue .fpow a b
  | .ipow, .int a, .int b =>
    if b < 0 then some .negExponent
    else if 64 < b ∧ 1 < a.natAbs then some .overflow
    else if inI64 (a ^ b.toNat) then none else some .overflow
  | .strRepeat, .str s, .int n => if Text.repeatFits s n then none else some .overflow
  | .substr n _, .str _, .int a => if Text.substrInRange a n then none else some .domain
  | .fatan2, .float y, .float x => domainIssue (atan2? y x)
  | .flogb, .float x, .float b => domainIssue (logb? x b)
  | .bit op, .int a, .int b => domainIssue (op.apply a b)
  | _, _, _ => none

/-- Is `c` the code of a finite double? -/
def isFiniteCode (c : Int) : Bool := decide (FloatCode.negInf < c) && decide (c < FloatCode.posInf)

/-- The operations of doubles that may overflow to `±∞` (#575). -/
def BinFn.makesInf : BinFn → Bool
  | .fadd | .fsub | .fmul | .fdiv | .fdivIeee | .fpow => true
  | _ => false

/-- An operation on finite doubles whose IEEE result is `±∞` (#575). -/
def BinFn.infIssue (f : BinFn) (v w : Value) : Option Issue :=
  match v, w, f.apply v w with
  | .float a, .float b, .float r =>
    -- IEEE division by a zero is `±∞` by the option's choice (D39), not an overflow.
    if f.makesInf && isFiniteCode (FloatCode.canon a) && isFiniteCode (FloatCode.canon b) && isInfCode r &&
        !(f == .fdivIeee && FloatCode.canon b == 0) then
      some .infinite
    else none
  | _, _, _ => none

/-- `exp` of a finite double whose result is `±∞` (#575): the other
elementary functions of a finite double are finite, or a domain error. -/
def UnFn.infIssue (f : UnFn) (v : Value) : Option Issue :=
  match f, v, f.apply v with
  | .fmath .exp, .float a, .float r =>
    if isFiniteCode (FloatCode.canon a) && isInfCode r then some .infinite else none
  | _, _, _ => none

/-- The issue of a call: the error first, else an overflow to `±∞`. -/
def UnFn.issueAll (f : UnFn) (v : Value) : Option Issue := (f.issue v).or (f.infIssue v)

def BinFn.issueAll (f : BinFn) (v w : Value) : Option Issue := (f.issue v w).or (f.infIssue v w)

/-- Where a NaN case holds (`∞ - ∞`, `0 · ∞`, `∞ / ∞`, …), the reference
reports an issue: an engine's own NaN there is on the error side. -/
theorem nanCase_issue {f : BinFn} {a b : Int} (hn : nanCase f a b = true) :
    f.issue (.float a) (.float b) ≠ none := by
  cases f <;> simp only [nanCase, Bool.false_eq_true] at hn <;>
    simp only [BinFn.issue, nanIssue, nanCase] at * <;> (try split) <;> simp_all

theorem UnFn.infIssue_eq {f : UnFn} {v : Value} {k : Issue} (h : f.infIssue v = some k) :
    k = .infinite := by
  unfold UnFn.infIssue at h; split at h <;> (try split at h) <;> simp_all

theorem BinFn.infIssue_eq {f : BinFn} {v w : Value} {k : Issue} (h : f.infIssue v w = some k) :
    k = .infinite := by
  unfold BinFn.infIssue at h; split at h <;> (try split at h) <;> simp_all

/-- The issues evaluating `e` on `row` runs into, each with the operation
that raises it. A `CASE` only evaluates the branch it takes. -/
def Expr.issues (row : Row) : Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | .un f a => a.issues row ++ ((f.issueAll (a.eval row)).map (·, .un f a)).toList
  | .bin f a b =>
    a.issues row ++ b.issues row ++ ((f.issueAll (a.eval row) (b.eval row)).map (·, .bin f a b)).toList
  | .ifThen c t e => c.issues row ++ if (c.eval row).isTrue then t.issues row else e.issues row
  -- The lambda runs on every element.
  | .hof _ l b => l.issues row ++ (l.eval row).elems.flatMap fun x => b.issues (x :: row)

-- `AND` and `OR` evaluate both operands (D19, #604): `x <> 0 AND 10 / x > 1`
-- divides by zero on `x = 0`; guarding the division with a `CASE` does not.
#guard letI := Boxes.Ambient.none; (Expr.issues [.int 0] (.bin .and (.un .not (.bin .eq (.field 0) (.lit (.int 0))))
  (.bin .lt (.lit (.int 1)) (.bin .idiv (.lit (.int 10)) (.field 0))))).length == 1
#guard letI := Boxes.Ambient.none; (Expr.issues [.int 0] (.bin .lt (.lit (.int 1))
  (.ifThen (.un .not (.bin .eq (.field 0) (.lit (.int 0)))) (.bin .idiv (.lit (.int 10)) (.field 0))
    (.lit .null)))).isEmpty

end Substrait
