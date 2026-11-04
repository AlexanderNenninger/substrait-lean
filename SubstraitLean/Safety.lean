import SubstraitLean.Contracts

/-!
# Runtime errors

DataFusion fails at run time on integer division or remainder by zero, on
`MIN / -1`, on integer powers with a negative exponent or a result outside
64 bits, on `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, on
an invalid regular expression, on `repeat` writing more than `2³¹ - 1`
bytes, on `date_trunc` to a week, month, quarter or
year outside ±2⁶³ nanoseconds, and on date arithmetic (`DATE ± days`, adding
months) outside the years `chrono` represents. `date_trunc` of a DATE goes
through nanoseconds and gives garbage outside them (1677 to 2262), which is
reported as an error too. Integer `+`, `-`, `*` and negation do not fail in
DataFusion: they wrap around silently; so does `date_trunc` to a day or less
below `-2⁶³`. The reference raises there (#202: `overflow` omitted means
ERROR, at the declared width), and an error allows DataFusion's answer. All
of these are `Issue`s and errors, an integer `SUM` that leaves 64 bits too
(`Issue.sumWraps`, which the job also checks while it runs). So are arguments
outside a function's domain (`sqrt` of a negative, a shift by 64, …,
`SubstraitLean/Numeric.lean`), where the reference raises and DataFusion
gives an IEEE value or a wrapped shift instead: an error allows that.

**When does DataFusion evaluate an expression?** (Checked against DataFusion
51; this is the trusted part of the model.)

* `CASE` evaluates a branch only on rows that take it, so
  `CASE WHEN b <> 0 THEN a / b END` and `a / NULLIF(b, 0)` are safe.
* `AND` and `OR` evaluate both sides: `b <> 0 AND a / b > 1` fails on `b = 0`.
* Not every `CASE` is lazy, though. `COALESCE` evaluates all its arguments,
  and the simplifier rewrites a `CASE` with a boolean value into `AND`/`OR`,
  so `CASE WHEN b <> 0 THEN a / b > 1 ELSE false END` fails on `b = 0`. The
  parser makes those eager (`Parse.eagerly`); `Expr.ifThen` itself is lazy.
* `ABS` fails on the smallest integer (the parser writes `-a` as `a / -1`),
  and the simplifier makes `POWER(x, 0)` the constant 1, so it never fails.
* The optimizer merges filters and pushes them down through projections and
  joins, so a filter condition may be evaluated on rows that a filter below it
  would remove: `t.filter(b != 0).filter(a / b > 1)` fails on `b = 0`.
  `Rel.loose` is the input with those filters removed (and inner joins
  widened to cross joins); filter and join conditions are evaluated on it.
* A projection is evaluated on the rows that reach it. Under a filter or a
  join condition, though, its expressions may be inlined into that condition,
  so there they count as evaluated on the loose rows too.

`Rel.HasIssue` states this; `Rel.mayIssues` over-approximates it with the
abstract evaluation of `SubstraitLean/Contracts.lean`, and
`Rel.mayIssues_sound` proves that every issue that can happen is reported.
-/

namespace Substrait

open FloatCode (minI64 maxI64 castLo castHi)

inductive Issue where
  /-- Integer division or remainder by zero, or a double divided by zero. -/
  | divByZero
  /-- A result outside 64 bits where DataFusion fails (`MIN / -1`, `POWER`),
  a `repeat` beyond `Text.repeatMax` bytes, or a decimal of more digits than
  its precision (`UnFn.decimal`). -/
  | overflow
  /-- `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value. -/
  | badCast
  /-- `POWER` of integers with a negative exponent. -/
  | negExponent
  /-- A regular expression outside `Text.simpleRegex`, which may not compile. -/
  | badRegex
  /-- `+`, `-`, `*` or negation whose result does not fit its declared width:
  64 bits, or narrower integers (`UnFn.wrap`). With `overflow` omitted or
  `ERROR`, the reference raises (#202); DataFusion wraps around instead,
  which an error allows (a refinement). -/
  | wraps
  /-- A `SUM` leaving its type (`Measure.sumOk`): 64 bits for integers, the
  result's precision for decimals (#316). The reference raises, and so does
  the SQL sverify writes, which keeps its check while the job runs (DuckDB
  raises on a decimal `SUM` that leaves 38 digits). An error like any other:
  a plan that may raise is not proved, unless the input's rows and the
  argument's range bound the sum (`Measure.sumFits`). Kept apart from
  `wraps` because it comes from a group's rows, not from one row:
  `SubstraitLean/Guards.lean` drops row-level checks, never this one. -/
  | sumWraps
  /-- An argument outside a function's domain (`SubstraitLean/Numeric.lean`):
  `sqrt` of a negative, a logarithm of zero or a negative, `asin` or `acos`
  outside `[-1, 1]`, `atan2(0, 0)`, `logb` to a base that is not positive or
  is 1, a shift count outside `0`–`63`, a `substring` offset outside
  `[-2³², 2³²)` or length of `2³²` or more (`Text.substrInRange`, #336,
  where DuckDB raises too). The reference raises (Substrait's
  `on_domain_error` = ERROR); DataFusion gives NaN, ±∞ or a wrapped shift
  instead, which an error allows (a refinement, epic #185). -/
  | domain
  /-- Raised by a shim's guard (`UnFn.raise`, #185), where an engine would
  answer while the reference raises. Plans `verify` checks have none. -/
  | raised
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

/-- The aggregates among a list of window functions. -/
def WinFn.aggs (fns : List WinFn) : List Measure :=
  fns.filterMap fun
    | .agg m _ _ => some m
    | _ => none

/-- Errors are what a proof must rule out: every issue raises. -/
def Issue.isError : Issue → Bool
  | _ => true

def inI64 (i : Int) : Bool := decide (minI64 ≤ i) && decide (i ≤ maxI64)

def wrapIf (i : Int) : Option Issue := if inI64 i then none else some .wraps

/-- A domain error where a partial function has no result. -/
def domainIssue (r : Option Int) : Option Issue := if r.isSome then none else some .domain

def withinRange (lo hi i : Int) : Bool := decide (lo ≤ i) && decide (i ≤ hi)

/-- `overflow` unless the argument `x` and the result `y` are in `[lo, hi]`:
the dates and timestamps `chrono` represents, or DataFusion's nanoseconds. -/
def rangeIssue (lo hi x y : Int) : Option Issue :=
  if withinRange lo hi x && withinRange lo hi y then none else some .overflow

/-! ## What goes wrong on a row -/

def UnFn.issue : UnFn → Value → Option Issue
  -- A black box that may raise, where it does (#325).
  | .bbox n, v => if BlackBox.raisesOn n [v] then some .domain else none
  | .neg, .int i => wrapIf (-i)
  | .ftoi, .int c => match FloatCode.toInt? c with
    | some x => if inI64 x then none else some .badCast
    | none => some .badCast
  | .narrow n, .int i => if fitsBits n i then none else some .badCast
  | .wrap n, .int i => if fitsBits n i then none else some .wraps
  -- The pattern is compiled whatever the input.
  | .regexMatch p, _ => if Text.simpleRegex p then none else some .badRegex
  | .dateTrunc u, .int ts =>
    if u.calendar then
      if ts ≤ Time.nsMax ∧ Time.nsMin ≤ Time.trunc u ts then none else some .overflow
    else wrapIf (Time.trunc u ts)
  | .dayTrunc u, .int d => rangeIssue Time.nsDayMin Time.nsDayMax d (Time.truncDay u d)
  | .addMonths m false, .int d => rangeIssue Time.dayMin Time.dayMax d (Time.addMonths m d)
  | .addMonths m true, .int ts => rangeIssue Time.partMin Time.partMax ts (Time.addMonthsUs m ts)
  -- chrono's calendar, which fails outside its years.
  | .timeOfDay, .int ts | .strftime _, .int ts => rangeIssue Time.partMin Time.partMax ts ts
  -- DataFusion bins in nanoseconds, which wrap around outside ±2⁶³.
  | .bucket k o, .int ts => rangeIssue Time.nsMin Time.nsMax ts (Time.bucket k o ts)
  | .fmath f, .int c => domainIssue (f.apply c)
  | .decimal p _, .int i => if fitsDigits p i then none else some .overflow
  -- NaN and ±∞ have no decimal.
  | .ftod s, .int c => if (FloatCode.toDecimal? c s).isSome then none else some .badCast
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
  | .fmul, a, b => (a == 0 && isInfCode b) || (isInfCode a && b == 0)
  | .fdiv, a, b => isInfCode a && isInfCode b
  | .fmod, a, b => isInfCode a && b != FloatCode.nan
  | .fpow, a, b => decide (FloatCode.negInf < a) && decide (a < 0) &&
      decide (FloatCode.negInf < b) && decide (b < FloatCode.posInf) && FloatCode.floor b != b
  | _, _, _ => false

def nanIssue (f : BinFn) (a b : Int) : Option Issue := if nanCase f a b then some .domain else none

def BinFn.issue : BinFn → Value → Value → Option Issue
  | .bbox2 n, v, w => if BlackBox.raisesOn n [v, w] then some .domain else none
  | .add, .int a, .int b => wrapIf (a + b)
  | .sub, .int a, .int b => wrapIf (a - b)
  | .mul, .int a, .int b => wrapIf (a * b)
  | .dateAdd, .int a, .int b => rangeIssue Time.dayMin Time.dayMax a (a + b)
  | .idiv, .int a, .int b =>
    if b = 0 then some .divByZero else if inI64 (a.tdiv b) then none else some .overflow
  | .imod, .int _, .int b => if b = 0 then some .divByZero else none
  -- A double divided by zero (the code of `0.0`): Substrait's
  -- `on_division_by_zero` = ERROR. The parser writes the other options as a
  -- `CASE` around this (`Parse.divByZero`).
  | .fdiv, .int a, .int b => if b = 0 then some .divByZero else nanIssue .fdiv a b
  | .fmod, .int a, .int b => if b = 0 then some .divByZero else nanIssue .fmod a b
  | .fadd, .int a, .int b => nanIssue .fadd a b
  | .fsub, .int a, .int b => nanIssue .fsub a b
  | .fmul, .int a, .int b => nanIssue .fmul a b
  | .fpow, .int a, .int b => nanIssue .fpow a b
  | .ipow, .int a, .int b =>
    if b < 0 then some .negExponent
    else if 64 < b ∧ 1 < a.natAbs then some .overflow
    else if inI64 (a ^ b.toNat) then none else some .overflow
  | .strRepeat, .str s, .int n => if Text.repeatFits s n then none else some .overflow
  | .substr n _, .str _, .int a => if Text.substrInRange a n then none else some .domain
  | .fatan2, .int y, .int x => domainIssue (atan2? y x)
  | .flogb, .int x, .int b => domainIssue (logb? x b)
  | .bit op, .int a, .int b => domainIssue (op.apply a b)
  | _, _, _ => none

/-- The issues evaluating `e` on `row` runs into, each with the operation
that raises it. A `CASE` only evaluates the branch it takes. -/
def Expr.issues (row : Row) : Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | .un f a => a.issues row ++ ((f.issue (a.eval row)).map (·, .un f a)).toList
  | .bin f a b =>
    a.issues row ++ b.issues row ++ ((f.issue (a.eval row) (b.eval row)).map (·, .bin f a b)).toList
  | .ifThen c t e => c.issues row ++ if (c.eval row).isTrue then t.issues row else e.issues row
  -- The lambda runs on every element.
  | .hof _ l b => l.issues row ++ (l.eval row).elems.flatMap fun x => b.issues [x]

/-! ## What may go wrong, abstractly -/

def Bound.inI64 (b : Bound) : Bool := b.lo.any (minI64 ≤ ·) && b.hi.any (· ≤ maxI64)

/-- Every integer `a` describes fits in 64 bits. -/
def AVal.intFits (a : AVal) : Bool := a.int.all Bound.inI64

theorem AVal.inI64_of_fits {a : AVal} {i : Int} (h : a.intFits = true) (hm : a.Mem (.int i)) :
    inI64 i = true := by
  obtain ⟨b, hb, hi⟩ := hm
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.intFits, hb, Option.all_some, Bound.inI64] at h
  simp only [Bound.Mem] at hi
  cases bl <;> cases bh <;> simp_all [inI64] <;> constructor <;> omega

/-- Every integer `a` describes is in `[lo, hi]`. -/
def AVal.within (lo hi : Int) (a : AVal) : Bool :=
  a.int.all fun b => b.lo.any (lo ≤ ·) && b.hi.any (· ≤ hi)

theorem AVal.withinRange_of_within {a : AVal} {lo hi i : Int} (h : a.within lo hi = true)
    (hm : a.Mem (.int i)) : withinRange lo hi i = true := by
  obtain ⟨b, hb, hi⟩ := hm
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.within, hb, Option.all_some, Bool.and_eq_true, Option.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨l, rfl, hl⟩, ⟨u, rfl, hu⟩⟩ := h
  have := hi.1 l rfl
  have := hi.2 u rfl
  simp only [withinRange, Bool.and_eq_true, decide_eq_true_eq]; omega

def rangeMay (lo hi : Int) (aa ar : AVal) : List Issue :=
  if aa.within lo hi && ar.within lo hi then [] else [.overflow]

theorem rangeIssue_sound {lo hi x y : Int} {aa ar : AVal} {k : Issue} (ha : aa.Mem (.int x))
    (hr : ar.Mem (.int y)) (hk : rangeIssue lo hi x y = some k) : k ∈ rangeMay lo hi aa ar := by
  simp only [rangeIssue] at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
  subst hk
  simp only [rangeMay]
  split
  · rename_i hn hw
    simp only [Bool.and_eq_true] at hw
    simp [AVal.withinRange_of_within hw.1 ha, AVal.withinRange_of_within hw.2 hr] at hn
  · simp

/-- Every double code `a` describes has a decimal at scale `s`: the casts of
its bounds do (`FloatCode.toDecimal?_between`, #223). -/
def AVal.decFits (s : Nat) (a : AVal) : Bool := a.int.all fun b =>
  match b.lo, b.hi with
  | some l, some h => (FloatCode.toDecimal? l s).isSome && (FloatCode.toDecimal? h s).isSome
  | _, _ => false

/-- Every double code `a` describes casts to a `BIGINT`. -/
def AVal.castFits (a : AVal) : Bool := a.int.all fun b => b.lo.any (castLo ≤ ·) && b.hi.any (· ≤ castHi)

/-- Every timestamp `aa` describes, and its truncation `ar`, is within
DataFusion's nanosecond range. -/
def nsFits (aa ar : AVal) : Bool :=
  aa.int.all (·.hi.any (· ≤ Time.nsMax)) && ar.int.all (·.lo.any (Time.nsMin ≤ ·))

def UnFn.mayIssue : UnFn → AVal → AVal → List Issue
  | .neg, _, ar => if ar.intFits then [] else [.wraps]
  | .ftoi, aa, _ => if aa.castFits then [] else [.badCast]
  | .narrow n, aa, _ => if aa.int.all (·.fitsBits n) then [] else [.badCast]
  | .wrap n, aa, _ => if aa.int.all (·.fitsBits n) then [] else [.wraps]
  | .regexMatch p, _, _ => if Text.simpleRegex p then [] else [.badRegex]
  | .dateTrunc u, aa, ar =>
    if u.calendar then (if nsFits aa ar then [] else [.overflow])
    else if ar.intFits then [] else [.wraps]
  | .dayTrunc _, aa, ar => rangeMay Time.nsDayMin Time.nsDayMax aa ar
  | .addMonths _ false, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .addMonths _ true, aa, ar => rangeMay Time.partMin Time.partMax aa ar
  | .timeOfDay, aa, _ | .strftime _, aa, _ => rangeMay Time.partMin Time.partMax aa aa
  | .bucket _ _, aa, ar => rangeMay Time.nsMin Time.nsMax aa ar
  | .fmath f, aa, _ => if f.safe aa then [] else [.domain]
  | .decimal p _, aa, _ => if aa.int.all (·.fitsDigits p) then [] else [.overflow]
  | .ftod s, aa, _ => if aa.decFits s then [] else [.badCast]
  | .raise _, _, _ => [.raised]
  | .bbox n, _, _ => if BlackBox.mayRaise n then [.domain] else []
  | _, _, _ => []

/-- `|a|ᵏ` for the largest `|a|` in a finite interval. -/
def Bound.powMax (b : Bound) (k : Nat) : Option Nat :=
  match b.lo, b.hi with
  | some l, some h => some (max l.natAbs h.natAbs ^ k)
  | _, _ => none

/-- `aᵇ` fits: `b` is a constant in `[0, 64]` and `|a|ᵇ ≤ 2⁶³ - 1`. -/
def powFits (aa ab : AVal) : Bool :=
  match aa.int, ab.int with
  | some x, some y => match y.point with
    | some k => decide (0 ≤ k) && decide (k ≤ 64) &&
        (x.powMax k.toNat).any fun m => decide ((m : Int) ≤ maxI64)
    | none => false
  | _, _ => true

/-- The UTF-8 size of a constant string. -/
def Expr.strBytes? : Expr → Option Nat
  | .lit (.str s) => some s.utf8ByteSize
  | _ => none

/-- `repeat(s, n)` fits for every `n` of `ab`, where `s` has `sz` bytes if
it is a constant: `n ≤ 0`, or `sz · n ≤ Text.repeatMax`. -/
def repeatFitsAbs : Option Nat → AVal → Bool
  | some m, ab => m == 0 || ab.int.all (·.hi.any fun h => decide ((m : Int) * h ≤ Text.repeatMax))
  | none, ab => ab.int.all (·.hi.any (· ≤ 0))

def repeatMay (sz : Option Nat) (ab : AVal) : List Issue :=
  if repeatFitsAbs sz ab then [] else [.overflow]

/-- Is every offset of `ab`, and the length `n`, within `substring`'s range
(`Text.substrInRange`)? -/
def substrSafe (n : Option Nat) (ab : AVal) : Bool :=
  n.all (fun n => decide ((n : Int) < Text.substrMax)) &&
    ab.int.all fun b => b.lo.any (-Text.substrMax ≤ ·) && b.hi.any (· < Text.substrMax)

/-- May `a` be the double with code `c`? -/
def AVal.has (a : AVal) (c : Int) : Bool := a.int.any fun b => b.lo.all (· ≤ c) && b.hi.all (c ≤ ·)

/-- May `a` be a finite negative double? -/
def AVal.negFinite (a : AVal) : Bool :=
  a.int.any fun b => b.lo.all (· < 0) && b.hi.all (FloatCode.negInf < ·)

/-- May the inputs be a `nanCase` of `f`? -/
def BinFn.mayNan (f : BinFn) (aa ab : AVal) : Bool :=
  let inf (x : AVal) := x.has FloatCode.posInf || x.has FloatCode.negInf
  match f with
  | .fadd => (aa.has FloatCode.posInf && ab.has FloatCode.negInf) ||
      (aa.has FloatCode.negInf && ab.has FloatCode.posInf)
  | .fsub => (aa.has FloatCode.posInf && ab.has FloatCode.posInf) ||
      (aa.has FloatCode.negInf && ab.has FloatCode.negInf)
  | .fmul => (aa.has 0 && inf ab) || (inf aa && ab.has 0)
  | .fdiv => inf aa && inf ab
  | .fmod => inf aa
  -- An integer exponent (`x ** 2`) is fine.
  | .fpow => aa.negFinite && !(ab.int.any fun b => b.point.any fun k => FloatCode.floor k == k)
  | _ => false

theorem AVal.has_of_mem {a : AVal} {i : Int} (h : a.Mem (.int i)) : a.has i = true := by
  obtain ⟨b, hb, hm⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.has, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => hm.1 l hl, fun u hu => hm.2 u hu⟩

theorem AVal.negFinite_of_mem {a : AVal} {i : Int} (h : a.Mem (.int i))
    (h1 : FloatCode.negInf < i) (h2 : i < 0) : a.negFinite = true := by
  obtain ⟨b, hb, hm⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.negFinite, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => by have := hm.1 l hl; omega, fun u hu => by have := hm.2 u hu; omega⟩

/-- An IEEE NaN case of the inputs is one `BinFn.mayNan` reports. -/
theorem BinFn.mayNan_sound {f : BinFn} {aa ab : AVal} {a b : Int} (ha : aa.Mem (.int a))
    (hb : ab.Mem (.int b)) (h : nanCase f a b = true) : BinFn.mayNan f aa ab = true := by
  have hA := fun {c : Int} (e : a = c) => AVal.has_of_mem (e ▸ ha)
  have hB := fun {c : Int} (e : b = c) => AVal.has_of_mem (e ▸ hb)
  cases f <;> simp only [nanCase, Bool.false_eq_true] at h
  all_goals simp only [BinFn.mayNan, isInfCode, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h ⊢
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hA h1, hB h2⟩
    · exact .inr ⟨hA h1, hB h2⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hA h1, hB h2⟩
    · exact .inr ⟨hA h1, hB h2⟩
  · rcases h with ⟨h1, h2 | h2⟩ | ⟨h1 | h1, h2⟩
    · exact .inl ⟨hA h1, .inl (hB h2)⟩
    · exact .inl ⟨hA h1, .inr (hB h2)⟩
    · exact .inr ⟨.inl (hA h1), hB h2⟩
    · exact .inr ⟨.inr (hA h1), hB h2⟩
  · obtain ⟨h1 | h1, h2 | h2⟩ := h
    all_goals exact ⟨by first | exact .inl (hA h1) | exact .inr (hA h1),
      by first | exact .inl (hB h2) | exact .inr (hB h2)⟩
  · obtain ⟨h1 | h1, _⟩ := h
    · exact .inl (hA h1)
    · exact .inr (hA h1)
  · obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, h5⟩ := h
    simp only [decide_eq_true_eq] at h1 h2
    refine ⟨AVal.negFinite_of_mem ha h1 h2, ?_⟩
    obtain ⟨bd, hbd, hm⟩ := hb
    rw [hbd]
    simp only [Option.any_some]
    cases hp : bd.point with
    | none => rfl
    | some k =>
      have := Bound.point_mem hp hm
      subst this
      simpa using h5

/-- `nz`: the divisor is never the integer 0; `sz`: the first argument's
size, if it is a constant string. -/
def BinFn.mayIssue : BinFn → AVal → AVal → AVal → Bool → Option Nat → List Issue
  | .add, _, _, ar, _, _ | .sub, _, _, ar, _, _ | .mul, _, _, ar, _, _ =>
    if ar.intFits then [] else [.wraps]
  | .dateAdd, aa, _, ar, _, _ => rangeMay Time.dayMin Time.dayMax aa ar
  | .idiv, _, _, ar, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if ar.intFits then [] else [.overflow])
  | .imod, _, _, _, nz, _ => if nz then [] else [.divByZero]
  | .fdiv, aa, ab, _, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if BinFn.mayNan .fdiv aa ab then [.domain] else [])
  | .fmod, aa, ab, _, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if BinFn.mayNan .fmod aa ab then [.domain] else [])
  | .fadd, aa, ab, _, _, _ => if BinFn.mayNan .fadd aa ab then [.domain] else []
  | .fsub, aa, ab, _, _, _ => if BinFn.mayNan .fsub aa ab then [.domain] else []
  | .fmul, aa, ab, _, _, _ => if BinFn.mayNan .fmul aa ab then [.domain] else []
  | .fpow, aa, ab, _, _, _ => if BinFn.mayNan .fpow aa ab then [.domain] else []
  | .ipow, aa, ab, _, _, _ =>
    (if ab.int.all (·.lo.any (0 ≤ ·)) then [] else [.negExponent]) ++
      (if powFits aa ab then [] else [.overflow])
  | .strRepeat, _, ab, _, _, sz => repeatMay sz ab
  | .substr n _, _, ab, _, _, _ => if substrSafe n ab then [] else [.domain]
  | .fatan2, aa, ab, _, _, _ => if BinFn.domainSafe .fatan2 aa ab then [] else [.domain]
  | .flogb, aa, ab, _, _, _ => if BinFn.domainSafe .flogb aa ab then [] else [.domain]
  | .bit op, aa, ab, _, _, _ => if BinFn.domainSafe (.bit op) aa ab then [] else [.domain]
  | .bbox2 n, _, _, _, _, _ => if BlackBox.mayRaise n then [.domain] else []
  | _, _, _, _, _, _ => []

/-- Is `x`'s value never the integer 0? From its interval, an assumption
`x ≠ 0`, a fact `$j ≠ -c` for `x = $j + c`, both branches of a `CASE`, or both
factors of a product. -/
def Expr.nonZero (env : List AVal) (fs : List Fact) (ks : Assumptions) (x : Expr) : Bool :=
  (x.absD env fs ks).int.all (!·.has0) ||
  ks.any (fun sk => sk.1 == x && match sk.2 with | .ne 0 => true | _ => false) ||
  (match x.linTerm with | some (j, c) => fs.contains (.ne j (-c)) | none => false) ||
  match x with
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    (!ac.tt || t.nonZero (c.refine env) fs (c.cstrs true ++ ks)) &&
      (!(ac.nonBool || ac.ff) || e.nonZero (c.refineNeg env) fs (c.cstrs false ++ ks))
  -- A product of non-zero integers (exact in the model; overflow is an error).
  | .bin .mul a b => a.nonZero env fs ks && b.nonZero env fs ks
  -- A non-zero integer is a non-zero double (`FloatCode.ofInt_ne_zero`).
  | .un .itof a => a.nonZero env fs ks
  | _ => false

def Expr.mayIssues (env : List AVal) (fs : List Fact) (ks : Assumptions := []) :
    Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | .un f a =>
    a.mayIssues env fs ks ++
      (f.mayIssue (a.absD env fs ks) ((Expr.un f a).absD env fs ks)).map (·, .un f a)
  | .bin f a b =>
    a.mayIssues env fs ks ++ b.mayIssues env fs ks ++
      (f.mayIssue (a.absD env fs ks) (b.absD env fs ks) ((Expr.bin f a b).absD env fs ks)
        (b.nonZero env fs ks) a.strBytes?).map (·, .bin f a b)
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    c.mayIssues env fs ks ++
      (if ac.tt then t.mayIssues (c.refine env) fs (c.cstrs true ++ ks) else []) ++
      (if ac.nonBool || ac.ff then e.mayIssues (c.refineNeg env) fs (c.cstrs false ++ ks) else [])
  -- The body on any element: it reads only its parameter.
  | .hof _ l b => l.mayIssues env fs ks ++ b.mayIssues [AVal.top] [] []

/-! ## Soundness for expressions -/

theorem Expr.nonZero_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ (x : Expr), x.nonZero env fs ks = true → ∀ j, x.eval row = .int j → j ≠ 0 := by
  intro x hnz j hj
  unfold Expr.nonZero at hnz
  simp only [Bool.or_eq_true] at hnz
  rcases hnz with ((hb | hk) | hl) | hc
  · -- the interval excludes 0
    have hm := Expr.absD_sound h hfs hks x
    rw [hj] at hm
    obtain ⟨b, hb', hm⟩ := hm
    simp only [hb', Option.all_some, Bool.not_eq_true'] at hb
    exact Bound.ne_zero hm hb
  · -- an assumption `x ≠ 0`
    obtain ⟨sk, hsk, he⟩ := List.any_eq_true.mp hk
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨rfl, hne⟩ := he
    have := hks sk hsk
    match hk' : sk.2, hne with
    | .ne 0, _ => rw [hk'] at this; exact this j hj
  · -- a fact `$j ≠ -c`
    split at hl
    · rename_i j' c hlin
      obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_int hlin hj
      have hf := hfs _ (List.contains_iff_mem.mp hl)
      simp only [Fact.Holds] at hf
      rw [hy] at hf
      intro h0; apply hf; congr 1; omega
    · simp at hl
  · -- a `CASE` whose reachable branches are both non-zero
    split at hc
    · rename_i c t e
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
      obtain ⟨ht, he⟩ := hc
      simp only [eval] at hj
      have hcm := Expr.absD_sound h hfs hks c
      by_cases hct : (c.eval row).isTrue = true
      · simp only [hct, ite_true] at hj
        rcases ht with ht | ht
        · rw [Value.eq_true_of_isTrue hct] at hcm; simp_all [AVal.Mem]
        · exact Expr.nonZero_sound (Expr.refine_sound env c h hct) hfs
            (KsHold.cons_cstrs hct hks) t ht j hj
      · simp only [hct, ite_false, Bool.false_eq_true] at hj
        have hf : (c.eval row).isTrue = false := by simpa using hct
        rcases he with he | he
        · rcases mem_cases hcm with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp_all [AVal.nonBool]
          · simp_all [AVal.nonBool]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp_all
          · simp_all [AVal.nonBool]
          · simp_all [AVal.nonBool]
        · exact Expr.nonZero_sound (Expr.refineNeg_sound env c h hf) hfs
            (KsHold.cons_cstrs hf hks) e he j hj
    · rename_i a b
      simp only [Bool.and_eq_true] at hc
      simp only [eval] at hj
      cases ha : a.eval row <;> cases hb : b.eval row <;> simp [ha, hb, BinFn.apply] at hj
      rename_i x y
      subst hj
      exact Int.mul_ne_zero (Expr.nonZero_sound h hfs hks a hc.1 x ha)
        (Expr.nonZero_sound h hfs hks b hc.2 y hb)
    · rename_i a
      simp only [eval] at hj
      cases ha : a.eval row <;> simp [ha, UnFn.apply] at hj
      rename_i i
      subst hj
      exact FloatCode.ofInt_ne_zero (Expr.nonZero_sound h hfs hks a hc i ha)
    · simp at hc

theorem UnFn.mayIssue_sound (f : UnFn) {aa ar : AVal} {v : Value} {k : Issue}
    (ha : aa.Mem v) (hr : ar.Mem (f.apply v)) (hk : f.issue v = some k) : k ∈ f.mayIssue aa ar := by
  cases f
  case bbox n =>
    simp only [UnFn.issue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i h
    simp [UnFn.mayIssue, BlackBox.mayRaise_of_raisesOn h]
  all_goals (cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk)
  case raise.null | raise.bool | raise.int | raise.str | raise.list =>
    simp only [Option.some.injEq] at hk; subst hk; simp [UnFn.mayIssue]
  case fmath.int f c =>
    simp only [domainIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [UnFn.mayIssue]
    split
    · rename_i hn hs
      simp [FMath.apply, FMath.inDomain_of_safe hs ha] at hn
    · simp
  case neg.int i =>
    simp only [wrapIf] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [UnFn.mayIssue]
    split
    · rename_i hn hfits
      exact absurd (AVal.inI64_of_fits hfits (by simpa [UnFn.apply] using hr)) hn
    · simp
  case ftoi.int c =>
    simp only [UnFn.mayIssue]
    split
    · rename_i hfits
      exfalso
      obtain ⟨b, hb, hc⟩ := ha
      obtain ⟨bl, bh⟩ := b
      simp only [AVal.castFits, hb, Option.all_some, Bool.and_eq_true, Option.any_eq_true,
        decide_eq_true_eq] at hfits
      obtain ⟨⟨lo, hlo, hlo'⟩, ⟨hi, hhi, hhi'⟩⟩ := hfits
      subst hlo hhi
      obtain ⟨x, hx, hx₁, hx₂⟩ :=
        FloatCode.toInt?_of_range (Int.le_trans hlo' (hc.1 _ rfl)) (Int.le_trans (hc.2 _ rfl) hhi')
      rw [hx] at hk
      simp [inI64, hx₁, hx₂] at hk
    · cases hx : FloatCode.toInt? c <;> simp only [hx] at hk <;> (try split at hk) <;> simp_all
  case narrow.int n i =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    split
    · rename_i hn hfits
      obtain ⟨b, hb, hi⟩ := ha
      simp only [hb, Option.all_some] at hfits
      exact absurd (Bound.fitsBits_mem hfits hi) hn
    · simp_all
  case wrap.int n i =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    split
    · rename_i hn hfits
      obtain ⟨b, hb, hi⟩ := ha
      simp only [hb, Option.all_some] at hfits
      exact absurd (Bound.fitsBits_mem hfits hi) hn
    · simp_all
  case decimal.int p s i =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    split
    · rename_i hn hfits
      obtain ⟨b, hb, hi⟩ := ha
      simp only [hb, Option.all_some] at hfits
      exact absurd (Bound.fitsDigits_mem hfits hi) hn
    · simp_all
  case ftod.int s c =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    split
    · rename_i hnone hfits
      exfalso
      obtain ⟨b, hb, hc⟩ := ha
      obtain ⟨bl, bh⟩ := b
      simp only [AVal.decFits, hb, Option.all_some] at hfits
      split at hfits
      · simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfits
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hfits
        obtain ⟨q, hq, -, -⟩ := FloatCode.toDecimal?_between (hc.1 _ rfl) (hc.2 _ rfl) hx hy
        rw [hq] at hnone; simp at hnone
      · cases hfits
    · simp
  case regexMatch.null | regexMatch.int | regexMatch.bool | regexMatch.str | regexMatch.list =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp_all
  case dateTrunc.int u ts =>
    simp only [UnFn.mayIssue]
    cases hc : u.calendar <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    · simp only [wrapIf] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      split
      · rename_i hn hfits
        exact absurd (AVal.inI64_of_fits hfits (by simpa [UnFn.apply] using hr)) hn
      · simp
    · split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      split
      · rename_i hout hfits
        exfalso; apply hout
        simp only [nsFits, Bool.and_eq_true, Option.all_eq_true] at hfits
        obtain ⟨b, hb, hm⟩ := ha
        obtain ⟨b', hb', hm'⟩ : ar.Mem (.int (Time.trunc u ts)) := by simpa [UnFn.apply] using hr
        have h1 := hfits.1 b hb
        have h2 := hfits.2 b' hb'
        obtain ⟨bl, bh⟩ := b
        obtain ⟨bl', bh'⟩ := b'
        simp only [Bound.Mem] at hm hm'
        cases bh <;> cases bl' <;> simp_all <;> constructor <;> omega
      · simp
  case dayTrunc.int u d => exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk
  case timeOfDay.int ts => exact rangeIssue_sound ha ha hk
  case strftime.int fmt ts => exact rangeIssue_sound ha ha hk
  case bucket.int k o ts => exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk
  case addMonths.int m t x =>
    cases t
    · exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk
    · exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk

theorem repeatMay_sound {sz : Option Nat} {ab : AVal} {s : String} {n : Int}
    (hb : ab.Mem (.int n)) (hsz : ∀ m, sz = some m → s.utf8ByteSize = m)
    (hk : Text.repeatFits s n = false) : Issue.overflow ∈ repeatMay sz ab := by
  obtain ⟨y, hy, hn⟩ := hb
  simp only [repeatMay]
  split
  · rename_i hfits
    exfalso
    simp only [Text.repeatFits, decide_eq_false_iff_not, Nat.not_le] at hk
    have hpos : 0 < n := by
      rcases Int.lt_or_le 0 n with h | h
      · exact h
      · simp [Int.toNat_of_nonpos h] at hk
    cases sz with
    | some m =>
      have hs := hsz m rfl
      simp only [repeatFitsAbs, Bool.or_eq_true, beq_iff_eq, hy, Option.all_some,
        Option.any_eq_true, decide_eq_true_eq] at hfits
      rcases hfits with h0 | ⟨h, hh, hle⟩
      · subst h0; simp [hs] at hk
      · have hnh := hn.2 h hh
        have h1 : (s.utf8ByteSize : Int) * n ≤ (m : Int) * h := by
          rw [hs]; exact Int.mul_le_mul_of_nonneg_left hnh (Int.natCast_nonneg m)
        have h2 : ((s.utf8ByteSize * n.toNat : Nat) : Int) = (s.utf8ByteSize : Int) * n := by
          rw [Int.natCast_mul, Int.toNat_of_nonneg (Int.le_of_lt hpos)]
        have h3 : ((Text.repeatMax : Nat) : Int) < ((s.utf8ByteSize * n.toNat : Nat) : Int) :=
          Int.ofNat_lt.mpr hk
        omega
    | none =>
      simp only [repeatFitsAbs, hy, Option.all_some, Option.any_eq_true, decide_eq_true_eq] at hfits
      obtain ⟨h, hh, hle⟩ := hfits
      have := hn.2 h hh
      omega
  · simp

theorem substrSafe_sound {n : Option Nat} {ab : AVal} {a : Int} (hb : ab.Mem (.int a))
    (hs : substrSafe n ab = true) : Text.substrInRange a n = true := by
  obtain ⟨y, hy, hm⟩ := hb
  simp only [substrSafe, hy, Bool.and_eq_true, Option.all_some, Option.any_eq_true,
    decide_eq_true_eq] at hs
  obtain ⟨hn, ⟨l, hl, hle⟩, ⟨h, hh, hlt⟩⟩ := hs
  have h1 := hm.1 l hl
  have h2 := hm.2 h hh
  simp only [Text.substrInRange, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨by omega, by omega⟩, hn⟩

theorem BinFn.mayIssue_sound (f : BinFn) {aa ab ar : AVal} {v w : Value} {nz : Bool}
    {sz : Option Nat} {k : Issue}
    (ha : aa.Mem v) (hb : ab.Mem w) (hr : ar.Mem (f.apply v w))
    (hnz : nz = true → ∀ j, w = .int j → j ≠ 0)
    (hsz : ∀ m s, sz = some m → v = .str s → s.utf8ByteSize = m) (hk : f.issue v w = some k) :
    k ∈ f.mayIssue aa ab ar nz sz := by
  cases f
  case bbox2 n =>
    simp only [BinFn.issue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i h
    simp [BinFn.mayIssue, BlackBox.mayRaise_of_raisesOn h]
  all_goals (cases v <;> cases w <;> simp only [BinFn.issue, reduceCtorEq] at hk)
  case add.int.int i j | sub.int.int i j | mul.int.int i j =>
    simp only [wrapIf] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [BinFn.mayIssue]
    split
    · rename_i hn hfits
      exact absurd (AVal.inI64_of_fits hfits (by simpa [BinFn.apply] using hr)) hn
    · simp
  case dateAdd.int.int i j => exact rangeIssue_sound ha (by simpa [BinFn.apply] using hr) hk
  case fatan2.int.int i j | flogb.int.int i j | bit.int.int op i j =>
    simp only [domainIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [BinFn.mayIssue]
    split
    · rename_i hn hs
      first
        | exact absurd (BinFn.domainSafe_atan2 hs ha hb) hn
        | exact absurd (BinFn.domainSafe_logb hs ha hb) hn
        | exact absurd (BinFn.domainSafe_bit hs hb) hn
    · simp
  case strRepeat.str.int s n =>
    simp only [BinFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    rename_i hnf
    exact repeatMay_sound hb (fun m hm => hsz m s hm rfl) (by simpa using hnf)
  case substr.str.int n _ s a =>
    simp only [BinFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    rename_i hnr
    split
    · rename_i hs; exact absurd (substrSafe_sound hb hs) (by simpa using hnr)
    · simp
  case idiv.int.int i j =>
    simp only [BinFn.mayIssue, List.mem_append]
    split at hk
    · rename_i hj; simp only [Option.some.injEq] at hk; subst hk
      left; split
      · rename_i hnz'; exact absurd hj (hnz hnz' j rfl)
      · simp
    · rename_i hj
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      right; split
      · rename_i hn hfits
        exact absurd (AVal.inI64_of_fits hfits (by simpa [BinFn.apply, hj] using hr)) hn
      · simp
  case imod.int.int i j =>
    simp only [BinFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    split
    · rename_i hj hnz'; exact absurd hj (hnz hnz' j rfl)
    · simp
  case fdiv.int.int i j | fmod.int.int i j =>
    simp only [BinFn.mayIssue, List.mem_append]
    split at hk
    · rename_i hj; simp only [Option.some.injEq] at hk; subst hk
      left; split
      · rename_i hnz'; exact absurd hj (hnz hnz' j rfl)
      · simp
    · simp only [nanIssue] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      rename_i hn
      right; simp [BinFn.mayNan_sound ha hb hn]
  case fadd.int.int i j | fsub.int.int i j | fmul.int.int i j | fpow.int.int i j =>
    simp only [BinFn.mayIssue]
    simp only [nanIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    rename_i hn
    simp [BinFn.mayNan_sound ha hb hn]
  case ipow.int.int i j =>
    simp only [BinFn.mayIssue, List.mem_append]
    obtain ⟨x, hx, hi⟩ := ha
    obtain ⟨y, hy, hj⟩ := hb
    split at hk
    · -- a negative exponent
      rename_i hneg; simp only [Option.some.injEq] at hk; subst hk
      left; split
      · rename_i hall
        exfalso
        obtain ⟨yl, yh⟩ := y
        simp only [hy, Option.all_some, Option.any_eq_true, decide_eq_true_eq] at hall
        obtain ⟨l, hl, hl'⟩ := hall
        have := hj.1 l hl; omega
      · simp
    · -- overflow
      right
      have hk' : k = .overflow := by
        split at hk <;> (try split at hk) <;> simp_all
      subst hk'
      split
      · rename_i hfits
        exfalso
        simp only [powFits, hx, hy] at hfits
        split at hfits
        · rename_i n hp
          have hjn := Bound.point_mem hp hj
          subst hjn
          obtain ⟨xl, xh⟩ := x
          cases xl with
          | none => simp [Bound.powMax] at hfits
          | some l =>
            cases xh with
            | none => simp [Bound.powMax] at hfits
            | some u =>
              simp only [Bound.powMax, Bool.and_eq_true, decide_eq_true_eq] at hfits
              obtain ⟨⟨h0, h64⟩, hmax⟩ := hfits
              have hl := hi.1 l rfl; have hu := hi.2 u rfl
              have habs : i.natAbs ≤ max l.natAbs u.natAbs := by omega
              have hpow : (i ^ j.toNat).natAbs ≤ max l.natAbs u.natAbs ^ j.toNat := by
                rw [Int.natAbs_pow]; exact Nat.pow_le_pow_left habs _
              simp only [maxI64] at hmax
              split at hk
              · omega
              · split at hk
                · simp at hk
                · rename_i hout
                  have hout' : -2 ^ 63 ≤ i ^ j.toNat → ¬ i ^ j.toNat ≤ 2 ^ 63 - 1 := by
                    intro h1 h2
                    simp only [inI64, minI64, maxI64, Bool.and_eq_true] at hout
                    exact hout ⟨decide_eq_true h1, decide_eq_true h2⟩
                  have hm : (↑(max l.natAbs u.natAbs) : Int) ^ j.toNat ≤ 2 ^ 63 - 1 :=
                    of_decide_eq_true (by simp at hmax; exact hmax)
                  have hpow' : ((i ^ j.toNat).natAbs : Int) ≤ (↑(max l.natAbs u.natAbs) : Int) ^ j.toNat := by
                    exact_mod_cast hpow
                  omega
        · simp at hfits
      · simp

theorem Expr.strBytes?_sound (row : Row) (e : Expr) :
    ∀ m s, e.strBytes? = some m → e.eval row = .str s → s.utf8ByteSize = m := by
  intro m s hm hs
  match e, hm with
  | .lit (.str t), hm =>
    simp only [Expr.strBytes?, Option.some.injEq] at hm
    simp only [Expr.eval, Value.str.injEq] at hs
    subst hs; exact hm

theorem Expr.mayIssues_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ (e : Expr), ∀ p ∈ e.issues row, p ∈ e.mayIssues env fs ks
  | .lit _, p, hp | .field _, p, hp => by simp [Expr.issues] at hp
  | .un f a, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with hp | hp
    · exact .inl (Expr.mayIssues_sound h hfs hks a p hp)
    · right
      cases hi : f.issue (a.eval row) with
      | none => simp [hi] at hp
      | some k =>
        simp only [hi, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        exact List.mem_map_of_mem (UnFn.mayIssue_sound f (Expr.absD_sound h hfs hks a)
          (Expr.absD_sound h hfs hks (.un f a)) hi)
  | .bin f a b, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with (hp | hp) | hp
    · exact .inl (.inl (Expr.mayIssues_sound h hfs hks a p hp))
    · exact .inl (.inr (Expr.mayIssues_sound h hfs hks b p hp))
    · right
      cases hi : f.issue (a.eval row) (b.eval row) with
      | none => simp [hi] at hp
      | some k =>
        simp only [hi, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        exact List.mem_map_of_mem (BinFn.mayIssue_sound f (Expr.absD_sound h hfs hks a)
          (Expr.absD_sound h hfs hks b) (Expr.absD_sound h hfs hks (.bin f a b))
          (fun hnz => Expr.nonZero_sound h hfs hks b hnz) (Expr.strBytes?_sound row a) hi)
  | .ifThen c t e, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    have hc := Expr.absD_sound h hfs hks c
    rcases hp with hp | hp
    · exact .inl (.inl (Expr.mayIssues_sound h hfs hks c p hp))
    · by_cases hct : (c.eval row).isTrue = true
      · simp only [hct, ite_true] at hp
        left; right
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.absD env fs ks).tt = true := hc
        simp only [htt, ite_true]
        exact Expr.mayIssues_sound (Expr.refine_sound env c h hct) hfs (KsHold.cons_cstrs hct hks) t p hp
      · simp only [hct, ite_false, Bool.false_eq_true] at hp
        right
        have hf : (c.eval row).isTrue = false := by simpa using hct
        have : ((c.absD env fs ks).nonBool || (c.absD env fs ks).ff) = true := by
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hff]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        simp only [this, ite_true]
        exact Expr.mayIssues_sound (Expr.refineNeg_sound env c h hf) hfs (KsHold.cons_cstrs hf hks) e p hp
  | .hof _ l b, p, hp => by
    simp only [Expr.issues, List.mem_append, List.mem_flatMap] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with hp | ⟨x, _, hp⟩
    · exact .inl (Expr.mayIssues_sound h hfs hks l p hp)
    · -- The body sees one element, which `AVal.top` describes.
      have hx : EnvMem [AVal.top] [x] := fun i => by
        cases i <;> simp [AVal.mem_top]
      exact .inr (Expr.mayIssues_sound hx (fun _ hf => by simp at hf)
        (fun _ hk => by simp at hk) b p hp)

/-! ## Plans -/

/-- The plan with the filters DataFusion may merge into or push past removed:
filters go, inner joins become cross joins, semi and anti joins, sorts and
`DISTINCT` give way to their (left) input. Fetches, windows and aggregates
stop it: filters do not move across them (a filter on grouping columns does,
but only to rows with the same grouping values). -/
def Rel.loose : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r _ => r.loose
  | .project r es => .project r.loose es
  | .emit r m => .emit r.loose m
  | .cross a b => .cross a.loose b.loose
  | .join a b .inner _ => .cross a.loose b.loose
  | .join a b .left on => .join a.loose b.loose .left on
  | .fetch r off cnt => .fetch r off cnt
  | .unionAll a b => .unionAll a.loose b.loose
  | .window r part sort fns => .window r part sort fns
  | .semi a _ _ _ => a.loose
  | .orderBy r _ | .distinct r => r.loose
  | .aggregate r gs ms => .aggregate r gs ms
  -- DataFusion pushes filters on the other columns below an `UNNEST`, onto
  -- rows whose lists may be empty: the loose rows are both.
  | .unnest r c => .unionAll (.unnest r.loose c) r.loose

theorem Rel.loose_arity (cat : Catalog) : ∀ r : Rel, r.loose.arity cat = r.arity cat
  | .read _ | .values _ _ | .fetch _ _ _ | .window _ _ _ _ | .aggregate _ _ _ => rfl
  | .filter r _ => by simp [loose, arity, loose_arity cat r]
  | .project r _ => by simp [loose, arity, loose_arity cat r]
  | .emit _ _ => rfl
  | .cross a b => by simp [loose, arity, loose_arity cat a, loose_arity cat b]
  | .join a b .inner _ | .join a b .left _ => by
      simp [loose, arity, loose_arity cat a, loose_arity cat b]
  | .unionAll a _ => by simp [loose, arity, loose_arity cat a]
  | .semi a _ _ _ => by simp [loose, arity, loose_arity cat a]
  | .orderBy r _ | .distinct r => by simp [loose, arity, loose_arity cat r]
  | .unnest r _ => by simp [loose, arity, loose_arity cat r]

theorem Rel.loose_wf {cat : Catalog} : ∀ {r : Rel}, r.WF cat → r.loose.WF cat
  | .read _, h | .values _ _, h | .fetch _ _ _, h | .window _ _ _ _, h | .aggregate _ _ _, h => h
  | .filter r _, h => loose_wf (r := r) h.1
  | .project r _, h => ⟨loose_wf (r := r) h.1, by rw [loose_arity]; exact h.2⟩
  | .emit r _, h => ⟨loose_wf (r := r) h.1, by rw [loose_arity]; exact h.2⟩
  | .cross a b, h => ⟨loose_wf (r := a) h.1, loose_wf (r := b) h.2⟩
  | .join a b .inner _, h => ⟨loose_wf (r := a) h.1, loose_wf (r := b) h.2.1⟩
  | .join a b .left _, h =>
    ⟨loose_wf (r := a) h.1, loose_wf (r := b) h.2.1, by rw [loose_arity, loose_arity]; exact h.2.2⟩
  | .unionAll a b, h =>
    ⟨loose_wf (r := a) h.1, loose_wf (r := b) h.2.1, by rw [loose_arity, loose_arity]; exact h.2.2⟩
  | .semi a _ _ _, h => loose_wf (r := a) h.1
  | .orderBy r _, h => loose_wf (r := r) h.1
  | .distinct r, h => loose_wf (r := r) h
  | .unnest r _, h => ⟨⟨loose_wf (r := r) h.1, by rw [loose_arity]; exact h.2⟩, loose_wf (r := r) h.1,
      by simp [arity, loose_arity]⟩

/-- Is the value a double's `±∞`? -/
def isInfValue (v : Value) : Bool := v == .int FloatCode.posInf || v == .int FloatCode.negInf

/-- Would IEEE make the aggregate of these values NaN, from numbers (#257)?
A double `SUM` or `AVG` of `+∞` and `-∞`, and a variance of an infinity
(`∞ - ∞` in its deviations). A black box that raises on them (#326) is
reported here too, as the same domain error. -/
def AggFn.makesNan : AggFn → List Value → Bool
  | .fsum, vs | .avg, vs => vs.contains (.int FloatCode.posInf) && vs.contains (.int FloatCode.negInf)
  | .var _ _, vs => vs.contains (.int FloatCode.posInf) || vs.contains (.int FloatCode.negInf)
  -- A pair with an infinity: a deviation `∞ - ∞` (#54).
  | .cov _, vs | .corr, vs => vs.any fun
    | .list [a, b] => isInfValue a || isInfValue b
    | _ => false
  -- A black box that raises on these values (#326).
  | .bbox n, vs => BlackBox.aggRaisesOn n vs
  | _, _ => false

/-- May `makesNan` hold of values that `a` describes? -/
def AggFn.mayNan : AggFn → AVal → Bool
  | .fsum, a | .avg, a => a.has FloatCode.posInf && a.has FloatCode.negInf
  | .var _ _, a => a.has FloatCode.posInf || a.has FloatCode.negInf
  -- A pair's sides are what may be infinite (`Measure.mayNan`).
  | .cov _, _ | .corr, _ => true
  | .bbox n, _ => BlackBox.aggMayRaise n
  | _, _ => false

theorem AggFn.mayNan_of_makesNan {f : AggFn} {vs : List Value} {a : AVal}
    (has : ∀ c, .int c ∈ vs → a.has c = true) (h : f.makesNan vs = true) : f.mayNan a = true := by
  cases f <;> simp only [makesNan, mayNan, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at h ⊢
  all_goals first
    | exact ⟨has _ h.1, has _ h.2⟩
    | exact h.imp (has _) (has _)
    | exact BlackBox.aggMayRaise_of_aggRaisesOn h
    | simp at h

/-- Does the aggregate take pairs (`BinFn.pair`)? -/
def AggFn.paired : AggFn → Bool
  | .cov _ | .corr => true
  | _ => false

/-- May the abstract value hold `±∞`? -/
def AVal.mayInf (a : AVal) : Bool := a.has FloatCode.posInf || a.has FloatCode.negInf

/-- May either side of a pair be infinite (`true` for anything but a pair)? -/
def pairMayInf (abs : Expr → AVal) : Expr → Bool
  | .bin .pair x y => (abs x).mayInf || (abs y).mayInf
  | _ => true

/-- May `makesNan` hold of the measure's values, whose expressions `abs`
describes? A two-argument aggregate's pair is looked at side by side. -/
def Measure.mayNan (m : Measure) (abs : Expr → AVal) : Bool :=
  if m.fn.paired then pairMayInf abs m.arg else m.fn.mayNan (abs m.arg)

theorem Measure.mayNan_of_makesNan {m : Measure} {grp : Relation} {abs : Expr → AVal}
    (hsound : ∀ y ∈ grp, ∀ e : Expr, (abs e).Mem (e.eval y))
    (h : m.fn.makesNan (m.inputs grp) = true) : m.mayNan abs = true := by
  -- Every input is the argument's value on a row of the group.
  have from_row : ∀ v ∈ m.inputs grp, ∃ y ∈ grp, m.arg.eval y = v := fun v hv => by
    obtain ⟨_, y, hy, hv⟩ := Measure.mem_inputs hv; exact ⟨y, hy, hv⟩
  unfold Measure.mayNan
  by_cases hp : m.fn.paired = true
  · simp only [hp, ite_true]
    -- An input pair with an infinite side, from some row.
    have hex : ∃ v ∈ m.inputs grp, (match v with
        | .list [a, b] => isInfValue a || isInfValue b
        | _ => false) = true := by
      cases hf : m.fn <;> simp [hf, AggFn.paired] at hp <;> simpa [hf, AggFn.makesNan] using h
    obtain ⟨v, hv, hinf⟩ := hex
    obtain ⟨row, hrow, hev⟩ := from_row v hv
    cases harg : m.arg with
    | bin f x y =>
      cases f
      case pair =>
        simp only [pairMayInf]
        rw [harg] at hev
        simp only [Expr.eval] at hev
        have hx := hsound row hrow x
        have hy := hsound row hrow y
        cases hxv : x.eval row <;> cases hyv : y.eval row <;>
          simp only [hxv, hyv, BinFn.apply] at hev <;> subst hev <;>
          simp only [isInfValue, Bool.or_eq_true, beq_iff_eq] at hinf <;>
          rw [hxv] at hx <;> rw [hyv] at hy <;>
          simp only [AVal.mayInf, Bool.or_eq_true] <;>
          rcases hinf with (h1 | h1) | (h1 | h1) <;> simp_all [AVal.has_of_mem]
      all_goals rfl
    | _ => rfl
  · simp only [hp, Bool.false_eq_true, ite_false]
    refine AggFn.mayNan_of_makesNan (fun c hc => ?_) h
    obtain ⟨row, hrow, hev⟩ := from_row _ hc
    have := hsound row hrow m.arg
    rw [hev] at this
    exact AVal.has_of_mem this

/-! ## Bounded sums

An integer `SUM` may leave 64 bits, and the reference raises there. Without
a bound on how many rows a group has, nothing rules it out; where the plan's
shape bounds its rows (`Rel.maxRows` in `Contracts.lean`: a `VALUES` list, a
`FETCH` count, an aggregate without groups, products and unions of bounded
inputs) and the argument's interval bounds each value, the sum fits. -/

theorem length_le_of_mem_aggGroups {gs : List Expr} {rows grp : Relation}
    (hg : grp ∈ aggGroups gs rows) : grp.length ≤ rows.length := by
  unfold aggGroups at hg
  split at hg
  · simp only [List.mem_singleton] at hg; exact hg ▸ Nat.le_refl _
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
    exact List.length_filter_le _ _

theorem intSum_bound (M : Int) (hM : 0 ≤ M) : ∀ vs : List Value,
    (∀ i, Value.int i ∈ vs → -M ≤ i ∧ i ≤ M) →
      -(M * vs.length) ≤ intSum vs ∧ intSum vs ≤ M * vs.length
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    have ih := intSum_bound M hM vs fun i hi => h i (List.mem_cons_of_mem _ hi)
    have hl : M * ((v :: vs).length : Int) = M * vs.length + M := by
      simp [Int.mul_add]
    rw [hl]
    cases v with
    | int i =>
      have := h i (List.mem_cons_self ..)
      simp only [intSum]; omega
    | _ => simp only [intSum]; omega

/-- The digits of a decimal `SUM` of `m`'s argument: the result's precision,
ten more digits than the argument's and at most 38 (`Measure.kind`, #27).
None for an integer `SUM`. -/
def Measure.sumDigits (m : Measure) : Option Nat :=
  match m.arg with
  | .un (.decimal p _) _ => some (min 38 (p + 10))
  | _ => none

/-- Does a `SUM` of `m`'s argument fit its type: 64 bits for integers, the
result's precision for decimals (#316)? -/
def Measure.sumOk (m : Measure) (i : Int) : Bool :=
  match m.sumDigits with
  | some q => fitsDigits q i
  | none => inI64 i

/-- The largest magnitude a `SUM` of `m`'s argument is sure to fit. -/
def Measure.sumMax (m : Measure) : Int :=
  match m.sumDigits with
  | some q => 10 ^ q - 1
  | none => maxI64

theorem Measure.sumMax_nonneg (m : Measure) : 0 ≤ m.sumMax := by
  unfold Measure.sumMax
  cases m.sumDigits with
  | some q =>
    have : (0 : Int) < 10 ^ q := Int.pow_pos (by decide)
    simp only; omega
  | none => simp only; decide

theorem Measure.sumOk_of_le {m : Measure} {i : Int} (h1 : -m.sumMax ≤ i) (h2 : i ≤ m.sumMax) :
    m.sumOk i = true := by
  unfold Measure.sumMax at h1 h2
  unfold Measure.sumOk
  cases hq : m.sumDigits with
  | some q =>
    simp only [hq] at h1 h2 ⊢
    unfold fitsDigits
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega
  | none =>
    simp only [hq] at h1 h2 ⊢
    have hmax : maxI64 = 2 ^ 63 - 1 := rfl
    have hmin : minI64 = -(2 ^ 63) := rfl
    unfold inI64
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hmin, hmax]
    rw [hmax] at h1 h2
    omega

/-- The most rows a group or window frame of `r`'s rows has: `Rel.maxRows`,
and fewer than `2⁶³` by the size hypothesis (`Rel.Small`, #437), as
`COUNT(*)` of a group is a BIGINT. So a `SUM` of values in `[-1, 1]` fits
64 bits without a row cap. -/
def Rel.sumRows (r : Rel) : Nat := min (r.maxRows.getD (2 ^ 63 - 1)) (2 ^ 63 - 1)

theorem Rel.le_sumRows {cat : Catalog} {r : Rel} {n : Nat} (hlt : (r.eval cat).length < 2 ^ 63)
    (hn : n ≤ (r.eval cat).length) : n ≤ r.sumRows := by
  have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
  rw [h63] at hlt
  unfold Rel.sumRows
  rw [h63]
  cases hm : r.maxRows with
  | none => simp only [Option.getD_none, Nat.le_min]; omega
  | some k =>
    have := Rel.maxRows_sound (cat := cat) hm
    simp only [Option.getD_some, Nat.le_min]; omega

/-- Does a `SUM` of `m`'s argument fit its type (`Measure.sumOk`) on at most
`n` rows, with the argument within `abs m.arg`? -/
def Measure.sumFits (m : Measure) (abs : Expr → AVal) (n : Option Nat) : Bool :=
  match (abs m.arg).int, n with
  -- No integer at all: the sum is 0.
  | none, _ => true
  | some ⟨some lo, some hi⟩, some k =>
    decide (((max lo.natAbs hi.natAbs * k : Nat) : Int) ≤ m.sumMax)
  | _, _ => false

theorem Measure.sumFits_sound {m : Measure} {abs : Expr → AVal} {n : Option Nat} {grp : Relation}
    (hsound : ∀ y ∈ grp, (abs m.arg).Mem (m.arg.eval y))
    (hlen : ∀ k, n = some k → grp.length ≤ k) (h : m.sumFits abs n = true) :
    m.sumOk (intSum (m.inputs grp)) = true := by
  have from_row : ∀ i, Value.int i ∈ m.inputs grp → (abs m.arg).Mem (.int i) := fun i hi => by
    obtain ⟨_, y, hy, hv⟩ := Measure.mem_inputs hi
    exact hv ▸ hsound y hy
  unfold Measure.sumFits at h
  split at h
  · rename_i hn
    -- No integer input: every input is something else.
    have hz : ∀ vs : List Value, (∀ i, Value.int i ∈ vs → False) → intSum vs = 0 := by
      intro vs; induction vs with
      | nil => intro; rfl
      | cons v vs ih =>
        intro hv
        cases v with
        | int i => exact (hv i (List.mem_cons_self ..)).elim
        | _ => simp only [intSum]; exact ih fun i hi => hv i (List.mem_cons_of_mem _ hi)
    rw [hz _ fun i hi => by obtain ⟨b, hb, _⟩ := from_row i hi; simp [hn] at hb]
    have := m.sumMax_nonneg
    exact Measure.sumOk_of_le (by omega) (by omega)
  · rename_i lo hi k hb
    subst_vars
    have hk := hlen k rfl
    have hl := Nat.le_trans (Measure.inputs_length_le m grp) hk
    have hdec : (((max lo.natAbs hi.natAbs * k : Nat)) : Int) ≤ m.sumMax := of_decide_eq_true h
    have hbnd := intSum_bound ((max lo.natAbs hi.natAbs : Nat) : Int) (Int.natCast_nonneg _)
      (m.inputs grp) fun i hi' => by
        obtain ⟨b, hb', hm⟩ := from_row i hi'
        rw [hb] at hb'; cases hb'
        have h1 := hm.1 lo rfl; have h2 := hm.2 hi rfl
        omega
    have hmul : ((max lo.natAbs hi.natAbs : Nat) : Int) * ((m.inputs grp).length : Int) ≤
        ((max lo.natAbs hi.natAbs * k : Nat) : Int) := by
      rw [← Int.natCast_mul]; exact Int.ofNat_le.mpr (Nat.mul_le_mul_left _ hl)
    exact Measure.sumOk_of_le (by omega) (by omega)
  · simp at h

/-- **Where issues happen.** Filter and join conditions run on the loose
input; projections on their input, or on the loose input under a filter or
join condition (`under`), which may inline them. Aggregates evaluate their
grouping expressions and every measure's argument and filter like
projections, and a `SUM` raises when the true sum of a group leaves its type:
64 bits for integers, the result's precision for decimals (#316). -/
def Rel.HasIssue (cat : Catalog) : Bool → Rel → Issue × Expr → Prop
  | _, .read _, _ | _, .values _ _, _ => False
  | _, .filter r c, p => r.HasIssue cat true p ∨ ∃ row ∈ r.loose.eval cat, p ∈ c.issues row
  | u, .project r es, p => r.HasIssue cat u p ∨
      ∃ row ∈ (if u then r.loose else r).eval cat, ∃ e ∈ es, p ∈ e.issues row
  | u, .emit r _, p | u, .fetch r _ _, p | u, .orderBy r _, p
  | u, .distinct r, p | u, .unnest r _, p => r.HasIssue cat u p
  -- A window `SUM` may leave 64 bits (its argument is a column:
  -- `Parse.issueFree`).
  -- A window aggregate that would be NaN on some frame (#257): a frame is
  -- some of the input's rows.
  | u, .window r _ _ fns, p => r.HasIssue cat u p ∨
      (∃ m ∈ WinFn.aggs fns, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ r.eval cat) ∧ frame.length ≤ (r.eval cat).length ∧
          m.sumOk (intSum (m.inputs frame)) = false) ∨
      ∃ m ∈ WinFn.aggs fns, p = (.domain, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ r.eval cat) ∧ m.fn.makesNan (m.inputs frame) = true
  | u, .cross a b, p | u, .unionAll a b, p => a.HasIssue cat u p ∨ b.HasIssue cat u p
  | _, .join a b _ on, p | _, .semi a b _ on, p => a.HasIssue cat true p ∨ b.HasIssue cat true p ∨
      ∃ x ∈ a.loose.eval cat, ∃ y ∈ b.loose.eval cat, p ∈ on.issues (x ++ y)
  | u, .aggregate r gs ms, p => r.HasIssue cat u p ∨
      (∃ row ∈ (if u then r.loose else r).eval cat, ∃ e ∈ gs ++ ms.flatMap Measure.exprs,
        p ∈ e.issues row) ∨
      (∃ m ∈ ms, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), m.sumOk (intSum (m.inputs grp)) = false) ∨
      -- An aggregate that would be NaN, which no operation creates (#257).
      ∃ m ∈ ms, p = (.domain, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), m.fn.makesNan (m.inputs grp) = true

/-- The issues the abstract evaluation cannot rule out. -/
def Rel.mayIssues (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Bool → Rel → List (Issue × Expr)
  | _, .read _ | _, .values _ _ => []
  | _, .filter r c =>
    r.mayIssues cat A F T true ++ c.mayIssues (r.loose.aeval cat A F T true) (r.loose.facts cat F T)
  | u, .project r es =>
    let s := if u then r.loose else r
    r.mayIssues cat A F T u ++ es.flatMap (·.mayIssues (s.aeval cat A F T true) (s.facts cat F T))
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r
  | u, .unnest r _ => r.mayIssues cat A F T u
  | u, .window r _ _ fns => r.mayIssues cat A F T u ++
      (WinFn.aggs fns).filterMap (fun m =>
        if m.fn = .sum ∧
          m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false
        then some (.sumWraps, m.arg) else none) ++
      (WinFn.aggs fns).filterMap fun m =>
        if m.mayNan (·.absD (r.aeval cat A F T true) (r.facts cat F T))
        then some (.domain, m.arg) else none
  | u, .cross a b | u, .unionAll a b => a.mayIssues cat A F T u ++ b.mayIssues cat A F T u
  | _, .join a b _ on | _, .semi a b _ on =>
    let ab := Rel.cross a.loose b.loose
    a.mayIssues cat A F T true ++ b.mayIssues cat A F T true ++
      on.mayIssues (ab.aeval cat A F T true) (ab.facts cat F T)
  -- A sum may leave its type unless the input's rows and the argument bound it.
  | u, .aggregate r gs ms =>
    let s := if u then r.loose else r
    r.mayIssues cat A F T u ++
      (gs ++ ms.flatMap Measure.exprs).flatMap (·.mayIssues (s.aeval cat A F T true) (s.facts cat F T)) ++
      ms.filterMap (fun m =>
        if m.fn = .sum ∧
          m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false
        then some (.sumWraps, m.arg) else none) ++
      ms.filterMap fun m =>
        if m.mayNan (·.absD (r.aeval cat A F T true) (r.facts cat F T))
        then some (.domain, m.arg) else none

theorem KsHold.nil (row : Row) : KsHold [] row := by simp [KsHold]

theorem mem_of_mem_aggGroups {gs : List Expr} {rows grp : Relation} {y : Row}
    (hg : grp ∈ aggGroups gs rows) (hy : y ∈ grp) : y ∈ rows := by
  unfold aggGroups at hg
  split at hg
  · simp only [List.mem_singleton] at hg; exact hg ▸ hy
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
    exact (List.mem_filter.1 hy).1

/-- `Rel.loose` keeps every window as it is, so it keeps the size hypothesis. -/
theorem Rel.Small.loose {cat : Catalog} : ∀ {r : Rel}, r.Small cat → r.loose.Small cat
  | .read _, h | .values _ _, h => h
  | .filter r _, h | .orderBy r _, h | .distinct r, h => Rel.Small.loose (r := r) h
  | .project r _, h | .emit r _, h => Rel.Small.loose (r := r) h
  | .cross a b, h | .unionAll a b, h => ⟨Rel.Small.loose (r := a) h.1, Rel.Small.loose (r := b) h.2⟩
  | .join a b ty _, h => by
    cases ty <;> exact ⟨Rel.Small.loose (r := a) h.1, Rel.Small.loose (r := b) h.2⟩
  | .semi a _ _ _, h => Rel.Small.loose (r := a) h.1
  | .fetch _ _ _, h | .window _ _ _ _, h | .aggregate _ _ _, h => h
  | .unnest r _, h => ⟨Rel.Small.loose (r := r) h, Rel.Small.loose (r := r) h⟩

/-- Join and semi-join conditions run on pairs of loose input rows. -/
theorem condIssue_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {a b : Rel} {on : Expr} {p : Issue × Expr} {x y : Row} (ha : a.WF cat) (hb : b.WF cat)
    (hsa : a.Small cat) (hsb : b.Small cat) (hx : x ∈ a.loose.eval cat) (hy : y ∈ b.loose.eval cat) (hp : p ∈ on.issues (x ++ y)) :
    p ∈ on.mayIssues ((Rel.cross a.loose b.loose).aeval cat A F T true)
      ((Rel.cross a.loose b.loose).facts cat F T) := by
  have hab : (Rel.cross a.loose b.loose).WF cat := ⟨Rel.loose_wf ha, Rel.loose_wf hb⟩
  have hrow : x ++ y ∈ (Rel.cross a.loose b.loose).eval cat := by
    simp only [Rel.eval, mem_crossRows]; exact ⟨x, hx, y, hy, rfl⟩
  exact Expr.mayIssues_sound (Rel.aeval_sound hcat hA hF hT hab (fun _ => ⟨hsa.loose, hsb.loose⟩) _ hrow)
    (Rel.facts_sound hcat hF hT hab _ hrow) (KsHold.nil _) on p hp

/-- **Soundness**: every issue that can happen when running a well-formed plan
is among `Rel.mayIssues`, provided its windows read fewer than `2⁶²` rows
(the size hypothesis, `Rel.Small`). So an empty list proves the plan runs
without errors and without wrapping around. -/
theorem Rel.mayIssues_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat) :
    ∀ {u : Bool} {r : Rel}, r.WF cat → r.Small cat → ∀ p, r.HasIssue cat u p →
      p ∈ r.mayIssues cat A F T u
  | _, .read _, _, _, _, h | _, .values _ _, _, _, _, h => h.elim
  | _, .filter r c, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | ⟨row, hrow, hp⟩
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h)
    · have hl := loose_wf hwf.1
      exact .inr (Expr.mayIssues_sound (aeval_sound hcat hA hF hT hl (fun _ => Rel.Small.loose (r := r) hsm) row hrow)
        (facts_sound hcat hF hT hl row hrow) (KsHold.nil row) c p hp)
  | u, .project r es, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h)
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      have hsm' : (if u then r.loose else r).Small cat := by
        cases u
        · exact hsm
        · exact Rel.Small.loose (r := r) hsm
      exact .inr ⟨e, he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs (fun _ => hsm') row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩
  | _, .emit r _, hwf, hsm, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .fetch r _ _, hwf, hsm, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf hsm p h
  | _, .window r _ _ _, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_filterMap]
    have habs : ∀ y ∈ r.eval cat, ∀ e : Expr,
        (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := fun y hyr e =>
      Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm.2) y hyr)
        (facts_sound hcat hF hT hwf.1 y hyr) (KsHold.nil y) e
    rcases h with h | ⟨m, hm, hf, rfl, frame, hframe, hlen, hov⟩ |
      ⟨m, hm, rfl, frame, hframe, hnan⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT (r := r) hwf.1 hsm.2 p h))
    · have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows)
        · rfl
        · have := Measure.sumFits_sound (fun y hy => habs y (hframe y hy) m.arg)
            (fun k hk => by
              cases hk; exact Rel.le_sumRows (Nat.lt_trans hsm.1 (by decide)) hlen) hfit
          rw [hov] at this; cases this
      exact .inl (.inr ⟨m, hm, by simp [hf, hfits]⟩)
    · have hsound : ∀ y ∈ frame, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) :=
        fun y hy e => habs y (hframe y hy) e
      exact .inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩
  | _, .orderBy r _, hwf, hsm, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .distinct r, hwf, hsm, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf hsm p h
  | _, .unnest r _, hwf, hsm, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .cross a b, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 hsm.1 p h)
    · exact .inr (mayIssues_sound hcat hA hF hT hwf.2 hsm.2 p h)
  | _, .unionAll a b, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 hsm.1 p h)
    · exact .inr (mayIssues_sound hcat hA hF hT hwf.2.1 hsm.2 p h)
  | _, .join a b ty on, hwf, hsm, p, h => by
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT ha hsm.1 p h))
    · exact .inl (.inr (mayIssues_sound hcat hA hF hT hb hsm.2 p h))
    · exact .inr (condIssue_sound hcat hA hF hT ha hb hsm.1 hsm.2 hx hy hp)
  | _, .semi a b _ on, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm.1 p h))
    · exact .inl (.inr (mayIssues_sound hcat hA hF hT hwf.2.1 hsm.2 p h))
    · exact .inr (condIssue_sound hcat hA hF hT hwf.1 hwf.2.1 hsm.1 hsm.2 hx hy hp)
  | u, .aggregate r gs ms, hwf, ⟨hlt, hsm⟩, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap, List.mem_filterMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩ | ⟨m, hm, hf, rfl, grp, hgrp, hov⟩ |
      ⟨m, hm, rfl, grp, hgrp, hnan⟩
    · exact .inl (.inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h)))
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      have hsm' : (if u then r.loose else r).Small cat := by
        cases u
        · exact hsm
        · exact Rel.Small.loose (r := r) hsm
      exact .inl (.inl (.inr ⟨e, by simpa using he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs (fun _ => hsm') row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩))
    · have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows)
        · rfl
        · have := Measure.sumFits_sound (grp := grp) (fun y hy => by
              have hyr := mem_of_mem_aggGroups hgrp hy
              exact Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr)
                (facts_sound hcat hF hT hwf.1 y hyr) (KsHold.nil y) m.arg)
            (fun k hk => by
              cases hk; exact Rel.le_sumRows hlt (length_le_of_mem_aggGroups hgrp)) hfit
          rw [hov] at this; cases this
      exact .inl (.inr ⟨m, hm, by simp [hf, hfits]⟩)
    · have hsound : ∀ y ∈ grp, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := by
        intro y hy e
        have hyr := mem_of_mem_aggGroups hgrp hy
        exact Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr)
          (facts_sound hcat hF hT hwf.1 y hyr) (KsHold.nil y) e
      exact .inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩

/-- The assumption a report makes of the `SUM`s it cannot bound
(`Report.assumed` in `sverify`, inferred like #244's bounds): on this
catalog, no group's or frame's sum leaves its type (`Measure.sumOk`). `Rel.HasIssue`'s
`sumWraps` cases are exactly those sums, so this says none happens. The job
checks it on the data: the SQL sverify writes raises where a sum does not
fit. -/
def Rel.SumsFit (cat : Catalog) (r : Rel) : Prop :=
  ∀ p, r.HasIssue cat false p → p.1 ≠ .sumWraps

/-- **Runs without errors under the `SUM` assumption**: when every issue
`Rel.mayIssues` reports is a `SUM`, a catalog that meets the
preconditions and on which the sums fit (`Rel.SumsFit`) runs into no issue
at all. -/
theorem Rel.noIssue_of_sumsFit {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat)
    (hm : (r.mayIssues cat A F T false).all (·.1 == .sumWraps) = true) (hfit : r.SumsFit cat) :
    ∀ p, ¬r.HasIssue cat false p := fun p hp =>
  hfit p hp (by simpa using List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf hsmall p hp))

end Substrait
