import Sverify.Core.Issue
import SubstraitLean.Contracts

/-!
# Runtime errors

The reference raises where a result leaves its type or an argument leaves a
function's domain, and an error allows any engine's answer, whether the
engine raises, wraps or gives NULL there: integer division or remainder by
zero, `MIN / -1`,
integer powers with a negative exponent or a result outside 64 bits, integer
`+`, `-`, `*` and negation outside their declared width (#202: `overflow`
omitted means ERROR; DuckDB and Spark in ANSI mode raise, Polars wraps:
duckdb-int-narrow, spark-int-arith, polars-int-arith), a cast to a narrower
integer that does not fit (DuckDB, Polars and Spark raise: duckdb-int-narrow,
polars-cast-int, spark-cast-int-narrow),
`CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, an invalid
regular expression, `repeat` writing more than `Text.repeatMax` bytes, and an
integer `SUM` that leaves 64 bits (`Issue.sumWraps`, which the job also
checks while it runs). Date arithmetic raises outside the reference's dates
(#251), and the calendar functions on timestamps (`date_part`, truncation to a
week or longer, `date_bin`, `strftime`, adding months) outside the reference's
timestamps, 0001-01-01 to 9999-12-31 (D32). Arguments outside a function's
domain (`sqrt` of a negative, a shift by 64, …, `core/Sverify/Core/Numeric.lean`)
raise too, where an engine may give an IEEE value or a wrapped shift
instead: an error allows that.

## Where an engine evaluates an expression

Which expressions an engine evaluates on which rows is the trusted part of
this model (`docs/proofs.md`, "What is trusted"). `Rel.HasIssue` assumes:

* `CASE` evaluates a branch only on rows that take it, so
  `CASE WHEN b <> 0 THEN a / b END` and `a / NULLIF(b, 0)` are safe.
* `AND` and `OR` evaluate both sides: `b <> 0 AND a / b > 1` fails on `b = 0`.
* `COALESCE` evaluates all its arguments, and a `CASE` with a boolean value
  counts as `AND`/`OR`, so `CASE WHEN b <> 0 THEN a / b > 1 ELSE false END`
  fails on `b = 0`. The parser makes those eager (`Parse.eagerly`);
  `Expr.ifThen` itself is lazy. Polars evaluates `coalesce`, `&` and `|` on
  every row (`polars-exec-when-eager`); DataFusion's simplifier rewrites a
  boolean `CASE` into `AND`/`OR`.
* On DataFusion, `ABS` fails on the smallest integer (the parser writes `-a`
  as `a / -1`), and the simplifier makes `POWER(x, 0)` the constant 1, so it
  never fails.
* Optimizers merge filters and push them down through projections and
  joins, so a filter condition may be evaluated on rows that a filter below it
  would remove: `t.filter(b != 0).filter(a / b > 1)` fails on `b = 0`.
  `Rel.loose` is the input with those filters removed (and inner joins
  widened to cross joins); filter and join conditions are evaluated on it.
  DuckDB pushes filters into join inputs (`duckdb-exec-filter-pushdown`; the
  case of an empty other input lies outside `Rel.loose` and is open there);
  sverify runs Polars with predicate pushdown off
  (`polars-exec-predicate-pushdown`).
* A projection is evaluated on the rows that reach it. Under a filter or a
  join condition, though, its expressions may be inlined into that condition,
  so there they count as evaluated on the loose rows too.
* A constant subexpression that raises counts in every `CASE` branch, also on
  an empty table (D21, `Rel.constIssues`), which covers DuckDB folding a
  raising `WHEN` while planning (`upstream/bugs/DD-7.json`).

The engines' behaviour is recorded as facts in
`characterization/<engine>/facts/`. `Rel.HasIssue` states this model;
`Rel.mayIssues` over-approximates it with the abstract evaluation of
`SubstraitLean/Contracts.lean`, and
`Rel.mayIssues_sound` proves that every issue that can happen is reported.
-/

namespace Substrait

open FloatCode (minI64 maxI64 castLo castHi)

/-! ## What may go wrong, abstractly -/

def rangeMay (lo hi : Int) (aa ar : AVal) : List Issue :=
  if aa.within lo hi && ar.within lo hi then [] else [.overflow]

theorem AVal.memNum_of_unscaled {a : AVal} {v : Value} {i : Int} (hm : a.Mem v)
    (hv : v.unscaled? = some i) : ∃ k, a.MemNum k i := by
  cases v <;> simp only [Value.unscaled?, Option.some.injEq, reduceCtorEq] at hv <;> subst hv <;>
    exact ⟨_, hm⟩

/-- A value of the reference's calendar types lies in 0001-01-01 …
9999-12-31 (D32): a DATE in `Time.dayMin` … `Time.dayMax`, a TIMESTAMP in
`Time.tsMin` … `Time.tsMax`. A column read has it by its type
(`ContractCheck.typeEnv`), and the source read checks it; a computed date
outside it raises (#251). -/
def _root_.Substrait.Value.InCalendar : Value → Prop
  | .date d => Time.dayMin ≤ d ∧ d ≤ Time.dayMax
  | .ts t => Time.tsMin ≤ t ∧ t ≤ Time.tsMax
  | _ => True

variable [Boxes.Ambient]
/-- `date_part` raises nothing on the reference's values: calendar functions
are total on them (D32). -/
theorem UnFn.datePart_issue_of_inCalendar (p : Time.DatePart) {v : Value}
    (h : v.InCalendar) : (UnFn.datePart p).issue v = none := by
  cases v <;> simp_all [Value.InCalendar, UnFn.issue, rangeIssue, between]

theorem UnFn.dayPart_issue_of_inCalendar (p : Time.DatePart) {v : Value}
    (h : v.InCalendar) : (UnFn.dayPart p).issue v = none := by
  cases v <;> simp_all [Value.InCalendar, UnFn.issue, rangeIssue, between]

omit [Boxes.Ambient] in
theorem rangeIssue_sound {lo hi x y : Int} {aa ar : AVal} {k : Issue} {kx ky : NumKind}
    (ha : aa.MemNum kx x) (hr : ar.MemNum ky y) (hk : rangeIssue lo hi x y = some k) : k ∈ rangeMay lo hi aa ar := by
  simp only [rangeIssue] at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
  subst hk
  simp only [rangeMay]
  split
  · rename_i hn hw
    simp only [Bool.and_eq_true] at hw
    simp [AVal.within_memNum hw.1 ha, AVal.within_memNum hw.2 hr] at hn
  · simp

/-- Every double code `a` describes has a decimal at scale `s`: the casts of
its bounds do (`FloatCode.toDecimal?_between`, #223). -/
def AVal.decFits (s : Nat) (a : AVal) : Bool := a.int.all fun b =>
  match b.lo, b.hi with
  | some l, some h => (FloatCode.toDecimal? l s).isSome && (FloatCode.toDecimal? h s).isSome
  | _, _ => false

/-- Every timestamp `aa` describes, and its truncation `ar`, is within the
reference's timestamps (D32). -/
def tsFits (aa ar : AVal) : Bool :=
  aa.int.all (·.allLe Time.tsMax) && ar.int.all (·.allGe Time.tsMin)

def UnFn.mayIssue : UnFn → AVal → AVal → List Issue
  | .neg, _, ar => if ar.within minI64 maxI64 then [] else [.wraps]
  | .ftoi, aa, _ => if aa.within castLo castHi then [] else [.badCast]
  | .narrow n, aa, _ => if aa.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1) then [] else [.badCast]
  | .wrap n, aa, _ => if aa.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1) then [] else [.wraps]
  | .regexMatch p, _, _ => if Text.simpleRegex p then [] else [.badRegex]
  | .dateTrunc u, aa, ar =>
    if u.calendar then (if tsFits aa ar then [] else [.overflow])
    else if ar.within minI64 maxI64 then [] else [.wraps]
  | .dayTrunc _, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .addMonths _ false, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .dateTime, aa, _ => rangeMay Time.dayMin Time.dayMax aa aa
  | .addMonths _ true, aa, ar => rangeMay Time.tsMin Time.tsMax aa ar
  | .timeOfDay, aa, _ | .strftime _, aa, _ | .datePart _, aa, _ => rangeMay Time.tsMin Time.tsMax aa aa
  | .dayPart _, aa, _ => rangeMay Time.dayMin Time.dayMax aa aa
  | .bucket _ _, aa, ar => rangeMay Time.tsMin Time.tsMax aa ar
  | .fmath f, aa, _ => if f.safe aa then [] else [.domain]
  | .decimal p _, aa, _ => if aa.within (1 - 10 ^ p) (10 ^ p - 1) then [] else [.overflow]
  | .ftod s, aa, _ => if aa.decFits s then [] else [.badCast]
  | .raise _, _, _ => [.raised]
  | .bbox n, _, _ => if BlackBox.mayRaise Boxes.Ambient.boxes n then [.domain] else []
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
    ab.within (-Text.substrMax) (Text.substrMax - 1)

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

omit [Boxes.Ambient] in
theorem AVal.has_of_mem {a : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i) : a.has i = true := by
  obtain ⟨b, hb, hm, -⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.has, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => hm.1 l hl, fun u hu => hm.2 u hu⟩

omit [Boxes.Ambient] in
theorem AVal.has_of_memFloat {a : AVal} {i : Int} (h : a.Mem (.float i)) : a.has i = true :=
  AVal.has_of_mem h

omit [Boxes.Ambient] in
theorem AVal.negFinite_of_mem {a : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i)
    (h1 : FloatCode.negInf < i) (h2 : i < 0) : a.negFinite = true := by
  obtain ⟨b, hb, hm, -⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.negFinite, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => by have := hm.1 l hl; omega, fun u hu => by have := hm.2 u hu; omega⟩

omit [Boxes.Ambient] in
/-- An IEEE NaN case of the inputs is one `BinFn.mayNan` reports. -/
theorem BinFn.mayNan_sound {f : BinFn} {aa ab : AVal} {a b : Int} (ha : aa.Mem (.float a))
    (hb : ab.Mem (.float b)) (h : nanCase f a b = true) : BinFn.mayNan f aa ab = true := by
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
    obtain ⟨bd, hbd, hm, -⟩ := hb
    rw [hbd]
    simp only [Option.any_some]
    cases hp : bd.point with
    | none => rfl
    | some k =>
      have := Bound.point_mem hp hm
      subst this
      simpa using h5

/-- May the inputs be a `negInfPow`? Where the base may be `-∞` and the
exponent is not a constant integer. -/
def mayNegInfPow (aa ab : AVal) : Bool :=
  aa.has FloatCode.negInf && !(ab.int.any fun b => b.point.any fun k => FloatCode.floor k == k)

omit [Boxes.Ambient] in
theorem mayNegInfPow_sound {aa ab : AVal} {a b : Int} (ha : aa.Mem (.float a))
    (hb : ab.Mem (.float b)) (h : negInfPow a b = true) : mayNegInfPow aa ab = true := by
  simp only [negInfPow, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, _⟩, _⟩, h4⟩ := h
  subst h1
  simp only [mayNegInfPow, AVal.has_of_mem ha, Bool.true_and, Bool.not_eq_true']
  obtain ⟨bd, hbd, hm, -⟩ := hb
  rw [hbd]
  simp only [Option.any_some]
  cases hp : bd.point with
  | none => rfl
  | some k =>
    have := Bound.point_mem hp hm
    subst this
    simpa using h4

/-- `nz`: the divisor is never the integer 0; `sz`: the first argument's
size, if it is a constant string. -/
def BinFn.mayIssue : BinFn → AVal → AVal → AVal → Bool → Option Nat → List Issue
  | .add, _, _, ar, _, _ | .sub, _, _, ar, _, _ | .mul, _, _, ar, _, _ =>
    if ar.within minI64 maxI64 then [] else [.wraps]
  | .dateAdd, aa, _, ar, _, _ => rangeMay Time.dayMin Time.dayMax aa ar
  | .idiv, _, _, ar, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if ar.within minI64 maxI64 then [] else [.overflow])
  | .imod, _, _, _, nz, _ => if nz then [] else [.divByZero]
  | .fdiv, aa, ab, _, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if BinFn.mayNan .fdiv aa ab then [.domain] else [])
  | .fmod, aa, ab, _, nz, _ =>
    (if nz then [] else [.divByZero]) ++ (if BinFn.mayNan .fmod aa ab then [.domain] else [])
  | .fadd, aa, ab, _, _, _ => if BinFn.mayNan .fadd aa ab then [.domain] else []
  | .fsub, aa, ab, _, _, _ => if BinFn.mayNan .fsub aa ab then [.domain] else []
  | .fmul, aa, ab, _, _, _ => if BinFn.mayNan .fmul aa ab then [.domain] else []
  | .fpow, aa, ab, _, _, _ =>
    if BinFn.mayNan .fpow aa ab || mayNegInfPow aa ab then [.domain] else []
  | .ipow, aa, ab, _, _, _ =>
    (if ab.int.all (·.lo.any (0 ≤ ·)) then [] else [.negExponent]) ++
      (if powFits aa ab then [] else [.overflow])
  | .strRepeat, _, ab, _, _, sz => repeatMay sz ab
  | .substr n _, _, ab, _, _, _ => if substrSafe n ab then [] else [.domain]
  | .fatan2, aa, ab, _, _, _ => if BinFn.domainSafe .fatan2 aa.int ab.int then [] else [.domain]
  | .flogb, aa, ab, _, _, _ => if BinFn.domainSafe .flogb aa.int ab.int then [] else [.domain]
  | .bit op, aa, ab, _, _, _ => if BinFn.domainSafe (.bit op) aa.int ab.int then [] else [.domain]
  | .bbox2 n, _, _, _, _, _ => if BlackBox.mayRaise Boxes.Ambient.boxes n then [.domain] else []
  | _, _, _, _, _, _ => []

/-- Is `x`'s value never the zero of kind `k` (the integer 0, the double
`0.0`)? From its interval, an assumption `x ≠ 0`, a fact `$j ≠ -c` for
`x = $j + c`, both branches of a `CASE`, or both factors of a product. -/
def Expr.nonZero (env : List AVal) (fs : List Fact) (ks : Assumptions) (k : NumKind) (x : Expr) :
    Bool :=
  (x.absD env fs ks).int.all (!·.has0) ||
  ks.any (fun sk => sk.1 == x && match sk.2 with | .ne k' 0 => k' == k | _ => false) ||
  (match x.linTerm with | some (j, c) => fs.contains (.ne j k (-c)) | none => false) ||
  match x with
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    (!ac.tt || t.nonZero (c.refine env) fs (c.cstrs true ++ ks) k) &&
      (!(ac.nonBool || ac.ff) || e.nonZero (c.refineNeg env) fs (c.cstrs false ++ ks) k)
  -- A product of non-zero integers (exact in the model; overflow is an error).
  | .bin .mul a b => k == .int && a.nonZero env fs ks .int && b.nonZero env fs ks .int
  -- A non-zero integer is a non-zero double (`FloatCode.ofInt_ne_zero`).
  | .un .itof a => k == .float && a.nonZero env fs ks .int
  | _ => false

/-- The kind of a division's divisor: a double for `fdiv` and `fmod`. -/
def BinFn.divKind : BinFn → NumKind
  | .fdiv | .fmod => .float
  | _ => .int

/-- May `a` be a finite double? -/
def AVal.mayFinite (a : AVal) : Bool :=
  a.int.any fun b => b.lo.all (· < FloatCode.posInf) && b.hi.all (FloatCode.negInf < ·)

omit [Boxes.Ambient] in
theorem AVal.mayFinite_of_mem {a : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i)
    (hf : isFiniteCode i = true) : a.mayFinite = true := by
  obtain ⟨b, hb, hm, -⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [isFiniteCode, Bool.and_eq_true, decide_eq_true_eq] at hf
  simp only [AVal.mayFinite, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => by have := hm.1 l hl; omega, fun u hu => by have := hm.2 u hu; omega⟩

set_option exponentiation.threshold 1100 in
/-- `exp` of a finite double at most `709` is finite (#582): `709 < 1023 · ln 2`,
and `exp` is the platform's `libm`, within one ulp. Trusted, as the facts of
`FloatCode.add_scaled` …; proved for native doubles as `NativeLink.core_exp`
in `float-bounds/FloatBounds/Arith.lean`, from `NativeLink.exp`. -/
axiom FloatCode.exp_fin {a r : Int} (ha : FloatCode.IsFin a)
    (h : FloatCode.scaled a ≤ 709 * 2 ^ 1074) (hr : FMath.apply .exp a = some r) : FloatCode.IsFin r

set_option exponentiation.threshold 1100 in
/-- Do the argument's bounds keep it at most `709`, so that `exp` of a finite
one is finite? -/
def expFinite (aa : AVal) : Bool :=
  match aa.int with
  | some ⟨_, some h⟩ => decide (FloatCode.scaled h ≤ 709 * 2 ^ 1074)
  | _ => false

/-- May the call overflow to `±∞` (`UnFn.infIssue`)? Where its argument may
be finite and its bounds do not keep `exp` below the largest double. -/
def UnFn.mayInf (f : UnFn) (aa : AVal) : List Issue :=
  match f with
  | .fmath .exp => if aa.mayFinite && !expFinite aa then [.infinite] else []
  | _ => []

/-- The bound of a double operation's result (`faddBound` …), `top` for the
others. -/
def BinFn.fBound : BinFn → Bound → Bound → Bound
  | .fadd, x, y => faddBound false x y
  | .fsub, x, y => faddBound true x y
  | .fmul, x, y => fmulBound x y
  | .fdiv, x, y => fdivBound x y
  | _, _, _ => Bound.top

/-- Do the arguments' bounds show the result finite (#582)? -/
def BinFn.finiteResult (f : BinFn) (aa ab : AVal) : Bool :=
  match aa.int, ab.int with
  | some x, some y => match f.fBound x y with
    | ⟨some l, some h⟩ => decide (FloatCode.negInf < l) && decide (h < FloatCode.posInf)
    | _ => false
  | _, _ => false

/-- May the call overflow to `±∞` (`BinFn.infIssue`)? Where both arguments
may be finite and their bounds do not show the result finite. -/
def BinFn.mayInf (f : BinFn) (aa ab : AVal) : List Issue :=
  if f.makesInf && aa.mayFinite && ab.mayFinite && !f.finiteResult aa ab then [.infinite] else []

theorem BinFn.fBound_mem (f : BinFn) {x y : Bound} {a b r : Int} (hx : x.Mem a) (hy : y.Mem b)
    (hr : f.apply (.float a) (.float b) = .float r) : (f.fBound x y).Mem r := by
  cases f <;> simp only [BinFn.fBound] <;> try exact Bound.mem_top _
  all_goals simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
  · exact faddBound_mem' false hx hy (fun _ => rfl) (fun h => by cases h)
  · exact faddBound_mem' true hx hy (fun h => by cases h) (fun _ => rfl)
  · exact fmulBound_mem hx hy
  · exact fdivBound_mem hx hy

theorem BinFn.finiteResult_false (f : BinFn) {aa ab : AVal} {a b r : Int}
    (ha : aa.Mem (.float a)) (hb : ab.Mem (.float b)) (hr : f.apply (.float a) (.float b) = .float r)
    (hinf : isInfCode r = true) : f.finiteResult aa ab = false := by
  obtain ⟨x, hx, hxm, -⟩ := ha
  obtain ⟨y, hy, hym, -⟩ := hb
  have hm := f.fBound_mem hxm hym hr
  unfold BinFn.finiteResult
  rw [hx, hy]
  dsimp only
  split
  · rename_i l h heq
    rw [heq] at hm
    have h1 := hm.1 l rfl
    have h2 := hm.2 h rfl
    simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at hinf
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    rcases hinf with rfl | rfl <;> omega
  · rfl

omit [Boxes.Ambient] in
set_option exponentiation.threshold 1100 in
theorem expFinite_false {aa : AVal} {a r : Int} (ha : aa.Mem (.float a))
    (hfin : isFiniteCode a = true) (hr : FMath.apply .exp a = some r) (hinf : isInfCode r = true) :
    expFinite aa = false := by
  obtain ⟨x, hx, hxm, -⟩ := ha
  unfold expFinite
  rw [hx]
  split
  · rename_i l h heq
    cases heq
    have h2 := hxm.2 h rfl
    simp only [decide_eq_false_iff_not]
    intro c3
    simp only [isFiniteCode, Bool.and_eq_true, decide_eq_true_eq] at hfin
    have hf := FloatCode.exp_fin (a := a) ⟨hfin.1, hfin.2⟩
      (Int.le_trans (FloatCode.scaled_mono h2) c3) hr
    simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at hinf
    obtain ⟨f1, f2⟩ := hf
    rcases hinf with rfl | rfl <;> omega
  · rfl

theorem UnFn.mayInf_sound (f : UnFn) {aa : AVal} {v : Value} {k : Issue} (ha : aa.Mem v)
    (hk : f.infIssue v = some k) : k ∈ f.mayInf aa := by
  have := UnFn.infIssue_eq hk; subst this
  unfold UnFn.infIssue at hk
  split at hk
  · rename_i a r heq
    split at hk
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have hr : FMath.apply .exp a = some r := by
        simp only [UnFn.apply] at heq; split at heq <;> simp_all
      simp [UnFn.mayInf, AVal.mayFinite_of_mem ha hc.1, expFinite_false ha hc.1 hr hc.2]
    · simp at hk
  · simp at hk

theorem BinFn.mayInf_sound (f : BinFn) {aa ab : AVal} {v w : Value} {k : Issue} (ha : aa.Mem v)
    (hb : ab.Mem w) (hk : f.infIssue v w = some k) : k ∈ f.mayInf aa ab := by
  have := BinFn.infIssue_eq hk; subst this
  unfold BinFn.infIssue at hk
  split at hk
  · rename_i a b r heq
    split at hk
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      simp [BinFn.mayInf, hc.1.1.1, AVal.mayFinite_of_mem ha hc.1.1.2, AVal.mayFinite_of_mem hb hc.1.2,
        BinFn.finiteResult_false f ha hb heq hc.2]
    · simp at hk
  · simp at hk

/-! ## Guards on the NaN of a double operation (#702)

A `CASE` that guards `a * b` with `(a = ∞ OR a = -∞) AND b = 0` leaves its
`ELSE` branch with alternatives (`Expr.cstrAlts`): `a ≠ ±∞`, or `b ≠ 0`.
They go into the assumptions when there is one, and otherwise into a clause
of `Clauses`. An operation whose only domain error is a NaN case
(`BinFn.nanOnly`) has none where, under each combination of the clauses'
alternatives, its inputs cannot meet a NaN case (`Expr.nanExcluded`), by
their abstract values and the assumptions `x ≠ k`. This is how the DuckDB
lift's `+`, `-`, `*` and `/` of doubles, which give NaN as DuckDB does, are
shown not to raise. -/

/-- Operations of doubles whose only domain error is a NaN case (`nanCase`). -/
def BinFn.nanOnly : BinFn → Bool
  | .fadd | .fsub | .fmul | .fdiv | .fmod => true
  | _ => false

theorem BinFn.nanCase_of_issue {f : BinFn} (hf : f.nanOnly = true) {v w : Value}
    (h : f.issue v w = some .domain) : ∃ a b, v = .float a ∧ w = .float b ∧ nanCase f a b = true := by
  cases f <;> simp only [BinFn.nanOnly, Bool.false_eq_true] at hf <;>
    cases v <;> cases w <;> simp only [BinFn.issue, reduceCtorEq] at h <;>
    (try split at h) <;> simp_all [nanIssue] <;>
    (split at h <;> simp_all)

/-- `BinFn.mayNan` of the operations `nanOnly` names, where `pa k` and `pb k`
say whether each input may be the code `k`. -/
def BinFn.mayNanBy (f : BinFn) (pa pb : Int → Bool) : Bool :=
  let inf (p : Int → Bool) := p FloatCode.posInf || p FloatCode.negInf
  match f with
  | .fadd => (pa FloatCode.posInf && pb FloatCode.negInf) ||
      (pa FloatCode.negInf && pb FloatCode.posInf)
  | .fsub => (pa FloatCode.posInf && pb FloatCode.posInf) ||
      (pa FloatCode.negInf && pb FloatCode.negInf)
  | .fmul => (pa 0 && inf pb) || (inf pa && pb 0)
  | .fdiv => inf pa && inf pb
  | .fmod => inf pa
  | _ => true

omit [Boxes.Ambient] in
theorem BinFn.mayNanBy_sound {f : BinFn} {pa pb : Int → Bool} {a b : Int} (ha : pa a = true)
    (hb : pb b = true) (h : nanCase f a b = true) : f.mayNanBy pa pb = true := by
  cases f <;> simp only [nanCase, Bool.false_eq_true] at h <;>
    simp only [BinFn.mayNanBy, isInfCode, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at h ⊢
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨ha, hb⟩
    · exact .inr ⟨ha, hb⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨ha, hb⟩
    · exact .inr ⟨ha, hb⟩
  · rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl⟩
    · exact .inl ⟨ha, .inl hb⟩
    · exact .inl ⟨ha, .inr hb⟩
    · exact .inr ⟨.inl ha, hb⟩
    · exact .inr ⟨.inr ha, hb⟩
  · obtain ⟨rfl | rfl, rfl | rfl⟩ := h
    all_goals exact ⟨by first | exact .inl ha | exact .inr ha, by first | exact .inl hb | exact .inr hb⟩
  · obtain ⟨rfl | rfl, _⟩ := h
    · exact .inl ha
    · exact .inr ha

/-- May `x` be the double with code `k`? Its abstract value may hold `k`,
no assumption says `x ≠ k`, and for `0`, `Expr.nonZero` does not rule it out. -/
def Expr.mayBe (env : List AVal) (fs : List Fact) (ks : Assumptions) (x : Expr) (k : Int) : Bool :=
  (x.absD env fs ks).has k &&
    !(ks.any fun sk => sk.1 == x && match sk.2 with | .ne .float j => j == k | _ => false) &&
    (k != 0 || !x.nonZero env fs ks .float)

/-- Clauses: lists of alternatives, one of each of which holds. -/
abbrev Clauses := List (List Assumptions)

def ClausesHold (ors : Clauses) (row : Row) : Prop := ∀ as ∈ ors, AltsHold as row

/-- The combinations of one alternative per clause, the newest clauses
first, while there are at most `budget` of them. -/
def clauseCombos (budget : Nat) : Clauses → List Assumptions
  | [] => [[]]
  | as :: rest =>
    if as.length ≤ budget then altsProd as (clauseCombos (budget / max as.length 1) rest)
    else clauseCombos budget rest

theorem clauseCombos_sound {row : Row} (budget : Nat) :
    ∀ {ors : Clauses}, ClausesHold ors row → AltsHold (clauseCombos budget ors) row
  | [], _ => ⟨[], by simp [clauseCombos], fun _ hp => by simp at hp⟩
  | as :: rest, h => by
    have hr : ClausesHold rest row := fun a ha => h a (List.mem_cons_of_mem _ ha)
    unfold clauseCombos
    split
    · exact (h as (List.mem_cons_self ..)).prod (clauseCombos_sound _ hr)
    · exact clauseCombos_sound _ hr

/-- Assumptions and clauses with the alternatives `as` added: to the
assumptions when there is one, as a clause otherwise. -/
def withAlts (as : List Assumptions) (ks : Assumptions) (ors : Clauses) : Assumptions × Clauses :=
  match as with
  | [k] => (k ++ ks, ors)
  | _ => (ks, as :: ors)

theorem withAlts_sound {as : List Assumptions} {ks : Assumptions} {ors : Clauses} {row : Row}
    (h : AltsHold as row) (hks : KsHold ks row) (hors : ClausesHold ors row) :
    KsHold (withAlts as ks ors).1 row ∧ ClausesHold (withAlts as ks ors).2 row := by
  unfold withAlts
  split
  · obtain ⟨k', hk', hh⟩ := h
    simp only [List.mem_singleton] at hk'
    subst hk'
    exact ⟨hh.append hks, hors⟩
  · refine ⟨hks, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h
    · exact hors a ha

/-- Do the assumptions and clauses rule out every NaN case of `f a b`, for
an operation `nanOnly` names? -/
def Expr.nanExcluded (env : List AVal) (fs : List Fact) (ks : Assumptions) (ors : Clauses)
    (f : BinFn) (a b : Expr) : Bool :=
  f.nanOnly && (clauseCombos 16 ors).all fun ks' =>
    !f.mayNanBy (a.mayBe env fs (ks' ++ ks)) (b.mayBe env fs (ks' ++ ks))

/-- `BinFn.mayIssue`, without its domain error where `excl`. -/
def BinFn.mayIssueX (f : BinFn) (aa ab ar : AVal) (nz : Bool) (sz : Option Nat) (excl : Bool) :
    List Issue :=
  if excl then (f.mayIssue aa ab ar nz sz).filter (· != .domain) else f.mayIssue aa ab ar nz sz

def Expr.mayIssues (env : List AVal) (fs : List Fact) (ks : Assumptions := []) (ors : Clauses := []) :
    Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | .un f a =>
    a.mayIssues env fs ks ors ++
      (f.mayIssue (a.absD env fs ks) ((Expr.un f a).absD env fs ks) ++
        f.mayInf (a.absD env fs ks)).map (·, .un f a)
  | .bin f a b =>
    a.mayIssues env fs ks ors ++ b.mayIssues env fs ks ors ++
      (f.mayIssueX (a.absD env fs ks) (b.absD env fs ks) ((Expr.bin f a b).absD env fs ks)
        (b.nonZero env fs ks f.divKind) a.strBytes? (Expr.nanExcluded env fs ks ors f a b) ++
        f.mayInf (a.absD env fs ks) (b.absD env fs ks)).map (·, .bin f a b)
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    let tk := withAlts (c.cstrAlts true) ks ors
    let ek := withAlts (c.cstrAlts false) ks ors
    c.mayIssues env fs ks ors ++
      (if ac.tt then t.mayIssues (c.refine env) fs tk.1 tk.2 else []) ++
      (if ac.nonBool || ac.ff then e.mayIssues (c.refineNeg env) fs ek.1 ek.2 else [])
  -- The body on any element, with the row in scope (D28).
  | .hof _ l b => l.mayIssues env fs ks ors ++ b.mayIssues (AVal.top :: env) [] []

-- The DuckDB lift's `a * b` of doubles (#702): the NaN of `0 · ∞` and
-- `∞ · 0` as a `CASE`, whose `ELSE` branch has no domain error; the bare product
-- has one. (Both may overflow to `±∞`, an assumed issue of its own.)
#guard
  letI := Boxes.Ambient.none
  let dbl : AVal := { int := some Bound.top, nk := some .float }
  let a := Expr.field 0
  let b := Expr.field 1
  let isInf (x : Expr) := Expr.bin .or (.bin .eq x (.lit (.float FloatCode.posInf)))
    (.bin .eq x (.lit (.float FloatCode.negInf)))
  let isZero (x : Expr) := Expr.bin .eq x (.lit (.float 0))
  let nan := Expr.lit (.float FloatCode.nan)
  let guarded := Expr.ifThen (.bin .and (isZero a) (isInf b)) nan
    (.ifThen (.bin .and (isInf a) (isZero b)) nan (.bin .fmul a b))
  (guarded.mayIssues [dbl, dbl] []).all (·.1 != .domain) &&
    ((Expr.bin .fmul a b).mayIssues [dbl, dbl] []).any (·.1 == .domain)

/-! ## Soundness for expressions -/

theorem Expr.nonZero_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ (k : NumKind) (x : Expr), x.nonZero env fs ks k = true → ∀ j, x.eval row = k.val j → j ≠ 0 := by
  intro k x hnz j hj
  unfold Expr.nonZero at hnz
  simp only [Bool.or_eq_true] at hnz
  rcases hnz with ((hb | hk) | hl) | hc
  · -- the interval excludes 0
    have hm := Expr.absD_sound h hfs hks x
    rw [hj, AVal.mem_val] at hm
    obtain ⟨b, hb', hm, -⟩ := hm
    simp only [hb', Option.all_some, Bool.not_eq_true'] at hb
    exact Bound.ne_zero hm hb
  · -- an assumption `x ≠ 0`
    obtain ⟨sk, hsk, he⟩ := List.any_eq_true.mp hk
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨rfl, hne⟩ := he
    have := hks sk hsk
    match hk' : sk.2, hne with
    | .ne k' 0, hne =>
      rw [hk'] at this
      simp only [beq_iff_eq] at hne
      subst hne
      exact this j hj
  · -- a fact `$j ≠ -c`
    split at hl
    · rename_i j' c hlin
      obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_num hlin hj
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
            (KsHold.cons_cstrs hct hks) k t ht j hj
      · simp only [hct, ite_false, Bool.false_eq_true] at hj
        have hf : (c.eval row).isTrue = false := by simpa using hct
        rcases he with he | he
        · rcases AVal.mem_cases hcm with ⟨_, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ |
              ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp_all [AVal.nonBool]
          · simp_all [AVal.nonBool]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp_all
          · simp_all [AVal.nonBool]
          · simp_all [AVal.nonBool]
        · exact Expr.nonZero_sound (Expr.refineNeg_sound env c h hf) hfs
            (KsHold.cons_cstrs hf hks) k e he j hj
    · rename_i a b
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, ha'⟩, hb'⟩ := hc
      simp only [eval, NumKind.val] at hj
      cases ha : a.eval row <;> cases hb : b.eval row <;> simp [ha, hb, BinFn.apply] at hj
      rename_i x y
      subst hj
      exact Int.mul_ne_zero (Expr.nonZero_sound h hfs hks .int a ha' x ha)
        (Expr.nonZero_sound h hfs hks .int b hb' y hb)
    · rename_i a
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, ha'⟩ := hc
      simp only [eval, NumKind.val] at hj
      cases ha : a.eval row <;> simp [ha, UnFn.apply] at hj
      rename_i i
      subst hj
      exact FloatCode.ofInt_ne_zero (Expr.nonZero_sound h hfs hks .int a ha' i ha)
    · simp at hc

theorem UnFn.mayIssue_sound (f : UnFn) {aa ar : AVal} {v : Value} {k : Issue}
    (ha : aa.Mem v) (hr : ar.Mem (f.apply v)) (hk : f.issue v = some k) : k ∈ f.mayIssue aa ar := by
  cases f
  case bbox n =>
    simp only [UnFn.issue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i h
    simp [UnFn.mayIssue, BlackBox.mayRaise_of_raisesOn h]
  case raise =>
    simp only [UnFn.issue, Option.some.injEq] at hk; subst hk; simp [UnFn.mayIssue]
  case regexMatch p =>
    simp only [UnFn.issue] at hk
    simp only [UnFn.mayIssue]
    split at hk <;> simp_all
  case decimal p s =>
    simp only [UnFn.issue] at hk
    simp only [UnFn.mayIssue]
    cases hu : v.unscaled? with
    | none => cases v <;> simp_all
    | some i =>
      simp only [hu] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      split
      · rename_i hn hfits
        obtain ⟨_, hm⟩ := AVal.memNum_of_unscaled ha hu
        exact absurd (AVal.within_memNum hfits hm) hn
      · simp_all
  all_goals (cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk)
  case fmath.float f c =>
    simp only [domainIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [UnFn.mayIssue]
    split
    · rename_i hn hs
      obtain ⟨b, hb, hm, -⟩ := ha
      have hs' : f.safeB (some b) = true := by simpa [FMath.safe, FMath.safeB, hb] using hs
      simp [FMath.apply, FMath.inDomain_of_safe hs' hm] at hn
    · simp
  case neg.int i =>
    simp only [wrapIf] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [UnFn.mayIssue]
    split
    · rename_i hn hfits
      have hr' := hr; simp only [UnFn.apply] at hr'
      exact absurd (AVal.within_memNum hfits hr') hn
    · simp
  case ftoi.float c =>
    simp only [UnFn.mayIssue]
    split
    · rename_i hfits
      have h := AVal.within_memNum hfits ha
      simp only [between, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, hx, hx₁, hx₂⟩ := FloatCode.toInt?_of_range h.1 h.2
      simp [hx, inI64, between, hx₁, hx₂] at hk
    · cases hx : FloatCode.toInt? c <;> simp only [hx] at hk <;> (try split at hk) <;> simp_all
  case narrow.int n i | wrap.int n i =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    split
    · rename_i hn hfits
      exact absurd (AVal.within_memNum hfits ha) hn
    · simp_all
  case ftod.float s c =>
    simp only [UnFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    split
    · rename_i hnone hfits
      exfalso
      obtain ⟨b, hb, hc, -⟩ := ha
      obtain ⟨bl, bh⟩ := b
      simp only [AVal.decFits, hb, Option.all_some] at hfits
      split at hfits
      · simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfits
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hfits
        obtain ⟨q, hq, -, -⟩ := FloatCode.toDecimal?_between (hc.1 _ rfl) (hc.2 _ rfl) hx hy
        rw [hq] at hnone; simp at hnone
      · cases hfits
    · simp
  case dateTrunc.ts u ts | dateTrunc.tod u ts =>
    simp only [UnFn.mayIssue]
    have hr' := hr; simp only [UnFn.apply] at hr'
    cases hc : u.calendar <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    · simp only [wrapIf] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      split
      · rename_i hn hfits
        exact absurd (AVal.within_memNum hfits hr') hn
      · simp
    · split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      split
      · rename_i hout hfits
        exfalso; apply hout
        simp only [tsFits, Bool.and_eq_true, Option.all_eq_true] at hfits
        obtain ⟨b, hb, hm, -⟩ := ha
        obtain ⟨b', hb', hm', -⟩ := hr'
        have h1 := hfits.1 b hb
        have h2 := hfits.2 b' hb'
        obtain ⟨bl, bh⟩ := b
        obtain ⟨bl', bh'⟩ := b'
        simp only [Bound.Mem] at hm hm'
        cases bh <;> cases bl' <;> simp_all [Bound.allLe, Bound.allGe] <;> constructor <;> omega
      · simp
  case dayTrunc.date u d | bucket.ts k o d =>
    have hr' := hr; simp only [UnFn.apply] at hr'
    exact rangeIssue_sound ha hr' hk
  case timeOfDay.ts ts | timeOfDay.tod ts | dateTime.date ts | strftime.ts fmt ts |
      datePart.ts p ts | dayPart.date p ts =>
    exact rangeIssue_sound ha ha hk
  case addMonths.date m t x | addMonths.ts m t x =>
    cases t <;> (try simp only [reduceCtorEq] at hk) <;>
    · have hr' := hr; simp only [UnFn.apply] at hr'
      exact rangeIssue_sound ha hr' hk

omit [Boxes.Ambient] in
theorem repeatMay_sound {sz : Option Nat} {ab : AVal} {s : String} {n : Int}
    (hb : ab.Mem (.int n)) (hsz : ∀ m, sz = some m → s.utf8ByteSize = m)
    (hk : Text.repeatFits s n = false) : Issue.overflow ∈ repeatMay sz ab := by
  obtain ⟨y, hy, hn, -⟩ := hb
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

omit [Boxes.Ambient] in
theorem substrSafe_sound {n : Option Nat} {ab : AVal} {a : Int} (hb : ab.Mem (.int a))
    (hs : substrSafe n ab = true) : Text.substrInRange a n = true := by
  simp only [substrSafe, Bool.and_eq_true] at hs
  have h := AVal.within_memNum hs.2 hb
  simp only [between, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Text.substrInRange, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.1, by omega⟩, hs.1⟩

theorem BinFn.mayIssue_sound (f : BinFn) {aa ab ar : AVal} {v w : Value} {nz : Bool}
    {sz : Option Nat} {k : Issue}
    (ha : aa.Mem v) (hb : ab.Mem w) (hr : ar.Mem (f.apply v w))
    (hnz : nz = true → ∀ j, w = f.divKind.val j → j ≠ 0)
    (hsz : ∀ m s, sz = some m → v = .str s → s.utf8ByteSize = m) (hk : f.issue v w = some k) :
    k ∈ f.mayIssue aa ab ar nz sz := by
  cases f
  case bbox2 n =>
    simp only [BinFn.issue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i h
    simp [BinFn.mayIssue, BlackBox.mayRaise_of_raisesOn h]
  case add | sub | mul =>
    simp only [BinFn.issue, wrapNum] at hk
    split at hk
    · rename_i kk i hnum
      simp only [wrapIf] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      simp only [BinFn.mayIssue]
      split
      · rename_i hn hfits
        rw [Value.numOf?_some hnum, AVal.mem_val] at hr
        exact absurd (AVal.within_memNum hfits hr) hn
      · simp
    · simp at hk
  all_goals (cases v <;> cases w <;> simp only [BinFn.issue, reduceCtorEq] at hk)
  case dateAdd.date.int i j =>
    have hr' := hr; simp only [BinFn.apply] at hr'
    exact rangeIssue_sound ha hr' hk
  case fatan2.float.float i j | flogb.float.float i j | bit.int.int op i j =>
    simp only [domainIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    simp only [BinFn.mayIssue]
    split
    · rename_i hn hs
      obtain ⟨x, hx, hi, -⟩ := ha
      obtain ⟨y, hy, hj, -⟩ := hb
      rw [hx, hy] at hs
      first
        | exact absurd (BinFn.domainSafe_atan2 hs hi hj) hn
        | exact absurd (BinFn.domainSafe_logb hs hi hj) hn
        | exact absurd (BinFn.domainSafe_bit hs hj) hn
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
        simp only [BinFn.apply, hj, ite_false] at hr
        exact absurd (AVal.within_memNum hfits hr) hn
      · simp
  case imod.int.int i j | imod.tod.int i j =>
    simp only [BinFn.mayIssue]
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    split
    · rename_i hj hnz'; exact absurd hj (hnz hnz' j rfl)
    · simp
  case fdiv.float.float i j | fmod.float.float i j =>
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
  case fadd.float.float i j | fsub.float.float i j | fmul.float.float i j =>
    simp only [BinFn.mayIssue]
    simp only [nanIssue] at hk
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk
    rename_i hn
    simp [BinFn.mayNan_sound ha hb hn]
  case fpow.float.float i j =>
    simp only [BinFn.mayIssue]
    split at hk
    · simp only [Option.some.injEq] at hk
      subst hk
      rename_i hn
      simp [mayNegInfPow_sound ha hb hn]
    · simp only [nanIssue] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      rename_i _ hn
      simp [BinFn.mayNan_sound ha hb hn]
  case ipow.int.int i j =>
    simp only [BinFn.mayIssue, List.mem_append]
    obtain ⟨x, hx, hi, -⟩ := ha
    obtain ⟨y, hy, hj, -⟩ := hb
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
                    simp only [inI64, between, minI64, maxI64, Bool.and_eq_true] at hout
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

theorem Expr.mayBe_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) {x : Expr} {c : Int}
    (hx : x.eval row = .float c) : x.mayBe env fs ks c = true := by
  have hm := Expr.absD_sound h hfs hks x
  rw [hx] at hm
  simp only [Expr.mayBe, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨AVal.has_of_mem hm, ?_⟩, ?_⟩
  · rw [List.any_eq_false]
    intro sk hsk hsk'
    simp only [Bool.and_eq_true, beq_iff_eq] at hsk'
    obtain ⟨rfl, hne⟩ := hsk'
    have := hks sk hsk
    match hk' : sk.2, hne with
    | .ne .float j, hj =>
      rw [hk'] at this
      simp only [beq_iff_eq] at hj
      exact this c hx hj.symm
  · by_cases hc : c = 0
    · right
      subst hc
      cases hnz : x.nonZero env fs ks .float with
      | false => rfl
      | true => exact absurd rfl (Expr.nonZero_sound h hfs hks .float x hnz 0 hx)
    · exact .inl hc

/-- Where `nanExcluded` holds, the operation has no domain error. -/
theorem Expr.nanExcluded_sound {env : List AVal} {fs : List Fact} {ks : Assumptions}
    {ors : Clauses} {row : Row} (h : EnvMem env row) (hfs : FactsHold fs row)
    (hks : KsHold ks row) (hors : ClausesHold ors row) {f : BinFn} {a b : Expr}
    (hx : Expr.nanExcluded env fs ks ors f a b = true) :
    f.issue (a.eval row) (b.eval row) ≠ some .domain := by
  intro hd
  simp only [Expr.nanExcluded, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hx
  obtain ⟨hf, hall⟩ := hx
  obtain ⟨x, y, hxa, hyb, hn⟩ := BinFn.nanCase_of_issue hf hd
  obtain ⟨ks', hk', hh⟩ := clauseCombos_sound 16 hors
  have hk := hh.append hks
  have := BinFn.mayNanBy_sound (Expr.mayBe_sound h hfs hk hxa) (Expr.mayBe_sound h hfs hk hyb) hn
  rw [hall ks' hk'] at this
  exact Bool.false_ne_true this

theorem BinFn.mayIssueX_sound (f : BinFn) {aa ab ar : AVal} {v w : Value} {nz excl : Bool}
    {sz : Option Nat} {k : Issue}
    (ha : aa.Mem v) (hb : ab.Mem w) (hr : ar.Mem (f.apply v w))
    (hnz : nz = true → ∀ j, w = f.divKind.val j → j ≠ 0)
    (hsz : ∀ m s, sz = some m → v = .str s → s.utf8ByteSize = m)
    (hex : excl = true → f.issue v w ≠ some .domain) (hk : f.issue v w = some k) :
    k ∈ f.mayIssueX aa ab ar nz sz excl := by
  have hm := BinFn.mayIssue_sound f ha hb hr hnz hsz hk
  unfold BinFn.mayIssueX
  split
  · rename_i he
    refine List.mem_filter.mpr ⟨hm, ?_⟩
    have hne : k ≠ .domain := fun hd => hex he (hd ▸ hk)
    simpa using hne
  · exact hm

/-- `Expr.mayIssues` reports every issue evaluating `e` runs into, on a row
its abstract environment, facts, assumptions and clauses describe. -/
theorem Expr.mayIssuesC_sound {env : List AVal} {fs : List Fact} {ks : Assumptions}
    {ors : Clauses} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row)
    (hors : ClausesHold ors row) :
    ∀ (e : Expr), ∀ p ∈ e.issues row, p ∈ e.mayIssues env fs ks ors
  | .lit _, p, hp | .field _, p, hp => by simp [Expr.issues] at hp
  | .un f a, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with hp | hp
    · exact .inl (Expr.mayIssuesC_sound h hfs hks hors a p hp)
    · right
      cases hi : f.issueAll (a.eval row) with
      | none => simp [hi] at hp
      | some k =>
        simp only [hi, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        refine List.mem_map_of_mem (List.mem_append.mpr ?_)
        unfold UnFn.issueAll at hi
        cases hj : f.issue (a.eval row) with
        | some k' =>
          rw [hj] at hi; cases hi
          exact .inl (UnFn.mayIssue_sound f (Expr.absD_sound h hfs hks a)
            (Expr.absD_sound h hfs hks (.un f a)) hj)
        | none =>
          rw [hj, Option.none_or] at hi
          exact .inr (UnFn.mayInf_sound f (Expr.absD_sound h hfs hks a) hi)
  | .bin f a b, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with (hp | hp) | hp
    · exact .inl (.inl (Expr.mayIssuesC_sound h hfs hks hors a p hp))
    · exact .inl (.inr (Expr.mayIssuesC_sound h hfs hks hors b p hp))
    · right
      cases hi : f.issueAll (a.eval row) (b.eval row) with
      | none => simp [hi] at hp
      | some k =>
        simp only [hi, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        refine List.mem_map_of_mem (List.mem_append.mpr ?_)
        unfold BinFn.issueAll at hi
        cases hj : f.issue (a.eval row) (b.eval row) with
        | some k' =>
          rw [hj] at hi; cases hi
          exact .inl (BinFn.mayIssueX_sound f (Expr.absD_sound h hfs hks a)
            (Expr.absD_sound h hfs hks b) (Expr.absD_sound h hfs hks (.bin f a b))
            (fun hnz => Expr.nonZero_sound h hfs hks _ b hnz) (Expr.strBytes?_sound row a)
            (fun hx => Expr.nanExcluded_sound h hfs hks hors hx) hj)
        | none =>
          rw [hj, Option.none_or] at hi
          exact .inr (BinFn.mayInf_sound f (Expr.absD_sound h hfs hks a)
            (Expr.absD_sound h hfs hks b) hi)
  | .ifThen c t e, p, hp => by
    simp only [Expr.issues, List.mem_append] at hp
    simp only [Expr.mayIssues, List.mem_append]
    have hc := Expr.absD_sound h hfs hks c
    rcases hp with hp | hp
    · exact .inl (.inl (Expr.mayIssuesC_sound h hfs hks hors c p hp))
    · by_cases hct : (c.eval row).isTrue = true
      · simp only [hct, ite_true] at hp
        left; right
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.absD env fs ks).tt = true := hc
        simp only [htt, ite_true]
        have hw := withAlts_sound (Expr.cstrAlts_sound hct) hks hors
        exact Expr.mayIssuesC_sound (Expr.refine_sound env c h hct) hfs hw.1 hw.2 t p hp
      · simp only [hct, ite_false, Bool.false_eq_true] at hp
        right
        have hf : (c.eval row).isTrue = false := by simpa using hct
        have : ((c.absD env fs ks).nonBool || (c.absD env fs ks).ff) = true := by
          rcases AVal.mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hff]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        simp only [this, ite_true]
        have hw := withAlts_sound (Expr.cstrAlts_sound hf) hks hors
        exact Expr.mayIssuesC_sound (Expr.refineNeg_sound env c h hf) hfs hw.1 hw.2 e p hp
  | .hof _ l b, p, hp => by
    simp only [Expr.issues, List.mem_append, List.mem_flatMap] at hp
    simp only [Expr.mayIssues, List.mem_append]
    rcases hp with hp | ⟨x, _, hp⟩
    · exact .inl (Expr.mayIssuesC_sound h hfs hks hors l p hp)
    · -- The body sees an element, which `AVal.top` describes, and the row.
      have hx : EnvMem (AVal.top :: env) (x :: row) := fun i => by
        cases i with
        | zero => simp [AVal.mem_top]
        | succ i => simpa using h i
      exact .inr (Expr.mayIssuesC_sound hx (fun _ hf => by simp at hf)
        (fun _ hk => by simp at hk) (fun _ ha => by simp at ha) b p hp)

theorem Expr.mayIssues_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ (e : Expr), ∀ p ∈ e.issues row, p ∈ e.mayIssues env fs ks :=
  Expr.mayIssuesC_sound h hfs hks (fun _ ha => by simp at ha)

/-! ## Plans -/

/-- The plan with the filters an optimizer may merge into or push past
removed (the reference does not fix where a filter runs): filters go, inner
joins become cross joins, semi and anti joins, sorts and `DISTINCT` give way
to their (left) input. Fetches, windows and aggregates
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
  -- A filter on the other columns may run below an `UNNEST`, on rows whose
  -- lists are empty (DataFusion's optimizer does): the loose rows are both.
  | .unnest r c => .unionAll (.unnest r.loose c) r.loose

omit [Boxes.Ambient] in
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

omit [Boxes.Ambient] in
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
def isInfValue (v : Value) : Bool := v == .float FloatCode.posInf || v == .float FloatCode.negInf

/-- Are `QUANTILE_CONT`'s neighbours among the values in order `-∞` and
`+∞` (`contNeighbours`)? Its interpolation between them is NaN. -/
def quantileOpposite (num scale : Nat) (vs : List Value) : Bool :=
  match contNeighbours num scale (sortVals vs) with
  | some (l, h, _) => l == FloatCode.negInf && h == FloatCode.posInf
  | none => false

/-- Would IEEE make the aggregate of these values NaN, from numbers (#257)?
A double `SUM` or `AVG` of `+∞` and `-∞`, and a variance of an infinity
(`∞ - ∞` in its deviations). A black box that raises on them (#326) is
reported here too, as the same domain error. -/
def AggFn.makesNan : AggFn → List Value → Bool
  | .fsum, vs | .avg, vs => vs.contains (.float FloatCode.posInf) && vs.contains (.float FloatCode.negInf)
  | .var _ _, vs => vs.contains (.float FloatCode.posInf) || vs.contains (.float FloatCode.negInf)
  -- A pair with an infinity: a deviation `∞ - ∞` (#54).
  | .cov _, vs | .corr, vs => vs.any fun
    | .list [a, b] => isInfValue a || isInfValue b
    | _ => false
  -- `QUANTILE_CONT` between `-∞` and `+∞`: IEEE's interpolation is NaN
  -- (DuckDB gives it), the model's clamp `+∞`; the reference raises (D21).
  | .quantile true num scale, vs =>
    vs.contains (.float FloatCode.posInf) && vs.contains (.float FloatCode.negInf) &&
      quantileOpposite num scale vs
  -- A black box that raises on these values (#326).
  | .bbox n, vs => BlackBox.aggRaisesOn Boxes.Ambient.boxes n vs
  | _, _ => false

/-- May `makesNan` hold of values that `a` describes? -/
def AggFn.mayNan : AggFn → AVal → Bool
  | .fsum, a | .avg, a => a.has FloatCode.posInf && a.has FloatCode.negInf
  | .var _ _, a => a.has FloatCode.posInf || a.has FloatCode.negInf
  | .quantile true _ _, a => a.has FloatCode.posInf && a.has FloatCode.negInf
  -- A pair's sides are what may be infinite (`Measure.mayNan`).
  | .cov _, _ | .corr, _ => true
  | .bbox n, _ => BlackBox.aggMayRaise Boxes.Ambient.boxes n
  | _, _ => false

theorem AggFn.mayNan_of_makesNan {f : AggFn} {vs : List Value} {a : AVal}
    (has : ∀ c, .float c ∈ vs → a.has c = true) (h : f.makesNan vs = true) : f.mayNan a = true := by
  cases f
  case quantile c _ _ =>
    cases c <;> simp only [makesNan, mayNan, Bool.and_eq_true, List.contains_iff_mem,
      reduceCtorEq] at h ⊢
    all_goals first
      | exact ⟨has _ h.1.1, has _ h.1.2⟩
      | simp at h
  all_goals simp only [makesNan, mayNan, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at h ⊢
  all_goals first
    | exact ⟨has _ h.1, has _ h.2⟩
    | exact ⟨has _ h.1.1, has _ h.1.2⟩
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
          rcases hinf with (h1 | h1) | (h1 | h1) <;> simp_all [AVal.has_of_memFloat]
      all_goals rfl
    | _ => rfl
  · simp only [hp, Bool.false_eq_true, ite_false]
    refine AggFn.mayNan_of_makesNan (fun c hc => ?_) h
    obtain ⟨row, hrow, hev⟩ := from_row _ hc
    have := hsound row hrow m.arg
    rw [hev] at this
    exact AVal.has_of_mem this

/-! ## Aggregates that overflow to `±∞` (#575) -/

/-- The aggregates of doubles whose result may overflow: `SUM`, `AVG` and the
statistical aggregates. -/
def AggFn.infAgg : AggFn → Bool
  | .fsum | .avg | .var _ _ | .cov _ | .corr => true
  | _ => false

/-- A finite double, or a pair of them; anything else is not a double. -/
def finiteValue : Value → Bool
  | .float c => isFiniteCode c
  | .list [.float a, .float b] => isFiniteCode a && isFiniteCode b
  | _ => true

/-- Is the aggregate of these rows `±∞` though every value is finite? -/
def Measure.makesInf (m : Measure) (grp : Relation) : Bool :=
  m.fn.infAgg && (m.inputs grp).all finiteValue && isInfValue (m.eval grp)

/-- May the aggregate, whose result `r` describes (`Measure.abs`), overflow?
Ruled out where `r` excludes `±∞`: a `SUM` or `AVG` of bounded values over at
most `2³²` rows (`floatBound`, from #85's error bounds). -/
def Measure.mayInf (m : Measure) (r : AVal) : Bool :=
  m.fn.infAgg && (r.has FloatCode.posInf || r.has FloatCode.negInf)

theorem Measure.mayInf_of_makesInf {m : Measure} {grp : Relation} {r : AVal}
    (hr : r.Mem (m.eval grp)) (h : m.makesInf grp = true) : m.mayInf r = true := by
  simp only [Measure.makesInf, Bool.and_eq_true] at h
  obtain ⟨⟨hf, _⟩, hinf⟩ := h
  simp only [isInfValue, Bool.or_eq_true, beq_iff_eq] at hinf
  simp only [Measure.mayInf, hf, Bool.true_and, Bool.or_eq_true]
  rcases hinf with h | h <;> rw [h] at hr
  · exact .inl (AVal.has_of_mem hr)
  · exact .inr (AVal.has_of_mem hr)

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

omit [Boxes.Ambient] in
theorem intSum_bound (M : Int) (hM : 0 ≤ M) : ∀ vs : List Value,
    (∀ v ∈ vs, ∀ i, v.unscaled? = some i → -M ≤ i ∧ i ≤ M) →
      -(M * vs.length) ≤ intSum vs ∧ intSum vs ≤ M * vs.length
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    have ih := intSum_bound M hM vs fun w hw => h w (List.mem_cons_of_mem _ hw)
    have hl : M * ((v :: vs).length : Int) = M * vs.length + M := by
      simp [Int.mul_add]
    rw [hl, intSum_cons]
    cases hv : v.unscaled? with
    | some i =>
      have := h v (List.mem_cons_self ..) i hv
      simp only [Option.getD_some]; omega
    | none => simp only [Option.getD_none]; omega

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

omit [Boxes.Ambient] in
theorem Measure.sumMax_nonneg (m : Measure) : 0 ≤ m.sumMax := by
  unfold Measure.sumMax
  cases m.sumDigits with
  | some q =>
    have : (0 : Int) < 10 ^ q := Int.pow_pos (by decide)
    simp only; omega
  | none => simp only; decide

omit [Boxes.Ambient] in
theorem Measure.sumOk_of_le {m : Measure} {i : Int} (h1 : -m.sumMax ≤ i) (h2 : i ≤ m.sumMax) :
    m.sumOk i = true := by
  unfold Measure.sumMax at h1 h2
  unfold Measure.sumOk
  cases hq : m.sumDigits with
  | some q =>
    simp only [hq] at h1 h2 ⊢
    unfold fitsDigits between
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega
  | none =>
    simp only [hq] at h1 h2 ⊢
    have hmax : maxI64 = 2 ^ 63 - 1 := rfl
    have hmin : minI64 = -(2 ^ 63) := rfl
    unfold inI64 between
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
  have from_row : ∀ v ∈ m.inputs grp, ∀ i, v.unscaled? = some i → ∃ k, (abs m.arg).MemNum k i :=
    fun v hv i hi => by
      obtain ⟨_, y, hy, hv⟩ := Measure.mem_inputs hv
      exact AVal.memNum_of_unscaled (hv ▸ hsound y hy) hi
  unfold Measure.sumFits at h
  split at h
  · rename_i hn
    -- No integer input: every input is something else.
    have hz : ∀ vs : List Value, (∀ v ∈ vs, ∀ i, v.unscaled? = some i → False) →
        intSum vs = 0 := by
      intro vs; induction vs with
      | nil => intro; rfl
      | cons v vs ih =>
        intro hv
        rw [intSum_cons, ih fun w hw => hv w (List.mem_cons_of_mem _ hw)]
        cases hu : v.unscaled? with
        | some i => exact (hv v (List.mem_cons_self ..) i hu).elim
        | none => rfl
    rw [hz _ fun v hv i hi => by
      obtain ⟨_, b, hb, _⟩ := from_row v hv i hi; simp [hn] at hb]
    have := m.sumMax_nonneg
    exact Measure.sumOk_of_le (by omega) (by omega)
  · rename_i lo hi k hb
    subst_vars
    have hk := hlen k rfl
    have hl := Nat.le_trans (Measure.inputs_length_le m grp) hk
    have hdec : (((max lo.natAbs hi.natAbs * k : Nat)) : Int) ≤ m.sumMax := of_decide_eq_true h
    have hbnd := intSum_bound ((max lo.natAbs hi.natAbs : Nat) : Int) (Int.natCast_nonneg _)
      (m.inputs grp) fun v hv i hi' => by
        obtain ⟨_, b, hb', hm, -⟩ := from_row v hv i hi'
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
      (∃ m ∈ WinFn.aggs fns, p = (.domain, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ r.eval cat) ∧ m.fn.makesNan (m.inputs frame) = true) ∨
      -- A window aggregate that would be `±∞` on some frame (#575).
      ∃ m ∈ WinFn.aggs fns, p = (.infinite, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ r.eval cat) ∧ frame.length ≤ (r.eval cat).length ∧
          m.makesInf frame = true
  | u, .cross a b, p | u, .unionAll a b, p => a.HasIssue cat u p ∨ b.HasIssue cat u p
  | _, .join a b _ on, p | _, .semi a b _ on, p => a.HasIssue cat true p ∨ b.HasIssue cat true p ∨
      ∃ x ∈ a.loose.eval cat, ∃ y ∈ b.loose.eval cat, p ∈ on.issues (x ++ y)
  | u, .aggregate r gs ms, p => r.HasIssue cat u p ∨
      (∃ row ∈ (if u then r.loose else r).eval cat, ∃ e ∈ gs ++ ms.flatMap Measure.exprs,
        p ∈ e.issues row) ∨
      (∃ m ∈ ms, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), m.sumOk (intSum (m.inputs grp)) = false) ∨
      -- An aggregate that would be NaN, which no operation creates (#257).
      (∃ m ∈ ms, p = (.domain, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), m.fn.makesNan (m.inputs grp) = true) ∨
      -- An aggregate of finite values that would be `±∞` (#575).
      ∃ m ∈ ms, p = (.infinite, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), m.makesInf grp = true

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
      (WinFn.aggs fns).filterMap (fun m =>
        if m.mayNan (·.absD (r.aeval cat A F T true) (r.facts cat F T))
        then some (.domain, m.arg) else none) ++
      (WinFn.aggs fns).filterMap fun m =>
        if m.mayInf (m.abs (r.aeval cat A F T true) (r.facts cat F T) false (some r.sumRows))
        then some (.infinite, m.arg) else none
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
      ms.filterMap (fun m =>
        if m.mayNan (·.absD (r.aeval cat A F T true) (r.facts cat F T))
        then some (.domain, m.arg) else none) ++
      ms.filterMap fun m =>
        if m.mayInf (m.abs (r.aeval cat A F T true) (r.facts cat F T) false (some r.sumRows))
        then some (.infinite, m.arg) else none

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
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
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
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
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
      ⟨m, hm, rfl, frame, hframe, hnan⟩ | ⟨m, hm, rfl, frame, hframe, hlen, hinf⟩
    · exact .inl (.inl (.inl (mayIssues_sound hcat hA hF hT (r := r) hwf.1 hsm.2 p h)))
    · have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows)
        · rfl
        · have := Measure.sumFits_sound (fun y hy => habs y (hframe y hy) m.arg)
            (fun k hk => by
              cases hk; exact Rel.le_sumRows (Nat.lt_trans hsm.1 (by decide)) hlen) hfit
          rw [hov] at this; cases this
      exact .inl (.inl (.inr ⟨m, hm, by simp [hf, hfits]⟩))
    · have hsound : ∀ y ∈ frame, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) :=
        fun y hy e => habs y (hframe y hy) e
      exact .inl (.inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩)
    · have hres := Measure.abs_sound (grp := frame)
        (fun y hy => ⟨aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm.2) y (hframe y hy),
          facts_sound hcat hF hT hwf.1 y (hframe y hy)⟩) m false (by simp) (some r.sumRows)
        (fun k hk => by cases hk; exact Rel.le_sumRows (Nat.lt_trans hsm.1 (by decide)) hlen)
      exact .inr ⟨m, hm, by simp [Measure.mayInf_of_makesInf hres hinf]⟩
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
      ⟨m, hm, rfl, grp, hgrp, hnan⟩ | ⟨m, hm, rfl, grp, hgrp, hinf⟩
    · exact .inl (.inl (.inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h))))
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      have hsm' : (if u then r.loose else r).Small cat := by
        cases u
        · exact hsm
        · exact Rel.Small.loose (r := r) hsm
      exact .inl (.inl (.inl (.inr ⟨e, by simpa using he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs (fun _ => hsm') row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩)))
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
      exact .inl (.inl (.inr ⟨m, hm, by simp [hf, hfits]⟩))
    · have hsound : ∀ y ∈ grp, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := by
        intro y hy e
        have hyr := mem_of_mem_aggGroups hgrp hy
        exact Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr)
          (facts_sound hcat hF hT hwf.1 y hyr) (KsHold.nil y) e
      exact .inl (.inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩)
    · have hres := Measure.abs_sound (grp := grp)
        (fun y hy => by
          have hyr := mem_of_mem_aggGroups hgrp hy
          exact ⟨aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr,
            facts_sound hcat hF hT hwf.1 y hyr⟩) m false (by simp) (some r.sumRows)
        (fun k hk => by cases hk; exact Rel.le_sumRows hlt (length_le_of_mem_aggGroups hgrp))
      exact .inr ⟨m, hm, by simp [Measure.mayInf_of_makesInf hres hinf]⟩

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
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat)
    (hm : (r.mayIssues cat A F T false).all (·.1 == .sumWraps) = true) (hfit : r.SumsFit cat) :
    ∀ p, ¬r.HasIssue cat false p := fun p hp =>
  hfit p hp (by simpa using List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf hsmall p hp))

/-- The assumptions a report makes (`Report.assumed`): no `SUM` leaves its
type and no operation on finite doubles gives `±∞` (#575). The job checks
both on the data. -/
def Rel.AssumedHold (cat : Catalog) (r : Rel) : Prop :=
  ∀ p, r.HasIssue cat false p → p.1.assumed = false

/-- **Runs without issues under the assumptions**: when every issue
`Rel.mayIssues` reports is assumed (`Issue.assumed`), a catalog that meets
the preconditions and the assumptions runs into no issue at all. -/
theorem Rel.noIssue_of_assumedHold {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) (hok : r.AssumedHold cat) :
    ∀ p, ¬r.HasIssue cat false p := fun p hp => by
  have := hok p hp
  rw [List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf hsmall p hp)] at this
  cases this

/-! ## Constant subexpressions that raise (#609)

DuckDB folds a `CASE`'s constant conditions when it plans a query, with the
evaluator that raises: `CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END`
raises on any data, an empty table included (DD-7). The reference counts every
constant subexpression that raises as raising for the whole plan, whatever
the data and whichever branch a row takes (D21: strict, and constants that
raise are rare). No precondition rules one out. -/

/-- Does `e` read no column? A lambda's body reads its parameter. -/
def Expr.isConst : Expr → Bool
  | .lit _ => true
  | .field _ => false
  | .un _ a => a.isConst
  | .bin _ a b => a.isConst && b.isConst
  | .ifThen c t e => c.isConst && t.isConst && e.isConst
  | .hof _ _ _ => false

/-- The errors of `e` itself if it is constant, on no row. -/
def Expr.selfConstIssues (e : Expr) : List (Issue × Expr) :=
  if e.isConst then (e.issues []).filter (·.1.isError) else []

/-- The errors of every constant subexpression of `e`, every branch of a
constant `CASE` included. -/
def Expr.constIssues : Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | e@(.un _ a) => e.selfConstIssues ++ a.constIssues
  | e@(.bin _ a b) => e.selfConstIssues ++ a.constIssues ++ b.constIssues
  | e@(.ifThen c t x) => e.selfConstIssues ++ c.constIssues ++ t.constIssues ++ x.constIssues
  | .hof _ l _ => l.constIssues

/-- Every expression of a plan: conditions, projections, grouping keys and
the measures' arguments and filters. -/
def Rel.planExprs : Rel → List Expr
  | .read _ | .values _ _ => []
  | .filter r c => c :: r.planExprs
  | .project r es => es ++ r.planExprs
  | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ => r.planExprs
  | .window r _ _ fns => (WinFn.aggs fns).flatMap Measure.exprs ++ r.planExprs
  | .cross a b | .unionAll a b => a.planExprs ++ b.planExprs
  | .join a b _ on | .semi a b _ on => on :: a.planExprs ++ b.planExprs
  | .aggregate r gs ms => gs ++ ms.flatMap Measure.exprs ++ r.planExprs

/-- **The plan's constant errors** (#609, D21): each raises when the plan
runs, on any data. -/
def Rel.constIssues (r : Rel) : List (Issue × Expr) :=
  (r.planExprs.flatMap Expr.constIssues).eraseDups

-- `1 // 0 = 1` in a later `WHEN` raises whatever the first condition says;
-- a constant without an error is nothing.
#guard letI := Boxes.Ambient.none; (Expr.ifThen (.bin .lt (.lit (.int 0)) (.field 0)) (.lit (.int 1))
  (.ifThen (.bin .eq (.bin .idiv (.lit (.int 1)) (.lit (.int 0))) (.lit (.int 1)))
    (.lit (.int 2)) (.lit .null))).constIssues.eraseDups.map (·.1) == [.divByZero]
#guard letI := Boxes.Ambient.none; (Expr.bin .add (.field 0) (.bin .idiv (.lit (.int 6)) (.lit (.int 3)))).constIssues.isEmpty

end Substrait
