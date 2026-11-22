import Sverify.Core.Issue
import Sverify.Analysis.Contracts

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
  every row (`polars-exec-when-eager`); an optimizer that rewrites a boolean
  `CASE` into `AND`/`OR` does the same.
* `ABS` fails on the smallest integer (the parser writes `-a` as `a / -1`).
* Optimizers merge filters and push them down through projections and
  joins, so a filter condition may be evaluated on rows that a filter below it
  would remove: `t.filter(b != 0).filter(a / b > 1)` fails on `b = 0`.
  `Rel.loose` is the input with those filters removed (and inner joins
  widened to cross joins); filter and join conditions are evaluated on it.
  DuckDB pushes filters into join inputs (`duckdb-exec-filter-pushdown`), and
  a hash join computes a key such as `10 // a.x` on every row of its side, so
  every subexpression of a filter or join condition that runs on every row
  (`Expr.eager`) may run on the rows of the join inputs it reads, whatever
  the other inputs hold, an empty one included (`Rel.ViewAllowed`, #1484 R3).
  A left join counts as a cross join for this: a filter that rejects NULLs
  lets an engine make it inner. sverify runs Polars with predicate pushdown
  off (`polars-exec-predicate-pushdown`).
* A projection is evaluated on the rows that reach it. Under a filter or a
  join condition, though, its expressions may be inlined into that condition,
  so there they count as evaluated on the loose rows too.
* A constant subexpression that raises counts in every `CASE` branch, also on
  an empty table (D21, `Rel.constIssues`), which covers DuckDB folding a
  raising `WHEN` while planning (`upstream/bugs/DD-7.json`).

The engines' behaviour is recorded as facts in
`engines/<engine>/facts/`. `Rel.HasIssue` states this model on the
rows `Rel.eval` gives; `Rel.HasIssueAll` states it on every order of the ties
the reference allows (`Rel.OrderAllowed`), so an engine that breaks a
window's ties another way is covered too (#1484). `Rel.mayIssues`
over-approximates both with the abstract evaluation of
`analysis/Sverify/Analysis/Contracts.lean`: `Rel.mayIssues_sound` and
`Rel.mayIssues_sound_all` prove that every issue that can happen is reported.
-/

namespace Substrait

open FloatCode (minI64 maxI64 castLo castHi)

/-! ## What may go wrong, abstractly -/

def rangeMay (lo hi : Int) (aa ar : AVal) : List Issue :=
  if aa.within lo hi && ar.within lo hi then [] else [.overflow]

theorem AVal.memNum_of_unscaled {a : AVal} {v : Value} {i : Int} (hm : a.Mem v)
    (hv : v.unscaled? = some i) : ∃ k, a.MemNum k i ∧ k.norm i = i := by
  cases v <;> simp only [Value.unscaled?, Option.some.injEq, reduceCtorEq] at hv <;> subst hv <;>
    exact ⟨_, hm, rfl⟩

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
    (ha : aa.MemNum kx x) (hr : ar.MemNum ky y) (hk : rangeIssue lo hi x y = some k)
    (hkx : kx ≠ .float := by decide) (hky : ky ≠ .float := by decide) :
    k ∈ rangeMay lo hi aa ar := by
  have ex : kx.norm x = x := by cases kx <;> first | rfl | exact absurd rfl hkx
  have ey : ky.norm y = y := by cases ky <;> first | rfl | exact absurd rfl hky
  simp only [rangeIssue] at hk
  split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
  subst hk
  simp only [rangeMay]
  split
  · rename_i hn hw
    simp only [Bool.and_eq_true] at hw
    have h1 := AVal.within_memNum hw.1 ha
    have h2 := AVal.within_memNum hw.2 hr
    rw [ex] at h1; rw [ey] at h2
    simp [h1, h2] at hn
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

/-- Is every string `a` describes ASCII (`Issue.nonAscii`, D43)? -/
def AVal.asciiOk (a : AVal) : Bool := a.ascii || a.plain || !a.str

/-- Is every string `a` describes ASCII without a vertical tab? -/
def AVal.plainOk (a : AVal) : Bool := a.plain || !a.str

/-- Is every string `a` describes in `UPPER`'s agreed alphabet, none a scalar of its raise
set (`Issue.caseDiffers`, D51)? ASCII text is. -/
def AVal.upperOk (a : AVal) : Bool := a.upperAgreed || a.asciiOk

/-- As `upperOk`, for `LOWER`. -/
def AVal.lowerOk (a : AVal) : Bool := a.lowerAgreed || a.asciiOk

omit [Boxes.Ambient] in
theorem AVal.isAscii_of_asciiOk {a : AVal} {s : String} (h : a.Mem (.str s))
    (ho : a.asciiOk = true) : Text.isAscii s = true := by
  simp only [AVal.Mem, AVal.MemR] at h
  simp only [AVal.asciiOk] at ho
  cases hx : a.ascii <;> cases hy : a.plain <;> cases hz : a.str <;>
    simp_all [AVal.textOk, Text.isPlain]

omit [Boxes.Ambient] in
theorem AVal.isPlain_of_plainOk {a : AVal} {s : String} (h : a.Mem (.str s))
    (ho : a.plainOk = true) : Text.isPlain s = true := by
  simp only [AVal.Mem, AVal.MemR] at h
  simp only [AVal.plainOk] at ho
  cases hx : a.ascii <;> cases hy : a.plain <;> cases hz : a.str <;>
    simp_all [AVal.textOk, Text.isPlain]

omit [Boxes.Ambient] in
theorem AVal.not_upperRaises_of_upperOk {a : AVal} {s : String} (h : a.Mem (.str s))
    (ho : a.upperOk = true) : Text.upperRaises s = false := by
  simp only [AVal.upperOk, Bool.or_eq_true] at ho
  rcases ho with ho | ho
  · simp only [AVal.Mem, AVal.MemR, AVal.textOk, ho, Bool.and_eq_true] at h
    simpa using h.2.1.2
  · exact Text.upperRaises_of_isAscii (AVal.isAscii_of_asciiOk h ho)

omit [Boxes.Ambient] in
theorem AVal.not_lowerRaises_of_lowerOk {a : AVal} {s : String} (h : a.Mem (.str s))
    (ho : a.lowerOk = true) : Text.lowerRaises s = false := by
  simp only [AVal.lowerOk, Bool.or_eq_true] at ho
  rcases ho with ho | ho
  · simp only [AVal.Mem, AVal.MemR, AVal.textOk, ho, Bool.and_eq_true] at h
    simpa using h.2.2
  · exact Text.lowerRaises_of_isAscii (AVal.isAscii_of_asciiOk h ho)

def UnFn.mayIssue : UnFn → AVal → AVal → List Issue
  | .neg, _, ar => if ar.within minI64 maxI64 then [] else [.wraps]
  | .ftoi, aa, _ => if aa.within castLo castHi then [] else [.badCast]
  | .narrow n, aa, _ => if aa.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1) then [] else [.badCast]
  | .wrap n, aa, _ => if aa.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1) then [] else [.wraps]
  | .regexMatch p, aa, _ =>
    (if Text.simpleRegex p then [] else [.badRegex]) ++
      (if !Text.regexClasses p.toList || aa.plainOk then [] else [.nonAscii])
  | .regexExtract p _, aa, _ | .regexReplace p _ _, aa, _ =>
    if !Text.regexClasses p.toList || aa.plainOk then [] else [.nonAscii]
  | .upper, aa, _ => if aa.upperOk then [] else [.caseDiffers]
  | .lower, aa, _ => if aa.lowerOk then [] else [.caseDiffers]
  | .reverse, aa, _ | .ascii, aa, _ => if aa.asciiOk then [] else [.nonAscii]
  | .dateTrunc u, aa, ar =>
    if u.calendar then (if tsFits aa ar then [] else [.overflow])
    else if ar.within minI64 maxI64 then [] else [.wraps]
  | .dayTrunc _, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .addMonths _ false, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .dateTime, aa, _ => rangeMay Time.dayMin Time.dayMax aa aa
  | .asTime, aa, _ => rangeMay Time.tsMin Time.tsMax aa aa
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
  | .fdivIeee => (inf aa && inf ab) || (aa.has 0 && ab.has 0)
  | .fmod => inf aa
  -- An integer exponent (`x ** 2`) is fine.
  | .fpow => aa.negFinite && !(ab.int.any fun b => b.point.any fun k => FloatCode.floor k == k)
  | _ => false

omit [Boxes.Ambient] in
theorem AVal.has_of_mem {a : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i) :
    a.has (k.norm i) = true := by
  obtain ⟨b, hb, hm, -⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.has, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => hm.1 l hl, fun u hu => hm.2 u hu⟩

omit [Boxes.Ambient] in
theorem AVal.has_of_memFloat {a : AVal} {i : Int} (h : a.Mem (.float i)) :
    a.has (FloatCode.canon i) = true :=
  AVal.has_of_mem h

omit [Boxes.Ambient] in
theorem AVal.has_posInf_of_mem {a : AVal} (h : a.Mem (.float FloatCode.posInf)) :
    a.has FloatCode.posInf = true := by
  have := AVal.has_of_memFloat h; rwa [FloatCode.canon_posInf] at this

omit [Boxes.Ambient] in
theorem AVal.has_negInf_of_mem {a : AVal} (h : a.Mem (.float FloatCode.negInf)) :
    a.has FloatCode.negInf = true := by
  have := AVal.has_of_memFloat h; rwa [FloatCode.canon_negInf] at this

omit [Boxes.Ambient] in
theorem AVal.negFinite_of_mem {a : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i)
    (h1 : FloatCode.negInf < k.norm i) (h2 : k.norm i < 0) : a.negFinite = true := by
  obtain ⟨b, hb, hm, -⟩ := h
  obtain ⟨bl, bh⟩ := b
  simp only [AVal.negFinite, hb, Option.any_some, Bool.and_eq_true, Option.all_eq_true,
    decide_eq_true_eq]
  exact ⟨fun l hl => by have := hm.1 l hl; omega, fun u hu => by have := hm.2 u hu; omega⟩

omit [Boxes.Ambient] in
/-- An IEEE NaN case of the inputs is one `BinFn.mayNan` reports. -/
theorem BinFn.mayNan_sound {f : BinFn} {aa ab : AVal} {a b : Int} (ha : aa.Mem (.float a))
    (hb : ab.Mem (.float b)) (h : nanCase f a b = true) : BinFn.mayNan f aa ab = true := by
  -- The analysis bounds canonical codes: `-0.0` is `0.0` there.
  have hA' := AVal.has_of_mem ha
  have hB' := AVal.has_of_mem hb
  rw [NumKind.norm_float] at hA' hB'
  have hAp : a = FloatCode.posInf → aa.has FloatCode.posInf = true := fun e => by
    rwa [e, FloatCode.canon_posInf] at hA'
  have hAn : a = FloatCode.negInf → aa.has FloatCode.negInf = true := fun e => by
    rwa [e, FloatCode.canon_negInf] at hA'
  have hBp : b = FloatCode.posInf → ab.has FloatCode.posInf = true := fun e => by
    rwa [e, FloatCode.canon_posInf] at hB'
  have hBn : b = FloatCode.negInf → ab.has FloatCode.negInf = true := fun e => by
    rwa [e, FloatCode.canon_negInf] at hB'
  have z0 : FloatCode.canon FloatCode.negZero = 0 := FloatFormat.canon_negZero fp64
  have hA0 : a = 0 ∨ a = FloatCode.negZero → aa.has 0 = true := fun e => by
    rcases e with e | e <;> rw [e] at hA'
    · rwa [FloatCode.canon_zero] at hA'
    · rwa [z0] at hA'
  have hB0 : b = 0 ∨ b = FloatCode.negZero → ab.has 0 = true := fun e => by
    rcases e with e | e <;> rw [e] at hB'
    · rwa [FloatCode.canon_zero] at hB'
    · rwa [z0] at hB'
  cases f <;> simp only [nanCase, Bool.false_eq_true] at h
  all_goals simp only [BinFn.mayNan, isInfCode, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h ⊢
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hAp h1, hBn h2⟩
    · exact .inr ⟨hAn h1, hBp h2⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hAp h1, hBp h2⟩
    · exact .inr ⟨hAn h1, hBn h2⟩
  · rcases h with ⟨h1, h2 | h2⟩ | ⟨h1 | h1, h2⟩
    · exact .inl ⟨hA0 h1, .inl (hBp h2)⟩
    · exact .inl ⟨hA0 h1, .inr (hBn h2)⟩
    · exact .inr ⟨.inl (hAp h1), hB0 h2⟩
    · exact .inr ⟨.inr (hAn h1), hB0 h2⟩
  · obtain ⟨h1 | h1, h2 | h2⟩ := h
    all_goals exact ⟨by first | exact .inl (hAp h1) | exact .inr (hAn h1),
      by first | exact .inl (hBp h2) | exact .inr (hBn h2)⟩
  · rcases h with h | ⟨h1, h2⟩
    · obtain ⟨h1 | h1, h2 | h2⟩ := h
      all_goals exact .inl ⟨by first | exact .inl (hAp h1) | exact .inr (hAn h1),
        by first | exact .inl (hBp h2) | exact .inr (hBn h2)⟩
    · exact .inr ⟨by rw [h1] at hA'; exact hA', by rw [h2] at hB'; exact hB'⟩
  · obtain ⟨h1 | h1, _⟩ := h
    · exact .inl (hAp h1)
    · exact .inr (hAn h1)
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    simp only [decide_eq_true_eq] at h1 h2 h3 h4
    have hp0 : (0 : Int) < FloatCode.posInf := FloatFormat.zero_lt_posInf fp64
    have hca : FloatCode.canon a = a := FloatCode.canon_of_bounds ⟨h1, by omega⟩
    have hcb : FloatCode.canon b = b := FloatCode.canon_of_bounds ⟨h3, h4⟩
    refine ⟨AVal.negFinite_of_mem ha (by rwa [NumKind.norm_float, hca])
      (by rwa [NumKind.norm_float, hca]), ?_⟩
    obtain ⟨bd, hbd, hm, -⟩ := hb
    rw [hbd]
    simp only [Option.any_some]
    cases hp : bd.point with
    | none => rfl
    | some k =>
      have := Bound.point_mem hp hm
      rw [NumKind.norm_float, hcb] at this
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
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1
  have hA := AVal.has_of_mem ha
  rw [NumKind.norm_float, FloatCode.canon_negInf] at hA
  have hcb : FloatCode.canon b = b := FloatCode.canon_of_bounds ⟨h2, h3⟩
  simp only [mayNegInfPow, hA, Bool.true_and, Bool.not_eq_true']
  obtain ⟨bd, hbd, hm, -⟩ := hb
  rw [hbd]
  simp only [Option.any_some]
  cases hp : bd.point with
  | none => rfl
  | some k =>
    have := Bound.point_mem hp hm
    rw [NumKind.norm_float, hcb] at this
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
  -- IEEE by a zero (D39): only `±∞ / ±∞` and `0 / 0` raise (D37).
  | .fdivIeee, aa, ab, _, _, _ => if BinFn.mayNan .fdivIeee aa ab then [.domain] else []
  | .fadd, aa, ab, _, _, _ => if BinFn.mayNan .fadd aa ab then [.domain] else []
  | .fsub, aa, ab, _, _, _ => if BinFn.mayNan .fsub aa ab then [.domain] else []
  | .fmul, aa, ab, _, _, _ => if BinFn.mayNan .fmul aa ab then [.domain] else []
  | .fpow, aa, ab, _, _, _ =>
    if BinFn.mayNan .fpow aa ab || mayNegInfPow aa ab then [.domain] else []
  | .ipow, aa, ab, _, _, _ =>
    (if ab.int.all (·.lo.any (0 ≤ ·)) then [] else [.negExponent]) ++
      (if powFits aa ab then [] else [.overflow])
  | .strRepeat, _, ab, _, _, sz => repeatMay sz ab
  | .ilike, aa, ab, _, _, _ | .levenshtein, aa, ab, _, _, _ =>
    if aa.asciiOk && ab.asciiOk then [] else [.nonAscii]
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
    (hf : isFiniteCode (k.norm i) = true) : a.mayFinite = true := by
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
in `float-bounds/FloatBounds/Arith.lean`, from `NativeLink.exp`. Stated on the
canonical code, so `-0.0` is covered (`exp(-0.0) = 1`, D31). -/
axiom FloatCode.exp_fin {a r : Int} (ha : FloatCode.IsFin (FloatCode.canon a))
    (h : FloatCode.scaled (FloatCode.canon a) ≤ 709 * 2 ^ 1074) (hr : FMath.apply .exp a = some r) :
    FloatCode.IsFin r

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

/-- Does a bound show its doubles at least `1` in magnitude? -/
def Bound.atLeastOne (y : Bound) : Bool :=
  y.allGe (FloatCode.exactCode 1) || y.allLe (FloatCode.exactCode (-1))

/-- Does a bound show its doubles at most `1` in magnitude? -/
def Bound.atMostOne (y : Bound) : Bool := y.within (FloatCode.exactCode (-1)) (FloatCode.exactCode 1)

/-- Does a bound show its doubles zero? -/
def Bound.isZero (y : Bound) : Bool := y.within 0 0

/-- Is the result at most an argument in magnitude: a quotient by a double of
at least `1`, a product with one of at most `1`, or a sum or difference with a
zero, such as the `+ 0.0` that canonicalises a zero's sign (#1787)? -/
def BinFn.shrinks : BinFn → Bound → Bound → Bool
  | .fdiv, _, y | .fdivIeee, _, y => y.atLeastOne
  | .fmul, x, y => x.atMostOne || y.atMostOne
  | .fadd, x, y | .fsub, x, y => x.isZero || y.isZero
  | _, _, _ => false

/-- Do the arguments' bounds show the result finite (#582)? Their bounds
bound the result's, or the call shrinks its first argument (#1787). -/
def BinFn.finiteResult (f : BinFn) (aa ab : AVal) : Bool :=
  match aa.int, ab.int with
  | some x, some y => f.shrinks x y || match f.fBound x y with
    | ⟨some l, some h⟩ => decide (FloatCode.negInf < l) && decide (h < FloatCode.posInf)
    | _ => false
  | _, _ => false

/-- May the call overflow to `±∞` (`BinFn.infIssue`)? Where both arguments
may be finite and their bounds do not show the result finite. -/
def BinFn.mayInf (f : BinFn) (aa ab : AVal) : List Issue :=
  if f.makesInf && aa.mayFinite && ab.mayFinite && !f.finiteResult aa ab then [.infinite] else []

/-- The bounds of the canonical codes of the arguments bound the canonical
code of the result. -/
theorem BinFn.fBound_mem (f : BinFn) {x y : Bound} {a b r : Int} (hx : x.Mem (FloatCode.canon a))
    (hy : y.Mem (FloatCode.canon b)) (hr : f.apply (.float a) (.float b) = .float r) :
    (f.fBound x y).Mem (FloatCode.canon r) := by
  cases f <;> simp only [BinFn.fBound] <;> try exact Bound.mem_top _
  all_goals simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
  · exact faddBound_mem' false hx hy (fun _ => (FloatCode.fadd_canon a b).symm) (fun h => by cases h)
  · exact faddBound_mem' true hx hy (fun h => by cases h) (fun _ => (FloatCode.fsub_canon a b).symm)
  · rw [← FloatCode.fmul_canon]; exact fmulBound_mem hx hy
  · rw [← FloatCode.fdiv_canon_left]; exact fdivBound_mem hx hy

omit [Boxes.Ambient] in
theorem Bound.atLeastOne_scaled {y : Bound} {c : Int} (hy : y.Mem c) (h : y.atLeastOne = true) :
    FloatCode.unitK ≤ (FloatCode.scaled c).natAbs := by
  have e1 := FloatCode.scaled_exactCode 1
  have e2 := FloatCode.scaled_exactCode (-1)
  simp only [Bound.atLeastOne, Bool.or_eq_true] at h
  rcases h with h | h
  · have := FloatCode.scaled_mono (Bound.allGe_le h hy); omega
  · have := FloatCode.scaled_mono (Bound.le_allLe h hy); omega

omit [Boxes.Ambient] in
theorem Bound.isZero_scaled {y : Bound} {c : Int} (hy : y.Mem c) (h : y.isZero = true) :
    FloatCode.scaled c = 0 := by
  simp only [Bound.isZero, Bound.within, Bool.and_eq_true] at h
  have h1 := Bound.allGe_le h.1 hy
  have h2 := Bound.le_allLe h.2 hy
  rw [show c = 0 by omega]; rfl

omit [Boxes.Ambient] in
theorem Bound.atMostOne_scaled {y : Bound} {c : Int} (hy : y.Mem c) (h : y.atMostOne = true) :
    (FloatCode.scaled c).natAbs ≤ FloatCode.unitK := by
  have e1 := FloatCode.scaled_exactCode 1
  have e2 := FloatCode.scaled_exactCode (-1)
  simp only [Bound.atMostOne, Bound.within, Bool.and_eq_true] at h
  have := FloatCode.scaled_mono (Bound.allGe_le h.1 hy)
  have := FloatCode.scaled_mono (Bound.le_allLe h.2 hy)
  omega

/-- A call that shrinks its first argument (`BinFn.shrinks`) has a finite
result on finite arguments (`FloatCode.fdiv_fin_of_one_le`,
`FloatCode.fmul_fin_of_le_one`). -/
theorem BinFn.shrinks_fin {f : BinFn} {x y : Bound} {a b r : Int} (hx : x.Mem (FloatCode.canon a))
    (hy : y.Mem (FloatCode.canon b)) (hfa : isFiniteCode (FloatCode.canon a) = true)
    (hfb : isFiniteCode (FloatCode.canon b) = true) (hr : f.apply (.float a) (.float b) = .float r)
    (hs : f.shrinks x y = true) : FloatCode.IsFin (FloatCode.canon r) := by
  have fa : FloatCode.IsFin (FloatCode.canon a) := by
    simpa [isFiniteCode, FloatCode.IsFin] using hfa
  have fb : FloatCode.IsFin (FloatCode.canon b) := by
    simpa [isFiniteCode, FloatCode.IsFin] using hfb
  cases f <;> simp only [BinFn.shrinks, Bool.false_eq_true] at hs
  case fmul =>
    simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
    rw [← FloatCode.fmul_canon]
    simp only [Bool.or_eq_true] at hs
    exact FloatCode.fmul_fin_of_le_one fa fb
      (hs.imp (Bound.atMostOne_scaled hx) (Bound.atMostOne_scaled hy))
  case fadd =>
    simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
    rw [← FloatCode.fadd_canon]
    simp only [Bool.or_eq_true] at hs
    exact FloatCode.fadd_fin_of_zero fa fb (hs.imp (Bound.isZero_scaled hx) (Bound.isZero_scaled hy))
  case fsub =>
    simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
    rw [← FloatCode.fsub_canon]
    simp only [Bool.or_eq_true] at hs
    exact FloatCode.fsub_fin_of_zero fa fb (hs.imp (Bound.isZero_scaled hx) (Bound.isZero_scaled hy))
  case fdiv =>
    simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
    rw [← FloatCode.fdiv_canon_left]
    exact FloatCode.fdiv_fin_of_one_le fa fb (Bound.atLeastOne_scaled hy hs)
  case fdivIeee =>
    simp only [BinFn.apply, Value.float.injEq] at hr; subst hr
    have h1 := Bound.atLeastOne_scaled hy hs
    -- `|b| ≥ 1`: `b` is neither `-0.0` nor the negative NaN, so `canon` keeps it.
    have hb : FloatCode.canon b = b := by
      rcases FloatCode.canon_cases b with ⟨-, h0⟩ | ⟨-, hn⟩ | h
      · rw [h0, show FloatCode.scaled 0 = 0 from rfl] at h1; have := FloatCode.unitK_pos; omega
      · rw [hn] at fb; have := fb.not_nan; simp [FloatCode.isNanCode] at this
      · exact h
    rw [← FloatCode.fdiv_canon_left, ← hb]
    exact FloatCode.fdiv_fin_of_one_le fa fb h1

theorem BinFn.finiteResult_false (f : BinFn) {aa ab : AVal} {a b r : Int}
    (ha : aa.Mem (.float a)) (hb : ab.Mem (.float b)) (hfa : isFiniteCode (FloatCode.canon a) = true)
    (hfb : isFiniteCode (FloatCode.canon b) = true) (hr : f.apply (.float a) (.float b) = .float r)
    (hinf : isInfCode r = true) : f.finiteResult aa ab = false := by
  obtain ⟨x, hx, hxm, -⟩ := ha
  obtain ⟨y, hy, hym, -⟩ := hb
  have hm := f.fBound_mem hxm hym hr
  simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at hinf
  have hcr : FloatCode.canon r = r := by
    rcases hinf with rfl | rfl
    · exact FloatCode.canon_posInf
    · exact FloatCode.canon_negInf
  have hs : f.shrinks x y = false := by
    rw [← Bool.not_eq_true]; intro hsh
    have hfin := BinFn.shrinks_fin hxm hym hfa hfb hr hsh
    rw [hcr] at hfin
    obtain ⟨h1, h2⟩ := hfin
    rcases hinf with rfl | rfl <;> omega
  rw [hcr] at hm
  unfold BinFn.finiteResult
  rw [hx, hy]
  dsimp only
  rw [hs, Bool.false_or]
  split
  · rename_i l h heq
    rw [heq] at hm
    have h1 := hm.1 l rfl
    have h2 := hm.2 h rfl
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    rcases hinf with rfl | rfl <;> omega
  · rfl

omit [Boxes.Ambient] in
set_option exponentiation.threshold 1100 in
theorem expFinite_false {aa : AVal} {a r : Int} (ha : aa.Mem (.float a))
    (hfin : isFiniteCode (FloatCode.canon a) = true) (hr : FMath.apply .exp a = some r)
    (hinf : isInfCode r = true) :
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
      simp [BinFn.mayInf, hc.1.1.1.1, AVal.mayFinite_of_mem ha hc.1.1.1.2, AVal.mayFinite_of_mem hb hc.1.1.2,
        BinFn.finiteResult_false f ha hb hc.1.1.1.2 hc.1.1.2 heq hc.1.2]
    · simp at hk
  · simp at hk

/-- May the bound hold a value: no lower end above its upper end? -/
def Bound.nonempty : Bound → Bool
  | ⟨some l, some h⟩ => decide (l ≤ h)
  | _ => true

omit [Boxes.Ambient] in
theorem Bound.nonempty_of_mem {p : Bound} {c : Int} (h : p.Mem c) : p.nonempty = true := by
  obtain ⟨lo, hi⟩ := p
  cases lo <;> cases hi <;> simp only [Bound.nonempty]
  rename_i l u
  have := h.1 l rfl; have := h.2 u rfl
  simp only [decide_eq_true_eq]; omega

/-- The parts of a divisor's bound that a nonzero decimal at scale `s`, as a
double, can be in: at least `ofDecimal 1 s`, or at most `ofDecimal (-1) s`.
Its ends are finite, as every decimal's double is (`ofDecimal_bounds`). -/
def Bound.decParts (s : Nat) (y : Bound) : List Bound :=
  let d1 := FloatCode.ofDecimal 1 s
  let m1 := FloatCode.ofDecimal (-1) s
  let top := FloatCode.posInf - 1
  let bot := FloatCode.negInf + 1
  [⟨some (y.lo.elim d1 (max d1)), some (y.hi.elim top (min top))⟩,
    ⟨some (y.lo.elim bot (max bot)), some (y.hi.elim m1 (min m1))⟩].filter Bound.nonempty

/-- Does a double divided by a nonzero decimal at scale `s`, as a double, stay
finite by the bounds: the dividend's over each part of the divisor's? -/
def decQuotFinite (s : Nat) (aa ab : AVal) : Bool :=
  match aa.int, ab.int with
  | some x, some y => (y.decParts s).all fun p => match fdivBound x p with
    | ⟨some l, some h⟩ => decide (FloatCode.negInf < l) && decide (h < FloatCode.posInf)
    | _ => false
  | _, _ => false

omit [Boxes.Ambient] in
/-- A nonzero decimal's double is in one of the parts `Bound.decParts` keeps. -/
theorem Bound.decParts_mem {s : Nat} {y : Bound} {i : Int} (hi0 : i ≠ 0)
    (hy : y.Mem (FloatCode.ofDecimal i s)) : ∃ p ∈ y.decParts s, p.Mem (FloatCode.ofDecimal i s) := by
  obtain ⟨lo, hi⟩ := y
  have hf := FloatCode.ofDecimal_bounds i s
  -- Each end of a part is an end of `y` or a bound every nonzero decimal of its sign meets.
  have hl : ∀ d, d ≤ FloatCode.ofDecimal i s → ∀ l, some (lo.elim d (max d)) = some l →
      l ≤ FloatCode.ofDecimal i s := fun d hd l hl => by
    cases lo with
    | none => simp only [Option.elim, Option.some.injEq] at hl; omega
    | some l' => simp only [Option.elim, Option.some.injEq] at hl; have := hy.1 l' rfl; omega
  have hh : ∀ d, FloatCode.ofDecimal i s ≤ d → ∀ u, some (hi.elim d (min d)) = some u →
      FloatCode.ofDecimal i s ≤ u := fun d hd u hu => by
    cases hi with
    | none => simp only [Option.elim, Option.some.injEq] at hu; omega
    | some h => simp only [Option.elim, Option.some.injEq] at hu; have := hy.2 h rfl; omega
  have hp : ∀ p, p.Mem (FloatCode.ofDecimal i s) → p ∈ [
      (⟨some (lo.elim (FloatCode.ofDecimal 1 s) (max (FloatCode.ofDecimal 1 s))),
        some (hi.elim (FloatCode.posInf - 1) (min (FloatCode.posInf - 1)))⟩ : Bound),
      ⟨some (lo.elim (FloatCode.negInf + 1) (max (FloatCode.negInf + 1))),
        some (hi.elim (FloatCode.ofDecimal (-1) s) (min (FloatCode.ofDecimal (-1) s)))⟩] →
      ∃ p ∈ Bound.decParts s ⟨lo, hi⟩, p.Mem (FloatCode.ofDecimal i s) :=
    fun p hm hor => ⟨p, by
      simp only [Bound.decParts, List.mem_filter]
      exact ⟨hor, Bound.nonempty_of_mem hm⟩, hm⟩
  rcases Int.lt_or_gt_of_ne hi0 with hneg | hpos
  · have hm := FloatCode.ofDecimal_mono s (show i ≤ -1 by omega)
    exact hp ⟨some (lo.elim (FloatCode.negInf + 1) (max (FloatCode.negInf + 1))),
      some (hi.elim (FloatCode.ofDecimal (-1) s) (min (FloatCode.ofDecimal (-1) s)))⟩
      ⟨hl _ (by omega), hh _ hm⟩ (by simp)
  · have hm := FloatCode.ofDecimal_mono s (show 1 ≤ i by omega)
    exact hp ⟨some (lo.elim (FloatCode.ofDecimal 1 s) (max (FloatCode.ofDecimal 1 s))),
      some (hi.elim (FloatCode.posInf - 1) (min (FloatCode.posInf - 1)))⟩
      ⟨hl _ hm, hh _ (by omega)⟩ (by simp)

/-- A double divided by a nonzero decimal as a double does not overflow where
`decQuotFinite` holds: the divisor is in a part of its bound away from zero,
over which `fdivBound` bounds the quotient (#1787). -/
theorem decQuotFinite_sound {s : Nat} {aa ab : AVal} {a i : Int} {k : Issue}
    (hq : decQuotFinite s aa ab = true) (ha : aa.Mem (.float a))
    (hb : ab.Mem (.float (FloatCode.ofDecimal i s))) (hi0 : i ≠ 0)
    (hk : BinFn.fdiv.infIssue (.float a) (.float (FloatCode.ofDecimal i s)) = some k) : False := by
  obtain ⟨x, hx, hxm, -⟩ := ha
  obtain ⟨y, hy, hym, -⟩ := hb
  rw [NumKind.norm_float] at hxm hym
  have hfin := FloatCode.ofDecimal_bounds i s
  have hcc : FloatCode.canon (FloatCode.ofDecimal i s) = FloatCode.ofDecimal i s := by
    have := FloatCode.negZero_eq'; have := FloatCode.negNan_eq'; have := FloatCode.negInf_eq
    rcases FloatCode.canon_cases (FloatCode.ofDecimal i s) with ⟨h, -⟩ | ⟨h, -⟩ | h
    · omega
    · omega
    · exact h
  rw [hcc] at hym
  obtain ⟨p, hp, hpm⟩ := Bound.decParts_mem hi0 hym
  unfold decQuotFinite at hq
  rw [hx, hy] at hq
  have hP := List.all_eq_true.mp hq p hp
  have hm := fdivBound_mem hxm hpm
  rw [FloatCode.fdiv_canon_left] at hm
  unfold BinFn.infIssue at hk
  simp only [BinFn.apply, hcc] at hk
  split at hk
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    have hinf := hc.1.2
    simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at hinf
    have hcr : FloatCode.canon (FloatCode.fdiv a (FloatCode.ofDecimal i s)) =
        FloatCode.fdiv a (FloatCode.ofDecimal i s) := by
      rcases hinf with h | h <;> rw [h]
      · exact FloatCode.canon_posInf
      · exact FloatCode.canon_negInf
    rw [hcr] at hm
    generalize fdivBound x p = B at hP hm
    obtain ⟨lo, hi⟩ := B
    cases lo with
    | none => simp at hP
    | some l => cases hi with
      | none => simp at hP
      | some u =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        have := hm.1 l rfl; have := hm.2 u rfl
        rcases hinf with h | h <;> omega
  · simp at hk

/-- `BinFn.mayInf` of a call `f a b`, read with its divisor's shape
: a double
divided by an integer cast to a double (`x / DOUBLE(n)`) does not overflow.
Its divisor is zero, which raises first (`BinFn.issue`), or at least `1` in
magnitude, so the quotient is at most `x` (`FloatCode.fdiv_ofInt_fin`, #1787). -/
def Expr.mayInfBin (f : BinFn) (b : Expr) (aa ab : AVal) : List Issue :=
  match f, b with
  | .fdiv, .un .itof _ => []
  | .fdiv, .un (.dtof s) _ => if decQuotFinite s aa ab then [] else f.mayInf aa ab
  | _, _ => f.mayInf aa ab

theorem UnFn.itof_float {x : Value} {c : Int} (h : UnFn.itof.apply x = .float c) :
    ∃ i, c = FloatCode.ofInt i := by
  cases x <;> simp [UnFn.apply] at h
  exact ⟨_, h.symm⟩

theorem UnFn.dtof_float {s : Nat} {x : Value} {c : Int} (h : (UnFn.dtof s).apply x = .float c) :
    ∃ i, c = FloatCode.ofDecimal i s := by
  cases x <;> simp [UnFn.apply] at h
  all_goals exact ⟨_, h.symm⟩

/-- A double divided by a nonzero integer, as a double, does not overflow:
where `BinFn.issue` gives nothing, the divisor is not zero. -/
theorem BinFn.fdiv_ofInt_infIssue {v : Value} {i : Int}
    (hj : BinFn.fdiv.issue v (.float (FloatCode.ofInt i)) = none) :
    BinFn.fdiv.infIssue v (.float (FloatCode.ofInt i)) = none := by
  cases v
  case float a =>
    have hi0 : i ≠ 0 := by
      rintro rfl
      have h0 : FloatCode.ofInt 0 = 0 := by rw [FloatCode.ofInt_exact (by decide)]; rfl
      simp [BinFn.issue, h0, FloatCode.canon_zero] at hj
    unfold BinFn.infIssue
    simp only [BinFn.apply, FloatCode.canon_ofInt]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, isFiniteCode] at hc
      have hf := FloatCode.fdiv_ofInt_fin (a := FloatCode.canon a) ⟨hc.1.1.1.2.1, hc.1.1.1.2.2⟩ hi0
      rw [FloatCode.fdiv_canon_left] at hf
      have hr := hc.1.2
      simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at hr
      rcases hr with e | e <;> rw [e] at hf
      · rw [FloatCode.canon_posInf] at hf; exact absurd hf.2 (Int.lt_irrefl _)
      · rw [FloatCode.canon_negInf] at hf; exact absurd hf.1 (Int.lt_irrefl _)
    · rfl
  all_goals simp [BinFn.infIssue]

theorem Expr.mayInfBin_sound {row : Row} (f : BinFn) (a b : Expr) {aa ab : AVal} {k : Issue}
    (ha : aa.Mem (a.eval row)) (hb : ab.Mem (b.eval row))
    (hj : f.issue (a.eval row) (b.eval row) = none)
    (hi : f.infIssue (a.eval row) (b.eval row) = some k) : k ∈ Expr.mayInfBin f b aa ab := by
  unfold Expr.mayInfBin
  split
  · rename_i e
    exfalso
    cases hw : (Expr.un .itof e).eval row with
    | float c =>
      obtain ⟨i, rfl⟩ := UnFn.itof_float hw
      rw [hw] at hj hi
      rw [BinFn.fdiv_ofInt_infIssue hj] at hi
      cases hi
    | _ => rw [hw] at hi; simp [BinFn.infIssue] at hi
  · rename_i s e
    split
    · rename_i hq
      exfalso
      cases hw : (Expr.un (.dtof s) e).eval row with
      | float c =>
        obtain ⟨i, rfl⟩ := UnFn.dtof_float hw
        rw [hw] at hj hi hb
        cases hv : a.eval row with
        | float x =>
          rw [hv] at hj hi ha
          have hi0 : i ≠ 0 := by
            rintro rfl
            simp [BinFn.issue, FloatCode.ofDecimal_zero, FloatCode.canon_zero] at hj
          exact decQuotFinite_sound hq ha hb hi0 hi
        | _ => rw [hv] at hi; simp [BinFn.infIssue] at hi
      | _ => rw [hw] at hi; simp [BinFn.infIssue] at hi
    · exact BinFn.mayInf_sound _ ha hb hi
  · exact BinFn.mayInf_sound f ha hb hi

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
  | .fadd | .fsub | .fmul | .fdiv | .fdivIeee | .fmod => true
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
  | .fdivIeee => (inf pa && inf pb) || (pa 0 && pb 0)
  | .fmod => inf pa
  | _ => true

omit [Boxes.Ambient] in
/-- The predicates read canonical codes, as the analysis does: `-0.0` is
`0.0` there. -/
theorem BinFn.mayNanBy_sound {f : BinFn} {pa pb : Int → Bool} {a b : Int}
    (ha : pa (FloatCode.canon a) = true) (hb : pb (FloatCode.canon b) = true)
    (h : nanCase f a b = true) : f.mayNanBy pa pb = true := by
  have hAp : a = FloatCode.posInf → pa FloatCode.posInf = true := fun e => by
    rwa [e, FloatCode.canon_posInf] at ha
  have hAn : a = FloatCode.negInf → pa FloatCode.negInf = true := fun e => by
    rwa [e, FloatCode.canon_negInf] at ha
  have hBp : b = FloatCode.posInf → pb FloatCode.posInf = true := fun e => by
    rwa [e, FloatCode.canon_posInf] at hb
  have hBn : b = FloatCode.negInf → pb FloatCode.negInf = true := fun e => by
    rwa [e, FloatCode.canon_negInf] at hb
  have z0 : FloatCode.canon FloatCode.negZero = 0 := FloatFormat.canon_negZero fp64
  have hA0 : a = 0 ∨ a = FloatCode.negZero → pa 0 = true := fun e => by
    rcases e with e | e <;> rw [e] at ha
    · rwa [FloatCode.canon_zero] at ha
    · rwa [z0] at ha
  have hB0 : b = 0 ∨ b = FloatCode.negZero → pb 0 = true := fun e => by
    rcases e with e | e <;> rw [e] at hb
    · rwa [FloatCode.canon_zero] at hb
    · rwa [z0] at hb
  cases f <;> simp only [nanCase, Bool.false_eq_true] at h <;>
    simp only [BinFn.mayNanBy, isInfCode, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at h ⊢
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hAp h1, hBn h2⟩
    · exact .inr ⟨hAn h1, hBp h2⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hAp h1, hBp h2⟩
    · exact .inr ⟨hAn h1, hBn h2⟩
  · rcases h with ⟨h1, h2 | h2⟩ | ⟨h1 | h1, h2⟩
    · exact .inl ⟨hA0 h1, .inl (hBp h2)⟩
    · exact .inl ⟨hA0 h1, .inr (hBn h2)⟩
    · exact .inr ⟨.inl (hAp h1), hB0 h2⟩
    · exact .inr ⟨.inr (hAn h1), hB0 h2⟩
  · obtain ⟨h1 | h1, h2 | h2⟩ := h
    all_goals exact ⟨by first | exact .inl (hAp h1) | exact .inr (hAn h1),
      by first | exact .inl (hBp h2) | exact .inr (hBn h2)⟩
  · rcases h with h | ⟨h1, h2⟩
    · obtain ⟨h1 | h1, h2 | h2⟩ := h
      all_goals exact .inl ⟨by first | exact .inl (hAp h1) | exact .inr (hAn h1),
        by first | exact .inl (hBp h2) | exact .inr (hBn h2)⟩
    · exact .inr ⟨by rw [h1] at ha; exact ha, by rw [h2] at hb; exact hb⟩
  · obtain ⟨h1 | h1, _⟩ := h
    · exact .inl (hAp h1)
    · exact .inr (hAn h1)

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
        Expr.mayInfBin f b (a.absD env fs ks) (b.absD env fs ks)).map (·, .bin f a b)
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    let tk := withAlts (c.cstrAlts true) ks ors
    let ek := withAlts (c.cstrAlts false) ks ors
    c.mayIssues env fs ks ors ++
      (if ac.tt then t.mayIssues (c.refine env) (fs ++ c.factsOf) tk.1 tk.2 else []) ++
      (if ac.nonBool || ac.ff then e.mayIssues (c.refineNeg env) fs ek.1 ek.2 else [])
  -- The body on any element, with the row in scope (D28).
  | .hof _ l b => l.mayIssues env fs ks ors ++ b.mayIssues (AVal.top :: env) [] []

/-! ### `Expr.mayIssues` in one pass (#925)

`Expr.mayIssues` asks each node for its own and its operands' abstract values,
and `Expr.absD` evaluates the whole subtree each time: a node's value is
computed once per ancestor. `Expr.mayIssuesA` returns each subtree's issues
with its abstract value, so a parent takes its operands' values from the
recursion. Only what the recursion cannot give is evaluated again: the right
operand of `OR` under the left one's refinement, and the branches of a `CASE`
or a lambda's body, which `Expr.absD` evaluates under other environments. The
`@[csimp]` lemma makes compiled code run it; the proofs keep `Expr.mayIssues`. -/

/-- `Expr.nonZero` given `x`'s abstract value `ax` (`Expr.nonZero_eq_nonZeroA`). -/
def Expr.nonZeroA (env : List AVal) (fs : List Fact) (ks : Assumptions) (k : NumKind) (x : Expr)
    (ax : AVal) : Bool :=
  ax.int.all (!·.has0) ||
  ks.any (fun sk => sk.1 == x && match sk.2 with | .ne k' 0 => k' == k | _ => false) ||
  (match x.linTerm with | some (j, c) => fs.contains (.ne j k (-c)) | none => false) ||
  match x with
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    (!ac.tt || t.nonZero (c.refine env) fs (c.cstrs true ++ ks) k) &&
      (!(ac.nonBool || ac.ff) || e.nonZero (c.refineNeg env) fs (c.cstrs false ++ ks) k)
  | .bin .mul a b => k == .int && a.nonZero env fs ks .int && b.nonZero env fs ks .int
  | .un .itof a => k == .float && a.nonZero env fs ks .int
  | _ => false

theorem Expr.nonZero_eq_nonZeroA (env : List AVal) (fs : List Fact) (ks : Assumptions)
    (k : NumKind) (x : Expr) :
    x.nonZero env fs ks k = x.nonZeroA env fs ks k (x.absD env fs ks) := by
  rw [Expr.nonZero.eq_def]; rfl

/-- `Expr.mayIssues` with `Expr.absD` (`Expr.mayIssuesA_eq`). -/
def Expr.mayIssuesA (env : List AVal) (fs : List Fact) (ks : Assumptions) (ors : Clauses) :
    Expr → List (Issue × Expr) × AVal
  | .lit v => ([], (Expr.lit v).absD env fs ks)
  | .field i => ([], (Expr.field i).absD env fs ks)
  | .un f a =>
    let ra := a.mayIssuesA env fs ks ors
    let ar := narrowAll ks (.un f a) (f.abs ra.2)
    (ra.1 ++ (f.mayIssue ra.2 ar ++ f.mayInf ra.2).map (·, .un f a), ar)
  | .bin f a b =>
    let ra := a.mayIssuesA env fs ks ors
    let rb := b.mayIssuesA env fs ks ors
    let ar := Expr.absBin env fs ks f a b ra.2 (fun _ => rb.2) (fun env' ks' => b.absD env' fs ks')
    (ra.1 ++ rb.1 ++
      (f.mayIssueX ra.2 rb.2 ar (b.nonZeroA env fs ks f.divKind rb.2) a.strBytes?
        (Expr.nanExcluded env fs ks ors f a b) ++ Expr.mayInfBin f b ra.2 rb.2).map (·, .bin f a b), ar)
  | .ifThen c t e =>
    let rc := c.mayIssuesA env fs ks ors
    let tk := withAlts (c.cstrAlts true) ks ors
    let ek := withAlts (c.cstrAlts false) ks ors
    (rc.1 ++
      (if rc.2.tt then t.mayIssues (c.refine env) (fs ++ c.factsOf) tk.1 tk.2 else []) ++
      (if rc.2.nonBool || rc.2.ff then e.mayIssues (c.refineNeg env) fs ek.1 ek.2 else []),
      (Expr.ifThen c t e).absD env fs ks)
  | .hof f l b =>
    ((l.mayIssuesA env fs ks ors).1 ++ b.mayIssues (AVal.top :: env) [] [],
      (Expr.hof f l b).absD env fs ks)

theorem Expr.mayIssuesA_eq (env : List AVal) (fs : List Fact) (ks : Assumptions) (ors : Clauses) :
    ∀ e : Expr, e.mayIssuesA env fs ks ors = (e.mayIssues env fs ks ors, e.absD env fs ks)
  | .lit _ | .field _ => rfl
  | .un f a => by
    simp only [Expr.mayIssuesA, Expr.mayIssuesA_eq env fs ks ors a, Expr.mayIssues, Expr.absD]
  | .bin f a b => by
    simp only [Expr.mayIssuesA, Expr.mayIssuesA_eq env fs ks ors a,
      Expr.mayIssuesA_eq env fs ks ors b, Expr.mayIssues, Expr.nonZero_eq_nonZeroA, Expr.absD]
  | .ifThen c t e => by
    simp only [Expr.mayIssuesA, Expr.mayIssuesA_eq env fs ks ors c, Expr.mayIssues]
  | .hof f l b => by
    simp only [Expr.mayIssuesA, Expr.mayIssuesA_eq env fs ks ors l, Expr.mayIssues]

/-- `Expr.mayIssues` by `Expr.mayIssuesA`. -/
def Expr.mayIssuesFast (env : List AVal) (fs : List Fact) (ks : Assumptions := [])
    (ors : Clauses := []) (e : Expr) : List (Issue × Expr) :=
  (e.mayIssuesA env fs ks ors).1

omit [Boxes.Ambient] in
@[csimp] theorem Expr.mayIssues_csimp : @Expr.mayIssues = @Expr.mayIssuesFast := by
  funext _ env fs ks ors e; rw [Expr.mayIssuesFast, Expr.mayIssuesA_eq]

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
    ∀ (k : NumKind) (x : Expr), x.nonZero env fs ks k = true → ∀ j, x.eval row = k.val j →
      k.norm j ≠ 0 := by
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
      have hn := hf y hy
      obtain ⟨h1, h2⟩ := Expr.linTerm_norm hlin hy (by rw [hj]; exact NumKind.val_ne_null _ _)
      have h3 := h2 0
      rw [Int.zero_sub, NumKind.norm_zero, Int.zero_sub] at h3
      rw [h1]; rw [h3] at hn; omega
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
      have h1 := Expr.nonZero_sound h hfs hks .int a ha' x ha
      have h2 := Expr.nonZero_sound h hfs hks .int b hb' y hb
      simp only [NumKind.norm_int] at h1 h2 ⊢
      exact Int.mul_ne_zero h1 h2
    · rename_i a
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, ha'⟩ := hc
      simp only [eval, NumKind.val] at hj
      cases ha : a.eval row <;> simp [ha, UnFn.apply] at hj
      rename_i i
      subst hj
      rw [NumKind.norm_float, FloatCode.canon_ofInt]
      exact FloatCode.ofInt_ne_zero (by simpa using Expr.nonZero_sound h hfs hks .int a ha' i ha)
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
    cases v with
    | str s =>
      simp only [UnFn.issue] at hk
      simp only [UnFn.mayIssue, List.mem_append]
      split at hk
      · rename_i hn
        simp only [Option.some.injEq] at hk; subst hk
        left; simpa using hn
      · split at hk
        · rename_i hs hc
          simp only [Option.some.injEq] at hk; subst hk
          right
          simp only [Bool.not_eq_true] at hs
          by_cases hp : aa.plainOk = true
          · have := Text.classesDiffer_of_isPlain p (AVal.isPlain_of_plainOk ha hp)
            simp_all
          · simp only [hp, Bool.or_false]
            simp only [Text.classesDiffer, Bool.and_eq_true] at hc
            simp [hc.1]
        · simp at hk
    | _ => simp_all [UnFn.issue, UnFn.mayIssue]
  case regexExtract p g | regexReplace p r g =>
    all_goals
      cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk
      rename_i s
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk; rename_i hc
      simp only [UnFn.mayIssue]
      split
      · rename_i hok
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at hok
        rcases hok with hok | hok
        · simp [Text.classesDiffer, hok] at hc
        · have := Text.classesDiffer_of_isPlain p (AVal.isPlain_of_plainOk ha hok)
          simp_all
      · simp
  case upper =>
    cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk
    rename_i s
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i hn
    simp only [UnFn.mayIssue]
    split
    · rename_i hok
      exact absurd hn (by rw [AVal.not_upperRaises_of_upperOk ha hok]; simp)
    · simp
  case lower =>
    cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk
    rename_i s
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i hn
    simp only [UnFn.mayIssue]
    split
    · rename_i hok
      exact absurd hn (by rw [AVal.not_lowerRaises_of_lowerOk ha hok]; simp)
    · simp
  case reverse | ascii =>
    cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk
    rename_i s
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i hn
    simp only [UnFn.mayIssue]
    split
    · rename_i hok; exact absurd (AVal.isAscii_of_asciiOk ha hok) (by simpa using hn)
    · simp
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
        obtain ⟨_, hm, hn'⟩ := AVal.memNum_of_unscaled ha hu
        have := AVal.within_memNum hfits hm
        rw [hn'] at this
        exact absurd this hn
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
      rw [NumKind.norm_float] at hm
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
      rw [NumKind.norm_float] at h
      simp only [between, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, hx, hx₁, hx₂⟩ := FloatCode.toInt?_of_range h.1 h.2
      simp [hx, inI64, between, hx₁, hx₂] at hk
    · cases hx : FloatCode.toInt? (FloatCode.canon c) <;> simp only [hx] at hk <;> (try split at hk) <;>
        simp_all
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
        rw [NumKind.norm_float] at hq
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
  case timeOfDay.ts ts | timeOfDay.tod ts | asTime.int ts | dateTime.date ts | strftime.ts fmt ts |
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
      simp only [NumKind.norm_int] at this
      omega
  · simp

omit [Boxes.Ambient] in
theorem substrSafe_sound {n : Option Nat} {ab : AVal} {a : Int} (hb : ab.Mem (.int a))
    (hs : substrSafe n ab = true) : Text.substrInRange a n = true := by
  simp only [substrSafe, Bool.and_eq_true] at hs
  have h := AVal.within_memNum hs.2 hb
  simp only [NumKind.norm_int] at h
  simp only [between, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Text.substrInRange, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.1, by omega⟩, hs.1⟩

theorem BinFn.mayIssue_sound (f : BinFn) {aa ab ar : AVal} {v w : Value} {nz : Bool}
    {sz : Option Nat} {k : Issue}
    (ha : aa.Mem v) (hb : ab.Mem w) (hr : ar.Mem (f.apply v w))
    (hnz : nz = true → ∀ j, w = f.divKind.val j → f.divKind.norm j ≠ 0)
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
        have hkk : kk ≠ .float := by
          rintro rfl
          cases v <;> cases w <;> simp [BinFn.apply, Value.numOf?] at hnum
        have := AVal.within_memNum hfits hr
        rw [show kk.norm i = i by cases kk <;> first | rfl | exact absurd rfl hkk] at this
        exact absurd this hn
      · simp
    · simp at hk
  all_goals (cases v <;> cases w <;> simp only [BinFn.issue, reduceCtorEq] at hk)
  case dateAdd.date.int i j =>
    have hr' := hr; simp only [BinFn.apply] at hr'
    exact rangeIssue_sound ha hr' hk
  case ilike.str.str a b | levenshtein.str.str a b =>
    split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
    subst hk; rename_i hn
    simp only [BinFn.mayIssue]
    split
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      exact absurd (by simp [AVal.isAscii_of_asciiOk ha hok.1, AVal.isAscii_of_asciiOk hb hok.2]) hn
    · simp
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
      simp only [NumKind.norm_float, NumKind.norm_int] at hi hj
      first
        | exact absurd ((atan2?_isSome_canon i j).symm.trans
            (BinFn.domainSafe_atan2 hs hi hj (FloatCode.canon_idem _) (FloatCode.canon_idem _))) hn
        | exact absurd ((logb?_isSome_canon i j).symm.trans
            (BinFn.domainSafe_logb hs hi hj (FloatCode.canon_idem _) (FloatCode.canon_idem _))) hn
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
    · rename_i hj hnz'
      have := hnz hnz' j rfl
      simp only [BinFn.divKind, NumKind.norm_int] at this
      exact absurd hj this
    · simp
  case fdiv.float.float i j | fmod.float.float i j =>
    simp only [BinFn.mayIssue, List.mem_append]
    split at hk
    · rename_i hj; simp only [Option.some.injEq] at hk; subst hk
      left; split
      · rename_i hnz'
        have := hnz hnz' j rfl
        simp only [BinFn.divKind, NumKind.norm_float] at this
        exact absurd hj this
      · simp
    · simp only [nanIssue] at hk
      split at hk <;> simp only [Option.some.injEq, reduceCtorEq] at hk
      subst hk
      rename_i hn
      right; simp [BinFn.mayNan_sound ha hb hn]
  case fadd.float.float i j | fsub.float.float i j | fmul.float.float i j | fdivIeee.float.float i j =>
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
        have := hj.1 l hl; simp only [NumKind.norm_int] at this; omega
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
          simp only [NumKind.norm_int] at hjn
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
              simp only [NumKind.norm_int] at hl hu
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
    (hx : x.eval row = .float c) : x.mayBe env fs ks (FloatCode.canon c) = true := by
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
      exact this c hx (by rw [NumKind.norm_float]; exact hj.symm)
  · by_cases hc : FloatCode.canon c = 0
    · right
      cases hnz : x.nonZero env fs ks .float with
      | false => rfl
      | true => exact absurd hc (Expr.nonZero_sound h hfs hks .float x hnz c hx)
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
    (hnz : nz = true → ∀ j, w = f.divKind.val j → f.divKind.norm j ≠ 0)
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
          exact .inr (Expr.mayInfBin_sound f a b (Expr.absD_sound h hfs hks a)
            (Expr.absD_sound h hfs hks b) hj hi)
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
        exact Expr.mayIssuesC_sound (Expr.refine_sound env c h hct)
          (FactsHold.append hfs (Expr.factsOf_sound c hct)) hw.1 hw.2 t p hp
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
  -- lists are empty (an optimizer may do that): the loose rows are both.
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

/-- Would IEEE make the aggregate of these values NaN, from numbers (#257)?
`AggFn.nanCase`'s cases, and a black box that raises on them (#326), reported
here as the same domain error. -/
def AggFn.makesNan : AggFn → List Value → Bool
  | .bbox n, vs => BlackBox.aggRaisesOn Boxes.Ambient.boxes n vs
  | f, vs => f.nanCase vs

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
    (has : ∀ c, .float c ∈ vs → a.has (FloatCode.canon c) = true) (h : f.makesNan vs = true) :
    f.mayNan a = true := by
  have hasP : .float FloatCode.posInf ∈ vs → a.has FloatCode.posInf = true := fun hm => by
    have := has _ hm; rwa [FloatCode.canon_posInf] at this
  have hasN : .float FloatCode.negInf ∈ vs → a.has FloatCode.negInf = true := fun hm => by
    have := has _ hm; rwa [FloatCode.canon_negInf] at this
  cases f
  case quantile c _ _ =>
    cases c <;> simp only [makesNan, AggFn.nanCase, mayNan, Bool.and_eq_true,
      List.contains_iff_mem, reduceCtorEq] at h ⊢
    all_goals first
      | exact ⟨hasP h.1.1, hasN h.1.2⟩
      | simp at h
  case var =>
    simp only [makesNan, AggFn.nanCase, mayNan, List.any_eq_true, Value.isInf_iff,
      Bool.or_eq_true] at h ⊢
    obtain ⟨v, hv, hv'⟩ := h
    rcases hv' with rfl | rfl
    · exact .inl (hasP hv)
    · exact .inr (hasN hv)
  all_goals simp only [makesNan, AggFn.nanCase, mayNan, Bool.and_eq_true,
    List.contains_iff_mem] at h ⊢
  all_goals first
    | exact ⟨hasP h.1, hasN h.2⟩
    | exact ⟨hasP h.1.1, hasN h.1.2⟩
    | exact h.imp hasP hasN
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
    have hex : ∃ v ∈ m.inputs grp, v.pairHasInf = true := by
      cases hf : m.fn <;> simp [hf, AggFn.paired] at hp <;> simpa [hf, AggFn.makesNan, AggFn.nanCase] using h
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
          simp only [Value.pairHasInf, Value.isInf_iff, Bool.or_eq_true] at hinf <;>
          rw [hxv] at hx <;> rw [hyv] at hy <;>
          simp only [AVal.mayInf, Bool.or_eq_true] <;>
          rcases hinf with (h1 | h1) | (h1 | h1) <;>
          simp_all [AVal.has_posInf_of_mem, AVal.has_negInf_of_mem]
      all_goals rfl
    | _ => rfl
  · simp only [hp, Bool.false_eq_true, ite_false]
    refine AggFn.mayNan_of_makesNan (fun c hc => ?_) h
    obtain ⟨row, hrow, hev⟩ := from_row _ hc
    have := hsound row hrow m.arg
    rw [hev] at this
    have := AVal.has_of_mem this
    rwa [NumKind.norm_float] at this

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
  m.fn.infAgg && (m.inputs grp).all finiteValue && Value.isInf (m.eval grp)

/-- May the aggregate, whose result `r` describes (`Measure.abs`), overflow?
Ruled out where `r` excludes `±∞`: a `SUM` or `AVG` of bounded values over at
most `2³²` rows (`floatBound`, from #85's error bounds). -/
def Measure.mayInf (m : Measure) (r : AVal) : Bool :=
  m.fn.infAgg && (r.has FloatCode.posInf || r.has FloatCode.negInf)

theorem Measure.mayInf_of_makesInf {m : Measure} {grp : Relation} {r : AVal}
    (hr : r.Mem (m.eval grp)) (h : m.makesInf grp = true) : m.mayInf r = true := by
  simp only [Measure.makesInf, Bool.and_eq_true] at h
  obtain ⟨⟨hf, _⟩, hinf⟩ := h
  simp only [Value.isInf_iff] at hinf
  simp only [Measure.mayInf, hf, Bool.true_and, Bool.or_eq_true]
  rcases hinf with h | h <;> rw [h] at hr <;> have := AVal.has_of_mem hr <;>
    rw [NumKind.norm_float] at this
  · rw [FloatCode.canon_posInf] at this; exact .inl this
  · rw [FloatCode.canon_negInf] at this; exact .inr this

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

/-- At most `Rel.sumRows` rows in any order's result of fewer than `2⁶³`
rows. -/
theorem Rel.le_sumRows_of {cat : Catalog} {r : Rel} {i : Relation} {n : Nat}
    (hi : r.OrderAllowed cat i) (hlt : i.length < 2 ^ 63) (hn : n ≤ i.length) :
    n ≤ r.sumRows := by
  have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
  rw [h63] at hlt
  unfold Rel.sumRows
  rw [h63]
  cases hm : r.maxRows with
  | none => simp only [Option.getD_none, Nat.le_min]; omega
  | some k =>
    have := Rel.maxRows_sound_all (cat := cat) hm hi
    simp only [Option.getD_some, Nat.le_min]; omega

theorem Rel.le_sumRows {cat : Catalog} {r : Rel} {n : Nat} (hlt : (r.eval cat).length < 2 ^ 63)
    (hn : n ≤ (r.eval cat).length) : n ≤ r.sumRows :=
  Rel.le_sumRows_of (r.eval_orderAllowed cat) hlt hn

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
  have from_row : ∀ v ∈ m.inputs grp, ∀ i, v.unscaled? = some i →
      ∃ k, (abs m.arg).MemNum k i ∧ k.norm i = i :=
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
      obtain ⟨_, ⟨b, hb, _⟩, _⟩ := from_row v hv i hi; simp [hn] at hb]
    have := m.sumMax_nonneg
    exact Measure.sumOk_of_le (by omega) (by omega)
  · rename_i lo hi k hb
    subst_vars
    have hk := hlen k rfl
    have hl := Nat.le_trans (Measure.inputs_length_le m grp) hk
    have hdec : (((max lo.natAbs hi.natAbs * k : Nat)) : Int) ≤ m.sumMax := of_decide_eq_true h
    have hbnd := intSum_bound ((max lo.natAbs hi.natAbs : Nat) : Int) (Int.natCast_nonneg _)
      (m.inputs grp) fun v hv i hi' => by
        obtain ⟨_, ⟨b, hb', hm, -⟩, hni⟩ := from_row v hv i hi'
        rw [hb] at hb'; cases hb'
        have h1 := hm.1 lo rfl; have h2 := hm.2 hi rfl
        rw [hni] at h1 h2
        omega
    have hmul : ((max lo.natAbs hi.natAbs : Nat) : Int) * ((m.inputs grp).length : Int) ≤
        ((max lo.natAbs hi.natAbs * k : Nat) : Int) := by
      rw [← Int.natCast_mul]; exact Int.ofNat_le.mpr (Nat.mul_le_mul_left _ hl)
    exact Measure.sumOk_of_le (by omega) (by omega)
  · simp at h

/-- The bound of `Measure.finiteAnyOrder`: `[lo, hi]` holds only finite codes,
at most `k ≤ 2³²` values, and `c · (k · M + k · 2⁵²)` stays within the largest
double, `M` the larger magnitude of `lo` and `hi`. A NaN's code lies above
`+∞`'s, so `hi < +∞` rules a NaN out (ruling 238, K1). -/
def finiteSumBound (c : Nat) (lo hi : Int) (k : Nat) : Bool :=
  decide (FloatCode.negInf < lo) && decide (hi < FloatCode.posInf) && decide (k ≤ 2 ^ 32) &&
    decide (c * (k * max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs + k * 2 ^ 52)
      ≤ FloatCode.maxMag)

/-- **A double `SUM` or `AVG` no summation order overflows** (#1787 item 4,
rulings 238 and 242): its argument's values are doubles whose canonical codes
lie in a finite `[lo, hi]`, a group has at most `k` rows (`n`, from
`Rel.maxRows`), and `finiteSumBound` holds with `c = 2` for a sum and `4` for
a mean. Then every sum and mean a `sum_order` behaviour allows has a finite
canonical code (`Measure.finiteAnyOrder_sound`, `MarginSound.lean`), so the
writer's check against `±∞` cannot fire. It reads the bound `Measure.sumFits`
reads, with a margin for an order that rounds at every step: `crBound`, which
`Measure.mayInf` reads, has none (ruling 238). -/
def Measure.finiteAnyOrder (m : Measure) (abs : Expr → AVal) (n : Option Nat) : Bool :=
  match m.fn, (abs m.arg).int, n with
  | .fsum, some ⟨some lo, some hi⟩, some k => (abs m.arg).kindOnly .float && finiteSumBound 2 lo hi k
  | .avg, some ⟨some lo, some hi⟩, some k => (abs m.arg).kindOnly .float && finiteSumBound 4 lo hi k
  | _, _, _ => false

/-! ## Conditions that read some of a join's inputs (#1484, R3)

An engine may evaluate a part of a filter or join condition on one input of
a join before any pair exists: DuckDB pushes a one-side filter into its
input, and a hash join computes a key such as `10 // a.x` on every row of its
side. The rows it runs on are that input's rows, whatever the other inputs
hold, an empty one included. `Rel.ViewAllowed` gives those rows: the inputs
the subexpression reads, the others padded with NULLs so that its column
numbers stay. A left join counts as a cross join here: a NULL-rejecting
filter above it lets an engine make it inner. -/

/-- Is `r` a pair of inputs, a cross or a join? -/
def Rel.isPair : Rel → Bool
  | .cross _ _ | .join _ _ _ _ => true
  | _ => false

/-- The rows a subexpression reading the columns `cols` of `r` may run on:
below `r`'s crosses and joins, the rows of the inputs it reads, in any order
the reference allows, the other inputs' columns NULL. -/
def Rel.ViewAllowed (cat : Catalog) (cols : List Nat) : Rel → Relation → Prop
  | .cross a b, out | .join a b _ _, out =>
    let n := a.arity cat
    if cols.all (· < n) then
      ∃ x, a.ViewAllowed cat cols x ∧ out = x.map (· ++ List.replicate (b.arity cat) .null)
    else if cols.all (n ≤ ·) then
      ∃ y, b.ViewAllowed cat (cols.map (· - n)) y ∧ out = y.map (List.replicate n .null ++ ·)
    else
      ∃ x y, a.ViewAllowed cat (cols.filter (· < n)) x ∧
        b.ViewAllowed cat ((cols.filter (n ≤ ·)).map (· - n)) y ∧ out = crossRows x y
  | r, out => r.OrderAllowed cat out

/-- The abstract values of `Rel.ViewAllowed`'s rows: the inputs' own, a padded
input's anything. -/
def Rel.viewEnv (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (cols : List Nat) : Rel → List AVal
  | .cross a b | .join a b _ _ =>
    let n := a.arity cat
    if cols.all (· < n) then
      a.viewEnv cat A F T cols ++ List.replicate (b.arity cat) AVal.top
    else if cols.all (n ≤ ·) then
      List.replicate n AVal.top ++ b.viewEnv cat A F T (cols.map (· - n))
    else
      a.viewEnv cat A F T (cols.filter (· < n)) ++
        b.viewEnv cat A F T ((cols.filter (n ≤ ·)).map (· - n))
  | r => r.aeval cat A F T true

/-- The facts of `Rel.ViewAllowed`'s rows: the inputs' own, none of a padded
input. -/
def Rel.viewFacts (cat : Catalog) (F : String → List Fact) (T : WindowKeys) (cols : List Nat) :
    Rel → List Fact
  | .cross a b | .join a b _ _ =>
    let n := a.arity cat
    if cols.all (· < n) then
      (a.viewFacts cat F T cols).filter (·.inRange n)
    else if cols.all (n ≤ ·) then
      (b.viewFacts cat F T (cols.map (· - n))).map (·.shift n)
    else
      (a.viewFacts cat F T (cols.filter (· < n))).filter (·.inRange n) ++
        (b.viewFacts cat F T ((cols.filter (n ≤ ·)).map (· - n))).map (·.shift n)
  | r => r.facts cat F T

theorem Rel.viewEnv_length {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
    {T : WindowKeys} (r : Rel) :
    ∀ {cols : List Nat}, r.WF cat → (r.viewEnv cat A F T cols).length = r.arity cat := by
  induction r with
  | cross a b iha ihb =>
    intro cols hwf
    simp only [viewEnv, arity]
    split
    · simp [iha hwf.1]
    · split
      · simp [ihb hwf.2]
      · simp [iha hwf.1, ihb hwf.2]
  | join a b ty on iha ihb =>
    intro cols hwf
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    cases ty <;> simp only [viewEnv, arity] <;> split <;> (try split) <;>
      simp [iha ha, ihb hb]
  | _ => intro cols hwf; simp only [viewEnv]; exact aeval_length hwf

/-- **The views are described soundly**: each row of `Rel.ViewAllowed` has
`r`'s arity and meets `Rel.viewEnv` and `Rel.viewFacts`. -/
theorem Rel.view_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ (r : Rel) {cols : List Nat} {out : Relation}, r.WF cat → r.SmallAll cat →
      r.ViewAllowed cat cols out → ∀ row ∈ out, row.length = r.arity cat ∧
        EnvMem (r.viewEnv cat A F T cols) row ∧ FactsHold (r.viewFacts cat F T cols) row := by
  intro r
  induction r with
  | cross a b iha ihb =>
    intro cols out hwf hsm h row hr
    exact pair hwf.1 hwf.2 hsm.1 hsm.2 (fun h => iha hwf.1 hsm.1 h) (fun h => ihb hwf.2 hsm.2 h)
      h row hr
  | join a b ty on iha ihb =>
    intro cols out hwf hsm h row hr
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    have := pair ha hb hsm.1 hsm.2 (fun h => iha ha hsm.1 h) (fun h => ihb hb hsm.2 h) h row hr
    cases ty <;> exact this
  | _ =>
    intro cols out hwf hsm h row hr
    simp only [ViewAllowed, viewEnv, viewFacts] at h ⊢
    exact ⟨orderAllowed_arity hcat hwf h row hr,
      aeval_sound_allSz hcat hA hF hT (sz := true) hwf (fun _ => hsm) h row hr,
      facts_sound_all hcat hF hT hwf h row hr⟩
where
  /-- A cross or join, from its inputs' views. -/
  pair {a b : Rel} {cols : List Nat} {out : Relation} (ha : a.WF cat) (hb : b.WF cat)
      (hsa : a.SmallAll cat) (hsb : b.SmallAll cat)
      (iha : ∀ {cols out}, a.ViewAllowed cat cols out → ∀ row ∈ out, row.length = a.arity cat ∧
        EnvMem (a.viewEnv cat A F T cols) row ∧ FactsHold (a.viewFacts cat F T cols) row)
      (ihb : ∀ {cols out}, b.ViewAllowed cat cols out → ∀ row ∈ out, row.length = b.arity cat ∧
        EnvMem (b.viewEnv cat A F T cols) row ∧ FactsHold (b.viewFacts cat F T cols) row)
      (h : (Rel.cross a b).ViewAllowed cat cols out) :
      ∀ row ∈ out, row.length = (Rel.cross a b).arity cat ∧
        EnvMem ((Rel.cross a b).viewEnv cat A F T cols) row ∧
        FactsHold ((Rel.cross a b).viewFacts cat F T cols) row := by
    intro row hr
    simp only [ViewAllowed, viewEnv, viewFacts, arity] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hl, he, hf⟩ := iha hx u hu
      refine ⟨by simp [hl], he.append (EnvMem.replicate _ _) (by rw [viewEnv_length a ha, hl]),
        hf.prefix fun i hi => getD_append_left' (hl ▸ hi)⟩
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i hc'
        simp only [hc', ↓reduceIte]
        obtain ⟨y, hy, rfl⟩ := h
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
        obtain ⟨hl, he, hf⟩ := ihb hy v hv
        refine ⟨by simp [hl], (EnvMem.replicate _ _).append he (by simp),
          hf.shift fun i => ?_⟩
        have := getD_append_right' (x := List.replicate (a.arity cat) Value.null) (y := v) i
        simpa using this
      · rename_i hc'
        simp only [hc', Bool.false_eq_true, ↓reduceIte]
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hr
        obtain ⟨hlu, heu, hfu⟩ := iha hx u hu
        obtain ⟨hlv, hev, hfv⟩ := ihb hy v hv
        refine ⟨by simp [hlu, hlv], heu.append hev (by rw [viewEnv_length a ha, hlu]),
          (hfu.prefix fun i hi => getD_append_left' (hlu ▸ hi)).append
            (hfv.shift fun i => hlu ▸ getD_append_right' i)⟩

/-- `e`, or a subexpression it always evaluates (`Expr.eager`: all but a
`CASE`'s branches and a lambda's body, as in `Expr.issues`), raises on a row of
a view of `r`. A `CASE` counts as a whole, so its guard still protects its
branches. -/
def Rel.ViewIssue (cat : Catalog) (r : Rel) (e : Expr) (p : Issue × Expr) : Prop :=
  ∃ d ∈ e :: e.eager, ∃ out, r.ViewAllowed cat d.cols out ∧ ∃ row ∈ out, p ∈ d.issues row

/-- The issues of `e`'s eager subexpressions on the views of a cross or a
join `r`; elsewhere a view is `r` itself, whose issues the expression's own
pass reports (`Expr.issues_eager`). -/
def Rel.viewIssues (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (r : Rel) (e : Expr) : List (Issue × Expr) :=
  if r.isPair then
    (e :: e.eager).flatMap fun d =>
      d.mayIssues (r.viewEnv cat A F T d.cols) (r.viewFacts cat F T d.cols)
  else []

/-- A view issue is among `Rel.viewIssues`, or one of `e`'s own on a row of `r`. -/
theorem Rel.viewIssues_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} {e : Expr} {p : Issue × Expr} (hwf : r.WF cat) (hsm : r.SmallAll cat)
    (h : r.ViewIssue cat e p) :
    p ∈ r.viewIssues cat A F T e ∨ ∃ out, r.OrderAllowed cat out ∧ ∃ row ∈ out, p ∈ e.issues row := by
  obtain ⟨d, hd, out, hv, row, hrow, hp⟩ := h
  cases hpair : r.isPair
  · have he : p ∈ e.issues row := by
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hp
      · exact Expr.issues_eager hd hp
    refine .inr ⟨out, ?_, row, hrow, he⟩
    cases r <;> simp_all [Rel.isPair, Rel.ViewAllowed]
  · obtain ⟨-, he, hf⟩ := Rel.view_sound hcat hA hF hT r hwf hsm hv row hrow
    simp only [Rel.viewIssues, hpair, ↓reduceIte, List.mem_flatMap]
    exact .inl ⟨d, hd, Expr.mayIssues_sound he hf (by simp [KsHold]) d p hp⟩

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
    r.mayIssues cat A F T true ++ c.mayIssues (r.loose.aeval cat A F T true) (r.loose.facts cat F T) ++
      r.loose.viewIssues cat A F T c
  | u, .project r es =>
    let s := if u then r.loose else r
    r.mayIssues cat A F T u ++ es.flatMap (·.mayIssues (s.aeval cat A F T true) (s.facts cat F T)) ++
      (if u then es.flatMap (r.loose.viewIssues cat A F T) else [])
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
      on.mayIssues (ab.aeval cat A F T true) (ab.facts cat F T) ++ ab.viewIssues cat A F T on
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
      ms.filterMap (fun m =>
        if m.mayInf (m.abs (r.aeval cat A F T true) (r.facts cat F T) false (some r.sumRows))
        then some (.infinite, m.arg) else none) ++
      (if u then (gs ++ ms.flatMap Measure.exprs).flatMap (r.loose.viewIssues cat A F T) else [])

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
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h))
    · have hl := loose_wf hwf.1
      exact .inl (.inr (Expr.mayIssues_sound (aeval_sound hcat hA hF hT hl (fun _ => Rel.Small.loose (r := r) hsm) row hrow)
        (facts_sound hcat hF hT hl row hrow) (KsHold.nil row) c p hp))
  | u, .project r es, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h))
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      have hsm' : (if u then r.loose else r).Small cat := by
        cases u
        · exact hsm
        · exact Rel.Small.loose (r := r) hsm
      exact .inl (.inr ⟨e, he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs (fun _ => hsm') row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩)
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
    · exact .inl (.inl (.inl (mayIssues_sound hcat hA hF hT ha hsm.1 p h)))
    · exact .inl (.inl (.inr (mayIssues_sound hcat hA hF hT hb hsm.2 p h)))
    · exact .inl (.inr (condIssue_sound hcat hA hF hT ha hb hsm.1 hsm.2 hx hy hp))
  | _, .semi a b _ on, hwf, hsm, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (.inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm.1 p h)))
    · exact .inl (.inl (.inr (mayIssues_sound hcat hA hF hT hwf.2.1 hsm.2 p h)))
    · exact .inl (.inr (condIssue_sound hcat hA hF hT hwf.1 hwf.2.1 hsm.1 hsm.2 hx hy hp))
  | u, .aggregate r gs ms, hwf, ⟨hlt, hsm⟩, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap, List.mem_filterMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩ | ⟨m, hm, hf, rfl, grp, hgrp, hov⟩ |
      ⟨m, hm, rfl, grp, hgrp, hnan⟩ | ⟨m, hm, rfl, grp, hgrp, hinf⟩
    · exact .inl (.inl (.inl (.inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 hsm p h)))))
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      have hsm' : (if u then r.loose else r).Small cat := by
        cases u
        · exact hsm
        · exact Rel.Small.loose (r := r) hsm
      exact .inl (.inl (.inl (.inl (.inr ⟨e, by simpa using he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs (fun _ => hsm') row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩))))
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
      exact .inl (.inl (.inl (.inr ⟨m, hm, by simp [hf, hfits]⟩)))
    · have hsound : ∀ y ∈ grp, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := by
        intro y hy e
        have hyr := mem_of_mem_aggGroups hgrp hy
        exact Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr)
          (facts_sound hcat hF hT hwf.1 y hyr) (KsHold.nil y) e
      exact .inl (.inl (.inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩))
    · have hres := Measure.abs_sound (grp := grp)
        (fun y hy => by
          have hyr := mem_of_mem_aggGroups hgrp hy
          exact ⟨aeval_sound hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) y hyr,
            facts_sound hcat hF hT hwf.1 y hyr⟩) m false (by simp) (some r.sumRows)
        (fun k hk => by cases hk; exact Rel.le_sumRows hlt (length_le_of_mem_aggGroups hgrp))
      exact .inl (.inr ⟨m, hm, by simp [Measure.mayInf_of_makesInf hres hinf]⟩)

/-! ## Issues on every order of the ties (#1484)

`Rel.HasIssue` reads the rows `Rel.eval` gives, one order of the ties. An
engine that breaks a window's ties another way feeds later expressions other
rows. `Rel.HasIssueAll` states the same model over every result the reference
allows for each input (`Rel.OrderAllowed`), `Rel.eval`'s among them
(`Rel.hasIssueAll_of_hasIssue`), and `Rel.mayIssues_sound_all` proves that
`Rel.mayIssues` reports each such issue: the abstract evaluation is
order-blind. -/

/-- **Where issues happen, on every order**: `Rel.HasIssue` with each input's
rows from any result the reference allows for it. -/
def Rel.HasIssueAll (cat : Catalog) : Bool → Rel → Issue × Expr → Prop
  | _, .read _, _ | _, .values _ _, _ => False
  | _, .filter r c, p => r.HasIssueAll cat true p ∨
      (∃ i, r.loose.OrderAllowed cat i ∧ ∃ row ∈ i, p ∈ c.issues row) ∨ r.loose.ViewIssue cat c p
  | u, .project r es, p => r.HasIssueAll cat u p ∨
      (∃ i, (if u then r.loose else r).OrderAllowed cat i ∧ ∃ row ∈ i, ∃ e ∈ es, p ∈ e.issues row) ∨
      (u = true ∧ ∃ e ∈ es, r.loose.ViewIssue cat e p)
  | u, .emit r _, p | u, .fetch r _ _, p | u, .orderBy r _, p
  | u, .distinct r, p | u, .unnest r _, p => r.HasIssueAll cat u p
  | u, .window r _ _ fns, p => r.HasIssueAll cat u p ∨ ∃ i, r.OrderAllowed cat i ∧
      ((∃ m ∈ WinFn.aggs fns, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ i) ∧ frame.length ≤ i.length ∧
          m.sumOk (intSum (m.inputs frame)) = false) ∨
      (∃ m ∈ WinFn.aggs fns, p = (.domain, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ i) ∧ m.fn.makesNan (m.inputs frame) = true) ∨
      ∃ m ∈ WinFn.aggs fns, p = (.infinite, m.arg) ∧
        ∃ frame : Relation, (∀ y ∈ frame, y ∈ i) ∧ frame.length ≤ i.length ∧
          m.makesInf frame = true)
  | u, .cross a b, p | u, .unionAll a b, p => a.HasIssueAll cat u p ∨ b.HasIssueAll cat u p
  | _, .join a b _ on, p | _, .semi a b _ on, p =>
      a.HasIssueAll cat true p ∨ b.HasIssueAll cat true p ∨
      (∃ xs, a.loose.OrderAllowed cat xs ∧ ∃ ys, b.loose.OrderAllowed cat ys ∧
        ∃ x ∈ xs, ∃ y ∈ ys, p ∈ on.issues (x ++ y)) ∨
      (Rel.cross a.loose b.loose).ViewIssue cat on p
  | u, .aggregate r gs ms, p => r.HasIssueAll cat u p ∨
      (∃ i, (if u then r.loose else r).OrderAllowed cat i ∧ ∃ row ∈ i,
        ∃ e ∈ gs ++ ms.flatMap Measure.exprs, p ∈ e.issues row) ∨
      (∃ i, r.OrderAllowed cat i ∧
        ((∃ m ∈ ms, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
          ∃ grp ∈ aggGroups gs i, m.sumOk (intSum (m.inputs grp)) = false) ∨
        (∃ m ∈ ms, p = (.domain, m.arg) ∧
          ∃ grp ∈ aggGroups gs i, m.fn.makesNan (m.inputs grp) = true) ∨
        ∃ m ∈ ms, p = (.infinite, m.arg) ∧
          ∃ grp ∈ aggGroups gs i, m.makesInf grp = true)) ∨
      (u = true ∧ ∃ e ∈ gs ++ ms.flatMap Measure.exprs, r.loose.ViewIssue cat e p)

/-- `Rel.HasIssueAll` is the stronger specification: `Rel.eval`'s result is
one order the reference allows. -/
theorem Rel.hasIssueAll_of_hasIssue {cat : Catalog} :
    ∀ {u : Bool} {r : Rel} {p : Issue × Expr}, r.HasIssue cat u p → r.HasIssueAll cat u p
  | _, .read _, _, h | _, .values _ _, _, h => h.elim
  | _, .filter r _, _, h => by
    rcases h with h | ⟨row, hrow, hp⟩
    · exact .inl (hasIssueAll_of_hasIssue (r := r) h)
    · exact .inr (.inl ⟨_, r.loose.eval_orderAllowed cat, row, hrow, hp⟩)
  | _, .project r _, _, h => by
    rcases h with h | ⟨row, hrow, e, he, hp⟩
    · exact .inl (hasIssueAll_of_hasIssue (r := r) h)
    · exact .inr (.inl ⟨_, Rel.eval_orderAllowed cat _, row, hrow, e, he, hp⟩)
  | _, .emit r _, _, h | _, .fetch r _ _, _, h | _, .orderBy r _, _, h
  | _, .distinct r, _, h | _, .unnest r _, _, h => hasIssueAll_of_hasIssue (r := r) h
  | _, .window r _ _ _, _, h => by
    rcases h with h | h | h | h
    · exact .inl (hasIssueAll_of_hasIssue (r := r) h)
    · exact .inr ⟨_, r.eval_orderAllowed cat, .inl h⟩
    · exact .inr ⟨_, r.eval_orderAllowed cat, .inr (.inl h)⟩
    · exact .inr ⟨_, r.eval_orderAllowed cat, .inr (.inr h)⟩
  | _, .cross a b, _, h | _, .unionAll a b, _, h => by
    rcases h with h | h
    · exact .inl (hasIssueAll_of_hasIssue (r := a) h)
    · exact .inr (hasIssueAll_of_hasIssue (r := b) h)
  | _, .join a b _ _, _, h | _, .semi a b _ _, _, h => by
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (hasIssueAll_of_hasIssue (r := a) h)
    · exact .inr (.inl (hasIssueAll_of_hasIssue (r := b) h))
    · exact .inr (.inr (.inl ⟨_, a.loose.eval_orderAllowed cat, _, b.loose.eval_orderAllowed cat,
        x, hx, y, hy, hp⟩))
  | _, .aggregate r _ _, _, h => by
    rcases h with h | ⟨row, hrow, e, he, hp⟩ | h | h | h
    · exact .inl (hasIssueAll_of_hasIssue (r := r) h)
    · exact .inr (.inl ⟨_, Rel.eval_orderAllowed cat _, row, hrow, e, he, hp⟩)
    · exact .inr (.inr (.inl ⟨_, r.eval_orderAllowed cat, .inl h⟩))
    · exact .inr (.inr (.inl ⟨_, r.eval_orderAllowed cat, .inr (.inl h)⟩))
    · exact .inr (.inr (.inl ⟨_, r.eval_orderAllowed cat, .inr (.inr h)⟩))

/-- `Rel.loose` keeps every window as it is, so it keeps the size hypothesis
on every order. -/
theorem Rel.SmallAll.loose {cat : Catalog} : ∀ {r : Rel}, r.SmallAll cat → r.loose.SmallAll cat
  | .read _, h | .values _ _, h => h
  | .filter r _, h | .orderBy r _, h | .distinct r, h => Rel.SmallAll.loose (r := r) h
  | .project r _, h | .emit r _, h => Rel.SmallAll.loose (r := r) h
  | .cross a b, h | .unionAll a b, h =>
    ⟨Rel.SmallAll.loose (r := a) h.1, Rel.SmallAll.loose (r := b) h.2⟩
  | .join a b ty _, h => by
    cases ty <;> exact ⟨Rel.SmallAll.loose (r := a) h.1, Rel.SmallAll.loose (r := b) h.2⟩
  | .semi a _ _ _, h => Rel.SmallAll.loose (r := a) h.1
  | .fetch _ _ _, h | .window _ _ _ _, h | .aggregate _ _ _, h => h
  | .unnest r _, h => ⟨Rel.SmallAll.loose (r := r) h, Rel.SmallAll.loose (r := r) h⟩

theorem Rel.SmallAll.ite {cat : Catalog} {r : Rel} (u : Bool) (h : r.SmallAll cat) :
    (if u then r.loose else r).SmallAll cat := by
  cases u
  · exact h
  · exact h.loose

omit [Boxes.Ambient] in
theorem Rel.WF.ite {cat : Catalog} {r : Rel} (u : Bool) (h : r.WF cat) :
    (if u then r.loose else r).WF cat := by
  cases u
  · exact h
  · exact Rel.loose_wf h

/-- Join and semi-join conditions run on pairs of loose input rows, of any
orders. -/
theorem condIssue_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {a b : Rel} {on : Expr} {p : Issue × Expr} {xs ys : Relation} {x y : Row} (ha : a.WF cat)
    (hb : b.WF cat) (hsa : a.SmallAll cat) (hsb : b.SmallAll cat)
    (hxs : a.loose.OrderAllowed cat xs) (hys : b.loose.OrderAllowed cat ys)
    (hx : x ∈ xs) (hy : y ∈ ys) (hp : p ∈ on.issues (x ++ y)) :
    p ∈ on.mayIssues ((Rel.cross a.loose b.loose).aeval cat A F T true)
      ((Rel.cross a.loose b.loose).facts cat F T) := by
  have hab : (Rel.cross a.loose b.loose).WF cat := ⟨Rel.loose_wf ha, Rel.loose_wf hb⟩
  have hc : (Rel.cross a.loose b.loose).OrderAllowed cat (crossRows xs ys) :=
    ⟨xs, ys, hxs, hys, .refl _⟩
  have hrow : x ++ y ∈ crossRows xs ys := mem_crossRows.mpr ⟨x, hx, y, hy, rfl⟩
  exact Expr.mayIssues_sound
    (Rel.aeval_sound_allSz hcat hA hF hT (sz := true) hab (fun _ => ⟨hsa.loose, hsb.loose⟩) hc _ hrow)
    (Rel.facts_sound_all hcat hF hT hab hc _ hrow) (KsHold.nil _) on p hp

/-- **Soundness on every order** (#1484): every issue that can happen on any
order of the ties the reference allows is among `Rel.mayIssues`, for a
well-formed plan whose windows and aggregates read fewer rows than the size
hypothesis allows on every order (`Rel.SmallAll`). So an empty list proves
the plan runs without errors on every engine's order. -/
theorem Rel.mayIssues_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {u : Bool} {r : Rel}, r.WF cat → r.SmallAll cat → ∀ p, r.HasIssueAll cat u p →
      p ∈ r.mayIssues cat A F T u
  | _, .read _, _, _, _, h | _, .values _ _, _, _, _, h => h.elim
  | _, .filter r c, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append]
    have hl := loose_wf hwf.1
    have hsl := Rel.SmallAll.loose (r := r) hsm
    have own : ∀ {i}, r.loose.OrderAllowed cat i → ∀ row ∈ i, p ∈ c.issues row →
        p ∈ c.mayIssues (r.loose.aeval cat A F T true) (r.loose.facts cat F T) :=
      fun hi row hrow hp => Expr.mayIssues_sound
        (aeval_sound_allSz hcat hA hF hT (sz := true) hl (fun _ => hsl) hi row hrow)
        (facts_sound_all hcat hF hT hl hi row hrow) (KsHold.nil row) c p hp
    rcases h with h | ⟨i, hi, row, hrow, hp⟩ | hv
    · exact .inl (.inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm p h))
    · exact .inl (.inr (own hi row hrow hp))
    · rcases Rel.viewIssues_sound hcat hA hF hT hl hsl hv with h | ⟨i, hi, row, hrow, hp⟩
      · exact .inr h
      · exact .inl (.inr (own hi row hrow hp))
  | u, .project r es, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap]
    have hs := hwf.1.ite u
    have own : ∀ {i}, (if u then r.loose else r).OrderAllowed cat i → ∀ row ∈ i, ∀ e ∈ es,
        p ∈ e.issues row → ∃ e ∈ es, p ∈ e.mayIssues
          ((if u then r.loose else r).aeval cat A F T true) ((if u then r.loose else r).facts cat F T) :=
      fun hi row hrow e he hp => ⟨e, he, Expr.mayIssues_sound
        (aeval_sound_allSz hcat hA hF hT (sz := true) hs (fun _ => Rel.SmallAll.ite (r := r) u hsm)
          hi row hrow)
        (facts_sound_all hcat hF hT hs hi row hrow) (KsHold.nil row) e p hp⟩
    rcases h with h | ⟨i, hi, row, hrow, e, he, hp⟩ | ⟨rfl, e, he, hv⟩
    · exact .inl (.inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm p h))
    · exact .inl (.inr (own hi row hrow e he hp))
    · rcases Rel.viewIssues_sound hcat hA hF hT (loose_wf hwf.1) (Rel.SmallAll.loose (r := r) hsm) hv
        with h | ⟨i, hi, row, hrow, hp⟩
      · exact .inr (by simp only [ite_true, List.mem_flatMap]; exact ⟨e, he, h⟩)
      · exact .inl (.inr (own hi row hrow e he hp))
  | _, .emit r _, hwf, hsm, p, h => mayIssues_sound_all hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .fetch r _ _, hwf, hsm, p, h => mayIssues_sound_all hcat hA hF hT (r := r) hwf hsm p h
  | _, .window r _ _ _, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨i, hi, h⟩
    · exact .inl (.inl (.inl (mayIssues_sound_all hcat hA hF hT (r := r) hwf.1 hsm.2 p h)))
    have habs : ∀ y ∈ i, ∀ e : Expr,
        (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := fun y hyr e =>
      Expr.absD_sound (aeval_sound_allSz hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm.2) hi y hyr)
        (facts_sound_all hcat hF hT hwf.1 hi y hyr) (KsHold.nil y) e
    have hlt : i.length < 2 ^ 63 := Nat.lt_trans (hsm.1 i hi) (by decide)
    rcases h with ⟨m, hm, hf, rfl, frame, hframe, hlen, hov⟩ |
      ⟨m, hm, rfl, frame, hframe, hnan⟩ | ⟨m, hm, rfl, frame, hframe, hlen, hinf⟩
    · have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows)
        · rfl
        · have := Measure.sumFits_sound (fun y hy => habs y (hframe y hy) m.arg)
            (fun k hk => by cases hk; exact Rel.le_sumRows_of hi hlt hlen) hfit
          rw [hov] at this; cases this
      exact .inl (.inl (.inr ⟨m, hm, by simp [hf, hfits]⟩))
    · have hsound : ∀ y ∈ frame, ∀ e : Expr,
          (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) :=
        fun y hy e => habs y (hframe y hy) e
      exact .inl (.inr ⟨m, hm, by simp [Measure.mayNan_of_makesNan hsound hnan]⟩)
    · have hres := Measure.abs_sound (grp := frame)
        (fun y hy => ⟨aeval_sound_allSz hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm.2) hi y
            (hframe y hy),
          facts_sound_all hcat hF hT hwf.1 hi y (hframe y hy)⟩) m false (by simp) (some r.sumRows)
        (fun k hk => by cases hk; exact Rel.le_sumRows_of hi hlt hlen)
      exact .inr ⟨m, hm, by simp [Measure.mayInf_of_makesInf hres hinf]⟩
  | _, .orderBy r _, hwf, hsm, p, h => mayIssues_sound_all hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .distinct r, hwf, hsm, p, h => mayIssues_sound_all hcat hA hF hT (r := r) hwf hsm p h
  | _, .unnest r _, hwf, hsm, p, h => mayIssues_sound_all hcat hA hF hT (r := r) hwf.1 hsm p h
  | _, .cross a b, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm.1 p h)
    · exact .inr (mayIssues_sound_all hcat hA hF hT hwf.2 hsm.2 p h)
  | _, .unionAll a b, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm.1 p h)
    · exact .inr (mayIssues_sound_all hcat hA hF hT hwf.2.1 hsm.2 p h)
  | _, .join a b ty on, hwf, hsm, p, h => by
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨xs, hxs, ys, hys, x, hx, y, hy, hp⟩ | hv
    · exact .inl (.inl (.inl (mayIssues_sound_all hcat hA hF hT ha hsm.1 p h)))
    · exact .inl (.inl (.inr (mayIssues_sound_all hcat hA hF hT hb hsm.2 p h)))
    · exact .inl (.inr (condIssue_sound_all hcat hA hF hT ha hb hsm.1 hsm.2 hxs hys hx hy hp))
    · rcases Rel.viewIssues_sound (r := Rel.cross a.loose b.loose) hcat hA hF hT ⟨Rel.loose_wf ha, Rel.loose_wf hb⟩
          ⟨hsm.1.loose, hsm.2.loose⟩ hv with h | ⟨out, ⟨xs, ys, hxs, hys, hperm⟩, row, hrow, hp⟩
      · exact .inr h
      · obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp (hperm.mem_iff.mp hrow)
        exact .inl (.inr (condIssue_sound_all hcat hA hF hT ha hb hsm.1 hsm.2 hxs hys hx hy hp))
  | _, .semi a b _ on, hwf, hsm, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨xs, hxs, ys, hys, x, hx, y, hy, hp⟩ | hv
    · exact .inl (.inl (.inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm.1 p h)))
    · exact .inl (.inl (.inr (mayIssues_sound_all hcat hA hF hT hwf.2.1 hsm.2 p h)))
    · exact .inl (.inr (condIssue_sound_all hcat hA hF hT hwf.1 hwf.2.1 hsm.1 hsm.2 hxs hys hx hy hp))
    · rcases Rel.viewIssues_sound (r := Rel.cross a.loose b.loose) hcat hA hF hT ⟨Rel.loose_wf hwf.1, Rel.loose_wf hwf.2.1⟩
          ⟨hsm.1.loose, hsm.2.loose⟩ hv with h | ⟨out, ⟨xs, ys, hxs, hys, hperm⟩, row, hrow, hp⟩
      · exact .inr h
      · obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp (hperm.mem_iff.mp hrow)
        exact .inl (.inr (condIssue_sound_all hcat hA hF hT hwf.1 hwf.2.1 hsm.1 hsm.2 hxs hys hx hy hp))
  | u, .aggregate r gs ms, hwf, ⟨hlt, hsm⟩, p, h => by
    simp only [HasIssueAll] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap, List.mem_filterMap]
    have hs := hwf.1.ite u
    have own : ∀ {i}, (if u then r.loose else r).OrderAllowed cat i → ∀ row ∈ i,
        ∀ e ∈ gs ++ ms.flatMap Measure.exprs, p ∈ e.issues row →
        p ∈ (gs ++ ms.flatMap Measure.exprs).flatMap (·.mayIssues
          ((if u then r.loose else r).aeval cat A F T true) ((if u then r.loose else r).facts cat F T)) :=
      fun hi row hrow e he hp => List.mem_flatMap.mpr ⟨e, he, Expr.mayIssues_sound
        (aeval_sound_allSz hcat hA hF hT (sz := true) hs (fun _ => Rel.SmallAll.ite (r := r) u hsm)
          hi row hrow)
        (facts_sound_all hcat hF hT hs hi row hrow) (KsHold.nil row) e p hp⟩
    rcases h with h | ⟨i, hi, row, hrow, e, he, hp⟩ | ⟨i, hi, h⟩ | ⟨rfl, e, he, hv⟩
    · exact .inl (.inl (.inl (.inl (.inl (mayIssues_sound_all hcat hA hF hT hwf.1 hsm p h)))))
    · exact .inl (.inl (.inl (.inl (.inr (by
        have := own hi row hrow e he hp
        simpa only [List.mem_flatMap, List.mem_append] using this)))))
    rotate_left
    · rcases Rel.viewIssues_sound hcat hA hF hT (loose_wf hwf.1) (Rel.SmallAll.loose (r := r) hsm) hv
        with h | ⟨i, hi, row, hrow, hp⟩
      · exact .inr (by simp only [ite_true, List.mem_flatMap]; exact ⟨e, he, h⟩)
      · exact .inl (.inl (.inl (.inl (.inr (by
        have := own hi row hrow e he hp
        simpa only [List.mem_flatMap, List.mem_append] using this)))))
    have habs : ∀ y ∈ i, ∀ e : Expr,
        (e.absD (r.aeval cat A F T true) (r.facts cat F T)).Mem (e.eval y) := fun y hyr e =>
      Expr.absD_sound (aeval_sound_allSz hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) hi y hyr)
        (facts_sound_all hcat hF hT hwf.1 hi y hyr) (KsHold.nil y) e
    have hlti := hlt i hi
    rcases h with ⟨m, hm, hf, rfl, grp, hgrp, hov⟩ |
      ⟨m, hm, rfl, grp, hgrp, hnan⟩ | ⟨m, hm, rfl, grp, hgrp, hinf⟩
    · have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (some r.sumRows)
        · rfl
        · have := Measure.sumFits_sound (grp := grp)
            (fun y hy => habs y (mem_of_mem_aggGroups hgrp hy) m.arg)
            (fun k hk => by
              cases hk; exact Rel.le_sumRows_of hi hlti (length_le_of_mem_aggGroups hgrp)) hfit
          rw [hov] at this; cases this
      exact .inl (.inl (.inl (.inr ⟨m, hm, by simp [hf, hfits]⟩)))
    · exact .inl (.inl (.inr ⟨m, hm, by
        simp [Measure.mayNan_of_makesNan (fun y hy e => habs y (mem_of_mem_aggGroups hgrp hy) e)
          hnan]⟩))
    · have hres := Measure.abs_sound (grp := grp)
        (fun y hy => ⟨aeval_sound_allSz hcat hA hF hT (sz := true) hwf.1 (fun _ => hsm) hi y
            (mem_of_mem_aggGroups hgrp hy),
          facts_sound_all hcat hF hT hwf.1 hi y (mem_of_mem_aggGroups hgrp hy)⟩) m false (by simp)
        (some r.sumRows)
        (fun k hk => by
          cases hk; exact Rel.le_sumRows_of hi hlti (length_le_of_mem_aggGroups hgrp))
      exact .inl (.inr ⟨m, hm, by simp [Measure.mayInf_of_makesInf hres hinf]⟩)

/-- `Rel.mayIssues_sound` follows: `Rel.eval`'s order is one of them. -/
example {cat : Catalog} (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {u : Bool} {r : Rel} (hwf : r.WF cat) (hsm : r.SmallAll cat) (p : Issue × Expr)
    (h : r.HasIssue cat u p) : p ∈ r.mayIssues cat A F T u :=
  Rel.mayIssues_sound_all hcat hA hF hT hwf hsm p (Rel.hasIssueAll_of_hasIssue h)

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
  -- A lambda's body too: a constant in it that raises counts as everywhere else (D21).
  | .hof _ l b => l.constIssues ++ b.constIssues

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
-- A raising constant in a lambda's body (`list_transform(xs, e -> e + 1 // 0)`) is counted too.
#guard letI := Boxes.Ambient.none;
  (Expr.hof .transform (.field 0) (.bin .add (.field 1) (.bin .idiv (.lit (.int 1)) (.lit (.int 0)))))
    |>.constIssues.eraseDups.map (·.1) == [.divByZero]

end Substrait
