import SubstraitLean.Contracts

/-!
# Runtime errors

DataFusion fails at run time on integer division or remainder by zero, on
`MIN / -1`, on integer powers with a negative exponent or a result outside
64 bits, on `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, on
an invalid regular expression, on `date_trunc` to a week, month, quarter or
year outside ±2⁶³ nanoseconds, and on date arithmetic (`DATE ± days`, adding
months) outside the years `chrono` represents. `date_trunc` of a DATE goes
through nanoseconds and gives garbage outside them (1677 to 2262), which is
reported as an error too. Integer `+`, `-`, `*` and negation do not fail:
they wrap around silently, so the result differs from `Rel.eval`'s
(unbounded) integers; so does `date_trunc` to a day or less below `-2⁶³`. All of these are
`Issue`s; wrapping is a warning, the rest are errors.

**When does DataFusion evaluate an expression?** (Checked against DataFusion
51; this is the trusted part of the model.)

* `CASE` evaluates a branch only on rows that take it, so
  `CASE WHEN b <> 0 THEN a / b END` and `a / NULLIF(b, 0)` are safe.
* `AND` and `OR` evaluate both sides: `b <> 0 AND a / b > 1` fails on `b = 0`.
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
  /-- Integer division or remainder by zero. -/
  | divByZero
  /-- A result outside 64 bits where DataFusion fails (`MIN / -1`, `POWER`). -/
  | overflow
  /-- `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value. -/
  | badCast
  /-- `POWER` of integers with a negative exponent. -/
  | negExponent
  /-- A regular expression outside `Text.simpleRegex`, which may not compile. -/
  | badRegex
  /-- `+`, `-`, `*` or negation leaving 64 bits: DataFusion wraps around. -/
  | wraps
  /-- An integer `SUM` leaving 64 bits: DataFusion wraps around. Kept apart
  from `wraps` because it comes from a group's rows, not from one row:
  `SubstraitLean/Guards.lean` drops row-level checks, never this one. -/
  | sumWraps
  deriving Repr, DecidableEq

def Issue.name : Issue → String
  | .divByZero => "division by zero"
  | .overflow => "overflow"
  | .badCast => "cast out of range"
  | .negExponent => "negative exponent"
  | .badRegex => "invalid regular expression"
  | .wraps | .sumWraps => "may wrap around"

/-- The arguments of a list of window functions' integer `SUM`s. -/
def WinFn.sumArg? (fns : List WinFn) : List Expr :=
  fns.filterMap fun | .agg m _ _ => if m.fn = .sum then some m.arg else none | _ => none

/-- Errors stop the query; wrapping silently gives a different result. -/
def Issue.isError : Issue → Bool
  | .wraps | .sumWraps => false
  | _ => true

def inI64 (i : Int) : Bool := decide (minI64 ≤ i) && decide (i ≤ maxI64)

def wrapIf (i : Int) : Option Issue := if inI64 i then none else some .wraps

def withinRange (lo hi i : Int) : Bool := decide (lo ≤ i) && decide (i ≤ hi)

/-- `overflow` unless the argument `x` and the result `y` are in `[lo, hi]`:
the dates and timestamps `chrono` represents, or DataFusion's nanoseconds. -/
def rangeIssue (lo hi x y : Int) : Option Issue :=
  if withinRange lo hi x && withinRange lo hi y then none else some .overflow

/-! ## What goes wrong on a row -/

def UnFn.issue : UnFn → Value → Option Issue
  | .neg, .int i => wrapIf (-i)
  | .ftoi, .int c => match FloatCode.toInt? c with
    | some x => if inI64 x then none else some .badCast
    | none => some .badCast
  | .narrow n, .int i => if fitsBits n i then none else some .badCast
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
  | _, _ => none

def BinFn.issue : BinFn → Value → Value → Option Issue
  | .add, .int a, .int b => wrapIf (a + b)
  | .sub, .int a, .int b => wrapIf (a - b)
  | .mul, .int a, .int b => wrapIf (a * b)
  | .dateAdd, .int a, .int b => rangeIssue Time.dayMin Time.dayMax a (a + b)
  | .idiv, .int a, .int b =>
    if b = 0 then some .divByZero else if inI64 (a.tdiv b) then none else some .overflow
  | .imod, .int _, .int b => if b = 0 then some .divByZero else none
  | .ipow, .int a, .int b =>
    if b < 0 then some .negExponent
    else if 64 < b ∧ 1 < a.natAbs then some .overflow
    else if inI64 (a ^ b.toNat) then none else some .overflow
  | _, _, _ => none

/-- The issues evaluating `e` on `row` runs into, each with the operation
that raises it. A `CASE` only evaluates the branch it takes. -/
def Expr.issues (row : Row) : Expr → List (Issue × Expr)
  | .lit _ | .field _ => []
  | .un f a => a.issues row ++ ((f.issue (a.eval row)).map (·, .un f a)).toList
  | .bin f a b =>
    a.issues row ++ b.issues row ++ ((f.issue (a.eval row) (b.eval row)).map (·, .bin f a b)).toList
  | .ifThen c t e => c.issues row ++ if (c.eval row).isTrue then t.issues row else e.issues row

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
  | .regexMatch p, _, _ => if Text.simpleRegex p then [] else [.badRegex]
  | .dateTrunc u, aa, ar =>
    if u.calendar then (if nsFits aa ar then [] else [.overflow])
    else if ar.intFits then [] else [.wraps]
  | .dayTrunc _, aa, ar => rangeMay Time.nsDayMin Time.nsDayMax aa ar
  | .addMonths _ false, aa, ar => rangeMay Time.dayMin Time.dayMax aa ar
  | .addMonths _ true, aa, ar => rangeMay Time.partMin Time.partMax aa ar
  | .timeOfDay, aa, _ | .strftime _, aa, _ => rangeMay Time.partMin Time.partMax aa aa
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

/-- `nz`: the divisor is never the integer 0. -/
def BinFn.mayIssue : BinFn → AVal → AVal → AVal → Bool → List Issue
  | .add, _, _, ar, _ | .sub, _, _, ar, _ | .mul, _, _, ar, _ =>
    if ar.intFits then [] else [.wraps]
  | .dateAdd, aa, _, ar, _ => rangeMay Time.dayMin Time.dayMax aa ar
  | .idiv, _, _, ar, nz => (if nz then [] else [.divByZero]) ++ (if ar.intFits then [] else [.overflow])
  | .imod, _, _, _, nz => if nz then [] else [.divByZero]
  | .ipow, aa, ab, _, _ =>
    (if ab.int.all (·.lo.any (0 ≤ ·)) then [] else [.negExponent]) ++
      (if powFits aa ab then [] else [.overflow])
  | _, _, _, _, _ => []

/-- Is `x`'s value never the integer 0? From its interval, an assumption
`x ≠ 0`, a fact `$j ≠ -c` for `x = $j + c`, or both branches of a `CASE`. -/
def Expr.nonZero (env : List AVal) (fs : List Fact) (ks : Assumptions) (x : Expr) : Bool :=
  (x.absD env fs ks).int.all (!·.has0) ||
  ks.any (fun sk => sk.1 == x && match sk.2 with | .ne 0 => true | _ => false) ||
  (match x.linTerm with | some (j, c) => fs.contains (.ne j (-c)) | none => false) ||
  match x with
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    (!ac.tt || t.nonZero (c.refine env) fs (c.cstrs true ++ ks)) &&
      (!(ac.nonBool || ac.ff) || e.nonZero (c.refineNeg env) fs (c.cstrs false ++ ks))
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
        (b.nonZero env fs ks)).map (·, .bin f a b)
  | .ifThen c t e =>
    let ac := c.absD env fs ks
    c.mayIssues env fs ks ++
      (if ac.tt then t.mayIssues (c.refine env) fs (c.cstrs true ++ ks) else []) ++
      (if ac.nonBool || ac.ff then e.mayIssues (c.refineNeg env) fs (c.cstrs false ++ ks) else [])

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
        · rcases mem_cases hcm with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ | ⟨_, _, hs⟩
          · simp_all [AVal.nonBool]
          · simp_all [AVal.nonBool]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp_all
          · simp_all [AVal.nonBool]
        · exact Expr.nonZero_sound (Expr.refineNeg_sound env c h hf) hfs
            (KsHold.cons_cstrs hf hks) e he j hj
    · simp at hc

theorem UnFn.mayIssue_sound (f : UnFn) {aa ar : AVal} {v : Value} {k : Issue}
    (ha : aa.Mem v) (hr : ar.Mem (f.apply v)) (hk : f.issue v = some k) : k ∈ f.mayIssue aa ar := by
  cases f <;> cases v <;> simp only [UnFn.issue, reduceCtorEq] at hk
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
  case regexMatch.null | regexMatch.int | regexMatch.bool | regexMatch.str =>
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
  case addMonths.int m t x =>
    cases t
    · exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk
    · exact rangeIssue_sound ha (by simpa [UnFn.apply] using hr) hk

theorem BinFn.mayIssue_sound (f : BinFn) {aa ab ar : AVal} {v w : Value} {nz : Bool} {k : Issue}
    (ha : aa.Mem v) (hb : ab.Mem w) (hr : ar.Mem (f.apply v w))
    (hnz : nz = true → ∀ j, w = .int j → j ≠ 0) (hk : f.issue v w = some k) :
    k ∈ f.mayIssue aa ab ar nz := by
  cases f <;> cases v <;> cases w <;> simp only [BinFn.issue, reduceCtorEq] at hk
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
          (fun hnz => Expr.nonZero_sound h hfs hks b hnz) hi)
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
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hff⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hff]
          · simp [AVal.nonBool, hs]
        simp only [this, ite_true]
        exact Expr.mayIssues_sound (Expr.refineNeg_sound env c h hf) hfs (KsHold.cons_cstrs hf hks) e p hp

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

/-- **Where issues happen.** Filter and join conditions run on the loose
input; projections on their input, or on the loose input under a filter or
join condition (`under`), which may inline them. Aggregates evaluate their
grouping expressions and every measure's argument and filter like
projections, and a `SUM` of integers wraps around when the true sum of a
group leaves 64 bits. -/
def Rel.HasIssue (cat : Catalog) : Bool → Rel → Issue × Expr → Prop
  | _, .read _, _ | _, .values _ _, _ => False
  | _, .filter r c, p => r.HasIssue cat true p ∨ ∃ row ∈ r.loose.eval cat, p ∈ c.issues row
  | u, .project r es, p => r.HasIssue cat u p ∨
      ∃ row ∈ (if u then r.loose else r).eval cat, ∃ e ∈ es, p ∈ e.issues row
  | u, .emit r _, p | u, .fetch r _ _, p | u, .orderBy r _, p
  | u, .distinct r, p => r.HasIssue cat u p
  -- A window `SUM` of integers may wrap around (its argument is a column:
  -- `Parse.issueFree`).
  | u, .window r _ _ fns, p => r.HasIssue cat u p ∨ p ∈ (WinFn.sumArg? fns).map (.sumWraps, ·)
  | u, .cross a b, p | u, .unionAll a b, p => a.HasIssue cat u p ∨ b.HasIssue cat u p
  | _, .join a b _ on, p | _, .semi a b _ on, p => a.HasIssue cat true p ∨ b.HasIssue cat true p ∨
      ∃ x ∈ a.loose.eval cat, ∃ y ∈ b.loose.eval cat, p ∈ on.issues (x ++ y)
  | u, .aggregate r gs ms, p => r.HasIssue cat u p ∨
      (∃ row ∈ (if u then r.loose else r).eval cat, ∃ e ∈ gs ++ ms.flatMap Measure.exprs,
        p ∈ e.issues row) ∨
      ∃ m ∈ ms, m.fn = .sum ∧ p = (.sumWraps, m.arg) ∧
        ∃ grp ∈ aggGroups gs (r.eval cat), inI64 (intSum (m.inputs grp)) = false

/-- The issues the abstract evaluation cannot rule out. -/
def Rel.mayIssues (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Bool → Rel → List (Issue × Expr)
  | _, .read _ | _, .values _ _ => []
  | _, .filter r c =>
    r.mayIssues cat A F T true ++ c.mayIssues (r.loose.aeval cat A F T) (r.loose.facts cat F T)
  | u, .project r es =>
    let s := if u then r.loose else r
    r.mayIssues cat A F T u ++ es.flatMap (·.mayIssues (s.aeval cat A F T) (s.facts cat F T))
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r =>
    r.mayIssues cat A F T u
  | u, .window r _ _ fns => r.mayIssues cat A F T u ++ (WinFn.sumArg? fns).map (.sumWraps, ·)
  | u, .cross a b | u, .unionAll a b => a.mayIssues cat A F T u ++ b.mayIssues cat A F T u
  | _, .join a b _ on | _, .semi a b _ on =>
    let ab := Rel.cross a.loose b.loose
    a.mayIssues cat A F T true ++ b.mayIssues cat A F T true ++
      on.mayIssues (ab.aeval cat A F T) (ab.facts cat F T)
  -- Nothing bounds the number of rows in a group, so any integer sum may wrap.
  | u, .aggregate r gs ms =>
    let s := if u then r.loose else r
    r.mayIssues cat A F T u ++
      (gs ++ ms.flatMap Measure.exprs).flatMap (·.mayIssues (s.aeval cat A F T) (s.facts cat F T)) ++
      ms.filterMap fun m => if m.fn = .sum then some (.sumWraps, m.arg) else none

theorem KsHold.nil (row : Row) : KsHold [] row := by simp [KsHold]

/-- Join and semi-join conditions run on pairs of loose input rows. -/
theorem condIssue_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {a b : Rel} {on : Expr} {p : Issue × Expr} {x y : Row} (ha : a.WF cat) (hb : b.WF cat)
    (hx : x ∈ a.loose.eval cat) (hy : y ∈ b.loose.eval cat) (hp : p ∈ on.issues (x ++ y)) :
    p ∈ on.mayIssues ((Rel.cross a.loose b.loose).aeval cat A F T)
      ((Rel.cross a.loose b.loose).facts cat F T) := by
  have hab : (Rel.cross a.loose b.loose).WF cat := ⟨Rel.loose_wf ha, Rel.loose_wf hb⟩
  have hrow : x ++ y ∈ (Rel.cross a.loose b.loose).eval cat := by
    simp only [Rel.eval, mem_crossRows]; exact ⟨x, hx, y, hy, rfl⟩
  exact Expr.mayIssues_sound (Rel.aeval_sound hcat hA hF hT hab _ hrow)
    (Rel.facts_sound hcat hF hT hab _ hrow) (KsHold.nil _) on p hp

/-- **Soundness**: every issue that can happen when running a well-formed plan
is among `Rel.mayIssues`. So an empty list proves the plan runs without
errors and without wrapping around. -/
theorem Rel.mayIssues_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat) :
    ∀ {u : Bool} {r : Rel}, r.WF cat → ∀ p, r.HasIssue cat u p → p ∈ r.mayIssues cat A F T u
  | _, .read _, _, _, h | _, .values _ _, _, _, h => h.elim
  | _, .filter r c, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | ⟨row, hrow, hp⟩
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 p h)
    · have hl := loose_wf hwf.1
      exact .inr (Expr.mayIssues_sound (aeval_sound hcat hA hF hT hl row hrow)
        (facts_sound hcat hF hT hl row hrow) (KsHold.nil row) c p hp)
  | u, .project r es, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 p h)
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      exact .inr ⟨e, he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩
  | _, .emit r _, hwf, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf.1 p h
  | _, .fetch r _ _, hwf, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf p h
  | _, .window r _ _ _, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound hcat hA hF hT (r := r) hwf.1 p h)
    · exact .inr h
  | _, .orderBy r _, hwf, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf.1 p h
  | _, .distinct r, hwf, p, h => mayIssues_sound hcat hA hF hT (r := r) hwf p h
  | _, .cross a b, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 p h)
    · exact .inr (mayIssues_sound hcat hA hF hT hwf.2 p h)
  | _, .unionAll a b, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h
    · exact .inl (mayIssues_sound hcat hA hF hT hwf.1 p h)
    · exact .inr (mayIssues_sound hcat hA hF hT hwf.2.1 p h)
  | _, .join a b ty on, hwf, p, h => by
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT ha p h))
    · exact .inl (.inr (mayIssues_sound hcat hA hF hT hb p h))
    · exact .inr (condIssue_sound hcat hA hF hT ha hb hx hy hp)
  | _, .semi a b _ on, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append]
    rcases h with h | h | ⟨x, hx, y, hy, hp⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 p h))
    · exact .inl (.inr (mayIssues_sound hcat hA hF hT hwf.2.1 p h))
    · exact .inr (condIssue_sound hcat hA hF hT hwf.1 hwf.2.1 hx hy hp)
  | u, .aggregate r gs ms, hwf, p, h => by
    simp only [HasIssue] at h
    simp only [mayIssues, List.mem_append, List.mem_flatMap, List.mem_filterMap]
    rcases h with h | ⟨row, hrow, e, he, hp⟩ | ⟨m, hm, hf, rfl, _⟩
    · exact .inl (.inl (mayIssues_sound hcat hA hF hT hwf.1 p h))
    · have hs : (if u then r.loose else r).WF cat := by
        cases u
        · exact hwf.1
        · exact loose_wf hwf.1
      exact .inl (.inr ⟨e, by simpa using he, Expr.mayIssues_sound (aeval_sound hcat hA hF hT hs row hrow)
        (facts_sound hcat hF hT hs row hrow) (KsHold.nil row) e p hp⟩)
    · exact .inr ⟨m, hm, by simp [hf]⟩

end Substrait
