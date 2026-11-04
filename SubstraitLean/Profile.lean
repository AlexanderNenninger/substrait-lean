import SubstraitLean.Safety
import SubstraitLean.Guards

/-!
# Engine profiles and proven shims (#185)

The reference semantics is `Expr.eval` together with `verify`'s errors
(`Expr.issues`, `SubstraitLean/Safety.lean`): on a row where an error issue
fires, the plan raises. An engine's semantics is a **profile**: what each
function gives, as an `Outcome`, a value or an error. The reference is one
profile (`Profile.reference`), and `Expr.evalP_reference` proves that
evaluating under it is `eval` and `issues`.

An engine's profile is a diff against the reference, from its
characterization (`characterization/duckdb/facts/` for DuckDB). A **shim**
rewrites a plan into one the engine evaluates to the reference's outcome,
adding guards (`UnFn.raise`, DuckDB's `error()`) where the engine is laxer,
or refuses it. A shimmed plan is an ordinary plan, so it is written and run
like any other. Shims are generated: `SubstraitLean/LoweringSearch.lean`
searches, for each function, for a template the engine evaluates to the
reference's outcome, and proves it (#241). `SubstraitLean/Lowering.lean` proves
lowering with such a table correct, and `SubstraitLean/LoweringDuckDB.lean`
holds DuckDB's tables, with `Rel.duckdb_shim_sound`.

Trusted, and tested rather than proved: that the profile matches the engine
(the fuzzer, #185), and that the SQL printer prints the plan faithfully,
`UnFn.isNum` as `IS NOT NULL` included.

This first slice covers scalar expressions and DuckDB's division and modulus
by zero (FACTS R2–R5).
-/

namespace Substrait

/-- What evaluating on an engine gives: a value, or an error it raises. -/
abbrev Outcome := Except Issue Value

/-- Two outcomes agree when they are the same value, or both errors. Which
error an engine reports first is not part of the semantics. -/
def Outcome.Agree : Outcome → Outcome → Prop
  | .ok v, .ok w => v = w
  | .error _, .error _ => True
  | _, _ => False

theorem Outcome.agree_refl : ∀ o : Outcome, o.Agree o
  | .ok _ => rfl
  | .error _ => trivial

/-- An engine's own algorithm for a family of aggregates of doubles, with
properties stricter than the generic ones the reference allows (#85,
`StatProps`, `FloatSums`). Each names what the engine's characterization
records (`characterization/<engine>/facts/`). -/
inductive AggAlgo where
  /-- Welford's update with Chan's merge (`duckdb-var-stddev`, `duckdb-covar`,
  `spark-var-stddev`, `spark-covar`). -/
  | welfordChan
  /-- Two-pass per block, blocks merged by Chan's formula (`polars-var-std`,
  ungrouped). -/
  | blockTwoPass
  /-- Pairwise summation (`polars-sum-float`). -/
  | pairwiseSum
  /-- Kahan's compensated summation (`duckdb-kahan-sum`, `fsum`). -/
  | kahanSum
  deriving Repr, DecidableEq

/-- An engine's semantics of each function. -/
structure Profile where
  un : UnFn → Value → Outcome
  bin : BinFn → Value → Value → Outcome
  /-- The algorithm of `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`, if the
  engine pins one with stricter properties; `none`: the generic properties
  (`StatProps`). -/
  statAlgo : Option AggAlgo := none
  /-- The algorithm of `SUM` and `AVG` of doubles, likewise; `none`: any order
  and grouping of the additions (`FloatSums`). -/
  sumAlgo : Option AggAlgo := none

/-- Raise an error issue; a warning (wrap-around) keeps the value. -/
def raiseIf (k : Option Issue) (v : Value) : Outcome :=
  match k with
  | some k => if k.isError then .error k else .ok v
  | none => .ok v

/-- The reference: the model's value, raising where `Safety.lean` reports an
error. -/
def Profile.reference : Profile where
  un f v := raiseIf (f.issue v) (f.apply v)
  bin f v w := raiseIf (f.issue v w) (f.apply v w)

/-- The error an outcome raises, if any. -/
def Outcome.err? : Outcome → Option Issue
  | .error k => some k
  | .ok _ => none

/-- An outcome's value (`NULL` for an error). -/
def Outcome.val : Outcome → Value
  | .ok w => w
  | .error _ => .null

/-- A higher-order function with a lambda that may raise: the lambda runs on
every element, and the first error raises. -/
def HoFn.applyP (f : HoFn) (v : Value) (p : Value → Outcome) : Outcome :=
  match v.elems.findSome? fun x => (p x).err? with
  | some k => .error k
  | none => .ok (f.apply v fun x => (p x).val)

/-- Evaluation under a profile: strict, left to right; a `CASE` evaluates the
branch it takes, and a lambda runs on every element. -/
def Expr.evalP (p : Profile) (row : Row) : Expr → Outcome
  | .lit v => .ok v
  | .field i => .ok (row.getD i .null)
  | .un f a => do p.un f (← a.evalP p row)
  | .bin f a b => do
    let x ← a.evalP p row
    let y ← b.evalP p row
    p.bin f x y
  | .ifThen c t e => do
    if (← c.evalP p row).isTrue then t.evalP p row else e.evalP p row
  | .hof f l b => do f.applyP (← l.evalP p row) fun x => b.evalP p [x]

/-! ## The reference is a profile -/

/-- The first error among issues. -/
def firstError (is : List (Issue × Expr)) : Option Issue := (is.find? (·.1.isError)).map (·.1)

theorem firstError_append (xs ys : List (Issue × Expr)) :
    firstError (xs ++ ys) = (firstError xs).or (firstError ys) := by
  simp only [firstError, List.find?_append]
  cases xs.find? (·.1.isError) <;> simp

/-- The reference's outcome, from `eval` and `issues`. -/
def Expr.refOutcome (row : Row) (e : Expr) : Outcome :=
  match firstError (e.issues row) with
  | some k => .error k
  | none => .ok (e.eval row)

theorem Expr.refOutcome_err (row : Row) (e : Expr) :
    (e.refOutcome row).err? = firstError (e.issues row) := by
  unfold refOutcome; cases firstError (e.issues row) <;> rfl

theorem Expr.refOutcome_val {row : Row} {e : Expr} (h : firstError (e.issues row) = none) :
    (e.refOutcome row).val = e.eval row := by
  unfold refOutcome; rw [h]; rfl

/-- The error an optional issue raises: none for a warning. -/
def errOf (o : Option Issue) : Option Issue := o.bind fun k => if k.isError then some k else none

theorem raiseIf_eq (o : Option Issue) (v : Value) :
    raiseIf o v = match errOf o with | some k => .error k | none => .ok v := by
  cases o with
  | none => rfl
  | some k => by_cases h : k.isError <;> simp [raiseIf, errOf, h]

theorem firstError_issue (o : Option Issue) (e : Expr) :
    firstError ((o.map (·, e)).toList) = errOf o := by
  cases o with
  | none => rfl
  | some k => by_cases h : k.isError <;> simp [firstError, errOf, h, List.find?]

theorem firstError_flatMap (xs : List Value) (g : Value → List (Issue × Expr)) :
    firstError (xs.flatMap g) = xs.findSome? fun x => firstError (g x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, firstError_append, ih, List.findSome?_cons]
    cases firstError (g x) <;> rfl

/-- An overflow to `±∞` (#575) is not an error: a call's errors are its
`issue`'s. -/
theorem errOf_or_inf {o i : Option Issue} (hi : ∀ k, i = some k → k = .infinite) :
    errOf (o.or i) = errOf o := by
  cases o with
  | some k => rfl
  | none =>
    cases i with
    | none => rfl
    | some k => rw [hi k rfl]; rfl

theorem UnFn.errOf_issueAll (f : UnFn) (v : Value) : errOf (f.issueAll v) = errOf (f.issue v) :=
  errOf_or_inf fun _ h => UnFn.infIssue_eq h

theorem BinFn.errOf_issueAll (f : BinFn) (v w : Value) :
    errOf (f.issueAll v w) = errOf (f.issue v w) :=
  errOf_or_inf fun _ h => BinFn.infIssue_eq h

/-- **The reference is a profile:** evaluating under `Profile.reference` is
`eval`, raising the first error `Safety.lean` reports. -/
theorem Expr.evalP_reference : ∀ (e : Expr) (row : Row),
    e.evalP Profile.reference row = e.refOutcome row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, row => by
    simp only [evalP, refOutcome, issues, firstError_append, firstError_issue,
      UnFn.errOf_issueAll, Expr.evalP_reference a row]
    cases firstError (a.issues row) with
    | some k => rfl
    | none =>
      simp only [Option.none_or, bind, Except.bind, Profile.reference, raiseIf_eq, eval]
      all_goals (cases errOf (f.issue (a.eval row)) <;> rfl)
  | .bin f a b, row => by
    simp only [evalP, refOutcome, issues, firstError_append, firstError_issue,
      BinFn.errOf_issueAll, Expr.evalP_reference a row, Expr.evalP_reference b row]
    cases firstError (a.issues row) with
    | some k => rfl
    | none =>
      cases firstError (b.issues row) with
      | some k => rfl
      | none =>
        simp only [Option.none_or, bind, Except.bind, Profile.reference, raiseIf_eq, eval]
        all_goals (cases errOf (f.issue (a.eval row) (b.eval row)) <;> rfl)
  | .ifThen c t e, row => by
    simp only [evalP, refOutcome, issues, firstError_append, Expr.evalP_reference c row]
    cases firstError (c.issues row) with
    | some k => rfl
    | none =>
      simp only [Option.none_or, bind, Except.bind, eval]
      split
      · rw [Expr.evalP_reference t row]; rfl
      · rw [Expr.evalP_reference e row]; rfl
  | .hof f l b, row => by
    simp only [evalP, refOutcome, issues, firstError_append, firstError_flatMap,
      Expr.evalP_reference l row]
    cases firstError (l.issues row) with
    | some k => rfl
    | none =>
      simp only [Option.none_or, bind, Except.bind, HoFn.applyP, eval]
      have hb : ∀ x, b.evalP Profile.reference [x] = b.refOutcome [x] :=
        fun x => Expr.evalP_reference b [x]
      simp only [hb, Expr.refOutcome_err]
      cases h : (l.eval row).elems.findSome? fun x => firstError (b.issues [x]) with
      | some k => rfl
      | none =>
        simp only [List.findSome?_eq_none_iff] at h
        exact congrArg Except.ok
          (HoFn.apply_congr f _ fun x hx => Expr.refOutcome_val (h x hx))

/-- A number: what `UnFn.isNum` tests. -/
def Value.isNum : Value → Bool
  | .int _ => true
  | _ => false

theorem UnFn.apply_isNum (v : Value) : UnFn.apply .isNum v = .bool v.isNum := by
  cases v <;> rfl

/-! The special codes' order, which the generated proofs compare with. -/

theorem FloatCode.negInf_lt_zero : FloatCode.negInf < 0 := fp64.negInf_lt_zero

theorem FloatCode.zero_lt_posInf : 0 < FloatCode.posInf := fp64.zero_lt_posInf

theorem FloatCode.posInf_lt_nan : FloatCode.posInf < FloatCode.nan := fp64.posInf_lt_nan

set_option exponentiation.threshold 3000 in
theorem FloatCode.one_lt_posInf : FloatCode.one < FloatCode.posInf := by
  rw [FloatCode.posInf_eq, FloatCode.maxMag_def]; unfold FloatCode.one; decide

theorem FloatCode.zero_lt_one : (0 : Int) < FloatCode.one := by
  unfold FloatCode.one
  have h : (0 : Int) < 2 ^ 1074 := Int.pow_pos (by decide)
  omega

theorem FloatCode.negInf_lt_negOne : FloatCode.negInf < FloatCode.negOne := by
  have := FloatCode.one_lt_posInf
  rw [FloatCode.negInf_eq]; rw [FloatCode.posInf_eq] at this
  unfold FloatCode.negOne; omega

theorem FloatCode.negOne_lt_zero : FloatCode.negOne < 0 := by
  have := FloatCode.zero_lt_one; unfold FloatCode.negOne; omega

theorem FloatCode.negInf_eq_neg_posInf : FloatCode.negInf = -FloatCode.posInf := by
  rw [FloatCode.negInf_eq, FloatCode.posInf_eq]

/-! ## DuckDB -/

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
  else FloatCode.lift₂ (· / ·) x y

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
  | .fadd, a, b => if nanCase .fadd a b then some (.ok (.int FloatCode.nan)) else none
  | .fsub, a, b => if nanCase .fsub a b then some (.ok (.int FloatCode.nan)) else none
  | .fmul, a, b => if nanCase .fmul a b then some (.ok (.int FloatCode.nan)) else none
  | .fdiv, a, b =>
    if b = 0 then some (if s.ieeeOps then .ok (.int (ieeeDivZero a)) else duckZero s)
    else if nanCase .fdiv a b then some (.ok (.int FloatCode.nan)) else none
  | .fmod, a, b =>
    if b = 0 then some (if s.ieeeOps then .ok (.int FloatCode.nan) else duckZero s)
    else if nanCase .fmod a b then some (.ok (.int FloatCode.nan)) else none
  -- `(-∞) ^ y` for a finite `y` that is not an integer: IEEE's `+∞` or `0`,
  -- under any setting, where the reference raises (`negInfPow`).
  | .fpow, a, b =>
    if negInfPow a b then some (.ok (.int (duckNegInfPow b)))
    else if s.ieeeOps then (if nanCase .fpow a b then some (.ok (.int FloatCode.nan)) else none)
    -- Without IEEE operations `0 ^ y` raises for a negative `y` (the reference: `∞`).
    else if a = 0 ∧ b < 0 then some (.error .domain) else none
  | .fatan2, a, b => if a = 0 ∧ b = 0 then some (.ok (.int 0)) else none
  | .bit .shl, a, b => some (duckShl a b)
  | .bit .shr, _, b => if b < 0 ∨ 64 ≤ b then some (.ok (.int 0)) else none
  | _, _, _ => none

/-- **DuckDB's unary functions** where they differ from the reference: with
`ieeeOps`, an elementary function outside its domain is NaN, or `-∞` for a
logarithm of zero (R15). -/
def duckUn (s : DuckDBSettings) : UnFn → Int → Option Outcome
  | .fmath f, x =>
    if s.ieeeOps ∧ f.apply x = none then some (.ok (.int (duckElementary f x))) else none
  | _, _ => none

/-- **DuckDB's profile**, as a diff against the reference (`duckBin`,
`duckUn`): what DuckDB 2.0 computes under the settings `s`, as probed
(`sverify_dev.probe`). Functions not probed are taken to be the reference's. -/
def Profile.duckdb (s : DuckDBSettings) : Profile where
  un f v := match v with
    | .int x => (duckUn s f x).getD (Profile.reference.un f v)
    | _ => Profile.reference.un f v
  bin f v w := match v, w with
    | .int x, .int y => (duckBin s f x y).getD (Profile.reference.bin f v w)
    | _, _ => Profile.reference.bin f v w

/-- DuckDB's `%` by a positive divisor is the reference's (the wrap-around
schema computes with it, `LoweringSearch.schema?`). -/
theorem Profile.duckdb_imod_pos (s : DuckDBSettings) (a m : Int) (hm : 0 < m) :
    (Profile.duckdb s).bin .imod (.int a) (.int m) = Profile.reference.bin .imod (.int a) (.int m) := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ -1 := by omega
  simp [Profile.duckdb, duckBin, h0, h1]

/-! ## Agreeing outcomes -/

theorem Outcome.agree_bind {o o' : Outcome} {g h : Value → Outcome} (ho : Outcome.Agree o o')
    (hg : ∀ v, Outcome.Agree (g v) (h v)) : Outcome.Agree (o >>= g) (o' >>= h) :=
  match o, o', ho with
  | .error _, .error _, _ => trivial
  | .ok v, .ok w, ho => by
    simp only [Outcome.Agree] at ho; subst ho; exact hg v

theorem Outcome.agree_err {o o' : Outcome} (h : o.Agree o') : o.err?.isSome = o'.err?.isSome := by
  cases o <;> cases o' <;> simp_all [Outcome.Agree, Outcome.err?]

theorem Outcome.agree_val {o o' : Outcome} (h : o.Agree o') : o.val = o'.val := by
  cases o <;> cases o' <;> simp_all [Outcome.Agree, Outcome.val]

theorem findSome?_isSome_congr {xs : List Value} {f g : Value → Option Issue}
    (h : ∀ x, (f x).isSome = (g x).isSome) :
    (xs.findSome? f).isSome = (xs.findSome? g).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    have := h x
    cases hf : f x <;> cases hg : g x <;> simp_all

theorem HoFn.applyP_agree (f : HoFn) (v : Value) {p q : Value → Outcome}
    (h : ∀ x, Outcome.Agree (p x) (q x)) : Outcome.Agree (f.applyP v p) (f.applyP v q) := by
  have hs := findSome?_isSome_congr (xs := v.elems) (fun x => Outcome.agree_err (h x))
  unfold HoFn.applyP
  cases hp : v.elems.findSome? (fun x => (p x).err?) <;>
    cases hq : v.elems.findSome? (fun x => (q x).err?) <;> simp_all [Outcome.Agree]
  exact HoFn.apply_congr f v fun x _ => Outcome.agree_val (h x)

/-! ## Plans that cannot raise

For a plan `verify` proves error-free from its contract, no shim is needed:
an engine whose profile agrees with the reference wherever the reference
does not raise (`Impl.Faithful`) gives `Rel.eval`'s rows, by guard
elimination (`Rel.guardFree_sound`). DuckDB's profile is such a profile. The
benchmark queries of #229 take this route. -/

/-- A profile's values, where it does not raise: what an engine computes. -/
def Profile.impl (p : Profile) : Impl :=
  ⟨fun f v => (p.un f v).val, fun f v w => (p.bin f v w).val⟩

theorem Profile.reference_faithful : Profile.reference.impl.Faithful :=
  ⟨fun f v h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val],
   fun f v w h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val]⟩

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
      · rename_i x y
        cases f <;> simp only [duckBin, BinFn.duckdbWritten] at hw ⊢ <;> (try split) <;>
          (try split) <;> (try split) <;>
          simp_all [BinFn.issue, nanIssue, domainIssue, BitOp.apply, atan2?] <;> omega
      · exact hr

/-- **A verified plan runs correctly on DuckDB.** When `Rel.mayIssues` reports
nothing but integer `SUM`s that may wrap (which keep their check), on every
catalog that satisfies the preconditions `A`, `F`, evaluating the plan with
DuckDB's functions gives `Rel.eval`'s rows, under DuckDB's IEEE operations
(the default), provided the plan's windows read fewer than `2⁶²` rows (the
size hypothesis, `Rel.Small`). Trusted: that `Profile.duckdb` is DuckDB's
(probed: `characterization/duckdb/probes.json`), and that the SQL printer is
faithful, writing out `MIN % -1` and `<<` (`Profile.duckdbWritten`). -/
theorem Rel.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.evalI (Profile.duckdbWritten s).impl cat = r.eval cat :=
  Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm (Profile.duckdbWritten_faithful s hieee)

/-! ## Plans that may raise

A plan `verify` cannot prove error-free still runs on DuckDB: its SQL raises
where an operation goes wrong (DuckDB's own errors, the shim's guards). What
holds for it is **partial correctness**: DuckDB returns `Rel.eval`'s rows, or
raises.

* `Expr.Exact p t e`: `t`, run with `p`'s functions, computes `e`'s value on
  every row where it does not raise. `Lowering.lower_exact` proves it for every
  expression and its lowering (`SubstraitLean/Lowering.lean`).
* `Rel.Raises p cat t`: some expression of `t` raises on a row `Rel.evalI`
  evaluates it on.
* `Rel.evalI_mapExprs`: a plan whose expressions are each `Exact` computes
  `Rel.eval`'s rows unless it raises. `Lowering.lowerRel_sound` applies it to
  a lowered plan, and `Rel.duckdb_shim_sound` to the shimmed plan on DuckDB.

No guard elimination is involved, so this needs neither a contract nor
`looseSub`. An engine may evaluate an expression on fewer rows than
`Rel.evalI` (a hash join tries its condition only on pairs whose keys match,
a pushed-down filter drops rows first); that skips evaluations without
changing a value, which is the engine's own correctness, trusted as before. -/

/-- Evaluating without errors under a profile is evaluating with its
functions. -/
theorem Expr.evalI_of_evalP {p : Profile} :
    ∀ {e : Expr} {row : Row} {v : Value}, e.evalP p row = .ok v → e.evalI p.impl row = v
  | .lit _, _, _, h | .field _, _, _, h => by
    simp only [Expr.evalP, Except.ok.injEq] at h; subst h; rfl
  | .un f a, row, v, h => by
    cases ha : a.evalP p row with
    | error k => simp [Expr.evalP, ha, bind, Except.bind] at h
    | ok x =>
      simp only [Expr.evalP, ha, bind, Except.bind] at h
      simp only [Expr.evalI]; rw [evalI_of_evalP ha]
      simp only [Profile.impl, h, Outcome.val]
  | .bin f a b, row, v, h => by
    cases ha : a.evalP p row with
    | error k => simp [Expr.evalP, ha, bind, Except.bind] at h
    | ok x =>
      cases hb : b.evalP p row with
      | error k => simp [Expr.evalP, ha, hb, bind, Except.bind] at h
      | ok y =>
        simp only [Expr.evalP, ha, hb, bind, Except.bind] at h
        simp only [Expr.evalI]; rw [evalI_of_evalP ha, evalI_of_evalP hb]
        simp only [Profile.impl, h, Outcome.val]
  | .ifThen c t e, row, v, h => by
    cases hc : c.evalP p row with
    | error k => simp [Expr.evalP, hc, bind, Except.bind] at h
    | ok x =>
      simp only [Expr.evalP, hc, bind, Except.bind] at h
      simp only [Expr.evalI, evalI_of_evalP hc]
      split
      · rename_i hx; simp only [hx, ↓reduceIte] at h; exact evalI_of_evalP h
      · rename_i hx
        simp only [hx, Bool.false_eq_true, ↓reduceIte] at h; exact evalI_of_evalP h
  | .hof f l b, row, v, h => by
    cases hl : l.evalP p row with
    | error k => simp [Expr.evalP, hl, bind, Except.bind] at h
    | ok w =>
      simp only [Expr.evalP, hl, bind, Except.bind, HoFn.applyP] at h
      split at h
      · cases h
      · rename_i hn
        simp only [Except.ok.injEq] at h; subst h
        simp only [Expr.evalI, evalI_of_evalP hl]
        refine HoFn.apply_congr f _ fun x hx => ?_
        have := (List.findSome?_eq_none_iff.mp hn) x hx
        cases hb : b.evalP p [x] with
        | error k => simp [hb, Outcome.err?] at this
        | ok y => rw [evalI_of_evalP hb]; rfl

/-- Where the reference does not raise, its value is `eval`'s. -/
theorem Expr.evalP_reference_ok {e : Expr} {row : Row} {v : Value}
    (h : e.evalP Profile.reference row = .ok v) : v = e.eval row := by
  rw [Expr.evalP_reference] at h
  unfold Expr.refOutcome at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; exact h.symm

/-- `t`, run with `p`'s functions, computes `e` on every row where it does
not raise. -/
def Expr.Exact (p : Profile) (t e : Expr) : Prop :=
  ∀ row v, t.evalP p row = .ok v → t.evalI p.impl row = e.eval row

theorem Expr.reference_exact (e : Expr) : Expr.Exact Profile.reference e e :=
  fun _ _ h => (evalI_of_evalP h).trans (evalP_reference_ok h)

/-! ### Relations -/

/-- `f` applied to a measure's argument and filter. -/
def Measure.mapExpr (f : Expr → Expr) (m : Measure) : Measure :=
  { m with arg := f m.arg, filter := m.filter.map f }

/-- `f` applied to every expression of a plan (window functions, whose
arguments are columns, are left as they are). -/
def Rel.mapExprs (f : Expr → Expr) : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (r.mapExprs f) (f c)
  | .project r es => .project (r.mapExprs f) (es.map f)
  | .emit r m => .emit (r.mapExprs f) m
  | .cross a b => .cross (a.mapExprs f) (b.mapExprs f)
  | .join a b ty on => .join (a.mapExprs f) (b.mapExprs f) ty (f on)
  | .fetch r o c => .fetch (r.mapExprs f) o c
  | .unionAll a b => .unionAll (a.mapExprs f) (b.mapExprs f)
  | .window r part sort fns => .window (r.mapExprs f) part sort fns
  | .semi a b anti on => .semi (a.mapExprs f) (b.mapExprs f) anti (f on)
  | .orderBy r keys => .orderBy (r.mapExprs f) keys
  | .distinct r => .distinct (r.mapExprs f)
  | .aggregate r gs ms => .aggregate (r.mapExprs f) (gs.map f) (ms.map (Measure.mapExpr f))
  | .unnest r c => .unnest (r.mapExprs f) c

theorem Rel.arity_mapExprs (f : Expr → Expr) (cat : Catalog) :
    ∀ r : Rel, (r.mapExprs f).arity cat = r.arity cat
  | .read _ | .values _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ => by
    simp [mapExprs, arity, arity_mapExprs f cat r]
  | .project r es | .window r _ _ es => by simp [mapExprs, arity, arity_mapExprs f cat r]
  | .emit _ _ | .aggregate _ _ _ => by simp [mapExprs, arity]
  | .cross a b | .join a b _ _ => by simp [mapExprs, arity, arity_mapExprs f cat a, arity_mapExprs f cat b]
  | .unionAll a _ | .semi a _ _ _ => by simp [mapExprs, arity, arity_mapExprs f cat a]

/-- An expression that raises under `p` on `row`. -/
def Expr.RaisesOn (p : Profile) (row : Row) (e : Expr) : Prop := (e.evalP p row).err?.isSome

theorem Expr.ok_of_not_raises {p : Profile} {row : Row} {e : Expr} (h : ¬e.RaisesOn p row) :
    ∃ v, e.evalP p row = .ok v := by
  cases he : e.evalP p row with
  | error k => simp [Expr.RaisesOn, he, Outcome.err?] at h
  | ok v => exact ⟨v, rfl⟩

/-- An exact expression that does not raise computes the reference's value. -/
theorem Expr.Exact.eq {p : Profile} {t e : Expr} (hx : Expr.Exact p t e) {row : Row}
    (h : ¬t.RaisesOn p row) : t.evalI p.impl row = e.eval row := by
  obtain ⟨v, hv⟩ := Expr.ok_of_not_raises h
  exact hx row v hv

/-- **Some expression raises** on a row `Rel.evalI` evaluates it on. -/
def Rel.Raises (p : Profile) (cat : Catalog) : Rel → Prop
  | .read _ | .values _ _ => False
  | .filter r c => r.Raises p cat ∨ ∃ row ∈ r.evalI p.impl cat, c.RaisesOn p row
  | .project r es => r.Raises p cat ∨ ∃ row ∈ r.evalI p.impl cat, ∃ e ∈ es, e.RaisesOn p row
  | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r | .unnest r _ =>
    r.Raises p cat
  | .cross a b | .unionAll a b => a.Raises p cat ∨ b.Raises p cat
  | .join a b _ on | .semi a b _ on => a.Raises p cat ∨ b.Raises p cat ∨
      ∃ x ∈ a.evalI p.impl cat, ∃ y ∈ b.evalI p.impl cat, on.RaisesOn p (x ++ y)
  | .aggregate r gs ms => r.Raises p cat ∨
      ∃ row ∈ r.evalI p.impl cat, ∃ e ∈ gs ++ ms.flatMap Measure.exprs, e.RaisesOn p row

theorem leftJoinRowI_map {I : Impl} {on on' : Expr} {n : Nat} {ys : Relation} {x : Row}
    (h : ∀ y ∈ ys, on'.evalI I (x ++ y) = on.eval (x ++ y)) :
    leftJoinRowI I on' n ys x = leftJoinRow on n ys x := by
  have : ((ys.map (x ++ ·)).filter fun row => (on'.evalI I row).isTrue) =
      (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue :=
    List.filter_congr fun row hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      rw [h y hy]
  simp only [leftJoinRowI, leftJoinRow, this]

theorem hasMatchI_map {I : Impl} {on on' : Expr} {x : Row} :
    ∀ {ys : Relation}, (∀ y ∈ ys, on'.evalI I (x ++ y) = on.eval (x ++ y)) →
      hasMatchI I on' ys x = hasMatch on ys x
  | [], _ => rfl
  | y :: ys, h => by
    have ih := hasMatchI_map (ys := ys) fun z hz => h z (by simp [hz])
    simp only [hasMatchI, hasMatch, List.any_cons] at ih ⊢
    rw [h y (by simp), ih]

theorem Measure.mapExpr_exprs (f : Expr → Expr) (m : Measure) :
    (m.mapExpr f).exprs = f m.arg :: m.filter.toList.map f ++ m.sort.map (.field ·.col) := by
  cases h : m.filter <;> simp [Measure.mapExpr, Measure.exprs, h]

theorem aggregateEvalI_map {I : Impl} {f : Expr → Expr} {gs : List Expr} {ms : List Measure}
    {rows : Relation}
    (h : ∀ row ∈ rows, ∀ e ∈ gs ++ ms.flatMap Measure.exprs, (f e).evalI I row = e.eval row) :
    aggregateEvalI I (gs.map f) (ms.map (Measure.mapExpr f)) rows = aggregateEval gs ms rows := by
  have hk : ∀ row ∈ rows, groupKeyI I (gs.map f) row = groupKey gs row := fun row hr => by
    simp only [groupKeyI, groupKey, List.map_map]
    exact List.map_congr_left fun g hg => h row hr g (List.mem_append_left _ hg)
  have hin : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      (m.mapExpr f).inputsI I sub = m.inputs sub := by
    intro m hm sub hsub
    have he : ∀ row ∈ sub, ∀ e ∈ m.exprs, (f e).evalI I row = e.eval row := fun row hr e he =>
      h row (hsub row hr) e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, he⟩))
    have hkept : (m.mapExpr f).keptI I sub = m.kept sub := by
      cases hc : m.filter with
      | none => simp only [Measure.keptI, Measure.kept, Measure.mapExpr, hc, Option.map_none]
      | some c =>
        simp only [Measure.keptI, Measure.kept, Measure.mapExpr, hc, Option.map_some]
        exact List.filter_congr fun row hr => by
          rw [he row hr c (by simp [Measure.exprs, hc])]
    have hsub' : ∀ row ∈ m.kept sub, row ∈ sub := fun row hr => by
      unfold Measure.kept at hr; split at hr
      · exact hr
      · exact (List.mem_filter.mp hr).1
    simp only [Measure.inputsI, Measure.inputs, hkept]
    have : (m.mapExpr f).distinct = m.distinct := rfl
    rw [this, List.map_congr_left fun row hr =>
      (show (m.mapExpr f).arg.evalI I row = m.arg.eval row from
        he row (hsub' row hr) m.arg (by simp [Measure.exprs]))]
  have hm : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      (m.mapExpr f).evalI I sub = m.eval sub := by
    intro m hm sub hsub
    have hfn : (m.mapExpr f).fn = m.fn := rfl
    have hsort : (m.mapExpr f).sort = m.sort := rfl
    cases hf : m.fn
    all_goals simp only [Measure.evalI, Measure.eval, hfn, hsort, hf]
    case collect => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case pick => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case concat => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case mode => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    all_goals rw [hin m hm sub hsub]
  unfold aggregateEvalI aggregateEval
  simp only [List.isEmpty_map]
  split
  · simp only [List.map_map]
    exact congrArg (fun x => [x]) (List.map_congr_left fun m hmm => hm m hmm rows fun _ h => h)
  · rw [List.map_congr_left hk]
    refine List.map_congr_left fun k _ => ?_
    have hf : (rows.filter fun row => groupKeyI I (gs.map f) row == k) = groupRows gs rows k :=
      List.filter_congr fun row hr => by rw [hk row hr]
    rw [hf, List.map_map]
    exact congrArg (k ++ ·) (List.map_congr_left fun m hmm =>
      hm m hmm _ fun _ hr => (List.mem_filter.mp hr).1)

/-- **A plan of exact expressions computes `Rel.eval`'s rows unless it
raises.** `f` must keep columns as they are (a measure's sort keys). -/
theorem Rel.evalI_mapExprs {p : Profile} {f : Expr → Expr} (hx : ∀ e, Expr.Exact p (f e) e)
    (hf : ∀ i, f (.field i) = .field i) {cat : Catalog} :
    ∀ {r : Rel}, ¬(r.mapExprs f).Raises p cat → (r.mapExprs f).evalI p.impl cat = r.eval cat
  | .read _, _ | .values _ _, _ => rfl
  | .filter r c, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have ih := evalI_mapExprs hx hf (r := r) h.1
    have h2 := h.2; rw [ih] at h2
    simp only [mapExprs, evalI, eval, ih]
    exact List.filter_congr fun row hr => by rw [(hx c).eq (h2 row hr)]
  | .project r es, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have ih := evalI_mapExprs hx hf (r := r) h.1
    have h2 := h.2; rw [ih] at h2
    simp only [mapExprs, evalI, eval, ih, List.map_map]
    exact List.map_congr_left fun row hr => congrArg (row ++ ·) (List.map_congr_left fun e he =>
      (hx e).eq (h2 row hr (f e) (List.mem_map_of_mem he)))
  | .emit r _, h | .orderBy r _, h | .distinct r, h | .unnest r _, h | .window r _ _ _, h => by
    simp only [mapExprs, Raises] at h
    simp only [mapExprs, evalI, eval, evalI_mapExprs hx hf (r := r) h]
  | .fetch r _ cnt, h => by
    simp only [mapExprs, Raises] at h
    have ih := evalI_mapExprs hx hf (r := r) h
    cases cnt <;> simp only [mapExprs, evalI, eval, ih]
  | .cross a b, h | .unionAll a b, h => by
    simp only [mapExprs, Raises, not_or] at h
    simp only [mapExprs, evalI, eval, evalI_mapExprs hx hf (r := a) h.1,
      evalI_mapExprs hx hf (r := b) h.2]
  | .join a b .inner on, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have iha := evalI_mapExprs hx hf (r := a) h.1
    have ihb := evalI_mapExprs hx hf (r := b) h.2.1
    have h2 := h.2.2; rw [iha, ihb] at h2
    simp only [mapExprs, evalI, eval, iha, ihb]
    exact List.filter_congr fun row hr => by
      obtain ⟨x, hx', y, hy, rfl⟩ := mem_crossRows.mp hr
      rw [(hx on).eq (h2 x hx' y hy)]
  | .join a b .left on, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have iha := evalI_mapExprs hx hf (r := a) h.1
    have ihb := evalI_mapExprs hx hf (r := b) h.2.1
    have h2 := h.2.2; rw [iha, ihb] at h2
    simp only [mapExprs, evalI, eval, iha, ihb, arity_mapExprs]
    exact flatMap_congr fun x hx' => leftJoinRowI_map fun y hy => (hx on).eq (h2 x hx' y hy)
  | .semi a b _ on, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have iha := evalI_mapExprs hx hf (r := a) h.1
    have ihb := evalI_mapExprs hx hf (r := b) h.2.1
    have h2 := h.2.2; rw [iha, ihb] at h2
    simp only [mapExprs, evalI, eval, iha, ihb]
    exact List.filter_congr fun x hx' => by
      rw [hasMatchI_map fun y hy => (hx on).eq (h2 x hx' y hy)]
  | .aggregate r gs ms, h => by
    simp only [mapExprs, Raises, not_or, not_exists, not_and] at h
    have ih := evalI_mapExprs hx hf (r := r) h.1
    have h2 := h.2; rw [ih] at h2
    simp only [mapExprs, evalI, eval, ih]
    refine aggregateEvalI_map fun row hr e he => ?_
    have hmem : ∀ e' ∈ gs.map f ++ (ms.map (Measure.mapExpr f)).flatMap Measure.exprs,
        ¬e'.RaisesOn p row := h2 row hr
    simp only [List.mem_append, List.mem_flatMap] at he
    rcases he with he | ⟨m, hm, he⟩
    · exact (hx e).eq (hmem _ (List.mem_append_left _ (List.mem_map_of_mem he)))
    · have hin : ∀ e' ∈ (m.mapExpr f).exprs, ¬e'.RaisesOn p row := fun e' he' =>
        hmem e' (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hm, he'⟩))
      rw [Measure.mapExpr_exprs] at hin
      simp only [Measure.exprs, List.mem_cons, List.mem_append, List.mem_map] at he
      rcases he with (rfl | he) | ⟨k, _, rfl⟩
      · exact (hx _).eq (hin _ (List.mem_cons_self ..))
      · exact (hx e).eq (hin _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem he))))
      · rw [hf]; rfl

end Substrait
