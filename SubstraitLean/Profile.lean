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
characterization (`characterization/duckdb/FACTS.md` for DuckDB). A **shim**
rewrites a plan into one the engine evaluates to the reference's outcome,
adding guards (`UnFn.raise`, DuckDB's `error()`) where the engine is laxer,
or refuses it. A shimmed plan is an ordinary plan, so it is written and run
like any other. `shim_correct` proves it: the shimmed expression under the
engine's profile has the reference's outcome, the same value or an error.

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

/-- An engine's semantics of each function. -/
structure Profile where
  un : UnFn → Value → Outcome
  bin : BinFn → Value → Value → Outcome

/-- Raise an error issue; a warning (wrap-around) keeps the value. -/
def raiseIf (k : Option Issue) (v : Value) : Outcome :=
  match k with
  | some k => if k.isError then .error k else .ok v
  | none => .ok v

/-- The reference: the model's value, raising where `Safety.lean` reports an
error. -/
def Profile.reference : Profile :=
  ⟨fun f v => raiseIf (f.issue v) (f.apply v), fun f v w => raiseIf (f.issue v w) (f.apply v w)⟩

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

/-- **The reference is a profile:** evaluating under `Profile.reference` is
`eval`, raising the first error `Safety.lean` reports. -/
theorem Expr.evalP_reference : ∀ (e : Expr) (row : Row),
    e.evalP Profile.reference row = e.refOutcome row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, row => by
    simp only [evalP, refOutcome, issues, firstError_append, firstError_issue,
      Expr.evalP_reference a row]
    cases firstError (a.issues row) with
    | some k => rfl
    | none =>
      simp only [Option.none_or, bind, Except.bind, Profile.reference, raiseIf_eq, eval]
      all_goals (cases errOf (f.issue (a.eval row)) <;> rfl)
  | .bin f a b, row => by
    simp only [evalP, refOutcome, issues, firstError_append, firstError_issue,
      Expr.evalP_reference a row, Expr.evalP_reference b row]
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

/-! ## DuckDB -/

/-- The DuckDB settings its profile depends on. -/
structure DuckDBSettings where
  /-- `error_on_division_by_zero`, on by default since DuckDB 2.0
  (`characterization/duckdb/FACTS.md`, R2–R5). -/
  errorOnDivZero : Bool := true

/-- Integer `//` and `%`, and double `/` and `%`. -/
def BinFn.divides : BinFn → Bool
  | .idiv | .imod | .fdiv | .fmod => true
  | _ => false

/-- `x / 0.0` in IEEE arithmetic: NaN for `0.0` and NaN, else ±∞ by the
dividend's sign. -/
def ieeeDivZero (x : Int) : Int :=
  if x = 0 ∨ x = FloatCode.nan then FloatCode.nan
  else if 0 < x then FloatCode.posInf else FloatCode.negInf

/-- What DuckDB gives for a division or modulus by zero with
`error_on_division_by_zero` off: NULL for integers (R2, R3), IEEE values for
`/` of doubles (R5), NaN for `%` of doubles (R4). -/
def duckDivZero : BinFn → Int → Value
  | .fdiv, x => .int (ieeeDivZero x)
  | .fmod, _ => .int FloatCode.nan
  | _, _ => .null

/-- **DuckDB's profile**, as a diff against the reference: with
`error_on_division_by_zero` off, a division or modulus by zero does not raise.
Everything else is native. -/
def Profile.duckdb (s : DuckDBSettings) : Profile where
  un := Profile.reference.un
  bin f v w := match v, w with
    | .int x, .int 0 =>
      if f.divides && !s.errorOnDivZero then .ok (duckDivZero f x) else Profile.reference.bin f v w
    | _, _ => Profile.reference.bin f v w

/-- **DuckDB's shim:** with `error_on_division_by_zero` off, a division or
modulus raises on a zero divisor, `CASE WHEN x IS NOT NULL AND y = 0 THEN
error() ELSE x / y END` (a NULL dividend gives NULL, as in the reference).
Everything else is written as it is. -/
def shimDuckDB (s : DuckDBSettings) : Expr → Option Expr
  | .lit v => some (.lit v)
  | .field i => some (.field i)
  | .un f a => (shimDuckDB s a).map (.un f)
  | .bin f a b => do
    let a' ← shimDuckDB s a
    let b' ← shimDuckDB s b
    if f.divides && !s.errorOnDivZero then
      some (.ifThen (.bin .and (.un .isNum a') (.bin .eq b' (.lit (.int 0))))
        (.un (.raise "division by zero") b') (.bin f a' b'))
    else some (.bin f a' b')
  | .ifThen c t e => do some (.ifThen (← shimDuckDB s c) (← shimDuckDB s t) (← shimDuckDB s e))
  | .hof f l b => do some (.hof f (← shimDuckDB s l) (← shimDuckDB s b))

/-! ## The shim is correct -/

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

/-- A division or modulus of a number by zero raises in the reference. -/
theorem reference_divZero {f : BinFn} (hf : f.divides = true) (a : Int) :
    Profile.reference.bin f (.int a) (.int 0) = .error .divByZero := by
  cases f <;> simp_all [BinFn.divides, Profile.reference, raiseIf, BinFn.issue, Issue.isError]

/-- The guard's condition is true only for a number divided by zero. -/
theorem guard_true {p : Bool} {y : Value}
    (h : (and3 (.bool p) (BinFn.apply .eq y (.int 0))).isTrue = true) : p = true ∧ y = .int 0 := by
  cases p <;> simp [and3, Value.isTrue] at h
  cases y <;> simp_all [BinFn.apply]
  rename_i i
  by_cases hi : i = 0
  · exact hi
  · have hb : (i == 0) = false := by simpa using hi
    rw [hb] at h; exact absurd h (by decide)

/-- `=` and `AND` never raise on DuckDB. -/
theorem duckdb_eq (s : DuckDBSettings) (y z : Value) :
    (Profile.duckdb s).bin .eq y z = .ok (BinFn.apply .eq y z) := by
  simp only [Profile.duckdb]
  split <;> simp [BinFn.divides, Profile.reference, raiseIf, BinFn.issue]

theorem duckdb_isNum (s : DuckDBSettings) (x : Value) :
    (Profile.duckdb s).un .isNum x = .ok (.bool x.isNum) := by
  simp [Profile.duckdb, Profile.reference, raiseIf, UnFn.issue, UnFn.apply_isNum]

theorem duckdb_raise (s : DuckDBSettings) (m : String) (x : Value) :
    (Profile.duckdb s).un (.raise m) x = .error .raised := by
  simp [Profile.duckdb, Profile.reference, raiseIf, UnFn.issue, Issue.isError]

theorem duckdb_and (s : DuckDBSettings) (u v : Value) :
    (Profile.duckdb s).bin .and u v = .ok (BinFn.apply .and u v) := by
  simp only [Profile.duckdb]
  split <;> simp [BinFn.divides, Profile.reference, raiseIf, BinFn.issue]

/-- With the guard's condition false, DuckDB's division is the reference's. -/
theorem duckdb_bin_of_not_zero (s : DuckDBSettings) (f : BinFn) {x y : Value}
    (h : ¬(x.isNum = true ∧ y = .int 0)) : (Profile.duckdb s).bin f x y = Profile.reference.bin f x y := by
  simp only [Profile.duckdb]
  split
  · rename_i a; simp [Value.isNum] at h
  · rfl

/-- **DuckDB's shim is correct:** the shimmed expression, run under DuckDB's
profile with settings `s`, has the reference's outcome: the same value, or an
error. -/
theorem shimDuckDB_correct (s : DuckDBSettings) :
    ∀ (e t : Expr), shimDuckDB s e = some t → ∀ row : Row,
      Outcome.Agree (t.evalP (Profile.duckdb s) row) (e.evalP Profile.reference row)
  | .lit _, t, h, _ => by simp only [shimDuckDB, Option.some.injEq] at h; subst h; exact Outcome.agree_refl _
  | .field _, t, h, _ => by simp only [shimDuckDB, Option.some.injEq] at h; subst h; exact Outcome.agree_refl _
  | .un f a, t, h, row => by
    simp only [shimDuckDB, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    exact Outcome.agree_bind (shimDuckDB_correct s a a' ha row) fun v => Outcome.agree_refl _
  | .bin f a b, t, h, row => by
    simp only [shimDuckDB, bind, Option.bind_eq_some_iff] at h
    obtain ⟨a', ha, b', hb, h⟩ := h
    have iha := shimDuckDB_correct s a a' ha row
    have ihb := shimDuckDB_correct s b b' hb row
    split at h
    · rename_i hd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      simp only [Option.some.injEq] at h; subst h
      simp only [Expr.evalP, Expr.evalP]
      cases hx : a'.evalP (Profile.duckdb s) row <;> cases hx' : a.evalP Profile.reference row <;>
        rw [hx, hx'] at iha <;> simp only [Outcome.Agree] at iha
      · -- `a` raises in both.
        simp only [bind, Except.bind]; trivial
      · subst iha
        cases hy : b'.evalP (Profile.duckdb s) row <;> cases hy' : b.evalP Profile.reference row <;>
          rw [hy, hy'] at ihb <;> simp only [Outcome.Agree] at ihb
        · -- `b` raises in both.
          simp only [bind, Except.bind]; trivial
        · subst ihb
          rename_i x y
          simp only [bind, Except.bind, duckdb_eq, duckdb_and, duckdb_isNum, duckdb_raise]
          split
          · -- The guard raises: a number divided by zero, which raises in the reference.
            rename_i hc
            obtain ⟨hn, rfl⟩ := guard_true (by simpa [BinFn.apply] using hc)
            cases x <;> simp [Value.isNum] at hn
            rw [reference_divZero hd.1]; trivial
          · rename_i hc
            have : ¬(x.isNum = true ∧ y = .int 0) := by
              rintro ⟨hn, rfl⟩
              cases x <;> simp_all [Value.isNum, BinFn.apply, and3, Value.isTrue]
            rw [duckdb_bin_of_not_zero s f this]; exact Outcome.agree_refl _
    · simp only [Option.some.injEq] at h; subst h
      simp only [Expr.evalP, Expr.evalP]
      refine Outcome.agree_bind iha fun x => Outcome.agree_bind ihb fun y => ?_
      rename_i hd
      have : (Profile.duckdb s).bin f x y = Profile.reference.bin f x y := by
        simp only [Profile.duckdb]
        split
        · simp_all
        · rfl
      rw [this]; exact Outcome.agree_refl _
  | .ifThen c t' e, t, h, row => by
    simp only [shimDuckDB, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c', hc, t'', ht, e', he, rfl⟩ := h
    simp only [Expr.evalP, Expr.evalP]
    refine Outcome.agree_bind (shimDuckDB_correct s c c' hc row) fun v => ?_
    split
    · exact shimDuckDB_correct s t' t'' ht row
    · exact shimDuckDB_correct s e e' he row
  | .hof f l b, t, h, row => by
    simp only [shimDuckDB, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l', hl, b', hb, rfl⟩ := h
    simp only [Expr.evalP, Expr.evalP]
    exact Outcome.agree_bind (shimDuckDB_correct s l l' hl row) fun v =>
      HoFn.applyP_agree f v fun x => shimDuckDB_correct s b b' hb [x]

end Substrait
