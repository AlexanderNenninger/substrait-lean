import SubstraitLean.Value

/-!
# Black-box functions (#325)

DuckDB has hundreds of functions that are hard or pointless to model exactly.
A **black box** is one the checker treats as opaque: no proof depends on what
it computes, only on what its row of the table below declares of it.

* its name (DuckDB's, and the Substrait extension function's, under the URN
  `blackBoxUrn`), its argument types and its result type;
* how it treats NULL: a scalar is `strict` (NULL in, NULL out) or not; an
  aggregate skips NULLs, as every aggregate does (`Measure.inputs`), and
  gives `empty` without values;
* whether a scalar may raise (`Raises`), which `verify` reports as a domain
  error (`UnFn.issue`);
* its **laws**: properties of the result the contract checker may use
  (`Law`), such as "not NULL" or "at least 0".

`UPPER`, `LOWER`, `ILIKE`, the regexes and the digests (`Text.lean`, #70,
#50) are black boxes written by hand; this table generalises them, so adding
a function means adding a row (`CLAUDE.md`, "Adding functions").

## What is proved and what is assumed

The function itself is `rawScalar`/`rawAgg`, an `opaque` constant: the kernel
knows nothing of it. The model's value is that function **where it keeps the
declared laws**, and the row's `sample` elsewhere (`Scalar.call`,
`Aggregate.call`), as `varOf` keeps a variance at `0` or above. So every law
is a theorem of the model (`Scalar.call_ok`, `Aggregate.call_ok`), proved
from the table (`scalars_wf`, `aggregates_wf`, by `decide`), and there is no
`axiom`.

What is assumed is that an engine computes the model's function: that
DuckDB's function keeps the laws, and is the one the plan calls. That is
`Impl.Faithful` (`Guards.lean`) and the profile's agreement with the engine
(`Profile.lean`), the hypotheses the theorems about engines already take; the
differential tests pin each black box to DuckDB, and the laws are checked
on random data (`python/tests/test_black_box.py`).

Lean's evaluator computes the black boxes it has an evaluator for
(`evalScalar`, `base64`) and panics at the others, so `substrait-check`
refuses to print rows rather than print wrong ones.
-/

namespace Substrait.BlackBox

/-- The URN of sverify's black-box functions: Substrait has none of them. -/
def blackBoxUrn : String := "extension:io.sverify:black_box"

/-- The types of a black box's arguments and result. Doubles are their codes
(`SubstraitLean/Float.lean`). -/
inductive Ty where
  | int | double | str | bool
  /-- Any value (an aggregate's argument). -/
  | any
  deriving Repr, DecidableEq

/-- Is `v` NULL or a value of the type? -/
def Ty.has : Ty → Value → Bool
  | _, .null => true
  | .int, .int _ | .double, .int _ => true
  | .str, .str _ => true
  | .bool, .bool _ => true
  | .any, _ => true
  | _, _ => false

/-- A property of a black box's result that the contract checker may use. -/
inductive Law where
  /-- Not NULL: a scalar's where no argument is NULL, an aggregate's over
  values. -/
  | nonNull
  /-- At least `k`: an integer, or a double's code (`atLeast 0` is `≥ +0.0`;
  NaN is above every number). -/
  | atLeast (k : Int)
  /-- At most `k`, likewise. -/
  | atMost (k : Int)
  deriving Repr, DecidableEq

/-- Does the result `v` keep the law, where no argument is NULL (`set`) or
some may be? -/
def Law.holds (set : Bool) : Law → Value → Bool
  | .nonNull, v => !set || v != .null
  | .atLeast k, .int i => decide (k ≤ i)
  | .atMost k, .int i => decide (i ≤ k)
  | _, _ => true

/-- When a scalar black box may raise. -/
inductive Raises where
  | never
  /-- On some non-NULL arguments, which the function decides (`rawRaises`):
  a domain error (`Issue.domain`). -/
  | sometimes
  deriving Repr, DecidableEq

/-- A result of type `result` that keeps `laws`. -/
def ok (result : Ty) (laws : List Law) (set : Bool) (v : Value) : Bool :=
  result.has v && laws.all fun l => l.holds set v

/-- A scalar black box. -/
structure Scalar where
  /-- DuckDB's name, and the extension function's. -/
  name : String
  args : List Ty
  result : Ty
  /-- NULL in, NULL out. -/
  strict : Bool := true
  raises : Raises := .never
  laws : List Law := []
  /-- A result the laws allow where no argument is NULL: the witness that
  they are consistent (`scalars_wf`). -/
  sample : Value
  deriving Repr

/-- An aggregate black box. NULLs are skipped (`Measure.inputs`); aggregates
do not raise. -/
structure Aggregate where
  name : String
  arg : Ty
  result : Ty
  /-- The result without values: NULL, or a constant (`entropy` gives `0.0`). -/
  empty : Value := .null
  /-- Hold over values (there is at least one). -/
  laws : List Law := []
  /-- A result the laws allow (`aggregates_wf`). -/
  sample : Value
  deriving Repr

/-! ## The table

A row per function. `CLAUDE.md` ("Adding functions") says what else a new
row needs: its lift rule and its SQL, both from the row's name. -/

/-- The scalar black boxes. -/
def scalars : List Scalar := [
  -- `base64(encode(s))`: the UTF-8 bytes of `s` in base64 (DuckDB's `base64`
  -- takes a BLOB). Not NULL for a string.
  { name := "base64", args := [.str], result := .str, laws := [.nonNull], sample := .str "" }]

/-- The aggregate black boxes. -/
def aggregates : List Aggregate := [
  -- `entropy(x)`: the Shannon entropy, in bits, of the counts of the
  -- distinct values; `0.0` without values. A double at least `+0.0`.
  { name := "entropy", arg := .any, result := .double, empty := .int 0,
    laws := [.nonNull, .atLeast 0], sample := .int 0 }]

/-- Each name once, a scalar's or an aggregate's. -/
example : (scalars.map (·.name) ++ aggregates.map (·.name)).Nodup := by decide

/-- **The laws are consistent**: each row's sample keeps them. -/
theorem scalars_wf : ∀ f ∈ scalars, ok f.result f.laws true f.sample = true := by decide

theorem aggregates_wf : ∀ f ∈ aggregates,
    ok f.result f.laws true f.sample = true ∧ f.result.has f.empty = true := by decide

def scalar? (name : String) : Option Scalar := scalars.find? (·.name == name)
def aggregate? (name : String) : Option Aggregate := aggregates.find? (·.name == name)

/-! ## Lean's evaluators -/

def b64Digit (n : Nat) : Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.getD n '='

/-- Bytes in base64, padded with `=` (RFC 4648). -/
def base64Bytes : List UInt8 → List Char
  | [] => []
  | [a] =>
    let n := a.toNat * 65536
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), '=', '=']
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), b64Digit (n / 64 % 64), '=']
  | a :: b :: c :: r =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), b64Digit (n / 64 % 64), b64Digit (n % 64)] ++
      base64Bytes r

/-- `base64(encode(s))`. -/
def base64 (s : String) : String := String.ofList (base64Bytes s.toUTF8.toList)

#guard base64 "" == "" && base64 "f" == "Zg==" && base64 "fo" == "Zm8=" && base64 "foo" == "Zm9v"
#guard base64 "foobar" == "Zm9vYmFy" && base64 "é" == "w6k="

def unevaluated {α : Type} [Inhabited α] (name : String) : α :=
  panic! s!"{name} is a black box Lean does not evaluate"

/-- The scalar black boxes Lean evaluates. -/
def evalScalar : String → List Value → Value
  | "base64", [.str s] => .str (base64 s)
  | name, _ => unevaluated name

def evalAgg (name : String) (_ : List Value) : Value := unevaluated name

def evalRaises (name : String) (_ : List Value) : Bool := unevaluated name

/-! ## The functions -/

/-- The scalar black box `name` of the arguments: the kernel knows nothing of it. -/
@[implemented_by evalScalar] opaque rawScalar : String → List Value → Value

/-- The aggregate black box `name` of the values (non-NULL, at least one, in
the order the engine takes them). -/
@[implemented_by evalAgg] opaque rawAgg : String → List Value → Value

/-- Does the scalar black box `name` raise on these (non-NULL) arguments? -/
@[implemented_by evalRaises] opaque rawRaises : String → List Value → Bool

/-- The model's value of a scalar black box: NULL for a NULL argument of a
strict one, else the function where it keeps the laws. -/
def Scalar.call (f : Scalar) (vs : List Value) : Value :=
  if f.strict && vs.contains .null then .null else
    let v := rawScalar f.name vs
    if ok f.result f.laws (!vs.contains .null) v then v else f.sample

/-- Does the scalar raise on these arguments? -/
def Scalar.raisesOn (f : Scalar) (vs : List Value) : Bool :=
  f.raises == .sometimes && !vs.contains .null && rawRaises f.name vs

/-- The model's value of an aggregate black box of non-NULL values. -/
def Aggregate.call (f : Aggregate) (vs : List Value) : Value :=
  if vs.isEmpty then f.empty else
    let v := rawAgg f.name vs
    if ok f.result f.laws true v then v else f.sample

/-- The scalar black box `name`, NULL for a name without a row. -/
def callScalar (name : String) (vs : List Value) : Value :=
  match scalar? name with
  | some f => f.call vs
  | none => .null

def raisesOn (name : String) (vs : List Value) : Bool :=
  match scalar? name with
  | some f => f.raisesOn vs
  | none => false

/-- May the scalar black box `name` raise at all? -/
def mayRaise (name : String) : Bool := (scalar? name).any (·.raises == .sometimes)

def callAgg (name : String) (vs : List Value) : Value :=
  match aggregate? name with
  | some f => f.call vs
  | none => .null

/-! ## The laws hold -/

theorem Law.holds_of_set {l : Law} {v : Value} (h : l.holds true v = true) (set : Bool) :
    l.holds set v = true := by
  cases l <;> cases v <;> cases set <;> simp_all [Law.holds]

theorem ok_of_set {result : Ty} {laws : List Law} {v : Value} (h : ok result laws true v = true)
    (set : Bool) : ok result laws set v = true := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun l hl => Law.holds_of_set (h.2 l hl) set⟩

theorem ok_null {result : Ty} {laws : List Law} : ok result laws false .null = true := by
  simp only [ok, Ty.has, Bool.true_and, List.all_eq_true]
  intro l _; cases l <;> rfl

theorem scalar?_mem {name : String} {f : Scalar} (h : scalar? name = some f) : f ∈ scalars :=
  List.mem_of_find?_eq_some h

theorem aggregate?_mem {name : String} {f : Aggregate} (h : aggregate? name = some f) :
    f ∈ aggregates :=
  List.mem_of_find?_eq_some h

/-- **A scalar black box keeps its laws.** -/
theorem Scalar.call_ok {f : Scalar} (hf : f ∈ scalars) (vs : List Value) :
    ok f.result f.laws (!vs.contains .null) (f.call vs) = true := by
  unfold Scalar.call
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [h.2]; exact ok_null
  · simp only
    split
    · assumption
    · exact ok_of_set (scalars_wf f hf) _

/-- **An aggregate black box keeps its laws** over values. -/
theorem Aggregate.call_ok {f : Aggregate} (hf : f ∈ aggregates) {vs : List Value}
    (hne : vs ≠ []) : ok f.result f.laws true (f.call vs) = true := by
  unfold Aggregate.call
  simp only [List.isEmpty_iff, hne, ite_false]
  split
  · assumption
  · exact (aggregates_wf f hf).1

theorem Aggregate.call_nil (f : Aggregate) : f.call [] = f.empty := rfl

theorem mayRaise_of_raisesOn {name : String} {vs : List Value} (h : raisesOn name vs = true) :
    mayRaise name = true := by
  unfold raisesOn at h; unfold mayRaise
  cases hs : scalar? name <;> simp_all [Scalar.raisesOn]

/-! ## The examples' laws, as theorems -/

/-- `base64` of a string is a string. -/
theorem base64_str (s : String) : ∃ t, callScalar "base64" [.str s] = .str t := by
  have hf : scalar? "base64" = some (scalars.head (by decide)) := rfl
  have h := Scalar.call_ok (scalar?_mem hf) [.str s]
  simp only [callScalar, hf]
  generalize Scalar.call _ _ = v at h
  cases v <;> simp_all [ok, Ty.has, Law.holds, scalars]

/-- `entropy` over values is a double at least `+0.0`. -/
theorem entropy_nonneg {vs : List Value} (hne : vs ≠ []) :
    ∃ c, callAgg "entropy" vs = .int c ∧ 0 ≤ c := by
  have hf : aggregate? "entropy" = some (aggregates.head (by decide)) := rfl
  have h := Aggregate.call_ok (aggregate?_mem hf) hne
  simp only [callAgg, hf]
  generalize Aggregate.call _ _ = v at h
  cases v <;> simp_all [ok, Ty.has, Law.holds, aggregates]

end Substrait.BlackBox
