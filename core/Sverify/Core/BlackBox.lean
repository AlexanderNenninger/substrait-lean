import Sverify.Core.Value
import Sverify.Core.Reflect

/-!
# Black-box functions (#325)

Engines have hundreds of functions that are hard or pointless to model
exactly. A **black box** is one the checker treats as opaque: no proof
depends on what it computes, only on what its row of a **black-box
catalogue** (`Boxes`) declares of it:

* its name (the engine's, and the Substrait extension function's, under the
  URN `blackBoxUrn`), its argument types and its result type;
* how it treats NULL: a scalar is `strict` (NULL in, NULL out) or not; an
  aggregate skips NULLs, as every aggregate does (`Measure.inputs`), and
  gives `empty` without values;
* whether a scalar may raise (`Raises`), which `verify` reports as a domain
  error (`UnFn.issue`);
* its **laws**: properties of the result the contract checker may use
  (`Law`), such as "not NULL" or "at least 0";
* the function itself, `eval`, which the engine package supplies (#1189).

The core holds the mechanism only. The rows are an engine package's:
DuckDB's are `Boxes.duckdb` (`SubstraitLean/DuckDBBoxes.lean`).

## What is proved and what is assumed

The model's value of a row is its `eval` **where it keeps the declared
laws**, and the row's `sample` elsewhere (`Scalar.call`, `Aggregate.call`),
as `varOf` keeps a variance at `0` or above. So every law is a theorem of the
model (`Scalar.call_ok`, `Aggregate.call_ok`), from the catalogue's
well-formedness `Boxes.WF`: each sample keeps its row's laws, which an engine
package proves by reflection (`Reflect.lean`). There is no `axiom`.

What is assumed is that an engine computes its rows' functions: that the
engine's function keeps the laws, and is the one the plan calls. That is
`Impl.Faithful` (`Guards.lean`) and the profile's agreement with the engine,
the hypotheses the theorems about engines already take.
-/

namespace Substrait.BlackBox

/-- The URN of sverify's black-box functions: Substrait has none of them. -/
def blackBoxUrn : String := "extension:io.sverify:black_box"

/-- The types of a black box's arguments and result. Doubles are their codes
(`core/Sverify/Core/Float.lean`). -/
inductive Ty where
  | int | double | str | bool
  /-- A date, as days since 1970-01-01. -/
  | date
  /-- A timestamp, as microseconds since 1970-01-01 (#806). -/
  | timestamp
  /-- An integer, string or boolean: a value whose type its `Value` shows.
  A double's code or a date is an integer too, so a scalar whose result
  depends on the type (`printf`) takes this. -/
  | atom
  /-- A list of doubles (their codes) or of integers, NULLs among them. -/
  | doubles | ints
  /-- A list of strings, NULLs among them. -/
  | strs
  /-- Any value (an aggregate's argument). -/
  | any
  deriving Repr, DecidableEq

/-- Is `v` NULL or an integer: an element of `ints`? -/
def intOrNull : Value → Bool
  | .null | .int _ => true
  | _ => false

/-- Is `v` NULL or a double: an element of `doubles`? -/
def floatOrNull : Value → Bool
  | .null | .float _ => true
  | _ => false

/-- Is `v` NULL or a string: an element of `strs`? -/
def strOrNull : Value → Bool
  | .null | .str _ => true
  | _ => false

/-- Is `v` NULL or a value of the type? -/
def Ty.has : Ty → Value → Bool
  | _, .null => true
  | .int, .int _ | .double, .float _ | .date, .date _ | .timestamp, .ts _ => true
  | .str, .str _ => true
  | .bool, .bool _ => true
  | .atom, .int _ | .atom, .float _ | .atom, .date _ | .atom, .ts _ | .atom, .tod _
  | .atom, .dec _ _ | .atom, .str _ | .atom, .bool _ => true
  | .doubles, .list vs => vs.all floatOrNull
  | .ints, .list vs => vs.all intOrNull
  | .strs, .list vs => vs.all strOrNull
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
  | .atLeast k, .int i | .atLeast k, .float i | .atLeast k, .date i | .atLeast k, .ts i
  | .atLeast k, .tod i | .atLeast k, .dec _ i => decide (k ≤ i)
  | .atMost k, .int i | .atMost k, .float i | .atMost k, .date i | .atMost k, .ts i
  | .atMost k, .tod i | .atMost k, .dec _ i => decide (i ≤ k)
  | _, _ => true

/-- When a scalar black box may raise. -/
inductive Raises where
  | never
  /-- On some non-NULL arguments, which the function decides (`Scalar.raises?`):
  a domain error (`Issue.domain`). -/
  | sometimes
  deriving Repr, DecidableEq

/-- A result of type `result` that keeps `laws`. -/
def ok (result : Ty) (laws : List Law) (set : Bool) (v : Value) : Bool :=
  result.has v && laws.all fun l => l.holds set v

/-- A scalar black box: its row, and its function, which the engine package
supplies. -/
structure Scalar where
  /-- The engine's name, and the extension function's. -/
  name : String
  args : List Ty
  result : Ty
  /-- NULL in, NULL out. -/
  strict : Bool := true
  raises : Raises := .never
  laws : List Law := []
  /-- A result the laws allow where no argument is NULL: the witness that
  they are consistent (`Boxes.WF`). -/
  sample : Value
  /-- The function, of the arguments. -/
  eval : List Value → Value := fun _ => .null
  /-- Does it raise on these (non-NULL) arguments? Read only where `raises`
  is `sometimes`. -/
  raises? : List Value → Bool := fun _ => false

/-- An aggregate black box. NULLs are skipped (`Measure.inputs`). One that
may raise does so on some groups of values, which the function decides
(`raises?`): `verify` reports a domain error (`AggFn.makesNan`). -/
structure Aggregate where
  name : String
  arg : Ty
  result : Ty
  raises : Raises := .never
  /-- The result without values: NULL, or a constant (`entropy` gives `0.0`). -/
  empty : Value := .null
  /-- Hold over values (there is at least one). -/
  laws : List Law := []
  /-- A result the laws allow (`Boxes.WF`). -/
  sample : Value
  /-- The function, of the values (non-NULL, at least one, in the order the
  engine takes them). -/
  eval : List Value → Value := fun _ => .null
  /-- Does it raise on these values (non-NULL, at least one)? -/
  raises? : List Value → Bool := fun _ => false

end BlackBox

open BlackBox in
/-- **A black-box catalogue**: an engine package's black boxes, scalars and
aggregates. -/
structure Boxes where
  scalars : List Scalar := []
  aggregates : List Aggregate := []

instance : Inhabited Boxes := ⟨{}⟩

namespace Boxes
open BlackBox

/-- **A well-formed catalogue**: each row's sample keeps its laws, and an
aggregate's `empty` is of its result type. An engine package proves it by
reflection (`Boxes.wf_of_check`). -/
def WF (B : Boxes) : Prop :=
  (∀ f ∈ B.scalars, ok f.result f.laws true f.sample = true) ∧
    ∀ f ∈ B.aggregates, ok f.result f.laws true f.sample = true ∧ f.result.has f.empty = true

/-- The check `Boxes.WF` reflects. -/
def check (B : Boxes) : Bool :=
  B.scalars.all (fun f => ok f.result f.laws true f.sample) &&
    B.aggregates.all fun f => ok f.result f.laws true f.sample && f.result.has f.empty

theorem wf_of_check {B : Boxes} (h : B.check = true) : B.WF := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1, fun f hf => by simpa only [Bool.and_eq_true] using h.2 f hf⟩

/-- The rows' names, a scalar's or an aggregate's. -/
def names (B : Boxes) : List String :=
  B.scalars.map (·.name) ++ B.aggregates.map (·.name)

/-- The catalogue of several packages' rows, refused where a name appears
twice: a row's function cannot be compared, so two packages may not both
state one function. -/
def combine (bs : List Boxes) : Except String Boxes :=
  let B : Boxes := ⟨bs.flatMap (·.scalars), bs.flatMap (·.aggregates)⟩
  match B.names.filter (fun n => B.names.count n > 1) with
  | [] => .ok B
  | n :: _ => .error s!"the black box {n} has rows in more than one catalogue"

def scalar? (B : Boxes) (name : String) : Option Scalar :=
  B.scalars.find? (·.name == name)

def aggregate? (B : Boxes) (name : String) : Option Aggregate :=
  B.aggregates.find? (·.name == name)

end Boxes

namespace BlackBox

/-! ## The functions -/

/-- The model's value of a scalar black box: NULL for a NULL argument of a
strict one, else the function where it keeps the laws. -/
def Scalar.call (f : Scalar) (vs : List Value) : Value :=
  if f.strict && vs.contains .null then .null else
    let v := f.eval vs
    if ok f.result f.laws (!vs.contains .null) v then v else f.sample

/-- Does the scalar raise on these arguments? -/
def Scalar.raisesOn (f : Scalar) (vs : List Value) : Bool :=
  f.raises == .sometimes && !vs.contains .null && f.raises? vs

/-- The model's value of an aggregate black box of non-NULL values. -/
def Aggregate.call (f : Aggregate) (vs : List Value) : Value :=
  if vs.isEmpty then f.empty else
    let v := f.eval vs
    if ok f.result f.laws true v then v else f.sample

/-- Does the aggregate raise on these values? -/
def Aggregate.raisesOn (f : Aggregate) (vs : List Value) : Bool :=
  f.raises == .sometimes && !vs.isEmpty && f.raises? vs

/-- The scalar black box `name` of `B`, NULL for a name without a row. -/
def callScalar (B : Boxes) (name : String) (vs : List Value) : Value :=
  match B.scalar? name with
  | some f => f.call vs
  | none => .null

def raisesOn (B : Boxes) (name : String) (vs : List Value) : Bool :=
  match B.scalar? name with
  | some f => f.raisesOn vs
  | none => false

/-- May the scalar black box `name` raise at all? -/
def mayRaise (B : Boxes) (name : String) : Bool := (B.scalar? name).any (·.raises == .sometimes)

def callAgg (B : Boxes) (name : String) (vs : List Value) : Value :=
  match B.aggregate? name with
  | some f => f.call vs
  | none => .null

def aggRaisesOn (B : Boxes) (name : String) (vs : List Value) : Bool :=
  match B.aggregate? name with
  | some f => f.raisesOn vs
  | none => false

/-- May the aggregate black box `name` raise at all? -/
def aggMayRaise (B : Boxes) (name : String) : Bool :=
  (B.aggregate? name).any (·.raises == .sometimes)

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

theorem scalar?_mem {B : Boxes} {name : String} {f : Scalar} (h : B.scalar? name = some f) :
    f ∈ B.scalars :=
  List.mem_of_find?_eq_some h

theorem aggregate?_mem {B : Boxes} {name : String} {f : Aggregate}
    (h : B.aggregate? name = some f) : f ∈ B.aggregates :=
  List.mem_of_find?_eq_some h

/-- **A scalar black box keeps its laws**, given a sample that does. -/
theorem Scalar.call_ok {f : Scalar} (hs : ok f.result f.laws true f.sample = true)
    (vs : List Value) : ok f.result f.laws (!vs.contains .null) (f.call vs) = true := by
  unfold Scalar.call
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [h.2]; exact ok_null
  · simp only
    split
    · assumption
    · exact ok_of_set hs _

/-- **An aggregate black box keeps its laws** over values, given a sample
that does. -/
theorem Aggregate.call_ok {f : Aggregate} (hs : ok f.result f.laws true f.sample = true)
    {vs : List Value} (hne : vs ≠ []) : ok f.result f.laws true (f.call vs) = true := by
  unfold Aggregate.call
  simp only [List.isEmpty_iff, hne, ite_false]
  split
  · assumption
  · exact hs

theorem Aggregate.call_nil (f : Aggregate) : f.call [] = f.empty := rfl

/-- A row of a well-formed catalogue keeps its laws. -/
theorem Scalar.call_ok_of_wf {B : Boxes} (hB : B.WF) {f : Scalar} (hf : f ∈ B.scalars)
    (vs : List Value) : ok f.result f.laws (!vs.contains .null) (f.call vs) = true :=
  Scalar.call_ok (hB.1 f hf) vs

theorem Aggregate.call_ok_of_wf {B : Boxes} (hB : B.WF) {f : Aggregate}
    (hf : f ∈ B.aggregates) {vs : List Value} (hne : vs ≠ []) :
    ok f.result f.laws true (f.call vs) = true :=
  Aggregate.call_ok (hB.2 f hf).1 hne

theorem mayRaise_of_raisesOn {B : Boxes} {name : String} {vs : List Value}
    (h : raisesOn B name vs = true) : mayRaise B name = true := by
  unfold raisesOn at h; unfold mayRaise
  cases hs : B.scalar? name <;> simp_all [Scalar.raisesOn]

theorem aggMayRaise_of_aggRaisesOn {B : Boxes} {name : String} {vs : List Value}
    (h : aggRaisesOn B name vs = true) : aggMayRaise B name = true := by
  unfold aggRaisesOn at h; unfold aggMayRaise
  cases hs : B.aggregate? name <;> simp_all [Aggregate.raisesOn]

end Substrait.BlackBox
