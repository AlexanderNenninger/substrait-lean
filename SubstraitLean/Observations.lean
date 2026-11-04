import Lean.Data.Json
import SubstraitLean.Options

/-!
# Observations, classes and the reference's tools (#444)

Two columns next to each profile's choices (`docs/core-semantics.md`, D15),
and the reference's tool per option (D9).

* An observation `q` (D18) says what a consumer looks at: a product of
  components (rows, floats, zeros and NaNs, timestamps, strings, errors),
  each a short chain from exact to coarse. `q'` refines `q` (`Obs.le q' q`)
  when it observes everything `q` does, componentwise; the identity
  (`Obs.exact`) is the finest.
* A profile's row at a group and option (`ObsRow`) gives its class against
  the reference (#568: refines, refines up to `q`, approx, refused), the
  finest `q` it is equal up to, the shim that gets it there, if any, and the
  evidence: a Lean proof, or a test or fact. The engine profiles fill these
  (step 3a); the reference refines itself exactly.
* The tool table: per option, whether the reference raises, chooses a value
  or leaves it open, and the precondition a raise puts on every plan that
  meets it. `SubstraitLean/EngineTables.lean` adds each engine's shim count. -/

namespace Substrait

/-! ## Observations -/

/-- Rows: as a sequence, as a sequence up to the order of rows that tie in
the plan's order, or as a multiset (their order forgotten). -/
inductive RowsObs | sequence | tiesPermuted | multiset
  deriving Repr, DecidableEq

/-- A list's elements: as a sequence, or as a multiset. -/
inductive ElemsObs | sequence | multiset
  deriving Repr, DecidableEq

/-- Decimals: with their scale, or by value (`1.50` is `1.5`). -/
inductive DecObs | exact | value
  deriving Repr, DecidableEq

/-- Doubles: exactly, or within a named error bound (#85's, an ulp count). -/
inductive FloatObs | exact | within (bound : String)
  deriving Repr, DecidableEq

/-- Zeros and NaNs: as they are, or up to `canon` (one zero, one NaN, D4). -/
inductive ZeroNaNObs | exact | canon
  deriving Repr, DecidableEq

/-- A timestamp's precision. -/
inductive TimeUnit | ns | us | ms | s
  deriving Repr, DecidableEq

def TimeUnit.rank : TimeUnit → Nat
  | .ns => 0 | .us => 1 | .ms => 2 | .s => 3

/-- Timestamps: exactly, or truncated to a unit. -/
inductive TimeObs | exact | truncated (unit : TimeUnit)
  deriving Repr, DecidableEq

/-- Strings: exactly, up to NFC, or up to case folding (which normalises). -/
inductive StringObs | exact | nfc | casefold
  deriving Repr, DecidableEq

/-- Errors: which error, only its kind, or only that it raises. -/
inductive ErrorObs | exact | kind | raises
  deriving Repr, DecidableEq

/-- An observation: one level per component. -/
structure Obs where
  rows : RowsObs := .sequence
  elements : ElemsObs := .sequence
  floats : FloatObs := .exact
  zeros : ZeroNaNObs := .exact
  times : TimeObs := .exact
  strings : StringObs := .exact
  errors : ErrorObs := .exact
  decimals : DecObs := .exact
  deriving Repr, DecidableEq

/-- The identity: everything observed. -/
def Obs.exact : Obs := {}

def RowsObs.rank : RowsObs → Nat
  | .sequence => 0 | .tiesPermuted => 1 | .multiset => 2

def RowsObs.le (a b : RowsObs) : Bool := a.rank ≤ b.rank

def FloatObs.le : FloatObs → FloatObs → Bool
  | .exact, _ => true
  | .within b, .within b' => b == b'
  | .within _, .exact => false

def ZeroNaNObs.le : ZeroNaNObs → ZeroNaNObs → Bool
  | .exact, _ | .canon, .canon => true
  | .canon, .exact => false

def TimeObs.le : TimeObs → TimeObs → Bool
  | .exact, _ => true
  | .truncated u, .truncated u' => u.rank ≤ u'.rank
  | .truncated _, .exact => false

def StringObs.rank : StringObs → Nat
  | .exact => 0 | .nfc => 1 | .casefold => 2

def ErrorObs.rank : ErrorObs → Nat
  | .exact => 0 | .kind => 1 | .raises => 2

/-- **`q'` refines `q`**: it observes everything `q` does (D18), so equality
up to `q'` implies equality up to `q`. -/
def ElemsObs.le : ElemsObs → ElemsObs → Bool
  | .sequence, _ | .multiset, .multiset => true
  | .multiset, .sequence => false

def DecObs.le : DecObs → DecObs → Bool
  | .exact, _ | .value, .value => true
  | .value, .exact => false

def Obs.le (q' q : Obs) : Bool :=
  q'.rows.le q.rows && q'.elements.le q.elements && q'.decimals.le q.decimals &&
    q'.floats.le q.floats && q'.zeros.le q.zeros && q'.times.le q.times &&
    q'.strings.rank ≤ q.strings.rank && q'.errors.rank ≤ q.errors.rank

theorem Obs.le_refl (q : Obs) : q.le q = true := by
  obtain ⟨r, l, f, z, t, s, e, d⟩ := q
  cases r <;> cases l <;> cases f <;> cases z <;> cases t <;> cases d <;>
    simp [Obs.le, RowsObs.le, RowsObs.rank, ElemsObs.le, DecObs.le, FloatObs.le, ZeroNaNObs.le, TimeObs.le]

theorem Obs.le_trans {a b c : Obs} (hab : a.le b = true) (hbc : b.le c = true) : a.le c = true := by
  obtain ⟨r₁, l₁, f₁, z₁, t₁, s₁, e₁, d₁⟩ := a
  obtain ⟨r₂, l₂, f₂, z₂, t₂, s₂, e₂, d₂⟩ := b
  obtain ⟨r₃, l₃, f₃, z₃, t₃, s₃, e₃, d₃⟩ := c
  simp only [Obs.le, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, by omega⟩, by omega⟩
  · simp only [RowsObs.le, decide_eq_true_eq] at *; omega
  · cases l₁ <;> cases l₂ <;> cases l₃ <;> simp_all [ElemsObs.le]
  · cases d₁ <;> cases d₂ <;> cases d₃ <;> simp_all [DecObs.le]
  · cases f₁ <;> cases f₂ <;> cases f₃ <;> simp_all [FloatObs.le]
  · cases z₁ <;> cases z₂ <;> cases z₃ <;> simp_all [ZeroNaNObs.le]
  · cases t₁ <;> cases t₂ <;> cases t₃ <;> simp_all [TimeObs.le] <;> omega

theorem Obs.exact_le (q : Obs) : Obs.exact.le q = true := by
  obtain ⟨r, l, f, z, t, s, e, d⟩ := q
  cases r <;> cases l <;> cases f <;> cases z <;> cases t <;> cases d <;>
    simp [Obs.le, Obs.exact, RowsObs.le, RowsObs.rank, ElemsObs.le, DecObs.le, FloatObs.le, ZeroNaNObs.le,
      TimeObs.le, StringObs.rank, ErrorObs.rank]

/-! ## Classes -/

/-- A profile's function against the reference's (#568), best first. A shim
in the row makes the class "after a shim". -/
inductive Cls
  /-- Every outcome is one the reference allows, on the reference's
  non-raising domain. -/
  | refines
  /-- The same up to the row's observation `q`. -/
  | refinesUpTo
  /-- Within the row's float bound of an outcome the reference allows. -/
  | approx
  | refused
  deriving Repr, DecidableEq

/-- What a row rests on. -/
inductive Evidence
  /-- A Lean theorem, by name. -/
  | proved (thm : String)
  /-- A test, a probe or an engine fact, by id. -/
  | tested (ids : List String)
  /-- An engine fact whose evidence is a probe of the engine run for it, by id. -/
  | probed (ids : List String)
  | none
  deriving Repr, DecidableEq

/-- A profile's observation column at a group and option (D15). -/
structure ObsRow where
  cls : Cls
  /-- The finest observation the profile's function equals the reference's up to. -/
  q : Obs := Obs.exact
  /-- The shim that makes it so, if any: a written argument, a rewrite, a guard. -/
  shim : Option String := none
  evidence : Evidence := .none
  /-- What may differ between two runs of the engine on the same input (D20):
`some Obs.exact` where every run gives the same result, `none` where that is
not known. D10's determinism and the Python side's `rerun ⊑ q` check read it. -/
  rerun : Option Obs := none
  /-- What `rerun` rests on, apart from the class's evidence: a row can be
  proved to refine the reference and still vary run to run. -/
  rerunEvidence : Evidence := .none
  /-- Where the engine executes the row's functions, if not its default
  (Polars: streaming; `"in-memory"` where streaming falls back). -/
  engine : Option String := none
  /-- What the engine's behaviour rests on, beyond the reference's
  preconditions: proved from the bounds where possible, else checked on the
  data, as #575's are. -/
  precondition : String := ""
  /-- Why the row is as it is. -/
  note : String := ""
  deriving Repr, DecidableEq

/-- A row says what its class needs: `refines` is exact, `refinesUpTo` is
not, `approx` names a float bound. -/
def ObsRow.wf (r : ObsRow) : Bool :=
  match r.cls with
  | .refines => r.q == Obs.exact
  | .refinesUpTo => r.q != Obs.exact
  | .approx => match r.q.floats with | .within _ => true | .exact => false
  | .refused => r.shim.isNone

/-- The observation rows of each profile, keyed as its choices. -/
abbrev ObsTable := List (Option String × String × ObsRow)

/-- The row at `option` for a function of `group`: the group's own, else the option's. -/
def ObsTable.row? (t : ObsTable) (group option : String) : Option ObsRow :=
  match t.find? (fun (g, o, _) => g == some group && o == option) with
  | some (_, _, r) => some r
  | none => (t.find? (fun (g, o, _) => g.isNone && o == option)).map (·.2.2)

/-- The reference refines itself, exactly, at every option. -/
def Profile.reference.obs : ObsTable :=
  options.map fun o =>
    (none, o.id, { cls := .refines, evidence := .proved "Rel.allowedP_reference" })

/-! ## The reference's tools (D9) -/

/-- What the reference does at an option. -/
inductive Tool
  /-- Raise: a precondition for every plan that meets the option. -/
  | raise
  /-- Pick one value: a shim on every engine that picks another. -/
  | choose
  /-- Allow several: the contract must not tell them apart. -/
  | leaveOpen
  deriving Repr, DecidableEq

structure ToolRow where
  option : String
  tool : Tool
  /-- The precondition a raise creates (`""` for the other tools). -/
  precondition : String := ""
  /-- For an option left open, the coarsest observation a contract can hold
  under every choice: what it must not tell apart. -/
  q : Option Obs := none
  deriving Repr, DecidableEq

/-- The reference's tool per option (`docs/core-semantics.md`, "What
strictness buys"). -/
def Profile.reference.tools : List ToolRow := [
  { option := "overflow", tool := .raise,
    precondition := "every result fits its declared width: proved from the inferred bounds (#244), or a SUM's checked on the data (#316)" },
  { option := "on_division_by_zero", tool := .raise, precondition := "no divisor is 0" },
  { option := "division_type", tool := .choose },
  { option := "min_mod_neg_one", tool := .choose },
  { option := "shift_range", tool := .raise, precondition := "every shift count is in [0, 63]" },
  { option := "decimal_rescale", tool := .choose },
  { option := "rounding", tool := .choose },
  { option := "on_domain_error", tool := .raise,
    precondition := "every argument is in its function's domain" },
  { option := "on_log_zero", tool := .raise, precondition := "no logarithm of 0" },
  { option := "nan_creation", tool := .raise,
    precondition := "no operation makes a NaN of non-NaN values (∞ − ∞, 0 · ∞, ∞ / ∞, #257)" },
  { option := "zero_sign", tool := .choose },
  { option := "nan_equality", tool := .choose },
  { option := "nan_order", tool := .choose },
  { option := "nan_kind", tool := .choose },
  { option := "negative_start", tool := .choose },
  { option := "substring_range", tool := .raise,
    precondition := "every substring offset is in [-2³², 2³²) (#336)" },
  { option := "case_sensitivity", tool := .choose },
  { option := "char_set", tool := .choose },
  { option := "null_handling", tool := .choose },
  { option := "date_range", tool := .raise,
    precondition := "dates and timestamps stay in 0001-01-01 … 9999-12-31 (#251)" },
  { option := "time_interval_months", tool := .raise,
    precondition := "no interval with months is added to a TIME (the parser refuses it)" },
  { option := "list_null_order", tool := .choose },
  { option := "sum_order", tool := .leaveOpen, q := some { floats := .within "plan" } },
  { option := "stat_algo", tool := .leaveOpen, q := some { floats := .within "plan" } },
  { option := "stat_degenerate", tool := .choose },
  { option := "avg_int_result", tool := .choose },
  { option := "quantile_interp", tool := .leaveOpen, q := some { floats := .within "plan" } },
  -- The element multiset: which row of a tie, which order of a list's elements.
  { option := "tie_pick", tool := .leaveOpen, q := some { rows := .multiset } },
  { option := "tie_order", tool := .leaveOpen, q := some { rows := .multiset, elements := .multiset } },
  { option := "null_order", tool := .choose },
  { option := "clustered", tool := .leaveOpen, q := some { rows := .multiset } },
  { option := "ntile_spread", tool := .choose },
  { option := "float_to_int", tool := .choose },
  { option := "cast_failure", tool := .raise,
    precondition := "every value a cast with UNSPECIFIED failure behaviour converts" },
  { option := "distribution", tool := .choose },
  { option := "empty_group_aggregates", tool := .choose },
  { option := "float_overflow", tool := .raise,
    precondition := "no finite double operation overflows to ±∞: proved from the bounds, or checked on the data (#575)" },
  { option := "null_join_keys", tool := .choose },
  { option := "string_positions", tool := .choose }]

/-! ## Checks -/

/-- One tool per option, in the catalogue's order; a raise names its precondition. -/
example : Profile.reference.tools.map (·.option) = options.map (·.id) := by decide +kernel
example : Profile.reference.tools.all fun r => (r.tool == .raise) == (r.precondition != "") := by
  decide +kernel
/-- An open option names its observation; the others none. -/
example : Profile.reference.tools.all fun r => (r.tool == .leaveOpen) == r.q.isSome := by
  decide +kernel
/-- The options the reference leaves open are those whose choice allows any
order, value or row, a value of the core that sverify names for that. -/
example : Profile.reference.tools.all fun r => r.tool != .leaveOpen ||
    ((Profile.reference.table.dflt? r.option).any fun c =>
      (c.allows [] []).all (["ANY", "GENERIC", "BETWEEN", "ANY_ROW", "ADJACENT"].contains ·)) := by
  decide +kernel
/-- The reference's rows are well-formed. -/
example : Profile.reference.obs.all (·.2.2.wf) := by decide +kernel

/-! ## For Python -/

open Lean (Json toJson) in
def Obs.json (q : Obs) : Json :=
  Json.mkObj [
    ("rows", toJson (match q.rows with
      | .sequence => "sequence" | .tiesPermuted => "ties permuted" | .multiset => "multiset")),
    ("elements", toJson (match q.elements with | .sequence => "sequence" | .multiset => "multiset")),
    -- A named bound (#85's): the plan's own, which `verify`'s float bounds compute.
    ("floats", match q.floats with | .exact => toJson "exact" | .within b => Json.mkObj [("bound", toJson b)]),
    ("zeros", toJson (match q.zeros with | .exact => "exact" | .canon => "canon")),
    ("timestamps", toJson (match q.times with
      | .exact => "exact"
      | .truncated u => match u with | .ns => "ns" | .us => "us" | .ms => "ms" | .s => "s")),
    ("strings", toJson (match q.strings with | .exact => "exact" | .nfc => "nfc" | .casefold => "casefold")),
    ("decimals", toJson (match q.decimals with | .exact => "exact" | .value => "value")),
    ("errors", toJson (match q.errors with | .exact => "exact" | .kind => "kind" | .raises => "raises"))]

open Lean (Json toJson) in
/-- An observation as the Python side reads it (D18): only the components
that are not exact. -/
def Obs.sparseJson (q : Obs) : Json :=
  let full := q.json
  let keep := [("rows", q.rows != .sequence), ("elements", q.elements != .sequence),
    ("floats", q.floats != .exact), ("zeros", q.zeros != .exact),
    ("timestamps", q.times != .exact), ("strings", q.strings != .exact),
    ("decimals", q.decimals != .exact), ("errors", q.errors != .exact)]
  Json.mkObj (keep.filterMap fun (k, b) => if b then (full.getObjVal? k).toOption.map (k, ·) else none)

open Lean (Json toJson) in
def ObsRow.json (r : ObsRow) : Json :=
  Json.mkObj [
    ("class", toJson (match r.cls with
      | .refines => "refines" | .refinesUpTo => "refines_up_to" | .approx => "approx"
      | .refused => "refused")),
    ("q", r.q.json), ("shim", toJson r.shim),
    ("evidence", match r.evidence with
      | .proved t => Json.mkObj [("proved", toJson t)]
      | .tested ids => Json.mkObj [("tested", toJson ids)]
      | .probed ids => Json.mkObj [("probe", toJson ids)]
      | .none => Json.null)]

open Lean (Json toJson) in
def obsTableJson (t : ObsTable) : Json :=
  Json.arr <| (t.map fun (g, o, r) => Json.mkObj [
    ("group", toJson g), ("option", toJson o), ("row", r.json)]).toArray

end Substrait
