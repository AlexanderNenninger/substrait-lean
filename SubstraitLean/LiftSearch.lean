import Lean
import SubstraitLean.Parse
import SubstraitLean.DuckDBSQL
import SubstraitLean.LoweringSearch
import SubstraitLean.LiftHint

/-!
# The lift generator (#268)

`generate_lift L : s using [lemmas]` builds, at build time, the table of what
DuckDB's SQL functions (`DuckFn`, `SubstraitLean/DuckDBSQL.lean`) lift to under
the semantics `s`: for each, a Substrait expression over its arguments that
the parser (`Parse.parseExpr`) reads as the same function. It is the lowering
search (`SubstraitLean/LoweringSearch.lean`) run backwards.

For each `DuckFn` it builds templates around a **core**:

* a Substrait call: a function of the right arity (`divide`, `sverify_fmod`,
  `log10`, `greatest_skip_null`, …) on the arguments as they are or cast to the
  result's type (Substrait's signatures take and give one type), with every
  assignment of the options the parser accepts (`Parse.optionAccepts`);
* the cast of the argument to the result's type;
* a constant of the result's type.

A core may sit under a chain of up to four **guards**, `CASE WHEN g THEN v
ELSE … END`, where `g` tests arguments (`IS [NOT] NULL`, `isnan`, `= 0`,
`< 0`, `0 <`, infinite, or two such tests of different arguments joined by
`AND`) and `v` is a constant (`NULL`, NaN, `±∞`, `-1`, `0`, `1`) or an
argument. The chain is built greedily on the sample rows: a guard fires only
where its value is right, and the chain catches every row the core gets
wrong. This states what Substrait's options cannot: DuckDB's `log(0)` is
`-∞`. Templates with fewer guards are tried first.

An aggregate (`DuckAgg`) lifts to measures and an expression that finishes
them: one measure (`avg` or `sum`), or the exact `sum` and the `count` divided
as doubles; each is read by `Parse.parseMeasure`, compared with
`DuckAgg.eval` on sample groups, and proved for every group.

Each candidate is read by the parser, evaluated on sample arguments under the
reference, and compared with `DuckFn.eval`; the first that agrees on all of
them is proved for every argument of the function's types. The entry is a
definition with that proof, so the kernel checks it.

Trusted: that the parser's output for the entry's JSON is the template the
proof is about. The parser is `partial`, so the kernel cannot run it; the
generator runs it (compiled, as `substrait-check` does) and records the result.

A function without an entry fails the build, and `L.coverage` lists it.
-/

namespace Substrait

-- The generator searches DuckDB's lift: DuckDB's black boxes (#1189).
open scoped Substrait.DuckDB
/-- A lift entry: the Substrait expression, as JSON over the arguments (field
references `0`, `1`, …), what the parser reads it as, and the proof that this
means what DuckDB's function means. -/
structure LiftEntry (s : Semantics) (f : DuckFn) where
  json : String
  tmpl : Expr
  agree : ∀ xs : List Value, DuckType.HaveAll f.args xs →
    (tmpl.evalP Profile.reference xs).Agree (DuckFn.eval s f xs)

theorem LiftEntry.of₁ {s : Semantics} {f : DuckFn} {t : DuckType} {tmpl : Expr}
    (hf : f.args = [t])
    (h : ∀ x, t.Has x → (tmpl.evalP Profile.reference [x]).Agree (DuckFn.eval s f [x])) :
    ∀ xs : List Value, DuckType.HaveAll f.args xs →
      (tmpl.evalP Profile.reference xs).Agree (DuckFn.eval s f xs) := by
  intro xs hx; rw [hf] at hx
  match xs, hx with
  | [x], hx => exact h x hx.1

theorem LiftEntry.of₂ {s : Semantics} {f : DuckFn} {t u : DuckType} {tmpl : Expr}
    (hf : f.args = [t, u])
    (h : ∀ x y, t.Has x → u.Has y →
      (tmpl.evalP Profile.reference [x, y]).Agree (DuckFn.eval s f [x, y])) :
    ∀ xs : List Value, DuckType.HaveAll f.args xs →
      (tmpl.evalP Profile.reference xs).Agree (DuckFn.eval s f xs) := by
  intro xs hx; rw [hf] at hx
  match xs, hx with
  | [x, y], hx => exact h x y hx.1 hx.2.1

/-- A lifted aggregate: measures over its argument (field `0`), and an
expression over their results (fields `0`, `1`, …) that finishes it, with the
proof that, on every group, this is what DuckDB's aggregate gives. -/
structure AggEntry (s : Semantics) (g : DuckAgg) where
  json : String
  measures : List Measure
  finish : Expr
  agree : ∀ vs : List Value, (∀ v ∈ vs, g.arg.Has v) →
    (finish.evalP Profile.reference (measures.map (·.eval (vs.map ([·]))))).Agree (.ok (g.eval s vs))

/-- A lift table: an entry for each function and aggregate under the
semantics, or none. -/
structure Lift (s : Semantics) where
  entry : (f : DuckFn) → Option (LiftEntry s f)
  agg : (g : DuckAgg) → Option (AggEntry s g)

namespace LiftSearch

open Lean Meta Elab Command Term
open LoweringSearch (prove simpArgs)

/-! ## Substrait JSON -/

def fieldJ (i : Nat) : Json :=
  Json.mkObj [("selection", Json.mkObj [
    ("directReference", Json.mkObj [("structField", Json.mkObj [("field", toJson i)])]),
    ("rootReference", Json.mkObj [])])]

def typeJ (t : String) : Json := Json.mkObj [(t, Json.mkObj [("nullability", "NULLABILITY_NULLABLE")])]

def castJ (t : String) (e : Json) : Json :=
  Json.mkObj [("cast", Json.mkObj [("type", typeJ t), ("input", e),
    ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]

def litJ (t : String) (v : Json) : Json := Json.mkObj [("literal", Json.mkObj [(t, v)])]

def nullJ (t : String) : Json := Json.mkObj [("literal", Json.mkObj [("null", typeJ t)])]

/-- The extension URN of a Substrait function. -/
def urnOf (name : String) : String :=
  if name == "sverify_fmod" then "extension:io.sverify:functions"
  else if ["equal", "lt", "is_null", "is_not_null", "is_nan", "greatest", "least",
      "greatest_skip_null", "least_skip_null"].contains name then
    "extension:io.substrait:functions_comparison"
  else if ["and", "or", "not"].contains name then "extension:io.substrait:functions_boolean"
  else if ["sin", "cos", "tan", "asin", "acos", "atan"].contains name then
    "extension:io.substrait:functions_arithmetic"
  else if ["floor", "ceil", "round"].contains name then "extension:io.substrait:functions_rounding"
  else if name == "count" then "extension:io.substrait:functions_aggregate_generic"
  else "extension:io.substrait:functions_arithmetic"

/-- Functions of two arguments of one type that candidates call. -/
def binaryNames : List String :=
  ["divide", "modulus", "sverify_fmod", "power", "greatest_skip_null", "least_skip_null",
   "greatest", "least"]

/-- The functions candidates call, with their anchors, signatures and
extension URNs: each of `binaryNames` on `i64` and on `fp64`, the logarithms,
and the guards' comparisons and connectives. -/
def functions : List (Nat × String × String) :=
  let typed := binaryNames.flatMap fun n => ["i64", "fp64"].map fun t => s!"{n}:{t}_{t}"
  let unary := (FMath.all.map (·.name) ++ ["floor"]).map (· ++ ":fp64")
  let guards := ["equal:any_any", "lt:any_any", "is_null:any", "is_not_null:any", "is_nan:fp64",
    "and:bool", "or:bool", "not:bool"]
  let aggs := ["avg:i64", "avg:fp64", "sum:i64", "sum:fp64", "count:any"]
  -- Last, so the anchors before them stay: only seeded templates call them.
  let arith := ["add:fp64_fp64", "subtract:fp64_fp64", "multiply:fp64_fp64"]
  (typed ++ unary ++ guards ++ aggs ++ arith).zipIdx.map fun (n, i) => (i + 1, n, urnOf (Parse.baseName n))

def fns : List (Nat × String) := functions.map fun (a, n, _) => (a, n)

def anchorOf (full : String) : Option Nat :=
  (functions.find? fun (_, n, _) => n == full).map (·.1)

/-- A call of `full` (`name:signature`); `none` if it is not in `functions`. -/
def callJ? (full : String) (args : List Json) (opts : List (String × String)) (out : String) :
    Option Json := do
  let a ← anchorOf full
  return Json.mkObj [("scalarFunction", Json.mkObj [
    ("functionReference", toJson a),
    ("outputType", typeJ out),
    ("arguments", Json.arr (args.map fun a => Json.mkObj [("value", a)]).toArray),
    ("options", Json.arr (opts.map fun (o, p) =>
      Json.mkObj [("name", toJson o), ("preference", Json.arr #[toJson p])]).toArray)])]

/-- A guard's call (its function is always in `functions`). -/
def callJ (full : String) (args : List Json) : Json :=
  (callJ? full args [] "boolean").getD .null

/-- A template with each call naming its function (`"function"`), for the
cache (`LiftHint`); `anchored` turns it back. -/
partial def named : Json → Json
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      if k == "functionReference" then
        let name := (v.getNat?.toOption).bind fun a => fns.lookup a
        ("function", match name with | some n => toJson n | none => v)
      else (k, named v))
  | .arr vs => .arr (vs.map named)
  | j => j

partial def anchored : Json → Option Json
  | .obj kvs => do
    let kvs ← kvs.toArray.toList.mapM fun (k, v) => do
      if k == "function" then return ("functionReference", toJson (← anchorOf (← v.getStr?.toOption)))
      else return (k, ← anchored v)
    return Json.mkObj kvs
  | .arr vs => do return .arr (← vs.mapM anchored)
  | j => some j

def ifJ (c t e : Json) : Json :=
  Json.mkObj [("ifThen", Json.mkObj [
    ("ifs", Json.arr #[Json.mkObj [("if", c), ("then", t)]]), ("else", e)])]

/-! ## Candidates -/

/-- The options a call may set, each with the preferences the parser accepts. -/
def optionChoices (name : String) (float : Bool) : List (List (String × String)) :=
  ["overflow", "on_division_by_zero", "on_domain_error", "on_log_zero", "rounding",
   "division_type"].foldl (fun acc o =>
    match Parse.optionAccepts name float o with
    | some (some ps) => acc.flatMap fun a => a :: ps.map fun p => a ++ [(o, p)]
    | _ => acc) [[]]

/-- What a guard may give: the result type's constants (`NULL`; NaN and `±∞`
for a double; `-1`, `0`, `1` for an integer) and the arguments of the result's
type. -/
def values (f : DuckFn) : List Json :=
  let t := f.result.substrait
  let consts := if f.result == .double then [nullJ t, litJ t "nan", litJ t "inf", litJ t "-inf"]
    else [nullJ t, litJ t (toJson (0 : Int)), litJ t (toJson (-1 : Int)), litJ t (toJson (1 : Int))]
  consts ++ (f.args.zipIdx.filter (·.1 == f.result)).map (fieldJ ·.2)

/-- The cores a template is built around: calls of the right arity on the
arguments, as they are or cast to the result's type, with every option
assignment the parser accepts; for one argument of another type, the cast
to the result's; and the result type's constants. -/
def cores (f : DuckFn) : List (String × Json × List (String × String)) :=
  let n := f.args.length
  let out := f.result.substrait
  -- Substrait's `modulus` has no `fp64` signature: the remainder of doubles is
  -- sverify's own `sverify_fmod` (#256).
  let names := if n == 1 then FMath.all.map (·.name)
    else binaryNames.filter fun m => !(m == "modulus" && f.result == .double)
  let asIs := (List.range n).map fieldJ
  let cast := (f.args.zip asIs).map fun (t, a) => if t == f.result then a else castJ out a
  -- Substrait's signatures for these functions take and give one type: an
  -- `i64` divide gives an `i64`, so a `fp64` result needs `fp64` arguments.
  let argss := [(asIs, f.args), (cast, f.args.map fun _ => f.result)].filter
    (fun (_, ts) => ts.all (· == f.result)) |>.eraseDups
  let callsOf := names.flatMap fun name => argss.flatMap fun (args, ts) =>
    let full := s!"{name}:{"_".intercalate (ts.map (·.substrait))}"
    (optionChoices name (f.result == .double)).filterMap fun opts =>
      (callJ? full args opts out).map fun j => (name, j, opts)
  let casts := if n == 1 && f.args != [f.result] then [("cast", castJ out (fieldJ 0), [])] else []
  let consts := ((values f).filter fun j => (j.getObjVal? "selection").toOption.isNone).map
    fun j => ("constant", j, [])
  casts ++ callsOf ++ consts

/-- Tests of the arguments a guard is built from: `IS [NOT] NULL` and
comparisons with `0`; for a double also with `±1`, `isnan`, infinite, and
"a finite fraction" (`floor(x) <> x`). A double's comparison also comes
guarded, `NOT isnan(x) AND …` and `NOT isnan(x) AND NOT infinite AND …`: a
proof cannot see what a native function gives for NaN or `±∞`, and Kleene
`AND` with a false first operand is false whatever follows. Each atom also
comes negated, but for the guarded comparisons. -/
def atomsOf (f : DuckFn) (i : Nat) : List Json :=
  let t := f.args.getD i .bigint
  let x := fieldJ i
  let ty := t.substrait
  let num (k : Int) := if t == .double then litJ ty (Json.num k) else litJ ty (toJson k)
  let cmp (k : Int) := [callJ "equal:any_any" [x, num k], callJ "lt:any_any" [x, num k],
    callJ "lt:any_any" [num k, x]]
  let base := [callJ "is_null:any" [x], callJ "is_not_null:any" [x]] ++ cmp 0
  if t == .double then
    let isNan := callJ "is_nan:fp64" [x]
    let isInf := callJ "or:bool" [callJ "equal:any_any" [x, litJ ty "inf"],
      callJ "equal:any_any" [x, litJ ty "-inf"]]
    let notNan := callJ "not:bool" [isNan]
    let notInf := callJ "not:bool" [isInf]
    let cmps := cmp 0 ++ cmp 1 ++ cmp (-1)
    let frac := callJ "and:bool" [notNan, notInf,
      callJ "not:bool" [callJ "equal:any_any" [callJ? "floor:fp64" [x] [] "fp64" |>.getD .null, x]]]
    let simple := base ++ cmp 1 ++ cmp (-1) ++ [isNan, isInf, frac]
    simple ++ simple.map (fun a => callJ "not:bool" [a]) ++
      cmps.map (fun c => callJ "and:bool" [notNan, c]) ++
      cmps.map (fun c => callJ "and:bool" [notNan, notInf, c])
  else base ++ base.map fun a => callJ "not:bool" [a]

/-- The guards: each argument's atoms, and pairs of atoms joined by `AND`, of
different arguments (`x < 0 AND y is a finite fraction`), or of the one
argument of a unary function. -/
def guards (f : DuckFn) : List Json :=
  let byArg := (List.range f.args.length).map (atomsOf f)
  let pairs := match byArg with
    | [as] => as.zipIdx.flatMap fun (a, i) => (as.drop (i + 1)).map fun b => callJ "and:bool" [a, b]
    | _ => byArg.zipIdx.flatMap fun (as, i) => (byArg.drop (i + 1)).flatMap fun bs =>
        as.flatMap fun a => bs.map fun b => callJ "and:bool" [a, b]
  byArg.flatten ++ pairs

/-! ## Samples -/

def sampleValues : DuckType → List Value
  | .bigint => [.null, .int 0, .int 1, .int (-1), .int 7, .int (-7), .int (2 ^ 63 - 1), .int (-(2 ^ 63))]
  | .tinyint => [.null, .int 0, .int 1, .int (-1), .int 127, .int (-128)]
  | .double => [.null, .float 0, .float (FloatCode.ofFloat 1.5), .float (FloatCode.ofFloat (-2.5)),
      .float (FloatCode.ofFloat 100), .float (FloatCode.ofFloat 0.5), .float (FloatCode.ofFloat (-2)),
      .float (FloatCode.ofFloat 2), .float (FloatCode.ofFloat (-0.5)), .float (FloatCode.ofFloat 1),
      .float (FloatCode.ofFloat (-1)), .float (FloatCode.ofFloat (-1.5)), .float (FloatCode.ofFloat 3.5),
      .float FloatCode.nan,
      .float FloatCode.posInf, .float FloatCode.negInf]

def sampleRows : List DuckType → List Row
  | [] => [[]]
  | t :: ts => (sampleValues t).flatMap fun v => (sampleRows ts).map (v :: ·)

/-! ## Turning a template into a Lean term

Special double codes become their constants (`FloatCode.nan`, …), so the
proofs reason about them rather than about their digits. -/

def valueTerm : Value → MetaM Lean.Expr
  | .null => pure (Lean.mkConst ``Value.null)
  | .bool b => pure (mkApp (Lean.mkConst ``Value.bool) (toExpr b))
  | .str s => pure (mkApp (Lean.mkConst ``Value.str) (toExpr s))
  | .int i => pure (mkApp (Lean.mkConst ``Value.int) (toExpr i))
  | .float i =>
    let c := if i == FloatCode.nan then Lean.mkConst ``FloatCode.nan
      else if i == FloatCode.posInf then Lean.mkConst ``FloatCode.posInf
      else if i == FloatCode.negInf then Lean.mkConst ``FloatCode.negInf
      else if i == FloatCode.one then Lean.mkConst ``FloatCode.one
      else if i == FloatCode.negOne then Lean.mkConst ``FloatCode.negOne
      else toExpr i
    pure (mkApp (Lean.mkConst ``Value.float) c)
  | .date i => pure (mkApp (Lean.mkConst ``Value.date) (toExpr i))
  | .ts i => pure (mkApp (Lean.mkConst ``Value.ts) (toExpr i))
  | .tod i => pure (mkApp (Lean.mkConst ``Value.tod) (toExpr i))
  | .dec s i => pure (mkApp2 (Lean.mkConst ``Value.dec) (toExpr s) (toExpr i))
  | .list _ | .struct _ => throwError "list literals in a lift template are not supported"

-- One type a line: a list derives only its first.
deriving instance Lean.ToExpr for FMath
deriving instance Lean.ToExpr for BitOp
deriving instance Lean.ToExpr for ListOp
deriving instance Lean.ToExpr for Time.DatePart
deriving instance Lean.ToExpr for Time.TimeUnit
deriving instance Lean.ToExpr for OverflowMode
deriving instance Lean.ToExpr for NumKind
deriving instance Lean.ToExpr for IntWidth
deriving instance Lean.ToExpr for UnFn
deriving instance Lean.ToExpr for BinFn
deriving instance Lean.ToExpr for HoFn
deriving instance Lean.ToExpr for DuckType
deriving instance Lean.ToExpr for DuckAgg
deriving instance Lean.ToExpr for Semantics

unsafe def evalSemanticsImpl (e : Lean.Expr) : TermElabM Semantics :=
  Meta.evalExpr Semantics (Lean.mkConst ``Semantics) e
@[implemented_by evalSemanticsImpl] opaque evalSemantics (e : Lean.Expr) : TermElabM Semantics

unsafe def evalDuckAggImpl (e : Lean.Expr) : TermElabM DuckAgg := Meta.evalExpr DuckAgg (Lean.mkConst ``DuckAgg) e
@[implemented_by evalDuckAggImpl] opaque evalDuckAgg (e : Lean.Expr) : TermElabM DuckAgg

unsafe def evalDuckFnImpl (e : Lean.Expr) : TermElabM DuckFn := Meta.evalExpr DuckFn (Lean.mkConst ``DuckFn) e
@[implemented_by evalDuckFnImpl] opaque evalDuckFn (e : Lean.Expr) : TermElabM DuckFn

partial def exprTerm : Substrait.Expr → MetaM Lean.Expr
  | .lit v => return mkApp (Lean.mkConst ``Substrait.Expr.lit) (← valueTerm v)
  | .field i => return mkApp (Lean.mkConst ``Substrait.Expr.field) (toExpr i)
  | .un f a => return mkApp2 (Lean.mkConst ``Substrait.Expr.un) (toExpr f) (← exprTerm a)
  | .bin f a b => return mkApp3 (Lean.mkConst ``Substrait.Expr.bin) (toExpr f) (← exprTerm a) (← exprTerm b)
  | .ifThen c t e =>
    return mkApp3 (Lean.mkConst ``Substrait.Expr.ifThen) (← exprTerm c) (← exprTerm t) (← exprTerm e)
  | .hof f l b => return mkApp3 (Lean.mkConst ``Substrait.Expr.hof) (toExpr f) (← exprTerm l) (← exprTerm b)

/-! ## The search -/

/-- Read a candidate as the parser does. -/
def parse (f : DuckFn) (j : Json) : Option Substrait.Expr :=
  let cols := f.args.map fun t => if t == .double then Kind.float else .int
  (Parse.parseExpr fns cols (f.args.map fun _ => 64) j).toOption

def agrees (want got : List Outcome) : Bool :=
  (want.zip got).all fun (w, g) => LoweringSearch.Outcome.agreeB g w

/-- The rows (by index) where a predicate holds, as a bit mask. -/
def mask (bs : List Bool) : Nat :=
  bs.zipIdx.foldl (fun m (b, i) => if b then m ||| (1 <<< i) else m) 0

def popcount (m : Nat) : Nat := (Nat.toDigits 2 m).count '1'

/-- The candidates, in order, that agree with the function on the samples: a
core, under a chain of up to four guards. Guards and what they give are read
once, and a chain is built greedily on masks of the sample rows: a guard may
fire only on rows no earlier guard caught and where what it gives is right,
and the chain must catch every row the core gets wrong. A guard that fixes no
row may go first to shield a later one (`x IS NaN` before `0 < x`). -/
def survivors (s : Semantics) (f : DuckFn) : List (Json × Substrait.Expr × String) := Id.run do
  let rows := sampleRows f.args
  let want := rows.map (DuckFn.eval s f)
  let good (e : Substrait.Expr) : Nat :=
    mask ((rows.zip want).map fun (r, w) => LoweringSearch.Outcome.agreeB (e.evalP Profile.reference r) w)
  let all := (1 <<< rows.length) - 1
  -- A core that is right alone needs no guards: most functions, and every
  -- one under the reference's semantics. Guards are read only otherwise.
  let direct := (cores f).filterMap fun (name, j, opts) => (parse f j).bind fun e =>
    if good e == all then some (j, e, s!"{name} {opts}") else none
  if !direct.isEmpty then return direct.take 12
  let gs := (guards f).filterMap fun j => (parse f j).map fun e =>
    (j, e, mask (rows.map fun r => match e.evalP Profile.reference r with
      | .ok v => v.isTrue | .error _ => false))
  let vs := (values f).filterMap fun j => (parse f j).map fun e => (j, e, good e)
  let base := gs.flatMap fun (gj, ge, gm) => vs.map fun (vj, ve, vm) => (gj, ge, gm, vj, ve, vm)
  -- Right wherever it fires among the rows `rem`.
  let ok (rem gm vm : Nat) := gm &&& rem &&& (all ^^^ vm) == 0
  let mut found := #[]
  for (name, j, opts) in cores f do
    let some e := parse f j | continue
    let label := s!"{name} {opts}"
    let mut rem := all
    let ge0 := good e
    let mut bad := all ^^^ ge0
    -- A guard may also give the core itself: a shield that keeps rows the
    -- core gets right from a later guard (`x is infinite` before `x < 0`).
    let shields := gs.map fun (gj, ge, gm) => (gj, ge, gm, j, e, ge0)
    let pairs := base
    let mut chain : Array (Json × Substrait.Expr × Json × Substrait.Expr) := #[]
    for _ in [0:6] do
      if bad == 0 then break
      -- The guard that fixes most of the rows still wrong.
      let fixes := pairs.filter fun (_, _, gm, _, _, vm) => ok rem gm vm && gm &&& bad != 0
      let best := fixes.foldl (fun acc p => match acc with
        | none => some p
        | some q =>
          -- Most rows fixed; then fewest rows caught, the narrower test.
          let (fp, fq) := (popcount (p.2.2.1 &&& bad), popcount (q.2.2.1 &&& bad))
          if fp > fq || (fp == fq && popcount (p.2.2.1 &&& rem) < popcount (q.2.2.1 &&& rem)) then some p
          else acc) none
      match best with
      | some (gj, ge, gm, vj, ve, _) =>
        chain := chain.push (gj, ge, vj, ve); rem := rem &&& (all ^^^ gm); bad := bad &&& (all ^^^ gm)
      | none =>
        -- A shield: right where it fires, and once its rows are caught, some
        -- guard fixes rows.
        let shield := shields.find? fun (_, _, gm, _, _, vm) =>
          ok rem gm vm && gm &&& rem != 0 &&
            pairs.any fun (_, _, gm2, _, _, vm2) =>
              ok (rem &&& (all ^^^ gm)) gm2 vm2 && gm2 &&& bad &&& (all ^^^ gm) != 0
        match shield with
        | some (gj, ge, gm, vj, ve, _) =>
          chain := chain.push (gj, ge, vj, ve); rem := rem &&& (all ^^^ gm); bad := bad &&& (all ^^^ gm)
        | none => break
    if bad == 0 then
      -- Drop the guards the chain does not need: one that, left out, leaves
      -- every sample row right (each row takes the first guard that fires).
      let masks : Array (Nat × Nat) := chain.map fun (_, ge, _, ve) =>
        let gm := mask (rows.map fun r => match ge.evalP Profile.reference r with
          | .ok v => v.isTrue | .error _ => false)
        let vm := good ve
        (gm, if ve == e then ge0 else vm)
      let right (keep : List Nat) : Bool := Id.run do
        let mut caught := 0
        for i in keep do
          let (gm, vm) := masks[i]!
          if gm &&& (all ^^^ caught) &&& (all ^^^ vm) != 0 then return false
          caught := caught ||| gm
        return (all ^^^ caught) &&& (all ^^^ ge0) == 0
      let mut keep := List.range chain.size
      for i in List.range chain.size do
        let fewer := keep.erase i
        if right fewer then keep := fewer
      chain := keep.toArray.map (chain[·]!)
      let tj := chain.foldr (fun (gj, _, vj, _) acc => ifJ gj vj acc) j
      let te := chain.foldr (fun (_, ge, _, ve) acc => Substrait.Expr.ifThen ge ve acc) e
      -- Fewer guards first: a long chain may fit the samples by accident. On a
      -- tie a constant core, which states the function by cases, before a
      -- call the guards hide.
      found := found.push (2 * chain.size + (if name == "constant" then 0 else 1), tj, te, label)
  return ((found.toList.zipIdx.mergeSort fun (a, i) (b, j) => a.1 < b.1 || (a.1 == b.1 && i ≤ j)).map
    (·.1.2)).take 12

/-! ## Proving and emitting -/

/-- The proof tactic: split on the arguments' kinds (dropping those outside
their types), evaluate both sides, split on the comparisons, and compute. -/
def liftTac (n : Nat) (extra : Array Name) : TermElabM Syntax := do
  let ev ← simpArgs (#[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``DuckFn.eval, ``DuckFn.meaning, ``DuckFn.evalOwn, ``Semantics.profile,
    ``DuckDBSQL.duck_fdiv_float, ``DuckDBSQL.duck_fmod_float, ``DuckDBSQL.duck_fadd_float,
    ``DuckDBSQL.duck_fsub_float, ``DuckDBSQL.duck_fmul_float, ``DuckDBSQL.duck_fpow_float,
    ``DuckDBSQL.duck_fmath_float, ``DuckDBSQL.duck_bin_null_l, ``DuckDBSQL.duck_bin_null_r,
    ``DuckDBSQL.duck_un_null, ``DuckDBSQL.duck_itof, ``duckElementary, ``FMath.isLog, ``duckSign,
    ``nanCase, ``negInfPow, ``duckNegInfPow, ``isInfCode, ``ieeeDivZero, ``DuckDBSQL.ref_itof_null, ``DuckDBSQL.ref_fdiv_float,
    ``DuckDBSQL.ref_fmod_float, ``DuckDBSQL.ref_fdiv_null_l, ``DuckDBSQL.ref_fdiv_null_r,
    ``DuckDBSQL.ref_fmod_null_l, ``DuckDBSQL.ref_fmod_null_r, ``DuckDBSQL.apply_eq_int,
    ``DuckDBSQL.apply_lt_int, ``DuckDBSQL.apply_eq_float, ``DuckDBSQL.apply_lt_float, ``DuckDBSQL.apply_eq_null_l, ``DuckDBSQL.apply_eq_null_r,
    ``DuckDBSQL.apply_lt_null_l, ``DuckDBSQL.apply_lt_null_r, ``Lowering.ref_eq, ``Lowering.ref_lt, ``Lowering.ref_greatest, ``Lowering.ref_least,
    ``BinFn.apply, ``Value.numPair, ``Value.pick, ``Value.ltB,
    ``Lowering.ref_and, ``Lowering.ref_or, ``FloatCode.ofInt_ne_nan, ``DuckDBSQL.ref_fpow_float,
    ``DuckDBSQL.ref_fpow_null_l, ``DuckDBSQL.ref_fpow_null_r, ``DuckDBSQL.ref_ffloor_float,
    ``DuckDBSQL.ref_ffloor_null, ``DuckDBSQL.ref_fadd_float, ``DuckDBSQL.ref_fsub_float,
    ``DuckDBSQL.ref_fmul_float, ``DuckDBSQL.ref_fadd_null_l, ``DuckDBSQL.ref_fadd_null_r,
    ``DuckDBSQL.ref_fsub_null_l, ``DuckDBSQL.ref_fsub_null_r, ``DuckDBSQL.ref_fmul_null_l,
    ``DuckDBSQL.ref_fmul_null_r,
    ``DuckDBSQL.ite_or, ``Value.isTrue, ``and3, ``or3, ``Lowering.beq_int, ``Lowering.ref_isNull,
    ``Lowering.ref_not, ``Issue.isError, ``DuckDBSQL.ref_itof, ``DuckDBSQL.ref_fmath_float,
    ``DuckDBSQL.ref_fmath_null, ``FloatCode.ofInt_ne_posInf, ``FloatCode.ofInt_ne_negInf,
    ``Bool.false_eq_true, ``ite_false, ``ite_true, ``Bool.or_false, ``Bool.false_or,
    ``Bool.and_false, ``Bool.false_and, ``Bool.or_true, ``Bool.true_and] ++ extra)
  let fin ← simpArgs (#[``Outcome.Agree, ``Issue.isError] ++ extra)
  let intro ← if n == 1 then `(tactic| (intro x hx; cases x <;> simp (config := { failIfUnchanged := false }) only [DuckType.Has] at hx))
    else `(tactic| (intro x y hx hy; cases x <;> cases y <;> simp (config := { failIfUnchanged := false }) only [DuckType.Has] at hx hy))
  let cheap ← simpArgs #[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``DuckFn.eval, ``DuckFn.meaning, ``DuckFn.evalOwn, ``Semantics.profile,
    ``DuckDBSQL.ref_itof]
  `(tactic| (
    $intro:tactic
    all_goals try (simp only [$cheap,*]; exact Outcome.agree_refl _)
    all_goals have := FloatCode.negInf_lt_zero
    all_goals have := FloatCode.zero_lt_posInf
    all_goals have := FloatCode.posInf_lt_nan
    all_goals have := FloatCode.one_lt_posInf
    all_goals have := FloatCode.zero_lt_one
    all_goals simp (config := { failIfUnchanged := false }) only [$ev,*, Int.reduceEq, Int.reduceLT,
      Int.reduceLE, Int.reduceNeg, Int.reduceAdd, Int.reduceSub, Nat.reduceEqDiff, decide_true,
      decide_false, Bool.not_true, Bool.not_false]
    iterate 16
      all_goals try
        lowering_split_decide <;>
          simp (config := { failIfUnchanged := false }) only [$(mkIdent `hd):ident, $ev,*,
            Int.reduceEq, Int.reduceLT, Int.reduceLE, Int.reduceNeg, decide_true, decide_false,
            Bool.not_true, Bool.not_false]
    all_goals (repeat' split)
    all_goals first
      | (simp_all [$fin,*]; done)
      | (simp_all [$fin,*] <;> omega)
      | omega))

/-- The generated module a function's entry goes to (`writing`): entries of an
area check in parallel, each in a process of its own. -/
def areaOf (c : Name) : String :=
  match c.componentsRev.head!.toString with
  | "divInt" | "divDouble" | "modDouble" | "power" => "Arith"
  | "elementary" => "Math"
  | "castDoubleBigint" | "castBigintDouble" => "Casts"
  | _ => "Compare"

syntax (name := liftTemplateTac) "lift_template " num " [" ident,* "]" : tactic
syntax (name := liftAggTac) "lift_agg" : tactic

open Tactic in
@[tactic liftTemplateTac] def evalLiftTemplate : Tactic := fun stx => do
  Generated.proveOrAdmit do
    let extra ← stx[3].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    evalTactic (← liftTac stx[1].isNatLit?.get! extra)

/-- Search for and emit the entry of `f` under `s`; how it lifts, or why not. -/
def liftOne (tbl : Name) (s : Semantics) (sE : Lean.Expr) (extra : Array Name)
    (k : LoweringSearch.Construct) (f : DuckFn) (hint? : Option LiftHint)
    (sink : Option LoweringSearch.Sink := none) : TermElabM (Except String String) := do
  let short := k.short
  let fE := mkAppN (Lean.mkConst k.ctor) (k.args.map Lean.mkConst)
  let n := f.args.length
  if let some why := f.refused s then return .error s!"refused: {why}"
  let tac ← liftTac n extra
  let firstWhy ← IO.mkRef (none : Option String)
  let liftCand (j : Json) (e : Substrait.Expr) (label : String) : TermElabM (Option String) := do
    -- The parser reads the whole candidate as its parts combined.
    unless parse f j == some e do return none
    let tmpl ← exprTerm e
    let argTs ← f.args.mapM fun t => pure (toExpr t)
    let ty ← withLocalDeclD `x (Lean.mkConst ``Value) fun x => withLocalDeclD `y (Lean.mkConst ``Value) fun y => do
      let xs := if n == 1 then #[x] else #[x, y]
      let row ← mkListLit (Lean.mkConst ``Value) xs.toList
      let lhs ← mkAppM ``Expr.evalP #[Lean.mkConst ``Profile.reference, row, tmpl]
      let rhs ← mkAppM ``DuckFn.eval #[sE, fE, row]
      let body ← mkAppM ``Outcome.Agree #[lhs, rhs]
      let hs ← (xs.zip argTs.toArray).mapM fun (v, t) => mkAppM ``DuckType.Has #[t, v]
      let body ← hs.foldrM (fun h b => mkArrow h b) body
      mkForallFVars xs body
    let pf ← match ← LoweringSearch.proveE ty tac with
      | .ok pf => pure pf
      | .error why =>
        -- The breadcrumb: why the first candidate failed.
        if (← firstWhy.get).isNone then firstWhy.set (some s!"{label}: {why}")
        return none
    let agreeName := tbl ++ short.appendAfter "_agree"
    addDecl <| .thmDecl { name := agreeName, levelParams := [], type := ty, value := pf }
    let hf ← mkEqRefl (← mkAppM ``DuckFn.args #[fE])
    let agree ← mkAppM (if n == 1 then ``LiftEntry.of₁ else ``LiftEntry.of₂) #[hf, Lean.mkConst agreeName]
    let entry ← mkAppM ``LiftEntry.mk #[toExpr j.compress, tmpl, agree]
    let entryTy ← inferType entry
    addAndCompile <| .defnDecl {
      name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
      type := entryTy, value := entry }
    if let some out := sink then
      out.modify (·.push (areaOf k.ctor,
        -- The check elaborates the statement too: twice the search's budget.
        "set_option maxHeartbeats 400000 in\n" ++
        s!"theorem {agreeName} : {← LoweringSearch.ppSource ty} := by\n  lift_tac{n}\n\n" ++
        s!"abbrev {tbl ++ short} : {← LoweringSearch.ppSource entryTy} :=\n" ++
        s!"  ⟨{repr j.compress}, {← LoweringSearch.ppSource tmpl},\n" ++
        s!"    Substrait.LiftEntry.of{if n == 1 then "₁" else "₂"} rfl {agreeName}⟩\n\n" ++
        -- The parser still reads the JSON as the template the proof is about
        -- (`sverify.sql_lift` writes the JSON): checked by the build.
        s!"#guard Substrait.LiftSearch.parse ({← LoweringSearch.ppSource fE})\n" ++
        s!"  ((Lean.Json.parse ({tbl ++ short}).json).toOption.getD Lean.Json.null) ==\n" ++
        s!"    some ({tbl ++ short}).tmpl\n\n"))
    return some s!"{label}: {j.compress}"
  -- The cache's template first, if it still agrees on the samples.
  if let some h := hint? then
    let some j := (Json.parse h.template).toOption.bind anchored | pure ()
    let some e := parse f j | pure ()
    let rows := sampleRows f.args
    if rows.all fun r => LoweringSearch.Outcome.agreeB (e.evalP Profile.reference r) (DuckFn.eval s f r) then
      let src := if h.source.startsWith "seeded" then "seeded" else "cached"
      if let some r ← withCurrHeartbeats (liftCand j e s!"{src}") then return .ok r
  let cands := survivors s f
  for (j, e, label) in cands do
    -- Evaluating and proving count as heartbeats; each candidate starts afresh.
    let some r ← withCurrHeartbeats (liftCand j e label) | continue
    return .ok r
  let why := ((← firstWhy.get).map fun w => s!"; the first failed with {(w.take 1500)}").getD ""
  return .error s!"missing: {cands.length} candidates passed the samples, none proved{why}"

/-- The functions a template's `functionReference`s point to, as JSON. -/
def functionsJson : Json :=
  Json.arr (functions.map fun (a, n, u) =>
    Json.mkObj [("anchor", toJson a), ("name", toJson n), ("urn", toJson u)]).toArray

/-! ## Aggregates -/

def measureJ? (full : String) (arg : Json) (out : String) : Option Json := do
  let a ← anchorOf full
  return Json.mkObj [("measure", Json.mkObj [("functionReference", toJson a),
    ("outputType", typeJ out), ("arguments", Json.arr #[Json.mkObj [("value", arg)]]),
    ("phase", "AGGREGATION_PHASE_INITIAL_TO_RESULT"),
    ("invocation", "AGGREGATION_INVOCATION_ALL")])]

/-- The candidates for an aggregate: one measure (`avg` or `sum`, of the
argument as it is or cast to the result's type, with the result's or the
argument's type), or the exact `sum` and the `count`, finished by dividing
the one by the other as doubles (with each `on_division_by_zero`). Each is
the measures' JSON, the finishing expression's, and what kinds the measures
give. -/
def aggCandidates (g : DuckAgg) : List (List Json × Json × List Kind) :=
  let t := g.arg.substrait
  let r := g.result.substrait
  let x := fieldJ 0
  let kindOf (ty : String) := if ty == "fp64" then Kind.float else .int
  let single := ["avg", "sum"].flatMap fun name => [(x, t), (castJ r x, r)].flatMap fun (a, ta) =>
    [r, t].filterMap fun out => (measureJ? s!"{name}:{ta}" a out).map fun m => ([m], fieldJ 0, [kindOf out])
  let pair := match measureJ? s!"sum:{t}" x t, measureJ? "count:any" x "i64" with
    | some sm, some cm => (optionChoices "divide" true).filterMap fun opts =>
      (callJ? "divide:fp64_fp64" [castJ "fp64" (fieldJ 0), castJ "fp64" (fieldJ 1)] opts r).map
        fun fin => ([sm, cm], fin, [kindOf t, .int])
    | _, _ => []
  single ++ pair

def aggSampleGroups (t : DuckType) : List (List Value) :=
  let vs := sampleValues t
  -- A number of the type: a double's code for `DOUBLE` (#923).
  let n (i : Int) : Value := if t == .double then .float (FloatCode.ofInt i) else .int i
  -- Large integers whose sum rounds as doubles: `2⁵³ + 1 + 1`.
  [[], [.null], [n 1], [n 1, n 2], [n (-5), n 3, .null], [n (2 ^ 53), n 1, n 1],
   [n (2 ^ 62), n (-(2 ^ 62)), n 3]] ++ vs.map ([·])

/-- Read an aggregate candidate as the parser does. -/
def parseAgg (g : DuckAgg) (ms : List Json) (fin : Json) (kinds : List Kind) :
    Option (List Measure × Substrait.Expr) := do
  let cols := [if g.arg == .double then Kind.float else .int]
  let measures ← ms.mapM fun mj => ((Parse.parseMeasure fns cols [64] mj).toOption.map (·.1))
  let finish ← (Parse.parseExpr fns kinds (kinds.map fun _ => 64) fin).toOption
  return (measures, finish)

deriving instance Lean.ToExpr for AggFn

def measureTerm (m : Measure) : MetaM Lean.Expr := do
  unless m.filter.isNone && m.sort.isEmpty do throwError "only plain measures are lifted"
  return mkAppN (Lean.mkConst ``Measure.mk) #[toExpr m.fn, ← exprTerm m.arg, toExpr m.distinct,
    mkApp (Lean.mkConst ``Option.none [Level.zero]) (Lean.mkConst ``Substrait.Expr),
    ← mkListLit (Lean.mkConst ``SortKey) []]

/-- The proof tactic for an aggregate: compute the measures on the group's
rows, then split on whether any value is not `NULL`. -/
def aggTac (_defs : Array Name) : TermElabM Syntax := do
  let ev ← simpArgs #[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``DuckDBSQL.ref_itof, ``DuckDBSQL.ref_itof_null, ``DuckDBSQL.ref_fdiv_float,
    ``DuckDBSQL.ref_fdiv_null_l, ``DuckDBSQL.ref_fdiv_null_r, ``AggFn.apply, ``nanCase, ``isInfCode,
    ``Substrait.Expr.evalP,
    ``Lowering.beq_int, ``FloatCode.ofInt_ne_posInf, ``FloatCode.ofInt_ne_negInf,
    ``Bool.false_eq_true, ``ite_false, ``ite_true, ``Bool.or_false, ``Bool.false_or,
    ``Bool.and_false, ``Bool.false_and, ``Outcome.Agree, ``List.length_cons, ``Lowering.ref_eq,
    ``Lowering.ref_lt, ``Lowering.ref_not, ``Lowering.ref_isNull, ``DuckDBSQL.apply_eq_int,
    ``DuckDBSQL.apply_lt_int, ``DuckDBSQL.apply_eq_float, ``DuckDBSQL.apply_lt_float, ``Value.isTrue, ``decide_false, ``Bool.not_false]
  `(tactic| (
    intro vs hvs
    simp only [List.map_cons, List.map_nil, Measure.eval, Measure.inputs, Measure.kept,
      List.map_map, Function.comp_def, Substrait.Expr.eval, List.getD_cons_zero, List.map_id',
      DuckAgg.eval, Bool.false_eq_true, ite_false]
    -- The values of a `BIGINT` column are integers (or NULL, left out).
    have hint : ∀ v ∈ List.filter (fun x => x != Value.null) vs, ∃ i, v = .int i := fun v hv => by
      obtain ⟨h1, h2⟩ := List.mem_filter.mp hv
      have := hvs v h1
      cases v <;> simp_all [DuckType.Has, DuckAgg.arg]
    first
      | (simp only [Substrait.Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind]
         exact Outcome.agree_refl _)
      | (generalize List.filter (fun x => x != Value.null) vs = xs at hint
         cases xs with
         | nil => simp [$ev,*]
         | cons x xs =>
           have hne := FloatCode.ofInt_ne_zero (i := ((xs.length + 1 : Nat) : Int)) (by omega)
           have hsum := DuckDBSQL.sumOf_int_vals hint
           simp only [$ev,*, hne, hsum, decide_false])))

open Tactic in
@[tactic liftAggTac] def evalLiftAgg : Tactic := fun _ => do
  Generated.proveOrAdmit do evalTactic (← aggTac #[])

/-- Search for and emit the entry of the aggregate `g` under `s`. -/
def liftAgg (tbl : Name) (s : Semantics) (sE : Lean.Expr) (c : Name) (g : DuckAgg)
    (sink : Option LoweringSearch.Sink := none) : TermElabM (Except String String) := do
  let short := c.componentsRev.head!
  let rows := aggSampleGroups g.arg
  let mut passed := 0
  for (ms, fin, kinds) in aggCandidates g do
    let some (measures, finish) := parseAgg g ms fin kinds | continue
    let ok := rows.all fun vs => LoweringSearch.Outcome.agreeB
      (finish.evalP Profile.reference (measures.map (·.eval (vs.map ([·]))))) (.ok (g.eval s vs))
    unless ok do continue
    passed := passed + 1
    let r ← withCurrHeartbeats do
      let mTerm ← mkListLit (Lean.mkConst ``Measure) (← measures.mapM fun m => do return ← measureTerm m)
      let fTerm ← exprTerm finish
      let gT := toExpr g
      let ty ← Term.elabType (← `(∀ vs : List Value, (∀ v ∈ vs, (DuckAgg.arg $(← Term.exprToSyntax gT)).Has v) →
        (Expr.evalP Profile.reference (($(← Term.exprToSyntax mTerm) : List Measure).map
          (·.eval (vs.map ([·])))) $(← Term.exprToSyntax fTerm)).Agree
          (.ok (DuckAgg.eval $(← Term.exprToSyntax sE) $(← Term.exprToSyntax gT) vs))))
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      if ty.hasMVar then return none
      let some pf ← prove ty (← aggTac #[]) | return none
      let agreeName := tbl ++ short.appendAfter "_agree"
      addDecl <| .thmDecl { name := agreeName, levelParams := [], type := ty, value := pf }
      let json := Json.mkObj [("measures", Json.arr ms.toArray), ("finish", fin)]
      let entry ← mkAppM ``AggEntry.mk #[toExpr json.compress, mTerm, fTerm, Lean.mkConst agreeName]
      let eTy ← inferType entry
      addAndCompile <| .defnDecl {
        name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
        type := eTy, value := entry }
      if let some out := sink then
        out.modify (·.push ("Aggregates",
          s!"theorem {agreeName} : {← LoweringSearch.ppSource ty} := by\n  lift_agg\n\n" ++
          s!"abbrev {tbl ++ short} : {← LoweringSearch.ppSource eTy} :=\n" ++
          s!"  ⟨{repr json.compress}, {← LoweringSearch.ppSource mTerm},\n" ++
          s!"    {← LoweringSearch.ppSource fTerm}, {agreeName}⟩\n\n"))
      return some json.compress
    if let some j := r then return .ok j
  return .error s!"missing: {passed} candidates passed the samples, none proved"

syntax (name := generateLift) "generate_lift " ident " : " term " using " "[" ident,* "]"
  " cache " ident (" writing " str)? : command

unsafe def evalHintsImpl (n : Name) : TermElabM (List LiftHint) := do
  Meta.evalExpr (List LiftHint) (← mkAppM ``List #[Lean.mkConst ``LiftHint]) (Lean.mkConst n)
@[implemented_by evalHintsImpl] opaque evalHints (n : Name) : TermElabM (List LiftHint)

/-- `generate_lift L : s using [lemmas]`: the lift table `L : Lift s`, with
`L.coverage` and, when every function has an entry, `L.total`. -/
@[command_elab generateLift]
def elabGenerateLift : CommandElab := fun stx => do
  Generated.requireChecked "generate_lift"
  let short := stx[1].getId
  let tbl := (← getCurrNamespace) ++ short
  let sStx : Term := ⟨stx[3]⟩
  let extra ← (stx[6].getSepArgs).mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let cacheName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[9])
  let writeDir : Option String := if stx[10].isNone then none else stx[10][1].isStrLit?
  let sink : Option LoweringSearch.Sink ← if writeDir.isSome then some <$> IO.mkRef #[] else pure none
  let ctors := (← getConstInfoInduct ``DuckFn).ctors
  let results ← liftTermElabM do
    -- Equation lemmas once, outside the attempts (a failed one discards them).
    for d in [``BinFn.apply, ``BinFn.issue, ``UnFn.apply, ``UnFn.issue, ``DuckFn.eval, ``DuckFn.evalOwn,
        ``nanCase] do
      discard <| Meta.getEqnsFor? d
      discard <| Meta.getUnfoldEqnFor? d (nonRec := true)
    let sE ← instantiateMVars (← elabTermEnsuringType sStx (Lean.mkConst ``Semantics))
    let s ← evalSemantics sE
    -- A constructor with finite parameters (`elementary f`): one per value.
    let ks ← ctors.flatMapM fun c => do
      return (← LoweringSearch.instances c false).getD [⟨c, false, #[]⟩]
    let hints ← evalHints cacheName
    ks.mapM fun k => withCurrHeartbeats do
      let f ← evalDuckFn (mkAppN (Lean.mkConst k.ctor) (k.args.map Lean.mkConst))
      let t0 ← IO.monoMsNow
      let hint? := hints.find? fun h => h.semantics == s.name && h.construct == f.sql
      let r ← liftOne tbl s sE extra k f hint? sink
      return (k, f, r, (← IO.monoMsNow) - t0)
  let aggCtors := (← getConstInfoInduct ``DuckAgg).ctors
  let aggResults ← liftTermElabM do
    let sE ← instantiateMVars (← elabTermEnsuringType sStx (Lean.mkConst ``Semantics))
    let s ← evalSemantics sE
    aggCtors.mapM fun c => withCurrHeartbeats do
      let g ← evalDuckAgg (Lean.mkConst c)
      let t0 ← IO.monoMsNow
      let r ← liftAgg tbl s sE c g sink
      return (c, g, r, (← IO.monoMsNow) - t0)
  let aggAlts ← aggResults.toArray.mapM fun (c, _, r, _) => do
    let rhs ← match r with
      | .ok _ => `(some $(mkIdent (tbl ++ c.componentsRev.head!)))
      | .error _ => `(none)
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) => $rhs)
  let alts ← results.toArray.mapM fun (k, _, r, _) => do
    let rhs ← match r with
      | .ok _ => `(some $(mkIdent (tbl ++ k.short)))
      | .error _ => `(none)
    let pats ← k.args.mapM fun a => `($(mkIdent a):ident)
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent k.ctor) $pats* => $rhs)
  elabCommand (← `(def $(mkIdent short) : Lift $sStx :=
    ⟨fun f => match f with $alts:matchAlt*, fun g => match g with $aggAlts:matchAlt*⟩))
  let summary : List (String × Except String String × Nat) :=
    results.map (fun ((_, f, r, ms) : LoweringSearch.Construct × DuckFn × Except String String × Nat) =>
      (f.sql, r, ms)) ++
      aggResults.map (fun ((_, g, r, ms) : Name × DuckAgg × Except String String × Nat) => (g.sql, r, ms))
  let rows ← summary.toArray.mapM fun (sql, r, ms) => do
    let how := match r with | .ok h => h | .error e => e
    `(($(quote sql), $(quote how), $(quote ms)))
  elabCommand (← `(def $(mkIdent (short ++ `coverage)) : List (String × String × Nat) := [$rows,*]))
  let missing := summary.filterMap fun (sql, r, _) => match r with
    | .error e => if e.startsWith "refused: " then none else some s!"{sql} ({e})"
    | .ok _ => none
  if missing.isEmpty then
    elabCommand (← `(theorem $(mkIdent (short ++ `total)) :
        ∀ f, (DuckFn.refused $sStx f).isNone → (($(mkIdent tbl)).entry f).isSome :=
      fun f h => by
        cases f <;> (try (rename_i a; cases a)) <;> first | rfl | simp [DuckFn.refused] at h))
  else
    logError m!"no lift found for {missing}"
  -- The generated modules (`writing`): what was found, to be checked by a
  -- build instead of searched for again.
  let some dir := writeDir | return
  let some sink := sink | return
  unless missing.isEmpty do return
  let sSrc ← liftTermElabM do
    LoweringSearch.ppSource (← instantiateMVars (← elabTermEnsuringType sStx (Lean.mkConst ``Semantics)))
  let chunks ← sink.get
  let modOf (area : String) : String := (dir.replace "/" ".") ++ "." ++ area
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let deps := (extra.filterMap moduleOf).toList.eraseDups
  let names := ", ".intercalate (extra.toList.map toString)
  let header (imports : List String) (what : String) : String :=
    "\n".intercalate (imports.map (s!"import {·}")) ++ "\n\n" ++
    s!"/-!\n# {what}\n\nGenerated by `generate_lift … writing` (`SubstraitLean/LiftSearch.lean`): do not edit. To regenerate,\n" ++
    "run `poe regen-lift` from `python/` (`docs/proofs.md`, \"Generated modules\"). A build\n" ++
    "checks these entries; it does not search for them.\n-/\n\ngenerated_entries\n\nopen Substrait\n\n" ++
    s!"local macro \"lift_tac1\" : tactic => `(tactic| lift_template 1 [{names}])\n" ++
    s!"local macro \"lift_tac2\" : tactic => `(tactic| lift_template 2 [{names}])\n\n"
  let base := ["SubstraitLean.LiftSearch"] ++ deps.map toString
  let areas := (chunks.toList.map (·.1)).eraseDups
  IO.FS.createDirAll dir
  for area in areas do
    let body := String.join ((chunks.toList.filter (·.1 == area)).map (·.2))
    IO.FS.writeFile s!"{dir}/{area}.lean" (header base s!"{tbl}: {area}" ++ body)
  let alts := "\n".intercalate (results.map fun (k, _, r, _) =>
    let pats := " ".intercalate (k.args.toList.map toString)
    let rhs := match r with | .ok _ => s!"some {tbl ++ k.short}" | .error _ => "none"
    s!"    | {k.ctor} {pats} => {rhs}")
  let aggAlts := "\n".intercalate (aggResults.map fun (c, _, r, _) =>
    let rhs := match r with | .ok _ => s!"some {tbl ++ c.componentsRev.head!}" | .error _ => "none"
    s!"    | {c} => {rhs}")
  let covRows := summary.map fun (sql, r, _) =>
    s!"  ({repr sql}, {repr (match r with | .ok h => h | .error e => e)}, 0)"
  let table :=
    header (base ++ areas.map modOf) s!"{tbl}: the table" ++
    s!"def {tbl} : Substrait.Lift ({sSrc}) :=\n  ⟨fun f => match f with\n{alts},\n" ++
    s!"   fun g => match g with\n{aggAlts}⟩\n\n" ++
    s!"/-- How each function lifts (`--lift-table`, the cache). -/\n" ++
    s!"def {tbl}.coverage : List (String × String × Nat) := [\n{",\n".intercalate covRows}]\n\n" ++
    s!"theorem {tbl}.total :\n    ∀ f, (Substrait.DuckFn.refused ({sSrc}) f).isNone → (({tbl}).entry f).isSome :=\n" ++
    "  fun f h => by\n" ++
    "    cases f <;> (try (rename_i a; cases a)) <;> first | rfl | simp [Substrait.DuckFn.refused] at h\n"
  IO.FS.writeFile s!"{dir}/Table.lean" table
  logInfo m!"wrote {dir}: {areas}, Table"

end LiftSearch
end Substrait
