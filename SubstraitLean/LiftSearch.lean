import Lean
import SubstraitLean.Parse
import SubstraitLean.DuckDBSQL
import SubstraitLean.LoweringSearch

/-!
# The lift generator (#268)

`generate_lift L : s using [lemmas]` builds, at build time, the table of what
DuckDB's SQL functions (`DuckFn`, `SubstraitLean/DuckDBSQL.lean`) lift to under
the semantics `s`: for each, a Substrait expression over its arguments that
the parser (`Parse.parseExpr`) reads as the same function. It is the lowering
search (`SubstraitLean/LoweringSearch.lean`) run backwards.

For each `DuckFn` it tries, in order:

1. **A call:** a Substrait function of the right arity (`divide`, `modulus`,
   `sverify_fmod`, `log10`, …), its arguments as they are or cast to the
   result's type, with every assignment of the options the parser accepts for
   it (`Parse.optionAccepts`).
2. **A guarded call:** `CASE WHEN g THEN v ELSE call END`, or two such
   guards, where `g` tests arguments (`IS NULL`, `= 0`, `< 0`, infinite, or
   two such tests joined by `AND`) and `v` is a constant (`NULL`, NaN, `±∞`).
   This states what Substrait's options cannot: DuckDB's `log(0)` is `-∞`.

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

/-- A lift table: an entry for each function under the semantics, or none. -/
structure Lift (s : Semantics) where
  entry : (f : DuckFn) → Option (LiftEntry s f)

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

/-- The functions candidates call, with their anchors, signatures and
extension URNs. -/
def functions : List (Nat × String × String) :=
  [(1, "divide:fp64_fp64", "extension:io.substrait:functions_arithmetic"),
   (2, "modulus:fp64_fp64", "extension:io.substrait:functions_arithmetic"),
   (3, "sverify_fmod:fp64_fp64", "extension:io.sverify:functions"),
   (4, "log10:fp64", "extension:io.substrait:functions_arithmetic"),
   (5, "ln:fp64", "extension:io.substrait:functions_arithmetic"),
   (6, "log2:fp64", "extension:io.substrait:functions_arithmetic"),
   (7, "power:fp64_fp64", "extension:io.substrait:functions_arithmetic"),
   (20, "equal:any_any", "extension:io.substrait:functions_comparison"),
   (21, "lt:any_any", "extension:io.substrait:functions_comparison"),
   (22, "is_null:any", "extension:io.substrait:functions_comparison"),
   (23, "and:bool", "extension:io.substrait:functions_boolean"),
   (24, "or:bool", "extension:io.substrait:functions_boolean")]

def fns : List (Nat × String) := functions.map fun (a, n, _) => (a, n)

def anchorOf (name : String) : Nat :=
  ((functions.find? fun (_, n, _) => Parse.baseName n == name).map (·.1)).getD 0

def callJ (name : String) (args : List Json) (opts : List (String × String)) (out : String) : Json :=
  Json.mkObj [("scalarFunction", Json.mkObj [
    ("functionReference", toJson (anchorOf name)),
    ("outputType", typeJ out),
    ("arguments", Json.arr (args.map fun a => Json.mkObj [("value", a)]).toArray),
    ("options", Json.arr (opts.map fun (o, p) =>
      Json.mkObj [("name", toJson o), ("preference", Json.arr #[toJson p])]).toArray)])]

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

/-- Calls of the right arity on the arguments, as they are or cast to the
result's type. -/
def calls (f : DuckFn) : List (String × Json × List (String × String)) :=
  let n := f.args.length
  let out := f.result.substrait
  let names := if n == 1 then ["log10", "ln", "log2"]
    else ["divide", "modulus", "sverify_fmod", "power"]
  let asIs := (List.range n).map fieldJ
  let cast := (f.args.zip asIs).map fun (t, a) => if t == f.result then a else castJ out a
  let argss := if asIs == cast then [asIs] else [asIs, cast]
  names.flatMap fun name => argss.flatMap fun args =>
    (optionChoices name (f.result == .double)).map fun opts =>
      (name, callJ name args opts out, opts)

/-- Tests of the arguments a guard is built from. -/
def atoms (f : DuckFn) : List Json :=
  (f.args.zipIdx).flatMap fun (t, i) =>
    let x := fieldJ i
    let ty := t.substrait
    let zero := if t == .double then litJ ty (Json.num 0) else litJ ty (toJson (0 : Int))
    let base := [callJ "is_null" [x] [] "boolean", callJ "equal" [x, zero] [] "boolean",
      callJ "lt" [x, zero] [] "boolean"]
    if t == .double then
      base ++ [callJ "or" [callJ "equal" [x, litJ ty "inf"] [] "boolean",
        callJ "equal" [x, litJ ty "-inf"] [] "boolean"] [] "boolean"]
    else base

/-- The guards: an atom, or two atoms of different arguments joined by `AND`. -/
def guards (f : DuckFn) : List Json :=
  let as := atoms f
  let per := as.length / max f.args.length 1
  let pairs := as.zipIdx.flatMap fun (a, i) =>
    (as.drop ((i / per + 1) * per)).map fun b => callJ "and" [a, b] [] "boolean"
  as ++ pairs

/-- The constants a guard may give. -/
def values (f : DuckFn) : List Json :=
  let t := f.result.substrait
  [nullJ t, litJ t "nan", litJ t "inf", litJ t "-inf"]

/-! ## Samples -/

def sampleValues : DuckType → List Value
  | .bigint => [.null, .int 0, .int 1, .int (-1), .int 7, .int (-7), .int (2 ^ 63 - 1), .int (-(2 ^ 63))]
  | .double => [.null, .int 0, .int (FloatCode.ofFloat 1.5), .int (FloatCode.ofFloat (-2.5)),
      .int (FloatCode.ofFloat 100), .int (FloatCode.ofFloat 0.5), .int FloatCode.nan,
      .int FloatCode.posInf, .int FloatCode.negInf]

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
  | .int i =>
    let c := if i == FloatCode.nan then Lean.mkConst ``FloatCode.nan
      else if i == FloatCode.posInf then Lean.mkConst ``FloatCode.posInf
      else if i == FloatCode.negInf then Lean.mkConst ``FloatCode.negInf
      else toExpr i
    pure (mkApp (Lean.mkConst ``Value.int) c)
  | .list _ => throwError "list literals in a lift template are not supported"

-- One type a line: a list derives only its first.
deriving instance Lean.ToExpr for FMath
deriving instance Lean.ToExpr for BitOp
deriving instance Lean.ToExpr for Time.DatePart
deriving instance Lean.ToExpr for Time.TimeUnit
deriving instance Lean.ToExpr for UnFn
deriving instance Lean.ToExpr for BinFn
deriving instance Lean.ToExpr for HoFn
deriving instance Lean.ToExpr for DuckType

unsafe def evalSemanticsImpl (e : Lean.Expr) : TermElabM Semantics :=
  Meta.evalExpr Semantics (Lean.mkConst ``Semantics) e
@[implemented_by evalSemanticsImpl] opaque evalSemantics (e : Lean.Expr) : TermElabM Semantics

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
  let cols := f.args.map fun t => if t == .double then Parse.Kind.float else .int
  (Parse.parseExpr fns cols (f.args.map fun _ => 64) j).toOption

def agrees (want got : List Outcome) : Bool :=
  (want.zip got).all fun (w, g) => LoweringSearch.Outcome.agreeB g w

/-- The candidates, in order, that agree with the function on the samples:
calls, then calls under one or two guards. Guards and constants are read
once; a guarded call's outcomes are combined from theirs. -/
def survivors (s : Semantics) (f : DuckFn) : List (Json × Substrait.Expr × String) := Id.run do
  let rows := sampleRows f.args
  let want := rows.map (DuckFn.eval s f)
  let out (e : Substrait.Expr) := rows.map fun r => e.evalP Profile.reference r
  let gs := (guards f).filterMap fun j => (parse f j).map fun e =>
    (j, e, rows.map fun r => match e.evalP Profile.reference r with | .ok v => v.isTrue | .error _ => false)
  let vs := (values f).filterMap fun j => (parse f j).map fun e => (j, e, out e)
  let mut found := #[]
  for (name, j, opts) in calls f do
    let some e := parse f j | continue
    let o := out e
    let label := s!"{name} {opts}"
    if agrees want o then found := found.push (j, e, label)
    -- One guard.
    for (gj, ge, gt) in gs do
      for (vj, ve, vo) in vs do
        let o1 := (gt.zip (vo.zip o)).map fun (b, v, x) => if b then v else x
        if agrees want o1 then
          found := found.push (ifJ gj vj j, .ifThen ge ve e, label)
        -- Two guards.
        else
          for (gj2, ge2, gt2) in gs do
            for (vj2, ve2, vo2) in vs do
              let o2 := (gt.zip (vo.zip ((gt2.zip (vo2.zip o)).map fun (b, v, x) => if b then v else x))).map
                fun (b, v, x) => if b then v else x
              if agrees want o2 then
                found := found.push (ifJ gj vj (ifJ gj2 vj2 j), .ifThen ge ve (.ifThen ge2 ve2 e), label)
    if found.size ≥ 4 then break
  return found.toList

/-! ## Proving and emitting -/

/-- The proof tactic: split on the arguments' kinds (dropping those outside
their types), evaluate both sides, split on the comparisons, and compute. -/
def liftTac (n : Nat) (extra : Array Name) : TermElabM Syntax := do
  let ev ← simpArgs (#[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``DuckFn.eval, ``duckDivide, ``duckMod, ``duckLog, ``Profile.reference,
    ``raiseIf, ``BinFn.issue, ``BinFn.apply, ``nanIssue, ``nanCase, ``isInfCode, ``ieeeDivZero,
    ``DuckDBSQL.ite_or, ``Value.isTrue, ``and3, ``or3, ``Lowering.beq_int, ``Lowering.ref_isNull,
    ``Lowering.ref_not, ``Issue.isError, ``DuckDBSQL.ref_itof, ``DuckDBSQL.ref_fmath_int,
    ``DuckDBSQL.ref_fmath_null, ``FloatCode.ofInt_ne_posInf, ``FloatCode.ofInt_ne_negInf,
    ``Bool.false_eq_true, ``ite_false, ``ite_true, ``Bool.or_false, ``Bool.false_or,
    ``Bool.and_false, ``Bool.false_and, ``Bool.or_true, ``Bool.true_and] ++ extra)
  let fin ← simpArgs (#[``Outcome.Agree, ``Issue.isError] ++ extra)
  let intro ← if n == 1 then `(tactic| (intro x hx; cases x <;> simp (config := { failIfUnchanged := false }) only [DuckType.Has] at hx))
    else `(tactic| (intro x y hx hy; cases x <;> cases y <;> simp (config := { failIfUnchanged := false }) only [DuckType.Has] at hx hy))
  `(tactic| (
    $intro:tactic
    all_goals have := FloatCode.negInf_lt_zero
    all_goals have := FloatCode.zero_lt_posInf
    all_goals have := FloatCode.posInf_lt_nan
    all_goals simp (config := { failIfUnchanged := false, decide := true }) only [$ev,*]
    iterate 6
      all_goals try
        lowering_split_decide <;>
          simp (config := { failIfUnchanged := false, decide := true }) only [$(mkIdent `hd):ident, $ev,*]
    all_goals (repeat' split)
    all_goals first
      | (simp_all [$fin,*]; done)
      | (simp_all [$fin,*] <;> omega)
      | omega))

/-- Search for and emit the entry of `f` under `s`; how it lifts, or why not. -/
def liftOne (tbl : Name) (s : Semantics) (sE : Lean.Expr) (extra : Array Name) (c : Name) (f : DuckFn) :
    TermElabM (Except String String) := do
  let short := c.componentsRev.head!
  let fE := Lean.mkConst c
  let n := f.args.length
  let cands := survivors s f
  let tac ← liftTac n extra
  for (j, e, label) in cands do
    -- The parser reads the whole candidate as its parts combined.
    unless parse f j == some e do continue
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
    let some pf ← prove ty tac | continue
    let agreeName := tbl ++ short.appendAfter "_agree"
    addDecl <| .thmDecl { name := agreeName, levelParams := [], type := ty, value := pf }
    let hf ← mkEqRefl (← mkAppM ``DuckFn.args #[fE])
    let agree ← mkAppM (if n == 1 then ``LiftEntry.of₁ else ``LiftEntry.of₂) #[hf, Lean.mkConst agreeName]
    let entry ← mkAppM ``LiftEntry.mk #[toExpr j.compress, tmpl, agree]
    addAndCompile <| .defnDecl {
      name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
      type := ← inferType entry, value := entry }
    return .ok s!"{label}: {j.compress}"
  return .error s!"missing: {cands.length} candidates passed the samples, none proved"

syntax (name := generateLift) "generate_lift " ident " : " term " using " "[" ident,* "]" : command

/-- `generate_lift L : s using [lemmas]`: the lift table `L : Lift s`, with
`L.coverage` and, when every function has an entry, `L.total`. -/
@[command_elab generateLift]
def elabGenerateLift : CommandElab := fun stx => do
  let short := stx[1].getId
  let tbl := (← getCurrNamespace) ++ short
  let sStx : Term := ⟨stx[3]⟩
  let extra ← (stx[6].getSepArgs).mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let ctors := (← getConstInfoInduct ``DuckFn).ctors
  let results ← liftTermElabM do
    let sE ← instantiateMVars (← elabTermEnsuringType sStx (Lean.mkConst ``Semantics))
    let s ← evalSemantics sE
    ctors.mapM fun c => do
      let f ← evalDuckFn (Lean.mkConst c)
      let t0 ← IO.monoMsNow
      let r ← liftOne tbl s sE extra c f
      return (c, f, r, (← IO.monoMsNow) - t0)
  let alts ← results.toArray.mapM fun (c, _, r, _) => do
    let rhs ← match r with
      | .ok _ => `(some $(mkIdent (tbl ++ c.componentsRev.head!)))
      | .error _ => `(none)
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) => $rhs)
  elabCommand (← `(def $(mkIdent short) : Lift $sStx := ⟨fun f => match f with $alts:matchAlt*⟩))
  let rows ← results.toArray.mapM fun (_, f, r, ms) => do
    let how := match r with | .ok h => h | .error e => e
    `(($(quote f.sql), $(quote how), $(quote ms)))
  elabCommand (← `(def $(mkIdent (short ++ `coverage)) : List (String × String × Nat) := [$rows,*]))
  let missing := results.filterMap fun (_, f, r, _) => match r with
    | .error e => some s!"{f.sql} ({e})" | .ok _ => none
  if missing.isEmpty then
    elabCommand (← `(theorem $(mkIdent (short ++ `total)) : ∀ f, ($(mkIdent tbl)).entry f |>.isSome :=
      fun f => by cases f <;> rfl))
  else
    logError m!"no lift found for {missing}"

end LiftSearch
end Substrait
