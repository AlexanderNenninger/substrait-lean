import Lean
import SubstraitLean.Lowering

/-!
# The lowering generator (#241)

`generate_lowering L : p using tac` builds a `Lowering p` named `L` at
build time. For each constructor of `UnFn` and `BinFn` (a construct: the
function, its signature, its options as constructor parameters) it searches
for a template the engine runs, in this order:

1. **Native:** the function itself, `f(#0, #1)`.
2. **Guarded:** `CASE WHEN g THEN r ELSE f(#0, #1) END`, where `r` raises with
   the reference's message (`UnFn.raise`, DuckDB's `error()`) or is a
   constant, and the guard `g` is a predicate over the arguments built from
   the engine's comparisons and NULL tests: an atom (`#i IS NOT NULL`,
   `#i IS NULL`, `#i = c`, `#i < 0`), its negation, or two of them joined by
   `AND` or `OR`. Smaller guards come first.

Each candidate is first **evaluated** on sample arguments under `p` and under
the reference (`Profile.reference`), and only one that agrees on all of them,
and reads every argument (`Expr.must`), is handed to the prover: `tac` proves
the entry's `agree` obligation for every argument value and every value of
the constructor's parameters. The entry is added as a definition with its
proof, so the kernel checks it. A construct whose search fails gets no entry,
an error fails the build, and `L.coverage` lists it as missing.

The emitted declarations, for a constructor `c`:

* `L.c_agree`: the template agrees with the reference (a theorem);
* `L.c`: the entry, `UnEntry p (.c …)` or `BinEntry p (.c …)`;
* `L`: the table, `Lowering p`; `L.total` when every construct has an entry;
* `L.coverage`: each construct, how it is lowered, and the time it took.

Equality saturation (lean-egg) was considered and not used: it proves
equalities but does not synthesize terms, it is deprecated, and it needs Lean
4.30 and Rust (#241).
-/

namespace Substrait.LoweringSearch

open Lean Meta Elab Command Term

/-- A candidate template: kept as a value (to evaluate) and turned into a Lean
term (to emit). `self` is the construct being lowered, with its arguments. -/
inductive Tm where
  | field (i : Nat)
  | lit (v : Value)
  | un (f : UnFn) (n : Name) (a : Tm)
  | raise (msg : String) (a : Tm)
  | bin (f : BinFn) (n : Name) (a b : Tm)
  | self (args : List Tm)
  | ite (c t e : Tm)
  deriving Inhabited

instance : Inhabited Substrait.Expr := ⟨.lit .null⟩

/-- The candidate as an expression, with the construct `mk` applied to its
arguments. -/
partial def Tm.toModel (mk : List Substrait.Expr → Substrait.Expr) : Tm → Substrait.Expr
  | .field i => .field i
  | .lit v => .lit v
  | .un f _ a => .un f (a.toModel mk)
  | .raise m a => .un (.raise m) (a.toModel mk)
  | .bin f _ a b => .bin f (a.toModel mk) (b.toModel mk)
  | .self args => mk (args.map (·.toModel mk))
  | .ite c t e => .ifThen (c.toModel mk) (t.toModel mk) (e.toModel mk)

/-- A value as a Lean term (the literals guards use). -/
def valueTerm : Value → Lean.Expr
  | .null => Lean.mkConst ``Value.null
  | .bool b => mkApp (Lean.mkConst ``Value.bool) (toExpr b)
  | .int i => mkApp (Lean.mkConst ``Value.int) (toExpr i)
  | .str s => mkApp (Lean.mkConst ``Value.str) (toExpr s)
  | .list _ => Lean.mkConst ``Value.null

/-- The candidate as a Lean term of type `Substrait.Expr`; `self` is the
construct (a term of type `UnFn` or `BinFn`), `unary` its arity. -/
partial def Tm.toTerm (self : Lean.Expr) (unary : Bool) : Tm → Lean.Expr
  | .field i => mkApp (Lean.mkConst ``Substrait.Expr.field) (toExpr i)
  | .lit v => mkApp (Lean.mkConst ``Substrait.Expr.lit) (valueTerm v)
  | .un _ n a => mkApp2 (Lean.mkConst ``Substrait.Expr.un) (Lean.mkConst n) (a.toTerm self unary)
  | .raise m a =>
    mkApp2 (Lean.mkConst ``Substrait.Expr.un) (mkApp (Lean.mkConst ``UnFn.raise) (toExpr m)) (a.toTerm self unary)
  | .bin _ n a b =>
    mkApp3 (Lean.mkConst ``Substrait.Expr.bin) (Lean.mkConst n) (a.toTerm self unary) (b.toTerm self unary)
  | .self args =>
    let args := args.map (·.toTerm self unary)
    if unary then mkApp2 (Lean.mkConst ``Substrait.Expr.un) self args[0]!
    else mkApp3 (Lean.mkConst ``Substrait.Expr.bin) self args[0]! args[1]!
  | .ite c t e =>
    mkApp3 (Lean.mkConst ``Substrait.Expr.ifThen) (c.toTerm self unary) (t.toTerm self unary) (e.toTerm self unary)

partial def Tm.size : Tm → Nat
  | .field _ | .lit _ => 1
  | .un _ _ a | .raise _ a => a.size + 1
  | .bin _ _ a b => a.size + b.size + 1
  | .self args => (args.map Tm.size).sum + 1
  | .ite c t e => c.size + t.size + e.size + 1

/-- The candidate in SQL-like notation, for the coverage report. -/
partial def Tm.show (fn : String) : Tm → String
  | .field i => s!"#{i}"
  | .lit .null => "NULL"
  | .lit (.int i) => toString i
  | .lit (.bool b) => if b then "TRUE" else "FALSE"
  | .lit _ => "?"
  | .un .isNum _ a => s!"{a.show fn} IS NOT NULL"
  | .un .isNull _ a => s!"{a.show fn} IS NULL"
  | .un .not _ a => s!"NOT ({a.show fn})"
  | .un _ n a => s!"{n.getString!}({a.show fn})"
  | .raise m a => s!"error('{m}', {a.show fn})"
  | .bin .eq _ a b => s!"{a.show fn} = {b.show fn}"
  | .bin .lt _ a b => s!"{a.show fn} < {b.show fn}"
  | .bin .and _ a b => s!"({a.show fn} AND {b.show fn})"
  | .bin .or _ a b => s!"({a.show fn} OR {b.show fn})"
  | .bin _ n a b => s!"{n.getString!}({a.show fn}, {b.show fn})"
  | .self args => s!"{fn}({", ".intercalate (args.map (·.show fn))})"
  | .ite c t e => s!"CASE WHEN {c.show fn} THEN {t.show fn} ELSE {e.show fn} END"

/-! ## Evaluation on samples -/

def Outcome.agreeB : Outcome → Outcome → Bool
  | .ok v, .ok w => decide (v = w)
  | .error _, .error _ => true
  | _, _ => false

/-- The sample arguments: NULL, booleans, integers at and around zero and the
64-bit bounds, double codes (NaN, ±∞, 1.5), strings and lists. -/
def samples : List Value :=
  [.null, .bool true, .bool false, .int 0, .int 1, .int (-1), .int 2, .int (-2), .int 7,
   .int (-7), .int (-(2 ^ 63)), .int (2 ^ 63 - 1), .int FloatCode.nan, .int FloatCode.posInf,
   .int FloatCode.negInf, .int (FloatCode.ofFloat 1.5), .int (FloatCode.ofFloat (-2.5)),
   .str "", .str "a", .list [], .list [.int 1]]

/-- The rows of `n` sample arguments. -/
def sampleRows : Nat → List Row
  | 0 => [[]]
  | n + 1 => (sampleRows n).flatMap fun r => samples.map fun v => r ++ [v]

/-- The reference outcome of the construct on a row of arguments. -/
abbrev RefFn := Row → Outcome

/-- Does the template agree with the reference on every sample row? -/
def agreesOnSamples (p : Profile) (ref : RefFn) (rows : List Row) (t : Substrait.Expr) : Bool :=
  rows.all fun row => Outcome.agreeB (t.evalP p row) (ref row)

/-! ## Candidates -/

def isNumFn : Tm → Tm := .un .isNum ``UnFn.isNum
def isNullFn : Tm → Tm := .un .isNull ``UnFn.isNull
def notFn : Tm → Tm := .un .not ``UnFn.not
def eqFn : Tm → Tm → Tm := .bin .eq ``BinFn.eq
def ltFn : Tm → Tm → Tm := .bin .lt ``BinFn.lt
def andFn : Tm → Tm → Tm := .bin .and ``BinFn.and
def orFn : Tm → Tm → Tm := .bin .or ``BinFn.or

/-- The guards over `n` arguments, smaller first. -/
def guards (n : Nat) : List Tm :=
  let atoms := (List.range n).flatMap fun i =>
    let x := Tm.field i
    [isNumFn x, isNullFn x, eqFn x (.lit (.int 0)), eqFn x (.lit (.int (-1))), ltFn x (.lit (.int 0))]
  let lits := atoms ++ atoms.map notFn
  let pairs := lits.zipIdx.flatMap fun (a, i) => (lits.drop (i + 1)).map (a, ·)
  lits ++ pairs.map (fun (a, b) => andFn a b) ++ pairs.map (fun (a, b) => orFn a b)

/-- The candidates for a construct of `n` arguments, `msg` the reference's
error message (if it raises on some sample). -/
def candidates (n : Nat) (msg : Option String) : List Tm :=
  let args := (List.range n).map Tm.field
  let self := Tm.self args
  let alts := (msg.map fun m => [Tm.raise m (.field (n - 1))]).getD [] ++
    [.lit .null, .lit (.int 0), .lit (.bool false), .lit (.bool true)]
  self :: (guards n).flatMap fun g => alts.map fun r => .ite g r self

/-! ## Proving -/

open Tactic in
/-- Case-split on the first comparison (`a = b`, `a < b`, `a ≤ b`, without a
`match`) the goal decides with `decide` or `if`; the hypothesis is `hd`. -/
elab "lowering_split_decide" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let env ← getEnv
  let atomic (q : Lean.Expr) :=
    (q.isAppOfArity ``Eq 3 || q.isAppOfArity ``LT.lt 4 || q.isAppOfArity ``LE.le 4) &&
      (q.find? fun s => isMatcherCore env s.getAppFn.constName || s.isAppOf ``ite).isNone
  let ok (e : Lean.Expr) := !e.hasLooseBVars && !e.hasMVar &&
    atomic (if e.isAppOfArity ``ite 5 then e.getArg! 1 else e.getArg! 0)
  let p ← match t.find? (fun e => e.isAppOfArity ``Decidable.decide 2 && ok e) with
    | some d => pure (d.getArg! 0)
    | none => match t.find? (fun e => e.isAppOfArity ``ite 5 && ok e) with
      | some i => pure (i.getArg! 1)
      | none => throwError "nothing to split"
  let gs ← g.byCases p `hd
  replaceMainGoal [gs.1.mvarId, gs.2.mvarId]

/-- Prove `type` with the tactic; `none` (and nothing left in the environment
or the message log) if it fails, leaves goals or uses `sorry`. -/
def prove (type : Lean.Expr) (tac : Syntax) : TermElabM (Option Lean.Expr) := withCurrHeartbeats do
  let s ← saveState
  try
    let mv ← mkFreshExprMVar type
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    let pf ← instantiateMVars mv
    if gs.isEmpty && !pf.hasMVar && !pf.hasSorry && !(← MonadLog.hasErrors) then return some pf
    s.restore; return none
  catch _ => s.restore; return none

unsafe def evalProfileImpl (e : Lean.Expr) : TermElabM Profile :=
  Meta.evalExpr Profile (Lean.mkConst ``Profile) e

@[implemented_by evalProfileImpl]
opaque evalProfile (e : Lean.Expr) : TermElabM Profile

unsafe def evalUnFnImpl (e : Lean.Expr) : TermElabM UnFn := Meta.evalExpr UnFn (Lean.mkConst ``UnFn) e
@[implemented_by evalUnFnImpl] opaque evalUnFn (e : Lean.Expr) : TermElabM UnFn

unsafe def evalBinFnImpl (e : Lean.Expr) : TermElabM BinFn := Meta.evalExpr BinFn (Lean.mkConst ``BinFn) e
@[implemented_by evalBinFnImpl] opaque evalBinFn (e : Lean.Expr) : TermElabM BinFn

/-- The construct `c` with default parameters, if every parameter type is
inhabited. -/
def sampleCtor (c : Name) : TermElabM (Option Lean.Expr) := do
  let info ← getConstInfoCtor c
  forallTelescope info.type fun ps _ => do
    let mut args := #[]
    for x in ps do
      match ← observing? (mkAppOptM ``Inhabited.default #[← inferType x, none]) with
      | some d => args := args.push d
      | none => return none
    return some (mkAppN (Lean.mkConst c) args)

/-- The construct's reference outcome on a row of arguments, and the construct
applied to expressions. -/
def sampleFns (c : Name) (unary : Bool) :
    TermElabM (Option (RefFn × (List Substrait.Expr → Substrait.Expr))) := do
  let some e ← sampleCtor c | return none
  if unary then
    let f ← evalUnFn e
    return some (fun row => Profile.reference.un f (row.getD 0 .null),
      fun args => .un f (args.getD 0 (.lit .null)))
  else
    let f ← evalBinFn e
    return some (fun row => Profile.reference.bin f (row.getD 0 .null) (row.getD 1 .null),
      fun args => .bin f (args.getD 0 (.lit .null)) (args.getD 1 (.lit .null)))

/-- `[ns,*]` as simp arguments. -/
def simpArgs (ns : Array Name) : TermElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)

/-- The tactic for a native construct: the engine's function is the
reference's, by unfolding the profile (`unfold`) and splitting cases. -/
def nativeTac (unfold : Array Name) : TermElabM Syntax := do
  let u ← simpArgs unfold
  `(tactic| (intros; first
    | rfl
    | (simp only [$u,*]; done)
    | (simp only [$u,*]; (repeat' split) <;> simp_all [$u,*])))

/-- The tactic for a guarded template: evaluate the guard's functions (`natives`,
the engine's, and the reference's), split on the arguments' kinds and on the
comparisons the guard and the profile make, and compute. -/
def templateTac (unfold natives : Array Name) (unary : Bool) : TermElabM Syntax := do
  let pre ← simpArgs (#[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``Lowering.ref_isNum, ``Lowering.ref_isNull, ``Lowering.ref_not,
    ``Lowering.ref_raise, ``Lowering.ref_eq, ``Lowering.ref_lt, ``Lowering.ref_and,
    ``Lowering.ref_or] ++ natives)
  let vals ← simpArgs #[``Value.isNum, ``and3, ``or3, ``BinFn.apply, ``Value.isTrue,
    ``Bool.false_eq_true, ``ite_false, ``ite_true, ``Bool.not_true, ``Bool.not_false]
  let ref ← simpArgs (unfold ++ #[``Profile.reference, ``raiseIf, ``Lowering.beq_int,
    if unary then ``UnFn.issue else ``BinFn.issue])
  let fin ← simpArgs (unfold ++ #[``Issue.isError, ``Outcome.Agree])
  let cases ← if unary then `(tactic| (rename_i x; cases x))
    else `(tactic| (rename_i x y; cases x <;> cases y))
  `(tactic| (
    intros
    simp only [$pre,*]
    $cases:tactic <;> simp (config := { failIfUnchanged := false }) only [$vals,*]
    all_goals first
      | exact Outcome.agree_refl _
      | (simp (config := { failIfUnchanged := false }) only [$ref,*] at *
         iterate 4
           try
             lowering_split_decide <;>
               simp (config := { failIfUnchanged := false }) only [$(mkIdent `hd):ident, decide_true, decide_false, ite_true, ite_false]
         all_goals (repeat' split)
         all_goals (simp_all [$fin,*]))))

/-! ## Emitting -/

/-- How a construct was lowered: `native`, its template, or `missing`; and the
milliseconds it took. -/
structure Found where
  ctor : Name
  how : String
  ms : Nat

/-- Try to prove the construct `c` native under the profile `pE`; emit
`tbl.c_native` and the entry `tbl.c` if it is. -/
def lowerNative (tbl : Name) (pE : Lean.Expr) (tac : Syntax) (unary : Bool) (c : Name) :
    TermElabM Bool := do
  let short := c.componentsRev.head!
  forallTelescope (← getConstInfoCtor c).type fun ps _ => do
    let selfE := mkAppN (Lean.mkConst c) ps
    let ty ← withLocalDeclD `x (Lean.mkConst ``Value) fun x => withLocalDeclD `y (Lean.mkConst ``Value) fun y => do
      let xs := if unary then #[x] else #[x, y]
      let fn := if unary then ``Profile.un else ``Profile.bin
      let lhs ← mkAppM fn (#[pE, selfE] ++ xs)
      let rhs ← mkAppM fn (#[Lean.mkConst ``Profile.reference, selfE] ++ xs)
      mkForallFVars (ps ++ xs) (← mkEq lhs rhs)
    let some pf ← prove ty tac | return false
    let nativeName := tbl ++ short.appendAfter "_native"
    addDecl <| .thmDecl { name := nativeName, levelParams := [], type := ty, value := pf }
    let h ← mkAppM (if unary then ``Lowering.un_agree_of_eq else ``Lowering.bin_agree_of_eq)
      #[mkAppN (Lean.mkConst nativeName) ps]
    let entry ← mkAppM (if unary then ``UnEntry.native else ``BinEntry.native) #[selfE, h]
    addAndCompile <| .defnDecl {
      name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
      type := ← mkForallFVars ps (← inferType entry), value := ← mkLambdaFVars ps entry }
    return true

/-- Search for a guarded template for the construct `c`, test the candidates on
the samples, prove the first that passes, and emit `tbl.c_agree` and the entry
`tbl.c`. -/
def lowerSearch (tbl : Name) (pE : Lean.Expr) (p : Profile) (tac : Syntax) (unary : Bool) (c : Name) :
    TermElabM (Option String) := do
  let n := if unary then 1 else 2
  let short := c.componentsRev.head!
  let some (ref, mk) ← sampleFns c unary | return none
  let rows := sampleRows n
  let msg := rows.findSome? fun row => match ref row with | .error k => some k.name | .ok _ => none
  forallTelescope (← getConstInfoCtor c).type fun ps _ => do
    let selfE := mkAppN (Lean.mkConst c) ps
    for cand in (candidates n msg).drop 1 do
      let t := cand.toModel mk
      unless (List.range n).all (· ∈ t.must) && agreesOnSamples p ref rows t do continue
      let tmpl := cand.toTerm selfE unary
      let agreeTy ← withLocalDeclD `x (Lean.mkConst ``Value) fun x => withLocalDeclD `y (Lean.mkConst ``Value) fun y => do
        let xs := if unary then #[x] else #[x, y]
        let row ← mkListLit (Lean.mkConst ``Value) xs.toList
        let lhs ← mkAppM ``Expr.evalP #[pE, row, tmpl]
        let rhs ← mkAppM (if unary then ``Profile.un else ``Profile.bin)
          (#[Lean.mkConst ``Profile.reference, selfE] ++ xs)
        mkForallFVars (ps ++ xs) (← mkAppM ``Outcome.Agree #[lhs, rhs])
      let some agree ← prove agreeTy tac | continue
      let agreeName := tbl ++ short.appendAfter "_agree"
      addDecl <| .thmDecl { name := agreeName, levelParams := [], type := agreeTy, value := agree }
      let mustE ← mkAppM ``Expr.must #[tmpl]
      let mem (i : Nat) := mkAppM ``Membership.mem #[mustE, toExpr i]
      let strictTy ← if unary then mem 0 else mkAppM ``And #[← mem 0, ← mem 1]
      let some strict ← prove strictTy (← `(tactic| simp [Substrait.Expr.must])) | continue
      let entry ← mkAppM (if unary then ``UnEntry.mk else ``BinEntry.mk)
        #[tmpl, strict, mkAppN (Lean.mkConst agreeName) ps]
      addAndCompile <| .defnDecl {
        name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
        type := ← mkForallFVars ps (← inferType entry), value := ← mkLambdaFVars ps entry }
      return some (cand.show short.toString)
    return none

/-- The constructors the guards are built from. -/
def guardFns : List Name :=
  [``UnFn.isNum, ``UnFn.isNull, ``UnFn.not, ``UnFn.raise, ``BinFn.eq, ``BinFn.lt, ``BinFn.and, ``BinFn.or]

syntax (name := generateLowering) "generate_lowering " ident " : " term " unfolding " "[" ident,* "]" : command

@[command_elab generateLowering]
def elabGenerateLowering : CommandElab := fun stx => do
  let short := stx[1].getId
  let tbl := (← getCurrNamespace) ++ short
  let pStx : Term := ⟨stx[3]⟩
  let unfold ← (stx[6].getSepArgs).mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let ctors ← [(``UnFn, true), (``BinFn, false)].flatMapM fun (ind, unary) => do
    return (← getConstInfoInduct ind).ctors.map (·, unary)
  let (found, missing) ← liftTermElabM do
    let pE ← instantiateMVars (← elabTermEnsuringType pStx (Lean.mkConst ``Profile))
    let p ← evalProfile pE
    let mut found : Array Found := #[]
    let mut rest := #[]
    -- Natives first: the guards are built from them.
    let ntac ← nativeTac unfold
    for (c, unary) in ctors do
      let t0 ← IO.monoMsNow
      if ← lowerNative tbl pE ntac unary c then found := found.push ⟨c, "native", (← IO.monoMsNow) - t0⟩
      else rest := rest.push (c, unary)
    let natives := guardFns.filter (fun c => found.any (·.ctor == c)) |>.map fun c =>
      tbl ++ c.componentsRev.head!.appendAfter "_native"
    let mut missing := #[]
    for (c, unary) in rest do
      let t0 ← IO.monoMsNow
      match ← lowerSearch tbl pE p (← templateTac unfold natives.toArray unary) unary c with
      | some how => found := found.push ⟨c, how, (← IO.monoMsNow) - t0⟩
      | none => missing := missing.push c
    return (found, missing)
  -- The table.
  let arms (ind : Name) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
    (← getConstInfoInduct ind).ctors.toArray.mapM fun c => do
      let nargs := (← getConstInfoCtor c).numFields
      let xs := (List.range nargs).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
      let rhs ← if missing.contains c then `(none)
        else `(some ($(mkIdent (tbl ++ c.componentsRev.head!)) $xs*))
      `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) $xs* => $rhs)
  let unAlts ← arms ``UnFn
  let binAlts ← arms ``BinFn
  elabCommand (← `(def $(mkIdent short) : Lowering $pStx :=
    ⟨fun f => match f with $unAlts:matchAlt*, fun f => match f with $binAlts:matchAlt*⟩))
  -- The coverage report.
  -- In the constructors' order.
  let rows := ctors.map fun (c, _) => match found.find? (·.ctor == c) with
    | some f => (c, f.how, f.ms)
    | none => (c, "missing", 0)
  let rows ← rows.mapM fun (c, how, ms) =>
    `(($(quote (c.replacePrefix `Substrait .anonymous).toString), $(quote how), $(quote ms)))
  elabCommand (← `(def $(mkIdent (short ++ `coverage)) : List (String × String × Nat) := [$(rows.toArray),*]))
  if missing.isEmpty then
    elabCommand (← `(theorem $(mkIdent (short ++ `total)) : ($(mkIdent tbl)).Total :=
      ⟨fun f => by cases f <;> rfl, fun f => by cases f <;> rfl⟩))
  else
    logError m!"no lowering found for {missing.toList}"

end Substrait.LoweringSearch
