import Lean
import SubstraitLean.LoweringHint
import Sverify.Engines.Generated

/-!
# The lowering generator (#241)

`generate_lowering L : p unfolding [defs] using [lemmas] excluding [fns] cache hints`
builds a `Lowering p` named `L` at build time. Each constructor of `UnFn` and
`BinFn` is a construct (the function, its signature, its options as
constructor parameters); a constructor whose parameters are all finite
(`OverflowMode`, `IntWidth`) and that is not native is split into one construct
per value of them. For each it looks for a template the engine runs, in this
order:

1. **Native:** the function itself, `f(#0, #1)`, unless the engine does not
   have it (`fns`, such as `UnFn.fit`).
2. **Hand-written schema** (`Schemas`, the engine's own), where the search
   does not reach: for DuckDB, the wrap-around of `overflow` = `SILENT`.
3. **Guarded:** `CASE WHEN g THEN r ELSE f(#0, #1) END`, where `r` raises with
   the reference's message (`UnFn.raise`, DuckDB's `error()`) or is a
   constant, and the guard `g` is a predicate over the arguments built from
   the engine's comparisons and NULL tests: an atom (`#i IS NOT NULL`,
   `#i IS NULL`, `#i = c`, `#i < 0`), its negation, or two of them joined by
   `AND` or `OR`. Smaller guards come first.
4. **`CASE` chains** of a unary construct: up to two comparisons of the
   argument with constants, each giving a constant or the argument, else the
   argument. The constants are those the reference gives on the samples
   (`harvest`): a clamp's bounds, for `overflow` = `SATURATE`.

Each candidate is first **evaluated** on sample arguments under `p` and under
the reference (`Profile.reference`), and only one that agrees on all of them,
and reads every argument (`Expr.must`), is handed to the prover, a tactic that
unfolds `defs`, rewrites with `lemmas`, splits cases and computes. It proves
the entry's `agree` obligation for every argument value and every value of the
remaining parameters. The entry is added as a definition with its proof, so
the kernel checks it, hand-written schemas included. A construct whose search
fails gets no entry, an error fails the build, and `L.coverage` lists it as
missing.

The emitted declarations, for a construct `k` (a constructor `c`, or `c`
with its finite parameters, `fit_saturate_i32`):

* `L.c_native` or `L.k_agree`: the function is the reference's, or the
  template agrees with it (theorems);
* `L.k`: the entry, `UnEntry p (.c …)` or `BinEntry p (.c …)`;
* `L`: the table, `Lowering p`; `L.total` when every construct has an entry;
* `L.coverage`: each construct, how it is lowered, and the time it took.

Equality saturation (lean-egg) was considered and not used: it proves
equalities but does not synthesize terms, it is deprecated, and it needs Lean
4.30 and Rust (#241).
-/

namespace Substrait.LoweringSearch

open Lean Meta Elab Command Term

/-- A sample kind, for constructs with a `NumKind` parameter (`UnFn.isNum`). -/
instance : Inhabited NumKind := ⟨.int⟩

/-- A number kind as a Lean term. -/
def numKindTerm : NumKind → Lean.Expr
  | .int => Lean.mkConst ``NumKind.int
  | .float => Lean.mkConst ``NumKind.float
  | .date => Lean.mkConst ``NumKind.date
  | .ts => Lean.mkConst ``NumKind.ts
  | .tod => Lean.mkConst ``NumKind.tod
  | .dec s => mkApp (Lean.mkConst ``NumKind.dec) (toExpr s)

/-- A candidate template: kept as a value (to evaluate) and turned into a Lean
term (to emit). `self` is the construct being lowered, with its arguments. -/
inductive Tm where
  | field (i : Nat)
  | lit (v : Value)
  | un (f : UnFn) (t : Lean.Expr) (a : Tm)
  | raise (msg : String) (a : Tm)
  | bin (f : BinFn) (n : Name) (a b : Tm)
  | self (args : List Tm)
  | ite (c t e : Tm)
  /-- A constant written by name (`FloatCode.posInf`), so that proofs unfold
  it as the profile's definitions do; `v` is its value, `label` how it shows. -/
  | named (v : Value) (term : Lean.Expr) (label : String)
  /-- An expression written by name (`Lowering.pow2Chain`), so that the proofs
  rewrite it with its own lemma; `e` is its value. -/
  | expr (e : Substrait.Expr) (term : Lean.Expr) (label : String)
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
  | .named v _ _ => .lit v
  | .expr e _ _ => e

/-- A value as a Lean term (the literals guards use). -/
def valueTerm : Value → Lean.Expr
  | .null => Lean.mkConst ``Value.null
  | .bool b => mkApp (Lean.mkConst ``Value.bool) (toExpr b)
  | .int i => mkApp (Lean.mkConst ``Value.int) (toExpr i)
  | .float i => mkApp (Lean.mkConst ``Value.float) (toExpr i)
  | .date i => mkApp (Lean.mkConst ``Value.date) (toExpr i)
  | .ts i => mkApp (Lean.mkConst ``Value.ts) (toExpr i)
  | .tod i => mkApp (Lean.mkConst ``Value.tod) (toExpr i)
  | .dec s i => mkApp2 (Lean.mkConst ``Value.dec) (toExpr s) (toExpr i)
  | .str s => mkApp (Lean.mkConst ``Value.str) (toExpr s)
  | .list _ | .struct _ => Lean.mkConst ``Value.null

/-- The candidate as a Lean term of type `Substrait.Expr`; `self` is the
construct (a term of type `UnFn` or `BinFn`), `unary` its arity. -/
partial def Tm.toTerm (self : Lean.Expr) (unary : Bool) : Tm → Lean.Expr
  | .field i => mkApp (Lean.mkConst ``Substrait.Expr.field) (toExpr i)
  | .lit v => mkApp (Lean.mkConst ``Substrait.Expr.lit) (valueTerm v)
  | .un _ t a => mkApp2 (Lean.mkConst ``Substrait.Expr.un) t (a.toTerm self unary)
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
  | .named _ term _ => mkApp (Lean.mkConst ``Substrait.Expr.lit) term
  | .expr _ term _ => term

partial def Tm.size : Tm → Nat
  | .field _ | .lit _ | .named .. | .expr .. => 1
  | .un _ _ a | .raise _ a => a.size + 1
  | .bin _ _ a b => a.size + b.size + 1
  | .self args => (args.map Tm.size).sum + 1
  | .ite c t e => c.size + t.size + e.size + 1

/-- The candidate in SQL-like notation, for the coverage report. -/
partial def Tm.show (fn : String) : Tm → String
  | .field i => s!"#{i}"
  | .lit .null => "NULL"
  | .lit (.int i) | .lit (.float i) => toString i
  | .lit (.bool b) => if b then "TRUE" else "FALSE"
  | .lit _ => "?"
  | .un (.isNum _) _ a => s!"{a.show fn} IS NOT NULL"
  | .un .isNull _ a => s!"{a.show fn} IS NULL"
  | .un .not _ a => s!"NOT ({a.show fn})"
  | .un _ t a => s!"{t.getAppFn.constName!.getString!}({a.show fn})"
  | .raise m a => s!"error('{m}', {a.show fn})"
  | .bin .eq _ a b => s!"{a.show fn} = {b.show fn}"
  | .bin .lt _ a b => s!"{a.show fn} < {b.show fn}"
  | .bin .and _ a b => s!"({a.show fn} AND {b.show fn})"
  | .bin .or _ a b => s!"({a.show fn} OR {b.show fn})"
  | .bin _ n a b => s!"{n.getString!}({a.show fn}, {b.show fn})"
  | .self args => s!"{fn}({", ".intercalate (args.map (·.show fn))})"
  | .ite c t e => s!"CASE WHEN {c.show fn} THEN {t.show fn} ELSE {e.show fn} END"
  | .named _ _ l | .expr _ _ l => l

/-! ## Evaluation on samples -/

def Outcome.agreeB : Outcome → Outcome → Bool
  | .ok v, .ok w => decide (v = w)
  | .error _, .error _ => true
  | _, _ => false

/-- The sample arguments: NULL, booleans, integers at and around zero and the
64-bit bounds, doubles (zero, the codes ±1, NaN, ±∞, 1.5), a date, a
timestamp, a time of day, a decimal, strings, lists and a struct (#923). -/
def samples : List Value :=
  [.null, .bool true, .bool false, .int 0, .int 1, .int (-1), .int 2, .int (-2), .int 7,
   .int (-7), .int (-(2 ^ 63)), .int (2 ^ 63 - 1), .float 0, .float 1, .float (-1),
   .float FloatCode.nan, .float FloatCode.posInf, .float FloatCode.negInf,
   .float FloatCode.negZero, .float FloatCode.negNan,
   .float (FloatCode.ofFloat 1.5), .float (FloatCode.ofFloat (-2.5)), .date 0, .ts 0, .tod 0,
   .dec 2 150, .str "", .str "a", .list [], .list [.int 1], .struct []]

/-- Integers at and around each width's bounds (`IntWidth`), for unary
constructs: what `UnFn.fit` wraps or clamps. -/
def boundarySamples : List Value :=
  [8, 16, 32, 64].flatMap fun b =>
    let h : Int := 2 ^ (b - 1)
    [.int (h - 1), .int h, .int (-h), .int (-h - 1), .int (2 * h), .int (-2 * h - 3), .int (3 * h + 5)]

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

def isNumFn (k : NumKind) : Tm → Tm :=
  .un (.isNum k) (mkApp (Lean.mkConst ``UnFn.isNum) (numKindTerm k))
def isNullFn : Tm → Tm := .un .isNull (Lean.mkConst ``UnFn.isNull)
def notFn : Tm → Tm := .un .not (Lean.mkConst ``UnFn.not)
def eqFn : Tm → Tm → Tm := .bin .eq ``BinFn.eq
def ltFn : Tm → Tm → Tm := .bin .lt ``BinFn.lt
def andFn : Tm → Tm → Tm := .bin .and ``BinFn.and
def orFn : Tm → Tm → Tm := .bin .or ``BinFn.or

/-- The guards over `n` arguments, smaller first. -/
def guards (k : NumKind) (n : Nat) : List Tm :=
  let atoms := (List.range n).flatMap fun i =>
    let x := Tm.field i
    [isNumFn k x, isNullFn x, eqFn x (.lit (k.val 0)), eqFn x (.lit (k.val (-1))),
      ltFn x (.lit (k.val 0))]
  let lits := atoms ++ atoms.map notFn
  let pairs := lits.zipIdx.flatMap fun (a, i) => (lits.drop (i + 1)).map (a, ·)
  lits ++ pairs.map (fun (a, b) => andFn a b) ++ pairs.map (fun (a, b) => orFn a b)

/-- The candidates for a construct of `n` arguments of kind `k`, `msg` the
reference's error message (if it raises on some sample). -/
def candidates (k : NumKind) (n : Nat) (msg : Option String) : List Tm :=
  let args := (List.range n).map Tm.field
  let self := Tm.self args
  let alts := (msg.map fun m => [Tm.raise m (.field (n - 1))]).getD [] ++
    [.lit .null, .lit (k.val 0), .lit (.bool false), .lit (.bool true)]
  self :: (guards k n).flatMap fun g => alts.map fun r => .ite g r self

def daddFn : Tm → Tm → Tm := .bin .dadd ``BinFn.dadd
def dsubFn : Tm → Tm → Tm := .bin .dsub ``BinFn.dsub
def imodFn : Tm → Tm → Tm := .bin .imod ``BinFn.imod

/-- Constants of a unary construct: the integers it gives for an integer
other than that integer (a clamp's bounds), at most four. -/
def harvest (ref : RefFn) (rows : List Row) : List Int :=
  let outs := rows.filterMap fun row => match row, ref row with
    | [.int i], .ok (.int o) => if o != i then some o else none
    | _, _ => none
  (outs.foldl (fun acc o => if acc.contains o then acc else acc ++ [o]) []).take 4

/-- `CASE` chains of a unary construct that is not itself available: up to two
comparisons of the argument with constants, each giving a constant or the
argument, else the argument. -/
def chains (consts : List Int) : List Tm :=
  let x := Tm.field 0
  let atoms := consts.flatMap fun c => [ltFn x (.lit (.int c)), ltFn (.lit (.int c)) x]
  let vals := x :: Tm.lit .null :: consts.map fun c => Tm.lit (.int c)
  let one := atoms.flatMap fun g => vals.map fun v => (g, v)
  one.map (fun (g, v) => Tm.ite g v x) ++
    one.flatMap fun (g1, v1) => one.map fun (g2, v2) => Tm.ite g1 v1 (.ite g2 v2 x)

/-- A double's code written as the Lean term `term` (of type `Int`). -/
def namedFloat (v : Int) (term : Lean.Expr) (label : String) : Tm :=
  .named (.float v) (mkApp (Lean.mkConst ``Value.float) term) label

def posInfT : Tm := namedFloat FloatCode.posInf (Lean.mkConst ``FloatCode.posInf) "'inf'"
def negInfT : Tm := namedFloat FloatCode.negInf (Lean.mkConst ``FloatCode.negInf) "'-inf'"
def nanT : Tm := namedFloat FloatCode.nan (Lean.mkConst ``FloatCode.nan) "'nan'"


/-- The elementary function as a Lean term. -/
def fmathTerm (f : FMath) : Lean.Expr :=
  Lean.mkConst (match f with
    | .sqrt => ``FMath.sqrt | .exp => ``FMath.exp | .ln => ``FMath.ln | .log10 => ``FMath.log10
    | .log2 => ``FMath.log2 | .sin => ``FMath.sin | .cos => ``FMath.cos | .tan => ``FMath.tan
    | .asin => ``FMath.asin | .acos => ``FMath.acos | .atan => ``FMath.atan)

/-- `#i = ±∞`. -/
def isInfT (x : Tm) : Tm := orFn (eqFn x posInfT) (eqFn x negInfT)

/-- **An engine's hand-written template schemas** (#241, #242), for the
constructs the search does not reach: a construct's schema is tried before the
search. Each instance is still proved, by the kernel. DuckDB's are
`duckdbSchemas` (`SubstraitLean/LoweringDuckDB/Schemas.lean`). -/
structure Schemas where
  un : UnFn → Option Tm := fun _ => none
  bin : BinFn → Option Tm := fun _ => none

partial def Tm.hasSelf : Tm → Bool
  | .field _ | .lit _ | .named .. | .expr .. => false
  | .un _ _ a | .raise _ a => a.hasSelf
  | .bin _ _ a b => a.hasSelf || b.hasSelf
  | .self _ => true
  | .ite c t e => c.hasSelf || t.hasSelf || e.hasSelf

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

/-- Prove `type` with the tactic: the proof, or why it failed (the first goal
left, or the error), with nothing left in the environment or the message log.
A proof that runs out of heartbeats or uses `sorry` fails. -/
def proveE (type : Lean.Expr) (tac : Syntax) : TermElabM (Except String Lean.Expr) :=
  withCurrHeartbeats do
  let s ← saveState
  -- Only an error this proof logs counts, not an earlier one of the command.
  let had ← MonadLog.hasErrors
  let n0 := (← Core.getMessageLog).toList.length
  tryCatchRuntimeEx
    (do
      let mv ← mkFreshExprMVar type
      let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
      let pf ← instantiateMVars mv
      let errs := !had && (← MonadLog.hasErrors)
      if gs.isEmpty && !pf.hasMVar && !pf.hasSorry && !errs then return .ok pf
      let why : String ← match gs with
        | g :: _ => pure s!"goal left: {← Meta.ppGoal g}"
        | [] => do
          let msgs ← ((← Core.getMessageLog).toList.drop n0).mapM (·.toString)
          pure s!"error: {msgs.headD "sorry or metavariables"}"
      s.restore; return .error why)
    fun e => do
      let m ← e.toMessageData.toString
      s.restore; return .error s!"exception: {m}"

/-- `proveE`, without the reason. -/
def prove (type : Lean.Expr) (tac : Syntax) : TermElabM (Option Lean.Expr) := do
  return (← proveE type tac).toOption

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
applied to expressions, for the closed instance `e` (a `UnFn` if `unary`). -/
def sampleFns (e : Lean.Expr) (unary : Bool) :
    TermElabM (RefFn × (List Substrait.Expr → Substrait.Expr)) := do
  if unary then
    let f ← evalUnFn e
    return (fun row => Profile.reference.un f (row.getD 0 .null),
      fun args => .un f (args.getD 0 (.lit .null)))
  else
    let f ← evalBinFn e
    return (fun row => Profile.reference.bin f (row.getD 0 .null) (row.getD 1 .null),
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

/-- One argument's split for `templateCases` (`Value.double_cases`): a value
that is not a double, kept whole (`d`: `x.isDouble = false`), `-0.0`, the
negative NaN, or a canonical double (`h`, `f`: its canonical code's facts).
Each branch names all three, `True` where it has none. -/
syntax "split4 " ident ident ident ident : tactic
macro_rules
  | `(tactic| split4 $x $h $f $d) => `(tactic|
      (rcases Value.double_cases $x with $d:ident | ⟨hx, $h:ident⟩ | ⟨hx, $h:ident⟩ |
          ⟨c, hx, $h:ident, hz, hn, $f:ident⟩ <;>
        first
          -- The canonical double (the only branch with `hz`), then the special ones.
          | (subst hx; revert hz; intro hz; have $d:ident : True := trivial)
          | (subst hx; have $f:ident : True := trivial; have $d:ident : True := trivial)
          | (have $h:ident : True := trivial; have $f:ident : True := trivial)))

/-- A value kept whole (`split4`'s first branch) split into its constructors,
for a goal that reads more of it than `templateTac`'s lemmas give (a function
of integers, `fpow`'s `floor`); a double's branch is impossible. -/
syntax "split_whole " ident ident : tactic
macro_rules
  | `(tactic| split_whole $x $d) => `(tactic|
      (try (cases $x:ident <;> (try simp only [Value.isDouble, Bool.true_eq_false] at $d:ident))))

/-- The lemmas that evaluate an expression over a row of arguments with the
reference's guard functions: the first simp set of `templateTac` and
`guardsTac`. -/
def evalNames : Array Name :=
  #[``Substrait.Expr.evalP, ``List.getD_cons_zero, ``List.getD_cons_succ,
    ``Outcome.ok_bind, ``Lowering.ref_isNum, ``Lowering.ref_isNull, ``Lowering.ref_not,
    ``Lowering.ref_raise, ``Lowering.ref_eq, ``Lowering.ref_lt, ``Lowering.ref_and,
    ``Lowering.ref_or, ``Lowering.ref_dadd, ``Lowering.ref_dsub, ``Lowering.ref_dmul]

/-- The template tactic's split on the arguments: four ways each
(`split4`), so that a double's comparisons, which read `canon c`, compute
(D31), and any other value stays whole; a function of doubles is the
reference's on it (`Lowering.duck_bin_nondouble_l`, …), and `templateTac`
splits it further only where a goal needs it (`split_whole`). `plain`: one
split of the whole value at once, for `guardsTac`'s issues. The names are unhygienic:
`templateTac`'s simp sets name them. -/
def splitArgs (unary : Bool) (plain : Bool := false) : TermElabM (TSyntax `tactic) := do
  let (x, y) := (mkIdent `x, mkIdent `y)
  -- `plain`: every constructor too, the whole value split at once.
  let sx ← if plain then
      `(tactic| (split4 $x $(mkIdent `hcx) $(mkIdent `hfx) $(mkIdent `hxx) <;>
        split_whole $x $(mkIdent `hxx)))
    else `(tactic| split4 $x $(mkIdent `hcx) $(mkIdent `hfx) $(mkIdent `hxx))
  if unary then return sx
  let sy ← if plain then
      `(tactic| (split4 $y $(mkIdent `hcy) $(mkIdent `hfy) $(mkIdent `hyy) <;>
        split_whole $y $(mkIdent `hyy)))
    else `(tactic| split4 $y $(mkIdent `hcy) $(mkIdent `hfy) $(mkIdent `hyy))
  `(tactic| ($sx:tactic <;> $sy:tactic))

/-- `splitArgs` on the last arguments introduced, named `x` and `y`. -/
def templateCases (unary : Bool) (plain : Bool := false) : TermElabM (TSyntax `tactic) := do
  let s ← splitArgs unary plain
  if unary then `(tactic| (rename_i $(mkIdent `x):ident; $s:tactic))
  else `(tactic| (rename_i $(mkIdent `x):ident $(mkIdent `y):ident; $s:tactic))

/-- The tactic for a template: evaluate the guard's functions (`natives`, the
engine's, and the reference's, and the lemmas `extra`), split on the
arguments' kinds (`templateCases`) and on the comparisons the template and
the profile make, and compute. -/
def templateTac (unfold natives extra : Array Name) (unary : Bool) (pre2 fin2 : Array Name := #[])
    (staged : Bool := true) (plain : Bool := false) :
    TermElabM Syntax := do
  let preNames := pre2 ++ evalNames ++ #[``Lowering.ref_imod_int] ++ natives ++ extra
  let valNames := #[``Value.isNum, ``Value.numPair, ``and3, ``or3, ``BinFn.apply,
    ``Value.isTrue,
    ``Bool.false_eq_true, ``ite_false, ``ite_true, ``Bool.not_true, ``Bool.not_false,
    ``Option.getD_some, ``Option.getD_none, ``Option.all_some, ``Option.all_none]
  let pre ← simpArgs preNames
  -- The whole values' hypotheses, for the lemmas on them (`isDouble`).
  let wholes : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (if unary then #[`hxx] else #[`hxx, `hyy]).mapM fun h =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent h):ident)
  let vals := (← simpArgs (preNames ++ valNames)) ++ wholes
  -- First without `BinFn.apply`, so that the lemmas on a whole value
  -- (`BinFn.apply_eq_nondouble_l`, …) rewrite before its match unfolds.
  let preW := pre ++ wholes
  -- Then the profile and the reference, and everything again.
  let ref ← simpArgs (preNames ++ valNames ++ unfold ++ #[``Profile.reference, ``raiseIf,
    ``Lowering.beq_int, ``UnFn.issue, ``BinFn.issue])
  -- Unfolding brings the special codes back: rewrite them to the variables.
  let eqs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (#[`hP, `hN, `hQ, `hO, `hM, `hZ, `hY, `g1, `g2, `g3, `g4, `g5, `g6, `g7, `g8, `g9, `g10, `g11, `g12, `g13, `g14, `g15, `g16, `hcx, `hfx] ++
      (if unary then #[] else #[`hcy, `hfy])).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $(mkIdent h):ident)
  -- A unary template's split leaves a profile's `Option` and the reference's
  -- binds (`round` below zero on DuckDB, `duckUn`).
  let late := if unary then #[``Outcome.ok_bind, ``Option.getD_some, ``Option.getD_none,
    ``BinFn.apply] else #[]
  let fin := (← simpArgs (unfold ++ extra ++ #[``Issue.isError, ``Outcome.Agree] ++ late ++ fin2)) ++
    eqs
  -- The profile and the reference unfold in stages on each goal the split
  -- leaves, the goal only: the profiles, then the issues, then the
  -- functions. One `simp` with all of them at once spends about 3 s a goal
  -- on `BinFn.apply`'s and `BinFn.issue`'s equations, and `On.Arith` has
  -- 21 such goals per theorem (#923's 11 kinds; docs/build-performance.md).
  -- On the goal only: at `*` they would rewrite `hP`, `hN`, … away before
  -- the issues bring the special codes back. `guardsTac`'s goals gain
  -- nothing from the stages (`staged := false`).
  let stage1 ← simpArgs (unfold ++ #[``Profile.reference, ``raiseIf])
  let stage2 ← simpArgs #[``BinFn.issue, ``UnFn.issue]
  let stage3 ← simpArgs #[``BinFn.apply, ``UnFn.apply]
  let stages ← if staged then
      `(tactic| (simp (config := { failIfUnchanged := false, decide := true }) only [$stage1,*]
                 simp (config := { failIfUnchanged := false, decide := true }) only [$stage2,*]
                 simp (config := { failIfUnchanged := false, decide := true }) only [$stage3,*]))
    else `(tactic| skip)
  -- `plain` (`guardsTac`'s goals, no `Outcome.Agree` to close a whole
  -- value's): every constructor at once.
  let cases ← templateCases unary plain
  let wholeSplit ← if unary then `(tactic| split_whole $(mkIdent `x) $(mkIdent `hxx))
    else `(tactic| (split_whole $(mkIdent `x) $(mkIdent `hxx); all_goals split_whole $(mkIdent `y) $(mkIdent `hyy)))
  -- The reference with the codes' equations and facts: at `*` for a binary
  -- template; on the goal only for a unary one, whose facts (`g6`, `hcx`, …)
  -- the final `simp_all` needs after a split (`round` below zero on DuckDB):
  -- at `*` they rewrite themselves to `True`.
  let refStep ← if unary then
      `(tactic| simp (config := { failIfUnchanged := false, decide := true }) only [$(ref ++ eqs),*])
    else
      `(tactic| simp (config := { failIfUnchanged := false, decide := true }) only [$(ref ++ eqs),*] at *)
  let codes := #[(``FloatCode.posInf, `cP, `hP), (``FloatCode.negInf, `cN, `hN),
    (``FloatCode.nan, `cQ, `hQ), (``FloatCode.one, `cO, `hO), (``FloatCode.negOne, `cM, `hM),
    (``FloatCode.negZero, `cZ, `hZ), (``FloatCode.negNan, `cY, `hY)]
  let gens ← codes.mapM fun (c, v, h) =>
    `(tactic| generalize $(mkIdent h):ident : $(mkIdent c):ident = $(mkIdent v):ident at *)
  `(tactic| (
    -- The special codes (`±∞`, NaN, `±1`) as variables with their order, so
    -- that nothing evaluates their 600-digit values and `omega` can compare;
    -- before `intros`, so that no argument is reintroduced.
    have $(mkIdent `f1) := FloatCode.negInf_lt_negOne
    have $(mkIdent `f2) := FloatCode.negOne_lt_zero
    have $(mkIdent `f3) := FloatCode.zero_lt_one
    have $(mkIdent `f4) := FloatCode.one_lt_posInf
    have $(mkIdent `f5) := FloatCode.posInf_lt_nan
    -- `-0.0` and the negative NaN below `-∞`, and the canonical codes.
    have $(mkIdent `f6) := FloatCode.negZero_lt_negNan
    have $(mkIdent `f7) := FloatCode.negNan_lt_negInf
    have $(mkIdent `g1) := FloatCode.canon_posInf
    have $(mkIdent `g2) := FloatCode.canon_negInf
    have $(mkIdent `g3) := FloatCode.canon_nan
    have $(mkIdent `g4) := FloatCode.canon_one
    have $(mkIdent `g5) := FloatCode.canon_negOne
    have $(mkIdent `g6) := FloatCode.canon_negZero'
    have $(mkIdent `g7) := FloatCode.canon_negNan'
    have $(mkIdent `g8) := FloatCode.canon_zero
    have $(mkIdent `g9) := FloatCode.canon_negInf_succ
    have $(mkIdent `g10) := FloatCode.canon_posInf_pred
    have $(mkIdent `g11) := FloatCode.floor_negZero
    have $(mkIdent `g12) := FloatCode.floor_negNan
    have $(mkIdent `g13) := FloatCode.round_negZero
    have $(mkIdent `g14) := FloatCode.round_negNan
    have $(mkIdent `g15) := FloatCode.ceil_negZero
    have $(mkIdent `g16) := FloatCode.ceil_negNan
    $[$gens]*
    intros
    simp (config := { decide := true }) only [$pre,*]
    $cases:tactic <;> simp (config := { failIfUnchanged := false, decide := true }) only [$preW,*]
    all_goals simp (config := { failIfUnchanged := false, decide := true }) only [$vals,*]
    all_goals first
      | exact Outcome.agree_refl _
      | ($wholeSplit:tactic
         all_goals simp (config := { failIfUnchanged := false, decide := true }) only [$vals,*]
         all_goals first
           | exact Outcome.agree_refl _
           | ($stages:tactic
              $refStep:tactic
              iterate 10
                all_goals try
                  lowering_split_decide <;>
                    simp (config := { failIfUnchanged := false, decide := true }) only [$(mkIdent `hd):ident, decide_true, decide_false, ite_true, ite_false, Option.getD_some, Option.getD_none, Outcome.ok_bind]
              all_goals (repeat' split)
              all_goals first
                | (simp_all [$fin,*]; done)
                | (simp_all [$fin,*] <;> omega)
                | omega))))

/-! ## Generated source

`generate_lowering … writing "dir"` also writes what it found as Lean source,
so that a build checks the entries instead of searching for them (`lake
build` elaborates `dir/<Area>.lean` and `dir/Table.lean`; `poe
regen-lowering` runs the search again). Each proof is one of the tactics
below with the generator's own simp sets, or a hand-written proof's name. -/

/-- An expression as source: full names, no abbreviation. -/
def ppSource (e : Lean.Expr) : MetaM String := do
  let fmt ← withOptions (fun o =>
    (((o.setBool `pp.fullNames true).setBool `pp.deepTerms true).set `pp.maxSteps (100000000 : Nat)
      |>.setBool `pp.fieldNotation false |>.setBool `pp.proofs true
      |>.setBool `pp.structureInstances false)) (ppExpr e)
  return fmt.pretty 100

/-- The generated module a construct's entry goes to: entries of an area
check in parallel, and a change rebuilds its area only. The doubles' entries
are two areas, the arithmetic and the powers, so that neither module's peak
memory nears its ceiling (`scripts/lean-budget.json`). -/
def areaOf (c : Name) : String :=
  match c.componentsRev.head!.toString with
  | "fmath" | "fround" | "fceil" => "Math"
  | "fadd" | "fsub" | "fmul" | "fdiv" | "fdivIeee" | "fmod" => "Arith"
  | "fpow" | "fatan2" | "flogb" => "Powers"
  | "idiv" | "imod" | "fit" | "ipow" => "Integers"
  | "bit" => "Bits"
  | _ => "Other"

/-- Generated source by module (`"Native"`, an area), in order. -/
abbrev Sink := IO.Ref (Array (String × String))

syntax (name := loweringNativeTac) "lowering_native " "[" ident,* "]" : tactic
/-- The tactic for a template's guards (`Expr.GuardsAt` with every guard
dropped): the template tactic, with the guards and the reference's issues
unfolded first. -/
def guardsTac (unfold natives extra : Array Name) (unary : Bool) (agree? : Option Name := none) :
    TermElabM Syntax := do
  let t ← templateTac unfold natives extra unary
    #[``Expr.GuardsAt, ``Expr.raiseMsg?, ``Outcome.FiresOnly, ``Option.map]
    #[``Issue.name, ``Option.map, ``Outcome.FiresOnly] (staged := false) (plain := true)
  let general : TSyntax `tactic := ⟨t⟩
  let some agree := agree? | `(tactic| first | (intros; trivial) | $general:tactic)
  -- One guard, from the entry's agreement (`Expr.GuardsAt.one`): where it is
  -- true the template raises, so the reference does, with the guard's issue
  -- if all of the function's issues have its name.
  let pre ← simpArgs (evalNames ++ natives)
  let issueFn := mkIdent (if unary then ``UnFn.issue else ``BinFn.issue)
  -- The arguments named at `intro`: `rename_i` would name the issue's
  -- `k` and `h`, which the `refine` below introduces after them.
  let cases ← splitArgs unary (plain := true)
  let intro ← if unary then `(tactic| intro $(mkIdent `x):ident)
    else `(tactic| intro $(mkIdent `x):ident $(mkIdent `y):ident)
  let ag ← if unary then `(($(mkIdent agree) _)) else `(($(mkIdent agree) _ _))
  let names ← simpArgs #[``nanIssue, ``domainIssue, ``rangeIssue, ``wrapIf, ``wrapNum]
  `(tactic| first
    | (intros; trivial)
    -- A template that never raises (`round` below zero on DuckDB): no guard.
    | (intros; exact Substrait.Expr.guardsAt_of_noGuards _ rfl)
    | ($intro:tactic
       refine Substrait.Expr.GuardsAt.one rfl $ag ?_ ?_ ?_ (Substrait.Expr.guardsAt_of_noGuards _ rfl)
       · simp [$pre,*, Substrait.Outcome.err?, bind, Except.bind]
       · refine Substrait.Outcome.raises_named fun k h => ?_
         unfold $issueFn:ident at h
         $cases:tactic <;> simp only [$names,*, reduceCtorEq] at h <;> (try split at h) <;>
           (try split at h) <;> cases k <;> simp_all [Substrait.Issue.name]
       · simp only [$pre,*]
         exact ⟨_, rfl⟩)
    | $general:tactic)

syntax (name := loweringGuardsTac) "lowering_guards " "[" ident,* "]" "[" ident,* "]" "[" ident,* "]"
  (&" unary")? (&" agree " ident)? : tactic

syntax (name := loweringTemplateTac) "lowering_template " "[" ident,* "]" "[" ident,* "]" "[" ident,* "]"
  (&" unary")? : tactic

open Tactic in
@[tactic loweringNativeTac] def evalLoweringNative : Tactic := fun stx => do
  Generated.proveOrAdmit do
    let us ← stx[2].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    evalTactic (← nativeTac us)

open Tactic in
@[tactic loweringTemplateTac] def evalLoweringTemplate : Tactic := fun stx => do
  Generated.proveOrAdmit do
    let names (i : Nat) := stx[i].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    evalTactic (← templateTac (← names 2) (← names 5) (← names 8) !stx[10].isNone)

open Tactic in
@[tactic loweringGuardsTac] def evalLoweringGuards : Tactic := fun stx => do
  Generated.proveOrAdmit do
    let names (i : Nat) := stx[i].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
    let agree ← if stx[11].isNone then pure none
      else some <$> realizeGlobalConstNoOverloadWithInfo stx[11][1]
    evalTactic (← guardsTac (← names 2) (← names 5) (← names 8) (!stx[10].isNone) agree)

/-! ## Emitting -/

/-- Try to prove the construct `c` native under the profile `pE`; emit
`tbl.c_native` and the entry `tbl.c` if it is. -/
def lowerNative (tbl : Name) (pE : Lean.Expr) (tac : Syntax) (unary : Bool) (c : Name)
    (sink : Option Sink := none) : TermElabM Bool := do
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
    let entryTy ← mkForallFVars ps (← inferType entry)
    let entryVal ← mkLambdaFVars ps entry
    addAndCompile <| .defnDecl {
      name := tbl ++ short, levelParams := [], safety := .safe, hints := .abbrev
      type := entryTy, value := entryVal }
    if let some out := sink then
      out.modify (·.push ("Native",
        s!"theorem {nativeName} : {← ppSource ty} := by\n  native_tac\n\n" ++
        s!"abbrev {tbl ++ short} : {← ppSource entryTy} :=\n  {← ppSource entryVal}\n\n"))
    return true

/-- A construct: a constructor, with its finite parameters (an option, a
width) given as constructors of their types; `ps` are its other parameters,
which the entry quantifies over. -/
structure Construct where
  ctor : Name
  unary : Bool
  args : Array Name

def Construct.short (k : Construct) : Name :=
  k.args.foldl (fun n a => n.appendAfter s!"_{a.componentsRev.head!}") k.ctor.componentsRev.head!

def Construct.label (k : Construct) : String :=
  let c := (k.ctor.replacePrefix `Substrait .anonymous).toString
  k.args.foldl (fun s a => s ++ s!" .{a.componentsRev.head!}") c

/-- The instances of a constructor whose parameters all have types of
constructors without fields (`OverflowMode`, `IntWidth`); none otherwise. -/
def instances (c : Name) (unary : Bool) : MetaM (Option (List Construct)) := do
  forallTelescope (← getConstInfoCtor c).type fun ps _ => do
    if ps.isEmpty then return none
    let mut combos : List (Array Name) := [#[]]
    for x in ps do
      let ty ← whnf (← inferType x)
      let some ind := ty.constName? | return none
      let some (.inductInfo iv) := (← getEnv).find? ind | return none
      unless iv.numParams == 0 && iv.numIndices == 0 do return none
      for k in iv.ctors do
        unless (← getConstInfoCtor k).numFields == 0 do return none
      combos := combos.flatMap fun a => iv.ctors.map a.push
    return some (combos.map fun a => ⟨c, unary, a⟩)

/-- `finite_values% T`: the values of the inductive `T` (`UnFn`, `BinFn`) whose
constructor has no fields, or only fields of types of constructors without
fields (`instances`): every function a table's export may list, from the type
itself, so a new constructor is listed without anyone adding it. -/
elab "finite_values% " t:ident : term => do
  let ind ← realizeGlobalConstNoOverloadWithInfo t
  let mut out : Array Lean.Expr := #[]
  for c in (← getConstInfoInduct ind).ctors do
    if (← getConstInfoCtor c).numFields == 0 then
      out := out.push (Lean.mkConst c)
    else if let some ks ← instances c true then
      out := out ++ (ks.map fun k => mkAppN (Lean.mkConst c) (k.args.map Lean.mkConst)).toArray
  mkListLit (Lean.mkConst ind) out.toList

/-- Search for a template for the construct `k`, test the candidates on the
samples, prove the first that passes, and emit `tbl.k_agree` and the entry
`tbl.k`. Hand-written schemas come first; a construct the engine does not
have (`excluded`) gets no template that calls it. -/
def lowerSearch (tbl : Name) (pE : Lean.Expr) (p : Profile) (schemas : Schemas) (tac : Syntax)
    (excluded : Bool) (k : Construct) (hint? : Option String := none) (sink : Option Sink := none)
    (guards : Option ((Name → TermElabM Syntax) × IO.Ref (Array String)) := none) :
    TermElabM (Except String String) := do
  let unary := k.unary
  let n := if unary then 1 else 2
  forallTelescope (← getConstInfoCtor k.ctor).type fun ps _ => do
    let fixed := k.args.map Lean.mkConst
    let ps := ps.extract fixed.size ps.size
    let selfE := mkAppN (Lean.mkConst k.ctor) (fixed ++ ps)
    let some sample ← if ps.isEmpty then pure (some selfE)
      else sampleCtor k.ctor | return .error "missing: a parameter without a sample value"
    let (ref, mk) ← sampleFns sample unary
    let rows := if unary then (samples ++ boundarySamples).map ([·]) else sampleRows n
    let msg := rows.findSome? fun row => match ref row with | .error k => some k.name | .ok _ => none
    let schema ← if unary then pure ((schemas.un (← evalUnFn sample)).map (·, true))
      else pure ((schemas.bin (← evalBinFn sample)).map (·, true))
    -- The plain call is tried as a candidate for an instance (`fmath .atan`):
    -- its constructor as a whole is not native.
    -- Guards compare with constants of the construct's kind (#923).
    let kind : NumKind := if ["Arith", "Powers", "Math"].contains (areaOf k.ctor) then .float else .int
    let cands := if k.args.isEmpty then (candidates kind n msg).drop 1 else candidates kind n msg
    let searched := cands.filter (fun c => !excluded || !c.hasSelf) ++
      (if unary then chains (harvest ref rows) else [])
    let passedRef ← IO.mkRef 0
    -- Each candidate gets its own heartbeats: a construct may try many.
    let attempt (cand : Tm) (written : Bool) : TermElabM (Option String) := do
      let t := cand.toModel mk
      unless (List.range n).all (· ∈ t.must) && agreesOnSamples p ref rows t do return none
      passedRef.modify (· + 1)
      let tmpl := cand.toTerm selfE unary
      let agreeTy ← withLocalDeclD `x (Lean.mkConst ``Value) fun x => withLocalDeclD `y (Lean.mkConst ``Value) fun y => do
        let xs := if unary then #[x] else #[x, y]
        let row ← mkListLit (Lean.mkConst ``Value) xs.toList
        let lhs ← mkAppM ``Expr.evalP #[pE, row, tmpl]
        let rhs ← mkAppM (if unary then ``Profile.un else ``Profile.bin)
          (#[Lean.mkConst ``Profile.reference, selfE] ++ xs)
        mkForallFVars (ps ++ xs) (← mkAppM ``Outcome.Agree #[lhs, rhs])
      -- A hand-written schema may come with its proof, `Lowering.<construct>_agree`.
      let hand := ``Lowering ++ k.short.appendAfter "_agree"
      let byHand := written && (← getEnv).contains hand
      let tac : Syntax ← if byHand then
          `(tactic| (intros; apply $(mkIdent hand))) else pure tac
      let some agree ← prove agreeTy tac | return none
      let agreeName := tbl ++ k.short.appendAfter "_agree"
      addDecl <| .thmDecl { name := agreeName, levelParams := [], type := agreeTy, value := agree }
      let mustE ← mkAppM ``Expr.must #[tmpl]
      let mem (i : Nat) := mkAppM ``Membership.mem #[mustE, toExpr i]
      let strictTy ← if unary then mem 0 else mkAppM ``And #[← mem 0, ← mem 1]
      -- A hand-written template comes with its strictness, by name: `T_must`
      -- for a template written as the constant `T` (DuckDB's `<<`, `round`
      -- and `ceil`, `SubstraitLean/LoweringDuckDB/Lemmas.lean`, which this
      -- module does not import).
      let env ← getEnv
      let named : Option Name := tmpl.constName?.bind fun c =>
        let m := c.appendAfter "_must"
        if env.contains m then some m else none
      let strictTac ← match named with
        | some m => `(tactic| exact $(mkIdent m))
        | none => `(tactic| simp [Substrait.Expr.must])
      let some strict ← prove strictTy strictTac | return none
      let entry ← mkAppM (if unary then ``UnEntry.mk else ``BinEntry.mk)
        #[tmpl, strict, mkAppN (Lean.mkConst agreeName) ps]
      let entryTy ← mkForallFVars ps (← inferType entry)
      addAndCompile <| .defnDecl {
        name := tbl ++ k.short, levelParams := [], safety := .safe, hints := .abbrev
        type := entryTy, value := ← mkLambdaFVars ps entry }
      -- The guards (`proving_guards`): each exact (`Expr.GuardsAt`, all dropped).
      if let some (gtac, failed) := guards then
        let issueFn := if unary then ``UnFn.issue else ``BinFn.issue
        let none' := Lean.mkLambda `_ .default (Lean.mkConst ``String) (Lean.mkConst ``Bool.false)
        let guardsTy ← withLocalDeclD `x (Lean.mkConst ``Value) fun x =>
            withLocalDeclD `y (Lean.mkConst ``Value) fun y => do
          let xs := if unary then #[x] else #[x, y]
          let row ← mkListLit (Lean.mkConst ``Value) xs.toList
          let iss ← mkAppM issueFn (#[selfE] ++ xs)
          mkForallFVars (ps ++ xs) (← mkAppM ``Expr.GuardsAt #[pE, none', iss, row, tmpl])
        let gName := tbl ++ k.short.appendAfter "_guards"
        -- A hand-written schema may come with its guards' proof, `Lowering.<construct>_guards`.
        let handG := ``Lowering ++ k.short.appendAfter "_guards"
        let byHandG := written && (← getEnv).contains handG
        let gtac : Syntax ← if byHandG then `(tactic| (intros; apply $(mkIdent handG)))
          else gtac agreeName
        match ← withCurrHeartbeats (prove guardsTy gtac) with
        | some gp =>
          addDecl <| .thmDecl { name := gName, levelParams := [], type := guardsTy, value := gp }
          if let some out := sink then
            let proof := if byHandG then s!"intros; apply {handG}"
              else if unary then s!"guards_un_tac {agreeName}" else s!"guards_bin_tac {agreeName}"
            out.modify (·.push ("Guards",
              (if written then "set_option maxHeartbeats 1600000 in\n"
                else "set_option maxHeartbeats 800000 in\n") ++
              s!"theorem {gName} : {← ppSource guardsTy} := by\n  {proof}\n\n"))
        | none => failed.modify (·.push k.label)
      if let some out := sink then
        unless ps.isEmpty do throwError "{k.label}: a template with parameters cannot be written out"
        let proof := if byHand then s!"intros; apply {hand}" else if unary then "un_tac" else "bin_tac"
        let strictSrc := match named with
          | some m => s!"exact {m}"
          | none => "simp [Substrait.Expr.must]"
        out.modify (·.push (areaOf k.ctor,
          -- A proof gets the budget the search gave it.
          (if byHand then "" else if written then "set_option maxHeartbeats 3200000 in\n"
            else "set_option maxHeartbeats 800000 in\n") ++
          s!"theorem {agreeName} : {← ppSource agreeTy} := by\n  {proof}\n\n" ++
          s!"abbrev {tbl ++ k.short} : {← ppSource entryTy} :=\n" ++
          s!"  ⟨{← ppSource tmpl}, by {strictSrc}, {agreeName}⟩\n\n"))
      let shown := cand.show k.ctor.componentsRev.head!.toString
      return some (if written then s!"hand-written schema: {shown}" else shown)
    -- The cache's template first (`LoweringHint`), found among the candidates
    -- by how it prints; then the schema, then the search.
    let fn := k.ctor.componentsRev.head!.toString
    let shownOf (c : Tm) (w : Bool) : String :=
      if w then s!"hand-written schema: {c.show fn}" else c.show fn
    let all := schema.toList ++ searched.map (·, false)
    let order := match hint? with
      | some h => all.filter (fun (c, w) => shownOf c w == h) ++ all.filter (fun (c, w) => shownOf c w != h)
      | none => all
    for (cand, written) in order do
      -- A binary template splits on 13 kinds of each argument (#923, a
      -- double three ways): a candidate that passes the samples gets four
      -- times the default, a hand-written schema, one proof rather than one
      -- of many and the heaviest guards (`fpow`'s), sixteen.
      let budget (ctx : Core.Context) :=
        { ctx with maxHeartbeats := ctx.maxHeartbeats * (if written then 16 else 4) }
      let how ← tryCatchRuntimeEx
        (withTheReader Core.Context budget (withCurrHeartbeats (attempt cand written)))
        fun _ => pure none
      if let some how := how then return .ok how
    let passed ← passedRef.get
    return .error s!"missing: {passed} of {schema.toList.length + searched.length} candidates passed the samples, none proved"

/-- The constructors templates are built from. -/
def guardFns : List Name :=
  [``UnFn.isNum, ``UnFn.isNull, ``UnFn.not, ``UnFn.raise, ``UnFn.ffloor, ``BinFn.eq, ``BinFn.lt,
   ``BinFn.and, ``BinFn.or, ``BinFn.dadd, ``BinFn.dsub, ``BinFn.dmul, ``BinFn.imod]

syntax (name := generateLowering) "generate_lowering " ident " : " term
  " unfolding " "[" ident,* "]" " using " "[" ident,* "]" " excluding " "[" ident,* "]"
  (" hand_written " ident)? (" cache " ident)? (" writing " str)? (" proving_guards")? : command

unsafe def evalHintsImpl (n : Name) : TermElabM (List LoweringHint) := do
  Meta.evalExpr (List LoweringHint) (← mkAppM ``List #[Lean.mkConst ``LoweringHint]) (Lean.mkConst n)
@[implemented_by evalHintsImpl] opaque evalHints (n : Name) : TermElabM (List LoweringHint)

unsafe def evalSchemasImpl (n : Name) : TermElabM Schemas := evalConst Schemas n
@[implemented_by evalSchemasImpl] opaque evalSchemas (n : Name) : TermElabM Schemas

/-- `generate_lowering L : p unfolding [defs] using [lemmas] excluding [ctors] hand_written S cache hints`:
`defs` unfold the profile, `lemmas` help the proofs, `ctors` are functions the
engine does not have, which every template must avoid, `S` (optional, a
`Schemas`) the engine's hand-written schemas, and `hints` (optional, a
`List LoweringHint`) the templates to try first. -/
@[command_elab generateLowering]
def elabGenerateLowering : CommandElab := fun stx => do
  Generated.requireChecked "generate_lowering"
  let short := stx[1].getId
  let tbl := (← getCurrNamespace) ++ short
  let pStx : Term := ⟨stx[3]⟩
  let names (i : Nat) := (stx[i].getSepArgs).mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let unfold ← names 6
  let extra ← names 10
  let excluded ← names 14
  let schemasName ← if stx[16].isNone then pure none
    else some <$> liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[16][1])
  let cacheName ← if stx[17].isNone then pure none
    else some <$> liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[17][1])
  let writeDir : Option String := if stx[18].isNone then none else stx[18][1].isStrLit?
  let provingGuards := !stx[19].isNone
  let guardFailures : IO.Ref (Array String) ← IO.mkRef #[]
  let sink : Option Sink ← if writeDir.isSome then some <$> IO.mkRef #[] else pure none
  let ctors ← [(``UnFn, true), (``BinFn, false)].flatMapM fun (ind, unary) => do
    return (← getConstInfoInduct ind).ctors.map (·, unary)
  -- Each constructor: native, or its constructs, each with how it was lowered.
  let (results, natives, pSrc) ← liftTermElabM do
    let pE ← instantiateMVars (← elabTermEnsuringType pStx (Lean.mkConst ``Profile))
    let p ← evalProfile pE
    let hints ← match cacheName with | some n => evalHints n | none => pure []
    let schemas ← match schemasName with | some n => evalSchemas n | none => pure ({} : Schemas)
    let hintOf (k : Construct) : Option String :=
      (hints.find? fun h => h.table == short.toString && h.construct == k.label && !h.template.isEmpty).map
        (·.template)
    let mut results : Array (Name × Option (Array (Construct × Except String String × Nat))) := #[]
    -- Natives first: templates are built from them.
    let ntac ← nativeTac unfold
    let mut rest := #[]
    let mut natives := #[]
    for (c, unary) in ctors do
      let t0 ← IO.monoMsNow
      if !excluded.contains c then
        -- Each constructor starts afresh: heartbeats count all of the
        -- command's work, and every new constructor adds to it.
        if ← withCurrHeartbeats (lowerNative tbl pE ntac unary c sink) then
          results := results.push (c, some #[(⟨c, unary, #[]⟩, .ok "native", (← IO.monoMsNow) - t0)])
          if guardFns.contains c then natives := natives.push (tbl ++ c.componentsRev.head!.appendAfter "_native")
          continue
      rest := rest.push (c, unary)
    for (c, unary) in rest do
      let tac ← templateTac unfold natives extra unary
      let guards ← if provingGuards then
          pure (some (fun a => guardsTac unfold natives extra unary (some a), guardFailures))
        else pure none
      let ks := (← withCurrHeartbeats (instances c unary)).getD [⟨c, unary, #[]⟩]
      let mut done := #[]
      for k in ks do
        let t0 ← IO.monoMsNow
        let t := tac
        let how ← withCurrHeartbeats (lowerSearch tbl pE p schemas t (excluded.contains c) k (hintOf k) sink guards)
        done := done.push (k, how, (← IO.monoMsNow) - t0)
      results := results.push (c, some done)
    return (results, natives, ← ppSource pE)
  let entries (c : Name) : Array (Construct × Except String String × Nat) :=
    ((results.find? (·.1 == c)).bind (·.2)).getD #[]
  let missing := results.flatMap fun (_, r) => (r.getD #[]).filterMap fun (k, how, _) =>
    match how with | .error e => some s!"{k.label} ({e})" | .ok _ => none
  -- The table: an arm for each constructor, or for each construct of one.
  let arms (ind : Name) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
    (← getConstInfoInduct ind).ctors.toArray.flatMapM fun c => do
      let nargs := (← getConstInfoCtor c).numFields
      let xs := (List.range nargs).toArray.map fun i => mkIdent (Name.mkSimple s!"a{i}")
      let es := entries c
      if let some (k, _, _) := es[0]? then
        if !k.args.isEmpty then
          return ← es.mapM fun (k, how, _) => do
            let pats ← k.args.mapM fun a => `($(mkIdent a):ident)
            let rhs ← match how with
              | .error _ => `(none)
              | .ok _ => `(some $(mkIdent (tbl ++ k.short)))
            `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) $pats* => $rhs)
      let rhs ← if es.any (·.2.1 matches .error _) || es.isEmpty then `(none)
        else `(some ($(mkIdent (tbl ++ c.componentsRev.head!)) $xs*))
      return #[← `(Lean.Parser.Term.matchAltExpr| | $(mkIdent c) $xs* => $rhs)]
  let unAlts ← arms ``UnFn
  let binAlts ← arms ``BinFn
  elabCommand (← `(def $(mkIdent short) : Lowering $pStx :=
    ⟨fun f => match f with $unAlts:matchAlt*, fun f => match f with $binAlts:matchAlt*⟩))
  -- The coverage report, in the constructors' order.
  let rows := ctors.toArray.flatMap fun (c, _) => (entries c).map fun (k, how, ms) =>
    (k.label, (match how with | .ok h => h | .error e => e), ms)
  let rowStx ← rows.mapM fun (c, how, ms) => `(($(quote c), $(quote how), $(quote ms)))
  elabCommand (← `(def $(mkIdent (short ++ `coverage)) : List (String × String × Nat) := [$rowStx,*]))
  if missing.isEmpty then
    elabCommand (← `(theorem $(mkIdent (short ++ `total)) : ($(mkIdent tbl)).Total :=
      ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),
       fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a))⟩))
  else
    logError m!"no lowering found for {missing.toList}"
  let failedGuards ← guardFailures.get
  unless failedGuards.isEmpty do
    logError m!"guards not proved for {failedGuards.toList}"
  -- The generated modules (`writing`): what was found, to be checked by a
  -- build instead of searched for again.
  let some dir := writeDir | return
  let some sink := sink | return
  unless missing.isEmpty do return
  let chunks ← sink.get
  let modOf (area : String) : String := (dir.replace "/" ".") ++ "." ++ area
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let deps := ((unfold ++ extra).filterMap moduleOf).toList.eraseDups
  let names (ns : Array Name) := ", ".intercalate (ns.toList.map toString)
  let macros :=
    s!"local macro \"native_tac\" : tactic => `(tactic| lowering_native [{names unfold}])\n" ++
    s!"local macro \"un_tac\" : tactic =>\n  `(tactic| lowering_template [{names unfold}] [{names natives}]\n" ++
    s!"    [{names extra}] unary)\n" ++
    s!"local macro \"bin_tac\" : tactic =>\n  `(tactic| lowering_template [{names unfold}] [{names natives}]\n" ++
    s!"    [{names extra}])\n"
  let header (imports : List String) (what : String) : String :=
    "\n".intercalate (imports.map (s!"import {·}")) ++ "\n\n" ++
    s!"/-!\n# {what}\n\nGenerated by `generate_lowering … writing` (`SubstraitLean/LoweringSearch.lean`): do not edit. To regenerate,\n" ++
    "run `poe regen-lowering` from `python/` (`docs/proofs.md`, \"Generated modules\"). A build\n" ++
    "checks these entries; it does not search for them.\n-/\n\ngenerated_entries\n\nopen Substrait\n\n" ++ macros ++ "\n"
  let base := ["SubstraitLean.LoweringSearch"] ++ deps.map toString
  let areas := (chunks.toList.map (·.1)).eraseDups.filter fun a => a != "Native" && a != "Guards"
  IO.FS.createDirAll dir
  let body (area : String) := String.join ((chunks.toList.filter (·.1 == area)).map (·.2))
  IO.FS.writeFile s!"{dir}/Native.lean"
    (header base s!"{tbl}: the functions the engine computes as the reference does" ++ body "Native")
  for area in areas do
    IO.FS.writeFile s!"{dir}/{area}.lean"
      (header (base ++ [modOf "Native"]) s!"{tbl}: {area}" ++ body area)
  -- The table, its coverage report and its totality.
  let armText (ind : Name) : CommandElabM String := do
    let lines ← (← getConstInfoInduct ind).ctors.mapM fun c => do
      let nargs := (← getConstInfoCtor c).numFields
      let es := entries c
      if let some (k, _, _) := es[0]? then
        if !k.args.isEmpty then
          return "\n".intercalate (es.toList.map fun (k, how, _) =>
            let pats := " ".intercalate (k.args.toList.map toString)
            let rhs := match how with | .error _ => "none" | .ok _ => s!"some {tbl ++ k.short}"
            s!"    | {c} {pats} => {rhs}")
      let xs := " ".intercalate ((List.range nargs).map (s!"a{·}"))
      let rhs := if es.any (·.2.1 matches .error _) || es.isEmpty then "none"
        else s!"some ({tbl ++ c.componentsRev.head!} {xs})"
      return s!"    | {c} {xs} => {rhs}"
    return "\n".intercalate lines
  let covRows := rows.toList.map fun (c, how, _) => s!"  ({repr c}, {repr how}, 0)"
  let table :=
    header (base ++ (("Native" :: areas).map modOf)) s!"{tbl}: the table" ++
    s!"def {tbl} : Substrait.Lowering ({pSrc}) :=\n  ⟨fun f => match f with\n{← armText ``UnFn},\n" ++
    s!"   fun f => match f with\n{← armText ``BinFn}⟩\n\n" ++
    s!"/-- How each construct is lowered (`--lowering-coverage`). -/\n" ++
    s!"def {tbl}.coverage : List (String × String × Nat) := [\n{",\n".intercalate covRows}]\n\n" ++
    s!"theorem {tbl}.total : ({tbl}).Total :=\n" ++
    "  ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),\n" ++
    "   fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a))⟩\n"
  IO.FS.writeFile s!"{dir}/Table.lean" table
  logInfo m!"wrote {dir}: Native, {areas}, Table"
  -- The guards (`proving_guards`), in a module of their own after the table,
  -- so that the table's modules do not change: every guard is exact, so a
  -- writer may drop them all (`guardsFor_none`).
  unless provingGuards && failedGuards.isEmpty do return
  let guardArms (ind : Name) (unary : Bool) : CommandElabM String := do
    let vacuous := "fun ⟨_, h⟩ => absurd h Bool.false_ne_true"
    let lines ← (← getConstInfoInduct ind).ctors.mapM fun c => do
      let nargs := (← getConstInfoCtor c).numFields
      let rhs (how : String) (k : Construct) : String :=
        if how == "native" then s!"⟨{vacuous}, fun {if unary then "_" else "_ _"} => trivial⟩"
        else
          let g := tbl ++ k.short.appendAfter "_guards"
          s!"⟨{vacuous}, {g}⟩"
      let es := entries c
      if let some (k, _, _) := es[0]? then
        if !k.args.isEmpty then
          return "\n".intercalate (es.toList.map fun (k, how, _) =>
            let pats := " ".intercalate (k.args.toList.map toString)
            s!"    | {c} {pats} => {rhs (how.toOption.getD "") k}")
      let xs := " ".intercalate ((List.range nargs).map fun _ => "_")
      let (k, how) := match es[0]? with
        | some (k, how, _) => (k, how.toOption.getD "")
        | none => (⟨c, unary, #[]⟩, "")
      return s!"    | {c} {xs} => {rhs how k}"
    return "\n".intercalate lines
  let guardMacros :=
    s!"local macro \"guards_un_tac \" a:ident : tactic =>\n  `(tactic| lowering_guards [{names unfold}] [{names natives}]\n" ++
    s!"    [{names extra}] unary agree $a)\n" ++
    s!"local macro \"guards_bin_tac \" a:ident : tactic =>\n  `(tactic| lowering_guards [{names unfold}] [{names natives}]\n" ++
    s!"    [{names extra}] agree $a)\n\n"
  let prop (unary : Bool) : String :=
    let args := if unary then "x" else "x y"
    let row := if unary then "[x]" else "[x, y]"
    let must := if unary then "0 ∈ (en.tmpl.keepGuards fun _ => false).must"
      else "0 ∈ (en.tmpl.keepGuards fun _ => false).must ∧ 1 ∈ (en.tmpl.keepGuards fun _ => false).must"
    s!"((∃ m, (fun _ : String => false) m = true) → {must}) ∧\n      " ++
      s!"∀ {args}, en.tmpl.GuardsAt ({pSrc}) (fun _ => false) (f.issue {args}) {row}"
  let guardsText :=
    header (base ++ [modOf "Table"]) s!"{tbl}: the guards" ++ guardMacros ++ body "Guards" ++
    s!"/-- Each unary entry's guards are exact. -/\n" ++
    s!"theorem {tbl}.guardsUn : ∀ f : Substrait.UnFn,\n" ++
    s!"    match ({tbl}).un f with\n    | some en => {prop true}\n    | none => True := fun f => match f with\n" ++
    s!"{← guardArms ``UnFn true}\n\n" ++
    s!"/-- Each binary entry's guards are exact. -/\n" ++
    s!"theorem {tbl}.guardsBin : ∀ f : Substrait.BinFn,\n" ++
    s!"    match ({tbl}).bin f with\n    | some en => {prop false}\n    | none => True := fun f => match f with\n" ++
    s!"{← guardArms ``BinFn false}\n\n" ++
    s!"/-- **Every guard of the table is exact** (`Lowering.GuardsFor`): a writer may drop them all. -/\n" ++
    s!"theorem {tbl}.guardsFor_none : ({tbl}).GuardsFor fun _ => false :=\n" ++
    s!"  ⟨fun f en h => by have g := {tbl}.guardsUn f; rw [h] at g; exact g,\n" ++
    s!"   fun f en h => by have g := {tbl}.guardsBin f; rw [h] at g; exact g⟩\n"
  IO.FS.writeFile s!"{dir}/Guards.lean" guardsText
  logInfo m!"wrote {dir}/Guards.lean"

end Substrait.LoweringSearch
