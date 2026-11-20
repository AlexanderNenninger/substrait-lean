import Sverify.Engines.LoweringSearch

/-!
# The guards no engine owns (#271)

Template pieces the hand-written schemas of several engines share
(`generate_lowering … hand_written`): DuckDB's (`Sverify.DuckDB.LoweringSchemas`)
and, next, Spark's and Polars's. Each copies one of the reference's error
conditions, atom for atom, where an engine's IEEE operation gives NaN, `±∞` or
`0` instead. They keep the namespace `Substrait.LoweringSearch`, so a generated
module reads the same names as before.
-/

namespace Substrait.LoweringSearch

open Lean

/-- The guard on which a double operation makes a NaN of numbers (`nanCase`),
atom for atom. -/
def nanGuard : BinFn → Option Tm
  | .fadd => some (orFn (andFn (eqFn (.field 0) posInfT) (eqFn (.field 1) negInfT))
      (andFn (eqFn (.field 0) negInfT) (eqFn (.field 1) posInfT)))
  | .fsub => some (orFn (andFn (eqFn (.field 0) posInfT) (eqFn (.field 1) posInfT))
      (andFn (eqFn (.field 0) negInfT) (eqFn (.field 1) negInfT)))
  | .fmul => some (orFn (andFn (eqFn (.field 0) (.lit (.float 0))) (isInfT (.field 1)))
      (andFn (isInfT (.field 0)) (eqFn (.field 1) (.lit (.float 0)))))
  | .fdiv => some (andFn (isInfT (.field 0)) (isInfT (.field 1)))
  -- IEEE division (D39): `0 / 0` too, either zero's sign.
  | .fdivIeee => some (orFn (andFn (isInfT (.field 0)) (isInfT (.field 1)))
      (andFn (eqFn (.field 0) (.lit (.float 0))) (eqFn (.field 1) (.lit (.float 0)))))
  | .fmod => some (andFn (isInfT (.field 0)) (notFn (eqFn (.field 1) nanT)))
  | _ => none

/-- `CASE WHEN x IS NOT NULL AND y = 0 THEN error ELSE e END`: a zero divisor
raises, `NULL / 0` stays `NULL`. `x` is of one of the kinds `ks`, `0` of kind
`k` (#923). -/
def zeroGuard (ks : List NumKind) (k : NumKind) (e : Tm) : Tm :=
  let isNum := match ks with
    | [] => Tm.lit (.bool false)
    | k :: ks => ks.foldl (fun g k => orFn g (isNumFn k (.field 0))) (isNumFn k (.field 0))
  .ite (andFn isNum (eqFn (.field 1) (.lit (k.val 0))))
    (.raise "division by zero" (.field 1)) e

/-- The condition under which an elementary function is outside its domain
(`FMath.inDomain`): `x < lo OR (hi < x AND x <> NaN)`, the bounds written as
`FMath.lo?` and `FMath.hi?`; none for a function defined everywhere. A schema
raises `domain error` on it, where an engine gives NaN or `-∞`. -/
def fmathGuard (f : FMath) : Option Tm :=
  let x := Tm.field 0
  -- The bounds as `FMath.lo?` and `FMath.hi?` write them, by name, so that
  -- the proofs treat `±1` and `±∞` as the variables they generalize to.
  let c (n : Lean.Name) := Lean.mkConst n
  let op (h i inst : Lean.Name) (a : Lean.Expr) : Lean.Expr :=
    mkApp6 (Lean.mkConst h [Level.zero, Level.zero, Level.zero]) (c ``Int) (c ``Int) (c ``Int)
      (mkApp2 (Lean.mkConst i [Level.zero]) (c ``Int) (c inst)) a (toExpr (1 : Int))
  let term (v : Int) : Lean.Expr :=
    if v == FloatCode.negOne then c ``FloatCode.negOne
    else if v == FloatCode.one then c ``FloatCode.one
    else if v == FloatCode.negInf + 1 then op ``HAdd.hAdd ``instHAdd ``Int.instAdd (c ``FloatCode.negInf)
    else if v == FloatCode.posInf - 1 then op ``HSub.hSub ``instHSub ``Int.instSub (c ``FloatCode.posInf)
    else toExpr v
  let bound (v : Int) (l : String) : Tm := namedFloat v (term v) l
  let lo := f.lo?.map fun v => ltFn x (bound v s!"lo({f.name})")
  let hi := f.hi?.map fun v =>
    andFn (ltFn (bound v s!"hi({f.name})") x) (notFn (eqFn x nanT))
  let g := match lo, hi with
    | some a, some b => some (orFn a b)
    | some a, none => some a
    | none, some b => some b
    | none, none => none
  g

end Substrait.LoweringSearch
