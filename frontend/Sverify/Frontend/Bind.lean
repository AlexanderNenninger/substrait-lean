import Sverify.Frontend.Guard

/-!
# Guarded columns: D50's lift in linear size (D50-d, #1719)

`Expr.andLift` writes a chain as a `CASE` nest, and a chain inside an operand
of another chain is copied with every guard that reads it: nested `k` deep,
an operand is written `2ᵏ` or `3ᵏ` times. The parser caps the lift at a
depth (`LIFT_LEVELS`) for that reason.

Relations bind. `Rel.project` appends a column, and `ifThen` evaluates only
the branch it takes, so a chain is bound in projections below the operator
that reads it, one projection per operand that may raise (ruling 102, B1 to
B7):

```
a₀ := conj P₀
aᵢ := aᵢ₋₁ AND (CASE WHEN aᵢ₋₁ IS NOT FALSE AND Out THEN uᵢ END) AND conj Pᵢ
```

with `uᵢ` the operands that may raise, `Pᵢ` the runs of plain operands
between them (`Expr.plain`) and `Out` the guard of the lazy contexts around
the chain. `OR` is the dual. Each operand is written once, so the bound plan
is linear in the size of the condition at any depth.

`LExpr` is a condition as the parser reads it: an expression whose chains
are kept apart (`body` reads chain `i` at column `w + i`). `LExpr.fill` writes
every chain with `andLift`/`orLift`, the plan D50 defines; `Rel.bindFilter`
binds them. A chain whose column sits in a `CASE` branch or a lambda body of
its expression stays filled (CASE branches bind in step D50-d3d).
-/

namespace Substrait

variable [Boxes.Ambient]

mutual
/-- A condition with its chains kept apart: `body` reads the row's columns
`0 … w-1` and, at `w + i`, the value of `chains[i]`. -/
inductive LExpr where
  | mk (body : Expr) (chains : List LChain)
/-- `AND` (`isAnd`) or `OR` of operands, each evaluated where the ones before
it do not decide the result (D50). -/
inductive LChain where
  | mk (isAnd : Bool) (ops : List LExpr)
end

mutual
/-- The expression D50 defines: every chain written with `andLift`/`orLift`. -/
def LExpr.fill (w : Nat) : LExpr → Expr
  | .mk body cs => body.subst ((List.range w).map .field ++ LChain.fillAll w cs)
/-- `fill` of each chain. -/
def LChain.fillAll (w : Nat) : List LChain → List Expr
  | [] => []
  | c :: cs => LChain.fill w c :: LChain.fillAll w cs
/-- A chain written with `andLift` or `orLift`. -/
def LChain.fill (w : Nat) : LChain → Expr
  | .mk true ops => Expr.andLift (LExpr.fillAll w ops)
  | .mk false ops => Expr.orLift (LExpr.fillAll w ops)
/-- `fill` of each operand. -/
def LExpr.fillAll (w : Nat) : List LExpr → List Expr
  | [] => []
  | x :: xs => LExpr.fill w x :: LExpr.fillAll w xs
end

/-- Does `e` read column `i`? -/
def Expr.reads (i : Nat) : Expr → Bool
  | .lit _ => false
  | .field j => i == j
  | .un _ a => a.reads i
  | .bin _ a b => a.reads i || b.reads i
  | .ifThen c t e => c.reads i || t.reads i || e.reads i
  | .hof _ l b => l.reads i || b.reads (i + 1)

/-- Does column `i` occur in `e` only where `e` evaluates it whenever `e` is
evaluated: outside the branches of a `CASE` and outside a lambda's body? -/
def Expr.eagerOnly (i : Nat) : Expr → Bool
  | .lit _ | .field _ => true
  | .un _ a => a.eagerOnly i
  | .bin _ a b => a.eagerOnly i && b.eagerOnly i
  | .ifThen c t e => c.eagerOnly i && !(t.reads i) && !(e.reads i)
  | .hof _ l b => l.eagerOnly i && !(b.reads (i + 1))

/-- An operand with nothing to bind and no raise: a plain expression and no
chain. -/
def LExpr.plain : LExpr → Bool
  | .mk body [] => body.plain
  | _ => false

/-- The binder's state: the relation so far and its width. The input's
columns stay at `0 … w-1`; each level appends one column. -/
structure BindSt where
  rel : Rel
  width : Nat

/-- One level: `rel` with the column `e` appended; its index. -/
def BindSt.push (s : BindSt) (e : Expr) : BindSt × Nat :=
  (⟨.project s.rel [e], s.width + 1⟩, s.width)

/-- `g AND h`, `h` alone where `g` is absent (TRUE). -/
def guardAnd : Option Expr → Expr → Expr
  | none, h => h
  | some g, h => .bin .and g h

/-- `CASE WHEN g THEN u END`, `u` where `g` is absent. -/
def guardCase : Option Expr → Expr → Expr
  | none, u => u
  | some g, u => .ifThen g u (.lit .null)

mutual
/-- Bind the chains of `x` that it reads eagerly, under the reach `g` (`none`:
every row): the state with their levels, and `x` over its columns. A chain
`x` reads only in a `CASE` branch or a lambda stays filled. -/
def LExpr.bind (w : Nat) (g : Option Expr) (s : BindSt) : LExpr → BindSt × Expr
  | .mk body cs =>
    let (s, cols) := LChain.bindAll w g s body 0 cs
    (s, body.subst ((List.range w).map .field ++ cols))
/-- `bind` of each chain `body` reads only eagerly, `fill` of the others; the
first is chain `i`, at column `w + i`. -/
def LChain.bindAll (w : Nat) (g : Option Expr) (s : BindSt) (body : Expr) (i : Nat) :
    List LChain → BindSt × List Expr
  | [] => (s, [])
  | c :: cs =>
    let (s, e) := if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)
    let (s, es) := LChain.bindAll w g s body (i + 1) cs
    (s, e :: es)
/-- Bind a chain under the reach `g`: one level per operand that may raise,
the running column holding the chain's value so far (B1, B2). -/
def LChain.bind (w : Nat) (g : Option Expr) (s : BindSt) : LChain → BindSt × Expr
  | .mk isAnd ops => LChain.bindOps w isAnd g s none ops
/-- The levels of the operands `ops`, `acc` the chain's value so far (`none`:
no operand yet). Plain operands join the running expression; an operand that
may raise gets a level, guarded by `acc IS NOT FALSE` (`IS NOT TRUE` for
`OR`) and `g`. -/
def LChain.bindOps (w : Nat) (isAnd : Bool) (g : Option Expr) (s : BindSt) :
    Option Expr → List LExpr → BindSt × Expr
  | acc, [] => (s, acc.getD (.lit (.bool isAnd)))
  | acc, x :: xs =>
    let op : Expr → Expr → Expr := if isAnd then .bin .and else .bin .or
    if x.plain then
      let e := LExpr.fill w x
      LChain.bindOps w isAnd g s (some (match acc with | none => e | some a => op a e)) xs
    else
      let reach : Option Expr := match acc with
        | none => g
        | some a => some (guardAnd g (if isAnd then a.notFalse else a.notTrue))
      let (s, u) := LExpr.bind w reach s x
      let v := guardCase reach u
      let (s, col) := s.push (match acc with | none => v | some a => op a v)
      LChain.bindOps w isAnd g s (some (.field col)) xs
end

/-- A filter on `x`, its chains bound below it and their columns dropped
above it. -/
def Rel.bindFilter (r : Rel) (w : Nat) (x : LExpr) : Rel :=
  let (s, c) := x.bind w none ⟨r, w⟩
  .emit (.filter s.rel c) (List.range w)

end Substrait
