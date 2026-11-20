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


/-! ## T1: the bound plan's rows (ruling 102, T1a to T1c)

Under the reference, a filter on the bound condition keeps the rows the
filter on D50's lift keeps: `Rel.bindFilter_eval`. The invariant: after each
level, the plan's rows are the input's rows, each extended by the levels'
columns, and wherever its reach holds, a chain's running column holds the
eager conjunction (disjunction) of the operands so far, which is the lift's
value (`Expr.andLift_eval`, `Expr.orLift_eval`). -/

theorem Expr.refsLt_mono : ∀ (e : Expr) {n m : Nat}, n ≤ m → e.refsLt n → e.refsLt m
  | .lit _, _, _, _, _ => trivial
  | .field _, _, _, h, he => Nat.lt_of_lt_of_le he h
  | .un _ a, _, _, h, he => Expr.refsLt_mono a h he
  | .bin _ a b, _, _, h, he => ⟨Expr.refsLt_mono a h he.1, Expr.refsLt_mono b h he.2⟩
  | .ifThen c t e, _, _, h, he =>
    ⟨Expr.refsLt_mono c h he.1, Expr.refsLt_mono t h he.2.1, Expr.refsLt_mono e h he.2.2⟩
  | .hof _ l b, _, _, h, he => ⟨Expr.refsLt_mono l h he.1, Expr.refsLt_mono b (Nat.succ_le_succ h) he.2⟩

/-- Substituting expressions that read below `n` for the columns below `k`
that `e` reads gives an expression that reads below `n`. -/
theorem Expr.refsLt_subst {n : Nat} : ∀ {k : Nat} {σ : List Expr} {e : Expr},
    e.refsLt k → (∀ i < k, (σ.getD i (.lit .null)).refsLt n) → (e.subst σ).refsLt n
  | _, _, .lit _, _, _ => trivial
  | _, _, .field i, he, hσ => hσ i he
  | _, _, .un _ a, he, hσ => Expr.refsLt_subst (e := a) he hσ
  | _, _, .bin _ a b, he, hσ => ⟨Expr.refsLt_subst he.1 hσ, Expr.refsLt_subst he.2 hσ⟩
  | _, _, .ifThen c t e, he, hσ =>
    ⟨Expr.refsLt_subst he.1 hσ, Expr.refsLt_subst he.2.1 hσ, Expr.refsLt_subst he.2.2 hσ⟩
  | k, σ, .hof _ l b, he, hσ => by
    refine ⟨Expr.refsLt_subst he.1 hσ, Expr.refsLt_subst (k := k + 1) he.2 ?_⟩
    intro i hi
    cases i with
    | zero => show (Expr.field 0).refsLt (n + 1); exact Nat.succ_pos n
    | succ i =>
      show ((σ.map (fun x : Expr => x.shift 0)).getD i (Expr.lit .null)).refsLt (n + 1)
      have := hσ i (by omega)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
      cases h : σ[i]? with
      | none => trivial
      | some x => simp only [h, Option.map_some, Option.getD_some] at this ⊢; exact Expr.refsLt_shift 0 this

mutual
/-- Every column `x` and its chains read is in scope: the row's `w` columns,
and in a body the chains it holds. -/
def LExpr.Scoped (w : Nat) : LExpr → Prop
  | .mk body cs => body.refsLt (w + cs.length) ∧ LChain.ScopedAll w cs
/-- `Scoped` of each chain. -/
def LChain.ScopedAll (w : Nat) : List LChain → Prop
  | [] => True
  | c :: cs => LChain.Scoped w c ∧ LChain.ScopedAll w cs
/-- `Scoped` of a chain: of each operand. -/
def LChain.Scoped (w : Nat) : LChain → Prop
  | .mk _ ops => LExpr.ScopedAll w ops
/-- `Scoped` of each operand. -/
def LExpr.ScopedAll (w : Nat) : List LExpr → Prop
  | [] => True
  | x :: xs => LExpr.Scoped w x ∧ LExpr.ScopedAll w xs
end

variable [Boxes.Ambient] in
mutual
/-- On `row`, every chain's operands, at every depth, are TRUE, FALSE or NULL
(the hypothesis of `Expr.andLift_eval`). -/
def LExpr.Bools (w : Nat) (row : Row) : LExpr → Prop
  | .mk _ cs => LChain.BoolsAll w row cs
/-- `Bools` of each chain. -/
def LChain.BoolsAll (w : Nat) (row : Row) : List LChain → Prop
  | [] => True
  | c :: cs => LChain.Bools w row c ∧ LChain.BoolsAll w row cs
/-- `Bools` of a chain: each operand is TRUE, FALSE or NULL, and so are its chains'. -/
def LChain.Bools (w : Nat) (row : Row) : LChain → Prop
  | .mk _ ops => LExpr.BoolsAll w row ops
/-- `Bools` of each operand, and its value TRUE, FALSE or NULL. -/
def LExpr.BoolsAll (w : Nat) (row : Row) : List LExpr → Prop
  | [] => True
  | x :: xs => (Expr.BoolVal row (LExpr.fill w x) ∧ LExpr.Bools w row x) ∧ LExpr.BoolsAll w row xs
end

theorem LChain.fillAll_length (w : Nat) : ∀ cs : List LChain, (LChain.fillAll w cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [LChain.fillAll, LChain.fillAll_length w cs]

mutual
theorem LExpr.fill_refsLt (w : Nat) : ∀ x : LExpr, x.Scoped w → (x.fill w).refsLt w
  | .mk body cs, ⟨hb, hcs⟩ => by
    simp only [LExpr.fill]
    apply Expr.refsLt_subst hb
    intro i hi
    have hlen : (LChain.fillAll w cs).length = cs.length := LChain.fillAll_length w cs
    by_cases hiw : i < w
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hiw)]
      simp [hiw]; exact hiw
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      have hj : i - w < (LChain.fillAll w cs).length := by omega
      rw [List.getElem?_eq_getElem hj, Option.getD_some]
      exact LChain.fillAll_refsLt w cs hcs _ (List.getElem_mem hj)
theorem LChain.fillAll_refsLt (w : Nat) : ∀ cs : List LChain, LChain.ScopedAll w cs →
    ∀ e ∈ LChain.fillAll w cs, e.refsLt w
  | [], _ => by simp [LChain.fillAll]
  | c :: cs, ⟨hc, hcs⟩ => by
    intro e he
    simp only [LChain.fillAll, List.mem_cons] at he
    rcases he with rfl | he
    · exact LChain.fill_refsLt w c hc
    · exact LChain.fillAll_refsLt w cs hcs e he
theorem LChain.fill_refsLt (w : Nat) : ∀ c : LChain, c.Scoped w → (c.fill w).refsLt w
  | .mk true ops, h => Expr.andLift_refsLt (LExpr.fillAll_refsLt w ops h)
  | .mk false ops, h => Expr.orLift_refsLt (LExpr.fillAll_refsLt w ops h)
theorem LExpr.fillAll_refsLt (w : Nat) : ∀ xs : List LExpr, LExpr.ScopedAll w xs →
    ∀ e ∈ LExpr.fillAll w xs, e.refsLt w
  | [], _ => by simp [LExpr.fillAll]
  | x :: xs, ⟨hx, hxs⟩ => by
    intro e he
    simp only [LExpr.fillAll, List.mem_cons] at he
    rcases he with rfl | he
    · exact LExpr.fill_refsLt w x hx
    · exact LExpr.fillAll_refsLt w xs hxs e he
end



section Eval
variable [Boxes.Ambient]

/-- The binder's state over the input `r`: its rows are `r`'s, `w` columns
wide, each extended by `F`. -/
def BindSt.Ext (cat : Catalog) (r : Rel) (w : Nat) (s : BindSt) (F : Row → Row) : Prop :=
  s.rel.eval cat = (r.eval cat).map (fun row => row ++ F row) ∧
    ∀ row ∈ r.eval cat, row.length = w ∧ w + (F row).length = s.width

/-- The reach `g` holds on `row` (`none`: everywhere). -/
def Reach (g : Option Expr) (row : Row) : Prop := ∀ c ∈ g, (c.eval row).isTrue = true

/-- An expression reading below the width of a row's extension `F` has the
same value on a longer extension. -/
theorem eval_ext {e : Expr} {row F G : Row} {n : Nat} (he : e.refsLt n)
    (hlen : row.length + F.length = n) : e.eval (row ++ (F ++ G)) = e.eval (row ++ F) := by
  rw [← List.append_assoc]; exact Expr.eval_append G he (by simp [hlen])

theorem eval_prefix {e : Expr} {row F F' : Row} {n : Nat} (he : e.refsLt n)
    (hlen : row.length + F.length = n) (hp : F <+: F') : e.eval (row ++ F') = e.eval (row ++ F) := by
  obtain ⟨G, rfl⟩ := hp; exact eval_ext he hlen

/-- Columns `0 … w-1` read the row. -/
theorem map_range_field (row X : Row) (w : Nat) (h : row.length = w) :
    ((List.range w).map Expr.field).map (·.eval (row ++ X)) = row := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]

theorem BindSt.push_ext {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (hs : s.Ext cat r w F) (e : Expr) :
    (s.push e).1.Ext cat r w (fun row => F row ++ [e.eval (row ++ F row)]) := by
  refine ⟨?_, fun row hr => ?_⟩
  · simp only [BindSt.push, Rel.eval, hs.1, List.map_map]
    congr 1; funext row; simp
  · obtain ⟨h1, h2⟩ := hs.2 row hr
    refine ⟨h1, ?_⟩; simp [BindSt.push]; omega

end Eval

end Substrait
