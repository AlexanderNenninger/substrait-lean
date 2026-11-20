import Sverify.Frontend.Guard

/-!
# Guarded columns: D50's lift in linear size (D50-d, #1719)

`Expr.andLift` writes a chain as a `CASE` nest, and a chain inside an operand
of another chain is copied with every guard that reads it: nested `k` deep,
an operand is written `2ᵏ` or `3ᵏ` times. The parser lifts only the top
`Parse.liftLevels` levels with the chain for that reason.

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
every chain with `andLift`/`orLift`, the plan D50 defines; `Rel.guardedFilter`
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
def Expr.readsCol (i : Nat) : Expr → Bool
  | .lit _ => false
  | .field j => i == j
  | .un _ a => a.readsCol i
  | .bin _ a b => a.readsCol i || b.readsCol i
  | .ifThen c t e => c.readsCol i || t.readsCol i || e.readsCol i
  | .hof _ l b => l.readsCol i || b.readsCol (i + 1)

/-- Does column `i` occur in `e` only where `e` evaluates it whenever `e` is
evaluated: outside the branches of a `CASE` and outside a lambda's body? -/
def Expr.eagerOnly (i : Nat) : Expr → Bool
  | .lit _ | .field _ => true
  | .un _ a => a.eagerOnly i
  | .bin _ a b => a.eagerOnly i && b.eagerOnly i
  | .ifThen c t e => c.eagerOnly i && !(t.readsCol i) && !(e.readsCol i)
  | .hof _ l b => l.eagerOnly i && !(b.readsCol (i + 1))

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

/-- Is `e` a column reference? -/
def Expr.isField : Expr → Bool
  | .field _ => true
  | _ => false

/-- The reach `g` as a column: a compound reach is appended once, so that a
chain's levels read one column and a nest's plan grows linearly with its depth
(#1719); a column, or no reach, stays as it is. -/
def BindSt.anchor (s : BindSt) : Option Expr → BindSt × Option Expr
  | some c => if c.isField then (s, some c) else ((s.push c).1, some (.field (s.push c).2))
  | none => (s, none)

/-- `g AND h`, `h` alone where `g` is absent (TRUE). -/
def guardAnd : Option Expr → Expr → Expr
  | none, h => h
  | some g, h => .bin .and g h

/-- `CASE WHEN g THEN u END`, `u` where `g` is absent. -/
def guardCase : Option Expr → Expr → Expr
  | none, u => u
  | some g, u => .ifThen g u (.lit .null)

/-- The running value joined with the next operand's: `acc AND e` (`OR`), or
`e` for the first operand. -/
def joinOp (isAnd : Bool) : Option Expr → Expr → Expr
  | none, e => e
  | some a, e => if isAnd then .bin .and a e else .bin .or a e

/-- Where the next operand is evaluated: where `g` holds and the running value
does not decide the chain (`IS NOT FALSE` for `AND`, `IS NOT TRUE` for `OR`). -/
def reachOf (isAnd : Bool) (g : Option Expr) : Option Expr → Option Expr
  | none => g
  | some a => some (guardAnd g (if isAnd then a.notFalse else a.notTrue))

mutual
/-- Bind the chains of `x` that it reads eagerly, under the reach `g` (`none`:
every row): the state with their levels, and `x` over its columns. A chain
`x` reads only in a `CASE` branch or a lambda stays filled. -/
def LExpr.bind (w : Nat) (g : Option Expr) (s : BindSt) : LExpr → BindSt × Expr
  | .mk body cs =>
    let p := LChain.bindAll w g s body 0 cs
    (p.1, body.subst ((List.range w).map .field ++ p.2))
/-- `bind` of each chain `body` reads, and reads only eagerly; `fill` of the others; the
first is chain `i`, at column `w + i`. -/
def LChain.bindAll (w : Nat) (g : Option Expr) (s : BindSt) (body : Expr) (i : Nat) :
    List LChain → BindSt × List Expr
  | [] => (s, [])
  | c :: cs =>
    let p := if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)
    let q := LChain.bindAll w g p.1 body (i + 1) cs
    (q.1, p.2 :: q.2)
/-- Bind a chain under the reach `g`: one level per operand that may raise,
the running column holding the chain's value so far (B1, B2). The reach is
first a column of its own (`BindSt.anchor`), so each level's guard reads two
columns, whatever the nest's depth. -/
def LChain.bind (w : Nat) (g : Option Expr) (s : BindSt) : LChain → BindSt × Expr
  | .mk isAnd ops => LChain.bindOps w isAnd (s.anchor g).2 (s.anchor g).1 none ops
/-- The levels of the operands `ops`, `acc` the chain's value so far (`none`:
no operand yet). Plain operands join the running expression; an operand that
may raise gets a level, guarded by `acc IS NOT FALSE` (`IS NOT TRUE` for
`OR`) and `g`. -/
def LChain.bindOps (w : Nat) (isAnd : Bool) (g : Option Expr) (s : BindSt) :
    Option Expr → List LExpr → BindSt × Expr
  | acc, [] => (s, acc.getD (.lit (.bool isAnd)))
  | acc, x :: xs =>
    if x.plain then
      LChain.bindOps w isAnd g s (some (joinOp isAnd acc (LExpr.fill w x))) xs
    else
      let reach := reachOf isAnd g acc
      let p := LExpr.bind w reach s x
      let q := p.1.push (joinOp isAnd acc (guardCase reach p.2))
      LChain.bindOps w isAnd g q.1 (some (.field q.2)) xs
end

/-- A filter on `x`, its chains bound below it and their columns dropped
above it. -/
def Rel.guardedFilter (r : Rel) (w : Nat) (x : LExpr) : Rel :=
  let (s, c) := x.bind w none ⟨r, w⟩
  .emit (.filter s.rel c) (List.range w)

/-- Bind the chains of each expression in turn, every row reached. -/
def LExpr.bindList (w : Nat) (s : BindSt) : List LExpr → BindSt × List Expr
  | [] => (s, [])
  | x :: xs =>
    let p := x.bind w none s
    let q := LExpr.bindList w p.1 xs
    (q.1, p.2 :: q.2)

/-- A projection of `xs`, their chains bound below it and their levels dropped
above it. -/
def Rel.guardedProject (r : Rel) (w : Nat) (xs : List LExpr) : Rel :=
  let p := LExpr.bindList w ⟨r, w⟩ xs
  .emit (.project p.1.rel p.2) (List.range w ++ (List.range xs.length).map (p.1.width + ·))


/-! ## T1: the bound plan's rows (ruling 102, T1a to T1c)

Under the reference, a filter on the bound condition keeps the rows the
filter on D50's lift keeps: `Rel.guardedFilter_eval`. The invariant: after each
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
theorem Expr.refsLt_subst_below {n : Nat} : ∀ {k : Nat} {σ : List Expr} {e : Expr},
    e.refsLt k → (∀ i < k, (σ.getD i (.lit .null)).refsLt n) → (e.subst σ).refsLt n
  | _, _, .lit _, _, _ => trivial
  | _, _, .field i, he, hσ => hσ i he
  | _, _, .un _ a, he, hσ => Expr.refsLt_subst_below (e := a) he hσ
  | _, _, .bin _ a b, he, hσ => ⟨Expr.refsLt_subst_below he.1 hσ, Expr.refsLt_subst_below he.2 hσ⟩
  | _, _, .ifThen c t e, he, hσ =>
    ⟨Expr.refsLt_subst_below he.1 hσ, Expr.refsLt_subst_below he.2.1 hσ, Expr.refsLt_subst_below he.2.2 hσ⟩
  | k, σ, .hof _ l b, he, hσ => by
    refine ⟨Expr.refsLt_subst_below he.1 hσ, Expr.refsLt_subst_below (k := k + 1) he.2 ?_⟩
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
/-- On `row`, under `I`, every chain's operands, at every depth, are TRUE, FALSE or NULL
(the hypothesis of `Expr.andLift_evalI`). -/
def LExpr.Bools (I : Impl) (w : Nat) (row : Row) : LExpr → Prop
  | .mk _ cs => LChain.BoolsAll I w row cs
/-- `Bools` of each chain. -/
def LChain.BoolsAll (I : Impl) (w : Nat) (row : Row) : List LChain → Prop
  | [] => True
  | c :: cs => LChain.Bools I w row c ∧ LChain.BoolsAll I w row cs
/-- `Bools` of a chain: each operand is TRUE, FALSE or NULL, and so are its chains'. -/
def LChain.Bools (I : Impl) (w : Nat) (row : Row) : LChain → Prop
  | .mk _ ops => LExpr.BoolsAll I w row ops
/-- `Bools` of each operand, and its value TRUE, FALSE or NULL. -/
def LExpr.BoolsAll (I : Impl) (w : Nat) (row : Row) : List LExpr → Prop
  | [] => True
  | x :: xs => (Expr.BoolValI I row (LExpr.fill w x) ∧ LExpr.Bools I w row x) ∧ LExpr.BoolsAll I w row xs
end

theorem LChain.fillAll_length (w : Nat) : ∀ cs : List LChain, (LChain.fillAll w cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [LChain.fillAll, LChain.fillAll_length w cs]

mutual
theorem LExpr.fill_refsLt (w : Nat) : ∀ x : LExpr, x.Scoped w → (x.fill w).refsLt w
  | .mk body cs, ⟨hb, hcs⟩ => by
    simp only [LExpr.fill]
    apply Expr.refsLt_subst_below hb
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
variable [Boxes.Ambient] {I : Impl}

/-- The binder's state over the input `r`: its rows are `r`'s, `w` columns
wide, each extended by `F`. -/
def BindSt.Ext (I : Impl) (cat : Catalog) (r : Rel) (w : Nat) (s : BindSt) (F : Row → Row) : Prop :=
  s.rel.eval cat I = (r.eval cat I).map (fun row => row ++ F row) ∧
    (∀ row ∈ r.eval cat I, row.length = w ∧ w + (F row).length = s.width) ∧ w ≤ s.width

/-- The reach `g` holds on `row` (`none`: everywhere). -/
def Reach (I : Impl) (g : Option Expr) (row : Row) : Prop := ∀ c ∈ g, (c.eval row I).isTrue = true

/-- An expression reading below the width of a row's extension `F` has the
same value on a longer extension. -/
theorem eval_ext {e : Expr} {row F G : Row} {n : Nat} (he : e.refsLt n)
    (hlen : row.length + F.length = n) : e.eval (row ++ (F ++ G)) I = e.eval (row ++ F) I := by
  rw [← List.append_assoc]; exact Expr.eval_append G he (by simp [hlen])

theorem eval_prefix {e : Expr} {row F F' : Row} {n : Nat} (he : e.refsLt n)
    (hlen : row.length + F.length = n) (hp : F <+: F') : e.eval (row ++ F') I = e.eval (row ++ F) I := by
  obtain ⟨G, rfl⟩ := hp; exact eval_ext he hlen

/-- Columns `0 … w-1` read the row. -/
theorem map_range_field (row X : Row) (w : Nat) (h : row.length = w) :
    ((List.range w).map Expr.field).map (·.eval (row ++ X) I) = row := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]

theorem BindSt.push_ext {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (hs : s.Ext I cat r w F) (e : Expr) :
    (s.push e).1.Ext I cat r w (fun row => F row ++ [e.eval (row ++ F row) I]) := by
  refine ⟨?_, fun row hr => ?_, ?_⟩
  · simp only [BindSt.push, Rel.eval, hs.1, List.map_map]
    congr 1; funext row; simp
  · obtain ⟨h1, h2⟩ := hs.2.1 row hr
    refine ⟨h1, ?_⟩; simp [BindSt.push]; omega
  · have := hs.2.2; simp [BindSt.push]; omega

/-- `AND`'s (`OR`'s) three-valued function. -/
def comb (isAnd : Bool) : Value → Value → Value := if isAnd then and3 else or3

/-- A chain's value so far: its operands' values folded onto `acc`'s. -/
def foldOpt (isAnd : Bool) : Option Value → List Value → Value
  | none, [] => .bool isAnd
  | none, v :: vs => vs.foldl (comb isAnd) v
  | some a, vs => vs.foldl (comb isAnd) a

omit [Boxes.Ambient] in
theorem foldOpt_cons (isAnd : Bool) (acc : Option Value) (v : Value) (vs : List Value) :
    foldOpt isAnd acc (v :: vs) =
      foldOpt isAnd (some (match acc with | none => v | some a => comb isAnd a v)) vs := by
  cases acc <;> rfl

omit [Boxes.Ambient] in
theorem LExpr.fillAll_length (w : Nat) : ∀ xs : List LExpr, (LExpr.fillAll w xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [LExpr.fillAll, LExpr.fillAll_length w xs]

omit [Boxes.Ambient] in
theorem LExpr.mem_fillAll {w : Nat} {e : Expr} : ∀ {xs : List LExpr}, e ∈ LExpr.fillAll w xs →
    ∃ x ∈ xs, e = x.fill w
  | [], h => by simp [LExpr.fillAll] at h
  | x :: xs, h => by
    simp only [LExpr.fillAll, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨x, by simp, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := LExpr.mem_fillAll h
      exact ⟨y, by simp [hy], rfl⟩

omit [Boxes.Ambient] in
theorem LExpr.fill_mem_fillAll {w : Nat} {x : LExpr} : ∀ {xs : List LExpr}, x ∈ xs →
    x.fill w ∈ LExpr.fillAll w xs
  | [], h => by simp at h
  | y :: xs, h => by
    simp only [List.mem_cons] at h
    simp only [LExpr.fillAll, List.mem_cons]
    rcases h with rfl | h
    · exact .inl rfl
    · exact .inr (LExpr.fill_mem_fillAll h)

theorem LExpr.boolsAll_boolVal (w : Nat) (row : Row) :
    ∀ xs : List LExpr, LExpr.BoolsAll I w row xs → ∀ q ∈ LExpr.fillAll w xs, Expr.BoolValI I row q
  | [], _ => by simp [LExpr.fillAll]
  | x :: xs, ⟨⟨hx, _⟩, hxs⟩ => by
    intro q hq
    simp only [LExpr.fillAll, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hx
    · exact LExpr.boolsAll_boolVal w row xs hxs q hq

/-- A chain's lift has the eager value of its operands (`Expr.andLift_evalI`). -/
theorem LChain.fill_eval (hI : I.Logic) (w : Nat) (isAnd : Bool) (ops : List LExpr) (row : Row)
    (hb : LExpr.BoolsAll I w row ops) :
    (LChain.fill w (.mk isAnd ops)).eval row I =
      foldOpt isAnd none ((LExpr.fillAll w ops).map (·.eval row I)) := by
  have hbv := LExpr.boolsAll_boolVal w row ops hb
  have hfold : ∀ (f : BinFn) (h3 : Value → Value → Value), (∀ v w, I.bin f v w = h3 v w) →
      ∀ (acc : Expr) (qs : List Expr), (qs.foldl (.bin f) acc).eval row I =
        (qs.map (·.eval row I)).foldl h3 (acc.eval row I) := by
    intro f h3 hf acc qs
    induction qs generalizing acc with
    | nil => rfl
    | cons q qs ih => simp only [List.foldl_cons, ih, Expr.eval, hf, List.map_cons]
  cases isAnd with
  | true =>
    simp only [LChain.fill]
    rw [Expr.andLift_evalI hI row _ hbv]
    cases LExpr.fillAll w ops with
    | nil => rfl
    | cons p ps => simp only [Expr.conj, hfold .and and3 hI.and, List.map_cons, foldOpt, comb]; rfl
  | false =>
    simp only [LChain.fill]
    rw [Expr.orLift_evalI hI row _ hbv]
    cases LExpr.fillAll w ops with
    | nil => rfl
    | cons p ps => simp only [Expr.disj, hfold .or or3 hI.or, List.map_cons, foldOpt, comb]; rfl

/-- The binder went from `s` (rows extended by `F`) to `s'` (by `F'`): `F'`
extends `F` and the width grew. -/
def Grows (I : Impl) (cat : Catalog) (r : Rel) (w : Nat) (s s' : BindSt) (F F' : Row → Row) : Prop :=
  s'.Ext I cat r w F' ∧ (∀ row, F row <+: F' row) ∧ s.width ≤ s'.width

theorem Grows.refl {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (hs : s.Ext I cat r w F) : Grows I cat r w s s F F :=
  ⟨hs, fun _ => List.prefix_refl _, Nat.le_refl _⟩

theorem Grows.trans {cat : Catalog} {r : Rel} {w : Nat} {s₁ s₂ s₃ : BindSt} {F₁ F₂ F₃ : Row → Row}
    (h₁ : Grows I cat r w s₁ s₂ F₁ F₂) (h₂ : Grows I cat r w s₂ s₃ F₂ F₃) : Grows I cat r w s₁ s₃ F₁ F₃ :=
  ⟨h₂.1, fun row => (h₁.2.1 row).trans (h₂.2.1 row), Nat.le_trans h₁.2.2 h₂.2.2⟩

theorem BindSt.push_grows {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (hs : s.Ext I cat r w F) (e : Expr) :
    Grows I cat r w s (s.push e).1 F (fun row => F row ++ [e.eval (row ++ F row) I]) :=
  ⟨BindSt.push_ext hs e, fun _ => List.prefix_append _ _, by simp [BindSt.push]⟩

omit [Boxes.Ambient] in
theorem and3_isTrue (a b : Value) : (and3 a b).isTrue = true ↔ a.isTrue = true ∧ b.isTrue = true := by
  constructor
  · intro h
    have := and3_eq_neut (a := a) (b := b) (by
      revert h; unfold Value.isTrue; split <;> simp_all)
    simp [this.1, this.2, Value.isTrue]
  · rintro ⟨ha, hb⟩
    have ha' : a = .bool true := by revert ha; unfold Value.isTrue; split <;> simp_all
    have hb' : b = .bool true := by revert hb; unfold Value.isTrue; split <;> simp_all
    simp [ha', hb', and3, Value.isTrue]

/-- A guard's value: `g AND h` is TRUE exactly where both are. -/
theorem guardAnd_isTrue (hI : I.Logic) (g : Option Expr) (h : Expr) (row : Row) :
    ((guardAnd g h).eval row I).isTrue = true ↔ Reach I g row ∧ (h.eval row I).isTrue = true := by
  cases g with
  | none => simp [guardAnd, Reach]
  | some g =>
    simp only [guardAnd, Expr.eval, hI.and, Reach, Option.mem_def, Option.some.injEq,
      forall_eq']
    exact and3_isTrue _ _

theorem guardCase_eval_reach {g : Option Expr} {u : Expr} {row : Row} (h : Reach I g row) :
    (guardCase g u).eval row I = u.eval row I := by
  cases g with
  | none => rfl
  | some g => simp only [guardCase, Expr.eval, h g rfl, ite_true]

theorem guardCase_eval_not {g : Option Expr} {u : Expr} {row : Row} (h : ¬ Reach I g row) :
    (guardCase g u).eval row I = .null := by
  cases g with
  | none => exact absurd (fun _ h => nomatch h) h
  | some g =>
    have : (g.eval row I).isTrue = false := by
      simp only [Reach, Option.mem_def, Option.some.injEq, forall_eq'] at h
      simpa using h
    simp only [guardCase, Expr.eval, this]; rfl

theorem notFalse_isTrue (hI : I.Logic) {row : Row} {a : Expr} (hb : Expr.BoolValI I row a) :
    ((a.notFalse).eval row I).isTrue = true ↔ a.eval row I ≠ .bool false := by
  simp only [Expr.notFalse, Expr.eval, hI.or, hI.isNull]
  rcases hb with h | ⟨b, h⟩ <;> rw [h]
  · simp [UnFn.apply, or3, Value.isTrue]
  · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

theorem notTrue_isTrue (hI : I.Logic) {row : Row} {a : Expr} (hb : Expr.BoolValI I row a) :
    ((a.notTrue).eval row I).isTrue = true ↔ a.eval row I ≠ .bool true := by
  simp only [Expr.notTrue, Expr.eval, hI.or, hI.isNull, hI.not]
  rcases hb with h | ⟨b, h⟩ <;> rw [h]
  · simp [UnFn.apply, or3, Value.isTrue]
  · cases b <;> simp [UnFn.apply, or3, Value.isTrue]

omit [Boxes.Ambient] in
/-- The value that decides a chain: FALSE for `AND`, TRUE for `OR`. -/
theorem comb_decides (isAnd : Bool) (v : Value) : comb isAnd (.bool !isAnd) v = .bool !isAnd := by
  cases isAnd <;> simp [comb, and3, or3]

omit [Boxes.Ambient] in
theorem comb_boolVal (isAnd : Bool) (a b : Value) :
    comb isAnd a b = .null ∨ ∃ c, comb isAnd a b = .bool c := by
  cases isAnd
  · exact or3_bool a b
  · exact and3_bool a b

theorem joinOp_eval (hI : I.Logic) (isAnd : Bool) (acc : Option Expr) (e : Expr) (row : Row) :
    (joinOp isAnd acc e).eval row I =
      match acc with | none => e.eval row I | some a => comb isAnd (a.eval row I) (e.eval row I) := by
  cases acc with
  | none => rfl
  | some a => cases isAnd <;> simp [joinOp, Expr.eval, hI.and, hI.or, comb]

omit [Boxes.Ambient] in
theorem joinOp_refsLt {isAnd : Bool} {acc : Option Expr} {e : Expr} {n : Nat}
    (ha : ∀ a ∈ acc, a.refsLt n) (he : e.refsLt n) : (joinOp isAnd acc e).refsLt n := by
  cases acc with
  | none => exact he
  | some a => cases isAnd <;> exact ⟨ha a rfl, he⟩

omit [Boxes.Ambient] in
theorem reachOf_refsLt {isAnd : Bool} {g acc : Option Expr} {n : Nat}
    (hg : ∀ c ∈ g, c.refsLt n) (ha : ∀ a ∈ acc, a.refsLt n) : ∀ c ∈ reachOf isAnd g acc, c.refsLt n := by
  intro c hc
  cases acc with
  | none => exact hg c hc
  | some a =>
    simp only [reachOf, Option.mem_def, Option.some.injEq] at hc
    subst hc
    have hn : (if isAnd then a.notFalse else a.notTrue).refsLt n := by
      have := ha a rfl
      cases isAnd
      · exact ⟨this, this⟩
      · exact ⟨this, this⟩
    cases g with
    | none => exact hn
    | some g => exact ⟨hg g rfl, hn⟩

/-- The reach of a level: where `g` holds, it holds unless the running value
decides the chain. -/
theorem reachOf_iff (hI : I.Logic) {isAnd : Bool} {g : Option Expr} {a : Expr} {row : Row}
    (hb : Expr.BoolValI I row a) (hg : Reach I g row) :
    Reach I (reachOf isAnd g (some a)) row ↔ a.eval row I ≠ .bool !isAnd := by
  simp only [reachOf, Reach, Option.mem_def, Option.some.injEq, forall_eq']
  rw [guardAnd_isTrue hI]
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]; rw [notTrue_isTrue hI hb]; exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  · simp only [↓reduceIte, Bool.not_true]; rw [notFalse_isTrue hI hb]; exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

theorem reach_prefix {g : Option Expr} {row F F' : Row} {n : Nat} (hg : ∀ c ∈ g, c.refsLt n)
    (hlen : row.length + F.length = n) (hp : F <+: F') : Reach I g (row ++ F') ↔ Reach I g (row ++ F) := by
  cases g with
  | none => simp [Reach]
  | some c => simp only [Reach, Option.mem_def, Option.some.injEq, forall_eq', eval_prefix (hg c rfl) hlen hp]

omit [Boxes.Ambient] in
theorem getD_append_single (l : List Value) (x : Value) (i : Nat) (h : l.length = i) :
    (l ++ [x]).getD i .null = x := by
  subst h; simp [List.getD_eq_getElem?_getD]

/-- The anchored reach holds where the reach did, over a state that grew. -/
theorem BindSt.anchor_spec {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (hs : s.Ext I cat r w F) (g : Option Expr) (hg : ∀ c ∈ g, c.refsLt s.width) :
    ∃ F', Grows I cat r w s (s.anchor g).1 F F' ∧
      (∀ c ∈ (s.anchor g).2, c.refsLt (s.anchor g).1.width) ∧
      ∀ row ∈ r.eval cat I, (Reach I (s.anchor g).2 (row ++ F' row) ↔ Reach I g (row ++ F row)) := by
  cases g with
  | none => exact ⟨F, Grows.refl hs, by simp [BindSt.anchor], fun _ _ => by simp [BindSt.anchor, Reach]⟩
  | some c =>
    by_cases hc : c.isField = true
    · have ha : s.anchor (some c) = (s, some c) := by simp [BindSt.anchor, hc]
      rw [ha]
      exact ⟨F, Grows.refl hs, hg, fun _ _ => Iff.rfl⟩
    · have ha : s.anchor (some c) = ((s.push c).1, some (.field (s.push c).2)) := by
        simp [BindSt.anchor, hc]
      rw [ha]
      refine ⟨_, BindSt.push_grows hs c, ?_, fun row hr => ?_⟩
      · intro c' hc'
        simp only [Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        show s.width < s.width + 1
        omega
      · have hl := hs.2.1 row hr
        have hidx : (row ++ F row).length = (s.push c).2 := by
          simp [BindSt.push]; omega
        simp only [Reach, Option.mem_def, Option.some.injEq, forall_eq', Expr.eval, ← List.append_assoc]
        rw [getD_append_single _ _ _ hidx]

/-- The bound body's and the lift's values: both read the row, then their
chains' values. -/
theorem subst_fields_eval (body : Expr) (row X : Row) (w : Nat) (h : row.length = w) (es : List Expr) :
    (body.subst ((List.range w).map Expr.field ++ es)).eval (row ++ X) I =
      body.eval (row ++ es.map (·.eval (row ++ X) I)) I := by
  rw [Expr.eval_subst, List.map_append, map_range_field row X w h]

mutual
/-- **The binder's invariant**: the levels extend the input's rows, and where
the reach `g` holds, the bound expression has the lift's value. -/
theorem LExpr.bind_spec (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (x : LExpr) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext I cat r w F →
      (∀ c ∈ g, c.refsLt s.width) → x.Scoped w →
      ∃ F', Grows I cat r w s (x.bind w g s).1 F F' ∧ (x.bind w g s).2.refsLt (x.bind w g s).1.width ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → x.Bools I w row →
          (x.bind w g s).2.eval (row ++ F' row) I = (x.fill w).eval row I
  | .mk body cs, g, s, F, hs, hg, ⟨hbody, hcs⟩ => by
    obtain ⟨F', hG, hrefs, hlen, hv⟩ := LChain.bindAll_spec hI cat r w body 0 cs g s F hs hg hcs
    refine ⟨F', hG, ?_, ?_⟩
    · simp only [LExpr.bind]
      apply Expr.refsLt_subst_below hbody
      intro i hi
      have hw := hG.1.2.2
      by_cases hiw : i < w
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hiw)]
        simp only [List.getElem?_map, List.getElem?_range hiw, Option.map_some, Option.getD_some]
        exact Nat.lt_of_lt_of_le hiw hw
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, List.length_range]
        have hj : i - w < (LChain.bindAll w g s body 0 cs).2.length := by omega
        rw [List.getElem?_eq_getElem hj, Option.getD_some]
        exact hrefs _ (List.getElem_mem hj)
    · intro row hr hreach hb
      have hrow := (hG.1.2.1 row hr).1
      simp only [LExpr.bind, LExpr.fill]
      rw [subst_fields_eval body row (F' row) w hrow, hv row hr hreach hb]
      have := subst_fields_eval (I := I) body row [] w hrow (LChain.fillAll w cs)
      simp only [List.append_nil] at this
      rw [this]
theorem LChain.bindAll_spec (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) (body : Expr) :
    ∀ (i : Nat) (cs : List LChain) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext I cat r w F →
      (∀ c ∈ g, c.refsLt s.width) → LChain.ScopedAll w cs →
      ∃ F', Grows I cat r w s (LChain.bindAll w g s body i cs).1 F F' ∧
        (∀ e ∈ (LChain.bindAll w g s body i cs).2, e.refsLt (LChain.bindAll w g s body i cs).1.width) ∧
        (LChain.bindAll w g s body i cs).2.length = cs.length ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → LChain.BoolsAll I w row cs →
          (LChain.bindAll w g s body i cs).2.map (·.eval (row ++ F' row) I) =
            (LChain.fillAll w cs).map (·.eval row I)
  | _, [], g, s, F, hs, _, _ => ⟨F, Grows.refl hs, by simp [LChain.bindAll], rfl,
      fun _ _ _ _ => by simp [LChain.bindAll, LChain.fillAll]⟩
  | i, c :: cs, g, s, F, hs, hg, ⟨hc, hcs⟩ => by
    -- The chain itself: bound, or filled in place.
    have hp : ∃ F₁, Grows I cat r w s
          (if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)).1 F F₁ ∧
        (if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)).2.refsLt
          (if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)).1.width ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → LChain.Bools I w row c →
          (if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)).2.eval
            (row ++ F₁ row) I = (LChain.fill w c).eval row I := by
      split
      · exact LChain.bind_spec hI cat r w c g s F hs hg hc
      · refine ⟨F, Grows.refl hs, Expr.refsLt_mono _ hs.2.2 (LChain.fill_refsLt w c hc), ?_⟩
        intro row hr _ _
        exact Expr.eval_append (F row) (LChain.fill_refsLt w c hc) (hs.2.1 row hr).1
    generalize hP : (if (body.readsCol (w + i) && body.eagerOnly (w + i)) then LChain.bind w g s c else (s, LChain.fill w c)) = P at hp
    obtain ⟨F₁, hG₁, hr₁, hv₁⟩ := hp
    have hg₁ : ∀ c ∈ g, c.refsLt P.1.width := fun c hc => Expr.refsLt_mono _ hG₁.2.2 (hg c hc)
    obtain ⟨F₂, hG₂, hrs₂, hlen₂, hv₂⟩ := LChain.bindAll_spec hI cat r w body (i + 1) cs g P.1 F₁ hG₁.1 hg₁ hcs
    have hb : LChain.bindAll w g s body i (c :: cs) = ((LChain.bindAll w g P.1 body (i + 1) cs).1,
        P.2 :: (LChain.bindAll w g P.1 body (i + 1) cs).2) := by
      simp only [LChain.bindAll, hP]
    rw [hb]
    refine ⟨F₂, Grows.trans hG₁ hG₂, ?_, by simp [hlen₂], ?_⟩
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact Expr.refsLt_mono _ hG₂.2.2 hr₁
      · exact hrs₂ e he
    · intro row hr hreach ⟨hbc, hbcs⟩
      have hl₁ := (hG₁.1.2.1 row hr)
      have hreach₁ : Reach I g (row ++ F₁ row) :=
        (reach_prefix hg (by have := (hs.2.1 row hr); omega) (hG₁.2.1 row)).mpr hreach
      simp only [List.map_cons, LChain.fillAll]
      rw [hv₂ row hr hreach₁ hbcs, ← hv₁ row hr hreach hbc,
        eval_prefix hr₁ (by omega) (hG₂.2.1 row)]
theorem LChain.bind_spec (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (c : LChain) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext I cat r w F →
      (∀ c ∈ g, c.refsLt s.width) → c.Scoped w →
      ∃ F', Grows I cat r w s (LChain.bind w g s c).1 F F' ∧
        (LChain.bind w g s c).2.refsLt (LChain.bind w g s c).1.width ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → LChain.Bools I w row c →
          (LChain.bind w g s c).2.eval (row ++ F' row) I = (LChain.fill w c).eval row I
  | .mk isAnd ops, g, s, F, hs, hg, hops => by
    obtain ⟨F₀, hG₀, hg₀, hR₀⟩ := BindSt.anchor_spec hs g hg
    obtain ⟨F', hG, hr, hv⟩ := LChain.bindOps_spec hI cat r w isAnd ops (s.anchor g).2 (s.anchor g).1 F₀
      none hG₀.1 hg₀ (by simp) hops
    refine ⟨F', Grows.trans hG₀ hG, hr, fun row hrow hreach hb => ?_⟩
    rw [LChain.fill_eval hI w isAnd ops row hb]
    exact hv row hrow ((hR₀ row hrow).mpr hreach) hb (by simp)
theorem LChain.bindOps_spec (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) (isAnd : Bool) :
    ∀ (ops : List LExpr) (g : Option Expr) (s : BindSt) (F : Row → Row) (acc : Option Expr),
      s.Ext I cat r w F → (∀ c ∈ g, c.refsLt s.width) → (∀ a ∈ acc, a.refsLt s.width) →
      LExpr.ScopedAll w ops →
      ∃ F', Grows I cat r w s (LChain.bindOps w isAnd g s acc ops).1 F F' ∧
        (LChain.bindOps w isAnd g s acc ops).2.refsLt (LChain.bindOps w isAnd g s acc ops).1.width ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → LExpr.BoolsAll I w row ops →
          (∀ a ∈ acc, Expr.BoolValI I (row ++ F row) a) →
          (LChain.bindOps w isAnd g s acc ops).2.eval (row ++ F' row) I =
            foldOpt isAnd (acc.map (·.eval (row ++ F row) I)) ((LExpr.fillAll w ops).map (·.eval row I))
  | [], g, s, F, acc, hs, _, ha, _ => by
    refine ⟨F, Grows.refl hs, ?_, fun row _ _ _ _ => ?_⟩
    · cases acc with
      | none => trivial
      | some a => exact ha a rfl
    · cases acc <;> rfl
  | x :: xs, g, s, F, acc, hs, hg, ha, ⟨hx, hxs⟩ => by
    by_cases hpl : x.plain
    · -- A plain operand joins the running value.
      have hb : LChain.bindOps w isAnd g s acc (x :: xs) =
          LChain.bindOps w isAnd g s (some (joinOp isAnd acc (LExpr.fill w x))) xs := by
        simp [LChain.bindOps, hpl]
      rw [hb]
      have hfx := Expr.refsLt_mono _ hs.2.2 (LExpr.fill_refsLt w x hx)
      obtain ⟨F', hG, hr, hv⟩ := LChain.bindOps_spec hI cat r w isAnd xs g s F
        (some (joinOp isAnd acc (LExpr.fill w x))) hs hg
        (fun a ha' => by
          simp only [Option.mem_def, Option.some.injEq] at ha'; subst ha'; exact joinOp_refsLt ha hfx) hxs
      refine ⟨F', hG, hr, fun row hrow hreach ⟨⟨hbx, _⟩, hbxs⟩ hba => ?_⟩
      have hl := (hs.2.1 row hrow)
      have hxe : (LExpr.fill w x).eval (row ++ F row) I = (LExpr.fill w x).eval row I :=
        Expr.eval_append (F row) (LExpr.fill_refsLt w x hx) hl.1
      rw [hv row hrow hreach hbxs ?_]
      · simp only [LExpr.fillAll, List.map_cons, foldOpt_cons, Option.map_some, joinOp_eval hI, hxe]
        cases acc <;> rfl
      · intro a ha'
        simp only [Option.mem_def, Option.some.injEq] at ha'; subst ha'
        rw [Expr.BoolValI, joinOp_eval hI]
        cases acc with
        | none => show Expr.BoolValI I _ _; unfold Expr.BoolValI; rw [hxe]; exact hbx
        | some a => exact comb_boolVal _ _ _
    · -- An operand that may raise gets a level.
      have hb : LChain.bindOps w isAnd g s acc (x :: xs) =
          LChain.bindOps w isAnd g ((LExpr.bind w (reachOf isAnd g acc) s x).1.push
            (joinOp isAnd acc (guardCase (reachOf isAnd g acc) (LExpr.bind w (reachOf isAnd g acc) s x).2))).1
            (some (.field ((LExpr.bind w (reachOf isAnd g acc) s x).1.push
            (joinOp isAnd acc (guardCase (reachOf isAnd g acc) (LExpr.bind w (reachOf isAnd g acc) s x).2))).2)) xs := by
        simp [LChain.bindOps, hpl]
      rw [hb]
      generalize hreachDef : reachOf isAnd g acc = reach at *
      have hreachRefs : ∀ c ∈ reach, c.refsLt s.width := hreachDef ▸ reachOf_refsLt hg ha
      obtain ⟨F₁, hG₁, hr₁, hv₁⟩ := LExpr.bind_spec hI cat r w x reach s F hs hreachRefs hx
      generalize hP : LExpr.bind w reach s x = P at hG₁ hr₁ hv₁
      have hcol : (joinOp isAnd acc (guardCase reach P.2)).refsLt P.1.width := by
        apply joinOp_refsLt (fun a ha' => Expr.refsLt_mono _ hG₁.2.2 (ha a ha'))
        cases reach with
        | none => exact hr₁
        | some c => exact ⟨Expr.refsLt_mono _ hG₁.2.2 (hreachRefs c rfl), hr₁, trivial⟩
      have hG₂ := BindSt.push_grows hG₁.1 (joinOp isAnd acc (guardCase reach P.2))
      generalize hQ : P.1.push (joinOp isAnd acc (guardCase reach P.2)) = Q at hG₂
      have hQ2 : Q.2 = P.1.width := by rw [← hQ]; rfl
      have hQw : Q.1.width = P.1.width + 1 := by rw [← hQ]; rfl
      obtain ⟨F₃, hG₃, hr₃, hv₃⟩ := LChain.bindOps_spec hI cat r w isAnd xs g Q.1 _ (some (.field Q.2))
        hG₂.1 (fun c hc => Expr.refsLt_mono _ (Nat.le_trans hG₁.2.2 hG₂.2.2) (hg c hc))
        (fun a ha' => by
          simp only [Option.mem_def, Option.some.injEq] at ha'; subst ha'; show Q.2 < Q.1.width; omega) hxs
      refine ⟨F₃, Grows.trans (Grows.trans hG₁ hG₂) hG₃, hr₃, fun row hrow hreach ⟨⟨hbx, hbx'⟩, hbxs⟩ hba => ?_⟩
      have hl := hs.2.1 row hrow
      have hl₁ := hG₁.1.2.1 row hrow
      -- The level's value: the running value joined with the operand's, where it is reached.
      have hlevel : (joinOp isAnd acc (guardCase reach P.2)).eval (row ++ F₁ row) I =
          match acc.map (·.eval (row ++ F row) I) with
          | none => (LExpr.fill w x).eval row I
          | some a => comb isAnd a ((LExpr.fill w x).eval row I) := by
        rw [joinOp_eval hI]
        have hacc : ∀ a ∈ acc, a.eval (row ++ F₁ row) I = a.eval (row ++ F row) I :=
          fun a ha' => eval_prefix (ha a ha') (by omega) (hG₁.2.1 row)
        cases acc with
        | none =>
          rw [← hreachDef] at hv₁ ⊢
          have hR : Reach I g (row ++ F₁ row) :=
            (reach_prefix hg (by omega) (hG₁.2.1 row)).mpr hreach
          simp only [reachOf] at hv₁ ⊢
          rw [guardCase_eval_reach hR]
          exact hv₁ row hrow hreach hbx'
        | some a =>
          simp only [Option.map_some]
          rw [hacc a rfl]
          have hba' := hba a rfl
          by_cases hR : Reach I reach (row ++ F row)
          · have hR₁ : Reach I reach (row ++ F₁ row) := (reach_prefix hreachRefs (by omega) (hG₁.2.1 row)).mpr hR
            rw [guardCase_eval_reach hR₁, hv₁ row hrow hR hbx']
          · have hR₁ : ¬ Reach I reach (row ++ F₁ row) :=
              fun h => hR ((reach_prefix hreachRefs (by omega) (hG₁.2.1 row)).mp h)
            rw [guardCase_eval_not hR₁]
            rw [← hreachDef] at hR
            have hdec : a.eval (row ++ F row) I = .bool !isAnd := by
              have := (not_congr (reachOf_iff hI (isAnd := isAnd) hba' hreach)).mp hR
              exact Classical.not_not.mp this
            rw [hdec, comb_decides, comb_decides]
      have hidx : (row ++ F₁ row).length = Q.2 := by
        rw [hQ2, List.length_append]; omega
      have hfield : (Expr.field Q.2).eval (row ++ (F₁ row ++
          [(joinOp isAnd acc (guardCase reach P.2)).eval (row ++ F₁ row) I])) I =
          (joinOp isAnd acc (guardCase reach P.2)).eval (row ++ F₁ row) I := by
        simp only [Expr.eval, ← List.append_assoc]
        exact getD_append_single _ _ _ hidx
      have hacc₃ : ∀ a ∈ some (Expr.field Q.2), Expr.BoolValI I (row ++ (F₁ row ++
          [(joinOp isAnd acc (guardCase reach P.2)).eval (row ++ F₁ row) I])) a := by
        intro a ha'
        simp only [Option.mem_def, Option.some.injEq] at ha'; subst ha'
        rw [Expr.BoolValI, hfield, hlevel]
        cases acc with
        | none => exact hbx
        | some a => exact comb_boolVal _ _ _
      have hreach₂ : Reach I g (row ++ (F₁ row ++ [(joinOp isAnd acc (guardCase reach P.2)).eval (row ++ F₁ row) I])) :=
        (reach_prefix hg (by omega) ((hG₁.2.1 row).trans (List.prefix_append _ _))).mpr hreach
      rw [hv₃ row hrow hreach₂ hbxs hacc₃]
      simp only [LExpr.fillAll, List.map_cons, foldOpt_cons, Option.map_some]
      rw [hfield, hlevel]
end

omit [Boxes.Ambient] in
theorem map_range_getD_append (row X : Row) (w : Nat) (h : row.length = w) :
    (List.range w).map ((row ++ X).getD · .null) = row := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]

/-- **T1, rows**: the filter on the bound condition keeps the rows the filter on
D50's lift keeps, in the same order, where every chain's operands are TRUE,
FALSE or NULL. -/
theorem Rel.guardedFilter_eval (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) (x : LExpr)
    (hw : ∀ row ∈ r.eval cat I, row.length = w) (hx : x.Scoped w)
    (hb : ∀ row ∈ r.eval cat I, x.Bools I w row) :
    (r.guardedFilter w x).eval cat I = (r.filter (x.fill w)).eval cat I := by
  have hs : BindSt.Ext I cat r w ⟨r, w⟩ (fun _ => []) :=
    ⟨by simp, fun row hr => ⟨hw row hr, by simp⟩, Nat.le_refl w⟩
  obtain ⟨F', hG, _, hv⟩ := LExpr.bind_spec hI cat r w x none ⟨r, w⟩ (fun _ => []) hs (by simp) hx
  simp only [Rel.guardedFilter, Rel.eval, hG.1.1, List.filter_map, List.map_map]
  have hf : List.filter ((fun row => (Expr.eval row (LExpr.bind w none ⟨r, w⟩ x).2 I).isTrue) ∘
      fun row => row ++ F' row) (r.eval cat I) =
      List.filter (fun row => ((x.fill w).eval row I).isTrue) (r.eval cat I) :=
    List.filter_congr fun row hr => by
      simp only [Function.comp_apply]
      rw [hv row hr (by simp [Reach]) (hb row hr)]
  rw [hf]
  conv => rhs; rw [← List.map_id (List.filter _ (r.eval cat I))]
  apply List.map_congr_left
  intro row hr
  have hr' := (List.mem_filter.mp hr).1
  exact map_range_getD_append row (F' row) w (hw row hr')

omit [Boxes.Ambient] in
theorem LExpr.bindList_length (w : Nat) : ∀ (s : BindSt) (xs : List LExpr),
    (LExpr.bindList w s xs).2.length = xs.length
  | _, [] => rfl
  | s, _ :: xs => by simp [LExpr.bindList, LExpr.bindList_length w _ xs]

/-- `bind_spec` for a list of expressions bound in turn. -/
theorem LExpr.bindList_spec (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (xs : List LExpr) (s : BindSt) (F : Row → Row), s.Ext I cat r w F → LExpr.ScopedAll w xs →
      ∃ F', Grows I cat r w s (LExpr.bindList w s xs).1 F F' ∧
        (∀ e ∈ (LExpr.bindList w s xs).2, e.refsLt (LExpr.bindList w s xs).1.width) ∧
        ∀ row ∈ r.eval cat I, LExpr.BoolsAll I w row xs →
          (LExpr.bindList w s xs).2.map (·.eval (row ++ F' row) I) = (LExpr.fillAll w xs).map (·.eval row I)
  | [], s, F, hs, _ => ⟨F, Grows.refl hs, by simp [LExpr.bindList], fun _ _ _ => by
      simp [LExpr.bindList, LExpr.fillAll]⟩
  | x :: xs, s, F, hs, ⟨hx, hxs⟩ => by
    obtain ⟨F₁, hG₁, hr₁, hv₁⟩ := LExpr.bind_spec hI cat r w x none s F hs (by simp) hx
    obtain ⟨F₂, hG₂, hr₂, hv₂⟩ := LExpr.bindList_spec hI cat r w xs _ F₁ hG₁.1 hxs
    refine ⟨F₂, Grows.trans hG₁ hG₂, ?_, fun row hr ⟨⟨_, hbx⟩, hbxs⟩ => ?_⟩
    · intro e he
      simp only [LExpr.bindList, List.mem_cons] at he
      rcases he with rfl | he
      · exact Expr.refsLt_mono _ hG₂.2.2 hr₁
      · exact hr₂ e he
    · have hl₁ := hG₁.1.2.1 row hr
      simp only [LExpr.bindList, List.map_cons, LExpr.fillAll]
      rw [hv₂ row hr hbxs, eval_prefix hr₁ (by omega) (hG₂.2.1 row), hv₁ row hr (by simp [Reach]) hbx]

/-- **T1 for a projection, rows**: the bound projection has the rows of the
projection of the lifts. -/
theorem Rel.guardedProject_eval (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) (xs : List LExpr)
    (hw : ∀ row ∈ r.eval cat I, row.length = w) (hx : LExpr.ScopedAll w xs)
    (hb : ∀ row ∈ r.eval cat I, LExpr.BoolsAll I w row xs) :
    (r.guardedProject w xs).eval cat I = (r.project (LExpr.fillAll w xs)).eval cat I := by
  have hs : BindSt.Ext I cat r w ⟨r, w⟩ (fun _ => []) :=
    ⟨by simp, fun row hr => ⟨hw row hr, by simp⟩, Nat.le_refl w⟩
  obtain ⟨F', hG, _, hv⟩ := LExpr.bindList_spec hI cat r w xs ⟨r, w⟩ (fun _ => []) hs hx
  simp only [Rel.guardedProject, Rel.eval, hG.1.1, List.map_map]
  apply List.map_congr_left
  intro row hr
  have hl := hG.1.2.1 row hr
  have hlen := LExpr.bindList_length w ⟨r, w⟩ xs
  simp only [Function.comp_apply, List.map_append, List.map_map]
  rw [← hv row hr (hb row hr)]
  congr 1
  · rw [List.append_assoc]; exact map_range_getD_append row _ w (hw row hr)
  · apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append]
    rw [show (LExpr.bindList w ⟨r, w⟩ xs).1.width + k - (row.length + (F' row).length) = k by omega]
    have hk : k < (LExpr.bindList w ⟨r, w⟩ xs).2.length := by simp at h2; omega
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]

end Eval


/-! ## T1: the bound plan's raises (T1a, T1b)

Under the reference, the bound filter raises exactly where the filter on
D50's lift does: `Rel.guardedFilter_raises`. A level raises only where its reach
holds and its operand raises; the guards and running values are plain
(`Expr.plain`) and raise nowhere. -/

section Raises
variable [Boxes.Ambient]

/-- The outcome of entry `i` of a substitution. -/
abbrev entryP (p : Profile) (σ : List Expr) (i : Nat) (row : Row) : Outcome :=
  (σ.getD i (.lit .null)).evalP p row

omit [Boxes.Ambient] in
/-- Substituting entries with the same outcome gives the same outcome; and
where an entry `t` reads eagerly raises, so does `t` with it substituted:
where the outcomes differ, it is because such an entry raises. -/
theorem Expr.evalP_subst_congr {p : Profile} :
    ∀ (t : Expr) (row row' : Row) (σ σ' : List Expr),
      (∀ i, t.readsCol i → entryP p σ i row = entryP p σ' i row' ∨
          (t.eagerOnly i ∧ (entryP p σ i row).err?.isSome)) →
      (t.subst σ).evalP p row = (t.subst σ').evalP p row' ∨
        ((t.subst σ).evalP p row).err?.isSome ∧ ∃ i, t.readsCol i ∧ entryP p σ i row ≠ entryP p σ' i row'
  | .lit _, _, _, _, _, _ => .inl rfl
  | .field i, row, row', σ, σ', h => by
    by_cases hq : entryP p σ i row = entryP p σ' i row'
    · exact .inl hq
    · rcases h i (by simp [Expr.readsCol]) with h | ⟨_, h⟩
      · exact absurd h hq
      · exact .inr ⟨h, i, by simp [Expr.readsCol], hq⟩
  | .un f a, row, row', σ, σ', h => by
    rcases Expr.evalP_subst_congr a row row' σ σ' h with h1 | ⟨h1, i, hi, hr⟩
    · left; simp only [Expr.subst, Expr.evalP, h1]
    · right; refine ⟨?_, i, hi, hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases ha : (a.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [ha, Outcome.err?] at h1
  | .bin f a b, row, row', σ, σ', h => by
    have ha := Expr.evalP_subst_congr a row row' σ σ' (fun i hi => (h i (by simp [Expr.readsCol, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1, hr⟩)
    have hb := Expr.evalP_subst_congr b row row' σ σ' (fun i hi => (h i (by simp [Expr.readsCol, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.2, hr⟩)
    rcases ha with ha | ⟨ha, i, hi, hr⟩
    · rcases hb with hb | ⟨hb, i, hi, hr⟩
      · left; simp only [Expr.subst, Expr.evalP, ha, hb]
      · right; refine ⟨?_, i, by simp [Expr.readsCol, hi], hr⟩
        simp only [Expr.subst, Expr.evalP]
        cases hx : (a.subst σ).evalP p row with
        | error k => rfl
        | ok v =>
          simp only [bind, Except.bind]
          cases hy : (b.subst σ).evalP p row with
          | error k => rfl
          | ok y => simp [hy, Outcome.err?] at hb
    · right; refine ⟨?_, i, by simp [Expr.readsCol, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (a.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at ha
  | .ifThen c t e, row, row', σ, σ', h => by
    have hc := Expr.evalP_subst_congr c row row' σ σ' (fun i hi => (h i (by simp [Expr.readsCol, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1.1, hr⟩)
    -- A branch reads only entries the `CASE` does not read eagerly: their outcomes agree.
    have heq : ∀ i, (t.readsCol i ∨ e.readsCol i) → entryP p σ i row = entryP p σ' i row' := by
      intro i hi
      have hr : (Expr.ifThen c t e).readsCol i := by
        simp only [Expr.readsCol, Bool.or_eq_true]; rcases hi with hi | hi
        · exact .inl (.inr hi)
        · exact .inr hi
      rcases h i hr with h1 | ⟨he, _⟩
      · exact h1
      · rcases hi with hi | hi <;> simp [Expr.eagerOnly, hi] at he
    have ht : (t.subst σ).evalP p row = (t.subst σ').evalP p row' := by
      rcases Expr.evalP_subst_congr t row row' σ σ' (fun i hi => .inl (heq i (.inl hi))) with h1 | ⟨_, i, hi, hr⟩
      · exact h1
      · exact absurd (heq i (.inl hi)) hr
    have he : (e.subst σ).evalP p row = (e.subst σ').evalP p row' := by
      rcases Expr.evalP_subst_congr e row row' σ σ' (fun i hi => .inl (heq i (.inr hi))) with h1 | ⟨_, i, hi, hr⟩
      · exact h1
      · exact absurd (heq i (.inr hi)) hr
    rcases hc with hc | ⟨hc, i, hi, hr⟩
    · left; simp only [Expr.subst, Expr.evalP, hc, ht, he]
    · right; refine ⟨?_, i, by simp [Expr.readsCol, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (c.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at hc
  | .hof f l b, row, row', σ, σ', h => by
    have hl := Expr.evalP_subst_congr l row row' σ σ' (fun i hi => (h i (by simp [Expr.readsCol, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1, hr⟩)
    -- The body reads only entries the lambda does not read eagerly: their outcomes agree.
    have heq : ∀ i, b.readsCol (i + 1) → entryP p σ i row = entryP p σ' i row' := by
      intro i hi
      rcases h i (by simp [Expr.readsCol, hi]) with h1 | ⟨he, _⟩
      · exact h1
      · simp [Expr.eagerOnly, hi] at he
    have hbody : ∀ x : Value, (b.subst (.field 0 :: σ.map (·.shift 0))).evalP p (x :: row) =
        (b.subst (.field 0 :: σ'.map (·.shift 0))).evalP p (x :: row') := by
      intro x
      have hent : ∀ j, b.readsCol j → entryP p (.field 0 :: σ.map (·.shift 0)) j (x :: row) =
          entryP p (.field 0 :: σ'.map (·.shift 0)) j (x :: row') := by
        intro j hj
        cases j with
        | zero => rfl
        | succ i =>
          have h1 := heq i hj
          simp only [entryP, List.getD_eq_getElem?_getD] at h1 ⊢
          cases hσ : σ[i]? <;> cases hσ' : σ'[i]? <;>
            simp_all [Expr.evalP_shift_cons, Expr.evalP]
      rcases Expr.evalP_subst_congr b (x :: row) (x :: row') _ _ (fun j hj => .inl (hent j hj)) with
        k | ⟨_, j, hj, hr⟩
      · exact k
      · exact absurd (hent j hj) hr
    rcases hl with hl | ⟨hl, i, hi, hr⟩
    · left; simp only [Expr.subst, Expr.evalP, hl, hbody]
    · right; refine ⟨?_, i, by simp [Expr.readsCol, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (l.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at hl

/-- Under the reference, raising is having an error issue. -/
theorem Expr.raisesOn_reference (row : Row) (e : Expr) :
    e.RaisesOn Profile.reference row ↔ e.Raises row := by
  simp only [Expr.RaisesOn, Expr.evalP_reference, Expr.refOutcome_err, Expr.Raises]

/-- A plain expression's outcome under the reference: its value. -/
theorem Expr.evalP_plain {row : Row} {e : Expr} (h : e.plain = true) :
    e.evalP Profile.reference row = .ok (e.eval row) := by
  rw [Expr.evalP_reference]; unfold Expr.refOutcome; rw [Expr.issues_plain row e h]; rfl

/-- A plain expression's value under the reference's functions is its value. -/
theorem Expr.evalI_plain {row : Row} {e : Expr} (h : e.plain = true) :
    e.eval row Profile.reference.impl = e.eval row :=
  Expr.evalI_of_evalP (Expr.evalP_plain h)

/-- A projection raises where its input does, or one of its expressions on one
of its input's rows. -/
theorem Rel.raises_project {p : Profile} {cat : Catalog} {R : Rel} {e : Expr} :
    (Rel.project R [e]).Raises p cat ↔ R.Raises p cat ∨ ∃ row ∈ R.eval cat p.impl, e.RaisesOn p row := by
  simp [Rel.Raises]

/-- Two extensions of the same state agree on the input's rows. -/
theorem BindSt.Ext.unique {I : Impl} {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F G : Row → Row}
    (hF : s.Ext I cat r w F) (hG : s.Ext I cat r w G) : ∀ row ∈ r.eval cat I, F row = G row := by
  intro row hr
  have := List.map_inj_left.mp (hF.1.symm.trans hG.1) row hr
  simpa using this

/-- Where `e` does not raise, its value under the reference's functions is its value. -/
theorem Expr.evalI_ref_of_not_raises {row : Row} {e : Expr} (h : ¬ e.Raises row) :
    e.eval row Profile.reference.impl = e.eval row := by
  apply Expr.evalI_of_evalP
  rw [Expr.evalP_reference]; unfold Expr.refOutcome
  have : firstError (e.issues row) = none := by
    simp only [Expr.Raises, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h; exact h
  rw [this]

/-- The running value lets the next operand run: not FALSE for `AND`, not TRUE
for `OR`; the first operand always runs. -/
def accGoes (isAnd : Bool) : Option Value → Prop
  | none => True
  | some a => a ≠ .bool !isAnd

/-- The running value after the next operand's value `v`. -/
def stepAcc (isAnd : Bool) (acc : Option Value) (v : Value) : Value :=
  match acc with | none => v | some a => comb isAnd a v

/-- Some operand of `ops` runs and raises: it raises under the reference, and
the running value before it (the operands' values under the reference's
functions, folded onto `acc`) lets it run. -/
def raiseFrom (w : Nat) (isAnd : Bool) (row : Row) : Option Value → List LExpr → Prop
  | _, [] => False
  | acc, x :: xs => (accGoes isAnd acc ∧ (x.fill w).Raises row) ∨
      raiseFrom w isAnd row (some (stepAcc isAnd acc ((x.fill w).eval row Profile.reference.impl))) xs

/-- An operand that goes on, for `AND` (`Expr.Go`) or `OR` (`Expr.GoOr`). -/
def goesOn (isAnd : Bool) (row : Row) (q : Expr) : Prop :=
  if isAnd then Expr.Go row q else Expr.GoOr row q

theorem raiseFrom_dead (w : Nat) (isAnd : Bool) (row : Row) :
    ∀ ops, ¬ raiseFrom w isAnd row (some (.bool !isAnd)) ops
  | [] => id
  | x :: xs => by
    simp only [raiseFrom, accGoes, ne_eq, not_true_eq_false, false_and, false_or, stepAcc,
      comb_decides]
    exact raiseFrom_dead w isAnd row xs

omit [Boxes.Ambient] in
theorem stepAcc_goes {isAnd : Bool} {acc : Option Value} {v : Value} (ha : accGoes isAnd acc)
    (hab : ∀ a ∈ acc, a.IsBool) (hv : v.IsBool) (hvd : v ≠ .bool !isAnd) :
    stepAcc isAnd acc v ≠ .bool !isAnd ∧ (stepAcc isAnd acc v).IsBool := by
  cases acc with
  | none => exact ⟨hvd, hv⟩
  | some a =>
    have haa := hab a rfl
    simp only [accGoes] at ha
    simp only [stepAcc]
    refine ⟨?_, comb_boolVal isAnd a v⟩
    rcases haa with rfl | ⟨b, rfl⟩ <;> rcases hv with rfl | ⟨c, rfl⟩ <;>
      cases isAnd <;> (try cases b) <;> (try cases c) <;> simp_all [comb, and3, or3]

/-- **`raiseFrom` is the lifts' raise** (`Expr.andLift_raises_iff`,
`Expr.orLift_raises_iff`): an operand raises after operands that go on. -/
theorem raiseFrom_iff (w : Nat) (isAnd : Bool) (row : Row) : ∀ (ops : List LExpr) (acc : Option Value),
    accGoes isAnd acc → (∀ a ∈ acc, a.IsBool) → LExpr.BoolsAll Profile.reference.impl w row ops →
    (raiseFrom w isAnd row acc ops ↔ ∃ pre p post, LExpr.fillAll w ops = pre ++ p :: post ∧
      (∀ q ∈ pre, goesOn isAnd row q) ∧ p.Raises row)
  | [], _, _, _, _ => by
    simp only [raiseFrom, LExpr.fillAll, false_iff, not_exists, not_and]
    intro pre p post h; simp at h
  | x :: xs, acc, ha, hab, ⟨⟨hbx, _⟩, hbxs⟩ => by
    simp only [raiseFrom, LExpr.fillAll]
    by_cases hx : (x.fill w).Raises row
    · simp only [ha, hx, and_self, true_or, true_iff]
      exact ⟨[], _, _, rfl, by simp, hx⟩
    · simp only [hx, and_false, false_or]
      have hval := Expr.evalI_ref_of_not_raises hx
      have hbv : (LExpr.fill w x).eval row |>.IsBool := by
        rw [← hval]; exact hbx
      -- `fill x` goes on exactly where its value is not the one that decides.
      have hgo : goesOn isAnd row (x.fill w) ↔ (x.fill w).eval row ≠ .bool !isAnd := by
        have hnr : firstError ((x.fill w).issues row) = none := by
          simp only [Expr.Raises, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hx; exact hx
        have hbv' : Expr.BoolVal row (x.fill w) := hbv
        cases isAnd
        · simp only [goesOn, Expr.GoOr, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          exact ⟨fun h => h.2.1, fun h => ⟨hnr, h, hbv'⟩⟩
        · simp only [goesOn, Expr.Go, ↓reduceIte, Bool.not_true]
          exact ⟨fun h => h.2.1, fun h => ⟨hnr, h, hbv'⟩⟩
      have hcons : (∃ pre p post, LExpr.fill w x :: LExpr.fillAll w xs = pre ++ p :: post ∧
            (∀ q ∈ pre, goesOn isAnd row q) ∧ p.Raises row) ↔
          goesOn isAnd row (x.fill w) ∧ ∃ pre p post, LExpr.fillAll w xs = pre ++ p :: post ∧
            (∀ q ∈ pre, goesOn isAnd row q) ∧ p.Raises row := by
        constructor
        · rintro ⟨pre, p, post, h, hpre, hp⟩
          cases pre with
          | nil => simp at h; exact absurd (h.1 ▸ hp) hx
          | cons q pre =>
            simp only [List.cons_append, List.cons.injEq] at h
            obtain ⟨rfl, h⟩ := h
            exact ⟨hpre _ (by simp), pre, p, post, h, fun q hq => hpre q (by simp [hq]), hp⟩
        · rintro ⟨hg, pre, p, post, h, hpre, hp⟩
          exact ⟨x.fill w :: pre, p, post, by simp [h], fun q hq => by
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hg
            · exact hpre q hq, hp⟩
      rw [hcons, hgo, ← hval]
      by_cases hd : (x.fill w).eval row Profile.reference.impl = .bool !isAnd
      · simp only [hd, ne_eq, not_true_eq_false, false_and, iff_false]
        have : stepAcc isAnd acc (.bool !isAnd) = .bool !isAnd := by
          cases acc with
          | none => rfl
          | some a => cases isAnd <;> simp [stepAcc, comb, and3_false_right, or3_true_right]
        rw [this]; exact raiseFrom_dead w isAnd row xs
      · obtain ⟨hg', hb'⟩ := stepAcc_goes ha hab (hval ▸ hbv) hd
        simp only [hd, ne_eq, not_false_eq_true, true_and]
        exact raiseFrom_iff w isAnd row xs _ hg' (by simpa using hb') hbxs

omit [Boxes.Ambient] in
theorem LChain.bindAll_length (w : Nat) (g : Option Expr) :
    ∀ (s : BindSt) (body : Expr) (i : Nat) (cs : List LChain),
      (LChain.bindAll w g s body i cs).2.length = cs.length
  | _, _, _, [] => rfl
  | s, body, i, _ :: cs => by
    simp only [LChain.bindAll, List.length_cons, LChain.bindAll_length w g _ body (i + 1) cs]

omit [Boxes.Ambient] in
theorem LChain.fillAll_getElem? (w : Nat) : ∀ (cs : List LChain) (j : Nat) (c : LChain),
    cs[j]? = some c → (LChain.fillAll w cs)[j]? = some (c.fill w)
  | [], _, _, h => by simp at h
  | d :: cs, 0, c, h => by simp at h; subst h; rfl
  | _ :: cs, j + 1, c, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [LChain.fillAll, List.getElem?_cons_succ]
    exact LChain.fillAll_getElem? w cs j c h

omit [Boxes.Ambient] in
/-- An eagerly read entry that raises makes the substituted expression raise. -/
theorem Expr.evalP_subst_eager {p : Profile} :
    ∀ (t : Expr) (row : Row) (σ : List Expr) (i : Nat), t.readsCol i → t.eagerOnly i →
      (entryP p σ i row).err?.isSome → ((t.subst σ).evalP p row).err?.isSome
  | .lit _, _, _, _, h, _, _ => by simp [Expr.readsCol] at h
  | .field j, row, σ, i, h, _, he => by
    simp only [Expr.readsCol, beq_iff_eq] at h; subst h; exact he
  | .un f a, row, σ, i, h, hg, he => by
    have := Expr.evalP_subst_eager a row σ i h hg he
    simp only [Expr.subst, Expr.evalP]
    cases ha : (a.subst σ).evalP p row with
    | error k => rfl
    | ok v => simp [ha, Outcome.err?] at this
  | .bin f a b, row, σ, i, h, hg, he => by
    simp only [Expr.eagerOnly, Bool.and_eq_true] at hg
    simp only [Expr.subst, Expr.evalP]
    cases ha : (a.subst σ).evalP p row with
    | error k => rfl
    | ok v =>
      simp only [bind, Except.bind]
      have hr : b.readsCol i := by
        simp only [Expr.readsCol, Bool.or_eq_true] at h
        rcases h with h | h
        · have := Expr.evalP_subst_eager a row σ i h hg.1 he
          simp [ha, Outcome.err?] at this
        · exact h
      have := Expr.evalP_subst_eager b row σ i hr hg.2 he
      cases hb : (b.subst σ).evalP p row with
      | error k => rfl
      | ok y => simp [hb, Outcome.err?] at this
  | .ifThen c t e, row, σ, i, h, hg, he => by
    simp only [Expr.eagerOnly, Bool.and_eq_true, Bool.not_eq_true'] at hg
    have hc : c.readsCol i := by
      simp only [Expr.readsCol, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact h
      · simp [hg.1.2] at h
      · simp [hg.2] at h
    have := Expr.evalP_subst_eager c row σ i hc hg.1.1 he
    simp only [Expr.subst, Expr.evalP]
    cases hx : (c.subst σ).evalP p row with
    | error k => rfl
    | ok v => simp [hx, Outcome.err?] at this
  | .hof f l b, row, σ, i, h, hg, he => by
    simp only [Expr.eagerOnly, Bool.and_eq_true, Bool.not_eq_true'] at hg
    have hl : l.readsCol i := by
      simp only [Expr.readsCol, Bool.or_eq_true] at h
      rcases h with h | h
      · exact h
      · simp [hg.2] at h
    have := Expr.evalP_subst_eager l row σ i hl hg.1 he
    simp only [Expr.subst, Expr.evalP]
    cases hx : (l.subst σ).evalP p row with
    | error k => rfl
    | ok v => simp [hx, Outcome.err?] at this

omit [Boxes.Ambient] in
theorem Expr.plain_subst {σ : List Expr} (hσ : ∀ i, (σ.getD i (.lit .null)).plain = true) :
    ∀ e : Expr, e.plain = true → (e.subst σ).plain = true
  | .lit _, _ => rfl
  | .field i, _ => hσ i
  | .un f a, h => by
    have ha := Expr.plain_subst hσ a
    cases f <;> simp_all [Expr.plain, Expr.subst]
  | .bin f a b, h => by
    have ha := Expr.plain_subst hσ a
    have hb := Expr.plain_subst hσ b
    cases f <;> simp_all [Expr.plain, Expr.subst]
  | .ifThen _ _ _, h | .hof _ _ _, h => by simp [Expr.plain] at h

omit [Boxes.Ambient] in
theorem LExpr.fill_plain {w : Nat} {x : LExpr} (h : x.plain = true) : (x.fill w).plain = true := by
  match x, h with
  | .mk body [], h =>
    simp only [LExpr.plain] at h
    simp only [LExpr.fill, LChain.fillAll, List.append_nil]
    apply Expr.plain_subst _ body h
    intro i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hi : i < w
    · simp [List.getElem?_range hi, Expr.plain]
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl

omit [Boxes.Ambient] in
theorem joinOp_plain {isAnd : Bool} {acc : Option Expr} {e : Expr} (ha : ∀ a ∈ acc, a.plain = true)
    (he : e.plain = true) : (joinOp isAnd acc e).plain = true := by
  cases acc with
  | none => exact he
  | some a => cases isAnd <;> simp [joinOp, Expr.plain, ha a rfl, he]

omit [Boxes.Ambient] in
theorem reachOf_plain {isAnd : Bool} {g acc : Option Expr} (hg : ∀ c ∈ g, c.plain = true)
    (ha : ∀ a ∈ acc, a.plain = true) : ∀ c ∈ reachOf isAnd g acc, c.plain = true := by
  intro c hc
  cases acc with
  | none => exact hg c hc
  | some a =>
    simp only [reachOf, Option.mem_def, Option.some.injEq] at hc; subst hc
    have hn : (if isAnd then a.notFalse else a.notTrue).plain = true := by
      cases isAnd <;> simp [Expr.notFalse, Expr.notTrue, Expr.plain, ha a rfl]
    cases g with
    | none => exact hn
    | some g => simp [guardAnd, Expr.plain, hg g rfl, hn]

omit [Boxes.Ambient] in
/-- A chain's running value is plain: it raises nowhere. -/
theorem LChain.bindOps_plain (w : Nat) (isAnd : Bool) (g : Option Expr) :
    ∀ (ops : List LExpr) (s : BindSt) (acc : Option Expr), (∀ a ∈ acc, a.plain = true) →
      (LChain.bindOps w isAnd g s acc ops).2.plain = true
  | [], _, acc, ha => by
    cases acc with
    | none => rfl
    | some a => exact ha a rfl
  | x :: xs, s, acc, ha => by
    simp only [LChain.bindOps]
    split
    · next hx => exact LChain.bindOps_plain w isAnd g xs s _ (fun a h => by
        simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact joinOp_plain ha (LExpr.fill_plain hx))
    · exact LChain.bindOps_plain w isAnd g xs _ _ (fun a h => by
        simp only [Option.mem_def, Option.some.injEq] at h; subst h; rfl)

/-- A level raises exactly where its reach holds and its operand raises. -/
theorem level_raises (isAnd : Bool) {acc reach : Option Expr} (ha : ∀ a ∈ acc, a.plain = true)
    (hr : ∀ c ∈ reach, c.plain = true) (u : Expr) (row : Row) :
    (joinOp isAnd acc (guardCase reach u)).Raises row ↔
      Reach Profile.reference.impl reach row ∧ u.Raises row := by
  have hg : (guardCase reach u).Raises row ↔ Reach Profile.reference.impl reach row ∧ u.Raises row := by
    cases reach with
    | none => simp [guardCase, Reach]
    | some c =>
      have hc := hr c rfl
      simp only [guardCase, Expr.Raises, Expr.issues, Expr.issues_plain row c hc, List.nil_append, Reach,
        Option.mem_def, Option.some.injEq, forall_eq', Expr.evalI_plain hc]
      split <;> simp_all [firstError]
  cases acc with
  | none => exact hg
  | some a =>
    have hap := ha a rfl
    rw [← hg]
    cases isAnd <;>
      simp [joinOp, Expr.Raises, Expr.issues, Expr.issues_plain row a hap,
        BinFn.issueAll_and, BinFn.issueAll_or]

/-- A level's value: the running value joined with the operand's, where the
operand runs; where it does not, the running value already decides. -/
theorem level_eval {I : Impl} (hI : I.Logic) (isAnd : Bool) {g acc : Option Expr} {u : Expr} {row : Row}
    {v : Value} (hg : Reach I g row) (hba : ∀ a ∈ acc, Expr.BoolValI I row a)
    (hu : Reach I (reachOf isAnd g acc) row → u.eval row I = v) :
    (joinOp isAnd acc (guardCase (reachOf isAnd g acc) u)).eval row I =
      stepAcc isAnd (acc.map (·.eval row I)) v := by
  rw [joinOp_eval hI]
  cases acc with
  | none =>
    simp only [reachOf] at hu ⊢
    rw [guardCase_eval_reach hg, hu hg]; rfl
  | some a =>
    simp only [Option.map_some, stepAcc]
    by_cases hR : Reach I (reachOf isAnd g (some a)) row
    · rw [guardCase_eval_reach hR, hu hR]
    · rw [guardCase_eval_not hR]
      have hdec : a.eval row I = .bool !isAnd := by
        have := (not_congr (reachOf_iff hI (isAnd := isAnd) (hba a rfl) hg)).mp hR
        exact Classical.not_not.mp this
      rw [hdec, comb_decides, comb_decides]

omit [Boxes.Ambient] in
theorem entry_fields {p : Profile} {w i : Nat} (es : List Expr) (R : Row) (hi : i < w) :
    entryP p ((List.range w).map Expr.field ++ es) i R = .ok (R.getD i .null) := by
  have : i < ((List.range w).map Expr.field).length := by simp [hi]
  simp only [entryP, List.getD_eq_getElem?_getD, List.getElem?_append_left this, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some, Expr.evalP]

omit [Boxes.Ambient] in
theorem entry_chains {p : Profile} {w : Nat} (es : List Expr) (R : Row) (j : Nat) :
    entryP p ((List.range w).map Expr.field ++ es) (w + j) R = entryP p es j R := by
  simp only [entryP, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

section RaiseInv
local notation "RP" => Profile.reference
local notation "RI" => Profile.reference.impl

/-- Anchoring a plain reach raises nowhere, and the anchored reach is plain. -/
theorem BindSt.anchor_raises {cat : Catalog} {r : Rel} {w : Nat} {s : BindSt} {F : Row → Row}
    (_hs : s.Ext RI cat r w F) (g : Option Expr) (hg : ∀ c ∈ g, c.refsLt s.width ∧ c.plain = true) :
    ((s.anchor g).1.rel.Raises RP cat ↔ s.rel.Raises RP cat) ∧
      ∀ c ∈ (s.anchor g).2, c.refsLt (s.anchor g).1.width ∧ c.plain = true := by
  cases g with
  | none => exact ⟨Iff.rfl, by simp [BindSt.anchor]⟩
  | some c =>
    by_cases hc : c.isField = true
    · have ha : s.anchor (some c) = (s, some c) := by simp [BindSt.anchor, hc]
      rw [ha]
      exact ⟨Iff.rfl, hg⟩
    · have ha : s.anchor (some c) = ((s.push c).1, some (.field (s.push c).2)) := by
        simp [BindSt.anchor, hc]
      rw [ha]
      have hp := (hg c rfl).2
      refine ⟨?_, ?_⟩
      · rw [show (s.push c).1.rel = .project s.rel [c] from rfl, Rel.raises_project]
        simp only [Expr.raisesOn_reference]
        refine ⟨fun h => h.elim id fun ⟨row, _, h⟩ => absurd h ?_, .inl⟩
        simp only [Expr.Raises, Expr.issues_plain row c hp, firstError]
        decide
      · intro c' hc'
        simp only [Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        exact ⟨show s.width < s.width + 1 by omega, rfl⟩

mutual
/-- **The binder's raises**: the levels added for `x` raise (`L`) exactly where,
under its reach, `x`'s lift raises and the bound expression does not account
for it. -/
theorem LExpr.bind_raise (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (x : LExpr) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext RI cat r w F →
      (∀ c ∈ g, c.refsLt s.width ∧ c.plain = true) → x.Scoped w →
      ∃ L : Row → Prop,
        ((x.bind w g s).1.rel.Raises RP cat ↔ s.rel.Raises RP cat ∨ ∃ row ∈ r.eval cat RI, L row) ∧
        ∀ F', (x.bind w g s).1.Ext RI cat r w F' → ∀ row ∈ r.eval cat RI, x.Bools RI w row →
          (¬ Reach RI g (row ++ F row) → ¬ L row) ∧
          (Reach RI g (row ++ F row) →
            ((x.fill w).Raises row ↔ L row ∨ (x.bind w g s).2.Raises (row ++ F' row)))
  | .mk body cs, g, s, F, hs, hg, ⟨hbody, hcs⟩ => by
    obtain ⟨L, hR, hL⟩ := LChain.bindAll_raise cat r w body 0 cs g s F hs hg hcs
    refine ⟨L, hR, fun F' hF' row hr hb => ?_⟩
    obtain ⟨hL1, hL2⟩ := hL F' hF' row hr hb
    refine ⟨hL1, fun hreach => ?_⟩
    obtain ⟨hLiff, hent⟩ := hL2 hreach
    have hrow := (hs.2.1 row hr).1
    have hrow' : (row ++ F' row).length ≥ w := by simp [hrow]
    -- The entries: the row's columns, then each chain's.
    have hlen := LChain.bindAll_length w g s body 0 cs
    have hfl := LChain.fillAll_length w cs
    -- The row's columns: the same on the row and on its extension.
    have hfield : ∀ i < w, ∀ es es' : List Expr,
        entryP RP ((List.range w).map Expr.field ++ es) i row =
          entryP RP ((List.range w).map Expr.field ++ es') i (row ++ F' row) := by
      intro i hi es es'
      rw [entry_fields es row hi, entry_fields es' _ hi]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < row.length by omega)]
    -- A chain's column: the lift's outcome, unless the chain is bound and raises.
    have hchain : ∀ j, (∀ c, cs[j]? = some c →
          entryP RP (LChain.bindAll w g s body 0 cs).2 j (row ++ F' row) = (c.fill w).evalP RP row ∨
          (body.readsCol (w + j) = true ∧ body.eagerOnly (w + j) = true ∧ (c.fill w).Raises row)) := by
      intro j c hcj
      simpa using hent j c hcj
    have hσ : ∀ i, body.readsCol i →
        entryP RP ((List.range w).map Expr.field ++ LChain.fillAll w cs) i row =
          entryP RP ((List.range w).map Expr.field ++ (LChain.bindAll w g s body 0 cs).2) i (row ++ F' row) ∨
        (body.eagerOnly i ∧ (entryP RP ((List.range w).map Expr.field ++ LChain.fillAll w cs) i row).err?.isSome) := by
      intro i hi
      by_cases hiw : i < w
      · exact .inl (hfield i hiw _ _)
      · obtain ⟨j, rfl⟩ : ∃ j, i = w + j := ⟨i - w, by omega⟩
        rw [entry_chains, entry_chains]
        by_cases hc : j < cs.length
        · obtain ⟨c, hcj⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hc⟩
          have hfj : entryP RP (LChain.fillAll w cs) j row = (c.fill w).evalP RP row := by
            simp [entryP, List.getD_eq_getElem?_getD, LChain.fillAll_getElem? w cs j c hcj]
          rw [hfj]
          rcases hchain j c hcj with he | ⟨_, heg, hrs⟩
          · exact .inl he.symm
          · exact .inr ⟨heg, (Expr.raisesOn_reference row _).mpr hrs⟩
        · left
          simp only [entryP, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
    simp only [LExpr.fill, LExpr.bind]
    rw [← Expr.raisesOn_reference, ← Expr.raisesOn_reference]
    rcases Expr.evalP_subst_congr body row (row ++ F' row) _ _ hσ with heq | ⟨hraise, i, hi, hne⟩
    · simp only [Expr.RaisesOn, heq]
      constructor
      · exact fun h => .inr h
      · rintro (hl | h)
        · obtain ⟨j, c, hcj, hrd, heg, hrs⟩ := hLiff.mp hl
          simp only [Nat.zero_add] at hrd heg
          have := Expr.evalP_subst_eager body row ((List.range w).map Expr.field ++ LChain.fillAll w cs)
            (w + j) hrd heg (by
              rw [entry_chains]
              simp only [entryP, List.getD_eq_getElem?_getD, LChain.fillAll_getElem? w cs j c hcj,
                Option.getD_some]
              exact (Expr.raisesOn_reference row _).mpr hrs)
          rw [heq] at this; exact this
        · exact h
    · -- The outcomes differ at an entry: a bound chain that raises.
      refine ⟨fun _ => .inl ?_, fun _ => hraise⟩
      by_cases hiw : i < w
      · exact absurd (hfield i hiw _ _) hne
      · obtain ⟨j, rfl⟩ : ∃ j, i = w + j := ⟨i - w, by omega⟩
        rw [entry_chains, entry_chains] at hne
        have hc : j < cs.length := Classical.byContradiction fun hc => by
          apply hne
          simp only [entryP, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl
        obtain ⟨c, hcj⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hc⟩
        have hfj : entryP RP (LChain.fillAll w cs) j row = (c.fill w).evalP RP row := by
          simp [entryP, List.getD_eq_getElem?_getD, LChain.fillAll_getElem? w cs j c hcj]
        rcases hchain j c hcj with he | ⟨hrd, heg, hrs⟩
        · exact absurd (hfj.trans he.symm) hne
        · exact hLiff.mpr ⟨j, c, hcj, by simpa using hrd, by simpa using heg, hrs⟩
theorem LChain.bindAll_raise (cat : Catalog) (r : Rel) (w : Nat) (body : Expr) :
    ∀ (i : Nat) (cs : List LChain) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext RI cat r w F →
      (∀ c ∈ g, c.refsLt s.width ∧ c.plain = true) → LChain.ScopedAll w cs →
      ∃ L : Row → Prop,
        ((LChain.bindAll w g s body i cs).1.rel.Raises RP cat ↔
          s.rel.Raises RP cat ∨ ∃ row ∈ r.eval cat RI, L row) ∧
        ∀ F', (LChain.bindAll w g s body i cs).1.Ext RI cat r w F' → ∀ row ∈ r.eval cat RI,
          LChain.BoolsAll RI w row cs →
          (¬ Reach RI g (row ++ F row) → ¬ L row) ∧
          (Reach RI g (row ++ F row) →
            (L row ↔ ∃ j c, cs[j]? = some c ∧ body.readsCol (w + (i + j)) = true ∧
              body.eagerOnly (w + (i + j)) = true ∧ (c.fill w).Raises row) ∧
            ∀ j c, cs[j]? = some c →
              entryP RP (LChain.bindAll w g s body i cs).2 j (row ++ F' row) = (c.fill w).evalP RP row ∨
              (body.readsCol (w + (i + j)) = true ∧ body.eagerOnly (w + (i + j)) = true ∧ (c.fill w).Raises row))
  | _, [], g, s, F, hs, _, _ => by
    refine ⟨fun _ => False, by simp [LChain.bindAll], fun F' _ row _ _ => ⟨fun _ h => h, fun _ => ?_⟩⟩
    simp
  | i, c :: cs, g, s, F, hs, hg, ⟨hc, hcs⟩ => by
    have hRL := Profile.reference_logic
    have hcRefs := LChain.fill_refsLt w c hc
    by_cases hcond : (body.readsCol (w + i) && body.eagerOnly (w + i)) = true
    · -- The chain is bound.
      have hb : LChain.bindAll w g s body i (c :: cs) =
          ((LChain.bindAll w g (LChain.bind w g s c).1 body (i + 1) cs).1,
            (LChain.bind w g s c).2 :: (LChain.bindAll w g (LChain.bind w g s c).1 body (i + 1) cs).2) := by
        simp only [LChain.bindAll, hcond, ↓reduceIte]
      rw [hb]
      obtain ⟨Lc, hRc, hLc⟩ := LChain.bind_raise cat r w c g s F hs hg hc
      obtain ⟨F₁, hG₁, hr₁, hv₁⟩ := LChain.bind_spec hRL cat r w c g s F hs (fun e h => (hg e h).1) hc
      have hg₁ : ∀ e ∈ g, e.refsLt (LChain.bind w g s c).1.width ∧ e.plain = true :=
        fun e h => ⟨Expr.refsLt_mono _ hG₁.2.2 (hg e h).1, (hg e h).2⟩
      obtain ⟨Lr, hRr, hLr⟩ := LChain.bindAll_raise cat r w body (i + 1) cs g _ F₁ hG₁.1 hg₁ hcs
      obtain ⟨F₂, hG₂, -, -, -⟩ := LChain.bindAll_spec hRL cat r w body (i + 1) cs g _ F₁ hG₁.1
        (fun e h => (hg₁ e h).1) hcs
      have hplain : (LChain.bind w g s c).2.plain = true := by
        match c with
        | .mk isAnd ops => exact LChain.bindOps_plain w isAnd (s.anchor g).2 ops (s.anchor g).1 none (by simp)
      refine ⟨fun row => Lc row ∨ Lr row, ?_, fun F' hF' row hr ⟨hbc, hbcs⟩ => ?_⟩
      · rw [hRr, hRc]
        constructor
        · rintro ((h | ⟨row, hr, h⟩) | ⟨row, hr, h⟩)
          · exact .inl h
          · exact .inr ⟨row, hr, .inl h⟩
          · exact .inr ⟨row, hr, .inr h⟩
        · rintro (h | ⟨row, hr, (h | h)⟩)
          · exact .inl (.inl h)
          · exact .inl (.inr ⟨row, hr, h⟩)
          · exact .inr ⟨row, hr, h⟩
      · have hl := hs.2.1 row hr
        have hl₁ := hG₁.1.2.1 row hr
        have hF₂ : F₂ row = F' row := BindSt.Ext.unique hG₂.1 hF' row hr
        have hpre : F₁ row <+: F' row := hF₂ ▸ hG₂.2.1 row
        have hreach₁ : Reach RI g (row ++ F₁ row) ↔ Reach RI g (row ++ F row) :=
          reach_prefix (fun e h => (hg e h).1) (by omega) (hG₁.2.1 row)
        obtain ⟨hc1, hc2⟩ := hLc F₁ hG₁.1 row hr hbc
        obtain ⟨hr1, hr2⟩ := hLr F' hF' row hr hbcs
        refine ⟨fun hn h => h.elim (hc1 hn) (hr1 (fun h' => hn (hreach₁.mp h'))), fun hreach => ?_⟩
        obtain ⟨hrIff, hrEnt⟩ := hr2 (hreach₁.mpr hreach)
        simp only [Bool.and_eq_true] at hcond
        refine ⟨?_, ?_⟩
        · show Lc row ∨ Lr row ↔ _
          rw [hrIff, ← hc2 hreach]
          constructor
          · rintro (h | ⟨j, c', hcj, hrd, heg, hrs⟩)
            · exact ⟨0, c, rfl, by simpa using hcond.1, by simpa using hcond.2, h⟩
            · exact ⟨j + 1, c', by simpa using hcj, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hrd,
                by rw [show i + (j + 1) = i + 1 + j by omega]; exact heg, hrs⟩
          · rintro ⟨j, c', hcj, hrd, heg, hrs⟩
            cases j with
            | zero => simp at hcj; subst hcj; exact .inl hrs
            | succ j =>
              exact .inr ⟨j, c', by simpa using hcj, by rw [show i + 1 + j = i + (j + 1) by omega]; exact hrd,
                by rw [show i + 1 + j = i + (j + 1) by omega]; exact heg, hrs⟩
        · intro j c' hcj
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hcj; subst hcj
            by_cases hrs : (c.fill w).Raises row
            · exact .inr ⟨by simpa using hcond.1, by simpa using hcond.2, hrs⟩
            · left
              simp only [entryP, List.getD_cons_zero]
              rw [Expr.evalP_plain hplain]
              have hfe : (c.fill w).evalP RP row = .ok ((c.fill w).eval row) := by
                rw [Expr.evalP_reference]; unfold Expr.refOutcome
                have : firstError ((c.fill w).issues row) = none := by
                  simp only [Expr.Raises, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hrs; exact hrs
                rw [this]
              rw [hfe, ← Expr.evalI_plain hplain, eval_prefix hr₁ (by omega) hpre,
                hv₁ row hr hreach hbc, Expr.evalI_ref_of_not_raises hrs]
          | succ j =>
            have := hrEnt j c' (by simpa using hcj)
            simp only [entryP, List.getD_cons_succ]
            rw [show i + (j + 1) = i + 1 + j by omega]
            exact this
    · -- The chain stays filled.
      have hb : LChain.bindAll w g s body i (c :: cs) =
          ((LChain.bindAll w g s body (i + 1) cs).1,
            LChain.fill w c :: (LChain.bindAll w g s body (i + 1) cs).2) := by
        simp only [LChain.bindAll, hcond, Bool.false_eq_true, ↓reduceIte]
      rw [hb]
      obtain ⟨Lr, hRr, hLr⟩ := LChain.bindAll_raise cat r w body (i + 1) cs g s F hs hg hcs
      refine ⟨Lr, hRr, fun F' hF' row hr ⟨_, hbcs⟩ => ?_⟩
      obtain ⟨hr1, hr2⟩ := hLr F' hF' row hr hbcs
      refine ⟨hr1, fun hreach => ?_⟩
      obtain ⟨hrIff, hrEnt⟩ := hr2 hreach
      simp only [Bool.and_eq_true, not_and] at hcond
      refine ⟨?_, ?_⟩
      · rw [hrIff]
        constructor
        · rintro ⟨j, c', hcj, hrd, heg, hrs⟩
          exact ⟨j + 1, c', by simpa using hcj, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hrd,
            by rw [show i + (j + 1) = i + 1 + j by omega]; exact heg, hrs⟩
        · rintro ⟨j, c', hcj, hrd, heg, hrs⟩
          cases j with
          | zero => exact absurd (by simpa using heg) (hcond (by simpa using hrd))
          | succ j =>
            exact ⟨j, c', by simpa using hcj, by rw [show i + 1 + j = i + (j + 1) by omega]; exact hrd,
              by rw [show i + 1 + j = i + (j + 1) by omega]; exact heg, hrs⟩
      · intro j c' hcj
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hcj; subst hcj
          left
          simp only [entryP, List.getD_cons_zero]
          exact Expr.evalP_append (F' row) hcRefs (hs.2.1 row hr).1
        | succ j =>
          have := hrEnt j c' (by simpa using hcj)
          simp only [entryP, List.getD_cons_succ]
          rw [show i + (j + 1) = i + 1 + j by omega]
          exact this
theorem LChain.bind_raise (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (c : LChain) (g : Option Expr) (s : BindSt) (F : Row → Row), s.Ext RI cat r w F →
      (∀ c ∈ g, c.refsLt s.width ∧ c.plain = true) → c.Scoped w →
      ∃ L : Row → Prop,
        ((LChain.bind w g s c).1.rel.Raises RP cat ↔ s.rel.Raises RP cat ∨ ∃ row ∈ r.eval cat RI, L row) ∧
        ∀ F', (LChain.bind w g s c).1.Ext RI cat r w F' → ∀ row ∈ r.eval cat RI, LChain.Bools RI w row c →
          (¬ Reach RI g (row ++ F row) → ¬ L row) ∧
          (Reach RI g (row ++ F row) → ((c.fill w).Raises row ↔ L row))
  | .mk isAnd ops, g, s, F, hs, hg, hops => by
    obtain ⟨hRa, hga⟩ := BindSt.anchor_raises hs g hg
    obtain ⟨F₀, hG₀, _, hR₀⟩ := BindSt.anchor_spec hs g (fun c h => (hg c h).1)
    obtain ⟨L, hR, hL⟩ := LChain.bindOps_raise cat r w isAnd ops (s.anchor g).2 (s.anchor g).1 F₀ none
      hG₀.1 hga (by simp) hops
    refine ⟨L, hR.trans (or_congr hRa Iff.rfl), fun F' _ row hr hb => ?_⟩
    obtain ⟨h1, h2⟩ := hL row hr hb (by simp)
    refine ⟨fun hn => h1 (fun h => hn ((hR₀ row hr).mp h)), fun hreach => ?_⟩
    rw [h2 ((hR₀ row hr).mpr hreach), Option.map_none, raiseFrom_iff w isAnd row ops none trivial (by simp) hb]
    have hbv : ∀ q ∈ LExpr.fillAll w ops, firstError (q.issues row) = none → Expr.BoolVal row q := by
      intro q hq hn
      have hnr : ¬ q.Raises row := by simp [Expr.Raises, hn]
      have := LExpr.boolsAll_boolVal w row ops hb q hq
      unfold Expr.BoolValI at this; rw [Expr.evalI_ref_of_not_raises hnr] at this; exact this
    cases isAnd
    · simp only [LChain.fill, Expr.Raises]
      rw [Expr.orLift_raises_iff row _ hbv]
      simp [goesOn]
    · simp only [LChain.fill, Expr.Raises]
      rw [Expr.andLift_raises_iff row _ hbv]
      simp [goesOn]
theorem LChain.bindOps_raise (cat : Catalog) (r : Rel) (w : Nat) (isAnd : Bool) :
    ∀ (ops : List LExpr) (g : Option Expr) (s : BindSt) (F : Row → Row) (acc : Option Expr),
      s.Ext RI cat r w F → (∀ c ∈ g, c.refsLt s.width ∧ c.plain = true) →
      (∀ a ∈ acc, a.refsLt s.width ∧ a.plain = true) → LExpr.ScopedAll w ops →
      ∃ L : Row → Prop,
        ((LChain.bindOps w isAnd g s acc ops).1.rel.Raises RP cat ↔
          s.rel.Raises RP cat ∨ ∃ row ∈ r.eval cat RI, L row) ∧
        ∀ row ∈ r.eval cat RI, LExpr.BoolsAll RI w row ops →
          (∀ a ∈ acc, Expr.BoolValI RI (row ++ F row) a) →
          (¬ Reach RI g (row ++ F row) → ¬ L row) ∧
          (Reach RI g (row ++ F row) →
            (L row ↔ raiseFrom w isAnd row (acc.map (·.eval (row ++ F row) RI)) ops))
  | [], g, s, F, acc, hs, _, _, _ => by
    refine ⟨fun _ => False, by simp [LChain.bindOps], fun row _ _ _ => ⟨fun _ h => h, fun _ => ?_⟩⟩
    simp [raiseFrom]
  | x :: xs, g, s, F, acc, hs, hg, ha, ⟨hx, hxs⟩ => by
    have hRL := Profile.reference_logic
    by_cases hpl : x.plain
    · have hb : LChain.bindOps w isAnd g s acc (x :: xs) =
          LChain.bindOps w isAnd g s (some (joinOp isAnd acc (LExpr.fill w x))) xs := by
        simp [LChain.bindOps, hpl]
      rw [hb]
      have hfx := Expr.refsLt_mono _ hs.2.2 (LExpr.fill_refsLt w x hx)
      obtain ⟨L, hR, hL⟩ := LChain.bindOps_raise cat r w isAnd xs g s F
        (some (joinOp isAnd acc (LExpr.fill w x))) hs hg (fun a h => by
          simp only [Option.mem_def, Option.some.injEq] at h; subst h
          exact ⟨joinOp_refsLt (fun a h => (ha a h).1) hfx,
            joinOp_plain (fun a h => (ha a h).2) (LExpr.fill_plain hpl)⟩) hxs
      refine ⟨L, hR, fun row hr ⟨⟨hbx, _⟩, hbxs⟩ hba => ?_⟩
      have hl := hs.2.1 row hr
      have hxe : (LExpr.fill w x).eval (row ++ F row) RI = (LExpr.fill w x).eval row RI :=
        Expr.eval_append (F row) (LExpr.fill_refsLt w x hx) hl.1
      have hba' : ∀ a ∈ some (joinOp isAnd acc (LExpr.fill w x)), Expr.BoolValI RI (row ++ F row) a := by
        intro a h; simp only [Option.mem_def, Option.some.injEq] at h; subst h
        rw [Expr.BoolValI, joinOp_eval hRL]
        cases acc with
        | none => show Expr.BoolValI _ _ _; unfold Expr.BoolValI; rw [hxe]; exact hbx
        | some a => exact comb_boolVal _ _ _
      obtain ⟨h1, h2⟩ := hL row hr hbxs hba'
      refine ⟨h1, fun hreach => (h2 hreach).trans ?_⟩
      have hnr : ¬ (x.fill w).Raises row := by
        simp only [Expr.Raises, Expr.issues_plain row _ (LExpr.fill_plain hpl), firstError]
        decide
      simp only [raiseFrom, hnr, and_false, false_or, Option.map_some, joinOp_eval hRL, hxe]
      cases acc <;> rfl
    · have hb : LChain.bindOps w isAnd g s acc (x :: xs) =
          LChain.bindOps w isAnd g ((LExpr.bind w (reachOf isAnd g acc) s x).1.push
            (joinOp isAnd acc (guardCase (reachOf isAnd g acc) (LExpr.bind w (reachOf isAnd g acc) s x).2))).1
            (some (.field ((LExpr.bind w (reachOf isAnd g acc) s x).1.push
            (joinOp isAnd acc (guardCase (reachOf isAnd g acc) (LExpr.bind w (reachOf isAnd g acc) s x).2))).2)) xs := by
        simp [LChain.bindOps, hpl]
      rw [hb]
      have hreachOk : ∀ c ∈ reachOf isAnd g acc, c.refsLt s.width ∧ c.plain = true := fun c hc =>
        ⟨reachOf_refsLt (fun c h => (hg c h).1) (fun a h => (ha a h).1) c hc,
          reachOf_plain (fun c h => (hg c h).2) (fun a h => (ha a h).2) c hc⟩
      obtain ⟨Lx, hRx, hLx⟩ := LExpr.bind_raise cat r w x (reachOf isAnd g acc) s F hs hreachOk hx
      obtain ⟨F₁, hG₁, hr₁, hv₁⟩ := LExpr.bind_spec hRL cat r w x (reachOf isAnd g acc) s F hs
        (fun c h => (hreachOk c h).1) hx
      generalize hP : LExpr.bind w (reachOf isAnd g acc) s x = P at hRx hLx hG₁ hr₁ hv₁
      have hG₂ := BindSt.push_grows hG₁.1 (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2))
      generalize hQ : P.1.push (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)) = Q at hG₂
      have hQ2 : Q.2 = P.1.width := by rw [← hQ]; rfl
      have hQw : Q.1.width = P.1.width + 1 := by rw [← hQ]; rfl
      have hQr : Q.1.rel = .project P.1.rel [joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)] := by
        rw [← hQ]; rfl
      obtain ⟨Lr, hRr, hLr⟩ := LChain.bindOps_raise cat r w isAnd xs g Q.1 _ (some (.field Q.2)) hG₂.1
        (fun c hc => ⟨Expr.refsLt_mono _ (Nat.le_trans hG₁.2.2 hG₂.2.2) (hg c hc).1, (hg c hc).2⟩)
        (fun a h => by
          simp only [Option.mem_def, Option.some.injEq] at h; subst h
          exact ⟨show Q.2 < Q.1.width by omega, rfl⟩) hxs
      let lev : Row → Prop := fun row =>
        (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)).Raises (row ++ F₁ row)
      refine ⟨fun row => Lx row ∨ lev row ∨ Lr row, ?_, ?_⟩
      · rw [hRr, hQr, Rel.raises_project, hRx, hG₁.1.1]
        simp only [List.mem_map, Expr.raisesOn_reference]
        constructor
        · rintro (((h | ⟨row, hr, h⟩) | ⟨_, ⟨row, hr, rfl⟩, h⟩) | ⟨row, hr, h⟩)
          · exact .inl h
          · exact .inr ⟨row, hr, .inl h⟩
          · exact .inr ⟨row, hr, .inr (.inl h)⟩
          · exact .inr ⟨row, hr, .inr (.inr h)⟩
        · rintro (h | ⟨row, hr, (h | h | h)⟩)
          · exact .inl (.inl (.inl h))
          · exact .inl (.inl (.inr ⟨row, hr, h⟩))
          · exact .inl (.inr ⟨_, ⟨row, hr, rfl⟩, h⟩)
          · exact .inr ⟨row, hr, h⟩
      · intro row hr ⟨⟨hbx, hbx'⟩, hbxs⟩ hba
        have hl := hs.2.1 row hr
        have hl₁ := hG₁.1.2.1 row hr
        have hpre₁ := hG₁.2.1 row
        have hreach₁ : ∀ e : Option Expr, (∀ c ∈ e, c.refsLt s.width) →
            (Reach RI e (row ++ F₁ row) ↔ Reach RI e (row ++ F row)) :=
          fun e he => reach_prefix he (by omega) hpre₁
        have hacc₁ : ∀ a ∈ acc, a.eval (row ++ F₁ row) RI = a.eval (row ++ F row) RI :=
          fun a h => eval_prefix (ha a h).1 (by omega) hpre₁
        have hba₁ : ∀ a ∈ acc, Expr.BoolValI RI (row ++ F₁ row) a := by
          intro a h; unfold Expr.BoolValI; rw [hacc₁ a h]; exact hba a h
        have hRg : ∀ {e : Option Expr} {R : Row}, Reach RI (reachOf isAnd e acc) R → Reach RI e R := by
          intro e R h
          cases acc with
          | none => exact h
          | some a =>
            simp only [reachOf, Reach, Option.mem_def, Option.some.injEq, forall_eq'] at h
            exact ((guardAnd_isTrue hRL e _ R).mp h).1
        have hRreach := fun c h => (hreachOk c h).1
        have hlev : ∀ R, (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)).Raises R ↔
            Reach RI (reachOf isAnd g acc) R ∧ P.2.Raises R :=
          level_raises isAnd (fun a h => (ha a h).2) (fun c h => (hreachOk c h).2) P.2
        -- The column the level appends, at the row's extension.
        let vlev := (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)).eval (row ++ F₁ row) RI
        have hidx : (row ++ F₁ row).length = Q.2 := by rw [hQ2, List.length_append]; omega
        have hfield : (Expr.field Q.2).eval (row ++ (F₁ row ++ [vlev])) RI = vlev := by
          simp only [Expr.eval, ← List.append_assoc]
          exact getD_append_single _ _ _ hidx
        have hpre₂ : F₁ row <+: F₁ row ++ [vlev] := List.prefix_append _ _
        obtain ⟨hLx1, hLx2⟩ := hLx F₁ hG₁.1 row hr hbx'
        refine ⟨fun hn h => ?_, fun hreach => ?_⟩
        · have hnR : ¬ Reach RI (reachOf isAnd g acc) (row ++ F row) := fun h' => hn (hRg h')
          rcases h with h | h | h
          · exact hLx1 hnR h
          · exact hnR ((hreach₁ _ hRreach).mp ((hlev _).mp h).1)
          · obtain ⟨hr1, _⟩ := hLr row hr hbxs (by
              intro a h'; simp only [Option.mem_def, Option.some.injEq] at h'; subst h'
              unfold Expr.BoolValI; rw [hfield]
              show Expr.BoolValI RI _ _
              unfold Expr.BoolValI; rw [joinOp_eval hRL]
              cases acc with
              | none =>
                by_cases hR : Reach RI g (row ++ F₁ row)
                · simp only [reachOf]; rw [guardCase_eval_reach hR]
                  exact absurd ((reach_prefix (fun c h => (hg c h).1) (by omega) hpre₁).mp hR) hn
                · simp only [reachOf]; rw [guardCase_eval_not hR]; exact .inl rfl
              | some a => exact comb_boolVal _ _ _)
            exact hr1 (fun h' => hn ((reach_prefix (fun c h => (hg c h).1) (by omega)
              (hpre₁.trans hpre₂)).mp h')) h
        · have hreachF₁ : Reach RI g (row ++ F₁ row) :=
            (reach_prefix (fun c h => (hg c h).1) (by omega) hpre₁).mpr hreach
          have hvlev : vlev = stepAcc isAnd (acc.map (·.eval (row ++ F row) RI)) ((LExpr.fill w x).eval row RI) := by
            have := level_eval hRL isAnd (g := g) (acc := acc) (u := P.2) (row := row ++ F₁ row)
              (v := (LExpr.fill w x).eval row RI) hreachF₁ hba₁
              (fun hR => hv₁ row hr ((hreach₁ _ hRreach).mp hR) hbx')
            show (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)).eval (row ++ F₁ row) RI = _
            rw [this]
            cases acc with
            | none => rfl
            | some a => simp only [Option.map_some, hacc₁ a rfl]
          have hbv : vlev = .null ∨ ∃ b, vlev = .bool b := by
            rw [hvlev]
            cases acc with
            | none =>
              have := hbx; unfold Expr.BoolValI at this; exact this
            | some a => exact comb_boolVal _ _ _
          obtain ⟨_, hr2⟩ := hLr row hr hbxs (by
            intro a h'; simp only [Option.mem_def, Option.some.injEq] at h'; subst h'
            unfold Expr.BoolValI; rw [hfield]; exact hbv)
          have hreach₂ : Reach RI g (row ++ (F₁ row ++ [vlev])) :=
            (reach_prefix (fun c h => (hg c h).1) (by omega) (hpre₁.trans hpre₂)).mpr hreach
          have hLrIff : Lr row ↔ raiseFrom w isAnd row
              (some (stepAcc isAnd (acc.map (·.eval (row ++ F row) RI)) ((LExpr.fill w x).eval row RI))) xs := by
            rw [hr2 hreach₂, Option.map_some, hfield, hvlev]
          show Lx row ∨ lev row ∨ Lr row ↔ _
          simp only [raiseFrom]
          rw [hLrIff, ← or_assoc]
          refine or_congr ?_ Iff.rfl
          -- The operand runs where the running value lets it.
          have hgo : Reach RI (reachOf isAnd g acc) (row ++ F row) ↔
              accGoes isAnd (acc.map (·.eval (row ++ F row) RI)) := by
            cases acc with
            | none => simp only [reachOf, accGoes, Option.map_none, iff_true]; exact hreach
            | some a => simpa [accGoes] using reachOf_iff hRL (isAnd := isAnd) (hba a rfl) hreach
          rw [← hgo]
          by_cases hR : Reach RI (reachOf isAnd g acc) (row ++ F row)
          · rw [(hLx2 hR)]
            simp only [hR, true_and, show lev row = (joinOp isAnd acc (guardCase (reachOf isAnd g acc) P.2)).Raises
              (row ++ F₁ row) from rfl, hlev, (hreach₁ _ hRreach).mpr hR, true_and]
          · simp only [hR, false_and, iff_false, not_or]
            exact ⟨hLx1 hR, fun h => hR ((hreach₁ _ hRreach).mp ((hlev _).mp h).1)⟩

end


/-- **T1, raises**: under the reference, the filter on the bound condition
raises exactly where the filter on D50's lift raises, where every chain's
operands are TRUE, FALSE or NULL. -/
theorem Rel.guardedFilter_raises (cat : Catalog) (r : Rel) (w : Nat) (x : LExpr)
    (hw : ∀ row ∈ r.eval cat RI, row.length = w) (hx : x.Scoped w)
    (hb : ∀ row ∈ r.eval cat RI, x.Bools RI w row) :
    (r.guardedFilter w x).Raises RP cat ↔ (r.filter (x.fill w)).Raises RP cat := by
  have hs : BindSt.Ext RI cat r w ⟨r, w⟩ (fun _ => []) :=
    ⟨by simp, fun row hr => ⟨hw row hr, by simp⟩, Nat.le_refl w⟩
  obtain ⟨L, hR, hL⟩ := LExpr.bind_raise cat r w x none ⟨r, w⟩ (fun _ => []) hs (by simp) hx
  obtain ⟨F', hG, -, -⟩ := LExpr.bind_spec Profile.reference_logic cat r w x none ⟨r, w⟩ (fun _ => []) hs
    (by simp) hx
  simp only [Rel.guardedFilter, Rel.Raises, hR, hG.1.1, List.mem_map]
  have hrow : ∀ row ∈ r.eval cat RI, ((x.fill w).RaisesOn RP row ↔
      L row ∨ (x.bind w none ⟨r, w⟩).2.RaisesOn RP (row ++ F' row)) := by
    intro row hr
    rw [Expr.raisesOn_reference, Expr.raisesOn_reference]
    exact ((hL F' hG.1 row hr (hb row hr)).2 (by simp [Reach]))
  constructor
  · rintro ((h | ⟨row, hr, h⟩) | ⟨_, ⟨row, hr, rfl⟩, h⟩)
    · exact .inl h
    · exact .inr ⟨row, hr, (hrow row hr).mpr (.inl h)⟩
    · exact .inr ⟨row, hr, (hrow row hr).mpr (.inr h)⟩
  · rintro (h | ⟨row, hr, h⟩)
    · exact .inl (.inl h)
    · rcases (hrow row hr).mp h with h | h
      · exact .inl (.inr ⟨row, hr, h⟩)
      · exact .inr ⟨_, ⟨row, hr, rfl⟩, h⟩


/-- Raising is kept on a longer row by an expression reading below the shorter one's width. -/
theorem raises_prefix {e : Expr} {row F F' : Row} {n : Nat} (he : e.refsLt n)
    (hlen : row.length + F.length = n) (hp : F <+: F') : e.Raises (row ++ F') ↔ e.Raises (row ++ F) := by
  rw [← Expr.raisesOn_reference, ← Expr.raisesOn_reference]
  obtain ⟨G, rfl⟩ := hp
  simp only [Expr.RaisesOn, ← List.append_assoc]
  rw [Expr.evalP_append G he (by simp [hlen])]

/-- `bind_raise` for a list of expressions bound in turn. -/
theorem LExpr.bindList_raise (cat : Catalog) (r : Rel) (w : Nat) :
    ∀ (xs : List LExpr) (s : BindSt) (F : Row → Row), s.Ext RI cat r w F → LExpr.ScopedAll w xs →
      ∃ L : Row → Prop,
        ((LExpr.bindList w s xs).1.rel.Raises RP cat ↔ s.rel.Raises RP cat ∨ ∃ row ∈ r.eval cat RI, L row) ∧
        ∀ F', (LExpr.bindList w s xs).1.Ext RI cat r w F' → ∀ row ∈ r.eval cat RI,
          LExpr.BoolsAll RI w row xs →
          ((∃ x ∈ xs, (x.fill w).Raises row) ↔
            L row ∨ ∃ e ∈ (LExpr.bindList w s xs).2, e.Raises (row ++ F' row))
  | [], s, F, hs, _ => ⟨fun _ => False, by simp [LExpr.bindList], fun _ _ _ _ _ => by simp [LExpr.bindList]⟩
  | x :: xs, s, F, hs, ⟨hx, hxs⟩ => by
    obtain ⟨Lx, hRx, hLx⟩ := LExpr.bind_raise cat r w x none s F hs (by simp) hx
    obtain ⟨F₁, hG₁, hr₁, -⟩ := LExpr.bind_spec Profile.reference_logic cat r w x none s F hs (by simp) hx
    obtain ⟨Lr, hRr, hLr⟩ := LExpr.bindList_raise cat r w xs _ F₁ hG₁.1 hxs
    obtain ⟨F₂, hG₂, -, -⟩ := LExpr.bindList_spec Profile.reference_logic cat r w xs _ F₁ hG₁.1 hxs
    refine ⟨fun row => Lx row ∨ Lr row, ?_, fun F' hF' row hr ⟨⟨_, hbx⟩, hbxs⟩ => ?_⟩
    · simp only [LExpr.bindList]
      rw [hRr, hRx]
      constructor
      · rintro ((h | ⟨row, hr, h⟩) | ⟨row, hr, h⟩)
        · exact .inl h
        · exact .inr ⟨row, hr, .inl h⟩
        · exact .inr ⟨row, hr, .inr h⟩
      · rintro (h | ⟨row, hr, (h | h)⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr ⟨row, hr, h⟩)
        · exact .inr ⟨row, hr, h⟩
    · have hl₁ := hG₁.1.2.1 row hr
      have hF₂ : F₂ row = F' row := BindSt.Ext.unique hG₂.1 hF' row hr
      have hpre : F₁ row <+: F' row := hF₂ ▸ hG₂.2.1 row
      have hx2 := ((hLx F₁ hG₁.1 row hr hbx).2 (by simp [Reach]))
      have hxs2 := hLr F' hF' row hr hbxs
      simp only [LExpr.bindList, List.mem_cons, exists_eq_or_imp]
      rw [hx2, hxs2, raises_prefix hr₁ (by omega) hpre]
      constructor
      · rintro ((h | h) | (h | ⟨e, he, h⟩))
        · exact .inl (.inl h)
        · exact .inr (.inl h)
        · exact .inl (.inr h)
        · exact .inr (.inr ⟨e, he, h⟩)
      · rintro ((h | h) | (h | ⟨e, he, h⟩))
        · exact .inl (.inl h)
        · exact .inr (.inl h)
        · exact .inl (.inr h)
        · exact .inr (.inr ⟨e, he, h⟩)

/-- **T1 for a projection, raises**: under the reference the bound projection
raises exactly where the projection of the lifts raises. -/
theorem Rel.guardedProject_raises (cat : Catalog) (r : Rel) (w : Nat) (xs : List LExpr)
    (hw : ∀ row ∈ r.eval cat RI, row.length = w) (hx : LExpr.ScopedAll w xs)
    (hb : ∀ row ∈ r.eval cat RI, LExpr.BoolsAll RI w row xs) :
    (r.guardedProject w xs).Raises RP cat ↔ (r.project (LExpr.fillAll w xs)).Raises RP cat := by
  have hs : BindSt.Ext RI cat r w ⟨r, w⟩ (fun _ => []) :=
    ⟨by simp, fun row hr => ⟨hw row hr, by simp⟩, Nat.le_refl w⟩
  obtain ⟨L, hR, hL⟩ := LExpr.bindList_raise cat r w xs ⟨r, w⟩ (fun _ => []) hs hx
  obtain ⟨F', hG, -, -⟩ := LExpr.bindList_spec Profile.reference_logic cat r w xs ⟨r, w⟩ (fun _ => []) hs hx
  have hfill : ∀ row, (∃ e ∈ LExpr.fillAll w xs, e.RaisesOn RP row) ↔ ∃ x ∈ xs, (x.fill w).Raises row := by
    intro row
    simp only [Expr.raisesOn_reference]
    constructor
    · rintro ⟨e, he, h⟩
      obtain ⟨x, hx, rfl⟩ := LExpr.mem_fillAll he
      exact ⟨x, hx, h⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨_, LExpr.fill_mem_fillAll hx, h⟩
  simp only [Rel.guardedProject, Rel.Raises, hR, hG.1.1, List.mem_map]
  constructor
  · rintro ((h | ⟨row, hr, h⟩) | ⟨_, ⟨row, hr, rfl⟩, e, he, h⟩)
    · exact .inl h
    · exact .inr ⟨row, hr, (hfill row).mpr ((hL F' hG.1 row hr (hb row hr)).mpr (.inl h))⟩
    · exact .inr ⟨row, hr, (hfill row).mpr ((hL F' hG.1 row hr (hb row hr)).mpr
        (.inr ⟨e, he, (Expr.raisesOn_reference _ _).mp h⟩))⟩
  · rintro (h | ⟨row, hr, h⟩)
    · exact .inl (.inl h)
    · rcases (hL F' hG.1 row hr (hb row hr)).mp ((hfill row).mp h) with h | ⟨e, he, h⟩
      · exact .inl (.inr ⟨row, hr, h⟩)
      · exact .inr ⟨_, ⟨row, hr, rfl⟩, e, he, (Expr.raisesOn_reference _ _).mpr h⟩

end RaiseInv

end Raises

end Substrait
