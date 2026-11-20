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
/-- `bind` of each chain `body` reads only eagerly, `fill` of the others; the
first is chain `i`, at column `w + i`. -/
def LChain.bindAll (w : Nat) (g : Option Expr) (s : BindSt) (body : Expr) (i : Nat) :
    List LChain → BindSt × List Expr
  | [] => (s, [])
  | c :: cs =>
    let p := if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)
    let q := LChain.bindAll w g p.1 body (i + 1) cs
    (q.1, p.2 :: q.2)
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
      apply Expr.refsLt_subst hbody
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
          (if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)).1 F F₁ ∧
        (if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)).2.refsLt
          (if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)).1.width ∧
        ∀ row ∈ r.eval cat I, Reach I g (row ++ F row) → LChain.Bools I w row c →
          (if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)).2.eval
            (row ++ F₁ row) I = (LChain.fill w c).eval row I := by
      split
      · exact LChain.bind_spec hI cat r w c g s F hs hg hc
      · refine ⟨F, Grows.refl hs, Expr.refsLt_mono _ hs.2.2 (LChain.fill_refsLt w c hc), ?_⟩
        intro row hr _ _
        exact Expr.eval_append (F row) (LChain.fill_refsLt w c hc) (hs.2.1 row hr).1
    generalize hP : (if body.eagerOnly (w + i) then LChain.bind w g s c else (s, LChain.fill w c)) = P at hp
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
    obtain ⟨F', hG, hr, hv⟩ := LChain.bindOps_spec hI cat r w isAnd ops g s F none hs hg (by simp) hops
    refine ⟨F', hG, hr, fun row hrow hreach hb => ?_⟩
    rw [LChain.fill_eval hI w isAnd ops row hb]
    exact hv row hrow hreach hb (by simp)
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
theorem map_range_getD (row X : Row) (w : Nat) (h : row.length = w) :
    (List.range w).map ((row ++ X).getD · .null) = row := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]

/-- **T1, rows**: the filter on the bound condition keeps the rows the filter on
D50's lift keeps, in the same order, where every chain's operands are TRUE,
FALSE or NULL. -/
theorem Rel.bindFilter_eval (hI : I.Logic) (cat : Catalog) (r : Rel) (w : Nat) (x : LExpr)
    (hw : ∀ row ∈ r.eval cat I, row.length = w) (hx : x.Scoped w)
    (hb : ∀ row ∈ r.eval cat I, x.Bools I w row) :
    (r.bindFilter w x).eval cat I = (r.filter (x.fill w)).eval cat I := by
  have hs : BindSt.Ext I cat r w ⟨r, w⟩ (fun _ => []) :=
    ⟨by simp, fun row hr => ⟨hw row hr, by simp⟩, Nat.le_refl w⟩
  obtain ⟨F', hG, _, hv⟩ := LExpr.bind_spec hI cat r w x none ⟨r, w⟩ (fun _ => []) hs (by simp) hx
  simp only [Rel.bindFilter, Rel.eval, hG.1.1, List.filter_map, List.map_map]
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
  exact map_range_getD row (F' row) w (hw row hr')

end Eval


/-! ## T1: the bound plan's raises (T1a, T1b)

Under the reference, the bound filter raises exactly where the filter on
D50's lift does: `Rel.bindFilter_raises`. A level raises only where its reach
holds and its operand raises; the guards and running values are plain
(`Expr.plain`) and raise nowhere. -/

section Raises
variable [Boxes.Ambient]

/-- The outcome of entry `i` of a substitution. -/
abbrev entryP (p : Profile) (σ : List Expr) (i : Nat) (row : Row) : Outcome :=
  (σ.getD i (.lit .null)).evalP p row

/-- Substituting entries with the same outcome gives the same outcome; and
where an entry `t` reads eagerly raises, so does `t` with it substituted:
where the outcomes differ, it is because such an entry raises. -/
theorem Expr.evalP_subst_congr {p : Profile} :
    ∀ (t : Expr) (row row' : Row) (σ σ' : List Expr),
      (∀ i, t.reads i → entryP p σ i row = entryP p σ' i row' ∨
          (t.eagerOnly i ∧ (entryP p σ i row).err?.isSome)) →
      (t.subst σ).evalP p row = (t.subst σ').evalP p row' ∨
        ((t.subst σ).evalP p row).err?.isSome ∧ ∃ i, t.reads i ∧ entryP p σ i row ≠ entryP p σ' i row'
  | .lit _, _, _, _, _, _ => .inl rfl
  | .field i, row, row', σ, σ', h => by
    by_cases hq : entryP p σ i row = entryP p σ' i row'
    · exact .inl hq
    · rcases h i (by simp [Expr.reads]) with h | ⟨_, h⟩
      · exact absurd h hq
      · exact .inr ⟨h, i, by simp [Expr.reads], hq⟩
  | .un f a, row, row', σ, σ', h => by
    rcases Expr.evalP_subst_congr a row row' σ σ' h with h1 | ⟨h1, i, hi, hr⟩
    · left; simp only [Expr.subst, Expr.evalP, h1]
    · right; refine ⟨?_, i, hi, hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases ha : (a.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [ha, Outcome.err?] at h1
  | .bin f a b, row, row', σ, σ', h => by
    have ha := Expr.evalP_subst_congr a row row' σ σ' (fun i hi => (h i (by simp [Expr.reads, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1, hr⟩)
    have hb := Expr.evalP_subst_congr b row row' σ σ' (fun i hi => (h i (by simp [Expr.reads, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.2, hr⟩)
    rcases ha with ha | ⟨ha, i, hi, hr⟩
    · rcases hb with hb | ⟨hb, i, hi, hr⟩
      · left; simp only [Expr.subst, Expr.evalP, ha, hb]
      · right; refine ⟨?_, i, by simp [Expr.reads, hi], hr⟩
        simp only [Expr.subst, Expr.evalP]
        cases hx : (a.subst σ).evalP p row with
        | error k => rfl
        | ok v =>
          simp only [bind, Except.bind]
          cases hy : (b.subst σ).evalP p row with
          | error k => rfl
          | ok y => simp [hy, Outcome.err?] at hb
    · right; refine ⟨?_, i, by simp [Expr.reads, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (a.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at ha
  | .ifThen c t e, row, row', σ, σ', h => by
    have hc := Expr.evalP_subst_congr c row row' σ σ' (fun i hi => (h i (by simp [Expr.reads, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1.1, hr⟩)
    -- A branch reads only entries the `CASE` does not read eagerly: their outcomes agree.
    have heq : ∀ i, (t.reads i ∨ e.reads i) → entryP p σ i row = entryP p σ' i row' := by
      intro i hi
      have hr : (Expr.ifThen c t e).reads i := by
        simp only [Expr.reads, Bool.or_eq_true]; rcases hi with hi | hi
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
    · right; refine ⟨?_, i, by simp [Expr.reads, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (c.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at hc
  | .hof f l b, row, row', σ, σ', h => by
    have hl := Expr.evalP_subst_congr l row row' σ σ' (fun i hi => (h i (by simp [Expr.reads, hi])).imp id
      fun ⟨he, hr⟩ => ⟨by simp only [Expr.eagerOnly, Bool.and_eq_true] at he; exact he.1, hr⟩)
    -- The body reads only entries the lambda does not read eagerly: their outcomes agree.
    have heq : ∀ i, b.reads (i + 1) → entryP p σ i row = entryP p σ' i row' := by
      intro i hi
      rcases h i (by simp [Expr.reads, hi]) with h1 | ⟨he, _⟩
      · exact h1
      · simp [Expr.eagerOnly, hi] at he
    have hbody : ∀ x : Value, (b.subst (.field 0 :: σ.map (·.shift 0))).evalP p (x :: row) =
        (b.subst (.field 0 :: σ'.map (·.shift 0))).evalP p (x :: row') := by
      intro x
      have hent : ∀ j, b.reads j → entryP p (.field 0 :: σ.map (·.shift 0)) j (x :: row) =
          entryP p (.field 0 :: σ'.map (·.shift 0)) j (x :: row') := by
        intro j hj
        cases j with
        | zero => rfl
        | succ i =>
          have h1 := heq i hj
          simp only [entryP, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map] at h1 ⊢
          cases hσ : σ[i]? <;> cases hσ' : σ'[i]? <;>
            simp_all [Expr.evalP_shift_cons, Expr.shift, Expr.evalP]
      rcases Expr.evalP_subst_congr b (x :: row) (x :: row') _ _ (fun j hj => .inl (hent j hj)) with
        k | ⟨_, j, hj, hr⟩
      · exact k
      · exact absurd (hent j hj) hr
    rcases hl with hl | ⟨hl, i, hi, hr⟩
    · left; simp only [Expr.subst, Expr.evalP, hl, hbody]
    · right; refine ⟨?_, i, by simp [Expr.reads, hi], hr⟩
      simp only [Expr.subst, Expr.evalP]
      cases hx : (l.subst σ).evalP p row with
      | error k => rfl
      | ok v => simp [hx, Outcome.err?] at hl

end Raises

end Substrait
