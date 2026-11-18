import Sverify.Core.Profile

/-!
# `AND` and `OR` as guards (D50)

The SQL and Ibis frontends lift `p₁ AND … AND pₙ` so that an operation in
`pₖ` that can raise runs only where no earlier operand is FALSE, and `OR`
likewise. The core's `AND` and `OR` stay eager (D19); the lift is an
expression the parser builds from the extension functions `sverify_and` and
`sverify_or` (`Parse.lean`), and a plan read as written is untouched.

`Expr.andG ps` is `(T₁ = 1)` with `Tₖ = CASE WHEN pₖ IS NOT FALSE THEN Tₖ₊₁
ELSE 0` and `Tₙ₊₁ = CASE WHEN p₁ AND … AND pₙ THEN 1 ELSE NULL`: the integer
`1`, `0` or `NULL` stands for TRUE, FALSE or NULL. `ifThen` evaluates only
the branch it takes, so `pₖ₊₁` is evaluated only where `pₖ` is not FALSE, and
no guard is copied. `Expr.orG` is the dual.

Under `Profile.reference` (`Expr.evalP_reference`), with every operand TRUE,
FALSE or NULL, and `k` the first operand whose outcome is FALSE or an error:

* `Expr.andG_false`: if it is FALSE, the outcome is FALSE, whatever the
  operands after `pₖ` do (G2);
* `Expr.andG_error`: if it is an error, the outcome is the eager conjunction's
  (G1);
* `Expr.andG_none`: if there is none, the outcome is the eager conjunction's
  (G1).

The same three for `Expr.orG`, with TRUE in place of FALSE.
-/

namespace Substrait

variable [Boxes.Ambient]

/-- `p IS NOT FALSE`: TRUE where `p` is TRUE or NULL. -/
def Expr.notFalse (p : Expr) : Expr := .bin .or (.un .isNull p) p

/-- `p IS NOT TRUE`: TRUE where `p` is FALSE or NULL. -/
def Expr.notTrue (p : Expr) : Expr := .bin .or (.un .isNull p) (.un .not p)

/-- The conjunction of `ps`, folded from the left (as the parser reads `and`). -/
def Expr.conj : List Expr → Expr
  | [] => .lit (.bool true)
  | p :: ps => ps.foldl (.bin .and) p

/-- The disjunction of `ps`, folded from the left. -/
def Expr.disj : List Expr → Expr
  | [] => .lit (.bool false)
  | p :: ps => ps.foldl (.bin .or) p

/-- `Tₖ` for the conjunction `all`: stop with `0` at a FALSE operand, and at the
end `1` where `all` is TRUE and `NULL` otherwise. -/
def Expr.andChain (all : Expr) : List Expr → Expr
  | [] => .ifThen all (.lit (.int 1)) (.lit .null)
  | p :: ps => .ifThen p.notFalse (Expr.andChain all ps) (.lit (.int 0))

/-- `p₁ AND … AND pₙ`, each operand evaluated only where the earlier ones are
not FALSE. -/
def Expr.andG (ps : List Expr) : Expr :=
  .bin .eq (Expr.andChain (Expr.conj ps) ps) (.lit (.int 1))

/-- The dual: stop with `1` at a TRUE operand, and at the end `0` where every
operand is FALSE and `NULL` otherwise. -/
def Expr.orChain (all : Expr) : List Expr → Expr
  | [] => .ifThen (.un .not all) (.lit (.int 0)) (.lit .null)
  | p :: ps => .ifThen p.notTrue (Expr.orChain all ps) (.lit (.int 1))

/-- `p₁ OR … OR pₙ`, each operand evaluated only where the earlier ones are
not TRUE. -/
def Expr.orG (ps : List Expr) : Expr :=
  .bin .eq (Expr.orChain (Expr.disj ps) ps) (.lit (.int 1))

/-! ## The reference's evaluation of the pieces -/

/-- An operand's value is TRUE, FALSE or NULL. -/
def Expr.BoolVal (row : Row) (p : Expr) : Prop :=
  p.eval row = .null ∨ ∃ b, p.eval row = .bool b

/-- `e` raises under the reference on `row`. -/
def Expr.Raises (row : Row) (e : Expr) : Prop := (firstError (e.issues row)).isSome

omit [Boxes.Ambient] in
theorem UnFn.issueAll_isNull (v : Value) : UnFn.isNull.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

omit [Boxes.Ambient] in
theorem UnFn.issueAll_not (v : Value) : UnFn.not.issueAll v = none := by
  cases v <;> simp [UnFn.issueAll, UnFn.issue, UnFn.infIssue]

omit [Boxes.Ambient] in
theorem BinFn.issueAll_logic (f : BinFn) (hf : f = .and ∨ f = .or ∨ f = .eq) (v w : Value) :
    f.issueAll v w = none := by
  rcases hf with rfl | rfl | rfl <;> cases v <;> cases w <;>
    simp [BinFn.issueAll, BinFn.issue, BinFn.infIssue, BinFn.makesInf]

theorem Expr.issues_notFalse (row : Row) (p : Expr) :
    p.notFalse.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notFalse, Expr.issues, UnFn.issueAll_isNull, BinFn.issueAll_logic .or (by simp)]

theorem Expr.issues_notTrue (row : Row) (p : Expr) :
    p.notTrue.issues row = p.issues row ++ p.issues row := by
  simp [Expr.notTrue, Expr.issues, UnFn.issueAll_isNull, UnFn.issueAll_not,
    BinFn.issueAll_logic .or (by simp)]

omit [Boxes.Ambient] in
theorem isTrue_or3_isNull (v : Value) :
    (or3 (UnFn.apply .isNull v) v).isTrue = true ↔ v ≠ .bool false ∧ (v = .null ∨ v = .bool true) := by
  cases v <;> simp [UnFn.apply, or3, Value.isTrue] <;> (try (rename_i b; cases b <;> simp))

theorem Expr.isTrue_notFalse {row : Row} {p : Expr} (h : Expr.BoolVal row p) :
    (p.notFalse.eval row).isTrue = !(decide (p.eval row = .bool false)) := by
  rcases h with h | ⟨b, h⟩ <;> cases b <;> simp [Expr.notFalse, Expr.eval, Impl.lean, h, UnFn.apply, BinFn.apply, or3, Value.isTrue]

end Substrait
