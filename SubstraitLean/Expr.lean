import SubstraitLean.Value

/-!
# Scalar expressions

Models a fragment of Substrait's `Expression` message:

* `Literal`                      → `Expr.lit`
* `FieldReference` (struct field) → `Expr.field`
* `ScalarFunction`               → `Expr.un` / `Expr.bin` (fixed arity)
* `IfThen`                       → `Expr.ifThen`

Boolean connectives use SQL three-valued logic (Kleene logic), which is what
the Substrait standard extensions (`functions_boolean.yaml`) specify.
-/

namespace Substrait

inductive UnFn where
  | not | isNull | neg
  deriving Repr, DecidableEq

inductive BinFn where
  | add | sub | mul | eq | lt | and | or
  deriving Repr, DecidableEq

inductive Expr where
  | lit (v : Value)
  | field (i : Nat)
  | un (f : UnFn) (a : Expr)
  | bin (f : BinFn) (a b : Expr)
  | ifThen (c t e : Expr)
  deriving Repr, DecidableEq

def UnFn.apply : UnFn → Value → Value
  | .not, .bool b => .bool (!b)
  | .isNull, .null => .bool true
  | .isNull, _ => .bool false
  | .neg, .int i => .int (-i)
  | _, _ => .null

/-- Kleene conjunction: `false` dominates, otherwise any `null` gives `null`. -/
def and3 : Value → Value → Value
  | .bool false, _ => .bool false
  | _, .bool false => .bool false
  | .bool true, .bool true => .bool true
  | _, _ => .null

/-- Kleene disjunction: `true` dominates, otherwise any `null` gives `null`. -/
def or3 : Value → Value → Value
  | .bool true, _ => .bool true
  | _, .bool true => .bool true
  | .bool false, .bool false => .bool false
  | _, _ => .null

/-- Arithmetic and comparisons are null-propagating; ill-typed calls yield
`null` (a well-typed plan never reaches those cases). -/
def BinFn.apply : BinFn → Value → Value → Value
  | .and, a, b => and3 a b
  | .or, a, b => or3 a b
  | .add, .int a, .int b => .int (a + b)
  | .sub, .int a, .int b => .int (a - b)
  | .mul, .int a, .int b => .int (a * b)
  | .eq, .int a, .int b => .bool (a == b)
  | .eq, .bool a, .bool b => .bool (a == b)
  | .eq, .str a, .str b => .bool (a == b)
  | .lt, .int a, .int b => .bool (decide (a < b))
  | _, _, _ => .null

/-- Out-of-range field references evaluate to `null`; `Expr.refsLt` rules
them out for well-formed plans. -/
def Expr.eval (row : Row) : Expr → Value
  | .lit v => v
  | .field i => row.getD i .null
  | .un f a => f.apply (a.eval row)
  | .bin f a b => f.apply (a.eval row) (b.eval row)
  | .ifThen c t e => if (c.eval row).isTrue then t.eval row else e.eval row

/-- All field references in the expression are `< n`. -/
def Expr.refsLt (n : Nat) : Expr → Prop
  | .lit _ => True
  | .field i => i < n
  | .un _ a => a.refsLt n
  | .bin _ a b => a.refsLt n ∧ b.refsLt n
  | .ifThen c t e => c.refsLt n ∧ t.refsLt n ∧ e.refsLt n

theorem isTrue_and3 (a b : Value) :
    (and3 a b).isTrue = (a.isTrue && b.isTrue) := by
  unfold and3
  split <;> simp_all [Value.isTrue] <;> split <;> simp_all

/-- An expression that only looks at the first `n` columns ignores whatever
is appended after them. This is the key lemma behind pushdown rewrites. -/
theorem Expr.eval_append {e : Expr} {n : Nat} {row : Row} (extra : Row)
    (he : e.refsLt n) (hlen : row.length = n) :
    e.eval (row ++ extra) = e.eval row := by
  induction e with
  | lit => rfl
  | field i =>
    simp only [refsLt] at he
    simp [eval, List.getD, List.getElem?_append_left (hlen ▸ he)]
  | un f a ih => simp [eval, ih he]
  | bin f a b iha ihb => simp [eval, iha he.1, ihb he.2]
  | ifThen c t e ihc iht ihe => simp [eval, ihc he.1, iht he.2.1, ihe he.2.2]

end Substrait
