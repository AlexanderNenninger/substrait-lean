import SubstraitLean.Value
import SubstraitLean.Rounding
import SubstraitLean.Text
import SubstraitLean.Time

/-!
# Scalar expressions

Models a fragment of Substrait's `Expression` message:

* `Literal`                      → `Expr.lit`
* `FieldReference` (struct field) → `Expr.field`
* `ScalarFunction`               → `Expr.un` / `Expr.bin` (fixed arity)
* `IfThen`                       → `Expr.ifThen`

Boolean connectives use SQL three-valued logic (Kleene logic), which is what
the Substrait standard extensions (`functions_boolean.yaml`) specify.

Doubles are integer *codes* (see `SubstraitLean/Float.lean`), so they share
`Value.int` and the integer comparisons. Float arithmetic has its own
operators (`fadd`, …), computed with native floats; rounding a double to an
integer is exact (see `SubstraitLean/Rounding.lean`).

Integer division and remainder truncate toward zero, as in DataFusion. Where
DataFusion raises an error (division by zero, a cast out of range, …) the
value here is `null`; `SubstraitLean/Safety.lean` says when that happens.

String functions are in `SubstraitLean/Text.lean` (`UPPER`, `LOWER` and
regular expressions are black boxes there); timestamps are microseconds, and
`date_part`/`date_trunc` are in `SubstraitLean/Time.lean`.
-/

namespace Substrait

inductive UnFn where
  | not | isNull | neg
  /-- Integer to double (`CAST(x AS DOUBLE)`). -/
  | itof
  /-- Negation of a double. -/
  | fneg
  /-- `FLOOR`, `CEIL` and `ROUND` of a double, as a double. -/
  | ffloor | fceil | fround
  /-- `ROUND(x, d)` of a double for `d ≠ 0`, computed with native floats. -/
  | froundTo (d : Int)
  /-- `CAST(x AS BIGINT)` of a double: truncation toward zero. -/
  | ftoi
  /-- `CAST(x AS INT)` of an integer to `bits` bits (32, or 16 for `SMALLINT`
  and 8 for `TINYINT`): the value itself, or `NULL` where it does not fit and
  DataFusion fails (`badCast` in `Safety.lean`). -/
  | narrow (bits : Nat)
  /-- `CAST(x AS VARCHAR)` of an integer. -/
  | itos
  /-- `UPPER`, `LOWER` (black boxes) and `CHARACTER_LENGTH` of a string. -/
  | upper | lower | length
  /-- `array_length(regexp_match(s, p))` for a constant pattern `p` (a black box):
  `NULL` if `p` does not match. -/
  | regexMatch (p : String)
  /-- `date_part(p, ts)`: `NULL` outside the years ±262142. -/
  | datePart (p : Time.DatePart)
  /-- `date_trunc(u, ts)`. -/
  | dateTrunc (u : Time.TimeUnit)
  /-- `CAST(ts AS DATE)`: days since 1970-01-01, rounding down. -/
  | toDate
  deriving Repr, DecidableEq

inductive BinFn where
  | add | sub | mul | eq | lt | and | or
  /-- Double arithmetic, rounded like IEEE 754. -/
  | fadd | fsub | fmul | fdiv
  /-- Integer division and remainder (truncating) and integer powers. -/
  | idiv | imod | ipow
  /-- `POWER` of doubles. -/
  | fpow
  /-- `s || t`, `strpos(s, t)`, `starts_with`, `ends_with` and `s LIKE p`. -/
  | concat | strpos | startsWith | endsWith | like
  /-- `substring(s FROM a [FOR n])` for a constant `n`. -/
  | substr (n : Option Nat)
  /-- `btrim`, `ltrim` and `rtrim` of a string and a set of characters. -/
  | trim (left right : Bool)
  deriving Repr, DecidableEq

inductive Expr where
  | lit (v : Value)
  | field (i : Nat)
  | un (f : UnFn) (a : Expr)
  | bin (f : BinFn) (a b : Expr)
  | ifThen (c t e : Expr)
  deriving Repr, DecidableEq

/-- Does `i` fit in a signed integer of `bits` bits? -/
def fitsBits (bits : Nat) (i : Int) : Bool :=
  decide (-(2 ^ (bits - 1) : Int) ≤ i) && decide (i < 2 ^ (bits - 1))

def UnFn.apply : UnFn → Value → Value
  | .not, .bool b => .bool (!b)
  | .isNull, .null => .bool true
  | .isNull, _ => .bool false
  | .neg, .int i => .int (-i)
  | .itof, .int i => .int (FloatCode.ofInt i)
  | .fneg, .int k => .int (FloatCode.neg k)
  | .ffloor, .int c => .int (FloatCode.floor c)
  | .fceil, .int c => .int (FloatCode.ceil c)
  | .fround, .int c => .int (FloatCode.round c)
  | .froundTo d, .int c => .int (FloatCode.roundTo d c)
  | .ftoi, .int c => match FloatCode.toInt? c with
    | some i => .int i
    | none => .null
  | .narrow n, .int i => if fitsBits n i then .int i else .null
  | .itos, .int i => .str (toString i)
  | .upper, .str s => .str (Text.upper s)
  | .lower, .str s => .str (Text.lower s)
  | .length, .str s => .int s.length
  | .regexMatch p, .str s => match Text.regexMatch s p with
    | some k => .int (k + 1)
    | none => .null
  | .datePart p, .int ts => match Time.datePart p ts with
    | some v => .int v
    | none => .null
  | .dateTrunc u, .int ts => .int (Time.trunc u ts)
  | .toDate, .int ts => .int (Time.days ts)
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
  | .fadd, .int a, .int b => .int (FloatCode.lift₂ (· + ·) a b)
  | .fsub, .int a, .int b => .int (FloatCode.lift₂ (· - ·) a b)
  | .fmul, .int a, .int b => .int (FloatCode.lift₂ (· * ·) a b)
  | .fdiv, .int a, .int b => .int (FloatCode.lift₂ (· / ·) a b)
  | .idiv, .int a, .int b => if b = 0 then .null else .int (a.tdiv b)
  | .imod, .int a, .int b => if b = 0 then .null else .int (a.tmod b)
  -- Exponents beyond 64 overflow anyway (unless `|a| ≤ 1`); don't compute them.
  | .ipow, .int a, .int b =>
    if b < 0 ∨ (64 < b ∧ 1 < a.natAbs) then .null else .int (a ^ b.toNat)
  | .fpow, .int a, .int b => .int (FloatCode.lift₂ Float.pow a b)
  | .concat, .str a, .str b => .str (a ++ b)
  | .strpos, .str a, .str b => .int (Text.strpos a b)
  | .startsWith, .str a, .str b => .bool (Text.startsWith a b)
  | .endsWith, .str a, .str b => .bool (Text.endsWith a b)
  | .like, .str a, .str b => .bool (Text.like a b)
  | .substr n, .str s, .int a => .str (Text.substr s a n)
  | .trim l r, .str s, .str set => .str (Text.trim l r s set)
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

theorem isTrue_or3 (a b : Value) :
    (or3 a b).isTrue = (a.isTrue || b.isTrue) := by
  unfold or3
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
