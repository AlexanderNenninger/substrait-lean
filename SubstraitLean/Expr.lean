import SubstraitLean.Value
import SubstraitLean.Rounding
import SubstraitLean.Text
import SubstraitLean.Time
import SubstraitLean.Numeric

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
an operation raises an error (division by zero, a cast out of range, a domain
error, …) the value here is `null`; `SubstraitLean/Safety.lean` says when
that happens.

String functions are in `SubstraitLean/Text.lean` (`UPPER`, `LOWER` and
regular expressions are black boxes there); timestamps are microseconds and dates
days; `date_part`, `date_trunc` and month arithmetic are in
`SubstraitLean/Time.lean`. Elementary functions of doubles and bitwise
operations are in `SubstraitLean/Numeric.lean`.
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
  /-- Integer arithmetic at `bits` bits (`INT`, `SMALLINT`, `TINYINT`): the
  value itself, like 64-bit arithmetic, which DataFusion wraps around where it
  does not fit (`wraps` in `Safety.lean`). -/
  | wrap (bits : Nat)
  /-- `CAST(x AS VARCHAR)` of an integer. -/
  | itos
  /-- `UPPER`, `LOWER` (black boxes) and `CHARACTER_LENGTH` of a string. -/
  | upper | lower | length
  /-- `reverse(s)` and `ascii(s)` (the first code point, `0` for `''`). -/
  | reverse | ascii
  /-- `replace(s, p, r)` for a constant pattern `p` and replacement `r`. -/
  | replace (p r : String)
  /-- `array_length(regexp_match(s, p))` for a constant pattern `p` (a black box):
  `NULL` if `p` does not match. -/
  | regexMatch (p : String)
  /-- `date_part(p, ts)`: `NULL` outside the years ±262142. -/
  | datePart (p : Time.DatePart)
  /-- `date_trunc(u, ts)`. -/
  | dateTrunc (u : Time.TimeUnit)
  /-- `CAST(ts AS DATE)`: days since 1970-01-01, rounding down. -/
  | toDate
  /-- `date_part(p, d)` of a DATE (days): the part of its midnight. -/
  | dayPart (p : Time.DatePart)
  /-- `date_trunc(u, d)` of a DATE, as a DATE. -/
  | dayTrunc (u : Time.TimeUnit)
  /-- `x + INTERVAL 'm' MONTH` of a DATE, or of a timestamp (`time`): the same
  day of the month, clamped to the month's end (`Time.addMonths`). -/
  | addMonths (m : Int) (time : Bool)
  /-- `CAST(ts AS TIME)`: the time of day, in microseconds since midnight. -/
  | timeOfDay
  /-- `CAST(n AS TIMESTAMP)` of microseconds since 1970-01-01: the same number. -/
  | asTime
  /-- `strftime(ts, fmt)` for a format `Time.parseFormat` accepts. -/
  | strftime (fmt : String)
  /-- `date_bin(INTERVAL k, ts, origin)`: the start of `ts`'s `k`-microsecond
  bucket (`Time.bucket`). -/
  | bucket (k : Nat) (origin : Int)
  /-- `sqrt`, `ln`, `sin`, … of a double: `NULL` outside its domain. -/
  | fmath (f : FMath)
  deriving Repr, DecidableEq

inductive BinFn where
  | add | sub | mul | eq | lt | and | or
  /-- Double arithmetic, rounded like IEEE 754. -/
  | fadd | fsub | fmul | fdiv
  /-- The remainder of doubles, C's `fmod` (`FloatCode.fmod`); by zero, an
  error (`Safety.lean`). -/
  | fmod
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
  /-- `repeat(s, n)`: `''` where DataFusion fails (`Text.repeatFits`). -/
  | strRepeat
  /-- `s ILIKE p` (a black box) and `levenshtein(s, t)`. -/
  | ilike | levenshtein
  /-- `d + n` days of a DATE (`d + INTERVAL 'n' DAY`). -/
  | dateAdd
  /-- `d - e` of DATEs, in days. -/
  | dateDiff
  /-- `atan2(y, x)` and `logb(x, b)` of doubles: `NULL` outside their domain. -/
  | fatan2 | flogb
  /-- `&`, `|`, `^` and the shifts of integers (`BitOp`). -/
  | bit (op : BitOp)
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
  | .wrap _, v => v
  | .itos, .int i => .str (toString i)
  | .upper, .str s => .str (Text.upper s)
  | .lower, .str s => .str (Text.lower s)
  | .length, .str s => .int s.length
  | .reverse, .str s => .str (Text.reverse s)
  | .ascii, .str s => .int (Text.ascii s)
  | .replace p r, .str s => .str (Text.replace s p r)
  | .regexMatch p, .str s => match Text.regexMatch s p with
    | some k => .int (k + 1)
    | none => .null
  | .datePart p, .int ts => match Time.datePart p ts with
    | some v => .int v
    | none => .null
  | .dateTrunc u, .int ts => .int (Time.trunc u ts)
  | .toDate, .int ts => .int (Time.days ts)
  | .dayPart p, .int d => match Time.datePartDay p d with
    | some v => .int v
    | none => .null
  | .dayTrunc u, .int d => .int (Time.truncDay u d)
  | .addMonths m false, .int d => .int (Time.addMonths m d)
  | .addMonths m true, .int ts => .int (Time.addMonthsUs m ts)
  | .timeOfDay, .int ts => .int (Time.timeOfDay ts)
  | .asTime, .int n => .int n
  | .strftime fmt, .int ts => .str (Time.strftime fmt ts)
  | .bucket k o, .int ts => .int (Time.bucket k o ts)
  | .fmath f, .int c => match f.apply c with
    | some r => .int r
    | none => .null
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
  -- Lists are equal element by element, NULL elements equal (DataFusion, DuckDB).
  | .eq, .list a, .list b => .bool (decide (a = b))
  | .lt, .int a, .int b => .bool (decide (a < b))
  -- Strings by code point, which is UTF-8 byte order (as `Value.le`).
  | .lt, .str a, .str b => .bool (decide (a < b))
  -- FALSE < TRUE, as in DataFusion.
  | .lt, .bool a, .bool b => .bool (!a && b)
  | .fadd, .int a, .int b => .int (FloatCode.lift₂ (· + ·) a b)
  | .fsub, .int a, .int b => .int (FloatCode.lift₂ (· - ·) a b)
  | .fmul, .int a, .int b => .int (FloatCode.lift₂ (· * ·) a b)
  | .fdiv, .int a, .int b => .int (FloatCode.lift₂ (· / ·) a b)
  | .fmod, .int a, .int b => .int (FloatCode.fmod a b)
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
  | .strRepeat, .str s, .int n => .str (if Text.repeatFits s n then Text.repeatStr s n else "")
  | .ilike, .str a, .str b => .bool (Text.ilike a b)
  | .levenshtein, .str a, .str b => .int (Text.levenshtein a b)
  | .dateAdd, .int d, .int n => .int (d + n)
  | .dateDiff, .int d, .int e => .int (d - e)
  | .fatan2, .int y, .int x => match atan2? y x with
    | some r => .int r
    | none => .null
  | .flogb, .int x, .int b => match logb? x b with
    | some r => .int r
    | none => .null
  | .bit op, .int a, .int b => match op.apply a b with
    | some r => .int r
    | none => .null
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
