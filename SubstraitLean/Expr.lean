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
  /-- `DECIMAL(p, s)` (#27). A decimal is its unscaled integer (`12.34` at scale
  2 is `1234`), so this is the value itself: it gives the expression its kind,
  and a value of more than `p` digits is an overflow (`Safety.lean`). -/
  | decimal (p s : Nat)
  /-- `DECIMAL(p, s)` without the check, where the value cannot have more
  digits: an average has no more than the values it averages (#27). -/
  | dkind (p s : Nat)
  /-- A decimal brought to a scale `k` digits smaller: divided by `10ᵏ`,
  rounding half away from zero (`roundDiv10`). -/
  | dround (k : Nat)
  /-- A decimal to an integer: divided by `10ᵏ`, truncating toward zero. -/
  | dtrunc (k : Nat)
  /-- A double to a decimal of scale `s` (`FloatCode.toDecimal?`); `NULL` for
  NaN and ±∞, where the cast fails (`Safety.lean`). -/
  | ftod (s : Nat)
  /-- A decimal of scale `s` to a double, correctly rounded (`FloatCode.ofDecimal`). -/
  | dtof (s : Nat)
  /-- Field `i` of a struct (Substrait's `StructField` reference segment). A
  struct is the list of its fields (`docs/nested-values.md`); a NULL struct
  has NULL fields. -/
  | structField (i : Nat)
  /-- Element `off` of a list (Substrait's `ListElement` reference segment):
  zero-based, a negative offset counting from the end (`-1` is the last
  element), `NULL` out of range in either direction, without wrapping
  (`Value.listElement`, #94). -/
  | listElement (off : Int)
  /-- `cardinality(l)`: the number of elements, NULL ones included
  (`functions_list.yaml`). -/
  | cardinality
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
  /-- Decimal arithmetic on unscaled integers (#27), exact. Engines compute it
  in 128 bits, so unlike `add`, `sub` and `mul` it does not wrap at 64;
  `UnFn.decimal` checks the precision. -/
  | dadd | dsub | dmul
  /-- `a / b` of decimals, rounded half away from zero (`roundDivInt?`), and
  `NULL` for `b = 0`: a decimal `AVG`'s sum by its count (#27). -/
  | ddiv
  deriving Repr, DecidableEq

/-- Substrait's higher-order functions on lists (`functions_list.yaml`), which
take a lambda (#94). -/
inductive HoFn where
  /-- `any_match`: the predicate's results ORed in Kleene logic. -/
  | anyMatch
  /-- `all_match`: the predicate's results ANDed in Kleene logic. -/
  | allMatch
  /-- `transform`: the function applied to every element. -/
  | transform
  /-- `filter`: the elements the predicate is `TRUE` for. -/
  | filter
  deriving Repr, DecidableEq

inductive Expr where
  | lit (v : Value)
  | field (i : Nat)
  | un (f : UnFn) (a : Expr)
  | bin (f : BinFn) (a b : Expr)
  | ifThen (c t e : Expr)
  /-- `f(l, x -> body)`: a higher-order function of the list `l`, with a
  *closed* lambda. Its body reads only the lambda's parameter, as field 0,
  so it is evaluated on the one-field row `[x]` and analysed as an expression
  of its own; reading the row's columns or an outer lambda's parameter is
  left for later (#94). -/
  | hof (f : HoFn) (l body : Expr)
  deriving Repr, DecidableEq

/-- Does `i` fit in a signed integer of `bits` bits? -/
def fitsBits (bits : Nat) (i : Int) : Bool :=
  decide (-(2 ^ (bits - 1) : Int) ≤ i) && decide (i < 2 ^ (bits - 1))

/-- Does `i` fit in `p` decimal digits (`|i| < 10ᵖ`)? -/
def fitsDigits (p : Nat) (i : Int) : Bool :=
  decide (-(10 ^ p : Int) < i) && decide (i < 10 ^ p)

/-- `i / 10ᵏ`, rounded half away from zero: a decimal brought to a scale `k`
digits smaller (#27). -/
def roundDiv10 (k : Nat) (i : Int) : Int :=
  let q : Int := ((i.natAbs + 10 ^ k / 2) / 10 ^ k : Nat)
  if i < 0 then -q else q

#guard roundDiv10 1 1235 == 124 && roundDiv10 1 (-5) == -1 && roundDiv10 2 250 == 3
#guard roundDiv10 2 (-250) == -3 && roundDiv10 1 1234 == 123 && roundDiv10 0 (-7) == -7

/-- `a / b` rounded half away from zero, `none` for `b = 0`: a decimal
average (#27). -/
def roundDivInt? (a b : Int) : Option Int :=
  if b = 0 then none else
    let q : Int := ((2 * a.natAbs + b.natAbs) / (2 * b.natAbs) : Nat)
    some (if (a < 0) = (b < 0) then q else -q)

#guard roundDivInt? 20000 3 == some 6667 && roundDivInt? (-20000) 3 == some (-6667)
#guard roundDivInt? 5 2 == some 3 && roundDivInt? (-5) 2 == some (-3) && roundDivInt? 4 2 == some 2
#guard roundDivInt? 1 0 == none && roundDivInt? 0 7 == some 0

/-- Element `off` of `vs`: zero-based, from the end for a negative `off`,
`NULL` out of range (Substrait's `ListElement`). -/
def Value.listElement (off : Int) (vs : List Value) : Value :=
  let k := if off < 0 then vs.length + off else off
  if 0 ≤ k then vs.getD k.toNat .null else .null

#guard Value.listElement 1 [.int 1, .int 2, .int 3] == .int 2
#guard Value.listElement (-1) [.int 1, .int 2, .int 3] == .int 3
#guard Value.listElement 3 [.int 1, .int 2, .int 3] == .null
#guard Value.listElement (-4) [.int 1, .int 2, .int 3] == .null
#guard Value.listElement 0 [] == .null

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
  | .decimal _ _, v => v
  | .dkind _ _, v => v
  | .dround k, .int i => .int (roundDiv10 k i)
  | .dtrunc k, .int i => .int (i.tdiv (10 ^ k))
  | .ftod s, .int c => match FloatCode.toDecimal? c s with
    | some m => .int m
    | none => .null
  | .dtof s, .int i => .int (FloatCode.ofDecimal i s)
  | .structField i, .list vs => vs.getD i .null
  | .listElement off, .list vs => Value.listElement off vs
  | .cardinality, .list vs => .int vs.length
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

/-- A higher-order function of a list value, with the lambda `p`: `NULL` for
anything but a list (`functions_list.yaml`). -/
def HoFn.apply (f : HoFn) (v : Value) (p : Value → Value) : Value :=
  match f, v with
  | .anyMatch, .list vs => vs.foldr (fun x acc => or3 (p x) acc) (.bool false)
  | .allMatch, .list vs => vs.foldr (fun x acc => and3 (p x) acc) (.bool true)
  | .transform, .list vs => .list (vs.map p)
  | .filter, .list vs => .list (vs.filter fun x => (p x).isTrue)
  | _, _ => .null

/-- The elements of a list value; none of anything else. -/
def Value.elems : Value → List Value
  | .list vs => vs
  | _ => []

/-- A higher-order function only applies its lambda to the list's elements. -/
theorem HoFn.apply_congr (f : HoFn) (v : Value) {p q : Value → Value}
    (h : ∀ x ∈ v.elems, p x = q x) : f.apply v p = f.apply v q := by
  cases v <;> cases f <;> simp only [HoFn.apply]
  case list.anyMatch vs | list.allMatch vs =>
    simp only [Value.elems] at h
    induction vs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldr_cons, h x (by simp),
        ih fun y hy => h y (List.mem_cons_of_mem x hy)]
  case list.transform vs =>
    simp only [Value.elems] at h
    exact congrArg Value.list (List.map_congr_left h)
  case list.filter vs =>
    simp only [Value.elems] at h
    congr 1
    exact List.filter_congr fun x hx => by rw [h x hx]

-- `any_match`: `TRUE` if some element matches, else `NULL` if some
-- predicate is `NULL`, else `FALSE`; `FALSE` for `[]`.
#guard HoFn.anyMatch.apply (.list [.int 1, .null]) (fun x => if x == .int 1 then .bool true else if x == .null then .null else .bool false) == .bool true
#guard HoFn.anyMatch.apply (.list [.int 2, .null]) (fun x => if x == .null then .null else .bool false) == .null
#guard HoFn.anyMatch.apply (.list []) (fun _ => .bool true) == .bool false
#guard HoFn.allMatch.apply (.list []) (fun _ => .bool false) == .bool true
#guard HoFn.anyMatch.apply .null (fun _ => .bool true) == .null

mutual
/-- `x < y` of two values, three-valued (`none` is `NULL`): integers (and
the codes of doubles and times) by value, strings by code point, `FALSE <
TRUE`, and lists lexicographically (`Value.listLt3`). -/
def Value.lt3 : Value → Value → Option Bool
  | .int a, .int b => some (decide (a < b))
  | .str a, .str b => some (decide (a < b))
  | .bool a, .bool b => some (!a && b)
  | .list as, .list bs => Value.listLt3 as bs
  | _, _ => none

/-- Lists element by element (#207): the first position where the elements
differ decides, and a proper prefix sorts first. Two `NULL`s at a position
are equal, as in list equality; a `NULL` against a value decides nothing,
so the result is `NULL` (`[1, NULL] < [2]` is TRUE, `[1, NULL] < [1, 3]` is
NULL). -/
def Value.listLt3 : List Value → List Value → Option Bool
  | [], [] => some false
  | [], _ :: _ => some true
  | _ :: _, [] => some false
  | x :: xs, y :: ys =>
    match x, y with
    | .null, .null => Value.listLt3 xs ys
    | .null, _ | _, .null => none
    | x, y => if x = y then Value.listLt3 xs ys else Value.lt3 x y
end

#guard Value.listLt3 [.int 1, .null] [.int 2] == some true
#guard Value.listLt3 [.int 1, .null] [.int 1, .int 3] == none
#guard Value.listLt3 [.null, .int 1] [.null, .int 2] == some true
#guard Value.listLt3 [.int 1] [.int 1, .int 2] == some true
#guard Value.listLt3 [.int 1, .int 2] [.int 1, .int 2] == some false
#guard Value.listLt3 [.list [.int 1, .int 2]] [.list [.int 1, .int 3]] == some true

/-- A three-valued answer as a value. -/
def Value.ofLt3 : Option Bool → Value
  | some r => .bool r
  | none => .null

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
  -- Lexicographically, element by element (#207).
  | .lt, .list a, .list b => Value.ofLt3 (Value.listLt3 a b)
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
  | .dadd, .int a, .int b => .int (a + b)
  | .dsub, .int a, .int b => .int (a - b)
  | .dmul, .int a, .int b => .int (a * b)
  | .ddiv, .int a, .int b => match roundDivInt? a b with
    | some r => .int r
    | none => .null
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
  | .hof f l b => f.apply (l.eval row) fun x => b.eval [x]

/-- All field references in the expression are `< n`. A lambda's body is
evaluated on its parameter alone, so its references are not the row's. -/
def Expr.refsLt (n : Nat) : Expr → Prop
  | .lit _ => True
  | .field i => i < n
  | .un _ a => a.refsLt n
  | .bin _ a b => a.refsLt n ∧ b.refsLt n
  | .ifThen c t e => c.refsLt n ∧ t.refsLt n ∧ e.refsLt n
  | .hof _ l _ => l.refsLt n

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
  | hof f l b ihl _ => simp [eval, ihl he]

end Substrait
