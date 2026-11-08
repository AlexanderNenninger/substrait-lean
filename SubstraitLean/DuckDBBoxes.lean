import Sverify.Core.BlackBox
import Sverify.Core.Float
import Sverify.Core.Time
import SubstraitLean.VarcharCasts

/-!
# DuckDB's black boxes (#325, #1189)

DuckDB's black-box catalogue, `Boxes.duckdb`: a row per function, its laws,
and the function itself. The core holds only the mechanism
(`core/Sverify/Core/BlackBox.lean`); these rows are DuckDB's, so they live
outside it, with the evaluators Lean has for some of them.

Lean's evaluator computes the black boxes it has an evaluator for
(`evalScalar`: `base64`, `octet_length`, `strlen`, `yearweek`, `list_sum`,
`string_split`, the casts from VARCHAR on a subset, and `signbit` away from
`±0.0` and NaN) and panics at the others, so `substrait-check` refuses to
print rows rather than print wrong ones. The kernel sees none of it: a row's
function is `rawScalar name` (`rawAgg name`), an `opaque` constant, and no
proof depends on it, only on the row's laws (`Boxes.WF`, `Boxes.duckdb_wf`).
The differential tests pin each black box to DuckDB, and the laws are
checked on random data (`python/tests/test_black_box.py`).
-/

namespace Substrait.BlackBox.DuckDB

open Substrait.BlackBox

/-! ## Lean's evaluators -/

def b64Digit (n : Nat) : Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.getD n '='

/-- Bytes in base64, padded with `=` (RFC 4648). -/
def base64Bytes : List UInt8 → List Char
  | [] => []
  | [a] =>
    let n := a.toNat * 65536
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), '=', '=']
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), b64Digit (n / 64 % 64), '=']
  | a :: b :: c :: r =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    [b64Digit (n / 262144), b64Digit (n / 4096 % 64), b64Digit (n / 64 % 64), b64Digit (n % 64)] ++
      base64Bytes r

/-- `base64(encode(s))`. -/
def base64 (s : String) : String := String.ofList (base64Bytes s.toUTF8.toList)

#guard base64 "" == "" && base64 "f" == "Zg==" && base64 "fo" == "Zm8=" && base64 "foo" == "Zm9v"
#guard base64 "foobar" == "Zm9vYmFy" && base64 "é" == "w6k="

def unevaluated {α : Type} [Inhabited α] (name : String) : α :=
  panic! s!"{name} is a black box Lean does not evaluate"

/-- The first day DuckDB's `yearweek` takes, 5877641-01-04 BC: before it, the
start of its ISO year is not a DuckDB date. -/
def yearweekMin : Int := -2147483453

/-- `yearweek(d)` of the day `d`: the ISO year of its Thursday times 100,
plus its ISO week, which DuckDB subtracts in the years up to 0. -/
def yearweek (d : Int) : Value :=
  if d < yearweekMin then .null else
    let y := Time.monthIndex (d - (d + 3) % 7 + 3) / 12
    let w := Time.isoWeek d
    .int (if 0 < y then y * 100 + w else y * 100 - w)

#guard yearweek (-1) == .int 197001 && yearweek 19723 == .int 202401 &&
  yearweek 18628 == .int 202053
#guard yearweek Time.dayMin == .int 101 && yearweek (Time.dayMin - 1) == .int (-52)
#guard yearweek yearweekMin == .int (-587764001) && yearweek (yearweekMin - 1) == .null

/-- The sum of the integers among `vs`; none without any. -/
def listSum (vs : List Value) : Option Int :=
  vs.foldl (fun acc v => match v with
    | .int i => some (acc.getD 0 + i)
    | _ => acc) none

#guard listSum [.int 1, .null, .int 2] == some 3 && listSum [.null] == none && listSum [] == none

/-- The bits of `i` that are 1, in 64-bit two's complement. -/
def bitCount (i : Int) : Nat :=
  ((Nat.toDigits 2 (i % 2 ^ 64).toNat).filter (· == '1')).length

#guard bitCount 7 == 3 && bitCount (-1) == 64 && bitCount 0 == 0 && bitCount (-2 ^ 63) == 1

/-- The pieces of a text between the occurrences of `sep` (not empty), left
to right: `skip` characters of a match still to drop, and `acc` the piece so
far, reversed. -/
def splitChars (sep : List Char) : Nat → List Char → List Char → List String
  | _, [], acc => [String.ofList acc.reverse]
  | k + 1, _ :: r, acc => splitChars sep k r acc
  | 0, c :: r, acc =>
    if sep.isPrefixOf (c :: r) then String.ofList acc.reverse :: splitChars sep (sep.length - 1) r []
    else splitChars sep 0 r (c :: acc)

/-- DuckDB's `string_split(s, sep)`: by characters for `sep = ''`. -/
def stringSplit (s sep : String) : List String :=
  if sep.isEmpty then (if s.isEmpty then [""] else s.toList.map Char.toString)
  else splitChars sep.toList 0 s.toList []

#guard stringSplit "a,,b" "," == ["a", "", "b"] && stringSplit "" "," == [""]
#guard stringSplit "aaa" "aa" == ["", "a"] && stringSplit "ababcab" "abc" == ["ab", "ab"]
#guard stringSplit "a,b," "," == ["a", "b", ""] && stringSplit "" "" == [""]
#guard stringSplit "héllo" "" == ["h", "é", "l", "l", "o"]

/-- A cast from VARCHAR (#806) by its target, the row's name less its prefix. -/
def varcharCast? : String → Option (String → VarcharCasts.Parsed)
  | "bigint" => some VarcharCasts.bigint
  | "double" => some VarcharCasts.double
  | "boolean" => some VarcharCasts.boolean
  | "date" => some VarcharCasts.date
  | "timestamp" => some VarcharCasts.timestamp
  | _ => none

/-- A cast from VARCHAR's row: its parser, and whether it is `TRY_CAST`. -/
def varcharRow? (name : String) : Option ((String → VarcharCasts.Parsed) × Bool) :=
  if name.startsWith "try_varchar_" then (varcharCast? (name.drop 12).toString).map (·, true)
  else if name.startsWith "varchar_" then (varcharCast? (name.drop 8).toString).map (·, false)
  else none

/-- The scalar black boxes Lean evaluates. -/
def evalScalar : String → List Value → Value
  | "base64", [.str s] => .str (base64 s)
  | "octet_length", [.str s] | "strlen", [.str s] => .int s.utf8ByteSize
  -- The sign of `±0.0` and of NaN is not in their codes.
  | "signbit", [.float c] =>
    if c == 0 || c == FloatCode.nan then unevaluated "signbit at ±0.0 or NaN" else .bool (c < 0)
  | "yearweek", [.date d] => yearweek d
  | "bit_count", [.int i] => .int (bitCount i)
  | "list_sum", [.list vs] => match listSum vs with
    | some n => .int n
    | none => .null
  | "string_split", [.str s, .str sep] => .list ((stringSplit s sep).map .str)
  | "string_split", [.str s, .null] => .list [.str s]
  | "string_split", [.null, _] => .null
  | name, [.str s] => match varcharRow? name with
    | some (parse, _) => match parse s with
      | .val v => v
      -- NULL for `TRY_CAST`; `CAST` raises there (`evalRaises`).
      | .bad => .null
      | .unknown => unevaluated s!"{name} of {s.quote}"
    | none => unevaluated name
  | name, _ => unevaluated name

def evalAgg (name : String) (_ : List Value) : Value := unevaluated name

def evalAggRaises (name : String) (_ : List Value) : Bool := unevaluated name

def evalRaises : String → List Value → Bool
  | "list_sum", [.list vs] => match listSum vs with
    | some n => !(decide (-2 ^ 63 ≤ n) && decide (n < 2 ^ 63))
    | none => false
  | name, [.str s] => match varcharRow? name with
    | some (parse, false) => match parse s with
      | .val _ => false
      | .bad => true
      | .unknown => unevaluated s!"{name} of {s.quote}"
    | _ => unevaluated name
  | name, _ => unevaluated name

/-! ## The functions, opaque to the kernel -/

/-- The scalar black box `name` of the arguments: the kernel knows nothing of it. -/
@[implemented_by evalScalar] opaque rawScalar : String → List Value → Value

/-- The aggregate black box `name` of the values (non-NULL, at least one, in
the order the engine takes them). -/
@[implemented_by evalAgg] opaque rawAgg : String → List Value → Value

/-- Does the aggregate black box `name` raise on these values (non-NULL, at
least one)? -/
@[implemented_by evalAggRaises] opaque rawAggRaises : String → List Value → Bool

/-- Does the scalar black box `name` raise on these (non-NULL) arguments? -/
@[implemented_by evalRaises] opaque rawRaises : String → List Value → Bool

/-- A row with its function and its raising, by its name. -/
def fn (f : Scalar) : Scalar := { f with eval := rawScalar f.name, raises? := rawRaises f.name }

def agg (f : Aggregate) : Aggregate :=
  { f with eval := rawAgg f.name, raises? := rawAggRaises f.name }

/-! ## The table

A row per function; `fn` and `agg` give each its function. The
`add-function` skill says what else a new row needs: its lift rule and its
SQL, both from the row's name. -/

/-- The code of `1.0` (`core/Sverify/Core/Float.lean`): `2 · 2¹⁰⁷⁴ + 1`. -/
def codeOne : Int := 2 * 2 ^ 1074 + 1

#guard codeOne == FloatCode.ofFloat 1.0 && -codeOne == FloatCode.ofFloat (-1.0)

/-- The scalar black boxes. -/
def scalarRows : List Scalar := [
  -- `base64(encode(s))`: the UTF-8 bytes of `s` in base64 (DuckDB's `base64`
  -- takes a BLOB). Not NULL for a string.
  { name := "base64", args := [.str], result := .str, laws := [.nonNull], sample := .str "" },
  -- `printf(fmt, x)` and `format(fmt, x)` of one value (#328): C's and
  -- Python's format strings. Strict, and raise on a format that does not fit
  -- the value (`printf('%d', 'x')`, `format('{} {}', 1)`). DuckDB formats a
  -- signed integer as a BIGINT whatever its width, so `x` is an `atom`.
  { name := "printf", args := [.str, .atom], result := .str, raises := .sometimes,
    laws := [.nonNull], sample := .str "" },
  { name := "format", args := [.str, .atom], result := .str, raises := .sometimes,
    laws := [.nonNull], sample := .str "" },
  -- `octet_length(encode(s))` and `strlen(s)`: the number of UTF-8 bytes of
  -- `s` (#328). Lean evaluates them.
  { name := "octet_length", args := [.str], result := .int, laws := [.nonNull, .atLeast 0],
    sample := .int 0 },
  { name := "strlen", args := [.str], result := .int, laws := [.nonNull, .atLeast 0],
    sample := .int 0 },
  -- `signbit(x)`: the sign bit of a double (#328), TRUE for `-0.0` and a
  -- negative NaN, which the model's codes do not tell from `+0.0` and NaN
  -- (`core/Sverify/Core/Float.lean`). Lean evaluates it elsewhere.
  { name := "signbit", args := [.double], result := .bool, laws := [.nonNull],
    sample := .bool false },
  -- `yearweek(d)`: the ISO year times 100 plus the ISO week, the week
  -- subtracted in the years up to 0 (`duckdb-yearweek`). NULL for an
  -- infinite date, and before 5877641-01-04 BC (`yearweekMin`), where DuckDB
  -- raises, as `date_part` is NULL outside chrono's dates. The bounds are
  -- those of DuckDB's dates, to 5881580 AD. Lean evaluates it.
  { name := "yearweek", args := [.date], result := .int,
    laws := [.atLeast (-587764053), .atMost 588158053], sample := .int 0 },
  -- The vector functions of lists of doubles (#327). Each raises where a
  -- list holds a NULL or the two differ in length. `list_cosine_similarity`
  -- is NULL for empty lists, NaN where a list is zero or holds NaN or an
  -- infinity, and else in [-1, 1] (`duckdb-list-vectors`): at least `-1.0`,
  -- as NaN is above every number. `array_*` are the same functions.
  { name := "list_cosine_similarity", args := [.doubles, .doubles], result := .double,
    raises := .sometimes, laws := [.atLeast (-codeOne)], sample := .float 0 },
  -- `1 - list_cosine_similarity`: in [0, 2], NaN or NULL likewise.
  { name := "list_cosine_distance", args := [.doubles, .doubles], result := .double,
    raises := .sometimes, laws := [.atLeast 0], sample := .float 0 },
  -- The Euclidean distance: `0.0` for empty lists, so not NULL.
  { name := "list_distance", args := [.doubles, .doubles], result := .double,
    raises := .sometimes, laws := [.nonNull, .atLeast 0], sample := .float 0 },
  { name := "list_inner_product", args := [.doubles, .doubles], result := .double,
    raises := .sometimes, laws := [.nonNull], sample := .float 0 },
  { name := "list_negative_inner_product", args := [.doubles, .doubles], result := .double,
    raises := .sometimes, laws := [.nonNull], sample := .float 0 },
  -- Of lists of length 3; it raises on others.
  { name := "array_cross_product", args := [.doubles, .doubles], result := .doubles,
    raises := .sometimes, laws := [.nonNull], sample := .list [] },
  -- `bit_count(x)` of a BIGINT: the number of its 64 bits that are 1, in
  -- two's complement (#326). DuckDB counts the bits of the argument's own
  -- width, so the lift takes BIGINTs only. Lean evaluates it.
  { name := "bit_count", args := [.int], result := .int,
    laws := [.nonNull, .atLeast 0, .atMost 64], sample := .int 0 },
  -- `list_sum(l)` of integers: the sum of the values, NULLs skipped, NULL
  -- without any (#327). DuckDB's is a HUGEINT; the model's a BIGINT, which
  -- raises past its range, as `SUM`. Lean evaluates it.
  { name := "list_sum", args := [.ints], result := .int, raises := .sometimes,
    sample := .int 0 },
  -- `string_split(s, sep)`: the pieces of `s` between the occurrences of
  -- `sep`, found left to right without overlapping; its characters (code
  -- points) for `sep = ''`, and `['']` for `s = ''` (#808). NULL for a NULL
  -- `s`, and `[s]` for a NULL `sep`, so not strict. Lean evaluates it.
  { name := "string_split", args := [.str, .str], result := .strs, strict := false,
    laws := [.nonNull], sample := .list [.str ""] },
  -- `CAST(s AS t)` and `TRY_CAST(s AS t)` of a string (#806), DuckDB's rules
  -- (`duckdb-cast-varchar`): spaces around, signs, fractions and exponents
  -- (a BIGINT rounds half away from zero), `inf` and `nan`, `true`/`t`/`yes`/
  -- `y`/`1`, ISO dates and times. `CAST` raises on a string DuckDB rejects,
  -- so it is not NULL for a string; `TRY_CAST` is NULL there. Lean evaluates
  -- a subset (`core/Sverify/Core/VarcharCasts.lean`).
  { name := "varchar_bigint", args := [.str], result := .int, raises := .sometimes,
    laws := [.nonNull], sample := .int 0 },
  { name := "try_varchar_bigint", args := [.str], result := .int, sample := .int 0 },
  { name := "varchar_double", args := [.str], result := .double, raises := .sometimes,
    laws := [.nonNull], sample := .float 0 },
  { name := "try_varchar_double", args := [.str], result := .double, sample := .float 0 },
  { name := "varchar_boolean", args := [.str], result := .bool, raises := .sometimes,
    laws := [.nonNull], sample := .bool false },
  { name := "try_varchar_boolean", args := [.str], result := .bool, sample := .bool false },
  { name := "varchar_date", args := [.str], result := .date, raises := .sometimes,
    laws := [.nonNull], sample := .date 0 },
  { name := "try_varchar_date", args := [.str], result := .date, sample := .date 0 },
  { name := "varchar_timestamp", args := [.str], result := .timestamp, raises := .sometimes,
    laws := [.nonNull], sample := .ts 0 },
  { name := "try_varchar_timestamp", args := [.str], result := .timestamp, sample := .ts 0 }]

/-- The aggregate black boxes. -/
def aggregateRows : List Aggregate := [
  -- `entropy(x)`: the Shannon entropy, in bits, of the counts of the
  -- distinct values; `0.0` without values. A double at least `+0.0`.
  { name := "entropy", arg := .any, result := .double, empty := .float 0,
    laws := [.nonNull, .atLeast 0], sample := .float 0 },
  -- The statistical aggregates of doubles (#326); the parser converts
  -- integers to doubles, as DuckDB does. NULL without values.
  -- `product(x)`: the product, in DuckDB's order.
  { name := "product", arg := .double, result := .double, laws := [.nonNull], sample := .float 0 },
  -- `kahan_sum(x)` (also `fsum`, `sumkahan`) and `favg(x)`: Kahan's
  -- compensated sum and its mean (`duckdb-kahan-sum`).
  { name := "kahan_sum", arg := .double, result := .double, laws := [.nonNull], sample := .float 0 },
  { name := "favg", arg := .double, result := .double, laws := [.nonNull], sample := .float 0 },
  -- `sem(x)`: the standard error of the mean, `0.0` for one value.
  { name := "sem", arg := .double, result := .double, laws := [.nonNull, .atLeast 0],
    sample := .float 0 },
  -- `mad(x)`: the median of the absolute deviations from the median.
  { name := "mad", arg := .double, result := .double, laws := [.nonNull, .atLeast 0],
    sample := .float 0 },
  -- `kurtosis(x)` (of a sample, NULL for fewer than 4 values),
  -- `kurtosis_pop(x)` (NULL for fewer than 2 values) and `skewness(x)` (for
  -- fewer than 3), both NULL also for equal ones. They raise where a moment is out of range: on an infinity
  -- or NaN, or a value whose fourth (third, for `skewness`) power
  -- overflows, from about `1e77` (`duckdb-moments`).
  { name := "kurtosis", arg := .double, result := .double, raises := .sometimes,
    sample := .float 0 },
  { name := "kurtosis_pop", arg := .double, result := .double, raises := .sometimes,
    sample := .float 0 },
  { name := "skewness", arg := .double, result := .double, raises := .sometimes,
    sample := .float 0 }]

end DuckDB

/-- **DuckDB's black-box catalogue.** -/
def _root_.Substrait.Boxes.duckdb : Boxes where
  scalars := DuckDB.scalarRows.map DuckDB.fn
  aggregates := DuckDB.aggregateRows.map DuckDB.agg

/-- Each name once, a scalar's or an aggregate's. -/
example : Boxes.duckdb.names.Nodup := nodup_of_nodupB (by decide +kernel)

/-- **DuckDB's catalogue is well-formed**: each row's sample keeps its laws. -/
theorem _root_.Substrait.Boxes.duckdb_wf : Boxes.duckdb.WF :=
  Boxes.wf_of_check (by decide +kernel)

/-! ## The evaluators keep the laws

The clamp (`Scalar.call`) gives the sample where an evaluator breaks its
row's laws, so a wrong evaluator would go unseen there. These samples catch
it: for each row Lean evaluates, arguments and what DuckDB returns for them
(the guards above, and `python/tests/test_black_box.py` on random data). Each
must be the evaluator's value, unclamped, and keep the row's laws. -/

/-- Arguments of a row Lean evaluates, and DuckDB's result. -/
def evaluated : List (String × List Value × Value) := [
  ("base64", [.str "foo"], .str "Zm9v"), ("base64", [.str ""], .str ""),
  ("octet_length", [.str "é"], .int 2), ("strlen", [.str "abc"], .int 3),
  ("signbit", [.float (-DuckDB.codeOne)], .bool true), ("signbit", [.float DuckDB.codeOne], .bool false),
  ("yearweek", [.date 19723], .int 202401), ("yearweek", [.date Time.dayMin], .int 101),
  ("bit_count", [.int (-1)], .int 64), ("bit_count", [.int 7], .int 3),
  ("list_sum", [.list [.int 1, .null, .int 2]], .int 3), ("list_sum", [.list [.null]], .null),
  ("string_split", [.str "a,,b", .str ","], .list [.str "a", .str "", .str "b"]),
  ("string_split", [.str "ab", .null], .list [.str "ab"]),
  ("varchar_bigint", [.str " 42 "], .int 42), ("try_varchar_bigint", [.str "x"], .null),
  ("varchar_boolean", [.str "yes"], .bool true), ("try_varchar_date", [.str "x"], .null)]

#guard evaluated.all fun (n, args, out) =>
  DuckDB.evalScalar n args == out &&
    (DuckDB.scalarRows.find? (·.name == n)).any fun f => ok f.result f.laws (!args.contains .null) out

-- A catalogue joined with itself is refused: each name once (`Boxes.combine`).
#guard (Boxes.combine [Boxes.duckdb]).toBool && !(Boxes.combine [Boxes.duckdb, Boxes.duckdb]).toBool

/-! ## The examples' laws, as theorems -/

/-- `base64` of a string is a string. -/
theorem base64_str (s : String) : ∃ t, callScalar .duckdb "base64" [.str s] = .str t := by
  have hf : Boxes.duckdb.scalar? "base64" = some (Boxes.duckdb.scalars.head (by decide)) := rfl
  have h := Scalar.call_ok_of_wf Boxes.duckdb_wf (scalar?_mem hf) [.str s]
  simp only [callScalar, hf]
  generalize Scalar.call _ _ = v at h
  cases v <;> simp_all [ok, Ty.has, Law.holds, Boxes.duckdb, DuckDB.scalarRows, DuckDB.fn]

/-- `entropy` over values is a double at least `+0.0`. -/
theorem entropy_nonneg {vs : List Value} (hne : vs ≠ []) :
    ∃ c, callAgg .duckdb "entropy" vs = .float c ∧ 0 ≤ c := by
  have hf : Boxes.duckdb.aggregate? "entropy" = some (Boxes.duckdb.aggregates.head (by decide)) :=
    rfl
  have h := Aggregate.call_ok_of_wf Boxes.duckdb_wf (aggregate?_mem hf) hne
  simp only [callAgg, hf]
  generalize Aggregate.call _ _ = v at h
  cases v <;> simp_all [ok, Ty.has, Law.holds, Boxes.duckdb, DuckDB.aggregateRows, DuckDB.agg]

end Substrait.BlackBox

namespace Substrait.DuckDB

/-- **DuckDB's black-box catalogue in scope**, for the files that state
DuckDB's theorems or run its plans: `open scoped Substrait.DuckDB`. Scoped, so
no import brings it into scope (#1189). -/
scoped instance boxes : Boxes.Ambient := ⟨Boxes.duckdb, Boxes.duckdb_wf⟩

end Substrait.DuckDB
