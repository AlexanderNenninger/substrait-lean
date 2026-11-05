import Lean.Data.Json
import SubstraitLean.Aggregate
import SubstraitLean.Reflect

/-!
# The function tables

One table per area (#544 wave 3, the first step of #269): for each of the
model's function constructors, its Substrait name, its anchor, its group
(`docs/core-semantics.md`, "Function groups") and how the parser reads it.
`Parse.lean`, `Write.lean` and `Pretty.lean` read these rows instead of
repeating the mapping; `substrait-check --functions` prints them as JSON for
the Python mirror's agreement test (D1).

A row is one constructor, so a name has one row per type it is modelled at:
`add` is `BinFn.add` on integers (`int.arith`), `fadd` on doubles
(`fp.arith`), `dadd` on decimals (`dec.arith`) and `dateAdd` on dates
(`time.arith`), all with anchor 4. A constructor with parameters has one row
for the parameters its anchor depends on (`trim true false` is `ltrim`) and
stands for all the others by `Ctor.key`. A row without a constructor is a
name the parser and the writer handle by an arm of their own (`abs`,
`median`, the window functions).

A new function goes at the end of its area's table, with the next free
anchor of that area's range. The checks at the end reject a name with two
anchors, an anchor with two names, a constructor with two rows, an anchor
outside its area's range and a group the design does not list. -/

namespace Substrait.Functions

/-- A function constructor of the model. -/
inductive Ctor where
  | un (f : UnFn) | bin (f : BinFn) | agg (f : AggFn) | hof (f : HoFn)
  deriving Repr, DecidableEq

/-- How the parser reads a call of the row's name. -/
inductive Reads where
  /-- `name(a)` or `name(a, b)`, by the arity of the constructor, is the row's
  constructor, in the area's `mk…Call?` (integers and everything that is not
  a double). -/
  | plain
  /-- The same, of doubles (`Parse.mkFloatCall`). -/
  | float
  /-- An arm of its own: a rewrite, constant arguments, a variadic call, a
  measure or a window function. -/
  | own
  deriving Repr, DecidableEq

structure FnRow where
  /-- Substrait's name (sverify's own start with `sverify_`). -/
  name : String
  /-- The anchor `Write.lean` declares it with. -/
  anchor : Nat
  /-- Its group in `docs/core-semantics.md`: the options it takes. -/
  group : String
  /-- The constructor, with `Ctor.key`'s parameters where it has some. -/
  ctor : Option Ctor := none
  reads : Reads := .own
  /-- How `Pretty.lean` renders the constructor, where it has no parameters
  (`""` for a constructor whose rendering shows them). -/
  pretty : String := ""
  deriving Repr, DecidableEq

/-- The constructor of the row that stands for `c`: the parameters an anchor
does not depend on, set to fixed values. -/
def Ctor.key : Ctor → Ctor
  | .un f => .un <| match f with
    | .froundTo _ => .froundTo 0
    | .replace _ _ => .replace "" ""
    | .regexExtract _ _ => .regexExtract "" 0
    | .regexReplace _ _ _ => .regexReplace "" "" false
    | .datePart _ => .datePart .year
    | .dayPart _ => .dayPart .year
    | .dateTrunc _ => .dateTrunc .year
    | .dayTrunc _ => .dayTrunc .year
    | .addMonths _ _ => .addMonths 0 false
    | .strftime _ => .strftime ""
    | .bucket _ _ => .bucket 0 0
    | .raise _ => .raise ""
    | f => f
  | .bin f => .bin <| match f with
    | .substr _ _ => .substr none true
    | .trim false _ => .trim false true
    | f => f
  | .agg f => .agg <| match f with
    -- The parser gives only `and`, `or` and `xor`; the writer writes the
    -- shifts as `bit_xor`.
    | .bit .shl | .bit .shr => .bit .xor
    | .concat _ => .concat ""
    | .quantile cont _ _ => .quantile cont 0 0
    | f => f
  | c => c

/-! ## The tables, area by area -/

/-- Logic, comparison and arithmetic: new anchors 100–199. -/
def core : List FnRow := [
  { name := "not", anchor := 1, group := "cmp", ctor := some (.un .not), reads := .plain,
    pretty := "NOT" },
  { name := "is_null", anchor := 2, group := "cmp", ctor := some (.un .isNull), reads := .plain,
    pretty := "IS_NULL" },
  { name := "negate", anchor := 3, group := "int.arith", ctor := some (.un .neg), reads := .plain,
    pretty := "-" },
  { name := "negate", anchor := 3, group := "fp.neg", ctor := some (.un .fneg), pretty := "-." },
  { name := "add", anchor := 4, group := "int.arith", ctor := some (.bin .add), reads := .plain,
    pretty := "+" },
  { name := "add", anchor := 4, group := "fp.arith", ctor := some (.bin .fadd), reads := .float,
    pretty := "+." },
  { name := "add", anchor := 4, group := "dec.arith", ctor := some (.bin .dadd), pretty := "+" },
  { name := "subtract", anchor := 5, group := "int.arith", ctor := some (.bin .sub),
    reads := .plain, pretty := "-" },
  { name := "subtract", anchor := 5, group := "fp.arith", ctor := some (.bin .fsub),
    reads := .float, pretty := "-." },
  { name := "subtract", anchor := 5, group := "dec.arith", ctor := some (.bin .dsub),
    pretty := "-" },
  { name := "multiply", anchor := 6, group := "int.arith", ctor := some (.bin .mul),
    reads := .plain, pretty := "*" },
  { name := "multiply", anchor := 6, group := "fp.arith", ctor := some (.bin .fmul),
    reads := .float, pretty := "*." },
  { name := "multiply", anchor := 6, group := "dec.arith", ctor := some (.bin .dmul),
    pretty := "*" },
  { name := "equal", anchor := 7, group := "cmp", ctor := some (.bin .eq), reads := .plain,
    pretty := "=" },
  { name := "lt", anchor := 8, group := "cmp", ctor := some (.bin .lt), reads := .plain,
    pretty := "<" },
  { name := "and", anchor := 9, group := "cmp", ctor := some (.bin .and), pretty := "AND" },
  { name := "or", anchor := 10, group := "cmp", ctor := some (.bin .or), pretty := "OR" },
  { name := "divide", anchor := 11, group := "int.div", ctor := some (.bin .idiv),
    reads := .plain, pretty := "/" },
  { name := "divide", anchor := 11, group := "fp.div", ctor := some (.bin .fdiv),
    reads := .float, pretty := "/." },
  { name := "divide", anchor := 11, group := "dec.div", ctor := some (.bin .ddiv),
    pretty := "/ROUND" },
  { name := "floor", anchor := 15, group := "fp.floor", ctor := some (.un .ffloor),
    reads := .float, pretty := "FLOOR" },
  { name := "ceil", anchor := 16, group := "fp.floor", ctor := some (.un .fceil), reads := .float,
    pretty := "CEIL" },
  { name := "round", anchor := 17, group := "fp.round", ctor := some (.un .fround),
    reads := .float, pretty := "ROUND" },
  { name := "round", anchor := 17, group := "fp.round", ctor := some (.un (.froundTo 0)) },
  { name := "modulus", anchor := 18, group := "int.mod", ctor := some (.bin .imod),
    reads := .plain, pretty := "%" },
  { name := "power", anchor := 19, group := "int.pow", ctor := some (.bin .ipow),
    reads := .plain, pretty := "^" },
  { name := "power", anchor := 19, group := "fp.elem", ctor := some (.bin .fpow), reads := .float,
    pretty := "^." },
  { name := "nanvl", anchor := 41, group := "cmp" },
  { name := "sqrt", anchor := 100, group := "fp.elem", ctor := some (.un (.fmath .sqrt)),
    reads := .float, pretty := "SQRT" },
  { name := "exp", anchor := 101, group := "fp.elem", ctor := some (.un (.fmath .exp)),
    reads := .float, pretty := "EXP" },
  { name := "ln", anchor := 102, group := "fp.log", ctor := some (.un (.fmath .ln)),
    reads := .float, pretty := "LN" },
  { name := "log10", anchor := 103, group := "fp.log", ctor := some (.un (.fmath .log10)),
    reads := .float, pretty := "LOG10" },
  { name := "log2", anchor := 104, group := "fp.log", ctor := some (.un (.fmath .log2)),
    reads := .float, pretty := "LOG2" },
  { name := "sin", anchor := 105, group := "fp.elem", ctor := some (.un (.fmath .sin)),
    reads := .float, pretty := "SIN" },
  { name := "cos", anchor := 106, group := "fp.elem", ctor := some (.un (.fmath .cos)),
    reads := .float, pretty := "COS" },
  { name := "tan", anchor := 107, group := "fp.elem", ctor := some (.un (.fmath .tan)),
    reads := .float, pretty := "TAN" },
  { name := "asin", anchor := 108, group := "fp.elem", ctor := some (.un (.fmath .asin)),
    reads := .float, pretty := "ASIN" },
  { name := "acos", anchor := 109, group := "fp.elem", ctor := some (.un (.fmath .acos)),
    reads := .float, pretty := "ACOS" },
  { name := "atan", anchor := 110, group := "fp.elem", ctor := some (.un (.fmath .atan)),
    reads := .float, pretty := "ATAN" },
  { name := "atan2", anchor := 111, group := "fp.elem", ctor := some (.bin .fatan2),
    reads := .float, pretty := "ATAN2" },
  { name := "logb", anchor := 112, group := "fp.log", ctor := some (.bin .flogb), reads := .float,
    pretty := "LOGB" },
  { name := "bitwise_and", anchor := 113, group := "int.bit", ctor := some (.bin (.bit .and)),
    reads := .plain, pretty := "&" },
  { name := "bitwise_or", anchor := 114, group := "int.bit", ctor := some (.bin (.bit .or)),
    reads := .plain, pretty := "|" },
  { name := "bitwise_xor", anchor := 115, group := "int.bit", ctor := some (.bin (.bit .xor)),
    reads := .plain, pretty := "^|" },
  { name := "bitwise_shift_left", anchor := 116, group := "int.shift",
    ctor := some (.bin (.bit .shl)), reads := .plain, pretty := "<<" },
  { name := "bitwise_shift_right", anchor := 117, group := "int.shift",
    ctor := some (.bin (.bit .shr)), reads := .plain, pretty := ">>" },
  -- sverify's own: a shim's guards (#185), which the SQL printers write as
  -- `error(…)` and `x IS NOT NULL`.
  { name := "sverify_raise", anchor := 118, group := "sverify", ctor := some (.un (.raise "")) },
  { name := "sverify_is_number", anchor := 119, group := "sverify", ctor := some (.un .isNum),
    reads := .plain, pretty := "IS_NUMBER" },
  -- sverify's own: a decimal divided by an integer, rounded half away from
  -- zero (a decimal `AVG` over a window, #27).
  { name := "sverify_decimal_div", anchor := 120, group := "dec.div" },
  -- `abs` of a decimal (`Parse.decimalCall`), #27; of an integer, the parser
  -- reads it as a division by `-1`.
  { name := "abs", anchor := 121, group := "dec.arith" },
  { name := "abs", anchor := 121, group := "int.abs" },
  -- sverify's own: the remainder of doubles, C's `fmod` (#256). Substrait's
  -- `modulus` has no double impl; the parser reads `modulus` of doubles so.
  { name := "sverify_fmod", anchor := 122, group := "fp.mod", ctor := some (.bin .fmod),
    pretty := "%." },
  -- sverify's own: two values as the argument of a two-argument aggregate
  -- (`COVAR_SAMP(x, y)`, #54), written as the measure's two arguments.
  { name := "sverify_pair", anchor := 123, group := "sverify", ctor := some (.bin .pair),
    reads := .plain, pretty := "PAIR" },
  -- `GREATEST`/`LEAST` of two values, skipping `NULL`s (`BinFn.greatest`,
  -- #340): untyped, as DataFusion writes its own and the parser reads them;
  -- Substrait's typed ones propagate `NULL`s.
  { name := "greatest", anchor := 124, group := "cmp", ctor := some (.bin .greatest),
    pretty := "GREATEST" },
  { name := "least", anchor := 125, group := "cmp", ctor := some (.bin .least),
    pretty := "LEAST" }]

/-- Strings: new anchors 200–299. -/
def strings : List FnRow := [
  { name := "upper", anchor := 20, group := "str.case", ctor := some (.un .upper),
    reads := .plain, pretty := "UPPER" },
  { name := "lower", anchor := 21, group := "str.case", ctor := some (.un .lower),
    reads := .plain, pretty := "LOWER" },
  { name := "character_length", anchor := 22, group := "str.plain", ctor := some (.un .length),
    reads := .plain, pretty := "LENGTH" },
  { name := "regexp_match", anchor := 23, group := "str.opaque" },
  { name := "str_concat", anchor := 27, group := "str.concat", ctor := some (.bin .concat),
    reads := .plain, pretty := "||" },
  { name := "strpos", anchor := 28, group := "str.match", ctor := some (.bin .strpos),
    reads := .plain, pretty := "STRPOS" },
  { name := "starts_with", anchor := 29, group := "str.match", ctor := some (.bin .startsWith),
    reads := .plain, pretty := "STARTS_WITH" },
  { name := "ends_with", anchor := 30, group := "str.match", ctor := some (.bin .endsWith),
    reads := .plain, pretty := "ENDS_WITH" },
  { name := "like", anchor := 31, group := "str.match", ctor := some (.bin .like),
    reads := .plain, pretty := "LIKE" },
  { name := "substring", anchor := 32, group := "str.sub", ctor := some (.bin (.substr none true)) },
  { name := "btrim", anchor := 33, group := "str.plain", ctor := some (.bin (.trim true true)),
    reads := .plain, pretty := "BTRIM" },
  { name := "ltrim", anchor := 34, group := "str.plain", ctor := some (.bin (.trim true false)),
    reads := .plain, pretty := "LTRIM" },
  { name := "rtrim", anchor := 35, group := "str.plain", ctor := some (.bin (.trim false true)),
    reads := .plain, pretty := "RTRIM" },
  { name := "reverse", anchor := 200, group := "str.plain", ctor := some (.un .reverse),
    reads := .plain, pretty := "REVERSE" },
  { name := "ascii", anchor := 201, group := "str.plain", ctor := some (.un .ascii),
    reads := .plain, pretty := "ASCII" },
  { name := "replace", anchor := 202, group := "str.match", ctor := some (.un (.replace "" "")) },
  { name := "repeat", anchor := 203, group := "str.plain", ctor := some (.bin .strRepeat),
    reads := .plain, pretty := "REPEAT" },
  { name := "ilike", anchor := 204, group := "str.opaque", ctor := some (.bin .ilike),
    reads := .plain, pretty := "ILIKE" },
  { name := "levenshtein", anchor := 205, group := "str.plain", ctor := some (.bin .levenshtein),
    reads := .plain, pretty := "LEVENSHTEIN" },
  -- Regular expressions with a constant pattern, and digests (#50).
  { name := "regexp_extract", anchor := 206, group := "str.opaque",
    ctor := some (.un (.regexExtract "" 0)) },
  { name := "regexp_replace", anchor := 207, group := "str.opaque",
    ctor := some (.un (.regexReplace "" "" false)) },
  { name := "md5", anchor := 208, group := "str.opaque", ctor := some (.un .md5), reads := .plain,
    pretty := "MD5" },
  { name := "sha256", anchor := 209, group := "str.opaque", ctor := some (.un .sha256),
    reads := .plain, pretty := "SHA256" }]

/-- Dates and times: new anchors 300–399. -/
def temporal : List FnRow := [
  -- Days added to a date, and months to a date or timestamp.
  { name := "add", anchor := 4, group := "time.arith", ctor := some (.bin .dateAdd),
    pretty := "+ DAYS" },
  { name := "add", anchor := 4, group := "time.arith", ctor := some (.un (.addMonths 0 false)) },
  { name := "date_part", anchor := 25, group := "time.part", ctor := some (.un (.datePart .year)) },
  { name := "date_part", anchor := 25, group := "time.part", ctor := some (.un (.dayPart .year)) },
  { name := "date_trunc", anchor := 26, group := "time.part",
    ctor := some (.un (.dateTrunc .year)) },
  { name := "date_trunc", anchor := 26, group := "time.part",
    ctor := some (.un (.dayTrunc .year)) },
  -- sverify's own: the days from `e` to `d`.
  { name := "date_diff", anchor := 60, group := "time.arith", ctor := some (.bin .dateDiff),
    reads := .plain, pretty := "- DATE" },
  { name := "strftime", anchor := 61, group := "time.part", ctor := some (.un (.strftime "")) },
  { name := "date_bin", anchor := 62, group := "time.arith", ctor := some (.un (.bucket 0 0)) }]

/-- Lists and structs: new anchors 400–499. -/
def nested : List FnRow := [
  { name := "array_length", anchor := 24, group := "list.plain" },
  -- sverify's own: `lt` of two lists (`Value.listLt3`), which the parser
  -- reads back as `lt`. Engines order lists with NULL elements their own
  -- way, so each needs to know a comparison is of lists (#207).
  { name := "list_lt", anchor := 400, group := "list.order" },
  { name := "cardinality", anchor := 401, group := "list.plain", ctor := some (.un .cardinality),
    reads := .plain, pretty := "CARDINALITY" },
  { name := "any_match", anchor := 402, group := "list.plain", ctor := some (.hof .anyMatch),
    pretty := "ANY_MATCH" },
  { name := "all_match", anchor := 403, group := "list.plain", ctor := some (.hof .allMatch),
    pretty := "ALL_MATCH" },
  { name := "transform", anchor := 404, group := "list.plain", ctor := some (.hof .transform),
    pretty := "TRANSFORM" },
  { name := "filter", anchor := 405, group := "list.plain", ctor := some (.hof .filter),
    pretty := "FILTER" }]

/-- Aggregate functions: new anchors 500–599. -/
def aggregates : List FnRow := [
  { name := "count", anchor := 36, group := "agg.plain", ctor := some (.agg .count),
    pretty := "COUNT" },
  { name := "sum", anchor := 37, group := "agg.isum", ctor := some (.agg .sum), pretty := "SUM" },
  { name := "sum", anchor := 37, group := "agg.fsum", ctor := some (.agg .fsum), pretty := "SUM" },
  { name := "avg", anchor := 38, group := "agg.fsum", ctor := some (.agg .avg), pretty := "AVG" },
  { name := "avg", anchor := 38, group := "agg.isum", ctor := some (.agg .iavg), pretty := "AVG" },
  { name := "min", anchor := 39, group := "agg.order", ctor := some (.agg .min), pretty := "MIN" },
  { name := "max", anchor := 40, group := "agg.order", ctor := some (.agg .max), pretty := "MAX" },
  { name := "array_agg", anchor := 42, group := "agg.seq", ctor := some (.agg .collect),
    pretty := "ARRAY_AGG" },
  -- 64-bit integers folded with a bit operation (#53).
  { name := "bit_and", anchor := 500, group := "agg.plain", ctor := some (.agg (.bit .and)) },
  { name := "bit_or", anchor := 501, group := "agg.plain", ctor := some (.agg (.bit .or)) },
  { name := "bit_xor", anchor := 502, group := "agg.plain", ctor := some (.agg (.bit .xor)) },
  -- The variance and standard deviation of doubles, each engine's own algorithm (#54).
  { name := "variance", anchor := 503, group := "agg.var", ctor := some (.agg (.var true false)),
    pretty := "VAR_SAMP" },
  { name := "variance", anchor := 503, group := "agg.var", ctor := some (.agg (.var false false)),
    pretty := "VAR_POP" },
  { name := "std_dev", anchor := 504, group := "agg.var", ctor := some (.agg (.var true true)),
    pretty := "STDDEV_SAMP" },
  { name := "std_dev", anchor := 504, group := "agg.var", ctor := some (.agg (.var false true)),
    pretty := "STDDEV_POP" },
  -- The first and last value in the measure's sort order (#55).
  { name := "first", anchor := 505, group := "agg.pick", ctor := some (.agg (.pick false)),
    pretty := "FIRST" },
  { name := "last", anchor := 506, group := "agg.pick", ctor := some (.agg (.pick true)),
    pretty := "LAST" },
  -- The covariance and correlation of pairs of doubles (#54).
  { name := "covar_samp", anchor := 507, group := "agg.stat", ctor := some (.agg (.cov true)),
    pretty := "COVAR_SAMP" },
  { name := "covar_pop", anchor := 508, group := "agg.stat", ctor := some (.agg (.cov false)),
    pretty := "COVAR_POP" },
  { name := "corr", anchor := 509, group := "agg.stat", ctor := some (.agg .corr), pretty := "CORR" },
  -- Strings joined in the measure's sort order (#55).
  { name := "string_agg", anchor := 510, group := "agg.seq", ctor := some (.agg (.concat "")) },
  -- Exact quantiles and the mode (#53). `median` is `quantile_cont(x, 0.5)`,
  -- and `arg_min(x, y)` is `first(x ORDER BY y)` over the rows where neither
  -- is NULL; the parser reads them so, and they are written so.
  { name := "median", anchor := 511, group := "agg.quant" },
  { name := "quantile_cont", anchor := 512, group := "agg.quant",
    ctor := some (.agg (.quantile true 0 0)) },
  { name := "quantile_disc", anchor := 513, group := "agg.order",
    ctor := some (.agg (.quantile false 0 0)) },
  { name := "mode", anchor := 514, group := "agg.pick", ctor := some (.agg .mode), pretty := "MODE" },
  { name := "arg_min", anchor := 515, group := "agg.pick" },
  { name := "arg_max", anchor := 516, group := "agg.pick" }]

/-- Window functions: new anchors 600–699. Their constructors (`WinFn`) carry
columns and frames, so the parser and the writer handle each by an arm of its
own. -/
def windows : List FnRow := [
  { name := "row_number", anchor := 12, group := "win.rank" },
  { name := "lag", anchor := 13, group := "win.value" },
  { name := "lead", anchor := 14, group := "win.value" },
  { name := "rank", anchor := 70, group := "win.rank" },
  { name := "dense_rank", anchor := 71, group := "win.rank" },
  { name := "percent_rank", anchor := 72, group := "win.rank" },
  { name := "cume_dist", anchor := 73, group := "win.rank" },
  { name := "ntile", anchor := 74, group := "win.ntile" },
  { name := "first_value", anchor := 75, group := "win.value" },
  { name := "last_value", anchor := 76, group := "win.value" },
  { name := "nth_value", anchor := 77, group := "win.value" }]

/-- Each area's name, rows and the range its new anchors come from. Black
boxes (#325, anchors 700–799) have a table of their own,
`SubstraitLean/BlackBox.lean`. -/
def areas : List (String × List FnRow × Nat) :=
  [("core", core, 100), ("strings", strings, 200), ("temporal", temporal, 300),
   ("nested", nested, 400), ("aggregates", aggregates, 500), ("windows", windows, 600)]

def all : List FnRow := areas.flatMap (·.2.1)

/-- The groups of `docs/core-semantics.md` that have functions here, with
the options each takes. -/
def groups : List (String × List String) := [
  ("int.arith", ["overflow"]), ("int.pow", ["overflow", "on_domain_error"]),
  ("int.abs", ["overflow"]),
  ("int.div", ["overflow", "on_division_by_zero", "on_domain_error", "division_type"]),
  ("int.mod", ["overflow", "on_division_by_zero", "division_type", "min_mod_neg_one"]),
  ("int.bit", []), ("int.shift", ["shift_range"]),
  ("dec.arith", ["overflow", "decimal_rescale"]), ("dec.div", []),
  ("fp.arith", ["rounding", "nan_creation", "zero_sign", "float_overflow"]),
  ("fp.neg", ["zero_sign"]),
  ("fp.div", ["rounding", "on_division_by_zero", "on_domain_error", "nan_creation", "zero_sign",
    "float_overflow"]),
  ("fp.mod", ["division_type", "on_division_by_zero", "nan_creation", "zero_sign"]),
  ("fp.elem", ["rounding", "on_domain_error"]),
  ("fp.log", ["rounding", "on_domain_error", "on_log_zero"]),
  ("fp.round", ["rounding"]), ("fp.floor", []),
  ("cmp", ["nan_equality", "nan_order", "zero_sign"]), ("sverify", []),
  ("str.sub", ["negative_start", "substring_range", "string_positions"]),
  ("str.match", ["case_sensitivity", "string_positions"]),
  ("str.case", ["char_set"]), ("str.concat", ["null_handling"]), ("str.plain", []),
  ("str.opaque", []),
  ("time.arith", ["date_range", "time_interval_months"]), ("time.part", []),
  ("list.order", ["list_null_order"]), ("list.plain", []),
  ("agg.isum", ["overflow", "avg_int_result", "empty_group_aggregates"]),
  ("agg.fsum", ["sum_order", "rounding", "nan_creation", "empty_group_aggregates", "float_overflow"]),
  ("agg.var", ["distribution", "rounding", "stat_algo", "stat_degenerate"]),
  ("agg.stat", ["stat_algo", "stat_degenerate"]),
  ("agg.order", ["nan_order", "zero_sign", "list_null_order"]),
  ("agg.quant", ["quantile_interp", "nan_order"]), ("agg.pick", ["tie_pick"]),
  ("agg.seq", ["tie_order"]), ("agg.plain", []),
  ("win.rank", ["tie_order"]), ("win.ntile", ["ntile_spread", "tie_order"]),
  ("win.value", ["tie_order"])]

/-! ## Lookups -/

/-- The row of a constructor. -/
def rowOf (c : Ctor) : Option FnRow := all.find? (·.ctor == some c.key)

/-- The anchor a constructor is written with; 0 for one without a row (casts,
references, the arithmetic of `wrap` and `fit`, decimals' rescaling). -/
def anchorOf (c : Ctor) : Nat := ((rowOf c).map (·.anchor)).getD 0

/-- The anchor of a name (0 for a name without a row). -/
def anchorNamed (name : String) : Nat := ((all.find? (·.name == name)).map (·.anchor)).getD 0

/-- How `Pretty.lean` renders a constructor without parameters. -/
def prettyOf (c : Ctor) : String := ((rowOf c).map (·.pretty)).getD ""

/-- The constructor the parser reads `name(args)` as, on the integer path
(`.plain`) or of doubles (`.float`), from the rows `rows`. -/
def read? (rows : List FnRow) (path : Reads) (name : String) : List Expr → Option Expr
  | [a] => rows.findSome? fun r =>
    if r.reads == path && r.name == name then
      match r.ctor with | some (.un f) => some (.un f a) | _ => none
    else none
  | [a, b] => rows.findSome? fun r =>
    if r.reads == path && r.name == name then
      match r.ctor with | some (.bin f) => some (.bin f a b) | _ => none
    else none
  | _ => none

theorem anchorOf_mem (c : Ctor) : anchorOf c = 0 ∨ ∃ r ∈ all, r.anchor = anchorOf c := by
  unfold anchorOf
  cases h : rowOf c with
  | none => exact Or.inl rfl
  | some r => exact Or.inr ⟨r, List.mem_of_find?_eq_some h, rfl⟩

theorem anchorNamed_mem (name : String) :
    anchorNamed name = 0 ∨ ∃ r ∈ all, r.anchor = anchorNamed name := by
  unfold anchorNamed
  cases h : all.find? (·.name == name) with
  | none => exact Or.inl rfl
  | some r => exact Or.inr ⟨r, List.mem_of_find?_eq_some h, rfl⟩

/-! ## Checks -/

/-- A name has one anchor and an anchor one name. -/
example : all.all fun r => all.all fun s => (r.name == s.name) == (r.anchor == s.anchor) := by
  decide +kernel
/-- A constructor has one row, and a row stands for itself. -/
example : ((all.filterMap (·.ctor)).Nodup) := nodup_of_nodupB (by decide +kernel)
example : all.all fun r => r.ctor.all fun c => c.key == c := by decide +kernel
/-- New anchors are in their area's range. -/
example : areas.all fun (_, rs, lo) => rs.all fun r =>
    r.anchor < 100 || (lo ≤ r.anchor && r.anchor < lo + 100) := by
  decide +kernel
/-- Every row's group is one of the design's. -/
example : all.all fun r => (groups.lookup r.group).isSome := by decide +kernel
/-- The parser reads `.plain` and `.float` rows by their constructors' arity. -/
example : all.all fun r => r.reads == .own ||
    r.ctor matches some (.un _) | some (.bin _) := by decide +kernel

/-! ## For the Python mirror -/

/-- A constructor as Lean writes it, without the namespace:
`BinFn.trim true false`. -/
def ctorName : Ctor → String
  | .un f => strip (reprStr f) | .bin f => strip (reprStr f) | .agg f => strip (reprStr f)
  | .hof f => strip (reprStr f)
where strip (s : String) : String := s.replace "Substrait." ""

open Lean (Json toJson) in
/-- The tables as JSON, area by area: `substrait-check --functions`. -/
def tableJson : Json :=
  Json.arr <| (areas.flatMap fun (area, rows, _) => rows.map fun r => Json.mkObj [
    ("area", toJson area), ("name", toJson r.name), ("anchor", toJson r.anchor),
    ("group", toJson r.group),
    ("ctor", match r.ctor with | some c => toJson (ctorName c) | none => Json.null),
    ("reads", toJson (match r.reads with | .plain => "plain" | .float => "float" | .own => "own")),
    ("options", toJson ((groups.lookup r.group).getD []))]).toArray

end Substrait.Functions
