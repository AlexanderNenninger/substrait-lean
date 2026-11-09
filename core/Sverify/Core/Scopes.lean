import Sverify.Core.Issue
import Sverify.Core.Options

/-!
# Option scopes (D34)

Each option differs from the reference only on its scope: a predicate on a
call's arguments and the reference's result, stated here beside the option,
one row per option of `options` in its order. A profile that allows an
option a behaviour the reference does not may give another value than the
reference's at a call only where the call is in that option's scope
(`CallExtra`, `AggExtra` in `core/Sverify/Core/AllowedP.lean`); everywhere else
the call is the reference's. A plan depends on an option only where a call
may be in its scope.

A scope may be wider than where the behaviours differ, never narrower: an
option whose scope is not pinned down yet is in scope at every call
(`true`), as `rounding` is. `sum_order`'s true scope is a sum that is not
exact; it is `true` until the analyses can tell. An engine's own order of
additions, overflow to `±∞` on the way included, is `sum_order`'s
(`FloatSums`), so `agg.fsum`'s `nan_creation` and `float_overflow` are about
the correctly rounded sum. -/

namespace Substrait
variable [Boxes.Ambient]

open Functions (Ctor)

mutual
/-- A NaN, here or inside a list or a struct. -/
def Value.hasNaN : Value → Bool
  | .float c => decide (FloatCode.nan ≤ c)
  | .list vs | .struct vs => Value.anyNaN vs
  | _ => false

def Value.anyNaN : List Value → Bool
  | [] => false
  | v :: vs => v.hasNaN || Value.anyNaN vs
end

mutual
/-- The double zero, here or inside a list or a struct: where an engine's
`-0.0` may arise or matter. -/
def Value.hasZero : Value → Bool
  | .float c => c == 0
  | .list vs | .struct vs => Value.anyZero vs
  | _ => false

def Value.anyZero : List Value → Bool
  | [] => false
  | v :: vs => v.hasZero || Value.anyZero vs
end

/-- `+∞` or `-∞`. -/
def Value.isInf : Value → Bool
  | .float c => isInfCode c
  | _ => false

/-- A finite double, or a value that is not a double. -/
def Value.finiteOrOther : Value → Bool
  | .float c => isFiniteCode c
  | _ => true

/-- The reference's result of a call. -/
def Functions.Ctor.result : Ctor → List Value → Value
  | .un f, [v] => f.apply v
  | .bin f, [v, w] => f.apply v w
  | .agg f, vs => f.apply vs
  | _, _ => .null

/-- The issue the reference reports at a call (`Safety.lean`). -/
def Functions.Ctor.issue : Ctor → List Value → Option Issue
  | .un f, [v] => f.issueAll v
  | .bin f, [v, w] => f.issueAll v w
  | _, _ => none

/-- A zero divisor: an integer `0`, or a double `0.0` or `-0.0`, where the
reference raises (D31). -/
def divisorZero : List Value → Bool
  | [_, .int 0] => true
  | [_, .float c] => FloatCode.canon c == 0
  | _ => false

/-- A quotient of operands of opposite signs with a remainder: where
`FLOOR` and `TRUNCATE` division differ. -/
def floorDiffers : List Value → Bool
  | [.int a, .int b] => decide (a * b < 0) && a.tmod b != 0
  | [.float a, .float b] => decide (a * b < 0)
  | _ => false

/-- Is an integer `SUM` of `vs` outside 64 bits? -/
def sumOverflows (vs : List Value) : Bool := !inI64 (intSum vs)

/-- **The scope of option `o`** at a call of `c` on `args` (an aggregate's
values for `.agg`): where its behaviours may differ from the reference
(D34). -/
def optionScope (o : String) (c : Ctor) (args : List Value) : Bool :=
  let iss := c.issue args
  let r := c.result args
  let isAgg := match c with | .agg _ => true | _ => false
  match o with
  -- Integers and decimals: the exact result outside the type's range.
  | "overflow" => iss == some .overflow || iss == some .wraps || iss == some .sumWraps ||
      (isAgg && sumOverflows args)
  | "on_division_by_zero" => divisorZero args
  | "division_type" => floorDiffers args
  | "min_mod_neg_one" => match args with
    | [.int a, .int b] => b == -1 && decide (a ≤ -2 ^ 63)
    | _ => false
  | "shift_range" => true
  | "decimal_rescale" => true
  -- Doubles.
  | "rounding" => true
  | "on_domain_error" => iss == some .domain
  | "on_log_zero" => iss == some .domain
  -- The arguments are not NaN and the IEEE result is: `∞ − ∞`, `0 · ∞`,
  -- `∞ / ∞`, `fmod(±∞, y)` (`nanCase`), `0 / 0`, `fmod(x, 0)`, a `SUM` of
  -- `+∞` and `−∞`.
  | "nan_creation" => match c, args with
    -- Zeros by their canonical codes: `-0.0` is a zero too (D31).
    | .bin f, [.float a, .float b] => nanCase f a b || (f == .fmod && FloatCode.canon b == 0) ||
        (f == .fdiv && FloatCode.canon a == 0 && FloatCode.canon b == 0)
    | .agg _, vs => !Value.anyNaN vs && vs.any (· == .float FloatCode.posInf) &&
        vs.any (· == .float FloatCode.negInf)
    | _, _ => false
  -- A zero argument or a zero result (underflow, `x − x`, a sum rounding to zero).
  | "zero_sign" => Value.anyZero args || r.hasZero
  -- The reference's result is a zero (`round(-0.4)`, `ceil(-0.4)`).
  | "round_zero_sign" => r.hasZero
  | "nan_equality" => Value.anyNaN args
  | "nan_order" => Value.anyNaN args
  | "nan_kind" => Value.anyNaN args || r.hasNaN
  -- Strings, dates and lists.
  | "negative_start" => args.any fun | .int a => decide (a < 0) | _ => false
  | "substring_range" => iss == some .domain
  | "case_sensitivity" => true
  | "char_set" => true
  | "null_handling" => args.any (· == .null)
  | "date_range" => iss == some .overflow
  | "time_interval_months" => true
  | "list_null_order" => true
  -- Aggregates, windows and relations.
  | "sum_order" => true
  | "stat_algo" => true
  | "window_sum_algo" => true
  | "stat_degenerate" => true
  -- An `AVG` with an integer result (`AggFn.iavg`): a `SUM` never meets it.
  | "avg_int_result" => c == .agg .iavg
  | "quantile_interp" => true
  | "tie_pick" => true
  | "tie_order" => true
  | "null_order" => true
  | "clustered" => true
  | "ntile_spread" => true
  | "float_to_int" => true
  | "cast_failure" => iss == some .badCast
  | "distribution" => true
  | "empty_group_aggregates" => isAgg && args.isEmpty
  -- Finite arguments, an infinite correctly rounded result.
  | "float_overflow" => iss == some .infinite ||
      (isAgg && args.all Value.finiteOrOther && r.isInf)
  | "null_join_keys" => true
  | "string_positions" => true
  | _ => true

/-- Can option `o` apply to a call of `c` at all? A call reads only its
group's options that apply to it (`ctorReads`). -/
def optionApplies (o : String) (c : Ctor) : Bool :=
  match o with
  | "avg_int_result" => c == .agg .iavg
  | "empty_group_aggregates" => match c with | .agg _ => true | _ => false
  | _ => true

/-- An option applies wherever a call may be in its scope. -/
theorem optionApplies_of_scope {o : String} {c : Ctor} {args : List Value}
    (h : optionScope o c args = true) : optionApplies o c = true := by
  unfold optionApplies
  split
  · simpa [optionScope] using h
  · cases c <;> simp_all [optionScope]
  · rfl

/-- The options whose scope is stated above, in the catalogue's order. -/
def scopedOptions : List String :=
  ["overflow", "on_division_by_zero", "division_type", "min_mod_neg_one", "shift_range",
   "decimal_rescale", "rounding", "on_domain_error", "on_log_zero", "nan_creation", "zero_sign",
   "round_zero_sign", "nan_equality", "nan_order", "nan_kind", "negative_start", "substring_range",
   "case_sensitivity", "char_set", "null_handling", "date_range", "time_interval_months",
   "list_null_order", "sum_order", "stat_algo", "window_sum_algo", "stat_degenerate",
   "avg_int_result", "quantile_interp", "tie_pick", "tie_order", "null_order", "clustered",
   "ntile_spread", "float_to_int", "cast_failure", "distribution", "empty_group_aggregates",
   "float_overflow", "null_join_keys", "string_positions"]

-- Every option of the catalogue has its scope here, and nothing else does.
#guard options.map (·.id) == scopedOptions

end Substrait
