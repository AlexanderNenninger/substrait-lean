import SubstraitLean.Safety
import SubstraitLean.Pretty

/-!
# Inferring the bounds a contract needs (#244)

Since #202, integer overflow at the declared width is an error, so a contract
on `amount * 2` must bound `amount`. This file finds such bounds: for each
overflow `Rel.mayIssues` reports, the range each base-table column must stay
in to rule it out. It is the forward range analysis of
`SubstraitLean/Contracts.lean` run backwards: `amount * 2` fits 64 bits when
`amount ∈ [-2⁶², 2⁶² - 1]`.

The inference is **untrusted**. Its bounds are candidates: the caller adds
them to the contract's preconditions, exactly as if the user had written
them, and proves the contract again (`contract_sound`, `Rel.mayIssues_sound`).
A wrong bound makes that proof fail; it can never make it pass wrongly. So
nothing here needs a proof, and nothing here is.

Each overflow gets a `Bounds`:

* `needs`, the columns and ranges, with `split := false` when the ranges
  follow from the operation alone (`+`, `-` and `*` with a constant or with a
  value the preconditions already bound, negation, `ABS`, chains of them,
  timestamp truncation);
* `split := true` when the operation has no unique weakest bound, such as the
  product or sum of two unbounded columns: the ranges are a suggestion (an
  even split), which the caller shows and does not assume;
* `why`, when no column range rules it out (an aggregate's or a window
  function's value): the caller suggests a bound in words.
-/

namespace Substrait.Infer

open FloatCode (minI64 maxI64)

/-- Columns of a relation's input and the ranges they must stay in. -/
abbrev Cols := List (Nat × Bound)

structure Found where
  cols : Cols := []
  /-- An arbitrary choice was made (two unbounded operands). -/
  split : Bool := false
  /-- Columns that must not hold a value (a divisor's column, `$j ≠ k`). -/
  nes : List (Nat × Int) := []

/-- What rules out one overflow. -/
structure Bounds where
  /-- Base-table columns (`table`, column) and their ranges. -/
  needs : List (String × Nat × Bound) := []
  split : Bool := false
  /-- Base-table columns and a value each must not hold. -/
  nes : List (String × Nat × Int) := []
  /-- Why no column range rules it out, if none does. -/
  why : Option String := none

def Found.append (a b : Found) : Found := ⟨a.cols ++ b.cols, a.split || b.split, a.nes ++ b.nes⟩

/-- `⌈a / b⌉` and `⌊a / b⌋` for `b > 0`. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)
def floorDiv (a b : Int) : Int := a / b

/-- A forward bound the preconditions give, if it is finite and well inside
64 bits (a type's own limits are no use to divide by). -/
def usable (a : AVal) : Option (Int × Int) :=
  match a.int with
  | some ⟨some l, some h⟩ =>
    if -2 ^ 62 ≤ l ∧ h ≤ 2 ^ 62 then some (l, h) else none
  | _ => none

/-- The largest `|x|` with `x · x ≤ m`. -/
def isqrt (m : Nat) : Nat := Id.run do
  -- Newton's method from above.
  let mut x := m
  let mut y := (m + 1) / 2
  for _ in [0:200] do
    if y < x then
      x := y
      y := (x + m / x) / 2
  return x

#guard isqrt (2 ^ 62) == 2 ^ 31 && isqrt 15 == 3 && isqrt 0 == 0

/-- How far `Time.trunc u ts` may be below `ts`, in microseconds. -/
def span : Time.TimeUnit → Int
  | .microsecond => 0
  | .millisecond => 1000
  | .second => 1_000_000
  | .minute => 60_000_000
  | .hour => 3_600_000_000
  | .day => Time.usPerDay
  | .week => 7 * Time.usPerDay
  | .month => 31 * Time.usPerDay
  | .quarter => 92 * Time.usPerDay
  | .year => 366 * Time.usPerDay

/-- In days, for truncating a DATE. -/
def spanDays (u : Time.TimeUnit) : Int := span u / Time.usPerDay

/-- Ranges of the columns of `env` that keep `e` in `[lo, hi]`, or why there
are none. Over-strict is fine; too weak only fails the proof. -/
partial def need (env : List AVal) (fs : List Fact) (lo hi : Int) : Expr → Except String Found
  | .field i => pure ⟨[(i, ⟨some lo, some hi⟩)], false⟩
  | .lit (.int v) => if lo ≤ v ∧ v ≤ hi then pure {} else throw "it adds a constant that is out of range"
  | .lit _ => pure {}
  | .un .neg a => need env fs (-hi) (-lo) a
  | .un (.wrap _) a | .un .widen a => need env fs lo hi a
  -- `trunc u x ∈ (x - span u, x]`.
  | .un (.dateTrunc u) a => need env fs (lo + span u) hi a
  | .un (.dayTrunc u) a => need env fs (lo + spanDays u) hi a
  | .un (.bucket k _) a => need env fs (lo + k) hi a
  | .un (.addMonths m time) a =>
    let d := (if time then Time.usPerDay else 1) * 31 * m.natAbs
    need env fs (lo + d) (hi - d) a
  | .bin .add a b | .bin .dateAdd a b =>
    match a, b with
    | _, .lit (.int c) => need env fs (lo - c) (hi - c) a
    | .lit (.int c), _ => need env fs (lo - c) (hi - c) b
    | _, _ =>
      match usable (b.absD env fs), usable (a.absD env fs) with
      | some (bl, bh), _ => need env fs (lo - bl) (hi - bh) a
      | none, some (al, ah) => need env fs (lo - al) (hi - ah) b
      | none, none => do
        let x ← need env fs (lo / 2) (hi / 2) a
        let y ← need env fs (lo / 2) (hi / 2) b
        pure ⟨x.cols ++ y.cols, true⟩
  | .bin .sub a b =>
    match a, b with
    | _, .lit (.int c) => need env fs (lo + c) (hi + c) a
    | .lit (.int c), _ => need env fs (c - hi) (c - lo) b
    | _, _ =>
      match usable (b.absD env fs), usable (a.absD env fs) with
      | some (bl, bh), _ => need env fs (lo + bh) (hi + bl) a
      | none, some (al, ah) => need env fs (ah - hi) (al - lo) b
      | none, none => do
        -- No unique split: half the range each.
        let x ← need env fs (lo / 2) (hi / 2) a
        let y ← need env fs (-(hi / 2)) (-(lo / 2)) b
        pure ⟨x.cols ++ y.cols, true⟩
  | .bin .mul a b =>
    match a, b with
    | x, .lit (.int c) | .lit (.int c), x =>
      if c = 0 then pure {}
      else if 0 < c then need env fs (ceilDiv lo c) (floorDiv hi c) x
      else need env fs (ceilDiv (-hi) (-c)) (floorDiv (-lo) (-c)) x
    | _, _ =>
      if lo > 0 ∨ hi < 0 then throw "it needs a product that is not 0" else
      let k := min hi (-lo)
      match usable (b.absD env fs), usable (a.absD env fs) with
      | some (bl, bh), _ =>
        let m := max bl.natAbs bh.natAbs
        if m = 0 then pure {} else need env fs (-(k / m)) (k / m) a
      | none, some (al, ah) =>
        let m := max al.natAbs ah.natAbs
        if m = 0 then pure {} else need env fs (-(k / m)) (k / m) b
      | none, none => do
        let r : Int := isqrt k.toNat
        let x ← need env fs (-r) r a
        let y ← need env fs (-r) r b
        pure ⟨x.cols ++ y.cols, true⟩
  -- `a / c`: only `c = ±1` can leave the range (`ABS` is `a / -1`).
  | .bin .idiv a (.lit (.int c)) =>
    if c = 1 then need env fs lo hi a
    else if c = -1 then need env fs (-hi) (-lo) a
    else if lo ≤ 0 ∧ 0 ≤ hi then pure {} else throw "it needs a quotient out of range"
  | .ifThen _ t e => do
    let x ← need env fs lo hi t
    let y ← need env fs lo hi e
    pure (x.append y)
  | e => throw s!"it reads {e.render}, which the inference does not look into"

/-- `need` with an open side: `none` stands for no bound. Codes of doubles
lie in `[negInf, nan]`, so those are the open ends, and the sides that stay
open are dropped from the result. -/
def needD (env : List AVal) (fs : List Fact) (lo hi : Option Int) (e : Expr) :
    Except String Found := do
  let l := lo.getD (FloatCode.negInf - 1)
  let h := hi.getD (FloatCode.nan + 1)
  let f ← need env fs l h e
  pure { f with cols := f.cols.map fun (j, b) =>
    (j, ⟨if lo.isNone && b.lo == some l then none else b.lo,
         if hi.isNone && b.hi == some h then none else b.hi⟩) }

/-- The finite doubles. -/
def finiteD (env : List AVal) (fs : List Fact) : Expr → Except String Found :=
  needD env fs (some (FloatCode.negInf + 1)) (some (FloatCode.posInf - 1))

/-- A divisor that must not be 0: `$j + c` needs `$j ≠ -c`. -/
def nonZero : Expr → Except String Found
  | .un .itof x => nonZero x
  | x => match x.linTerm with
    | some (j, c) => pure { nes := [(j, -c)] }
    | none => throw s!"it divides by {x.render}, which the inference does not look into"

/-- The range an expression with an issue must stay in, applied to its
operand where the issue is about the operand: overflow, division by zero,
domain errors, casts out of range, and a `SUM` excepted. -/
def atIssue (env : List AVal) (fs : List Fact) : Issue × Expr → Except String Found
  | (.wraps, .un (.wrap n) a) => need env fs (-(2 ^ (n - 1))) (2 ^ (n - 1) - 1) a
  | (.wraps, .un (.dateTrunc u) a) => need env fs (minI64 + span u) maxI64 a
  | (.wraps, e) => need env fs minI64 maxI64 e
  | (.overflow, .un (.dateTrunc u) a) => need env fs (Time.nsMin + span u) Time.nsMax a
  | (.overflow, .un (.dayTrunc u) a) =>
    need env fs (Time.nsDayMin + spanDays u) Time.nsDayMax a
  | (.overflow, .un (.addMonths m false) a) =>
    need env fs Time.dayMin Time.dayMax (.un (.addMonths m false) a)
  | (.overflow, .un (.addMonths m true) a) =>
    need env fs Time.partMin Time.partMax (.un (.addMonths m true) a)
  | (.overflow, .un .timeOfDay a) | (.overflow, .un (.strftime _) a) =>
    need env fs Time.partMin Time.partMax a
  | (.overflow, .un (.bucket k _) a) => need env fs (Time.nsMin + k) Time.nsMax a
  | (.overflow, .bin .dateAdd a b) => do
    -- Both the date and the result are in range.
    let x ← need env fs Time.dayMin Time.dayMax a
    let y ← need env fs Time.dayMin Time.dayMax (.bin .dateAdd a b)
    pure (x.append y)
  | (.overflow, e@(.bin .idiv _ _)) => need env fs minI64 maxI64 e
  | (.overflow, .un (.decimal p _) a) => need env fs (1 - 10 ^ p) (10 ^ p - 1) a
  | (.overflow, .bin .strRepeat s n) => match s.strBytes? with
    | some m => if m = 0 then pure {} else need env fs minI64 (Text.repeatMax / m) n
    | none => throw "it repeats a string that is not a constant"
  | (.divByZero, .bin _ _ b) => nonZero b
  | (.badCast, .un .ftoi a) => needD env fs (some FloatCode.castLo) (some FloatCode.castHi) a
  | (.badCast, .un (.narrow n) a) => need env fs (-(2 ^ (n - 1))) (2 ^ (n - 1) - 1) a
  | (.negExponent, .bin .ipow _ b) => need env fs 0 maxI64 b
  | (.domain, .un (.fmath f) a) => needD env fs f.lo? f.hi? a
  -- A negative base needs an integer exponent; a base ≥ 0 needs none.
  | (.domain, .bin .fpow a _) => needD env fs (some 0) none a
  -- `fmod(±∞, y)`.
  | (.domain, .bin .fmod a _) => finiteD env fs a
  -- `∞ - ∞`, `0 · ∞`, `∞ / ∞`: either side finite rules it out.
  | (.domain, .bin .fadd a b) | (.domain, .bin .fsub a b) | (.domain, .bin .fmul a b)
  | (.domain, .bin .fdiv a b) => do
    let x ← finiteD env fs a
    let y ← finiteD env fs b
    pure { x.append y with split := true }
  -- A logarithm of a positive number to a positive base other than 1.
  | (.domain, .bin .flogb x b) => do
    let fx ← needD env fs (some 1) none x
    let fb ← needD env fs (some 1) none b
    let one ← match b.linTerm with
      | some (j, c) => pure ({ nes := [(j, FloatCode.one - c)] } : Found)
      | none => throw s!"its base is {b.render}, which the inference does not look into"
    pure ((fx.append fb).append one)
  | (.domain, .bin (.substr n _) _ a) =>
    if n.all fun n => decide ((n : Int) < Text.substrMax) then
      need env fs (-Text.substrMax) (Text.substrMax - 1) a
    else throw "its length is a constant out of range"
  | (k, _) => throw s!"the inference does not cover this kind of {k.name}"

/-! ## Down to the base tables -/

/-- The base-table columns `(table, column, range)` behind column `i` of
`r` that keep it in `b`, and whether a choice was made on the way. -/
def pullNeeds (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Rel → Nat → Bound → Except String (List (String × Nat × Bound) × Bool)
  | .read t, i, b => pure ([(t, i, b)], false)
  | .values _ _, _, _ => throw "it reads a value written in the query (VALUES)"
  | .filter r _, i, b | .fetch r _ _, i, b | .orderBy r _, i, b | .distinct r, i, b
  | .semi r _ _ _, i, b => pullNeeds cat A F T r i b
  | .emit r m, i, b => match m[i]? with
    | some j => pullNeeds cat A F T r j b
    | none => throw "it reads a column out of range"
  | .project r es, i, b =>
    if i < r.arity cat then pullNeeds cat A F T r i b
    else match es[i - r.arity cat]?, b.lo, b.hi with
      | some e, some lo, some hi => do
        let f ← need (r.aeval cat A F T true) (r.facts cat F T) lo hi e
        let mut out := []
        let mut split := f.split
        for (j, c) in f.cols do
          let (n, s) ← pullNeeds cat A F T r j c
          out := out ++ n
          split := split || s
        pure (out, split)
      | _, _, _ => throw "it needs an unbounded range"
  | .cross a c, i, b | .join a c _ _, i, b =>
    if i < a.arity cat then pullNeeds cat A F T a i b
    else pullNeeds cat A F T c (i - a.arity cat) b
  | .unionAll a c, i, b => do
    let (x, s) ← pullNeeds cat A F T a i b
    let (y, s') ← pullNeeds cat A F T c i b
    pure (x ++ y, s || s')
  | .window r _ _ _, i, b =>
    if i < r.arity cat then pullNeeds cat A F T r i b
    else throw "it reads the value of a window function"
  | .unnest r col, i, b =>
    if i ≠ col then pullNeeds cat A F T r i b else throw "it reads an UNNEST element"
  | .aggregate r gs ms, i, b =>
    let s := r.aeval cat A F T true
    let go (e : Expr) : Except String (List (String × Nat × Bound) × Bool) :=
      match b.lo, b.hi with
      | some lo, some hi => do
        let f ← need s (r.facts cat F T) lo hi e
        let mut out := []
        let mut split := f.split
        for (j, c) in f.cols do
          let (n, sp) ← pullNeeds cat A F T r j c
          out := out ++ n
          split := split || sp
        pure (out, split)
      | _, _ => throw "it needs an unbounded range"
    match gs[i]? with
    | some g => go g
    | none => match ms[i - gs.length]? with
      -- MIN and MAX are values of their argument.
      | some m => if m.fn = .min ∨ m.fn = .max then go m.arg
        else throw "it reads the value of an aggregate other than MIN or MAX"
      | none => throw "it reads a column out of range"

/-- The base-table column behind column `i` of `r` that must not hold `k`. -/
def pullNe (cat : Catalog) : Rel → Nat → Int → Except String (List (String × Nat × Int))
  | .read t, i, k => pure [(t, i, k)]
  | .values _ _, _, _ => throw "it reads a value written in the query (VALUES)"
  | .filter r _, i, k | .fetch r _ _, i, k | .orderBy r _, i, k | .distinct r, i, k
  | .semi r _ _ _, i, k => pullNe cat r i k
  | .emit r m, i, k => match m[i]? with
    | some j => pullNe cat r j k
    | none => throw "it reads a column out of range"
  | .project r es, i, k =>
    if i < r.arity cat then pullNe cat r i k
    else match es[i - r.arity cat]?.bind Expr.linTerm with
      | some (j, c) => pullNe cat r j (k - c)
      | none => throw "it divides by a computed value"
  | .cross a c, i, k | .join a c _ _, i, k =>
    if i < a.arity cat then pullNe cat a i k else pullNe cat c (i - a.arity cat) k
  | .unionAll a c, i, k => do pure ((← pullNe cat a i k) ++ (← pullNe cat c i k))
  | .window r _ _ _, i, k =>
    if i < r.arity cat then pullNe cat r i k else throw "it reads the value of a window function"
  | .unnest r col, i, k =>
    if i ≠ col then pullNe cat r i k else throw "it reads an UNNEST element"
  | .aggregate r gs ms, i, k =>
    let go (e : Expr) := match e.linTerm with
      | some (j, c) => pullNe cat r j (k - c)
      | none => throw "it divides by a computed value"
    match gs[i]? with
    | some g => go g
    | none => match ms[i - gs.length]? with
      | some m => if m.fn = .min ∨ m.fn = .max then go m.arg
        else throw "it reads the value of an aggregate other than MIN or MAX"
      | none => throw "it reads a column out of range"

/-- The base-table columns behind a node's input columns `cols`. -/
def pullAll (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (r : Rel) (f : Found) : Bounds :=
  let step := fun (acc : Except String (List (String × Nat × Bound) × Bool)) (jc : Nat × Bound) =>
    do let (out, s) ← acc; let (n, s') ← pullNeeds cat A F T r jc.1 jc.2; pure (out ++ n, s || s')
  let nes := f.nes.foldl (init := pure []) fun acc (j, k) => do
    pure ((← acc) ++ (← pullNe cat r j k))
  match f.cols.foldl step (pure ([], f.split)), nes with
  | .ok (needs, split), .ok nes => { needs, split, nes }
  | .error why, _ | _, .error why => { why := some why }

/-- The bounds that rule out each overflow `e.mayIssues` reports on the rows
of `r`. -/
def onRows (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (r : Rel) (e : Expr) : List (Issue × Expr × Bounds) :=
  let env := r.aeval cat A F T true
  let fs := r.facts cat F T
  (e.mayIssues env fs).map fun ie =>
    (ie.1, ie.2, match atIssue env fs ie with
      | .ok f => pullAll cat A F T r f
      | .error why => { why := some why })

/-- Each issue of `Rel.mayIssues` with what would rule it out, in the same
walk. -/
def Rel.bounds (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Bool → Rel → List (Issue × Expr × Bounds)
  | _, .read _ | _, .values _ _ => []
  | _, .filter r c => Rel.bounds cat A F T true r ++ onRows cat A F T r.loose c
  | u, .project r es =>
    let s := if u then r.loose else r
    Rel.bounds cat A F T u r ++ es.flatMap (onRows cat A F T s)
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r
  | u, .unnest r _ | u, .window r _ _ _ => Rel.bounds cat A F T u r
  | u, .cross a b | u, .unionAll a b => Rel.bounds cat A F T u a ++ Rel.bounds cat A F T u b
  | _, .join a b _ on | _, .semi a b _ on =>
    Rel.bounds cat A F T true a ++ Rel.bounds cat A F T true b ++
      onRows cat A F T (Rel.cross a.loose b.loose) on
  | u, .aggregate r gs ms =>
    let s := if u then r.loose else r
    Rel.bounds cat A F T u r ++ (gs ++ ms.flatMap Measure.exprs).flatMap (onRows cat A F T s)

/-- The intersection of two ranges. -/
def meet (a b : Bound) : Bound :=
  ⟨match a.lo, b.lo with
    | some x, some y => some (max x y) | x, none => x | none, y => y,
   match a.hi, b.hi with
    | some x, some y => some (min x y) | x, none => x | none, y => y⟩

/-- The ranges without the sides each column's schema and preconditions
already imply. -/
def trim (A : String → List AVal) (needs : List (String × Nat × Bound)) :
    List (String × Nat × Bound) :=
  needs.filterMap fun (t, i, b) =>
    let known := ((A t).getD i AVal.top).int.getD Bound.top
    let lo := b.lo.filter fun l => !(known.lo.any (l ≤ ·))
    let hi := b.hi.filter fun h => !(known.hi.any (· ≤ h))
    if lo.isNone && hi.isNone then none else some (t, i, ⟨lo, hi⟩)

/-- One range per column for the overflows that have exact bounds, without
the sides the column's schema and preconditions already imply. -/
def merged (A : String → List AVal) (bs : List (Issue × Expr × Bounds)) :
    List (String × Nat × Bound) :=
  let exact := bs.filterMap fun (_, _, b) => if b.split || b.why.isSome then none else some b.needs
  let all := exact.flatten.foldl (init := ([] : List (String × Nat × Bound))) fun acc (t, i, b) =>
    match acc.find? (fun (t', i', _) => t' == t && i' == i) with
    | some (_, _, b') => acc.map fun x => if x.1 == t && x.2.1 == i then (t, i, meet b b') else x
    | none => acc ++ [(t, i, b)]
  trim A all

/-- The values each base-table column must not hold, for the issues that
have exact bounds. -/
def mergedNes (bs : List (Issue × Expr × Bounds)) : List (String × Nat × Int) :=
  (bs.filterMap fun (_, _, b) => if b.split || b.why.isSome then none else some b.nes).flatten.eraseDups

end Substrait.Infer
