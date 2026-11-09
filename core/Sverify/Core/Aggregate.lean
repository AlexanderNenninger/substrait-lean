import Sverify.Core.Order
import Sverify.Core.Dedup
import Sverify.Core.FloatMoments

/-!
# Aggregation

`AggregateRel` with one grouping set: the output has one row per distinct
value of the grouping expressions (in order of first occurrence), holding
those values followed by one value per measure. Without grouping
expressions there is exactly one output row, even for an empty input.

A measure is `COUNT`, `SUM`, `MIN`, `MAX`, `AVG` or `ARRAY_AGG` (`collect`,
whose rows may be ordered) of an expression, over the
rows that pass its `FILTER` (if any), skipping NULLs, and over distinct
values only for `COUNT(DISTINCT …)` and friends. On no values `COUNT` is 0
and the others are NULL. Checked against DataFusion 51:

* `SUM` of integers wraps around modulo 2⁶⁴; since wrapping addition is
  associative, the result is the true sum unless that leaves 64 bits.
  `SUM` here is the true sum, and `SubstraitLean/Safety.lean` warns.
* `SUM` and `AVG` of doubles round, in an order DataFusion does not promise;
  here they add in list order with native floats. `AVG` of integers is the
  `AVG` of their conversions to double, which the parser makes explicit.
* `MIN` and `MAX` use the same order as `ORDER BY` (`Value.le`). Only
  `--write-datafusion` refuses them on doubles (`DataFusion.floatExtremes`):
  DataFusion's grouped `MIN` of a group of +∞ is the largest finite double,
  and it skips NaN next to other values.
* Grouping compares values exactly; doubles have one zero and one NaN
  (`core/Sverify/Core/Float.lean`), so -0.0 and 0.0 are one group, and NULLs
  group together.
-/

namespace Substrait

/-! ## Measures -/

inductive AggFn where
  /-- `COUNT` of the non-NULL values (`COUNT(*)` counts a literal). -/
  | count
  /-- `SUM` of integers, exactly. -/
  | sum
  /-- `SUM` and `AVG` of doubles, with native floats. -/
  | fsum | avg
  /-- `MIN` and `MAX` by `Value.le`. -/
  | min | max
  /-- `ARRAY_AGG`: the list of the values, in the measure's `sort` order. -/
  | collect
  /-- `AVG` of integers with an integer result (Substrait's `avg` of `i64`,
  #209): the exact mean, truncated toward zero. It always fits, and lies
  between the smallest and largest value (`clampInts` changes nothing for
  integers; it spares the contract checker the division, #237). -/
  | iavg
  /-- `BIT_AND`, `BIT_OR`, `BIT_XOR` of 64-bit integers (#53): the operation
  folded over the values (the parser gives only these three). -/
  | bit (op : BitOp)
  /-- `VARIANCE` (`sqrt := false`) and `STDDEV` of doubles, of a sample
  (`n - 1`) or a population (`n`), #54. Engines compute it with their own
  algorithms, so the model claims only some double that is not negative (or
  NaN), and NULL where the definition has no value: no values, or a sample
  of one. The value it computes is one such double (`varOf`). -/
  | var (sample sqrt : Bool)
  /-- `FIRST` (`last := false`) and `LAST` of the values in the measure's
  `sort` order (#55), as `ARRAY_AGG(x ORDER BY …)[1]` and its last element:
  NULLs skipped, NULL without values. Ties make it depend on the engine, as
  for `collect`, which `Rel.windowsTotal` reports; without a sort every row
  ties (an engine may even pick each measure's value from another row), so
  contracts see only the values' range (`Measure.abs`). -/
  | pick (last : Bool)
  /-- `COVAR_SAMP`/`COVAR_POP` and `CORR` of pairs of doubles (#54), whose
  argument is `pair x y` (rows with a NULL skipped). Engines compute them
  their own way: the model claims some double, or NULL where the definition
  has no value. `CORR` is NULL, as the SQL standard says, for fewer than two
  pairs or a side whose values are all equal (DuckDB gives NaN there). -/
  | cov (sample : Bool)
  | corr
  /-- `STRING_AGG(x, sep ORDER BY …)` (Ibis's `group_concat`, #55): the strings
  in the measure's `sort` order, joined by the constant `sep`; NULLs skipped,
  NULL without values. Ties make it depend on the engine, as for `pick`. -/
  | concat (sep : String)
  /-- An aggregate black box (`core/Sverify/Core/BlackBox.lean`, #325): the
  table's row `name`, its `empty` value without values. -/
  | bbox (name : String)
  /-- `QUANTILE_DISC(x, q)` (`cont := false`) and `QUANTILE_CONT(x, q)` of the
  values (#53), for the exact decimal `q = num / 10 ^ scale` in `[0, 1]`
  (the parser refuses others); `MEDIAN` is `QUANTILE_CONT(x, 0.5)`. NULLs
  skipped, NULL without values. Of the `n` values in order (`sortVals`), the
  discrete one is the one at position `⌈n·q⌉` (counting from 1, at least the
  first), and the continuous one, of doubles, interpolates linearly between
  the neighbours at `⌊(n−1)·q⌋` and `⌈(n−1)·q⌉` (`contValue`). Engines round
  the interpolation their own way, so the reference allows any double
  between the two neighbours (`contAllowed`). -/
  | quantile (cont : Bool) (num scale : Nat)
  /-- `MODE(x ORDER BY …)` (#53): the most frequent value, and of the values
  that tie, the first in the measure's `sort` order (as DuckDB breaks ties,
  by first occurrence). NULLs skipped, NULL without values. Ties in the sort
  order make it depend on the engine, as for `pick`. -/
  | mode
  deriving Repr, DecidableEq

structure Measure where
  fn : AggFn
  arg : Expr
  /-- `fn(DISTINCT arg)` -/
  distinct : Bool := false
  /-- `fn(arg) FILTER (WHERE cond)` -/
  filter : Option Expr := none
  /-- `fn(arg ORDER BY …)`: the order of the rows, for `collect`. -/
  sort : List SortKey := []
  deriving Repr, DecidableEq

def Measure.refsLt (n : Nat) (m : Measure) : Prop :=
  m.arg.refsLt n ∧ ∀ c ∈ m.filter, c.refsLt n

/-- The expressions a measure evaluates (on every input row), and the
columns it orders the rows by. -/
def Measure.exprs (m : Measure) : List Expr :=
  m.arg :: m.filter.toList ++ m.sort.map (.field ·.col)

/-- The rows a measure looks at: those passing its filter. -/
def Measure.kept (m : Measure) (rows : Relation) (I : Impl := Impl.lean) : Relation :=
  match m.filter with
  | none => rows
  | some c => rows.filter fun row => (c.eval row I).isTrue

/-- The values a measure aggregates: its argument on the kept rows, without
NULLs, and without repetitions for `DISTINCT` (up to canonical codes,
`distinctVals`). -/
def Measure.inputs (m : Measure) (rows : Relation) (I : Impl := Impl.lean) : List Value :=
  let vs := ((m.kept rows I).map fun row => m.arg.eval row I).filter (· != .null)
  if m.distinct then distinctVals vs else vs

/-- The sum of the integers among `vs`, and of the unscaled values of its
decimals (a column has one scale). -/
def intSum : List Value → Int
  | [] => 0
  | .int i :: vs | .dec _ i :: vs => i + intSum vs
  | _ :: vs => intSum vs

theorem intSum_cons (v : Value) (vs : List Value) :
    intSum (v :: vs) = v.unscaled?.getD 0 + intSum vs := by
  cases v <;> simp [intSum]

/-- Is the value a decimal? -/
def Value.isDec : Value → Bool
  | .dec _ _ => true
  | _ => false

/-- Is the value a decimal of scale `s`? -/
def Value.isDecOf (s : Nat) : Value → Bool
  | .dec t _ => t == s
  | _ => false

/-- Is `vs` a non-empty list of decimals of scale `s`? -/
def allDecOf (s : Nat) (vs : List Value) : Bool := !vs.isEmpty && vs.all (Value.isDecOf s)

/-- `SUM` of integers, or of decimals of one scale at that scale. A mix of
decimals with other values or other scales has no type; it adds the
unscaled integers, whatever the order of the values (#923). -/
def sumOf (vs : List Value) : Value :=
  match vs with
  | .dec s _ :: _ => if vs.all (Value.isDecOf s) then .dec s (intSum vs) else .int (intSum vs)
  | _ => .int (intSum vs)

theorem intSum_perm {l l' : List Value} (h : l.Perm l') : intSum l = intSum l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [intSum, ih]
  | swap x y l => cases x <;> cases y <;> simp [intSum] <;> omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A `SUM`'s two outcomes: a decimal when all values are decimals of one
scale, an integer otherwise. -/
theorem sumOf_cases (vs : List Value) :
    (∃ s, allDecOf s vs = true ∧ sumOf vs = .dec s (intSum vs)) ∨
    ((∀ s, allDecOf s vs = false) ∧ sumOf vs = .int (intSum vs)) := by
  match vs with
  | [] => exact .inr ⟨fun _ => rfl, rfl⟩
  | .dec s x :: ws =>
    by_cases hall : (Value.dec s x :: ws).all (Value.isDecOf s) = true
    · exact .inl ⟨s, by simp only [allDecOf, hall]; rfl, by simp only [sumOf, hall, ite_true]⟩
    · refine .inr ⟨fun t => ?_, by simp [sumOf, hall]⟩
      by_cases hts : t = s
      · subst hts; simpa [allDecOf] using hall
      · simp [allDecOf, Value.isDecOf, Ne.symm hts]
  | .null :: ws | .bool _ :: ws | .int _ :: ws | .float _ :: ws | .date _ :: ws | .ts _ :: ws
  | .tod _ :: ws | .str _ :: ws | .list _ :: ws | .struct _ :: ws =>
    exact .inr ⟨fun t => by simp [allDecOf, Value.isDecOf], rfl⟩

theorem allDecOf_perm {vs ws : List Value} (h : vs.Perm ws) (s : Nat) :
    allDecOf s vs = allDecOf s ws := by
  have hall : vs.all (Value.isDecOf s) = ws.all (Value.isDecOf s) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact ⟨fun h' x hx => h' x (h.mem_iff.mpr hx), fun h' x hx => h' x (h.mem_iff.mp hx)⟩
  have hl := h.length_eq
  have he : vs.isEmpty = ws.isEmpty := by
    cases vs <;> cases ws <;> simp_all
  simp only [allDecOf, hall, he]

/-- Two lists of decimals of scales `s` and `t` with a value in common: `s = t`. -/
theorem allDecOf_scale {vs : List Value} {s t : Nat} (hs : allDecOf s vs = true)
    (ht : allDecOf t vs = true) : s = t := by
  simp only [allDecOf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hs ht
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil vs hs.1
  have a := List.all_eq_true.mp hs.2 w hw
  have b := List.all_eq_true.mp ht.2 w hw
  cases w <;> simp_all [Value.isDecOf]

/-- Two lists with the same unscaled sum and the same scales have one `SUM`. -/
theorem sumOf_eq_of {vs ws : List Value} (hi : intSum vs = intSum ws)
    (hd : ∀ s, allDecOf s vs = allDecOf s ws) : sumOf vs = sumOf ws := by
  rcases sumOf_cases vs with ⟨s, h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases sumOf_cases ws with ⟨t, g1, f1⟩ | ⟨g1, f1⟩ <;> rw [e1, f1, hi]
  · have hs : allDecOf s ws = true := by rw [← hd s]; exact h1
    rw [allDecOf_scale hs g1]
  · rw [hd s, g1] at h1; cases h1
  · rw [← hd t, h1] at g1; cases g1

@[simp] theorem sumOf_ne_null (vs : List Value) : sumOf vs ≠ .null := by
  rcases sumOf_cases vs with ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e] <;> simp

theorem sumOf_unscaled_eq (vs : List Value) : (sumOf vs).unscaled? = some (intSum vs) := by
  rcases sumOf_cases vs with ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e] <;> rfl

/-- A non-empty list's `SUM` is a decimal of scale `s` when all its values are. -/
theorem isDecOf_sumOf {vs : List Value} (hne : vs ≠ []) (s : Nat) :
    (sumOf vs).isDecOf s = vs.all (Value.isDecOf s) := by
  have ha : allDecOf s vs = vs.all (Value.isDecOf s) := by
    simp [allDecOf, List.isEmpty_eq_false_iff.mpr hne]
  rcases sumOf_cases vs with ⟨t, h1, e⟩ | ⟨h1, e⟩ <;> rw [e]
  · by_cases hts : t = s
    · subst hts; rw [← ha, h1]; simp [Value.isDecOf]
    · have : allDecOf s vs = false := by
        cases h : allDecOf s vs
        · rfl
        · exact absurd (allDecOf_scale h1 h) hts
      rw [← ha, this]; simp [Value.isDecOf, hts]
  · rw [← ha, h1]; rfl

/-- `SUM` does not depend on the order of its values. -/
theorem sumOf_perm {vs ws : List Value} (h : vs.Perm ws) : sumOf vs = sumOf ws := by
  have hsum := intSum_perm h
  rcases sumOf_cases vs with ⟨s, h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases sumOf_cases ws with ⟨t, g1, f1⟩ | ⟨g1, f1⟩ <;> rw [e1, f1, hsum]
  · have hs : allDecOf s ws = true := by rw [← allDecOf_perm h s]; exact h1
    rw [allDecOf_scale hs g1]
  · rw [allDecOf_perm h s, g1] at h1; cases h1
  · rw [← allDecOf_perm h t, h1] at g1; cases g1

def floatSum (vs : List Value) : Int :=
  vs.foldl (fun acc v => match v with
    | .float c => FloatCode.fadd acc c
    | _ => acc) (FloatCode.ofInt 0)

/-- The integers among `vs`. -/
def intsOf (vs : List Value) : List Int := vs.filterMap fun | .int c => some c | _ => none

/-- The doubles among `vs`. -/
def floatsOf (vs : List Value) : List Int := vs.filterMap fun | .float c => some c | _ => none

theorem mem_floatsOf {vs : List Value} {c : Int} : c ∈ floatsOf vs ↔ .float c ∈ vs := by
  simp only [floatsOf, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, h⟩; cases v <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

theorem floats_map_floatsOf : ∀ {vs : List Value}, (∀ w ∈ vs, ∃ i, w = .float i) →
    vs = (floatsOf vs).map .float
  | [], _ => rfl
  | v :: vs, h => by
    obtain ⟨i, rfl⟩ := h v (by simp)
    simp only [floatsOf, List.filterMap_cons, List.map_cons]
    exact congrArg _ (floats_map_floatsOf fun w hw => h w (by simp [hw]))

/-- `c` kept between the smallest and largest integer among `vs`, or `c`
without integers. -/
def clampInts (vs : List Value) (c : Int) : Int :=
  match intsOf vs with
  | [] => c
  | x :: xs => min (max c (xs.foldl min x)) (xs.foldl max x)

/-- `op` folded over the integers among `vs`, from `op`'s identity (`-1`,
all bits set, for `and`; `0` for `or` and `xor`). -/
def bitFold (op : BitOp) (vs : List Value) : Int :=
  vs.foldl (fun acc v => match v with
    | .int b => (op.apply acc b).getD acc
    | _ => acc) (if op == .and then -1 else 0)

/-- The codes of the pairs `ps`, flattened: what `nonFinite` reads. -/
def pairCodes (ps : List (Int × Int)) : List Value := ps.flatMap fun p => [.float p.1, .float p.2]

/-- `AggFn.var` of the doubles `vs` (at least one), D30: the exact moments
rounded once. `S = Σx² − (Σx)²/n` is exact (`comomentNum = n · S`), the
variance is `S / d` rounded to the nearest double (`d = n − 1` for a sample,
`n` for the population), and the deviation its correctly rounded square
root (`sqrtMag`). NULL for a sample of one; a NaN or an infinity among the
values gives NaN, as IEEE's deviations `∞ − ∞` do (the checker raises on an
infinity, #257). -/
def varOf (sample sqrt : Bool) (vs : List Value) : Value :=
  if sample && vs.length == 1 then .null else
    match nonFinite vs with
    | some _ => .float FloatCode.nan
    | none =>
      -- The doubles by their canonical codes (D31).
      let cs := (floatsOf vs).map FloatCode.canon
      let d := if sample then cs.length - 1 else cs.length
      let N := comomentNum cs
      if sqrt then .float (FloatCode.posCode (FloatCode.sqrtMag N.toNat (cs.length * d)))
      else .float (FloatCode.ofExactDiv N (cs.length * d * 2 ^ 1074))

/-- The pairs of doubles among `vs` (`BinFn.pair`'s lists). -/
def pairsOf (vs : List Value) : List (Int × Int) :=
  vs.filterMap fun | .list [.float a, .float b] => some (FloatCode.canon a, FloatCode.canon b) | _ => none

/-- `COVAR_SAMP` / `COVAR_POP` of the pairs among `vs`, D30: the exact
co-moment `C = Σxy − Σx·Σy/n` over `d`, rounded once; NULL without pairs
or for a sample of one; NaN for a NaN or an infinity. -/
def covOf (sample : Bool) (vs : List Value) : Value :=
  let ps := pairsOf vs
  if ps.isEmpty || (sample && ps.length == 1) then .null else
    match nonFinite (pairCodes ps) with
    | some _ => .float FloatCode.nan
    | none =>
      let d := if sample then ps.length - 1 else ps.length
      .float (FloatCode.ofExactDiv (coComomentNum ps) (ps.length * d * 2 ^ 1074))

/-- `CORR` of the pairs among `vs`, D30: `C / √(Sxx · Syy)` rounded once,
with `C`'s sign: its magnitude is `√(C² / (Sxx · Syy))` rounded to the grid
(`sqrtMag`, which compares squares, no square root computed), at most `1`
(Cauchy–Schwarz; the `min` states it). NULL for fewer than two pairs or a
side whose values are all equal (its co-moment is `0`, as `corrOf` gave
before D30); NaN for a NaN or an infinity. -/
def corrOf (vs : List Value) : Value :=
  let ps := pairsOf vs
  let nx := comomentNum (ps.map (·.1))
  let ny := comomentNum (ps.map (·.2))
  if ps.length < 2 || nx == 0 || ny == 0 then .null else
    match nonFinite (pairCodes ps) with
    | some _ => .float FloatCode.nan
    | none =>
      let c := coComomentNum ps
      let m := min (FloatCode.sqrtMag (c.natAbs * c.natAbs * 2 ^ 2148) (nx * ny).toNat) (2 ^ 1074)
      .float (if c < 0 then -FloatCode.posCode m else FloatCode.posCode m)

theorem pairsOf_perm {vs ws : List Value} (h : vs.Perm ws) : (pairsOf vs).Perm (pairsOf ws) :=
  h.filterMap _

/-- D30: a variance is a function of the multiset of values. -/
theorem varOf_perm (sample sqrt : Bool) {vs ws : List Value} (h : vs.Perm ws) :
    varOf sample sqrt vs = varOf sample sqrt ws := by
  have hi : ((floatsOf vs).map FloatCode.canon).Perm ((floatsOf ws).map FloatCode.canon) :=
    (h.filterMap _).map _
  simp only [varOf, h.length_eq, nonFinite_perm h, comomentNum_perm hi, hi.length_eq]

theorem covOf_perm (sample : Bool) {vs ws : List Value} (h : vs.Perm ws) :
    covOf sample vs = covOf sample ws := by
  have hp := pairsOf_perm h
  have hc : (pairCodes (pairsOf vs)).Perm (pairCodes (pairsOf ws)) := hp.flatMap_right _
  simp only [covOf, hp.length_eq, hp.isEmpty_eq, nonFinite_perm hc, coComomentNum_perm hp]

theorem corrOf_perm {vs ws : List Value} (h : vs.Perm ws) : corrOf vs = corrOf ws := by
  have hp := pairsOf_perm h
  have hc : (pairCodes (pairsOf vs)).Perm (pairCodes (pairsOf ws)) := hp.flatMap_right _
  simp only [corrOf, hp.length_eq, nonFinite_perm hc, coComomentNum_perm hp,
    comomentNum_perm (hp.map _)]

/-- The element `pick` keeps from each pair, from the left. -/
def pickFold (pick : Value → Value → Bool) (v : Value) (vs : List Value) : Value :=
  vs.foldl (fun a b => if pick a b then b else a) v

/-- The values in the order of `ORDER BY` (`Value.le`), tied doubles by
their codes (`Value.leT`), so the order doesn't depend on the input's. -/
def sortVals (vs : List Value) : List Value := vs.mergeSort fun a b => a.leT b

/-- The 0-based position of `QUANTILE_DISC`'s value among `n` values in order,
for `q = num / 10 ^ scale`: `⌈n·q⌉ − 1`, and the first for `n·q ≤ 1`. -/
def discIndex (n num scale : Nat) : Nat := (n * num + 10 ^ scale - 1) / 10 ^ scale - 1

/-- The code at position `i` of `s`, if it is a double. -/
def intAt (s : List Value) (i : Nat) : Option Int :=
  match s[i]? with
  | some (.float c) => some c
  | _ => none

/-- `QUANTILE_CONT`'s neighbours among the doubles `s` in order, for
`q = num / 10 ^ scale`: the codes at positions `⌊(n−1)·q⌋` and `⌈(n−1)·q⌉`
(the same one where `(n−1)·q` is a whole number), and the weight of the
upper one, `frac((n−1)·q)`, as a double. None if either is not a double. -/
def contNeighbours (num scale : Nat) (s : List Value) : Option (Int × Int × Int) :=
  let d := 10 ^ scale
  let p := (s.length - 1) * num
  (intAt s (p / d)).bind fun l =>
    if p % d == 0 then some (l, l, 0) else
    (intAt s (p / d + 1)).map fun h =>
      (l, h, FloatCode.fdiv (FloatCode.ofInt (p % d)) (FloatCode.ofInt d))

/-- `l·(1 − w) + h·w` with native doubles, as DuckDB interpolates doubles,
kept between `l` and `h` in the order of canonical codes (`ORDER BY`'s,
D31): rounding may leave them by an ulp. `−∞` with `+∞` gives NaN, which
the clamp makes `+∞`; the reference raises there (`AggFn.makesNan`, #561),
so no verified plan sees that value
(`characterization/duckdb/facts/duckdb-quantile-cont-interpolation.json`). -/
def interpolate (l h w : Int) : Int :=
  let r := FloatCode.fadd (FloatCode.fmul l (FloatCode.fsub (FloatCode.ofInt 1) w))
    (FloatCode.fmul h w)
  if FloatCode.canon r < FloatCode.canon l then l
  else if FloatCode.canon h < FloatCode.canon r then h else r

/-- `QUANTILE_CONT` of the doubles `s` in order. -/
def contValue (num scale : Nat) (s : List Value) : Value :=
  match contNeighbours num scale s with
  | some (l, h, w) => if l == h then .float l else .float (interpolate l h w)
  | none => .null

/-- What `QUANTILE_CONT` of the doubles `s` in order may give: NULL without
neighbours, else a double between them. -/
def contAllowed (num scale : Nat) (s : List Value) (v : Value) : Prop :=
  match contNeighbours num scale s with
  | some (l, h, _) => ∃ c, v = .float c ∧
      (c = l ∨ c = h ∨ (FloatCode.canon l ≤ FloatCode.canon c ∧ FloatCode.canon c ≤ FloatCode.canon h))
  | none => v = .null

/-- The most frequent of `vs`, the first of those that tie. -/
def modeOf (v : Value) (vs : List Value) : Value :=
  pickFold (fun a b => (v :: vs).count a < (v :: vs).count b) v (dedup (v :: vs))

def AggFn.apply : AggFn → List Value → Value
  | .count, vs => .int vs.length
  | .bbox n, vs => BlackBox.callAgg n vs
  | _, [] => .null
  | .sum, vs => sumOf vs
  -- D25: the exact sum, and the exact mean, rounded once (`FloatExact.lean`).
  | .fsum, vs => .float (floatSumCR vs)
  | .avg, vs => .float (floatAvgCR vs)
  | .iavg, vs => .int (clampInts vs ((intSum vs).tdiv vs.length))
  | .bit op, vs => .int (bitFold op vs)
  | .var sample sqrt, vs => varOf sample sqrt vs
  | .cov sample, vs => covOf sample vs
  | .corr, vs => corrOf vs
  | .min, v :: vs => pickFold (fun a b => !a.leT b) v vs
  | .max, v :: vs => pickFold (fun a b => !a.geT b) v vs
  | .collect, vs => .list vs
  | .pick last, v :: vs => if last then (v :: vs).getLast (List.cons_ne_nil _ _) else v
  | .concat sep, vs => .str (sep.intercalate (vs.map fun | .str s => s | _ => ""))
  | .quantile false num scale, vs =>
    (sortVals vs).getD (discIndex vs.length num scale) .null
  | .quantile true num scale, vs => contValue num scale (sortVals vs)
  | .mode, v :: vs => modeOf v vs

/-- `collect` takes the rows in its sort order (a stable sort, so without
one in list order: one of the orders an engine may choose). -/
def Measure.eval (rows : Relation) (m : Measure) (I : Impl := Impl.lean) : Value :=
  match m.fn with
  | .collect => AggFn.collect.apply (m.inputs (rows.mergeSort (sortLe m.sort)) I)
  | .pick last => (AggFn.pick last).apply (m.inputs (rows.mergeSort (sortLe m.sort)) I)
  | .concat sep => (AggFn.concat sep).apply (m.inputs (rows.mergeSort (sortLe m.sort)) I)
  | .mode => AggFn.mode.apply (m.inputs (rows.mergeSort (sortLe m.sort)) I)
  | f => f.apply (m.inputs rows I)

/-- Does the aggregate take its rows in the measure's `sort` order? -/
def AggFn.sorts : AggFn → Bool
  | .collect | .pick _ | .concat _ | .mode => true
  | _ => false

theorem Measure.eval_eq {m : Measure} (h : m.fn.sorts = false) (rows : Relation) :
    m.eval rows = m.fn.apply (m.inputs rows) := by
  unfold Measure.eval; split <;> simp_all [AggFn.sorts]

/-! ## Groups -/

def groupKey (gs : List Expr) (row : Row) (I : Impl := Impl.lean) : Row := gs.map (·.eval row I)

/-- The rows of the group with key `k`: keys are equal up to canonical codes
(D31). -/
def groupRows (gs : List Expr) (rows : Relation) (k : Row) (I : Impl := Impl.lean) : Relation :=
  rows.filter fun row => (groupKey gs row I).canon == k.canon

/-- `GROUP BY gs` with the measures `ms`, the functions of `I` (Lean's by
default) in the keys and the measures' arguments. -/
def aggregateEval (gs : List Expr) (ms : List Measure) (rows : Relation)
    (I : Impl := Impl.lean) : Relation :=
  if gs.isEmpty then [ms.map (·.eval rows I)]
  else (distinctRows (rows.map fun row => groupKey gs row I)).map fun k =>
    k ++ ms.map (·.eval (groupRows gs rows k I) I)

/-- The groups, one per output row. -/
def aggGroups (gs : List Expr) (rows : Relation) : List Relation :=
  if gs.isEmpty then [rows] else (distinctRows (rows.map (groupKey gs))).map (groupRows gs rows)

/-! ## Lemmas -/

theorem pickFold_mem (pick : Value → Value → Bool) :
    ∀ (v : Value) (vs : List Value), pickFold pick v vs ∈ v :: vs
  | v, [] => by simp [pickFold]
  | v, w :: vs => by
    have := pickFold_mem pick (if pick v w then w else v) vs
    simp only [pickFold, List.foldl_cons, List.mem_cons] at this ⊢
    by_cases hp : pick v w = true
    · simp only [hp, ↓reduceIte] at this ⊢; rcases this with h | h <;> simp [h]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at this ⊢; rcases this with h | h <;> simp [h]

theorem Measure.mem_inputs {m : Measure} {rows : Relation} {v : Value} (h : v ∈ m.inputs rows) :
    v ≠ .null ∧ ∃ row ∈ rows, m.arg.eval row = v := by
  have h' : v ∈ ((m.kept rows).map m.arg.eval).filter (· != .null) := by
    unfold inputs at h; split at h
    · exact canonReps_sub h
    · exact h
  simp only [List.mem_filter, List.mem_map, bne_iff_ne, ne_eq] at h'
  obtain ⟨⟨row, hrow, rfl⟩, hn⟩ := h'
  refine ⟨hn, row, ?_, rfl⟩
  unfold kept at hrow; split at hrow
  · exact hrow
  · exact (List.mem_filter.mp hrow).1

/-- `MIN` and `MAX` give one of the values (or NULL). -/
theorem AggFn.apply_pick (last : Bool) (vs : List Value) :
    (AggFn.pick last).apply vs = .null ∨ (AggFn.pick last).apply vs ∈ vs := by
  cases vs with
  | nil => exact .inl rfl
  | cons v vs =>
    refine .inr ?_
    cases last
    · simp [apply]
    · simp only [apply, ite_true]; exact List.getLast_mem _

theorem AggFn.apply_minmax {f : AggFn} (hf : f = .min ∨ f = .max) {vs : List Value} :
    f.apply vs = .null ∨ f.apply vs ∈ vs := by
  rcases hf with rfl | rfl <;> cases vs <;>
    first | (simp [apply]; done) | (simp only [apply]; exact .inr (pickFold_mem _ _ _))

theorem intAt_mem {s : List Value} {i : Nat} {c : Int} (h : intAt s i = some c) :
    .float c ∈ s := by
  unfold intAt at h
  split at h
  · rename_i c' heq; cases h; exact List.mem_of_getElem? heq
  · cases h

theorem contNeighbours_mem {num scale : Nat} {s : List Value} {l h w : Int}
    (hn : contNeighbours num scale s = some (l, h, w)) : .float l ∈ s ∧ .float h ∈ s := by
  unfold contNeighbours at hn
  cases h1 : intAt s ((s.length - 1) * num / 10 ^ scale) with
  | none => simp [h1] at hn
  | some l' =>
    simp only [h1, Option.bind_some] at hn
    split at hn
    · cases hn; exact ⟨intAt_mem h1, intAt_mem h1⟩
    · cases h2 : intAt s ((s.length - 1) * num / 10 ^ scale + 1) with
      | none => simp [h2] at hn
      | some h' =>
        simp only [h2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl, -⟩ := hn
        exact ⟨intAt_mem h1, intAt_mem h2⟩

theorem interpolate_between (l h w : Int) :
    interpolate l h w = l ∨ interpolate l h w = h ∨
      (FloatCode.canon l ≤ FloatCode.canon (interpolate l h w) ∧
        FloatCode.canon (interpolate l h w) ≤ FloatCode.canon h) := by
  unfold interpolate
  generalize FloatCode.fadd _ _ = r
  by_cases h1 : FloatCode.canon r < FloatCode.canon l
  · exact .inl (by simp only [h1, ↓reduceIte])
  · by_cases h2 : FloatCode.canon h < FloatCode.canon r
    · exact .inr (.inl (by simp only [h1, h2, ↓reduceIte]))
    · refine .inr (.inr ?_)
      simp only [h1, h2, ↓reduceIte]; omega

theorem contValue_allowed (num scale : Nat) (s : List Value) :
    contAllowed num scale s (contValue num scale s) := by
  unfold contAllowed contValue
  cases contNeighbours num scale s with
  | none => rfl
  | some t =>
    obtain ⟨l, h, w⟩ := t
    dsimp only
    split
    · exact ⟨l, rfl, .inl rfl⟩
    · exact ⟨_, rfl, interpolate_between l h w⟩

/-- `QUANTILE_CONT` gives NULL or a double between two of the values. -/
theorem AggFn.apply_cont (num scale : Nat) (vs : List Value) :
    (AggFn.quantile true num scale).apply vs = .null ∨ ∃ c l h,
      (AggFn.quantile true num scale).apply vs = .float c ∧ .float l ∈ vs ∧ .float h ∈ vs ∧
        (c = l ∨ c = h ∨ (FloatCode.canon l ≤ FloatCode.canon c ∧ FloatCode.canon c ≤ FloatCode.canon h)) := by
  cases vs with
  | nil => exact .inl rfl
  | cons v vs =>
    have hp := List.mergeSort_perm (v :: vs) (fun a b => a.leT b)
    have ha := contValue_allowed num scale (sortVals (v :: vs))
    show contValue num scale (sortVals (v :: vs)) = .null ∨ ∃ c l h,
      contValue num scale (sortVals (v :: vs)) = .float c ∧ _
    unfold contAllowed at ha
    cases hn : contNeighbours num scale (sortVals (v :: vs)) with
    | none => rw [hn] at ha; exact .inl ha
    | some t =>
      obtain ⟨l, h, w⟩ := t
      rw [hn] at ha
      obtain ⟨c, hc, hb⟩ := ha
      obtain ⟨hl, hh⟩ := contNeighbours_mem hn
      exact .inr ⟨c, l, h, hc, hp.mem_iff.mp hl, hp.mem_iff.mp hh, hb⟩

/-- `QUANTILE_DISC` gives one of the values (or NULL). -/
theorem AggFn.apply_disc (num scale : Nat) (vs : List Value) :
    (AggFn.quantile false num scale).apply vs = .null ∨
      (AggFn.quantile false num scale).apply vs ∈ vs := by
  cases vs with
  | nil => exact .inl rfl
  | cons v vs =>
    show (sortVals (v :: vs)).getD _ .null = .null ∨ (sortVals (v :: vs)).getD _ .null ∈ v :: vs
    rw [List.getD_eq_getElem?_getD]
    cases h : (sortVals (v :: vs))[discIndex (v :: vs).length num scale]? with
    | none => exact .inl rfl
    | some w =>
      exact .inr ((List.mergeSort_perm (v :: vs) (fun a b => a.leT b)).mem_iff.mp
        (List.mem_of_getElem? h))

/-- `MODE` gives one of the values (or NULL). -/
theorem AggFn.apply_mode (vs : List Value) : AggFn.mode.apply vs = .null ∨ AggFn.mode.apply vs ∈ vs := by
  cases vs with
  | nil => exact .inl rfl
  | cons v vs =>
    refine .inr ?_
    show modeOf v vs ∈ v :: vs
    have hm : modeOf v vs ∈ v :: dedup (v :: vs) := pickFold_mem _ _ _
    rcases List.mem_cons.mp hm with h | h
    · rw [h]; exact List.mem_cons_self ..
    · exact mem_dedup.mp h

theorem foldl_min_le : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, xs.foldl min x ≤ y
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    have ih := foldl_min_le (min x z) zs
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact Int.le_trans (ih _ (List.mem_cons_self ..)) (Int.min_le_left _ _)
    · exact Int.le_trans (ih _ (List.mem_cons_self ..)) (Int.min_le_right _ _)
    · exact ih y (by simp [hy])

theorem foldl_max_ge : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, y ≤ xs.foldl max x
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    have ih := foldl_max_ge (max x z) zs
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · exact Int.le_trans (Int.le_max_left _ _) (ih _ (List.mem_cons_self ..))
    · exact Int.le_trans (Int.le_max_right _ _) (ih _ (List.mem_cons_self ..))
    · exact ih y (by simp [hy])

theorem foldl_min_mem : ∀ (x : Int) (xs : List Int), xs.foldl min x ∈ x :: xs
  | x, [] => by simp
  | x, z :: zs => by
    simp only [List.foldl_cons]
    have := foldl_min_mem (min x z) zs
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rw [h]; rcases Int.le_total x z with hxz | hxz
      · exact .inl (Int.min_eq_left hxz)
      · exact .inr (.inl (Int.min_eq_right hxz))
    · exact .inr (.inr h)

theorem foldl_max_mem : ∀ (x : Int) (xs : List Int), xs.foldl max x ∈ x :: xs
  | x, [] => by simp
  | x, z :: zs => by
    simp only [List.foldl_cons]
    have := foldl_max_mem (max x z) zs
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rw [h]; rcases Int.le_total x z with hxz | hxz
      · exact .inr (.inl (Int.max_eq_right hxz))
      · exact .inl (Int.max_eq_left hxz)
    · exact .inr (.inr h)

theorem mem_intsOf {vs : List Value} {c : Int} : c ∈ intsOf vs ↔ .int c ∈ vs := by
  simp only [intsOf, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, h⟩; cases v <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

/-- A clamped value lies between two of the integers. -/
theorem clampInts_between {vs : List Value} (hne : intsOf vs ≠ []) (c : Int) :
    (∃ l ∈ intsOf vs, l ≤ clampInts vs c) ∧ (∃ h ∈ intsOf vs, clampInts vs c ≤ h) := by
  unfold clampInts
  split
  · contradiction
  · rename_i x xs hx
    rw [hx]
    have hl := foldl_min_le x xs (xs.foldl max x) (foldl_max_mem x xs)
    refine ⟨⟨_, foldl_min_mem x xs, ?_⟩, ⟨_, foldl_max_mem x xs, Int.min_le_right _ _⟩⟩
    exact Int.le_min.2 ⟨Int.le_max_right _ _, hl⟩

/-- `AVG` of integers with an integer result, of values with an integer among
them, lies between two of them. -/
theorem AggFn.apply_iavg_between {vs : List Value} (hne : intsOf vs ≠ []) :
    ∃ a, AggFn.iavg.apply vs = .int a ∧
      (∃ l ∈ intsOf vs, l ≤ a) ∧ (∃ h ∈ intsOf vs, a ≤ h) := by
  cases vs with
  | nil => simp [intsOf] at hne
  | cons v vs => exact ⟨_, rfl, clampInts_between hne _⟩

theorem Value.le_refl (a : Value) : a.le a = true := by
  rcases Value.le_total a a with h | h <;> exact h

/-- `m` is the least element of `l` in the order `le`. -/
def IsLeast {α : Type} (le : α → α → Bool) (m : α) (l : List α) : Prop :=
  m ∈ l ∧ ∀ w ∈ l, le m w = true

theorem pickFold_least {le : Value → Value → Bool} (hle : TotalPre le) :
    ∀ (v : Value) (vs : List Value), IsLeast le (pickFold (fun a b => !le a b) v vs) (v :: vs)
  | v, [] => ⟨by simp [pickFold], fun w hw => by simp at hw; subst hw; exact hle.refl _⟩
  | v, w :: vs => by
    show IsLeast le (pickFold (fun a b => !le a b) (if (!le v w) = true then w else v) vs) (v :: w :: vs)
    by_cases hp : le v w = true
    · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hm, hl⟩ := pickFold_least hle v vs
      refine ⟨?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hm with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact hl _ (by simp)
        · exact hle.trans _ _ _ (hl v (by simp)) hp
        · exact hl x (by simp [hx])
    · have hwv : le w v = true := by
        have := hle.total v w; simp only [hp, Bool.false_or] at this; exact this
      have hp' : le v w = false := by simpa using hp
      simp only [hp', Bool.not_false, ↓reduceIte]
      obtain ⟨hm, hl⟩ := pickFold_least hle w vs
      refine ⟨List.mem_cons_of_mem _ hm, fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hle.trans _ _ _ (hl w (by simp)) hwv
      · exact hl _ (by simp)
      · exact hl x (by simp [hx])

theorem pickFold_min_le (v : Value) (vs : List Value) : ∀ x ∈ v :: vs,
    (pickFold (fun a b => !a.leT b) v vs).le x = true := fun x hx =>
  Value.le_of_leT ((pickFold_least Value.leT_totalPre v vs).2 x hx)

theorem pickFold_max_ge (v : Value) (vs : List Value) : ∀ x ∈ v :: vs,
    x.le (pickFold (fun a b => !a.geT b) v vs) = true := fun x hx =>
  Value.le_of_geT ((pickFold_least Value.geT_totalPre v vs).2 x hx)

/-- `MIN` of values is one of them, and at most each of them. -/
theorem AggFn.apply_min {vs : List Value} {m : Value} (h : AggFn.min.apply vs = m) (hm : m ≠ .null) :
    m ∈ vs ∧ ∀ x ∈ vs, m.le x = true := by
  cases vs with
  | nil => simp [apply] at h; exact absurd h.symm hm
  | cons v vs =>
    simp only [apply] at h; subst h
    exact ⟨pickFold_mem _ _ _, pickFold_min_le v vs⟩

/-- `MAX` of values is one of them, and at least each of them. -/
theorem AggFn.apply_max {vs : List Value} {m : Value} (h : AggFn.max.apply vs = m) (hm : m ≠ .null) :
    m ∈ vs ∧ ∀ x ∈ vs, x.le m = true := by
  cases vs with
  | nil => simp [apply] at h; exact absurd h.symm hm
  | cons v vs =>
    simp only [apply] at h; subst h
    exact ⟨pickFold_mem _ _ _, pickFold_max_ge v vs⟩

theorem Value.le_int {x y : Int} : (Value.int x).le (.int y) = true ↔ x ≤ y :=
  Value.le_val .int

/-- Two measures of the same argument and filter aggregate the same values,
up to canonical codes (`DISTINCT` keeps one member of each class). -/
theorem Measure.mem_inputs_canon {m m' : Measure} (ha : m.arg = m'.arg) (hf : m.filter = m'.filter)
    {rows : Relation} {v : Value} (hv : v ∈ m.inputs rows) :
    ∃ w ∈ m'.inputs rows, w.canonV = v.canonV := by
  have hk : m.kept rows = m'.kept rows := by simp only [Measure.kept, hf]
  have hv' : v ∈ ((m'.kept rows).map m'.arg.eval).filter (· != .null) := by
    unfold Measure.inputs at hv; rw [hk, ha] at hv; split at hv
    · exact canonReps_sub hv
    · exact hv
  unfold Measure.inputs; split
  · exact ⟨_, classRep_mem_canonReps hv', classRep_canon _ _⟩
  · exact ⟨v, hv', rfl⟩

theorem mem_aggregateEval {gs : List Expr} {ms : List Measure} {rows : Relation} {row : Row}
    (h : row ∈ aggregateEval gs ms rows) :
    ∃ k grp, row = k ++ ms.map (·.eval grp) ∧ (∀ y ∈ grp, y ∈ rows) ∧
      ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k = groupKey gs x) := by
  unfold aggregateEval at h
  split at h
  · rename_i hg
    simp only [List.mem_singleton] at h
    exact ⟨[], rows, by simp [h], fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩⟩
  · simp only [List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
    exact ⟨_, _, rfl, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, rfl⟩⟩

/-- `mem_aggregateEval`, and with a grouping, the group has a row. -/
theorem mem_aggregateEval_nonempty {gs : List Expr} {ms : List Measure} {rows : Relation}
    {row : Row} (h : row ∈ aggregateEval gs ms rows) :
    ∃ k grp, row = k ++ ms.map (·.eval grp) ∧ (∀ y ∈ grp, y ∈ rows) ∧
      ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k = groupKey gs x) ∧ (gs ≠ [] → grp ≠ []) := by
  unfold aggregateEval at h
  split at h
  · rename_i hg
    simp only [List.mem_singleton] at h
    exact ⟨[], rows, by simp [h], fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩,
      fun hne => absurd (List.isEmpty_iff.mp hg) hne⟩
  · simp only [List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
    refine ⟨_, _, rfl, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, rfl⟩, fun _ => ?_⟩
    exact List.ne_nil_of_mem (a := x) (List.mem_filter.mpr ⟨hx, by simp⟩)

/-- `mem_aggregateEval_nonempty`, with the group no longer than the input. -/
theorem mem_aggregateEval_len {gs : List Expr} {ms : List Measure} {rows : Relation}
    {row : Row} (h : row ∈ aggregateEval gs ms rows) :
    ∃ k grp, row = k ++ ms.map (·.eval grp) ∧ (∀ y ∈ grp, y ∈ rows) ∧
      ((gs = [] ∧ k = []) ∨ ∃ x ∈ rows, k = groupKey gs x) ∧ (gs ≠ [] → grp ≠ []) ∧
      grp.length ≤ rows.length := by
  unfold aggregateEval at h
  split at h
  · rename_i hg
    simp only [List.mem_singleton] at h
    exact ⟨[], rows, by simp [h], fun _ hy => hy, .inl ⟨List.isEmpty_iff.mp hg, rfl⟩,
      fun hne => absurd (List.isEmpty_iff.mp hg) hne, Nat.le_refl _⟩
  · simp only [List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (canonReps_sub hk)
    refine ⟨_, _, rfl, fun y hy => (List.mem_filter.mp hy).1, .inr ⟨x, hx, rfl⟩, fun _ => ?_,
      List.length_filter_le _ _⟩
    exact List.ne_nil_of_mem (a := x) (List.mem_filter.mpr ⟨hx, by simp⟩)

theorem ints_map_intsOf : ∀ {vs : List Value}, (∀ w ∈ vs, ∃ i, w = .int i) →
    vs = (intsOf vs).map .int
  | [], _ => rfl
  | v :: vs, h => by
    obtain ⟨i, rfl⟩ := h v (by simp)
    simp only [intsOf, List.filterMap_cons, List.map_cons]
    exact congrArg _ (ints_map_intsOf fun w hw => h w (by simp [hw]))

theorem Measure.inputs_length_le (m : Measure) (rows : Relation) :
    (m.inputs rows).length ≤ rows.length := by
  have hk : (m.kept rows).length ≤ rows.length := by
    unfold Measure.kept; split
    · exact Nat.le_refl _
    · exact List.length_filter_le _ _
  have hf : (((m.kept rows).map m.arg.eval).filter (· != .null)).length ≤ rows.length :=
    Nat.le_trans (List.length_filter_le _ _) (by simpa using hk)
  unfold Measure.inputs; split
  · exact Nat.le_trans (canonReps_length_le _) hf
  · exact hf

theorem aggregateEval_length {gs : List Expr} {ms : List Measure} {rows : Relation} {row : Row}
    (h : row ∈ aggregateEval gs ms rows) : row.length = gs.length + ms.length := by
  obtain ⟨k, grp, rfl, _, hk⟩ := mem_aggregateEval h
  rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]

end Substrait
