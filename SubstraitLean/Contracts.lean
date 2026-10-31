import SubstraitLean.Rel

/-!
# Pre- and postconditions: a verified abstract interpreter

Data scientists state **preconditions** about input rows ("`amount ≥ 0`",
"`id` is not NULL") and **postconditions** about output rows. Postconditions are
proved, not tested: `Rel.aeval` computes, for every column of a plan's output,
an over-approximation (`AVal`) of the values it can hold. It tracks
whether a column can be NULL, an integer range, the possible booleans and
whether it can be a string. A postcondition holds when its column is
*certainly TRUE*.

* `Expr.abs_sound`: abstract expression evaluation is sound.
* `Expr.refine_sound`: a row that passes a filter satisfies what the filter
  condition says about it (`amount > 10` ⇒ `amount` is a non-NULL int ≥ 11).
* `Rel.aeval_sound`: every row a plan produces is described by `Rel.aeval`.
* `contract_sound`: if every postcondition column is certainly TRUE under the
  preconditions, then every output row satisfies every postcondition.
-/

namespace Substrait

/-! ## Integer intervals -/

/-- An integer interval; a `none` bound is infinite. -/
structure Bound where
  lo : Option Int
  hi : Option Int
  deriving Repr, BEq, DecidableEq

def Bound.Mem (b : Bound) (i : Int) : Prop :=
  (∀ l, b.lo = some l → l ≤ i) ∧ (∀ h, b.hi = some h → i ≤ h)

def Bound.top : Bound := ⟨none, none⟩
def Bound.exact (i : Int) : Bound := ⟨some i, some i⟩

def lift2 (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | some a, some b => some (f a b)
  | _, _ => none

def Bound.join (a b : Bound) : Bound := ⟨lift2 min a.lo b.lo, lift2 max a.hi b.hi⟩
def Bound.add (a b : Bound) : Bound := ⟨lift2 (· + ·) a.lo b.lo, lift2 (· + ·) a.hi b.hi⟩
def Bound.neg (a : Bound) : Bound := ⟨a.hi.map (- ·), a.lo.map (- ·)⟩
def Bound.sub (a b : Bound) : Bound := a.add b.neg

def Bound.scale (k : Int) (b : Bound) : Bound :=
  if k = 0 then Bound.exact 0
  else if 0 ≤ k then ⟨b.lo.map (k * ·), b.hi.map (k * ·)⟩ else ⟨b.hi.map (k * ·), b.lo.map (k * ·)⟩

/-- The single value of a one-point interval. -/
def Bound.point (b : Bound) : Option Int :=
  match b.lo, b.hi with
  | some l, some h => if l = h then some l else none
  | _, _ => none

/-- The products of the corners of two finite intervals. -/
def Bound.corners (al ah bl bh : Int) : Bound :=
  ⟨some (min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh))),
   some (max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)))⟩

/-- Multiplication: exact scaling by a constant, the corner products of two
finite intervals, and otherwise unbounded. -/
def Bound.mul (a b : Bound) : Bound :=
  match a.point, b.point with
  | some k, _ => b.scale k
  | none, some k => a.scale k
  | none, none => match a.lo, a.hi, b.lo, b.hi with
    | some al, some ah, some bl, some bh => Bound.corners al ah bl bh
    | _, _, _, _ => Bound.top

def Bound.atMost (b : Bound) (k : Int) : Bound :=
  ⟨b.lo, some (match b.hi with | some h => min h k | none => k)⟩

def Bound.atLeast (b : Bound) (k : Int) : Bound :=
  ⟨some (match b.lo with | some l => max l k | none => k), b.hi⟩

theorem Bound.mem_top (i : Int) : Bound.top.Mem i := by simp [Bound.Mem, Bound.top]

theorem Bound.mem_exact (i : Int) : (Bound.exact i).Mem i := by
  simp [Bound.Mem, Bound.exact]

theorem Bound.mem_join_left {a b : Bound} {i : Int} (h : a.Mem i) : (a.join b).Mem i := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.join] at *
  constructor
  · intro l hl; cases al <;> cases bl <;> simp_all [lift2] <;> subst hl <;> omega
  · intro u hu; cases ah <;> cases bh <;> simp_all [lift2] <;> subst hu <;> omega

theorem Bound.mem_join_right {a b : Bound} {i : Int} (h : b.Mem i) : (a.join b).Mem i := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.join] at *
  constructor
  · intro l hl; cases al <;> cases bl <;> simp_all [lift2] <;> subst hl <;> omega
  · intro u hu; cases ah <;> cases bh <;> simp_all [lift2] <;> subst hu <;> omega

theorem Bound.mem_add {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.add b).Mem (x + y) := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.add] at *
  constructor
  · intro l hl; cases al <;> cases bl <;> simp_all [lift2] <;> omega
  · intro u hu; cases ah <;> cases bh <;> simp_all [lift2] <;> omega

theorem Bound.mem_neg {a : Bound} {x : Int} (ha : a.Mem x) : a.neg.Mem (-x) := by
  obtain ⟨al, ah⟩ := a
  simp only [Bound.Mem, Bound.neg] at *
  constructor
  · intro l hl; cases ah <;> simp_all <;> omega
  · intro u hu; cases al <;> simp_all <;> omega

theorem Bound.mem_sub {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.sub b).Mem (x - y) := by
  rw [Int.sub_eq_add_neg]; exact Bound.mem_add ha (Bound.mem_neg hb)

theorem Bound.mem_scale {b : Bound} {x : Int} (k : Int) (hb : b.Mem x) :
    (b.scale k).Mem (k * x) := by
  obtain ⟨hl, hh⟩ := hb
  unfold Bound.scale
  split
  · rename_i hk; subst hk; simpa using Bound.mem_exact 0
  split
  · rename_i _ hk
    refine ⟨fun l h => ?_, fun u h => ?_⟩
    · obtain ⟨l0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonneg_left (hl l0 h0) hk
    · obtain ⟨u0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonneg_left (hh u0 h0) hk
  · rename_i _ hk
    refine ⟨fun l h => ?_, fun u h => ?_⟩
    · obtain ⟨u0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonpos_left (by omega) (hh u0 h0)
    · obtain ⟨l0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonpos_left (by omega) (hl l0 h0)

theorem Bound.point_mem {b : Bound} {k x : Int} (hp : b.point = some k) (hb : b.Mem x) : x = k := by
  obtain ⟨bl, bh⟩ := b
  cases bl <;> cases bh <;> simp [Bound.point] at hp
  simp [Bound.Mem] at hb
  omega

/-- `x * y` lies between the products of `x`'s bounds with `y`. -/
theorem mul_between {l h x : Int} (hl : l ≤ x) (hh : x ≤ h) (y : Int) :
    min (l * y) (h * y) ≤ x * y ∧ x * y ≤ max (l * y) (h * y) := by
  rcases Int.le_total 0 y with hy | hy
  · have := Int.mul_le_mul_of_nonneg_right hl hy
    have := Int.mul_le_mul_of_nonneg_right hh hy
    omega
  · have := Int.mul_le_mul_of_nonpos_right hl hy
    have := Int.mul_le_mul_of_nonpos_right hh hy
    omega

theorem Bound.mem_corners {al ah bl bh x y : Int} (hx : al ≤ x ∧ x ≤ ah) (hy : bl ≤ y ∧ y ≤ bh) :
    (Bound.corners al ah bl bh).Mem (x * y) := by
  have h1 := mul_between hx.1 hx.2 y
  have h2 := mul_between hy.1 hy.2 al
  have h3 := mul_between hy.1 hy.2 ah
  rw [Int.mul_comm y al, Int.mul_comm bl al, Int.mul_comm bh al] at h2
  rw [Int.mul_comm y ah, Int.mul_comm bl ah, Int.mul_comm bh ah] at h3
  simp only [Bound.Mem, Bound.corners, Option.some.injEq]
  constructor
  · rintro _ rfl; omega
  · rintro _ rfl; omega

theorem Bound.mem_mul {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.mul b).Mem (x * y) := by
  unfold Bound.mul
  match hpa : a.point, hpb : b.point with
  | some k, _ => simp only []; rw [Bound.point_mem hpa ha]; exact Bound.mem_scale k hb
  | none, some k =>
    simp only []; rw [Bound.point_mem hpb hb, Int.mul_comm]; exact Bound.mem_scale k ha
  | none, none =>
    simp only []
    obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
    match al, ah, bl, bh with
    | some al, some ah, some bl, some bh =>
      exact Bound.mem_corners ⟨ha.1 al rfl, ha.2 ah rfl⟩ ⟨hb.1 bl rfl, hb.2 bh rfl⟩
    | none, _, _, _ | some _, none, _, _ | some _, some _, none, _ | some _, some _, some _, none =>
      exact Bound.mem_top _

theorem Bound.mem_atMost {b : Bound} {x k : Int} (hb : b.Mem x) (hk : x ≤ k) :
    (b.atMost k).Mem x := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.atMost] at *
  refine ⟨hb.1, ?_⟩
  intro u hu; cases bh <;> simp_all <;> omega

theorem Bound.mem_atLeast {b : Bound} {x k : Int} (hb : b.Mem x) (hk : k ≤ x) :
    (b.atLeast k).Mem x := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.atLeast] at *
  refine ⟨?_, hb.2⟩
  intro l hl; cases bl <;> simp_all <;> omega

/-- Intersection of two intervals. -/
def Bound.meet (a b : Bound) : Bound :=
  let pick (f : Int → Int → Int) : Option Int → Option Int → Option Int
    | some x, some y => some (f x y)
    | some x, none => some x
    | none, y => y
  ⟨pick max a.lo b.lo, pick min a.hi b.hi⟩

theorem Bound.mem_meet {a b : Bound} {i : Int} (ha : a.Mem i) (hb : b.Mem i) : (a.meet b).Mem i := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.meet] at *
  constructor
  · intro l hl; cases al <;> cases bl <;> simp_all <;> omega
  · intro u hu; cases ah <;> cases bh <;> simp_all <;> omega

/-! ## Abstract values -/

/-- The set of values a column may hold. -/
structure AVal where
  /-- may be NULL -/
  null : Bool
  /-- may be an integer, within this interval -/
  int : Option Bound
  /-- may be TRUE -/
  tt : Bool
  /-- may be FALSE -/
  ff : Bool
  /-- may be a string -/
  str : Bool
  deriving Repr, BEq

def AVal.Mem (a : AVal) : Value → Prop
  | .null => a.null = true
  | .int i => ∃ b, a.int = some b ∧ b.Mem i
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .str _ => a.str = true
  -- The abstraction does not look into lists: a list is a member where the
  -- booleans and strings are. Functions of one type give NULL on the others,
  -- so each abstraction covers a list as it covers a value of another type.
  | .list _ => a.tt = true ∧ a.ff = true ∧ a.str = true

def AVal.top : AVal := ⟨true, some Bound.top, true, true, true⟩
def AVal.bot : AVal := ⟨false, none, false, false, false⟩

def AVal.ofValue : Value → AVal
  | .null => ⟨true, none, false, false, false⟩
  | .int i => ⟨false, some (.exact i), false, false, false⟩
  | .bool true => ⟨false, none, true, false, false⟩
  | .bool false => ⟨false, none, false, true, false⟩
  | .str _ => ⟨false, none, false, false, true⟩
  | .list _ => ⟨false, none, true, true, true⟩

def joinInt : Option Bound → Option Bound → Option Bound
  | some x, some y => some (x.join y)
  | some x, none => some x
  | none, y => y

def AVal.join (a b : AVal) : AVal :=
  ⟨a.null || b.null, joinInt a.int b.int, a.tt || b.tt, a.ff || b.ff, a.str || b.str⟩

/-- May be something other than a (non-NULL) integer. -/
def AVal.nonInt (a : AVal) : Bool := a.null || a.tt || a.ff || a.str
/-- May be something other than a (non-NULL) boolean. -/
def AVal.nonBool (a : AVal) : Bool := a.null || a.int.isSome || a.str

/-- Certainly TRUE: the only value a satisfied condition can have. -/
def AVal.certainlyTrue (a : AVal) : Bool := !a.null && a.int.isNone && !a.ff && !a.str

theorem AVal.mem_top : ∀ v, AVal.top.Mem v
  | .null | .bool true | .bool false | .str _ => rfl
  | .list _ => by simp [AVal.Mem, AVal.top]
  | .int i => ⟨_, rfl, Bound.mem_top i⟩

theorem AVal.mem_ofValue : ∀ v, (AVal.ofValue v).Mem v
  | .null | .bool true | .bool false | .str _ => rfl
  | .list _ => by simp [AVal.Mem, AVal.ofValue]
  | .int i => ⟨_, rfl, Bound.mem_exact i⟩

theorem AVal.mem_join_left {a b : AVal} : ∀ {v}, a.Mem v → (a.join b).Mem v
  | .null, h | .bool true, h | .bool false, h | .str _, h => by
      simp_all [AVal.Mem, AVal.join]
  | .list _, h => by
      simp only [AVal.Mem, AVal.join] at *
      exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩
  | .int i, ⟨x, hx, hm⟩ => by
      simp only [AVal.Mem, AVal.join, hx]
      cases b.int <;> simp [joinInt, hm, Bound.mem_join_left hm]

theorem AVal.mem_join_right {a b : AVal} : ∀ {v}, b.Mem v → (a.join b).Mem v
  | .null, h | .bool true, h | .bool false, h | .str _, h => by
      simp_all [AVal.Mem, AVal.join]
  | .list _, h => by
      simp only [AVal.Mem, AVal.join] at *
      exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩
  | .int i, ⟨y, hy, hm⟩ => by
      simp only [AVal.Mem, AVal.join, hy]
      cases ha : a.int <;> simp [joinInt, hm, Bound.mem_join_right hm]

theorem AVal.certainlyTrue_mem {a : AVal} {v : Value} (hc : a.certainlyTrue = true)
    (hm : a.Mem v) : v = .bool true := by
  simp only [AVal.certainlyTrue, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hc
  obtain ⟨⟨⟨hn, hi⟩, hf⟩, hs⟩ := hc
  match v, hm with
  | .null, hm => simp_all [AVal.Mem]
  | .int _, ⟨_, hb, _⟩ => simp_all
  | .bool true, _ => rfl
  | .bool false, hm => simp_all [AVal.Mem]
  | .str _, hm | .list _, hm => simp_all [AVal.Mem]

/-! ## Abstract expression evaluation -/

/-! ### Rounding, division and casts -/

/-- The image of an interval under a monotone map. -/
def Bound.mapMono (g : Int → Int) (b : Bound) : Bound := ⟨b.lo.map g, b.hi.map g⟩

theorem Bound.mem_mapMono {g : Int → Int} (hg : ∀ {x y}, x ≤ y → g x ≤ g y) {b : Bound} {i : Int}
    (h : b.Mem i) : (b.mapMono g).Mem (g i) := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.mapMono] at *
  constructor
  · intro l hl
    cases bl with
    | none => simp at hl
    | some l' => simp only [Option.map_some, Option.some.injEq] at hl; subst hl; exact hg (h.1 l' rfl)
  · intro u hu
    cases bh with
    | none => simp at hu
    | some u' => simp only [Option.map_some, Option.some.injEq] at hu; subst hu; exact hg (h.2 u' rfl)

/-- A double rounded by a monotone map (`FLOOR`, `CEIL`, `ROUND`). -/
def monoAbs (g : Int → Int) (a : AVal) : AVal :=
  ⟨a.nonInt, a.int.map (·.mapMono g), false, false, false⟩

/-- `CAST(x AS BIGINT)`: between the casts of the ends, if both are finite;
otherwise it may also fail (NULL here). -/
def ftoiAbs (a : AVal) : AVal :=
  match a.int with
  | some ⟨some lo, some hi⟩ =>
    match FloatCode.toInt? lo, FloatCode.toInt? hi with
    | some x, some y => ⟨a.nonInt, some ⟨some x, some y⟩, false, false, false⟩
    | _, _ => ⟨true, some Bound.top, false, false, false⟩
  | some _ => ⟨true, some Bound.top, false, false, false⟩
  | none => ⟨a.nonInt, none, false, false, false⟩

/-- Does every integer of the interval fit in `bits` bits? -/
def Bound.fitsBits (n : Nat) (b : Bound) : Bool :=
  b.lo.any (-(2 ^ (n - 1) : Int) ≤ ·) && b.hi.any (· < 2 ^ (n - 1))

theorem Bound.fitsBits_mem {n : Nat} {b : Bound} {i : Int} (h : b.fitsBits n = true)
    (hi : b.Mem i) : _root_.Substrait.fitsBits n i = true := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.fitsBits, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨lo, rfl, hlo⟩, ⟨hi', rfl, hhi⟩⟩ := h
  have h1 := hi.1 lo rfl
  have h2 := hi.2 hi' rfl
  simp only [_root_.Substrait.fitsBits, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `CAST(x AS INT)`: the integer itself, or NULL where it may not fit. -/
def narrowAbs (n : Nat) (a : AVal) : AVal :=
  ⟨a.nonInt || a.int.any (!·.fitsBits n), a.int, false, false, false⟩

/-- Can the interval contain 0? -/
def Bound.has0 (b : Bound) : Bool := b.lo.all (· ≤ 0) && b.hi.all (0 ≤ ·)

theorem Bound.ne_zero {b : Bound} {i : Int} (h : b.Mem i) (h0 : b.has0 = false) : i ≠ 0 := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.has0] at *
  rintro rfl
  cases bl <;> cases bh <;> simp_all <;> omega

/-- May an integer drawn from `a` be 0? -/
def AVal.mayZero (a : AVal) : Bool := a.int.all Bound.has0

/-- `[-A, A]` for `A` the largest absolute value in a finite interval. -/
def Bound.absHull (b : Bound) : Bound :=
  match b.lo, b.hi with
  | some l, some h => let A : Int := max l.natAbs h.natAbs; ⟨some (-A), some A⟩
  | _, _ => Bound.top

theorem Bound.mem_absHull {b : Bound} {i j : Int} (h : b.Mem i) (hj : j.natAbs ≤ i.natAbs) :
    b.absHull.Mem j := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.absHull] at *
  cases bl <;> cases bh <;> simp_all [Bound.top]
  rename_i l u
  have := h.1; have := h.2
  constructor <;> omega

/-- Between `min(lo, 0)` and `max(hi, 0)`. -/
def Bound.signHull (b : Bound) : Bound := ⟨b.lo.map (min · 0), b.hi.map (max · 0)⟩

/-- Truncating division: monotone for a positive constant divisor (and
antitone for a negative one), between 0 and the dividend for any positive
divisor, and never larger in absolute value than the dividend. -/
def divBound (x y : Bound) : Bound :=
  match y.point with
  | some k =>
    if 0 < k then x.mapMono (·.tdiv k)
    else if k < 0 then (x.mapMono (·.tdiv (-k))).neg
    else x.absHull
  | none => if y.lo.any (1 ≤ ·) then x.signHull else x.absHull

/-- For a positive divisor, `a / b` lies between 0 and `a`. -/
theorem tdiv_between {a b : Int} (hb : 0 < b) : min a 0 ≤ a.tdiv b ∧ a.tdiv b ≤ max a 0 := by
  rcases Int.le_total 0 a with ha | ha
  · have h₁ := Int.tdiv_nonneg ha (Int.le_of_lt hb)
    have h₂ := Int.tdiv_le_self b ha
    omega
  · have h₁ := Int.tdiv_nonneg (a := -a) (by omega) (Int.le_of_lt hb)
    have h₂ := Int.tdiv_le_self b (a := -a) (by omega)
    rw [Int.neg_tdiv] at h₁ h₂
    omega

/-- The remainder is smaller in absolute value than the divisor, and not
negative for a non-negative dividend. -/
def modBound (x y : Bound) : Bound :=
  let nonneg := x.lo.any (0 ≤ ·)
  match y.lo, y.hi with
  | some l, some h =>
    let M : Int := max l.natAbs h.natAbs - 1
    ⟨some (if nonneg then 0 else -M), some M⟩
  | _, _ => if nonneg then ⟨some 0, none⟩ else Bound.top

/-- Division and remainder: NULL for a NULL operand, and (here) for a zero
divisor, where DataFusion fails. -/
def divAbs (bound : Bound → Bound → Bound) (a b : AVal) : AVal :=
  ⟨a.nonInt || b.nonInt || b.mayZero,
   (match a.int, b.int with | some x, some y => some (bound x y) | _, _ => none), false, false, false⟩

/-- Integer powers: `x²` is not negative; the exponent must be in `[0, 64]`
for a result. -/
def powAbs (a b : AVal) : AVal :=
  let inRange := match b.int with
    | some ⟨some l, some h⟩ => decide (0 ≤ l) && decide (h ≤ 64)
    | _ => false
  let square := match b.int with | some y => y.point == some 2 | none => false
  ⟨a.nonInt || b.nonInt || !inRange,
   (match a.int, b.int with
    | some _, some _ => some (if square then ⟨some 0, none⟩ else Bound.top)
    | _, _ => none), false, false, false⟩

/-- May be something other than a (non-NULL) string. -/
def AVal.nonStr (a : AVal) : Bool := a.null || a.int.isSome || a.tt || a.ff

/-- The interval `[lo, ∞)`. -/
def Bound.ge (lo : Int) : Bound := ⟨some lo, none⟩

/-- `b` cut down to `[lo, hi]`. -/
def Bound.clamp (lo hi : Int) (b : Bound) : Bound :=
  ⟨some (max lo (b.lo.getD lo)), some (min hi (b.hi.getD hi))⟩

theorem Bound.mem_clamp {lo hi i : Int} {b : Bound} (h : b.Mem i) (hl : lo ≤ i) (hh : i ≤ hi) :
    (b.clamp lo hi).Mem i := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.Mem, Bound.clamp] at *
  constructor
  · intro l hl'; simp only [Option.some.injEq] at hl'; subst hl'
    cases bl with
    | none => simpa using hl
    | some x => have := h.1 x rfl; simp only [Option.getD_some]; omega
  · intro u hu; simp only [Option.some.injEq] at hu; subst hu
    cases bh with
    | none => simpa using hh
    | some x => have := h.2 x rfl; simp only [Option.getD_some]; omega

/-- `date_part`: a fixed range, or for the year, the years of the ends of the
timestamps `chrono` represents. -/
def partBound (p : Time.DatePart) (b : Bound) : Bound :=
  match p.range with
  | some (lo, hi) => ⟨some lo, some hi⟩
  | none => (b.clamp Time.partMin Time.partMax).mapMono (Time.partOf .year)

/-- Certainly within the timestamps `chrono` represents. -/
def Bound.inChrono (b : Bound) : Bool :=
  b.lo.any (Time.partMin ≤ ·) && b.hi.any (· ≤ Time.partMax)

def datePartAbs (p : Time.DatePart) (a : AVal) : AVal :=
  ⟨a.nonInt || !a.int.all Bound.inChrono, a.int.map (partBound p), false, false, false⟩

def UnFn.abs : UnFn → AVal → AVal
  | .not, a => ⟨a.nonBool, none, a.ff, a.tt, false⟩
  | .isNull, a => ⟨false, none, a.null, a.int.isSome || a.tt || a.ff || a.str, false⟩
  -- Double negation is code negation too (zero is `0`).
  | .neg, a | .fneg, a => ⟨a.nonInt, a.int.map Bound.neg, false, false, false⟩
  -- Float results: some double (any code), or NULL.
  | .itof, a | .froundTo _, a =>
      ⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false⟩
  | .ffloor, a => monoAbs FloatCode.floor a
  | .fceil, a => monoAbs FloatCode.ceil a
  | .fround, a => monoAbs FloatCode.round a
  | .ftoi, a => ftoiAbs a
  | .narrow n, a => narrowAbs n a
  | .wrap _, a => a
  | .itos, a => ⟨a.nonInt, none, false, false, a.int.isSome⟩
  | .upper, a | .lower, a => ⟨a.nonStr, none, false, false, a.str⟩
  | .length, a => ⟨a.nonStr, if a.str then some (.ge 0) else none, false, false, false⟩
  -- `NULL` when the pattern does not match.
  | .regexMatch _, a => ⟨true, if a.str then some (.ge 1) else none, false, false, false⟩
  | .datePart p, a => datePartAbs p a
  | .dateTrunc u, a => monoAbs (Time.trunc u) a
  | .toDate, a => monoAbs Time.days a

def arith (op : Bound → Bound → Bound) (a b : AVal) : AVal :=
  ⟨a.nonInt || b.nonInt,
   (match a.int, b.int with | some x, some y => some (op x y) | _, _ => none),
   false, false, false⟩

/-- Can some `i ∈ x` be below some `j ∈ y`? -/
def canLt (x y : Bound) : Bool :=
  match x.lo, y.hi with | some l, some h => decide (l < h) | _, _ => true

/-- Can some `i ∈ x` be at least some `j ∈ y`? -/
def canGe (x y : Bound) : Bool :=
  match x.hi, y.lo with | some h, some l => decide (l ≤ h) | _, _ => true

/-- Can some `i ∈ x` equal some `j ∈ y`? (Do the intervals overlap?) -/
def canEq (x y : Bound) : Bool := canGe x y && canGe y x

/-- Can some `i ∈ x` differ from some `j ∈ y`? Not when both are the same point. -/
def canNe (x y : Bound) : Bool :=
  match x.point, y.point with | some k, some k' => decide (k ≠ k') | _, _ => true

/-- Can two integers drawn from `a` and `b` be equal? -/
def intEq (a b : AVal) : Bool :=
  match a.int, b.int with | some x, some y => canEq x y | _, _ => false

/-- Can two integers drawn from `a` and `b` differ? -/
def intNe (a b : AVal) : Bool :=
  match a.int, b.int with | some x, some y => canNe x y | _, _ => false

def BinFn.abs : BinFn → AVal → AVal → AVal
  | .and, a, b =>
      ⟨(a.nonBool && (b.tt || b.nonBool)) || (a.tt && b.nonBool), none, a.tt && b.tt,
       a.ff || b.ff, false⟩
  | .or, a, b =>
      ⟨(a.nonBool && (b.ff || b.nonBool)) || (a.ff && b.nonBool), none, a.tt || b.tt,
       a.ff && b.ff, false⟩
  | .add, a, b => arith Bound.add a b
  | .sub, a, b => arith Bound.sub a b
  | .mul, a, b => arith Bound.mul a b
  | .fadd, a, b | .fsub, a, b | .fmul, a, b | .fdiv, a, b | .fpow, a, b =>
      arith (fun _ _ => Bound.top) a b
  | .idiv, a, b => divAbs divBound a b
  | .imod, a, b => divAbs modBound a b
  | .ipow, a, b => powAbs a b
  | .concat, a, b | .trim _ _, a, b =>
      ⟨a.nonStr || b.nonStr, none, false, false, a.str && b.str⟩
  | .strpos, a, b =>
      ⟨a.nonStr || b.nonStr, if a.str && b.str then some (.ge 0) else none, false, false, false⟩
  | .startsWith, a, b | .endsWith, a, b | .like, a, b =>
      ⟨a.nonStr || b.nonStr, none, a.str && b.str, a.str && b.str, false⟩
  | .substr _, a, b => ⟨a.nonStr || b.nonInt, none, false, false, a.str && b.int.isSome⟩
  | .eq, a, b =>
      let mismatch := a.null || b.null || (a.int.isSome && (b.tt || b.ff || b.str)) ||
        ((a.tt || a.ff) && (b.int.isSome || b.str)) || (a.str && (b.int.isSome || b.tt || b.ff))
      ⟨mismatch, none,
       intEq a b || (a.tt && b.tt) || (a.ff && b.ff) || (a.str && b.str),
       intNe a b || (a.tt && b.ff) || (a.ff && b.tt) || (a.str && b.str), false⟩
  | .lt, a, b =>
      -- Two strings may compare either way.
      let s := a.str && b.str
      match a.int, b.int with
      | some x, some y => ⟨a.nonInt || b.nonInt, none, canLt x y || s, canGe x y || s, false⟩
      | _, _ => ⟨true, none, s, s, false⟩

def Expr.abs (env : List AVal) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => env.getD i AVal.top
  | .un f a => f.abs (a.abs env)
  | .bin f a b => f.abs (a.abs env) (b.abs env)
  | .ifThen c t e =>
      let ac := c.abs env
      (if ac.tt then t.abs env else AVal.bot).join
        (if ac.nonBool || ac.ff then e.abs env else AVal.bot)

/-- Shapes of a value, for case analysis in the binary soundness proofs. -/
theorem mem_cases {a : AVal} {v : Value} (h : a.Mem v) :
    (v = .null ∧ a.null = true) ∨ (∃ i b, v = .int i ∧ a.int = some b ∧ b.Mem i) ∨
    (v = .bool true ∧ a.tt = true) ∨ (v = .bool false ∧ a.ff = true) ∨
    (∃ s, v = .str s ∧ a.str = true) ∨ (∃ vs, v = .list vs ∧ a.tt = true ∧ a.ff = true ∧ a.str = true) := by
  match v, h with
  | .null, h => exact .inl ⟨rfl, h⟩
  | .int i, ⟨b, hb, hm⟩ => exact .inr (.inl ⟨i, b, rfl, hb, hm⟩)
  | .bool true, h => exact .inr (.inr (.inl ⟨rfl, h⟩))
  | .bool false, h => exact .inr (.inr (.inr (.inl ⟨rfl, h⟩)))
  | .str s, h => exact .inr (.inr (.inr (.inr (.inl ⟨s, rfl, h⟩))))
  | .list vs, h => exact .inr (.inr (.inr (.inr (.inr ⟨vs, rfl, h⟩))))

theorem monoAbs_sound {g : Int → Int} (hg : ∀ {x y}, x ≤ y → g x ≤ g y) {f : UnFn}
    (hf : ∀ v, f.apply v = match v with | .int c => .int (g c) | _ => .null)
    {a : AVal} {v : Value} (h : a.Mem v) : (monoAbs g a).Mem (f.apply v) := by
  rw [hf]
  rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf'⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
  · simp [monoAbs, AVal.Mem, AVal.nonInt, hn]
  · exact ⟨b.mapMono g, by simp [monoAbs, hb], Bound.mem_mapMono hg hi⟩
  all_goals simp_all [monoAbs, AVal.Mem, AVal.nonInt]

theorem ftoiAbs_sound {a : AVal} {v : Value} (h : a.Mem v) :
    (ftoiAbs a).Mem (UnFn.apply .ftoi v) := by
  rcases mem_cases h with ⟨rfl, hn⟩ | ⟨c, b, rfl, hb, hc⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
  · unfold ftoiAbs; split <;> (try split) <;> simp_all [AVal.Mem, AVal.nonInt, UnFn.apply]
  · simp only [UnFn.apply]
    unfold ftoiAbs
    rw [hb]
    obtain ⟨bl, bh⟩ := b
    match bl, bh, hc with
    | some lo, some hi, hc =>
      simp only []
      split
      · rename_i x y hx hy
        obtain ⟨z, hz⟩ := FloatCode.toInt?_between (hc.1 lo rfl) (hc.2 hi rfl) hx hy
        rw [hz]
        exact ⟨_, rfl, fun _ hl => by
          cases hl; exact FloatCode.toInt?_mono (hc.1 lo rfl) hx hz,
          fun _ hh => by cases hh; exact FloatCode.toInt?_mono (hc.2 hi rfl) hz hy⟩
      · split <;> simp [AVal.Mem, Bound.mem_top]
    | none, _, _ | some _, none, _ =>
      simp only []
      split <;> simp [AVal.Mem, Bound.mem_top]
  all_goals unfold ftoiAbs; split <;> (try split) <;> simp_all [AVal.Mem, AVal.nonInt, UnFn.apply]

/-- A double result that is "some double" (native arithmetic). -/
theorem topAbs_sound {g : Int → Int} {f : UnFn}
    (hf : ∀ v, f.apply v = match v with | .int c => .int (g c) | _ => .null)
    {a : AVal} {v : Value} (h : a.Mem v) :
    (⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false⟩ : AVal).Mem (f.apply v) := by
  rw [hf]
  rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf'⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
  · simp [AVal.Mem, AVal.nonInt, hn]
  · exact ⟨Bound.top, by simp [hb], Bound.mem_top _⟩
  all_goals simp_all [AVal.Mem, AVal.nonInt]

theorem datePartAbs_sound (p : Time.DatePart) {a : AVal} {v : Value} (h : a.Mem v) :
    (datePartAbs p a).Mem (UnFn.apply (.datePart p) v) := by
  rcases mem_cases h with ⟨rfl, hn⟩ | ⟨ts, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
  · simp [datePartAbs, UnFn.apply, AVal.Mem, AVal.nonInt, hn]
  · simp only [UnFn.apply, Time.datePart]
    by_cases hr : Time.partMin ≤ ts ∧ ts ≤ Time.partMax
    · simp only [hr, and_self, ↓reduceIte]
      refine ⟨partBound p b, by simp [datePartAbs, hb], ?_⟩
      simp only [partBound]
      split
      · rename_i lo hi hp
        have := Time.partOf_range hp ts
        exact ⟨fun l hl => by simp at hl; omega, fun u hu => by simp at hu; omega⟩
      · rename_i hp
        have hy : p = .year := by cases p <;> simp_all [Time.DatePart.range]
        subst hy
        exact Bound.mem_mapMono Time.year_mono (Bound.mem_clamp hi hr.1 hr.2)
    · simp only [hr, ↓reduceIte]
      simp only [AVal.Mem, datePartAbs, hb, Option.all_some, Bool.or_eq_true, Bool.not_eq_true']
      right
      obtain ⟨bl, bh⟩ := b
      simp only [Bound.Mem] at hi
      cases bl <;> cases bh <;> simp_all [Bound.inChrono] <;> omega
  all_goals simp_all [datePartAbs, UnFn.apply, AVal.Mem, AVal.nonInt]

theorem Text.strpos_nonneg (s t : String) : 0 ≤ Text.strpos s t := by
  unfold Text.strpos; split <;> omega

theorem UnFn.abs_sound (f : UnFn) {a : AVal} {v : Value} (h : a.Mem v) :
    (f.abs a).Mem (f.apply v) := by
  cases f
  case ffloor => exact monoAbs_sound FloatCode.floor_mono (fun v => by cases v <;> rfl) h
  case fceil => exact monoAbs_sound FloatCode.ceil_mono (fun v => by cases v <;> rfl) h
  case fround => exact monoAbs_sound FloatCode.round_mono (fun v => by cases v <;> rfl) h
  case ftoi => exact ftoiAbs_sound h
  case narrow n =>
    rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
    · simp_all [UnFn.abs, narrowAbs, UnFn.apply, AVal.Mem, AVal.nonInt]
    · simp only [UnFn.apply, UnFn.abs]
      split
      · exact ⟨b, hb, hi⟩
      · rename_i hfit
        cases hfb : b.fitsBits n
        · simp [AVal.Mem, narrowAbs, hb, hfb]
        · exact absurd (Bound.fitsBits_mem hfb hi) hfit
    all_goals simp_all [UnFn.abs, narrowAbs, UnFn.apply, AVal.Mem, AVal.nonInt]
  case wrap => simpa [UnFn.abs, UnFn.apply] using h
  case itof => exact topAbs_sound (fun v => by cases v <;> rfl) h
  case froundTo d => exact topAbs_sound (fun v => by cases v <;> rfl) h
  case itos =>
    rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩ <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonInt]
  case datePart p => exact datePartAbs_sound p h
  case dateTrunc u => exact monoAbs_sound (Time.trunc_mono u) (fun v => by cases v <;> rfl) h
  case toDate => exact monoAbs_sound Time.days_mono (fun v => by cases v <;> rfl) h
  case upper | lower | length =>
    rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩ <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonStr, Bound.ge, Bound.Mem]
  case regexMatch p =>
    rcases mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩ <;>
      simp only [UnFn.abs, UnFn.apply, AVal.Mem]
    all_goals (try cases Text.regexMatch s p) <;> simp_all [Bound.ge, Bound.Mem] <;> omega
  all_goals match v, h with
    | .null, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .int i, ⟨b, hb, hm⟩ =>
        simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt, Bound.mem_neg,
          FloatCode.neg]
    | .bool true, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .bool false, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .str _, h | .list _, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]

theorem arith_sound {op : Bound → Bound → Bound} {f : Int → Int → Int}
    (hop : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j → (op x y).Mem (f i j))
    {g : BinFn} (hg : ∀ v w, g.apply v w =
      match v, w with | .int i, .int j => .int (f i j) | _, _ => .null)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (arith op a b).Mem (g.apply v w) := by
  rw [hg]
  rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
  rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
  simp_all [arith, AVal.Mem, AVal.nonInt] <;> exact hop hi hj

theorem canGe_of_le {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : j ≤ i) :
    canGe x y = true := by
  obtain ⟨xl, xh⟩ := x
  obtain ⟨yl, yh⟩ := y
  simp only [Bound.Mem] at hx hy
  unfold canGe
  cases xh <;> cases yl <;> simp_all <;> omega

theorem intEq_of {a b : AVal} {x y : Bound} {i : Int} (ha : a.int = some x) (hb : b.int = some y)
    (hx : x.Mem i) (hy : y.Mem i) : intEq a b = true := by
  simp [intEq, ha, hb, canEq, canGe_of_le hx hy (Int.le_refl i), canGe_of_le hy hx (Int.le_refl i)]

theorem intNe_of {a b : AVal} {x y : Bound} {i j : Int} (ha : a.int = some x)
    (hb : b.int = some y) (hx : x.Mem i) (hy : y.Mem j) (h : i ≠ j) : intNe a b = true := by
  simp only [intNe, ha, hb, canNe]
  split
  · rename_i k k' hk hk'
    rw [← Bound.point_mem hk hx, ← Bound.point_mem hk' hy]
    simpa using h
  · rfl

theorem divBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (_ : j ≠ 0) :
    (divBound x y).Mem (i.tdiv j) := by
  unfold divBound
  split
  · rename_i k hk
    split
    · rename_i hk0
      rw [Bound.point_mem hk hj]
      exact Bound.mem_mapMono (fun h => Int.tdiv_le_tdiv hk0 h) hi
    · split
      · rename_i _ hkn
        rw [Bound.point_mem hk hj]
        have hneg : i.tdiv k = -(i.tdiv (-k)) := by rw [Int.tdiv_neg, Int.neg_neg]
        rw [hneg]
        exact Bound.mem_neg (Bound.mem_mapMono (fun h => Int.tdiv_le_tdiv (by omega) h) hi)
      · exact Bound.mem_absHull hi (Int.natAbs_tdiv_le_natAbs i j)
  · split
    · rename_i hpos
      obtain ⟨yl, yh⟩ := y
      cases yl with
      | none => simp at hpos
      | some l =>
        simp only [Option.any_some, decide_eq_true_eq] at hpos
        have hj1 := hj.1 l rfl
        obtain ⟨h₁, h₂⟩ := tdiv_between (a := i) (b := j) (by omega)
        obtain ⟨xl, xh⟩ := x
        refine ⟨fun l' hl' => ?_, fun u' hu' => ?_⟩
        · simp only [Bound.signHull, Option.map_eq_some_iff] at hl'
          obtain ⟨l₀, h₀, rfl⟩ := hl'; have := hi.1 l₀ h₀; omega
        · simp only [Bound.signHull, Option.map_eq_some_iff] at hu'
          obtain ⟨u₀, h₀, rfl⟩ := hu'; have := hi.2 u₀ h₀; omega
    · exact Bound.mem_absHull hi (Int.natAbs_tdiv_le_natAbs i j)

theorem modBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (hj0 : j ≠ 0) :
    (modBound x y).Mem (i.tmod j) := by
  have hlt : (i.tmod j).natAbs < j.natAbs := by rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
  have hnn : x.lo.any (0 ≤ ·) = true → 0 ≤ i.tmod j := by
    intro h
    obtain ⟨xl, xh⟩ := x
    cases xl with
    | none => simp at h
    | some l => simp at h; exact Int.tmod_nonneg _ (by have := hi.1 l rfl; omega)
  obtain ⟨yl, yh⟩ := y
  have hj' := hj
  simp only [Bound.Mem] at hj'
  unfold modBound
  cases yl <;> cases yh <;> simp only []
  case some.some l u =>
    have h₁ := hj'.1 l rfl; have h₂ := hj'.2 u rfl
    constructor
    · intro b hb
      simp only [Option.some.injEq] at hb; subst hb
      split
      · exact hnn ‹_›
      · omega
    · intro b hb
      simp only [Option.some.injEq] at hb; subst hb
      omega
  all_goals
    split
    · exact ⟨fun l hl => by simp at hl; subst hl; exact hnn ‹_›, fun _ h => by simp at h⟩
    · exact Bound.mem_top _

theorem divAbs_sound {bound : Bound → Bound → Bound} {op : Int → Int → Int} {g : BinFn}
    (hbound : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j → j ≠ 0 → (bound x y).Mem (op i j))
    (hg : ∀ v w, g.apply v w = match v, w with
      | .int i, .int j => if j = 0 then .null else .int (op i j) | _, _ => .null)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (divAbs bound a b).Mem (g.apply v w) := by
  rw [hg]
  rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
  rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
  simp only [] <;> try (simp_all [divAbs, AVal.Mem, AVal.nonInt]; done)
  by_cases hj0 : j = 0
  · subst hj0
    have : y.has0 = true := by
      cases h0 : y.has0
      · exact absurd rfl (Bound.ne_zero hj h0)
      · rfl
    simp [divAbs, AVal.Mem, AVal.mayZero, hy, this]
  · simp only [hj0, ↓reduceIte]
    exact ⟨bound x y, by simp [divAbs, hx, hy], hbound hi hj hj0⟩

theorem powAbs_sound {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (powAbs a b).Mem (BinFn.apply .ipow v w) := by
  rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
  rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
  try (simp_all [powAbs, BinFn.apply, AVal.Mem, AVal.nonInt]; done)
  simp only [BinFn.apply]
  split
  · -- No result: the exponent is out of `[0, 64]`, so NULL is allowed.
    rename_i hout
    simp only [AVal.Mem, powAbs, Bool.or_eq_true, Bool.not_eq_true']
    right
    obtain ⟨yl, yh⟩ := y
    simp only [hy]
    cases yl <;> cases yh <;> simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] <;>
      first | rfl | (simp only [Bound.Mem] at hj; have := hj.1 _ rfl; have := hj.2 _ rfl; omega)
  · simp only [AVal.Mem, powAbs, hx, hy]
    refine ⟨_, rfl, ?_⟩
    split
    · rename_i hsq
      rw [Bound.point_mem (by simpa using hsq) hj]
      constructor
      · intro l hl; cases hl
        show 0 ≤ i ^ (2 : Int).toNat
        rw [show (2 : Int).toNat = 2 from rfl, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
        rcases Int.le_total 0 i with h | h
        · exact Int.mul_nonneg h h
        · exact Int.mul_nonneg_of_nonpos_of_nonpos h h
      · intro _ h; cases h
    · exact Bound.mem_top _

theorem BinFn.abs_sound (f : BinFn) {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (f.abs a b).Mem (f.apply v w) := by
  cases f
  case add => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case sub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case mul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fadd => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fsub => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fmul => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fdiv => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fpow => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case idiv => exact divAbs_sound divBound_sound (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case imod => exact divAbs_sound modBound_sound (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case ipow => exact powAbs_sound ha hb
  case concat | trim | strpos | startsWith | endsWith | like | substr =>
    rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
    rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
    simp_all [BinFn.abs, BinFn.apply, AVal.Mem, AVal.nonStr, AVal.nonInt, Bound.ge, Bound.Mem,
      Text.strpos_nonneg]
    all_goals split <;> simp_all
  case eq =>
    rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
    rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
    simp only [BinFn.abs, BinFn.apply, AVal.Mem]
    all_goals first | (simp_all; done) | skip
    -- What is left: two integers, or two strings.
    · by_cases hij : i = j
      · subst hij
        have : (i == i) = true := by simp
        rw [this]; simp [intEq_of hx hy hi hj]
      · have : (i == j) = false := by simpa using hij
        rw [this]; simp [intNe_of hx hy hi hj hij]
    · cases (s == s') <;> simp [h, h']
    -- Two lists.
    · rename_i vs ws
      by_cases hv : vs = ws <;> simp [hv, h.2.2, h'.2.2]
  all_goals
    rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
    rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩ <;>
    simp_all [BinFn.abs, BinFn.apply, and3, or3, AVal.Mem, AVal.nonBool, AVal.nonInt]
  all_goals (split <;> simp_all [canLt, canGe])
  -- What is left: comparisons of two integers against their intervals, and
  -- of two strings.
  all_goals first
    | (obtain ⟨xl, xh⟩ := x
       obtain ⟨yl, yh⟩ := y
       simp only [Bound.Mem] at hi hj
       cases xl <;> cases xh <;> cases yl <;> cases yh <;> simp_all <;> omega)
    | (split <;> rfl)

theorem Value.eq_true_of_isTrue {v : Value} (h : v.isTrue = true) : v = .bool true := by
  cases v with
  | bool b => cases b <;> simp_all [Value.isTrue]
  | _ => simp_all [Value.isTrue]

/-- Abstract values describe a row: column `i` lies in `env.getD i top`. -/
def EnvMem (env : List AVal) (row : Row) : Prop :=
  ∀ i, (env.getD i AVal.top).Mem (row.getD i .null)

theorem Expr.abs_sound {env : List AVal} {row : Row} (h : EnvMem env row) :
    ∀ e : Expr, (e.abs env).Mem (e.eval row)
  | .lit v => AVal.mem_ofValue v
  | .field i => h i
  | .un f a => UnFn.abs_sound f (Expr.abs_sound h a)
  | .bin f a b => BinFn.abs_sound f (Expr.abs_sound h a) (Expr.abs_sound h b)
  | .ifThen c t e => by
      have hc := Expr.abs_sound h c
      simp only [abs, eval]
      by_cases hct : (c.eval row).isTrue = true
      · rw [ite_eq_left hct]
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.abs env).tt = true := hc
        apply AVal.mem_join_left
        rw [ite_eq_left htt]
        exact Expr.abs_sound h t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.abs env).nonBool || (c.abs env).ff) = true := by
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        exact Expr.abs_sound h e

/-! ## Refinement by filter conditions -/

/-- A column known to be a non-NULL integer, with its interval transformed. -/
def AVal.nonNullInt (a : AVal) (f : Bound → Bound) : AVal := ⟨false, a.int.map f, false, false, false⟩

/-- `a` without NULL and the booleans: what an operand of a TRUE `<` can be. -/
def AVal.nonNullOrd (a : AVal) : AVal := ⟨false, a.int, false, false, a.str⟩

/-- An integer or a string: what `<` compares. -/
def Value.isOrd : Value → Bool
  | .int _ | .str _ => true
  | _ => false

/-- What a value known to equal (SQL `=`, so non-NULL) a value in `b` can be. -/
def AVal.meetEq (a b : AVal) : AVal :=
  ⟨false, (match a.int, b.int with | some x, some y => some (x.meet y) | _, _ => none),
   a.tt && b.tt, a.ff && b.ff, a.str && b.str⟩

theorem AVal.meetEq_mem {a b : AVal} {v : Value} (ha : a.Mem v) (hb : b.Mem v) (hn : v ≠ .null) :
    (a.meetEq b).Mem v := by
  match v, ha, hb with
  | .null, _, _ => exact absurd rfl hn
  | .int i, ⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩ =>
      exact ⟨x.meet y, by simp [AVal.meetEq, hx, hy], Bound.mem_meet hxi hyi⟩
  | .bool true, ha, hb | .bool false, ha, hb | .str _, ha, hb =>
      simp_all [AVal.Mem, AVal.meetEq]
  | .list _, ha, hb =>
      simp only [AVal.Mem, AVal.meetEq] at *
      exact ⟨by simp [ha.1, hb.1], by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩

def refineCol (env : List AVal) (i : Nat) (f : AVal → AVal) : List AVal :=
  env.set i (f (env.getD i AVal.top))

/-- What a row that makes `e` TRUE satisfies. Recognizes conjunctions,
disjunctions, comparisons of a column with an integer constant, `IS NULL`
and `IS NOT NULL`. -/
def Expr.refine (env : List AVal) : Expr → List AVal
  | .bin .and p q => q.refine (p.refine env)
  | .bin .lt (.field i) (.lit (.int k)) => refineCol env i (·.nonNullInt (·.atMost (k - 1)))
  | .bin .lt (.lit (.int k)) (.field i) => refineCol env i (·.nonNullInt (·.atLeast (k + 1)))
  | .un .not (.bin .lt (.field i) (.lit (.int k))) => refineCol env i (·.nonNullInt (·.atLeast k))
  | .un .not (.bin .lt (.lit (.int k)) (.field i)) => refineCol env i (·.nonNullInt (·.atMost k))
  | .bin .eq (.field i) (.lit (.int k)) => refineCol env i (·.nonNullInt fun _ => .exact k)
  | .un .not (.un .isNull (.field i)) => refineCol env i fun a => { a with null := false }
  | .bin .eq (.field i) (.field j) =>
      let ai := env.getD i AVal.top
      let aj := env.getD j AVal.top
      refineCol (refineCol env i (·.meetEq aj)) j (·.meetEq ai)
  -- `x <> k` is TRUE only for a non-NULL integer `x`.
  | .un .not (.bin .eq (.field i) (.lit (.int _))) => refineCol env i (·.nonNullInt id)
  -- Comparing two columns: TRUE only if both are non-NULL integers or strings.
  | .bin .lt (.field i) (.field j) | .un .not (.bin .lt (.field i) (.field j)) =>
      refineCol (refineCol env i AVal.nonNullOrd) j AVal.nonNullOrd
  -- Arithmetic is NULL-propagating: a non-NULL `a - b` has non-NULL operands
  -- (DataFusion inlines computed columns such as `gap = ts - prev_ts`).
  | .un .not (.un .isNull (.bin .add a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
  | .un .not (.un .isNull (.bin .sub a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
  | .un .not (.un .isNull (.bin .mul a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
  -- `p OR q` (e.g. `x IN (1, 2)`): what `p` gives, or what `q` gives.
  | .bin .or p q => List.zipWith AVal.join (p.refine env) (q.refine env)
  -- `x IS NULL`: only NULL (so `x IS NULL OR x >= 0` keeps the bound).
  | .un .isNull (.field i) => refineCol env i fun a => ⟨a.null, none, false, false, false⟩
  | _ => env
termination_by e => sizeOf e

theorem getD_top_eq (env : List AVal) (j : Nat) : env.getD j AVal.top = (env[j]?).getD AVal.top :=
  List.getD_eq_getElem?_getD

theorem refineCol_sound {env : List AVal} {row : Row} {i : Nat} {f : AVal → AVal}
    (h : EnvMem env row) (hf : (f (env.getD i AVal.top)).Mem (row.getD i .null)) :
    EnvMem (refineCol env i f) row := by
  intro j
  have hj := h j
  simp only [refineCol, getD_top_eq, List.getElem?_set] at *
  by_cases hij : i = j
  · subst hij
    by_cases hlen : i < env.length
    · simpa [hlen] using hf
    · simpa [hlen] using hj
  · simpa [hij] using hj

theorem refineCol_length (env : List AVal) (i : Nat) (f : AVal → AVal) :
    (refineCol env i f).length = env.length := by simp [refineCol]

theorem EnvMem.zip_left {e₁ e₂ : List AVal} {row : Row} (h : EnvMem e₁ row) :
    EnvMem (List.zipWith AVal.join e₁ e₂) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_zipWith] at *
  split <;> simp_all [AVal.mem_top, AVal.mem_join_left]

theorem EnvMem.zip_right {e₁ e₂ : List AVal} {row : Row} (h : EnvMem e₂ row) :
    EnvMem (List.zipWith AVal.join e₁ e₂) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_zipWith] at *
  split <;> simp_all [AVal.mem_top, AVal.mem_join_right]

theorem Expr.refine_length (env : List AVal) (e : Expr) : (e.refine env).length = env.length := by
  fun_induction Expr.refine env e <;> simp_all [refineCol_length]

theorem lt_int_right {v : Value} {k : Int} (h : (BinFn.apply .lt v (.int k)).isTrue = true) :
    ∃ x, v = .int x ∧ x < k := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]
  rename_i x; by_cases hx : x < k <;> simp_all

theorem lt_int_left {v : Value} {k : Int} (h : (BinFn.apply .lt (.int k) v).isTrue = true) :
    ∃ x, v = .int x ∧ k < x := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]
  rename_i x; by_cases hx : k < x <;> simp_all

theorem not_lt_int_right {v : Value} {k : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt v (.int k))).isTrue = true) :
    ∃ x, v = .int x ∧ k ≤ x := by
  cases v <;> simp_all [BinFn.apply, UnFn.apply, Value.isTrue]
  rename_i x; by_cases hx : x < k <;> simp_all <;> omega

theorem not_lt_int_left {v : Value} {k : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt (.int k) v)).isTrue = true) :
    ∃ x, v = .int x ∧ x ≤ k := by
  cases v <;> simp_all [BinFn.apply, UnFn.apply, Value.isTrue]
  rename_i x; by_cases hx : k < x <;> simp_all <;> omega

theorem eq_int {v : Value} {k : Int} (h : (BinFn.apply .eq v (.int k)).isTrue = true) :
    v = .int k := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]
  rename_i x; by_cases hx : x = k <;> simp_all

theorem isNull_true {v : Value} (h : (UnFn.apply .isNull v).isTrue = true) : v = .null := by
  cases v <;> simp_all [UnFn.apply, Value.isTrue]

theorem not_isNull {v : Value} (h : (UnFn.apply .not (UnFn.apply .isNull v)).isTrue = true) :
    v ≠ .null := by
  cases v <;> simp_all [UnFn.apply, Value.isTrue]

/-- SQL `v = w` is TRUE only when both are the same non-NULL value. -/
theorem eq_true_same {v w : Value} (h : (BinFn.apply .eq v w).isTrue = true) :
    v = w ∧ v ≠ .null := by
  cases v <;> cases w <;> simp [BinFn.apply, Value.isTrue] at h ⊢
  all_goals
    rename_i x y
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy] at h

theorem lt_fields_ord {v w : Value} (h : (BinFn.apply .lt v w).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  cases v <;> cases w <;> simp_all [BinFn.apply, Value.isTrue, Value.isOrd]

theorem not_lt_fields_ord {v w : Value}
    (h : (UnFn.apply .not (BinFn.apply .lt v w)).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  cases v <;> cases w <;> simp_all [BinFn.apply, UnFn.apply, Value.isTrue, Value.isOrd]

theorem nonNullOrd_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : v.isOrd = true) :
    a.nonNullOrd.Mem v := by
  cases v <;> simp_all [Value.isOrd, AVal.nonNullOrd, AVal.Mem]

theorem nonNullInt_mem {a : AVal} {x : Int} {f : Bound → Bound} (h : a.Mem (.int x))
    (hf : ∀ b, b.Mem x → (f b).Mem x) : (a.nonNullInt f).Mem (.int x) := by
  obtain ⟨b, hb, hm⟩ := h
  exact ⟨f b, by simp [AVal.nonNullInt, hb], hf b hm⟩

theorem not_isNull_arith {f : BinFn} (hf : f = .add ∨ f = .sub ∨ f = .mul) {v w : Value}
    (h : (UnFn.apply .not (UnFn.apply .isNull (BinFn.apply f v w))).isTrue = true) :
    (UnFn.apply .not (UnFn.apply .isNull v)).isTrue = true ∧
      (UnFn.apply .not (UnFn.apply .isNull w)).isTrue = true := by
  rcases hf with rfl | rfl | rfl <;> cases v <;> cases w <;>
    simp_all [BinFn.apply, UnFn.apply, Value.isTrue]

theorem Expr.refine_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refine env) row := by
  fun_induction Expr.refine env e
  case case1 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
    exact ihq (ihp h ht.1) ht.2
  case case2 env i k =>
    obtain ⟨x, hx, hk⟩ := lt_int_right (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact nonNullInt_mem this fun b hb => Bound.mem_atMost hb (by omega)
  case case3 env k i =>
    obtain ⟨x, hx, hk⟩ := lt_int_left (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact nonNullInt_mem this fun b hb => Bound.mem_atLeast hb (by omega)
  case case4 env i k =>
    obtain ⟨x, hx, hk⟩ := not_lt_int_right (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact nonNullInt_mem this fun b hb => Bound.mem_atLeast hb hk
  case case5 env k i =>
    obtain ⟨x, hx, hk⟩ := not_lt_int_left (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact nonNullInt_mem this fun b hb => Bound.mem_atMost hb hk
  case case6 env i k =>
    have hx := eq_int (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact nonNullInt_mem this fun _ _ => Bound.mem_exact k
  case case7 env i =>
    have hn : row.getD i .null ≠ .null := by
      simpa [List.getD_eq_getElem?_getD] using not_isNull (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    have := h i
    generalize row.getD i .null = v at hn this ⊢
    cases v with
    | bool b => cases b <;> simp_all [AVal.Mem]
    | _ => simp_all [AVal.Mem]
  case case8 env i j ai aj =>
    -- `a = b` is TRUE: both sides are the same non-NULL value.
    obtain ⟨hv, hn⟩ := eq_true_same (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD] at hv
    rw [← List.getD_eq_getElem?_getD] at hn
    have hi := h i
    have hj := h j
    have h₁ := refineCol_sound (f := (·.meetEq aj)) h (AVal.meetEq_mem hi (hv ▸ hj) hn)
    refine refineCol_sound h₁ ?_
    have hj' := h₁ j
    exact AVal.meetEq_mem hj' (hv ▸ hi) (hv ▸ hn)
  case case9 env i k =>
    obtain ⟨x, hx⟩ : ∃ x, row.getD i .null = .int x := by
      have ht' : (UnFn.apply .not (BinFn.apply .eq (row.getD i .null) (.int k))).isTrue = true := by
        simpa [eval, List.getD_eq_getElem?_getD] using ht
      generalize row.getD i .null = v at ht' ⊢
      cases v <;> simp_all [BinFn.apply, UnFn.apply, Value.isTrue]
    refine refineCol_sound h ?_
    have := h i
    rw [hx] at this ⊢
    exact nonNullInt_mem this fun _ hb => hb
  case case10 env i j =>
    obtain ⟨hx, hy⟩ := lt_fields_ord (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := AVal.nonNullOrd) h (nonNullOrd_mem (h i) hx)
    exact refineCol_sound h₁ (nonNullOrd_mem (h₁ j) hy)
  case case11 env i j =>
    obtain ⟨hx, hy⟩ := not_lt_fields_ord (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := AVal.nonNullOrd) h (nonNullOrd_mem (h i) hx)
    exact refineCol_sound h₁ (nonNullOrd_mem (h₁ j) hy)
  case case12 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .add (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inl rfl) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case13 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .sub (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inr (.inl rfl)) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case14 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .mul (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inr (.inr rfl)) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case15 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · exact EnvMem.zip_left (ihp h ht)
    · exact EnvMem.zip_right (ihq h ht)
  case case16 env i =>
    have hn : row.getD i .null = .null := by
      simpa [List.getD_eq_getElem?_getD] using isNull_true (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    have := h i
    rw [hn] at this ⊢
    simpa [AVal.Mem] using this
  case case17 => exact h

/-! ## What a condition says about one expression

`CASE WHEN c THEN t ELSE e END` evaluates `t` only where `c` is TRUE and `e`
only where it is not (FALSE or NULL). The rewrites of `GREATEST`, `LEAST`,
`ABS` and `NULLIF` branch on `IS NULL` and on comparisons with constants, so a
condition's *subject* (the expression it tests) is often the branch itself:
`CASE WHEN x < 0 THEN 0 ELSE x END` is `≥ 0` because in the `ELSE` branch
`x < 0` is not TRUE. -/

/-- A constraint on a value. -/
inductive Cstr where
  | null
  | notNull
  /-- An integer in `b`; if `strict`, certainly a (non-NULL) integer. -/
  | intIn (b : Bound) (strict : Bool)
  /-- Not the integer `k` (but maybe NULL or not an integer). -/
  | ne (k : Int)

def Cstr.Holds : Cstr → Value → Prop
  | .null, v => v = .null
  | .notNull, v => v ≠ .null
  | .intIn b true, v => ∃ j, v = .int j ∧ b.Mem j
  | .intIn b false, v => ∀ j, v = .int j → b.Mem j
  | .ne k, v => ∀ j, v = .int j → j ≠ k

/-- What `c` being TRUE (`pos`) or not TRUE says about its subject. -/
def Expr.cstr (pos : Bool) : Expr → Option (Expr × Cstr)
  | .un .isNull s => some (s, if pos then .null else .notNull)
  | .un .not (.un .isNull s) => some (s, if pos then .notNull else .null)
  | .bin .lt s (.lit (.int k)) => some (s, if pos then .intIn ⟨none, some (k - 1)⟩ true
      else .intIn ⟨some k, none⟩ false)
  | .bin .lt (.lit (.int k)) s => some (s, if pos then .intIn ⟨some (k + 1), none⟩ true
      else .intIn ⟨none, some k⟩ false)
  | .un .not (.bin .lt s (.lit (.int k))) => some (s, if pos then .intIn ⟨some k, none⟩ true
      else .intIn ⟨none, some (k - 1)⟩ false)
  | .un .not (.bin .lt (.lit (.int k)) s) => some (s, if pos then .intIn ⟨none, some k⟩ true
      else .intIn ⟨some (k + 1), none⟩ false)
  | .bin .eq s (.lit (.int k)) => some (s, if pos then .intIn (.exact k) true else .ne k)
  | .un .not (.bin .eq s (.lit (.int k))) => some (s, if pos then .ne k
      else .intIn (.exact k) false)
  | _ => none

/-- Narrow an abstract value by a constraint. -/
def Cstr.apply : Cstr → AVal → AVal
  | .null, a => ⟨a.null, none, false, false, false⟩
  | .notNull, a => { a with null := false }
  | .intIn b true, a => ⟨false, a.int.map (·.meet b), false, false, false⟩
  | .intIn b false, a => { a with int := a.int.map (·.meet b) }
  -- Intervals cannot exclude a single value.
  | .ne _, a => a

/-- The constraint on `-v` (integer or double negation) given one on `v`. -/
def Cstr.neg : Cstr → Option Cstr
  | .null => some .null
  | .notNull => none
  | .intIn b strict => some (.intIn b.neg strict)
  | .ne k => some (.ne (-k))

theorem Value.isTrue_bool (b : Bool) : (Value.bool b).isTrue = b := by cases b <;> rfl

theorem Expr.cstr_sound {pos : Bool} {c s : Expr} {k : Cstr} {row : Row}
    (hc : c.cstr pos = some (s, k)) (ht : (c.eval row).isTrue = pos) : k.Holds (s.eval row) := by
  unfold Expr.cstr at hc
  split at hc <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc <;>
    obtain ⟨rfl, rfl⟩ := hc <;> simp only [eval] at ht <;>
    generalize Expr.eval row _ = v at ht ⊢ <;> cases pos <;>
    cases v <;> simp only [UnFn.apply, BinFn.apply, Value.isTrue_bool, decide_eq_true_eq,
      decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne] at ht <;>
    simp_all [Cstr.Holds, Value.isTrue, Bound.Mem, Bound.exact] <;> omega

theorem Cstr.apply_sound {k : Cstr} {a : AVal} {v : Value} (hk : k.Holds v) (ha : a.Mem v) :
    (k.apply a).Mem v := by
  rcases mem_cases ha with ⟨rfl, hn⟩ | ⟨j, x, rfl, hx, hm⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩
  all_goals cases k with
    | null => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
    | notNull => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
    | intIn b strict =>
      cases strict <;> simp_all [Cstr.Holds, Cstr.apply, AVal.Mem] <;> exact Bound.mem_meet hm hk
    | ne k => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]

theorem Cstr.neg_sound {k k' : Cstr} {f : UnFn} (hf : f = .neg ∨ f = .fneg) {v : Value}
    (hk' : k.neg = some k') (hk : k.Holds v) : k'.Holds (f.apply v) := by
  rcases hf with rfl | rfl <;>
  match k, k', hk' with
  | .null, _, rfl => simp_all [Cstr.Holds, UnFn.apply]
  | .intIn b true, _, rfl =>
      obtain ⟨j, rfl, hj⟩ := hk
      exact ⟨-j, by simp [UnFn.apply, FloatCode.neg], Bound.mem_neg hj⟩
  | .intIn b false, _, rfl =>
      intro j hj
      cases v <;> simp_all [UnFn.apply, FloatCode.neg]
      rename_i i; rw [← hj]; exact Bound.mem_neg (hk i rfl)
  | .ne k, _, rfl =>
      intro j hj
      cases v <;> simp_all [UnFn.apply, FloatCode.neg]
      rename_i i; have := hk i rfl; omega

/-- Constraints known to hold on the current row, each on the value of an
expression (the conditions of the enclosing `CASE` branches and `OR`s). -/
abbrev Assumptions := List (Expr × Cstr)

def KsHold (ks : Assumptions) (row : Row) : Prop := ∀ p ∈ ks, p.2.Holds (p.1.eval row)

/-- `c`'s constraint when it is TRUE (`pos`) or not, as assumptions. -/
def Expr.cstrs (pos : Bool) (c : Expr) : Assumptions := (c.cstr pos).toList

theorem KsHold.cons_cstrs {pos : Bool} {c : Expr} {ks : Assumptions} {row : Row}
    (ht : (c.eval row).isTrue = pos) (hks : KsHold ks row) : KsHold (c.cstrs pos ++ ks) row := by
  intro p hp
  simp only [List.mem_append, Expr.cstrs] at hp
  rcases hp with hp | hp
  · cases hc : c.cstr pos with
    | none => simp [hc] at hp
    | some sk => simp only [hc, Option.toList_some, List.mem_singleton] at hp; subst hp;
                 exact Expr.cstr_sound hc ht
  · exact hks p hp

/-- Narrow the abstract value `a` of `e` by an assumption about `e`, or about
`x` when `e` is `-x`. -/
def narrowBy (e : Expr) (a : AVal) (sk : Expr × Cstr) : AVal :=
  if sk.1 = e then sk.2.apply a
  else match e with
    | .un f y => if (f = .neg ∨ f = .fneg) ∧ y = sk.1 then (sk.2.neg.map (·.apply a)).getD a else a
    | _ => a

def narrowAll (ks : Assumptions) (e : Expr) (a : AVal) : AVal := ks.foldl (narrowBy e) a

theorem narrowBy_sound {e : Expr} {a : AVal} {sk : Expr × Cstr} {row : Row}
    (hk : sk.2.Holds (sk.1.eval row)) (ha : a.Mem (e.eval row)) :
    (narrowBy e a sk).Mem (e.eval row) := by
  unfold narrowBy
  split
  · rename_i hs; rw [← hs]; exact Cstr.apply_sound hk (hs ▸ ha)
  · split
    · rename_i f y _
      split
      · rename_i hfy
        obtain ⟨hf, rfl⟩ := hfy
        cases hn : sk.2.neg with
        | none => exact ha
        | some k' => exact Cstr.apply_sound (Cstr.neg_sound hf hn hk) ha
      · exact ha
    · exact ha

theorem narrowAll_sound {e : Expr} {row : Row} :
    ∀ {ks : Assumptions} {a : AVal}, KsHold ks row → a.Mem (e.eval row) →
      (narrowAll ks e a).Mem (e.eval row)
  | [], _, _, ha => ha
  | sk :: ks, _, hks, ha => by
      simp only [narrowAll, List.foldl_cons]
      exact narrowAll_sound (ks := ks) (fun p hp => hks p (by simp [hp]))
        (narrowBy_sound (hks sk (by simp)) ha)

/-- What a row on which `e` is *not* TRUE satisfies (the `ELSE` branch of a
`CASE`). Recognizes the constraints of `Expr.cstr` on columns, and `OR`
(neither side is TRUE) and `AND` (one side is not TRUE). -/
def Expr.refineNeg (env : List AVal) : Expr → List AVal
  | .bin .or p q => q.refineNeg (p.refineNeg env)
  | .bin .and p q => List.zipWith AVal.join (p.refineNeg env) (q.refineNeg env)
  | e => match e.cstr false with
    | some (.field i, k) => refineCol env i k.apply
    | _ => env

theorem Expr.refineNeg_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = false) : EnvMem (e.refineNeg env) row := by
  fun_induction Expr.refineNeg env e
  case case1 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_false_iff] at ht
    exact ihq (ihp h ht.1) ht.2
  case case2 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_false_iff] at ht
    rcases ht with ht | ht
    · exact EnvMem.zip_left (ihp h ht)
    · exact EnvMem.zip_right (ihq h ht)
  case case3 env e _ _ i k hc =>
    refine refineCol_sound h ?_
    have hk := Expr.cstr_sound hc ht
    exact Cstr.apply_sound (by simpa [eval] using hk) (h i)
  case case4 => exact h

/-! ## Relational facts

Per-column descriptions cannot say "`t1` is exactly `Δ` after `t0`" or "`v` is
anything but -9999". `Fact`s can: they are collected alongside the column
descriptions and used when evaluating comparisons and differences. -/

/-- A fact about a row. -/
inductive Fact where
  /-- If columns `i` and `j` hold integers `x` and `y`, then `x - y ∈ b`. -/
  | diff (i j : Nat) (b : Bound)
  /-- Column `i` does not hold the integer `k`. -/
  | ne (i : Nat) (k : Int)
  deriving Repr, DecidableEq

def Fact.Holds (row : Row) : Fact → Prop
  | .diff i j b => ∀ x y, row.getD i .null = .int x → row.getD j .null = .int y → b.Mem (x - y)
  | .ne i k => row.getD i .null ≠ .int k

def FactsHold (fs : List Fact) (row : Row) : Prop := ∀ f ∈ fs, f.Holds row

theorem FactsHold.append {fs gs : List Fact} {row : Row} (h₁ : FactsHold fs row)
    (h₂ : FactsHold gs row) : FactsHold (fs ++ gs) row := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h₁ f hf
  · exact h₂ f hf

/-- `e` is column `j` plus the constant `c`. -/
def Expr.linTerm : Expr → Option (Nat × Int)
  | .field j => some (j, 0)
  | .bin .add (.field j) (.lit (.int c)) => some (j, c)
  | .bin .add (.lit (.int c)) (.field j) => some (j, c)
  | .bin .sub (.field j) (.lit (.int c)) => some (j, -c)
  | _ => none

theorem Expr.linTerm_spec {e : Expr} {j : Nat} {c : Int} (h : e.linTerm = some (j, c)) :
    (e = .field j ∧ c = 0) ∨ e = .bin .add (.field j) (.lit (.int c)) ∨
      e = .bin .add (.lit (.int c)) (.field j) ∨ e = .bin .sub (.field j) (.lit (.int (-c))) := by
  unfold Expr.linTerm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp

theorem Expr.linTerm_int {e : Expr} {j : Nat} {c y : Int} {row : Row}
    (h : e.linTerm = some (j, c)) (hy : row.getD j .null = .int y) :
    e.eval row = .int (y + c) := by
  rw [List.getD_eq_getElem?_getD] at hy
  rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl <;>
    simp [eval, BinFn.apply, hy] <;> omega

theorem Expr.linTerm_of_int {e : Expr} {j : Nat} {c v : Int} {row : Row}
    (h : e.linTerm = some (j, c)) (hv : e.eval row = .int v) :
    ∃ y, row.getD j .null = .int y ∧ v = y + c := by
  cases hy : row.getD j .null with
  | int y =>
    rw [Expr.linTerm_int h hy] at hv
    exact ⟨y, rfl, by injection hv; omega⟩
  | _ =>
    exfalso
    rw [List.getD_eq_getElem?_getD] at hy
    rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl <;>
      simp [eval, BinFn.apply, hy] at hv

def neFact (t : Expr) (k : Int) : List Fact :=
  match t.linTerm with | some (j, c) => [.ne j (k - c)] | none => []

def diffFact (t₁ t₂ : Expr) (mk : Int → Int → Bound) : List Fact :=
  match t₁.linTerm, t₂.linTerm with
  | some (i, c₁), some (j, c₂) => [.diff i j (mk c₁ c₂)]
  | _, _ => []

/-- Facts that hold on every row where `e` is TRUE. -/
def Fact.mentions (i : Nat) : Fact → Bool
  | .diff a b _ => a == i || b == i
  | .ne a _ => a == i

def Expr.factsOf : Expr → List Fact
  | .bin .and p q => p.factsOf ++ q.factsOf
  | .un .not (.bin .eq t (.lit (.int k))) => neFact t k
  | .un .not (.bin .eq (.lit (.int k)) t) => neFact t k
  | .bin .eq t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => .exact (c₂ - c₁)
  | .bin .lt t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => ⟨none, some (c₂ - c₁ - 1)⟩
  | .un .not (.bin .lt t₁ t₂) => diffFact t₁ t₂ fun c₁ c₂ => ⟨some (c₂ - c₁), none⟩
  -- NOT (p OR q) is NOT p AND NOT q.
  | .un .not (.bin .or p q) => (Expr.un .not p).factsOf ++ (Expr.un .not q).factsOf
  -- NOT (x IS NOT NULL AND q): either x is NULL, or NOT q. Facts about x hold
  -- in both cases, since facts only constrain non-NULL values. (Ibis writes
  -- `~x.isnan()` this way.)
  | .un .not (.bin .and (.un .not (.un .isNull (.field i))) q) =>
      (Expr.un .not q).factsOf.filter (·.mentions i)
  | _ => []
termination_by e => sizeOf e

theorem neFact_sound {t : Expr} {k : Int} {row : Row} (hne : t.eval row ≠ .int k) :
    FactsHold (neFact t k) row := by
  unfold neFact
  split
  · rename_i j c hl
    intro f hf
    simp only [List.mem_singleton] at hf; subst hf
    intro hj
    apply hne
    rw [Expr.linTerm_int hl hj]; congr 1; omega
  · intro f hf; simp at hf

theorem diffFact_sound {t₁ t₂ : Expr} {mk : Int → Int → Bound} {row : Row} {P : Int → Int → Prop}
    (hP : ∀ u w, t₁.eval row = .int u → t₂.eval row = .int w → P u w)
    (hmk : ∀ c₁ c₂ x y, P (x + c₁) (y + c₂) → (mk c₁ c₂).Mem (x - y)) :
    FactsHold (diffFact t₁ t₂ mk) row := by
  unfold diffFact
  split
  · rename_i i c₁ j c₂ h₁ h₂
    intro f hf
    simp only [List.mem_singleton] at hf; subst hf
    intro x y hx hy
    exact hmk c₁ c₂ x y (hP _ _ (Expr.linTerm_int h₁ hx) (Expr.linTerm_int h₂ hy))
  · intro f hf; simp at hf

theorem not_or3_true {v w : Value} (h : (UnFn.apply .not (or3 v w)).isTrue = true) :
    (UnFn.apply .not v).isTrue = true ∧ (UnFn.apply .not w).isTrue = true := by
  match v, w with
  | .bool false, .bool false => simp [UnFn.apply, Value.isTrue]
  | .bool true, _ => simp [or3, UnFn.apply, Value.isTrue] at h
  | .bool false, .bool true | .null, .bool true | .int _, .bool true | .str _, .bool true =>
      simp [or3, UnFn.apply, Value.isTrue] at h
  | .bool false, .null | .bool false, .int _ | .bool false, .str _ =>
      simp [or3, UnFn.apply, Value.isTrue] at h
  | .null, .bool false | .null, .null | .null, .int _ | .null, .str _ =>
      simp [or3, UnFn.apply, Value.isTrue] at h
  | .int _, .bool false | .int _, .null | .int _, .int _ | .int _, .str _ =>
      simp [or3, UnFn.apply, Value.isTrue] at h
  | .str _, .bool false | .str _, .null | .str _, .int _ | .str _, .str _ =>
      simp [or3, UnFn.apply, Value.isTrue] at h
  | .list _, .bool true | .list _, .bool false | .list _, .null | .list _, .int _
  | .list _, .str _ | .list _, .list _
  | .bool false, .list _ | .null, .list _ | .int _, .list _ | .str _, .list _ =>
      simp [or3, UnFn.apply, Value.isTrue] at h

theorem not_and3_notnull_true {x w : Value} (hx : x ≠ .null)
    (h : (UnFn.apply .not (and3 (UnFn.apply .not (UnFn.apply .isNull x)) w)).isTrue = true) :
    (UnFn.apply .not w).isTrue = true := by
  have : UnFn.apply .not (UnFn.apply .isNull x) = .bool true := by
    cases x <;> simp_all [UnFn.apply]
  rw [this] at h
  match w with
  | .bool false => simp [UnFn.apply, Value.isTrue]
  | .bool true => simp [and3, UnFn.apply, Value.isTrue] at h
  | .null | .int _ | .str _ => simp [and3, UnFn.apply, Value.isTrue] at h

theorem Fact.holds_of_null {f : Fact} {row : Row} {i : Nat} (hm : f.mentions i = true)
    (hn : row.getD i .null = .null) : f.Holds row := by
  cases f with
  | diff a b d =>
    simp only [Fact.mentions, Bool.or_eq_true, beq_iff_eq] at hm
    intro x y hx hy
    rcases hm with rfl | rfl
    · rw [hn] at hx; cases hx
    · rw [hn] at hy; cases hy
  | ne a k =>
    simp only [Fact.mentions, beq_iff_eq] at hm
    subst hm; intro h; rw [hn] at h; cases h

theorem Expr.factsOf_sound {row : Row} (e : Expr) (ht : (e.eval row).isTrue = true) :
    FactsHold e.factsOf row := by
  fun_induction Expr.factsOf e
  case case1 p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
    exact (ihp ht.1).append (ihq ht.2)
  case case2 t k =>
    apply neFact_sound
    intro hv
    simp [eval, hv, BinFn.apply, UnFn.apply, Value.isTrue] at ht
  case case3 k t =>
    apply neFact_sound
    intro hv
    simp [eval, hv, BinFn.apply, UnFn.apply, Value.isTrue] at ht
  case case4 t₁ t₂ =>
    refine diffFact_sound (P := fun u w => u = w) (fun u w hu hw => ?_) (fun c₁ c₂ x y h => ?_)
    · have := (eq_true_same (by simpa [eval] using ht)).1
      rw [hu, hw] at this; injection this
    · simp only [Bound.Mem, Bound.exact, Option.some.injEq]
      constructor <;> intro _ h' <;> subst h' <;> omega
  case case5 t₁ t₂ =>
    refine diffFact_sound (P := fun u w => u < w) (fun u w hu hw => ?_) (fun c₁ c₂ x y h => ?_)
    · simp only [eval, hu, hw, BinFn.apply, Value.isTrue] at ht
      by_cases hlt : u < w <;> simp_all
    · simp only [Bound.Mem, Option.some.injEq, reduceCtorEq]
      constructor
      · intro _ h'; cases h'
      · intro _ h'; subst h'; omega
  case case6 t₁ t₂ =>
    refine diffFact_sound (P := fun u w => w ≤ u) (fun u w hu hw => ?_) (fun c₁ c₂ x y h => ?_)
    · simp only [eval, hu, hw, BinFn.apply, UnFn.apply, Value.isTrue] at ht
      by_cases hlt : u < w <;> simp_all <;> omega
    · simp only [Bound.Mem, Option.some.injEq, reduceCtorEq]
      constructor
      · intro _ h'; subst h'; omega
      · intro _ h'; cases h'
  case case7 p q ihp ihq =>
    obtain ⟨hp, hq⟩ := not_or3_true (v := p.eval row) (w := q.eval row)
      (by simpa [eval, BinFn.apply] using ht)
    exact (ihp (by simpa [eval] using hp)).append (ihq (by simpa [eval] using hq))
  case case8 i q ih =>
    intro f hf
    simp only [List.mem_filter] at hf
    by_cases hn : row.getD i .null = .null
    · exact Fact.holds_of_null hf.2 hn
    · have hq := not_and3_notnull_true (w := q.eval row) hn
        (by simpa [eval, BinFn.apply, List.getD_eq_getElem?_getD] using ht)
      exact ih (by simpa [eval] using hq) f hf.1
  case case9 => intro f hf; simp at hf

/-! ### Facts through a plan -/

def Fact.inRange (n : Nat) : Fact → Bool
  | .diff i j _ => i < n && j < n
  | .ne i _ => i < n

def Fact.shift (n : Nat) : Fact → Fact
  | .diff i j b => .diff (n + i) (n + j) b
  | .ne i k => .ne (n + i) k

/-- Re-index a fact: column `i` of the input appears at every position in `σ i`. -/
def Fact.rename (σ : Nat → List Nat) : Fact → List Fact
  | .diff i j b => (σ i).flatMap fun p => (σ j).map fun q => .diff p q b
  | .ne i k => (σ i).map fun p => .ne p k

/-- Positions of input column `i` in an emit mapping. -/
def positions (m : List Nat) (i : Nat) : List Nat :=
  (List.range m.length).filter fun p => m[p]? == some i

/-- Where input column `i` appears in the output of `Project es` over `n`
columns: at `i` itself and wherever an expression copies it. -/
def copyCols (n : Nat) (es : List Expr) (i : Nat) : List Nat :=
  i :: ((List.range es.length).filter fun k => es[k]? == some (.field i)).map (n + ·)

/-- Facts about computed columns that are an input column plus a constant. -/
def linFacts (n : Nat) : Nat → List Expr → List Fact
  | _, [] => []
  | col, e :: es =>
      let here := match e with
        | .field _ => []
        | e => match e.linTerm with
          | some (j, c) => if j < n then [.diff col j (.exact c)] else []
          | none => []
      here ++ linFacts n (col + 1) es

/-! ### Facts about window columns

Window column `w` reads column `c` of another row of the partition. When that
row comes earlier (`LAG`) and `c` is the first sort key, ascending, then
`$c - $w ≥ 0`; `LEAD` and descending keys flip the sign. A partition column
read from the same partition is equal to the row's own. Only for a NULL
default: any other default could break both. -/

def orderFact (sort : List SortKey) (c w : Nat) (before : Bool) (gap : Int) : List Fact :=
  match sort with
  | k :: _ =>
    if k.col = c then
      if k.desc = before then [.diff w c ⟨some gap, none⟩] else [.diff c w ⟨some gap, none⟩]
    else []
  | [] => []

def partFact (part : List Nat) (c w : Nat) : List Fact :=
  if c ∈ part then [.diff c w (.exact 0)] else []

/-- How far apart a row and the one `offset` rows away are on the sort key: at
least `1` when the partition and the only sort key are a key of the input
(`strict`), else at least `0`. -/
def strictGap (strict : Bool) (sort : List SortKey) (offset : Nat) : Int :=
  if strict && sort.length == 1 && 1 ≤ offset then 1 else 0

def winFact (part : List Nat) (sort : List SortKey) (strict : Bool) (w : Nat) : WinFn → List Fact
  | .rowNumber => []
  | .lag c k d =>
      if d = .null then orderFact sort c w true (strictGap strict sort k) ++ partFact part c w else []
  | .lead c k d =>
      if d = .null then orderFact sort c w false (strictGap strict sort k) ++ partFact part c w else []

/-- Facts about the window columns appended after `n` input columns. -/
def winFacts (part : List Nat) (sort : List SortKey) (strict : Bool) (n : Nat) (fns : List WinFn) :
    List Fact :=
  fns.zipIdx.flatMap fun (f, t) => winFact part sort strict (n + t) f

/-- Does the fact mention a column at or after `n`? -/
def Fact.rightOf (n : Nat) : Fact → Bool
  | .diff i j _ => decide (n ≤ i) || decide (n ≤ j)
  | .ne i _ => decide (n ≤ i)

/-- Facts that hold on every output row of a plan, given facts `F t` about
each table. -/
def Rel.facts (cat : Catalog) (F : String → List Fact) (T : WindowKeys) : Rel → List Fact
  | .read t => F t
  | .values _ _ => []
  | .filter r c => r.facts cat F T ++ c.factsOf
  | .project r es =>
      let fs := (r.facts cat F T).filter (·.inRange (r.arity cat))
      fs.flatMap (Fact.rename (copyCols (r.arity cat) es)) ++ linFacts (r.arity cat) (r.arity cat) es
  | .emit r m => (r.facts cat F T).flatMap (Fact.rename (positions m))
  | .cross a b =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++ (b.facts cat F T).map (·.shift (a.arity cat))
  | .join a b .inner on =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++
        (b.facts cat F T).map (·.shift (a.arity cat)) ++ on.factsOf
  -- NULL padding keeps every fact true: facts only speak about integers. So
  -- are the condition's facts that mention a right column.
  | .join a b .left on =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++ (b.facts cat F T).map (·.shift (a.arity cat)) ++
        on.factsOf.filter (·.rightOf (a.arity cat))
  | .fetch r _ _ => r.facts cat F T
  | .unionAll a b => (a.facts cat F T).filter ((b.facts cat F T).contains ·)
  | .window r part sort fns =>
      (r.facts cat F T).filter (·.inRange (r.arity cat)) ++
        winFacts part sort (T r part sort) (r.arity cat) fns
  -- Some of the left rows, or all of the rows in another order or once each.
  | .semi a _ _ _ => a.facts cat F T
  | .orderBy r _ | .distinct r => r.facts cat F T
  | .aggregate _ _ _ | .unnest _ _ => []

theorem Fact.rename_holds {σ : Nat → List Nat} {row row' : Row}
    (hσ : ∀ i, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    ∀ {f : Fact}, f.Holds row → ∀ g ∈ f.rename σ, g.Holds row'
  | .diff i j b, h, g, hg => by
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i p hp ▸ hx) (hσ j q hq ▸ hy)
  | .ne i k, h, g, hg => by
      simp only [Fact.rename, List.mem_map] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      intro hx
      exact h (hσ i p hp ▸ hx)

theorem FactsHold.rename {σ : Nat → List Nat} {fs : List Fact} {row row' : Row}
    (h : FactsHold fs row) (hσ : ∀ i, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    FactsHold (fs.flatMap (Fact.rename σ)) row' := by
  intro g hg
  simp only [List.mem_flatMap] at hg
  obtain ⟨f, hf, hg⟩ := hg
  exact Fact.rename_holds hσ (h f hf) g hg

/-- A fact whose columns are all `< n` only depends on the first `n` columns. -/
theorem Fact.holds_prefix {n : Nat} {row row' : Row}
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    ∀ {f : Fact}, f.inRange n = true → f.Holds row → f.Holds row'
  | .diff i j b, hr, h => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      intro x y hx hy
      exact h x y (hpre i hr.1 ▸ hx) (hpre j hr.2 ▸ hy)
  | .ne i k, hr, h => by
      simp only [Fact.inRange, decide_eq_true_eq] at hr
      intro hx; exact h (hpre i hr ▸ hx)

theorem FactsHold.prefix {n : Nat} {fs : List Fact} {row row' : Row} (h : FactsHold fs row)
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    FactsHold (fs.filter (·.inRange n)) row' := by
  intro f hf
  simp only [List.mem_filter] at hf
  exact Fact.holds_prefix hpre hf.2 (h f hf.1)

theorem FactsHold.shift {n : Nat} {fs : List Fact} {row row' : Row} (h : FactsHold fs row)
    (hsh : ∀ i, row'.getD (n + i) .null = row.getD i .null) :
    FactsHold (fs.map (·.shift n)) row' := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  have := h f hf
  cases f with
  | diff i j b => intro x y hx hy; exact this x y (hsh i ▸ hx) (hsh j ▸ hy)
  | ne i k => intro hx; exact this (hsh i ▸ hx)

theorem getD_append_left' {x y : Row} {i : Nat} (h : i < x.length) :
    (x ++ y).getD i .null = x.getD i .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {x y : Row} (i : Nat) :
    (x ++ y).getD (x.length + i) .null = y.getD i .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem Fact.rename_holds_inRange {σ : Nat → List Nat} {row row' : Row} {n : Nat}
    (hσ : ∀ i < n, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    ∀ {f : Fact}, f.inRange n = true → f.Holds row → ∀ g ∈ f.rename σ, g.Holds row'
  | .diff i j b, hr, h, g, hg => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i hr.1 p hp ▸ hx) (hσ j hr.2 q hq ▸ hy)
  | .ne i k, hr, h, g, hg => by
      simp only [Fact.inRange, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_map] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      intro hx; exact h (hσ i hr p hp ▸ hx)

theorem copyCols_getD {n : Nat} {es : List Expr} {row : Row} {i p : Nat}
    (hlen : row.length = n) (hi : i < n) (hp : p ∈ copyCols n es i) :
    (row ++ es.map (·.eval row)).getD p .null = row.getD i .null := by
  simp only [copyCols, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range,
    beq_iff_eq] at hp
  rcases hp with rfl | ⟨k, ⟨hk, hek⟩, rfl⟩
  · exact getD_append_left' (hlen ▸ hi)
  · rw [← hlen, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hek, Expr.eval]

theorem linFacts_sound {n : Nat} {row row' : Row}
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    ∀ (col : Nat) (es : List Expr),
      (∀ k < es.length, row'.getD (col + k) .null = (es[k]?.getD (.lit .null)).eval row) →
      FactsHold (linFacts n col es) row'
  | _, [], _ => fun f hf => by simp [linFacts] at hf
  | col, e :: es, hcols => by
      simp only [linFacts]
      refine FactsHold.append ?_ (linFacts_sound hpre (col + 1) es fun k hk => ?_)
      · have hcol : row'.getD col .null = e.eval row := by simpa using hcols 0 (by simp)
        split
        · intro f hf; simp at hf
        · split
          · rename_i j c hl
            split
            · rename_i hjn
              intro g hg
              simp only [List.mem_singleton] at hg; subst hg
              intro x y hx hy
              rw [hcol] at hx
              obtain ⟨y', hy', hxy⟩ := Expr.linTerm_of_int hl hx
              rw [hpre j hjn, hy'] at hy
              injection hy with hy; subst hy
              simp only [Bound.Mem, Bound.exact, Option.some.injEq]
              constructor <;> intro _ h <;> subst h <;> omega
            · intro g hg; simp at hg
          · intro g hg; simp at hg
      · have := hcols (k + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem FactsHold.shift_nulls {n : Nat} {fs : List Fact} {row : Row}
    (hnull : ∀ i, row.getD (n + i) .null = .null) : FactsHold (fs.map (·.shift n)) row := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨f, _, rfl⟩ := hg
  cases f with
  | diff i j b => intro x y hx _; rw [hnull i] at hx; cases hx
  | ne i k => intro hx; rw [hnull i] at hx; cases hx

theorem positions_getD {m : List Nat} {row : Row} {i p : Nat} (hp : p ∈ positions m i) :
    (m.map (row.getD · .null)).getD p .null = row.getD i .null := by
  simp only [positions, List.mem_filter, List.mem_range, beq_iff_eq] at hp
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp.2]

/-- **Soundness of fact collection**: every row a well-formed plan produces
satisfies every fact `Rel.facts` collects, provided the table facts hold. -/
theorem FactsHold.rightOf_nulls {n : Nat} {fs : List Fact} {row : Row}
    (hn : ∀ i, n ≤ i → row.getD i .null = .null) : FactsHold (fs.filter (·.rightOf n)) row := by
  intro f hf
  simp only [List.mem_filter] at hf
  cases f with
  | diff i j b =>
    simp only [Fact.rightOf, Bool.or_eq_true, decide_eq_true_eq] at hf
    rcases hf.2 with h | h
    · exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i h)
    · exact Fact.holds_of_null (i := j) (by simp [Fact.mentions]) (hn j h)
  | ne i k =>
    simp only [Fact.rightOf, decide_eq_true_eq] at hf
    exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i hf.2)

theorem getD_pad_null {x : Row} {m i : Nat} (h : x.length ≤ i) :
    (x ++ List.replicate m Value.null).getD i .null = .null := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [getD_append_right']
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem orderFact_sound {sort : List SortKey} {c w : Nat} {before : Bool} {gap : Int} {row x : Row}
    (hgap : gap = 0 ∨ gap = 1) (hxc : row.getD c .null = x.getD c .null)
    (hv : ∀ Y, row.getD w .null = .int Y → ∃ y, (y = x ∨
      (if before then sortLe sort y x else sortLe sort x y) = true) ∧ y.getD c .null = .int Y ∧
      (gap = 1 → ∀ k ∈ sort, y.getD k.col .null ≠ x.getD k.col .null)) :
    FactsHold (orderFact sort c w before gap) row := by
  match sort, hv with
  | [], _ => intro f hf; simp [orderFact] at hf
  | k :: ks, hv =>
    unfold orderFact
    by_cases hk : k.col = c
    · subst hk
      have key : ∀ X Y, row.getD k.col .null = .int X → row.getD w .null = .int Y →
          if k.desc = before then gap ≤ Y - X else gap ≤ X - Y := by
        intro X Y hX hY
        obtain ⟨y, hy, hyc, hne⟩ := hv Y hY
        rw [hxc] at hX
        have hne' : gap = 1 → Y ≠ X := fun h1 he => by
          subst he; exact hne h1 k (by simp) (by rw [hyc, hX])
        rcases hy with rfl | hy
        · rw [hX] at hyc
          cases hyc
          rcases hgap with rfl | rfl
          · split <;> omega
          · exact absurd rfl (hne' rfl)
        · cases before
          · have := SortKey.le_int (lexLe_left (by simpa [sortLe] using hy)) hX hyc
            rcases hgap with rfl | rfl <;> have := hne' <;> cases hd : k.desc <;> simp_all <;> omega
          · have := SortKey.le_int (lexLe_left (by simpa [sortLe] using hy)) hyc hX
            rcases hgap with rfl | rfl <;> have := hne' <;> cases hd : k.desc <;> simp_all <;> omega
      simp only [↓reduceIte]
      intro f hf
      split at hf <;> simp only [List.mem_singleton] at hf <;> subst hf <;> intro X Y hX hY
      · rename_i hd; have := key Y X hY hX; simp only [hd, ↓reduceIte] at this
        simp [Bound.Mem]; omega
      · rename_i hd; have := key X Y hX hY; simp only [hd, ↓reduceIte] at this
        simp [Bound.Mem]; omega
    · intro f hf; simp [hk] at hf

theorem partFact_sound {part : List Nat} {c w : Nat} {row x : Row}
    (hxc : row.getD c .null = x.getD c .null)
    (hv : ∀ Y, row.getD w .null = .int Y →
      ∃ y, (y = x ∨ samePart part x y = true) ∧ y.getD c .null = .int Y) :
    FactsHold (partFact part c w) row := by
  unfold partFact
  split
  · rename_i hc
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    intro X Y hX hY
    obtain ⟨y, hy, hyc⟩ := hv Y hY
    have : x.getD c .null = y.getD c .null := by
      rcases hy with rfl | hy
      · rfl
      · simp only [samePart, decide_eq_true_eq, List.map_inj_left] at hy; exact hy c hc
    rw [hxc, this, hyc] at hX
    cases hX
    simp [Bound.Mem, Bound.exact]
  · intro f hf; simp at hf

theorem strictGap_cases (strict : Bool) (sort : List SortKey) (k : Nat) :
    strictGap strict sort k = 0 ∨ strictGap strict sort k = 1 := by
  unfold strictGap; split <;> simp

theorem strictGap_one {strict : Bool} {sort : List SortKey} {k : Nat}
    (h : strictGap strict sort k = 1) : strict = true ∧ sort.length = 1 ∧ 1 ≤ k := by
  unfold strictGap at h
  split at h
  · rename_i hc; simpa [and_assoc] using hc
  · cases h

/-- Rows of the same partition that differ on the key `part ++ sort` differ on
the only sort key. -/
theorem sort_ne_of_key {part : List Nat} {sort : List SortKey} {x y : Row}
    (hs : sort.length = 1) (hp : samePart part x y = true)
    (hk : keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    ∀ k ∈ sort, y.getD k.col .null ≠ x.getD k.col .null := by
  match sort, hs with
  | [k], _ =>
    intro k' hk' he
    simp only [List.mem_singleton] at hk'
    subst hk'
    apply hk
    simp only [samePart, decide_eq_true_eq] at hp
    simp only [keyOf, List.map_inj_left, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton]
    intro c hc
    rcases hc with hc | rfl
    · exact (List.map_inj_left.mp hp c hc).symm
    · exact he

theorem winFact_sound {part : List Nat} {sort : List SortKey} {strict : Bool} {n w : Nat}
    {b a : List Row} {x row : Row} {f : WinFn} (hf : f.refsLt n = true)
    (hpre : ∀ i < n, row.getD i .null = x.getD i .null)
    (hw : row.getD w .null = f.value part b a x)
    (hb : ∀ y ∈ b, sortLe sort y x = true) (ha : ∀ y ∈ a, sortLe sort x y = true)
    (hdist : strict = true → ∀ y, (y ∈ b ∨ y ∈ a) → samePart part x y = true →
      keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    FactsHold (winFact part sort strict w f) row := by
  cases f with
  | rowNumber => intro g hg; simp [winFact] at hg
  | lag c k d =>
    simp only [winFact]
    split
    · rename_i hd
      subst hd
      have hc : c < n := by simpa [WinFn.refsLt] using hf
      have hv : ∀ Y, row.getD w .null = .int Y →
          ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ b ∧ samePart part x y = true)) ∧ y.getD c .null = .int Y := by
        intro Y hY
        rcases WinFn.value_lag' (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
          (d := .null) with h | ⟨y, hy, h⟩
        · rw [hw, h] at hY; cases hY
        · exact ⟨y, hy, by rw [← h, ← hw, hY]⟩
      refine FactsHold.append (orderFact_sound (strictGap_cases _ _ _) (hpre c hc) fun Y hY => ?_)
        (partFact_sound (hpre c hc) fun Y hY => ?_)
      · obtain ⟨y, hy | hy, hyc⟩ := hv Y hY
        · refine ⟨y, .inl hy.1, hyc, fun h1 => ?_⟩
          have := (strictGap_one h1).2.2; omega
        · refine ⟨y, .inr (by simpa using hb y hy.1), hyc, fun h1 => ?_⟩
          obtain ⟨hs, hl, _⟩ := strictGap_one h1
          exact sort_ne_of_key hl hy.2 (hdist hs y (.inl hy.1) hy.2)
      · obtain ⟨y, hy | hy, hyc⟩ := hv Y hY
        · exact ⟨y, .inl hy.1, hyc⟩
        · exact ⟨y, .inr hy.2, hyc⟩
    · intro g hg; simp at hg
  | lead c k d =>
    simp only [winFact]
    split
    · rename_i hd
      subst hd
      have hc : c < n := by simpa [WinFn.refsLt] using hf
      have hv : ∀ Y, row.getD w .null = .int Y →
          ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ a ∧ samePart part x y = true)) ∧ y.getD c .null = .int Y := by
        intro Y hY
        rcases WinFn.value_lead' (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
          (d := .null) with h | ⟨y, hy, h⟩
        · rw [hw, h] at hY; cases hY
        · exact ⟨y, hy, by rw [← h, ← hw, hY]⟩
      refine FactsHold.append (orderFact_sound (strictGap_cases _ _ _) (hpre c hc) fun Y hY => ?_)
        (partFact_sound (hpre c hc) fun Y hY => ?_)
      · obtain ⟨y, hy | hy, hyc⟩ := hv Y hY
        · refine ⟨y, .inl hy.1, hyc, fun h1 => ?_⟩
          have := (strictGap_one h1).2.2; omega
        · refine ⟨y, .inr (by simpa using ha y hy.1), hyc, fun h1 => ?_⟩
          obtain ⟨hs, hl, _⟩ := strictGap_one h1
          exact sort_ne_of_key hl hy.2 (hdist hs y (.inr hy.1) hy.2)
      · obtain ⟨y, hy | hy, hyc⟩ := hv Y hY
        · exact ⟨y, .inl hy.1, hyc⟩
        · exact ⟨y, .inr hy.2, hyc⟩
    · intro g hg; simp at hg

theorem winFacts_sound {part : List Nat} {sort : List SortKey} {strict : Bool} {n : Nat}
    {fns : List WinFn} {b a : List Row} {x : Row} (hx : x.length = n)
    (hf : ∀ f ∈ fns, f.refsLt n = true)
    (hb : ∀ y ∈ b, sortLe sort y x = true) (ha : ∀ y ∈ a, sortLe sort x y = true)
    (hdist : strict = true → ∀ y, (y ∈ b ∨ y ∈ a) → samePart part x y = true →
      keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    FactsHold (winFacts part sort strict n fns) (x ++ fns.map (·.value part b a x)) := by
  intro g hg
  simp only [winFacts, List.mem_flatMap] at hg
  obtain ⟨⟨f, t⟩, hft, hg⟩ := hg
  have hget := List.mem_zipIdx_iff_getElem?.mp hft
  refine winFact_sound (hf f (List.mem_of_getElem? hget))
    (fun i hi => getD_append_left' (hx ▸ hi)) ?_ hb ha hdist g hg
  rw [← hx, getD_append_right']
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hget]

theorem Rel.facts_sound {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat) :
    ∀ {r : Rel}, r.WF cat → ∀ row ∈ r.eval cat, FactsHold (r.facts cat F T) row
  | .read t, _, row, h => hF t row h
  | .values _ _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .filter r c, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact (facts_sound hcat hF hT hwf.1 row h.1).append (c.factsOf_sound h.2)
  | .project r es, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hlen := eval_arity hcat hwf.1 x hx
      have hfx := facts_sound hcat hF hT hwf.1 x hx
      have hpre : ∀ i < r.arity cat, (x ++ es.map (·.eval x)).getD i .null = x.getD i .null :=
        fun i hi => getD_append_left' (hlen ▸ hi)
      simp only [Rel.facts]
      refine FactsHold.append ?_ (linFacts_sound hpre _ es fun k hk => ?_)
      · intro g hg
        simp only [List.mem_flatMap, List.mem_filter] at hg
        obtain ⟨f, ⟨hf, hfr⟩, hg⟩ := hg
        exact Fact.rename_holds_inRange (fun i hi p hp => copyCols_getD hlen hi hp) hfr (hfx f hf) g hg
      · rw [← hlen, getD_append_right']
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  | .emit r m, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (facts_sound hcat hF hT hwf.1 x hx).rename fun i p hp => positions_getD hp
  | .cross a b, hwf, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      have hlen := eval_arity hcat hwf.1 x hx
      simp only [Rel.facts]
      exact ((facts_sound hcat hF hT hwf.1 x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound hcat hF hT hwf.2 y hy).shift fun i => hlen ▸ getD_append_right' i)
  | .join a b .inner on, hwf, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, ht⟩ := h
      have hlen := eval_arity hcat hwf.1 x hx
      simp only [Rel.facts]
      exact (((facts_sound hcat hF hT hwf.1 x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound hcat hF hT hwf.2.1 y hy).shift fun i => hlen ▸ getD_append_right' i)).append
        (on.factsOf_sound ht)
  | .join a b .left on, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hlen := eval_arity hcat hwf.1 x hx
      have hfx := facts_sound hcat hF hT hwf.1 x hx
      simp only [Rel.facts]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (FactsHold.shift_nulls fun i => by
            rw [← hlen, getD_append_right']
            simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)).append
          (FactsHold.rightOf_nulls fun i hi => getD_pad_null (hlen ▸ hi))
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, ht⟩ := h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          ((facts_sound hcat hF hT hwf.2.1 y hy).shift fun i => hlen ▸ getD_append_right' i)).append
          fun f hf => on.factsOf_sound ht f (List.mem_filter.mp hf).1
  | .fetch r _ _, hwf, row, h => by
      simp only [eval] at h
      have := facts_sound hcat hF hT (r := r) hwf
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .semi a _ _ _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact facts_sound hcat hF hT hwf.1 row h.1
  | .orderBy r _, hwf, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact facts_sound hcat hF hT (r := r) hwf.1 row h
  | .distinct r, hwf, row, h => by
      simp only [eval, mem_dedup] at h
      exact facts_sound hcat hF hT (r := r) hwf row h
  | .aggregate _ _ _, _, _, _ | .unnest _ _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .unionAll a b, hwf, row, h => by
      simp only [eval, List.mem_append] at h
      intro f hf
      simp only [Rel.facts, List.mem_filter, List.contains_iff_mem] at hf
      rcases h with h | h
      · exact facts_sound hcat hF hT hwf.1 row h f hf.1
      · exact facts_sound hcat hF hT hwf.2.1 row h f hf.2
  | .window r part sort _, hwf, row, h => by
      obtain ⟨b, x, a, he, hx, rfl⟩ := mem_windowEval h
      obtain ⟨hb, ha, _⟩ := sorted_split he
      have hlen := eval_arity hcat hwf.1 x hx
      simp only [Rel.facts]
      refine ((facts_sound hcat hF hT hwf.1 x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        (winFacts_sound hlen hwf.2.2.2 hb ha fun hs y hy _ => ?_)
      -- With a key, rows at different positions of the sorted input differ on it.
      have hk := (hT _ _ _ hs hwf.1).perm (List.mergeSort_perm _ (sortLe sort)).symm
        fun h => Ne.symm h
      unfold KeyOn at hk
      rw [he, List.pairwise_append, List.pairwise_cons] at hk
      rcases hy with hy | hy
      · exact hk.2.2 y hy x (by simp)
      · exact Ne.symm (hk.2.1.1 y hy)

/-! ### Using facts when evaluating expressions -/

/-- A bound on `x - y` for columns `i` and `j`, from the facts. -/
def Fact.diffBound (i j : Nat) : Fact → Option Bound
  | .diff i' j' b => if i' = i ∧ j' = j then some b else if i' = j ∧ j' = i then some b.neg else none
  | .ne _ _ => none

/-- What all facts together say about `$i - $j` (`ts_right <= ts` and
`ts_right >= ts - 10` give `0 ≤ ts - ts_right ≤ 10`). -/
def Fact.diffOf (fs : List Fact) (i j : Nat) : Option Bound :=
  match fs.filterMap (Fact.diffBound i j) with
  | [] => none
  | b :: bs => some (bs.foldl Bound.meet b)

/-- A bound on `a - b` for two linear terms, from the facts. -/
def termDiff (fs : List Fact) (a b : Expr) : Option Bound :=
  match a.linTerm, b.linTerm with
  | some (i, c₁), some (j, c₂) => (Fact.diffOf fs i j).map (·.add (.exact (c₁ - c₂)))
  | _, _ => none

/-- No booleans or strings: only integers or NULL. -/
def AVal.intOrNull (a : AVal) : Bool := !a.tt && !a.ff && !a.str

def subSharpen : Option Bound → AVal → AVal
  | some d, base => { base with int := base.int.map fun _ => d }
  | none, base => base

def ltSharpen : Option Bound → AVal → AVal
  | some d, base => { base with tt := base.tt && canLt d (.exact 0), ff := base.ff && canGe d (.exact 0) }
  | none, base => base

def eqSharpen (d : Bound) (base : AVal) : AVal :=
  { base with tt := base.tt && canEq d (.exact 0), ff := base.ff && canNe d (.exact 0) }

/-- `t = k` cannot be TRUE when a fact excludes the value. -/
def neSharpen (fs : List Fact) (a b : Expr) (base : AVal) : AVal :=
  match a.linTerm, b with
  | some (j, c), .lit (.int k) => if fs.contains (.ne j (k - c)) then { base with tt := false } else base
  | _, _ => base

/-- Sharpen the abstract result of `f a b` using facts about `a` and `b`
(`aa` is the abstract value of `a`). -/
def sharpen (fs : List Fact) (f : BinFn) (a b : Expr) (aa base : AVal) : AVal :=
  match f with
  | .sub => subSharpen (termDiff fs a b) base
  -- Facts are about integers; strings compare by themselves.
  | .lt => if aa.intOrNull then ltSharpen (termDiff fs a b) base else base
  | .eq =>
      match termDiff fs a b with
      | some d => if aa.intOrNull then eqSharpen d base else base
      | none => neSharpen fs a b base
  | _ => base

/-- `FALSE OR v`: `v` if it is a boolean, else NULL. -/
def AVal.orFalse (a : AVal) : AVal := ⟨a.null || a.int.isSome || a.str, none, a.tt, a.ff, false⟩

/-- `p OR q` for a boolean `p`: TRUE where `p` is, else `q` on rows where
`NOT p` holds (`bq` is `q` under that refinement). This proves guarded
conditions such as `prev IS NULL OR prev <= ts`. -/
def orSplit (ap bq : AVal) : AVal :=
  (if ap.tt then AVal.ofValue (.bool true) else AVal.bot).join (if ap.ff then bq.orFalse else AVal.bot)

/-- An interval with values in it. -/
def Bound.nonEmpty (b : Bound) : Bool :=
  match b.lo, b.hi with
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- `a` without an empty interval: such a value is no integer. -/
def AVal.prune (a : AVal) : AVal := { a with int := a.int.filter Bound.nonEmpty }

theorem AVal.prune_mem {a : AVal} : ∀ {v : Value}, a.Mem v → a.prune.Mem v
  | .int i, ⟨b, hb, hm⟩ => by
      refine ⟨b, ?_, hm⟩
      have : b.nonEmpty = true := by
        unfold Bound.nonEmpty
        split
        · rename_i l h hl hh
          exact decide_eq_true (Int.le_trans (hm.1 l hl) (hm.2 h hh))
        · rfl
      simp [AVal.prune, hb, Option.filter, this]
  | .null, h | .bool true, h | .bool false, h | .str _, h | .list _, h => h

theorem EnvMem.prune {env : List AVal} {row : Row} (h : EnvMem env row) :
    EnvMem (env.map AVal.prune) row := by
  intro i
  have htop : AVal.top.prune = AVal.top := by
    simp [AVal.prune, AVal.top, Bound.top, Option.filter, Bound.nonEmpty]
  have := AVal.prune_mem (h i)
  rw [← htop] at this ⊢
  cases hi : env[i]? <;> simp_all [List.getD_eq_getElem?_getD]

/-- `NULL OR v`: TRUE where `v` is, else NULL. -/
def AVal.orNull (a : AVal) : AVal := ⟨a.null || a.ff || a.int.isSome || a.str, none, a.tt, false, false⟩

/-- `p OR q` for a `p` that is a boolean or NULL: as `orSplit`, and where `p`
is NULL, TRUE only where `q` is (`bq` is `q` where `p` is not TRUE). This
proves `x >= 0 OR x IS NULL` for a column `x` that may be NULL. -/
def orSplitNull (ap bq : AVal) : AVal :=
  (orSplit ap bq).join (if ap.null then bq.orNull else AVal.bot)

def Expr.absD (env : List AVal) (fs : List Fact) (ks : Assumptions := []) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => narrowAll ks (.field i) (env.getD i AVal.top)
  | .un f a => narrowAll ks (.un f a) (f.abs (a.absD env fs ks))
  | .bin f a b => narrowAll ks (.bin f a b) <|
      if f = .or ∧ (a.absD env fs ks).nonBool = false then
        orSplit (a.absD env fs ks) (b.absD ((Expr.un .not a).refine env) fs (a.cstrs false ++ ks))
      else if f = .or ∧ (a.absD env fs ks).int.isNone = true ∧ (a.absD env fs ks).str = false then
        orSplitNull (a.absD env fs ks)
          (b.absD ((a.refineNeg env).map AVal.prune) fs (a.cstrs false ++ ks))
      else sharpen fs f a b (a.absD env fs ks) (f.abs (a.absD env fs ks) (b.absD env fs ks))
  -- Each branch is evaluated knowing whether `c` is TRUE.
  | .ifThen c t e => narrowAll ks (.ifThen c t e) <|
      let ac := c.absD env fs ks
      (if ac.tt then t.absD (c.refine env) fs (c.cstrs true ++ ks) else AVal.bot).join
        (if ac.nonBool || ac.ff then e.absD (c.refineNeg env) fs (c.cstrs false ++ ks)
         else AVal.bot)

theorem Bound.mem_exact_iff {k i : Int} : (Bound.exact k).Mem i ↔ i = k := by
  simp only [Bound.Mem, Bound.exact, Option.some.injEq]
  constructor
  · intro ⟨h₁, h₂⟩; have := h₁ k rfl; have := h₂ k rfl; omega
  · rintro rfl; constructor <;> intro _ h <;> subst h <;> omega

theorem canLt_of_lt {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : i < j) :
    canLt x y = true := by
  obtain ⟨xl, xh⟩ := x
  obtain ⟨yl, yh⟩ := y
  simp only [Bound.Mem] at hx hy
  unfold canLt
  cases xl <;> cases yh <;> simp_all <;> omega

theorem canNe_of_ne {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : i ≠ j) :
    canNe x y = true := by
  unfold canNe
  split
  · rename_i k k' hk hk'
    rw [← Bound.point_mem hk hx, ← Bound.point_mem hk' hy]
    simpa using h
  · rfl

theorem Fact.diffBound_sound {f : Fact} {row : Row} {i j : Nat} {d : Bound} {x y : Int}
    (hg : f.diffBound i j = some d) (hh : f.Holds row)
    (hx : row.getD i .null = .int x) (hy : row.getD j .null = .int y) : d.Mem (x - y) := by
  cases f with
  | ne _ _ => simp [Fact.diffBound] at hg
  | diff i' j' b =>
    simp only [Fact.diffBound] at hg
    split at hg
    · rename_i h; obtain ⟨rfl, rfl⟩ := h
      cases hg; exact hh x y hx hy
    · split at hg
      · rename_i _ h; obtain ⟨rfl, rfl⟩ := h
        cases hg
        have := Bound.mem_neg (hh y x hy hx)
        simpa [Int.neg_sub] using this
      · cases hg

theorem foldl_meet_mem {z : Int} : ∀ {bs : List Bound} {b : Bound}, b.Mem z →
    (∀ b' ∈ bs, b'.Mem z) → (bs.foldl Bound.meet b).Mem z
  | [], _, hb, _ => hb
  | b' :: bs, _, hb, h => by
      rw [List.foldl_cons]
      exact foldl_meet_mem (Bound.mem_meet hb (h b' (by simp))) fun c hc => h c (by simp [hc])

theorem Fact.diffOf_sound {fs : List Fact} {row : Row} {i j : Nat} {d : Bound} {x y : Int}
    (hd : Fact.diffOf fs i j = some d) (hfs : FactsHold fs row)
    (hx : row.getD i .null = .int x) (hy : row.getD j .null = .int y) : d.Mem (x - y) := by
  have hall : ∀ b ∈ fs.filterMap (Fact.diffBound i j), b.Mem (x - y) := by
    intro b hb
    obtain ⟨f, hf, hg⟩ := List.mem_filterMap.mp hb
    exact Fact.diffBound_sound hg (hfs f hf) hx hy
  unfold Fact.diffOf at hd
  split at hd
  · cases hd
  · rename_i b bs h
    cases hd
    rw [h] at hall
    exact foldl_meet_mem (hall b (by simp)) fun c hc => hall c (by simp [hc])

theorem termDiff_sound {fs : List Fact} {row : Row} {a b : Expr} {d : Bound} {u w : Int}
    (hd : termDiff fs a b = some d) (hfs : FactsHold fs row)
    (hu : a.eval row = .int u) (hw : b.eval row = .int w) : d.Mem (u - w) := by
  unfold termDiff at hd
  split at hd
  · rename_i i c₁ j c₂ h₁ h₂
    obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨x, hx, rfl⟩ := Expr.linTerm_of_int h₁ hu
    obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_int h₂ hw
    have := Bound.mem_add (Fact.diffOf_sound hd₀ hfs hx hy) (Bound.mem_exact (c₁ - c₂))
    have heq : x + c₁ - (y + c₂) = x - y + (c₁ - c₂) := by omega
    rw [heq]; exact this
  · cases hd

theorem subSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .sub (a.eval row) (b.eval row))) :
    (subSharpen (termDiff fs a b) base).Mem (BinFn.apply .sub (a.eval row) (b.eval row)) := by
  cases hd : termDiff fs a b with
  | none => exact hbase
  | some d =>
    simp only [subSharpen]
    generalize hva : a.eval row = va at hbase ⊢
    generalize hvb : b.eval row = vb at hbase ⊢
    cases va <;> cases vb <;> simp only [BinFn.apply] at hbase ⊢ <;> try exact hbase
    obtain ⟨b₀, hb₀, _⟩ := hbase
    exact ⟨d, by simp [hb₀], termDiff_sound hd hfs hva hvb⟩

theorem ltSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {aa base : AVal}
    (hfs : FactsHold fs row) (hint : aa.intOrNull = true) (haa : aa.Mem (a.eval row))
    (hbase : base.Mem (BinFn.apply .lt (a.eval row) (b.eval row))) :
    (ltSharpen (termDiff fs a b) base).Mem (BinFn.apply .lt (a.eval row) (b.eval row)) := by
  cases hd : termDiff fs a b with
  | none => exact hbase
  | some d =>
    simp only [ltSharpen]
    generalize hva : a.eval row = va at hbase haa ⊢
    generalize hvb : b.eval row = vb at hbase ⊢
    cases va <;> cases vb <;> simp only [BinFn.apply] at hbase ⊢ <;> try exact hbase
    -- Strings are ruled out by `hint`.
    all_goals try (simp_all [AVal.intOrNull, AVal.Mem]; done)
    rename_i u w
    have hm := termDiff_sound hd hfs hva hvb
    by_cases hlt : u < w
    · simp only [hlt, decide_true, AVal.Mem] at hbase ⊢
      simp [hbase, canLt_of_lt hm (Bound.mem_exact 0) (by omega)]
    · simp only [hlt, decide_false, AVal.Mem] at hbase ⊢
      simp [hbase, canGe_of_le hm (Bound.mem_exact 0) (by omega)]

theorem eqSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {aa base : AVal} {d : Bound}
    (hfs : FactsHold fs row) (hd : termDiff fs a b = some d) (hint : aa.intOrNull = true)
    (haa : aa.Mem (a.eval row)) (hbase : base.Mem (BinFn.apply .eq (a.eval row) (b.eval row))) :
    (eqSharpen d base).Mem (BinFn.apply .eq (a.eval row) (b.eval row)) := by
  simp only [AVal.intOrNull, Bool.and_eq_true, Bool.not_eq_true'] at hint
  simp only [eqSharpen]
  generalize hva : a.eval row = va at hbase haa ⊢
  generalize hvb : b.eval row = vb at hbase ⊢
  cases va <;> cases vb <;> simp only [BinFn.apply] at hbase ⊢ <;> try exact hbase
  -- Booleans and strings are ruled out by `hint`.
  all_goals first
    | (rename_i u _; cases u <;> simp_all [AVal.Mem]; done)
    | (simp_all [AVal.Mem]; done)
    | skip
  rename_i u w
  have hm := termDiff_sound hd hfs hva hvb
  by_cases huw : u = w
  · subst huw
    simp only [beq_self_eq_true, AVal.Mem] at hbase ⊢
    simp [hbase, canEq, canGe_of_le hm (Bound.mem_exact 0) (by omega),
      canGe_of_le (Bound.mem_exact 0) hm (by omega)]
  · have hne : (u == w) = false := by simpa using huw
    simp only [hne, AVal.Mem] at hbase ⊢
    simp [hbase, canNe_of_ne hm (Bound.mem_exact 0) (by omega)]

theorem neSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .eq (a.eval row) (b.eval row))) :
    (neSharpen fs a b base).Mem (BinFn.apply .eq (a.eval row) (b.eval row)) := by
  unfold neSharpen
  split
  · rename_i _ j c k hl
    split
    · rename_i hne
      have hh := hfs _ (List.contains_iff_mem.mp hne)
      generalize hva : a.eval row = va at hbase ⊢
      cases va <;> simp only [Expr.eval, BinFn.apply] at hbase ⊢ <;> try exact hbase
      rename_i u
      by_cases huk : u = k
      · subst huk
        obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_int hl hva
        exact absurd (by rw [hy]; congr 1; omega) hh
      · have : (u == k) = false := by simpa using huk
        simp only [this, AVal.Mem] at hbase ⊢
        exact hbase
    · exact hbase
  · exact hbase

theorem sharpen_sound {fs : List Fact} {row : Row} (f : BinFn) (a b : Expr) {aa base : AVal}
    (hfs : FactsHold fs row) (haa : aa.Mem (a.eval row))
    (hbase : base.Mem (f.apply (a.eval row) (b.eval row))) :
    (sharpen fs f a b aa base).Mem (f.apply (a.eval row) (b.eval row)) := by
  cases f
  case sub => exact subSharpen_sound hfs hbase
  case lt =>
    simp only [sharpen]
    split
    · rename_i hint; exact ltSharpen_sound hfs hint haa hbase
    · exact hbase
  case eq =>
    simp only [sharpen]
    cases hd : termDiff fs a b with
    | none => exact neSharpen_sound hfs hbase
    | some d =>
      simp only []
      split
      · rename_i hint; exact eqSharpen_sound hfs hd hint haa hbase
      · exact hbase
  all_goals exact hbase

theorem Expr.absD_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ e : Expr, (e.absD env fs ks).Mem (e.eval row)
  | .lit v => AVal.mem_ofValue v
  | .field i => narrowAll_sound hks (h i)
  | .un f a => narrowAll_sound hks (UnFn.abs_sound f (Expr.absD_sound h hfs hks a))
  | .bin f a b => by
      simp only [absD]
      refine narrowAll_sound hks ?_
      simp only [eval]
      split
      · rename_i hc
        obtain ⟨rfl, hnb⟩ := hc
        have ha := Expr.absD_sound h hfs hks a
        rcases mem_cases ha with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
        · simp [AVal.nonBool, hn] at hnb
        · simp [AVal.nonBool, hb] at hnb
        · rw [hv]
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hr := Expr.refine_sound env (.un .not a) h (by simp [eval, hv, UnFn.apply, Value.isTrue])
          have hks' := KsHold.cons_cstrs (c := a) (pos := false)
            (by simp [hv, Value.isTrue]) hks
          have hq := Expr.absD_sound hr hfs hks' b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ | ⟨_, hv', hs⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem]
        · simp [AVal.nonBool, hs] at hnb
        · simp [AVal.nonBool, hs] at hnb
      split
      · rename_i _ hc
        obtain ⟨rfl, hni, hns⟩ := hc
        have ha := Expr.absD_sound h hfs hks a
        rcases mem_cases ha with ⟨hv, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ |
            ⟨_, _, hs⟩
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (Expr.refineNeg_sound env a h hnt).prune hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hn]
          rcases mem_cases hq with ⟨hv', hn'⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
              ⟨_, hv', hs⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orNull, AVal.Mem]
        · simp [hb] at hni
        · rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (Expr.refineNeg_sound env a h hnt).prune hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
              ⟨_, hv', hs⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem]
        · simp [hs] at hns
        · simp [hs] at hns
      · exact sharpen_sound f a b hfs (Expr.absD_sound h hfs hks a)
          (BinFn.abs_sound f (Expr.absD_sound h hfs hks a) (Expr.absD_sound h hfs hks b))
  | .ifThen c t e => by
      have hc := Expr.absD_sound h hfs hks c
      simp only [absD]
      refine narrowAll_sound hks ?_
      simp only [eval]
      by_cases hct : (c.eval row).isTrue = true
      · rw [ite_eq_left hct]
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.absD env fs ks).tt = true := hc
        apply AVal.mem_join_left
        rw [ite_eq_left htt]
        exact Expr.absD_sound (Expr.refine_sound env c h hct) hfs (KsHold.cons_cstrs hct hks) t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.absD env fs ks).nonBool || (c.absD env fs ks).ff) = true := by
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        have hf : (c.eval row).isTrue = false := by simpa using hct
        exact Expr.absD_sound (Expr.refineNeg_sound env c h hf) hfs (KsHold.cons_cstrs hf hks) e

/-! ## Abstract plan evaluation -/

/-- Exactly `n` columns: missing ones are unknown. -/
def fit (n : Nat) (env : List AVal) : List AVal := (List.range n).map (env.getD · AVal.top)

def AVal.nullable (a : AVal) : AVal := { a with null := true }

/-- `ROW_NUMBER` is a positive integer; `LAG`/`LEAD` read a value of the same
column of another input row, or give the default. -/
def WinFn.abs (env : List AVal) : WinFn → AVal
  | .rowNumber => ⟨false, some ⟨some 1, none⟩, false, false, false⟩
  | .lag c _ d | .lead c _ d => (env.getD c AVal.top).join (AVal.ofValue d)

/-- Sums of integers in `b` keep their sign. -/
def sumBound (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
   b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩

/-- Some double, or NULL. -/
def AVal.double : AVal := ⟨true, some Bound.top, false, false, false⟩

/-- A measure over rows described by `env` and `fs`: a count is a natural
number, a sum of integers keeps their sign, `MIN` and `MAX` are among the
argument's values, and the other measures are doubles. All but `COUNT` may
be NULL. -/
def Measure.abs (env : List AVal) (fs : List Fact) (m : Measure) : AVal :=
  let a := m.arg.absD env fs
  match m.fn with
  | .count => ⟨false, some (Bound.ge 0), false, false, false⟩
  | .sum => ⟨true, some (match a.int with | some b => sumBound b | none => Bound.top), false, false, false⟩
  | .fsum | .avg => AVal.double
  | .min | .max => a.nullable
  | .collect => AVal.top

/-- Abstract evaluation. `A t` describes the columns of table `t`; `F t` holds
facts about its rows. Computed columns use the facts of their input. -/
def Rel.aeval (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Rel → List AVal
  | .read t => fit (cat t).arity (A t)
  | .values n _ => List.replicate n AVal.top
  | .filter r c => c.refine (r.aeval cat A F T)
  | .project r es => r.aeval cat A F T ++ es.map (·.absD (r.aeval cat A F T) (r.facts cat F T))
  | .emit r m => m.map ((r.aeval cat A F T).getD · AVal.top)
  | .cross a b => a.aeval cat A F T ++ b.aeval cat A F T
  | .join a b .inner on => on.refine (a.aeval cat A F T ++ b.aeval cat A F T)
  | .join a b .left _ => a.aeval cat A F T ++ (b.aeval cat A F T).map AVal.nullable
  | .fetch r _ _ => r.aeval cat A F T
  | .unionAll a b => List.zipWith AVal.join (a.aeval cat A F T) (b.aeval cat A F T)
  | .window r _ _ fns => r.aeval cat A F T ++ fns.map (WinFn.abs (r.aeval cat A F T))
  | .semi a _ _ _ => a.aeval cat A F T
  | .orderBy r _ | .distinct r => r.aeval cat A F T
  | .unnest r c => (r.aeval cat A F T).set c AVal.top
  | .aggregate r gs ms =>
      gs.map (·.absD (r.aeval cat A F T) (r.facts cat F T)) ++
        ms.map (Measure.abs (r.aeval cat A F T) (r.facts cat F T))

theorem Rel.aeval_length {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
    {T : WindowKeys} :
    ∀ {r : Rel}, r.WF cat → (r.aeval cat A F T).length = r.arity cat
  | .read _, _ => by simp [aeval, fit, arity]
  | .values _ _, _ => by simp [aeval, arity]
  | .filter r _, h => by simp [aeval, arity, Expr.refine_length, aeval_length (r := r) h.1]
  | .project r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .emit _ _, _ => by simp [aeval, arity]
  | .cross a b, h => by simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2]
  | .join a b .inner _, h => by
      simp [aeval, arity, Expr.refine_length, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1]
  | .join a b .left _, h => by
      simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1]
  | .fetch r _ _, h => by simp [aeval, arity, aeval_length (r := r) h]
  | .unionAll a b, h => by
      simp [aeval, arity, aeval_length (r := a) h.1, aeval_length (r := b) h.2.1, h.2.2]
  | .window r _ _ _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .semi a _ _ _, h => by simp [aeval, arity, aeval_length (r := a) h.1]
  | .orderBy r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .distinct r, h => by simp [aeval, arity, aeval_length (r := r) h]
  | .unnest r _, h => by simp [aeval, arity, aeval_length (r := r) h.1]
  | .aggregate _ _ _, _ => by simp [aeval, arity]

theorem EnvMem.append {e₁ e₂ : List AVal} {r₁ r₂ : Row} (h₁ : EnvMem e₁ r₁) (h₂ : EnvMem e₂ r₂)
    (hl : e₁.length = r₁.length) : EnvMem (e₁ ++ e₂) (r₁ ++ r₂) := by
  intro j
  have := h₁ j; have := h₂ (j - r₁.length)
  simp only [List.getD_eq_getElem?_getD] at *
  by_cases hj : j < e₁.length
  · rwa [List.getElem?_append_left hj, List.getElem?_append_left (hl ▸ hj)]
  · rwa [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

theorem EnvMem.map {env : List AVal} {row : Row} (h : EnvMem env row) (es : List Expr) :
    EnvMem (es.map (·.abs env)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.abs_sound h]

theorem EnvMem.mapD {env : List AVal} {fs : List Fact} {row : Row} (h : EnvMem env row)
    (hfs : FactsHold fs row) (es : List Expr) :
    EnvMem (es.map (·.absD env fs)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.absD_sound h hfs (ks := []) (by simp [KsHold])]

theorem EnvMem.emit {env : List AVal} {row : Row} (h : EnvMem env row) (m : List Nat) :
    EnvMem (m.map (env.getD · AVal.top)) (m.map (row.getD · .null)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hm : m[j]? <;> simp [AVal.mem_top]
  have := h ‹Nat›
  simpa [getD_top_eq, List.getD_eq_getElem?_getD] using this

theorem EnvMem.fit {env : List AVal} {row : Row} (h : EnvMem env row) (n : Nat) :
    EnvMem (fit n env) row := by
  intro j
  simp only [_root_.Substrait.fit, getD_top_eq, List.getElem?_map]
  by_cases hj : j < n
  · simpa [hj, getD_top_eq] using h j
  · simp [hj, AVal.mem_top]

theorem EnvMem.replicate (n : Nat) (row : Row) : EnvMem (List.replicate n AVal.top) row := by
  intro j
  simp only [getD_top_eq, List.getElem?_replicate]
  split <;> simp [AVal.mem_top]

theorem AVal.mem_nullable {a : AVal} : ∀ {v}, a.Mem v → a.nullable.Mem v
  | .null, _ => rfl
  | .int _, h | .bool true, h | .bool false, h | .str _, h | .list _, h => h

/-- A column replaced by any value, its description by `AVal.top`. -/
theorem EnvMem.set_top {env : List AVal} {row : Row} (h : EnvMem env row) (c : Nat) (v : Value) :
    EnvMem (env.set c AVal.top) (row.set c v) := by
  intro j
  by_cases hj : c = j
  · subst hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self']
    cases env[c]? <;> simp [AVal.mem_top]
  · have := h j
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hj] using this

theorem EnvMem.nullable {env : List AVal} {row : Row} (h : EnvMem env row) :
    EnvMem (env.map AVal.nullable) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_map] at *
  cases hj : env[j]? with
  | none => simp [AVal.mem_top]
  | some a =>
    simp only [hj, Option.map_some, Option.getD_some] at this ⊢
    exact AVal.mem_nullable this

theorem EnvMem.nulls (env : List AVal) (m : Nat) :
    EnvMem (env.map AVal.nullable) (List.replicate m .null) := by
  intro j
  simp only [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  cases env[j]? <;> split <;> simp [AVal.top, AVal.nullable, AVal.Mem]

theorem intSum_nonneg : ∀ {vs : List Value}, (∀ i, .int i ∈ vs → 0 ≤ i) → 0 ≤ intSum vs
  | [], _ => by simp [intSum]
  | .int i :: vs, h => by
    have := intSum_nonneg (vs := vs) fun j hj => h j (List.mem_cons_of_mem _ hj)
    have := h i (by simp); simp only [intSum]; omega
  | .null :: vs, h | .bool _ :: vs, h | .str _ :: vs, h | .list _ :: vs, h => by
    simp only [intSum]; exact intSum_nonneg fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem intSum_nonpos : ∀ {vs : List Value}, (∀ i, .int i ∈ vs → i ≤ 0) → intSum vs ≤ 0
  | [], _ => by simp [intSum]
  | .int i :: vs, h => by
    have := intSum_nonpos (vs := vs) fun j hj => h j (List.mem_cons_of_mem _ hj)
    have := h i (by simp); simp only [intSum]; omega
  | .null :: vs, h | .bool _ :: vs, h | .str _ :: vs, h | .list _ :: vs, h => by
    simp only [intSum]; exact intSum_nonpos fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem sumBound_sound {b : Bound} {vs : List Value} (h : ∀ i, .int i ∈ vs → b.Mem i) :
    (sumBound b).Mem (intSum vs) := by
  constructor
  · intro l hl
    cases hb : b.lo with
    | none => simp [sumBound, hb] at hl
    | some l₀ =>
      simp only [sumBound, hb, Option.bind_some] at hl
      split at hl
      · cases hl; exact intSum_nonneg fun i hi => by have := (h i hi).1 l₀ hb; omega
      · cases hl
  · intro u hu
    cases hb : b.hi with
    | none => simp [sumBound, hb] at hu
    | some h₀ =>
      simp only [sumBound, hb, Option.bind_some] at hu
      split at hu
      · cases hu; exact intSum_nonpos fun i hi => by have := (h i hi).2 h₀ hb; omega
      · cases hu

theorem Measure.abs_sound {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (m : Measure) :
    (m.abs env fs).Mem (m.eval grp) := by
  have hin : ∀ v ∈ m.inputs grp, (m.arg.absD env fs).Mem v := by
    intro v hv
    obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
    exact Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) m.arg
  unfold Measure.abs Measure.eval
  cases hf : m.fn <;> dsimp only
  case collect => exact AVal.mem_top _
  case count => exact ⟨_, rfl, by simp [Bound.Mem, Bound.ge]⟩
  case sum =>
    cases hvs : m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [AggFn.apply]
      refine ⟨_, rfl, ?_⟩
      cases ha : (m.arg.absD env fs).int with
      | none => exact Bound.mem_top _
      | some b =>
        refine sumBound_sound fun i hi => ?_
        have := hin (.int i) (hvs ▸ hi)
        obtain ⟨b', hb', hm⟩ := this
        rw [ha] at hb'; cases hb'; exact hm
  case fsum | avg =>
    cases m.inputs grp <;> simp only [AggFn.apply] <;> first | rfl | exact ⟨_, rfl, Bound.mem_top _⟩
  case min | max =>
    have hmm := AggFn.apply_minmax (f := m.fn) (by simp [hf]) (vs := m.inputs grp)
    rw [hf] at hmm
    rcases hmm with h | h
    · rw [h]; rfl
    · exact AVal.mem_nullable (hin _ h)

theorem EnvMem.measures {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (ms : List Measure) :
    EnvMem (ms.map (Measure.abs env fs)) (ms.map (·.eval grp)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ms[j]? <;> simp [AVal.mem_top, Measure.abs_sound hall]

/-- **Soundness of abstract plan evaluation**: every row a well-formed plan
produces is described by `Rel.aeval`, provided the tables are. -/
theorem WinFn.abs_sound {env : List AVal} {part : List Nat} {b a : List Row} {x : Row}
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) :
    ∀ f : WinFn, (f.abs env).Mem (f.value part b a x)
  | .rowNumber => ⟨_, rfl, by simp [Bound.Mem]; omega⟩
  | .lag c k d => by
      simp only [WinFn.abs]
      rcases WinFn.value_lag (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
        (d := d) with h | ⟨y, hy, h⟩
      · rw [h]; exact AVal.mem_join_right (AVal.mem_ofValue d)
      · rw [h]
        exact AVal.mem_join_left (hall y (hy.elim .inl fun hy => .inr (.inl hy.1)) c)
  | .lead c k d => by
      simp only [WinFn.abs]
      rcases WinFn.value_lead (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
        (d := d) with h | ⟨y, hy, h⟩
      · rw [h]; exact AVal.mem_join_right (AVal.mem_ofValue d)
      · rw [h]
        exact AVal.mem_join_left (hall y (hy.elim .inl fun hy => .inr (.inr hy.1)) c)

theorem EnvMem.window {env : List AVal} {part : List Nat} {b a : List Row} {x : Row}
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) (fns : List WinFn) :
    EnvMem (fns.map (WinFn.abs env)) (fns.map (·.value part b a x)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases fns[j]? <;> simp [AVal.mem_top, WinFn.abs_sound hall]

theorem Rel.aeval_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat) :
    ∀ {r : Rel}, r.WF cat → ∀ row ∈ r.eval cat, EnvMem (r.aeval cat A F T) row
  | .read t, _, row, h => (hA t row h).fit _
  | .values _ _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact Expr.refine_sound _ c (aeval_sound hcat hA hF hT hwf.1 row h.1) h.2
  | .project r es, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hm := aeval_sound hcat hA hF hT hwf.1 x hx
      exact hm.append (hm.mapD (Rel.facts_sound hcat hF hT hwf.1 x hx) es)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .emit r m, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 x hx).emit m
  | .cross a b, hwf, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 x hx).append (aeval_sound hcat hA hF hT hwf.2 y hy)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .join a b .inner on, hwf, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, ht⟩ := h
      exact Expr.refine_sound _ on ((aeval_sound hcat hA hF hT hwf.1 x hx).append
        (aeval_sound hcat hA hF hT hwf.2.1 y hy) (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])) ht
  | .join a b .left on, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxm := aeval_sound hcat hA hF hT hwf.1 x hx
      have hl : (a.aeval cat A F T).length = x.length := by
        rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hxm.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        exact hxm.append (aeval_sound hcat hA hF hT hwf.2.1 y hy).nullable hl
  | .fetch r _ _, hwf, row, h => by
      simp only [eval] at h
      have := aeval_sound hcat hA hF hT (r := r) hwf
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .semi a _ _ _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact aeval_sound hcat hA hF hT hwf.1 row h.1
  | .orderBy r _, hwf, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf.1 row h
  | .distinct r, hwf, row, h => by
      simp only [eval, mem_dedup] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf row h
  | .unnest r c, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨_, v, _, _, rfl⟩ := mem_unnestRow h
      exact (aeval_sound hcat hA hF hT hwf.1 x hx).set_top c v
  | .aggregate r gs ms, hwf, row, h => by
      obtain ⟨k, grp, rfl, hgrp, hk⟩ := mem_aggregateEval h
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound hcat hA hF hT hwf.1 y (hgrp y hy),
          Rel.facts_sound hcat hF hT hwf.1 y (hgrp y hy)⟩
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) (EnvMem.measures hall ms) (by simp)
      · exact (EnvMem.mapD (aeval_sound hcat hA hF hT hwf.1 x hx)
          (Rel.facts_sound hcat hF hT hwf.1 x hx) gs).append (EnvMem.measures hall ms)
          (by simp)
  | .unionAll a b, hwf, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact (aeval_sound hcat hA hF hT hwf.1 row h).zip_left
      · exact (aeval_sound hcat hA hF hT hwf.2.1 row h).zip_right
  | .window r _ _ fns, hwf, row, h => by
      obtain ⟨b, x, a, he, hx, rfl⟩ := mem_windowEval h
      obtain ⟨_, _, hin⟩ := sorted_split he
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T) y :=
        fun y hy => aeval_sound hcat hA hF hT hwf.1 y (hin y hy)
      exact (hall x (.inl rfl)).append (EnvMem.window hall fns)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])

/-! ## Contracts -/

/-- Substitute expressions for field references. -/
def Expr.subst (cols : List Expr) : Expr → Expr
  | .lit v => .lit v
  | .field i => cols.getD i (.lit .null)
  | .un f a => .un f (a.subst cols)
  | .bin f a b => .bin f (a.subst cols) (b.subst cols)
  | .ifThen c t e => .ifThen (c.subst cols) (t.subst cols) (e.subst cols)

theorem getD_map_eval (cols : List Expr) (row : Row) (i : Nat) :
    (cols.map (·.eval row)).getD i .null = (cols.getD i (.lit .null)).eval row := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cols[i]? <;> rfl

theorem Expr.eval_subst (cols : List Expr) (row : Row) :
    ∀ e : Expr, (e.subst cols).eval row = e.eval (cols.map (·.eval row))
  | .lit _ => rfl
  | .field i => (getD_map_eval cols row i).symm
  | .un f a => by simp [subst, eval, Expr.eval_subst cols row a]
  | .bin f a b => by simp [subst, eval, Expr.eval_subst cols row a, Expr.eval_subst cols row b]
  | .ifThen c t e => by
      simp [subst, eval, Expr.eval_subst cols row c, Expr.eval_subst cols row t,
        Expr.eval_subst cols row e]

/-- A plan that only computes columns of one table (`Read` under projects and
emits) as expressions over that table's columns. Preconditions are given as
such plans: `orders.select(amount >= 0, ...)`. -/
def Rel.colExprs (cat : Catalog) : Rel → Option (String × List Expr)
  | .read t => some (t, (List.range (cat t).arity).map .field)
  | .project r es => (r.colExprs cat).map fun (t, cs) => (t, cs ++ es.map (·.subst cs))
  | .emit r m => (r.colExprs cat).map fun (t, cs) => (t, m.map (cs.getD · (.lit .null)))
  | _ => none

/-- Such a plan computes its expressions row by row: so "every output column
of the precondition plan is TRUE" means each expression is TRUE on each row. -/
theorem Rel.colExprs_eval {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel} {t : String} {cs : List Expr}, r.colExprs cat = some (t, cs) →
      r.eval cat = (cat t).rows.map fun row => cs.map (·.eval row)
  | .read t', t, cs, h => by
      simp only [colExprs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      conv => lhs; rw [← List.map_id (eval cat (read t'))]
      simp only [eval]
      apply List.map_congr_left
      intro row hrow
      simp only [List.map_map, Function.comp_def, Expr.eval, id]
      apply List.ext_getElem (by simp [hcat t' row hrow])
      intro i h₁ _
      simp [List.getD, List.getElem?_eq_getElem h₁]
  | .project r es, t, cs, h => by
      simp only [colExprs, Option.map_eq_some_iff] at h
      obtain ⟨⟨t', cs'⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [eval, colExprs_eval hcat hr, List.map_map]
      apply List.map_congr_left
      intro row _
      simp [List.map_append, Function.comp_def, Expr.eval_subst]
  | .emit r m, t, cs, h => by
      simp only [colExprs, Option.map_eq_some_iff] at h
      obtain ⟨⟨t', cs'⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [eval, colExprs_eval hcat hr, List.map_map]
      apply List.map_congr_left
      intro row _
      simp only [Function.comp_def]
      apply List.map_congr_left
      intro a _
      exact getD_map_eval cs' row a
  | .values _ _, _, _, h | .filter _ _, _, _, h | .cross _ _, _, _, h | .join _ _ _ _, _, _, h
  | .fetch _ _ _, _, _, h | .unionAll _ _, _, _, h | .window _ _ _ _, _, _, h
  | .semi _ _ _ _, _, _, h | .orderBy _ _, _, _, h | .distinct _, _, _, h
  | .unnest _ _, _, _, h => by
      simp [colExprs] at h

/-- What is known about a table: its schema, refined by its preconditions. -/
def tableEnv (schema : List AVal) (pre : List Expr) : List AVal := pre.foldl Expr.refine schema

theorem tableEnv_sound {row : Row} :
    ∀ {schema : List AVal} {pre : List Expr}, EnvMem schema row →
      (∀ e ∈ pre, (e.eval row).isTrue = true) → EnvMem (tableEnv schema pre) row
  | _, [], h, _ => h
  | _, e :: pre, h, hpre => by
      simp only [tableEnv, List.foldl_cons]
      exact tableEnv_sound (Expr.refine_sound _ e h (hpre e (by simp)))
        fun e' he' => hpre e' (by simp [he'])

/-- **Contract soundness.** Suppose every row of every table matches its
schema and satisfies its preconditions, and the postcondition plan `Q` (the
transformation followed by a select of the postconditions) is well-formed. If
the abstract evaluation shows every column of `Q` is certainly TRUE, then
every postcondition holds on every output row. -/
theorem contract_sound {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.Sound cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true := by
  intro row hrow v hv
  have hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold ((pre t).flatMap Expr.factsOf) row := by
    intro t row h f hf
    simp only [List.mem_flatMap] at hf
    obtain ⟨e, he, hf⟩ := hf
    exact Expr.factsOf_sound e (hpre t row h e he) f hf
  have hm := Q.aeval_sound hcat (fun t row h => tableEnv_sound (hS t row h) (hpre t row h)) hF hT
    hQ row hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : j < (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).length := by
    rw [Rel.aeval_length hQ, ← Rel.eval_arity hcat hQ row hrow]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen)
  have := hm j
  simp only [List.getElem?_eq_getElem hlen, Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

end Substrait
