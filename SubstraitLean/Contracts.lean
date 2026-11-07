import SubstraitLean.OrderAllowed

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

/-- Is every integer of `b` at least `l`? -/
def Bound.allGe (b : Bound) (l : Int) : Bool := b.lo.any (l ≤ ·)

/-- Is every integer of `b` at most `h`? -/
def Bound.allLe (b : Bound) (h : Int) : Bool := b.hi.any (· ≤ h)

/-- Is every integer of `b` in `[lo, hi]` (`between`)? The one range check of
the casts, the integer and decimal widths and the time ranges. -/
def Bound.within (lo hi : Int) (b : Bound) : Bool := b.allGe lo && b.allLe hi

theorem Bound.allGe_le {b : Bound} {l i : Int} (h : b.allGe l = true) (hi : b.Mem i) : l ≤ i := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.allGe, Option.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨l', rfl, hl⟩ := h
  have := hi.1 l' rfl; omega

theorem Bound.le_allLe {b : Bound} {h i : Int} (hb : b.allLe h = true) (hi : b.Mem i) : i ≤ h := by
  obtain ⟨bl, bh⟩ := b
  simp only [Bound.allLe, Option.any_eq_true, decide_eq_true_eq] at hb
  obtain ⟨h', rfl, hh⟩ := hb
  have := hi.2 h' rfl; omega

theorem Bound.within_mem {lo hi i : Int} {b : Bound} (h : b.within lo hi = true) (hm : b.Mem i) :
    between lo hi i = true := by
  simp only [Bound.within, Bool.and_eq_true] at h
  simp only [between, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Bound.allGe_le h.1 hm, Bound.le_allLe h.2 hm⟩

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

/-- The larger of two optional lower bounds: either one bounds `max x y`. -/
def maxLo : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | some a, none | none, some a => some a
  | none, none => none

/-- `max x y` for `x ∈ a`, `y ∈ b` (`GREATEST`): from the larger lower bound to
the larger upper bound. -/
def Bound.greatest (a b : Bound) : Bound := ⟨maxLo a.lo b.lo, lift2 Max.max a.hi b.hi⟩

/-- `min x y` (`LEAST`): from the smaller lower bound to the smaller upper. -/
def Bound.least (a b : Bound) : Bound :=
  ⟨lift2 Min.min a.lo b.lo, (maxLo (a.hi.map (- ·)) (b.hi.map (- ·))).map (- ·)⟩

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

theorem Bound.mem_greatest {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.greatest b).Mem (if x < y then y else x) := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.greatest] at *
  obtain ⟨hal, hah⟩ := ha; obtain ⟨hbl, hbh⟩ := hb
  constructor
  · intro l hl
    cases al <;> cases bl <;> simp only [maxLo, Option.some.injEq, reduceCtorEq] at hl <;>
      first | (subst hl; have := hal _ rfl; have := hbl _ rfl; split <;> omega)
            | (subst hl; have := hal _ rfl; split <;> omega)
            | (subst hl; have := hbl _ rfl; split <;> omega)
  · intro u hu
    cases ah <;> cases bh <;> simp only [lift2, Option.some.injEq, reduceCtorEq] at hu
    subst hu; have := hah _ rfl; have := hbh _ rfl; split <;> omega

theorem Bound.mem_least {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.least b).Mem (if y < x then y else x) := by
  obtain ⟨⟨al, ah⟩, bl, bh⟩ := a, b
  simp only [Bound.Mem, Bound.least] at *
  obtain ⟨hal, hah⟩ := ha; obtain ⟨hbl, hbh⟩ := hb
  constructor
  · intro l hl
    cases al <;> cases bl <;> simp only [lift2, Option.some.injEq, reduceCtorEq] at hl
    subst hl; have := hal _ rfl; have := hbl _ rfl; split <;> omega
  · intro u hu
    cases ah <;> cases bh <;>
      simp only [Option.map, maxLo, Option.some.injEq, reduceCtorEq] at hu <;>
      first | (subst hu; have := hah _ rfl; have := hbh _ rfl; split <;> omega)
            | (subst hu; have := hah _ rfl; split <;> omega)
            | (subst hu; have := hbh _ rfl; split <;> omega)

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
  /-- if `some l`, every string is in `l` (#708): the values of a status or a
  tag. At most `strCap` of them; past that, `none`. -/
  strs : Option (List String)
  deriving Repr, BEq

/-- The most strings an abstract value lists (#708); more, and any string may be. -/
def strCap : Nat := 64

def AVal.Mem (a : AVal) : Value → Prop
  | .null => a.null = true
  | .int i => ∃ b, a.int = some b ∧ b.Mem i
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .str s => (a.str && a.strs.all (·.contains s)) = true
  -- The abstraction does not look into lists: a list is a member where the
  -- booleans and strings are. Functions of one type give NULL on the others,
  -- so each abstraction covers a list as it covers a value of another type.
  | .list _ => a.tt = true ∧ a.ff = true ∧ a.str = true

/-- Every integer `a` describes is in `[lo, hi]`. -/
def AVal.within (lo hi : Int) (a : AVal) : Bool := a.int.all (·.within lo hi)

theorem AVal.within_mem {lo hi i : Int} {a : AVal} (h : a.within lo hi = true)
    (hm : a.Mem (.int i)) : between lo hi i = true := by
  obtain ⟨b, hb, hi⟩ := hm
  simp only [AVal.within, hb, Option.all_some] at h
  exact Bound.within_mem h hi

def AVal.top : AVal := ⟨true, some Bound.top, true, true, true, none⟩
def AVal.bot : AVal := ⟨false, none, false, false, false, none⟩

def AVal.ofValue : Value → AVal
  | .null => ⟨true, none, false, false, false, none⟩
  | .int i => ⟨false, some (.exact i), false, false, false, none⟩
  | .bool true => ⟨false, none, true, false, false, none⟩
  | .bool false => ⟨false, none, false, true, false, none⟩
  | .str s => ⟨false, none, false, false, true, some [s]⟩
  | .list _ => ⟨false, none, true, true, true, none⟩

def joinInt : Option Bound → Option Bound → Option Bound
  | some x, some y => some (x.join y)
  | some x, none => some x
  | none, y => y

/-- The strings of either side, within `strCap`. A side that holds no string
adds none. -/
def joinStrs (a b : AVal) : Option (List String) :=
  if !a.str then b.strs else if !b.str then a.strs else
  match a.strs, b.strs with
  | some l, some m =>
      let u := l ++ m.filter (!l.contains ·)
      if u.length ≤ strCap then some u else none
  | _, _ => none

def AVal.join (a b : AVal) : AVal :=
  ⟨a.null || b.null, joinInt a.int b.int, a.tt || b.tt, a.ff || b.ff, a.str || b.str, joinStrs a b⟩

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
  | .null | .bool true | .bool false => rfl
  | .str s => by simp [AVal.Mem, AVal.ofValue]
  | .list _ => by simp [AVal.Mem, AVal.ofValue]
  | .int i => ⟨_, rfl, Bound.mem_exact i⟩

theorem joinStrs_left {a b : AVal} {s : String} (ha : a.str = true)
    (hs : a.strs.all (·.contains s) = true) : (joinStrs a b).all (·.contains s) = true := by
  unfold joinStrs
  cases hA : a.strs <;> cases hB : b.strs <;> cases hb : b.str <;> simp_all
  all_goals (split <;> simp_all)

theorem joinStrs_right {a b : AVal} {s : String} (hb : b.str = true)
    (hs : b.strs.all (·.contains s) = true) : (joinStrs a b).all (·.contains s) = true := by
  unfold joinStrs
  cases hA : a.strs <;> cases hB : b.strs <;> cases ha : a.str <;> simp_all
  all_goals (split <;> simp_all)

theorem AVal.mem_join_left {a b : AVal} : ∀ {v}, a.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.join, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨.inl h.1, joinStrs_left h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
      simp_all [AVal.Mem, AVal.join]
  | .list _, h => by
      simp only [AVal.Mem, AVal.join] at *
      exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩
  | .int i, ⟨x, hx, hm⟩ => by
      simp only [AVal.Mem, AVal.join, hx]
      cases b.int <;> simp [joinInt, hm, Bound.mem_join_left hm]

theorem AVal.mem_join_right {a b : AVal} : ∀ {v}, b.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.join, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨.inr h.1, joinStrs_right h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
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
  ⟨a.nonInt, a.int.map (·.mapMono g), false, false, false, none⟩

/-- A conversion to finite doubles, monotone (`FloatCode.FiniteMonoConv`):
between the conversions of the ends, or of `-∞` and `+∞`'s neighbours. -/
def convAbs (c : FloatCode.FiniteMonoConv) (a : AVal) : AVal :=
  ⟨a.nonInt, a.int.map fun b => ⟨some (b.lo.elim (FloatCode.negInf + 1) c.conv),
    some (b.hi.elim (FloatCode.posInf - 1) c.conv)⟩, false, false, false, none⟩

/-- `CAST(x AS BIGINT)`: between the casts of the ends, if both are finite;
otherwise it may also fail (NULL here). -/
def ftoiAbs (a : AVal) : AVal :=
  match a.int with
  | some ⟨some lo, some hi⟩ =>
    match FloatCode.toInt? lo, FloatCode.toInt? hi with
    | some x, some y => ⟨a.nonInt, some ⟨some x, some y⟩, false, false, false, none⟩
    | _, _ => ⟨true, some Bound.top, false, false, false, none⟩
  | some _ => ⟨true, some Bound.top, false, false, false, none⟩
  | none => ⟨a.nonInt, none, false, false, false, none⟩

/-- `a`, or NULL. -/
def AVal.nullable (a : AVal) : AVal := { a with null := true }

theorem AVal.mem_nullable {a : AVal} : ∀ {v}, a.Mem v → a.nullable.Mem v
  | .null, _ => rfl
  | .int _, h | .bool true, h | .bool false, h | .str _, h | .list _, h => h

/-- `CAST(x AS INT)`: the integer itself, or NULL where it may not fit. -/
def narrowAbs (n : Nat) (a : AVal) : AVal :=
  ⟨a.nonInt || !a.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1), a.int, false, false, false, none⟩

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

/-- `roundDivInt?` for a non-zero divisor: a decimal `AVG`'s quotient (#27). -/
def roundDiv (a b : Int) : Int := (roundDivInt? a b).getD 0

theorem nat_roundDiv_le (A B : Nat) (hB : 0 < B) : (2 * A + B) / (2 * B) ≤ A := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have h1 : A ≤ A * B := Nat.le_mul_of_pos_right A hB
  have h2 : (A + 1) * (2 * B) = 2 * (A * B) + 2 * B := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  rw [Nat.succ_eq_add_one, h2]; omega

/-- The rounded quotient is no larger than the dividend in absolute value. -/
theorem roundDiv_natAbs_le {a b : Int} (hb : b ≠ 0) : (roundDiv a b).natAbs ≤ a.natAbs := by
  have hq := nat_roundDiv_le a.natAbs b.natAbs (Int.natAbs_pos.mpr hb)
  unfold roundDiv roundDivInt?
  simp only [hb, ↓reduceIte]
  generalize (2 * a.natAbs + b.natAbs) / (2 * b.natAbs) = q at hq ⊢
  dsimp only [Option.getD_some]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> exact hq

/-- For a positive divisor, the rounded quotient lies between 0 and the
dividend, as `tdiv_between` says of truncation. -/
theorem roundDiv_between {a b : Int} (hb : 0 < b) :
    min a 0 ≤ roundDiv a b ∧ roundDiv a b ≤ max a 0 := by
  have hq := nat_roundDiv_le a.natAbs b.natAbs (Int.natAbs_pos.mpr (by omega))
  have hb0 : b ≠ 0 := by omega
  unfold roundDiv roundDivInt?
  simp only [hb0, ↓reduceIte]
  generalize (2 * a.natAbs + b.natAbs) / (2 * b.natAbs) = q at hq ⊢
  dsimp only [Option.getD_some]
  have hbn : ¬b < 0 := by omega
  have hq' : (q : Int) ≤ a.natAbs := Int.ofNat_le.mpr hq
  split
  · rename_i hs
    have ha : 0 ≤ a := by
      rcases Int.lt_or_le a 0 with h | h
      · exact absurd (hs ▸ h) hbn
      · exact h
    have h1 : (a.natAbs : Int) = a := Int.natAbs_of_nonneg ha
    omega
  · rename_i hs
    have ha : a < 0 := by
      rcases Int.lt_or_le a 0 with h | h
      · exact h
      · exact absurd (propext ⟨fun h' => absurd h' (by omega), fun h' => absurd h' hbn⟩) hs
    have h1 : (a.natAbs : Int) = -a := Int.ofNat_natAbs_of_nonpos (by omega)
    omega

theorem nat_roundDiv_le_of {A N M : Nat} (hN : 0 < N) (h : A ≤ N * M) :
    (2 * A + N) / (2 * N) ≤ M := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have e1 : M * (2 * N) = 2 * (N * M) := by rw [Nat.mul_left_comm, Nat.mul_comm M N]
  have e2 : (M + 1) * (2 * N) = M * (2 * N) + 2 * N := Nat.succ_mul M (2 * N)
  show 2 * A + N < (M + 1) * (2 * N)
  omega

theorem nat_le_roundDiv_of {A N M : Nat} (hN : 0 < N) (h : N * M ≤ A) :
    M ≤ (2 * A + N) / (2 * N) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have e : M * (2 * N) = 2 * (N * M) := by rw [Nat.mul_left_comm, Nat.mul_comm M N]
  omega

/-- A rounded quotient by a positive divisor stays within integer bounds of
the exact one (a decimal `AVG` within its values, #237). -/
theorem roundDiv_bounds {a n : Int} (hn : 0 < n) :
    (∀ L, n * L ≤ a → L ≤ roundDiv a n) ∧ (∀ H, a ≤ n * H → roundDiv a n ≤ H) := by
  have hn0 : n ≠ 0 := by omega
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr hn0
  have hnN : (n.natAbs : Int) = n := Int.natAbs_of_nonneg (by omega)
  unfold roundDiv roundDivInt?
  simp only [hn0, ↓reduceIte, Option.getD_some]
  have hbn : ¬n < 0 := by omega
  by_cases ha : a < 0
  · have hs : ¬((a < 0) = (n < 0)) := by simp [ha, hbn]
    simp only [hs, ↓reduceIte]
    have haN : (a.natAbs : Int) = -a := Int.ofNat_natAbs_of_nonpos (by omega)
    constructor
    · intro L hL
      -- `|a| ≤ n · (-L)`
      have hL' : 0 ≤ -L := by
        rcases Int.lt_or_le L 0 with h | h
        · omega
        · have : 0 ≤ n * L := Int.mul_nonneg (by omega) h; omega
      have hm : a.natAbs ≤ n.natAbs * (-L).toNat := by
        have : (a.natAbs : Int) ≤ (n.natAbs : Int) * ((-L).toNat : Int) := by
          rw [Int.toNat_of_nonneg hL', hnN, haN, Int.mul_neg]; omega
        exact_mod_cast this
      have := nat_roundDiv_le_of hN hm
      have : (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) ≤ (-L).toNat :=
        by exact_mod_cast this
      rw [Int.toNat_of_nonneg hL'] at this; omega
    · intro H hH
      have hq : (0 : Int) ≤ (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) :=
        Int.natCast_nonneg _
      rcases Int.lt_or_le H 0 with hH0 | hH0
      · have hm : n.natAbs * (-H).toNat ≤ a.natAbs := by
          have : (n.natAbs : Int) * ((-H).toNat : Int) ≤ (a.natAbs : Int) := by
            rw [Int.toNat_of_nonneg (by omega), hnN, haN, Int.mul_neg]; omega
          exact_mod_cast this
        have := nat_le_roundDiv_of hN hm
        have : ((-H).toNat : Int) ≤ (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) :=
          by exact_mod_cast this
        rw [Int.toNat_of_nonneg (by omega)] at this; omega
      · omega
  · have hs : (a < 0) = (n < 0) := by simp [ha, hbn]
    simp only [hs, ↓reduceIte]
    have haN : (a.natAbs : Int) = a := Int.natAbs_of_nonneg (by omega)
    constructor
    · intro L hL
      rcases Int.lt_or_le L 0 with hL0 | hL0
      · have : (0 : Int) ≤ (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) :=
          Int.natCast_nonneg _
        omega
      · have hm : n.natAbs * L.toNat ≤ a.natAbs := by
          have : (n.natAbs : Int) * (L.toNat : Int) ≤ (a.natAbs : Int) := by
            rw [Int.toNat_of_nonneg hL0, hnN, haN]; exact hL
          exact_mod_cast this
        have := nat_le_roundDiv_of hN hm
        have : (L.toNat : Int) ≤ (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) :=
          by exact_mod_cast this
        rw [Int.toNat_of_nonneg hL0] at this; exact this
    · intro H hH
      have hH0 : 0 ≤ H := by
        rcases Int.lt_or_le H 0 with h | h
        · have : n * H < 0 := Int.mul_neg_of_pos_of_neg hn h; omega
        · exact h
      have hm : a.natAbs ≤ n.natAbs * H.toNat := by
        have : (a.natAbs : Int) ≤ (n.natAbs : Int) * (H.toNat : Int) := by
          rw [Int.toNat_of_nonneg hH0, hnN, haN]; exact hH
        exact_mod_cast this
      have := nat_roundDiv_le_of hN hm
      have : (((2 * a.natAbs + n.natAbs) / (2 * n.natAbs) : Nat) : Int) ≤ (H.toNat : Int) :=
        by exact_mod_cast this
      rw [Int.toNat_of_nonneg hH0] at this; exact this

/-- Decimal division (`AVG`): between 0 and the dividend for a divisor that is
not negative (a zero divisor gives NULL), no larger than it in absolute value
otherwise. -/
def ddivBound (x y : Bound) : Bound :=
  if y.lo.any (0 ≤ ·) then x.signHull else x.absHull

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
   (match a.int, b.int with | some x, some y => some (bound x y) | _, _ => none), false, false, false, none⟩

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
    | _, _ => none), false, false, false, none⟩

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

/-- `date_part` is NULL outside the timestamps `chrono` represents. -/
def datePartAbs (p : Time.DatePart) (a : AVal) : AVal :=
  ⟨a.nonInt || !a.within Time.partMin Time.partMax, a.int.map (partBound p), false, false, false, none⟩

/-! ## Domains

The elementary functions, `atan2`, `logb` and the shifts are `NULL` (an
error, `Issue.domain`) outside their domains (`SubstraitLean/Numeric.lean`).
Their results are "some double" or "some integer", or `NULL` where an
argument may be outside the domain. -/

/-- Is every double `a` describes in `f`'s domain? -/
def FMath.safe (f : FMath) (a : AVal) : Bool :=
  a.int.all fun b => f.lo?.all b.allGe && f.hi?.all b.allLe

/-- Is every pair of arguments `a`, `b` describe in the function's domain? -/
def BinFn.domainSafe : BinFn → AVal → AVal → Bool
  | .fatan2, a, b => a.int.all (!·.has0) || b.int.all (!·.has0)
  | .flogb, a, b => a.int.all (·.allGe 1) && b.int.all fun y =>
      y.allGe 1 && (y.allGe (FloatCode.one + 1) || y.allLe (FloatCode.one - 1))
  | .bit op, _, b => !op.isShift || b.int.all fun y => y.allGe 0 && y.allLe 63
  | _, _, _ => true

/-- Some integer, or `NULL` unless the argument is `safe`. -/
def partialAbs (safe : Bool) (a : AVal) : AVal :=
  ⟨a.nonInt || !safe, a.int.map fun _ => Bound.top, false, false, false, none⟩

/-- `CAST(x AS DECIMAL(_, s))`: between the casts of the double's bounds,
where both have a decimal (`FloatCode.toDecimal?_between`, #223); else some
integer, or `NULL`. -/
def ftodAbs (s : Nat) (a : AVal) : AVal :=
  match a.int with
  | some ⟨some l, some h⟩ =>
    match FloatCode.toDecimal? l s, FloatCode.toDecimal? h s with
    | some x, some y => ⟨a.nonInt, some ⟨some x, some y⟩, false, false, false, none⟩
    | _, _ => partialAbs false a
  | _ => partialAbs false a

/-- Some integer, or `NULL` unless the arguments are `safe`. -/
def partialAbs₂ (safe : Bool) (a b : AVal) : AVal :=
  ⟨a.nonInt || b.nonInt || !safe,
   (match a.int, b.int with | some _, some _ => some Bound.top | _, _ => none), false, false, false, none⟩

/-! ## Black boxes (#325)

What a black box's row declares of its result (`SubstraitLean/BlackBox.lean`):
its type, and its laws, which hold of the model by construction
(`BlackBox.Scalar.call_ok`). -/

def BlackBox.Law.bound : BlackBox.Law → Bound
  | .atLeast k => ⟨some k, none⟩
  | .atMost k => ⟨none, some k⟩
  | .nonNull => Bound.top

/-- The results of type `result` that keep `laws`, where no argument is NULL
(`set`) or some may be. -/
def BlackBox.lawsAbs (result : BlackBox.Ty) (laws : List BlackBox.Law) (set : Bool) : AVal :=
  ⟨!(set && laws.contains .nonNull),
   if result == .int || result == .double || result == .date || result == .timestamp ||
       result == .atom || result == .any then
     some (laws.foldr (fun l b => l.bound.meet b) Bound.top)
   else none,
   -- A list is a member where booleans and strings are (`AVal.Mem`).
   result == .bool || result == .atom || result == .doubles || result == .ints ||
     result == .strs || result == .any,
   result == .bool || result == .atom || result == .doubles || result == .ints ||
     result == .strs || result == .any,
   result == .str || result == .atom || result == .doubles || result == .ints ||
     result == .strs || result == .any, none⟩

theorem BlackBox.lawsBound_mem {set : Bool} {i : Int} :
    ∀ {laws : List BlackBox.Law}, (laws.all fun l => l.holds set (.int i)) = true →
      (laws.foldr (fun l b => l.bound.meet b) Bound.top).Mem i
  | [], _ => Bound.mem_top i
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    refine Bound.mem_meet ?_ (lawsBound_mem h.2)
    cases l <;> simp_all [BlackBox.Law.holds, BlackBox.Law.bound, Bound.Mem, Bound.top]

theorem BlackBox.lawsAbs_mem {result : BlackBox.Ty} {laws : List BlackBox.Law} {set : Bool}
    {v : Value} (h : BlackBox.ok result laws set v = true) :
    (BlackBox.lawsAbs result laws set).Mem v := by
  simp only [BlackBox.ok, Bool.and_eq_true] at h
  obtain ⟨ht, hl⟩ := h
  match v with
  | .null =>
    simp only [AVal.Mem, BlackBox.lawsAbs, Bool.not_eq_true', Bool.and_eq_false_iff]
    cases set
    · simp
    · right
      simp only [List.all_eq_true] at hl
      cases hc : laws.contains .nonNull
      · rfl
      · have := hl .nonNull (by simpa using hc)
        simp [BlackBox.Law.holds] at this
  | .int i =>
    refine ⟨_, ?_, lawsBound_mem hl⟩
    cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has]
  | .bool true | .bool false | .str _ =>
    cases result <;> simp_all [AVal.Mem, BlackBox.lawsAbs, BlackBox.Ty.has]
  | .list _ =>
    cases result <;> simp_all [AVal.Mem, BlackBox.lawsAbs, BlackBox.Ty.has]

/-- A scalar black box's result, where no argument is NULL (`set`) or some may be. -/
def BlackBox.scalarAbs (name : String) (set : Bool) : AVal :=
  match BlackBox.scalar? name with
  | some f => BlackBox.lawsAbs f.result f.laws set
  | none => ⟨true, none, false, false, false, none⟩

theorem BlackBox.scalarAbs_mem {name : String} {vs : List Value} {set : Bool}
    (hs : set = true → vs.contains .null = false) :
    (BlackBox.scalarAbs name set).Mem (BlackBox.callScalar name vs) := by
  unfold BlackBox.scalarAbs BlackBox.callScalar
  cases h : BlackBox.scalar? name with
  | none => rfl
  | some f =>
    apply BlackBox.lawsAbs_mem
    have hok := BlackBox.Scalar.call_ok (BlackBox.scalar?_mem h) vs
    cases set
    · cases hc : vs.contains .null
      · rw [hc] at hok; exact BlackBox.ok_of_set hok false
      · rw [hc] at hok; exact hok
    · rw [hs rfl] at hok; exact hok

/-- An aggregate black box's result: over values (`valued`), or maybe over none. -/
def BlackBox.aggAbs (name : String) (valued : Bool) : AVal :=
  match BlackBox.aggregate? name with
  | some f => (BlackBox.lawsAbs f.result f.laws true).join
      (if valued then AVal.bot else AVal.ofValue f.empty)
  | none => ⟨true, none, false, false, false, none⟩

theorem BlackBox.aggAbs_mem {name : String} {vs : List Value} {valued : Bool}
    (hv : valued = true → vs ≠ []) :
    (BlackBox.aggAbs name valued).Mem (BlackBox.callAgg name vs) := by
  unfold BlackBox.aggAbs BlackBox.callAgg
  cases h : BlackBox.aggregate? name with
  | none => rfl
  | some f =>
    cases vs with
    | nil =>
      apply AVal.mem_join_right
      cases valued
      · exact AVal.mem_ofValue _
      · exact absurd rfl (hv rfl)
    | cons v vs =>
      exact AVal.mem_join_left (BlackBox.lawsAbs_mem
        (BlackBox.Aggregate.call_ok (BlackBox.aggregate?_mem h) (List.cons_ne_nil _ _)))

def UnFn.abs : UnFn → AVal → AVal
  | .not, a => ⟨a.nonBool, none, a.ff, a.tt, false, none⟩
  | .isNull, a => ⟨false, none, a.null, a.int.isSome || a.tt || a.ff || a.str, false, none⟩
  -- Double negation is code negation too (zero is `0`).
  | .neg, a | .fneg, a => ⟨a.nonInt, a.int.map Bound.neg, false, false, false, none⟩
  -- Float results: some double (any code), or NULL.
  | .itof, a => convAbs FloatCode.intConv a
  | .froundTo _, a => ⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false, none⟩
  | .ffloor, a => monoAbs FloatCode.floor a
  | .fceil, a => monoAbs FloatCode.ceil a
  | .fround, a => monoAbs FloatCode.round a
  | .ftoi, a => ftoiAbs a
  | .narrow n, a => narrowAbs n a
  -- `ftoi`'s value, or NULL where the cast fails (#58).
  | .ftoiOrNull, a => (ftoiAbs a).nullable
  | .narrowOrNull n, a => narrowAbs n a
  | .wrap _, a => a
  | .decimal _ _, a | .dkind _ _, a => a
  | .dround _, a | .dtrunc _, a =>
      ⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false, none⟩
  | .dtof s, a => convAbs (FloatCode.decConv s) a
  | .ftod s, a => ftodAbs s a
  | .itos, a => ⟨a.nonInt, none, false, false, a.int.isSome, none⟩
  | .widen, a => a
  | .upper, a | .lower, a | .reverse, a | .replace _ _, a | .regexExtract _ _, a
  | .regexReplace _ _ _, a | .md5, a | .sha256, a => ⟨a.nonStr, none, false, false, a.str, none⟩
  -- Below `Text.sizeCap`, by the size hypothesis for strings.
  | .length, a | .ascii, a =>
    ⟨a.nonStr, if a.str then some ⟨some 0, some Text.sizeCap⟩ else none, false, false, false, none⟩
  -- `NULL` when the pattern does not match.
  | .regexMatch _, a => ⟨true, if a.str then some (.ge 1) else none, false, false, false, none⟩
  | .datePart p, a => datePartAbs p a
  | .dateTrunc u, a => monoAbs (Time.trunc u) a
  | .toDate, a => monoAbs Time.days a
  | .dayPart p, a => datePartAbs p (monoAbs (· * Time.usPerDay) a)
  | .dayTrunc u, a => monoAbs (Time.truncDay u) a
  | .addMonths m false, a => monoAbs (Time.addMonths m) a
  | .addMonths _ true, a => ⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false, none⟩
  | .timeOfDay, a =>
      ⟨a.nonInt, a.int.map fun _ => ⟨some 0, some (Time.usPerDay - 1)⟩, false, false, false, none⟩
  | .asTime, a => monoAbs id a
  | .dateTime, a => monoAbs (· * Time.usPerDay) a
  | .epochUs, a => monoAbs id a
  | .strftime _, a => ⟨a.nonInt, none, false, false, a.int.isSome, none⟩
  | .bucket k o, a => monoAbs (Time.bucket k o) a
  | .fmath f, a => partialAbs (f.safe a) a
  -- The abstraction does not look into lists: an element or a field is
  -- anything.
  | .structField _, _ | .listElement _, _ | .flatten, _ => AVal.top
  | .cardinality, _ => ⟨true, some (.ge 0), false, false, false, none⟩
  | .raise _, _ => ⟨true, none, false, false, false, none⟩
  | .isNum, _ => ⟨false, none, true, true, false, none⟩
  | .fit _ _, _ => AVal.top
  | .bbox n, a => BlackBox.scalarAbs n !a.null

def arith (op : Bound → Bound → Bound) (a b : AVal) : AVal :=
  ⟨a.nonInt || b.nonInt,
   (match a.int, b.int with | some x, some y => some (op x y) | _, _ => none),
   false, false, false, none⟩

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

/-- `GREATEST`/`LEAST` (`Value.pick`) of values in `a` and `b`: `NULL` only if
both are; an integer in `both` of two integers, else one side's integer where
the other is `NULL` or not an integer (the comparison is then FALSE and the
first value stays, or the `NULL` is skipped); a boolean or string from either. -/
def pickAbs (both : Bound → Bound → Bound) (a b : AVal) : AVal :=
  let pair : Option Bound := match a.int, b.int with
    | some x, some y => some (both x y)
    | _, _ => none
  let ints := joinInt (if b.nonInt then a.int else none) (joinInt (if a.null then b.int else none) pair)
  ⟨a.null && b.null, ints, a.tt || b.tt, a.ff || b.ff, a.str || b.str, none⟩

/-! ### Double arithmetic (#582)

A double `+`, `-`, `*`, `/` of finite doubles is bounded from its inputs'
bounds, by the trusted facts `FloatCode.add_scaled` … `div_scaled`: on
scaled values, the exact result's interval widened by its rounding, then
back to codes. Where the inputs may be infinite or NaN, or the result may
come near the largest double, the bound is `top`. -/

/-- The scaled ends of a bound of finite doubles' codes. -/
def finEnds (x : Bound) : Option (Int × Int) :=
  match x.lo, x.hi with
  | some l, some h =>
    if FloatCode.negInf < l ∧ h < FloatCode.posInf then some (FloatCode.scaled l, FloatCode.scaled h)
    else none
  | _, _ => none

/-- The codes whose scaled value is in `[l, h]`. -/
def codeBound (l h : Int) : Bound := ⟨some (FloatCode.codeLo l), some (FloatCode.codeHi h)⟩

/-- The largest magnitude in `[l, h]`. -/
def endsMag (l h : Int) : Nat := max l.natAbs h.natAbs

set_option exponentiation.threshold 3200 in
/-- `x + y` (`sub`: `x - y`) of doubles. -/
def faddBound (sub : Bool) (x y : Bound) : Bound :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) =>
    let S := endsMag la ha + endsMag lb hb
    if S ≤ 2 ^ 2097 then
      let e : Int := ((S / 2 ^ 50 + 1 : Nat) : Int)
      if sub then codeBound (la - hb - e) (ha - lb + e) else codeBound (la + lb - e) (ha + hb + e)
    else Bound.top
  | _, _ => Bound.top

set_option exponentiation.threshold 3200 in
/-- `x * y` of doubles. -/
def fmulBound (x y : Bound) : Bound :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) =>
    let P := endsMag la ha * endsMag lb hb
    if P ≤ 2 ^ 3171 then
      let E : Int := ((P / 2 ^ 50 + 2 ^ 1074 : Nat) : Int)
      match (Bound.mul ⟨some la, some ha⟩ ⟨some lb, some hb⟩) with
      | ⟨some l, some h⟩ =>
        codeBound ((l - E) / ((2 ^ 1074 : Nat) : Int)) ((h + E) / ((2 ^ 1074 : Nat) : Int))
      | _ => Bound.top
    else Bound.top
  | _, _ => Bound.top

/-- The least magnitude in `[l, h]`, where `0` is outside. -/
def endsMin (l h : Int) : Nat := if 0 < l then l.natAbs else if h < 0 then h.natAbs else 0

set_option exponentiation.threshold 3200 in
/-- `x / y` of doubles, by magnitude. -/
def fdivBound (x y : Bound) : Bound :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) =>
    let Ma := endsMag la ha
    let mb := endsMin lb hb
    if 0 < mb ∧ Ma * 2 ^ 1074 ≤ 2 ^ 2097 * mb then
      let K : Int := ((Ma * (2 ^ 1074 + 2 ^ 1024) / mb + 1 : Nat) : Int)
      codeBound (-K) K
    else Bound.top
  | _, _ => Bound.top

/-- `a = b` may be TRUE on two strings: both may be strings, and their sets
(#708) share one. -/
def strMayEq (a b : AVal) : Bool :=
  a.str && b.str && (match a.strs, b.strs with | some l, some m => l.any m.contains | _, _ => true)

/-- `a = b` may be FALSE on two strings: unless both are the same one string. -/
def strMayNe (a b : AVal) : Bool :=
  a.str && b.str && (match a.strs, b.strs with | some [x], some [y] => x != y | _, _ => true)

/-! #### Signs (#441)

Rounding keeps a result's sign (`FloatCode.add_nonneg` …), so a sum or
product of non-negative doubles, or a quotient of one by a positive one,
stays at least `0`; the absolute error of `faddBound` … alone would let its
bound dip below. -/

/-- Does every value of the bound sit at or above code `0` (`+0.0`)? -/
def Bound.nonneg (b : Bound) : Bool := b.lo.any (0 ≤ ·)

/-- `b`, raised to start at code `0`. -/
def Bound.atLeast0 (b : Bound) : Bound := ⟨some (b.lo.elim 0 (max 0)), b.hi⟩

theorem Bound.mem_atLeast0 {b : Bound} {r : Int} (h : b.Mem r) (h0 : 0 ≤ r) :
    b.atLeast0.Mem r := by
  obtain ⟨hl, hh⟩ := h
  refine ⟨fun l hl' => ?_, hh⟩
  simp only [Bound.atLeast0, Option.some.injEq] at hl'
  subst hl'
  cases hlo : b.lo with
  | none => simpa using h0
  | some l => have := hl l hlo; simp only [Option.elim]; omega

theorem Bound.nonneg_mem {b : Bound} {r : Int} (h : b.Mem r) (hn : b.nonneg = true) : 0 ≤ r := by
  unfold Bound.nonneg at hn
  cases hlo : b.lo with
  | none => simp [hlo] at hn
  | some l => simp only [hlo, Option.any_some, decide_eq_true_eq] at hn; have := h.1 l hlo; omega

set_option exponentiation.threshold 3200 in
/-- Do `faddBound`'s guards hold? -/
def faddOk (x y : Bound) : Bool :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) => decide (endsMag la ha + endsMag lb hb ≤ 2 ^ 2097)
  | _, _ => false

set_option exponentiation.threshold 3200 in
/-- Do `fmulBound`'s guards hold? -/
def fmulOk (x y : Bound) : Bool :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) => decide (endsMag la ha * endsMag lb hb ≤ 2 ^ 3171)
  | _, _ => false

set_option exponentiation.threshold 3200 in
/-- Do `fdivBound`'s guards hold? -/
def fdivOk (x y : Bound) : Bool :=
  match finEnds x, finEnds y with
  | some (la, ha), some (lb, hb) =>
    decide (0 < endsMin lb hb ∧ endsMag la ha * 2 ^ 1074 ≤ 2 ^ 2097 * endsMin lb hb)
  | _, _ => false

/-- `faddBound`, at least `0` for non-negative inputs. -/
def faddBoundS (sub : Bool) (x y : Bound) : Bound :=
  if !sub && x.nonneg && y.nonneg && faddOk x y then (faddBound sub x y).atLeast0
  else faddBound sub x y

/-- `fmulBound`, at least `0` for non-negative inputs. -/
def fmulBoundS (x y : Bound) : Bound :=
  if x.nonneg && y.nonneg && fmulOk x y then (fmulBound x y).atLeast0 else fmulBound x y

/-- `fdivBound`, at least `0` for a non-negative dividend and a positive divisor. -/
def fdivBoundS (x y : Bound) : Bound :=
  if x.nonneg && y.nonneg && fdivOk x y then (fdivBound x y).atLeast0 else fdivBound x y

def BinFn.abs : BinFn → AVal → AVal → AVal
  | .bbox2 n, a, b => BlackBox.scalarAbs n (!a.null && !b.null)
  | .greatest, a, b => pickAbs Bound.greatest a b
  | .least, a, b => pickAbs Bound.least a b
  | .and, a, b =>
      ⟨(a.nonBool && (b.tt || b.nonBool)) || (a.tt && b.nonBool), none, a.tt && b.tt,
       a.ff || b.ff, false, none⟩
  | .or, a, b =>
      ⟨(a.nonBool && (b.ff || b.nonBool)) || (a.ff && b.nonBool), none, a.tt || b.tt,
       a.ff && b.ff, false, none⟩
  | .add, a, b => arith Bound.add a b
  | .sub, a, b | .dateDiff, a, b => arith Bound.sub a b
  | .mul, a, b => arith Bound.mul a b
  | .dadd, a, b => arith Bound.add a b
  | .dsub, a, b => arith Bound.sub a b
  | .dmul, a, b => arith Bound.mul a b
  | .ddiv, a, b => divAbs ddivBound a b
  | .dateAdd, a, b => arith Bound.add a b
  | .fadd, a, b => arith (faddBoundS false) a b
  | .fsub, a, b => arith (faddBoundS true) a b
  | .fmul, a, b => arith fmulBoundS a b
  | .fdiv, a, b => arith fdivBoundS a b
  | .fmod, a, b | .fpow, a, b => arith (fun _ _ => Bound.top) a b
  | .idiv, a, b => divAbs divBound a b
  | .imod, a, b => divAbs modBound a b
  | .ipow, a, b => powAbs a b
  | .fatan2, a, b => partialAbs₂ (BinFn.domainSafe .fatan2 a b) a b
  | .flogb, a, b => partialAbs₂ (BinFn.domainSafe .flogb a b) a b
  | .bit op, a, b => partialAbs₂ (BinFn.domainSafe (.bit op) a b) a b
  | .concat, a, b | .trim _ _, a, b =>
      ⟨a.nonStr || b.nonStr, none, false, false, a.str && b.str, none⟩
  | .strpos, a, b | .levenshtein, a, b =>
      ⟨a.nonStr || b.nonStr, if a.str && b.str then some ⟨some 0, some Text.sizeCap⟩ else none,
        false, false, false, none⟩
  | .startsWith, a, b | .endsWith, a, b | .like, a, b | .ilike, a, b =>
      ⟨a.nonStr || b.nonStr, none, a.str && b.str, a.str && b.str, false, none⟩
  | .substr _ _, a, b | .strRepeat, a, b =>
      ⟨a.nonStr || b.nonInt, none, false, false, a.str && b.int.isSome, none⟩
  | .eq, a, b =>
      let mismatch := a.null || b.null || (a.int.isSome && (b.tt || b.ff || b.str)) ||
        ((a.tt || a.ff) && (b.int.isSome || b.str)) || (a.str && (b.int.isSome || b.tt || b.ff))
      ⟨mismatch, none,
       intEq a b || (a.tt && b.tt) || (a.ff && b.ff) || strMayEq a b,
       intNe a b || (a.tt && b.ff) || (a.ff && b.tt) || strMayNe a b, false, none⟩
  -- A list, which the abstraction does not look into, or `NULL`.
  | .pair, _, _ => AVal.top
  -- Of lists, which the abstraction does not look into (#812).
  | .listFn _, _, _ => AVal.top
  | .lt, a, b =>
      -- Two strings may compare either way; FALSE < TRUE.
      let s := a.str && b.str
      let t := s || (a.ff && b.tt)
      let f := s || (a.tt && (b.tt || b.ff)) || (a.ff && b.ff)
      match a.int, b.int with
      | some x, some y => ⟨a.nonInt || b.nonInt, none, canLt x y || t, canGe x y || f, false, none⟩
      | _, _ => ⟨true, none, t, f, false, none⟩

theorem strMayEq_of {a b : AVal} {s : String}
    (ha : a.str = true ∧ a.strs.all (·.contains s) = true)
    (hb : b.str = true ∧ b.strs.all (·.contains s) = true) : strMayEq a b = true := by
  unfold strMayEq
  cases hA : a.strs <;> cases hB : b.strs <;> simp_all
  exact ⟨s, ha.2, hb.2⟩

theorem strMayNe_of {a b : AVal} {s s' : String}
    (ha : a.str = true ∧ a.strs.all (·.contains s) = true)
    (hb : b.str = true ∧ b.strs.all (·.contains s') = true) (hne : s ≠ s') :
    strMayNe a b = true := by
  unfold strMayNe
  simp only [ha.1, hb.1, Bool.true_and]
  split
  · rename_i x y hx hy
    simp only [hx, hy, Option.all_some, List.contains_cons, List.contains_nil, Bool.or_false,
      beq_iff_eq] at ha hb
    simp only [bne_iff_ne, ne_eq]
    rw [← ha.2, ← hb.2]; exact hne
  · rfl

/-- A higher-order function's result: a boolean or `NULL` (`any_match`,
`all_match`), or a list or `NULL`, which the abstraction does not look into. -/
def HoFn.abs : HoFn → AVal
  | .anyMatch | .allMatch => ⟨true, none, true, true, false, none⟩
  | .transform | .filter => AVal.top

theorem or3_bool_or_null (a b : Value) : or3 a b = .null ∨ ∃ x, or3 a b = .bool x := by
  unfold or3; split <;> simp

theorem and3_bool_or_null (a b : Value) : and3 a b = .null ∨ ∃ x, and3 a b = .bool x := by
  unfold and3; split <;> simp

theorem HoFn.abs_sound (f : HoFn) (v : Value) (p : Value → Value) : f.abs.Mem (f.apply v p) := by
  have key : ∀ r : Value, (r = .null ∨ ∃ x, r = .bool x) →
      (⟨true, none, true, true, false, none⟩ : AVal).Mem r := by
    rintro r (rfl | ⟨x, rfl⟩)
    · rfl
    · cases x <;> rfl
  cases f
  case transform | filter => exact AVal.mem_top _
  case anyMatch =>
    apply key
    cases v
    case list vs =>
      cases vs with
      | nil => exact .inr ⟨false, rfl⟩
      | cons x xs => exact or3_bool_or_null _ _
    all_goals exact .inl rfl
  case allMatch =>
    apply key
    cases v
    case list vs =>
      cases vs with
      | nil => exact .inr ⟨true, rfl⟩
      | cons x xs => exact and3_bool_or_null _ _
    all_goals exact .inl rfl

def Expr.abs (env : List AVal) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => env.getD i AVal.top
  | .un f a => f.abs (a.abs env)
  | .bin f a b => f.abs (a.abs env) (b.abs env)
  | .ifThen c t e =>
      let ac := c.abs env
      (if ac.tt then t.abs env else AVal.bot).join
        (if ac.nonBool || ac.ff then e.abs env else AVal.bot)
  | .hof f _ _ => f.abs

/-- Shapes of a value, for case analysis in the binary soundness proofs. -/
theorem AVal.mem_cases {a : AVal} {v : Value} (h : a.Mem v) :
    (v = .null ∧ a.null = true) ∨ (∃ i b, v = .int i ∧ a.int = some b ∧ b.Mem i) ∨
    (v = .bool true ∧ a.tt = true) ∨ (v = .bool false ∧ a.ff = true) ∨
    (∃ s, v = .str s ∧ a.str = true ∧ a.strs.all (·.contains s) = true) ∨ (∃ vs, v = .list vs ∧ a.tt = true ∧ a.ff = true ∧ a.str = true) := by
  match v, h with
  | .null, h => exact .inl ⟨rfl, h⟩
  | .int i, ⟨b, hb, hm⟩ => exact .inr (.inl ⟨i, b, rfl, hb, hm⟩)
  | .bool true, h => exact .inr (.inr (.inl ⟨rfl, h⟩))
  | .bool false, h => exact .inr (.inr (.inr (.inl ⟨rfl, h⟩)))
  | .str s, h =>
      simp only [AVal.Mem, Bool.and_eq_true] at h
      exact .inr (.inr (.inr (.inr (.inl ⟨s, rfl, h⟩))))
  | .list vs, h => exact .inr (.inr (.inr (.inr (.inr ⟨vs, rfl, h⟩))))

/-- `mem_cases h with i b hb hi` splits `h : a.Mem v` into its six cases and
substitutes `v`: `hn` (NULL), an integer `i` with `hb : a.int = some b` and
`hi : b.Mem i`, `ht` (TRUE), `hf` (FALSE), `hs` (a string `s` or a list). -/
syntax "mem_cases " term " with " Lean.Parser.Tactic.rcasesPatLo Lean.Parser.Tactic.rcasesPatLo
  Lean.Parser.Tactic.rcasesPatLo Lean.Parser.Tactic.rcasesPatLo : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mem_cases $h with $i $b $hb $hi) => `(tactic|
      rcases AVal.mem_cases $h with ⟨rfl, hn⟩ | ⟨$i, $b, rfl, $hb, $hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf⟩ |
        ⟨s, rfl, hs⟩ | ⟨_, rfl, hs⟩)

/-- `mem_cases₂ ha hb` splits two memberships: `i x hx hi` and `j y hy hj` for
integers, `h` and `h'` for the other cases (strings `s`, `s'`). -/
syntax "mem_cases₂ " term:max term:max : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mem_cases₂ $ha $hb) => `(tactic|
      rcases AVal.mem_cases $ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
        ⟨s, rfl, h⟩ | ⟨_, rfl, h⟩ <;>
      rcases AVal.mem_cases $hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
        ⟨s', rfl, h'⟩ | ⟨_, rfl, h'⟩)

theorem monoAbs_sound {g : Int → Int} (hg : ∀ {x y}, x ≤ y → g x ≤ g y) {f : UnFn}
    (hf : ∀ v, f.apply v = match v with | .int c => .int (g c) | _ => .null)
    {a : AVal} {v : Value} (h : a.Mem v) : (monoAbs g a).Mem (f.apply v) := by
  rw [hf]
  mem_cases h with i b hb hi
  · simp [monoAbs, AVal.Mem, AVal.nonInt, hn]
  · exact ⟨b.mapMono g, by simp [monoAbs, hb], Bound.mem_mapMono hg hi⟩
  all_goals simp_all [monoAbs, AVal.Mem, AVal.nonInt]

/-- `g` applied to an integer; anything else becomes `NULL`. -/
def Value.mapInt (g : Int → Int) : Value → Value
  | .int c => .int (g c)
  | _ => .null

theorem monoAbs_mem {g : Int → Int} (hg : ∀ {x y}, x ≤ y → g x ≤ g y) {a : AVal} {v : Value}
    (h : a.Mem v) : (monoAbs g a).Mem (Value.mapInt g v) := by
  mem_cases h with i b hb hi
  · simp [Value.mapInt, monoAbs, AVal.Mem, AVal.nonInt, hn]
  · exact ⟨b.mapMono g, by simp [monoAbs, hb], Bound.mem_mapMono hg hi⟩
  all_goals simp_all [Value.mapInt, monoAbs, AVal.Mem, AVal.nonInt]

theorem ftoiAbs_sound {a : AVal} {v : Value} (h : a.Mem v) :
    (ftoiAbs a).Mem (UnFn.apply .ftoi v) := by
  mem_cases h with c b hb hc
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
    (⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false, none⟩ : AVal).Mem (f.apply v) := by
  rw [hf]
  mem_cases h with i b hb hi
  · simp [AVal.Mem, AVal.nonInt, hn]
  · exact ⟨Bound.top, by simp [hb], Bound.mem_top _⟩
  all_goals simp_all [AVal.Mem, AVal.nonInt]

theorem partialAbs_sound {f : UnFn} {g : Int → Option Int} {safe : Bool} {a : AVal}
    (hf : ∀ v, f.apply v = match v with
      | .int c => (match g c with | some r => .int r | none => .null) | _ => .null)
    (hs : safe = true → ∀ c, a.Mem (.int c) → (g c).isSome = true)
    {v : Value} (h : a.Mem v) : (partialAbs safe a).Mem (f.apply v) := by
  rw [hf]
  rcases AVal.mem_cases h with ⟨rfl, hn⟩ | ⟨i, b, rfl, hb, hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf'⟩ | ⟨s, rfl, hs'⟩ | ⟨_, rfl, hs'⟩
  · simp [partialAbs, AVal.Mem, AVal.nonInt, hn]
  · cases hg : g i with
    | some r => simp only [hg]; exact ⟨Bound.top, by simp [partialAbs, hb], Bound.mem_top _⟩
    | none =>
      simp only [hg]
      cases hsafe : safe
      · simp [partialAbs, AVal.Mem]
      · have := hs hsafe i ⟨b, hb, hi⟩; simp [hg] at this
  all_goals simp_all [partialAbs, AVal.Mem, AVal.nonInt]

theorem partialAbs₂_sound {f : BinFn} {g : Int → Int → Option Int} {safe : Bool} {a b : AVal}
    (hf : ∀ v w, f.apply v w = match v, w with
      | .int i, .int j => (match g i j with | some r => .int r | none => .null) | _, _ => .null)
    (hs : safe = true → ∀ i j, a.Mem (.int i) → b.Mem (.int j) → (g i j).isSome = true)
    {v w : Value} (ha : a.Mem v) (hb : b.Mem w) : (partialAbs₂ safe a b).Mem (f.apply v w) := by
  rw [hf]
  mem_cases₂ ha hb <;>
  simp only [] <;> try (simp_all [partialAbs₂, AVal.Mem, AVal.nonInt]; done)
  cases hg : g i j with
  | some r => exact ⟨Bound.top, by simp [partialAbs₂, hx, hy], Bound.mem_top _⟩
  | none =>
    cases hsafe : safe
    · simp [partialAbs₂, AVal.Mem]
    · have := hs hsafe i j ⟨x, hx, hi⟩ ⟨y, hy, hj⟩; simp [hg] at this

theorem FMath.inDomain_of_safe {f : FMath} {a : AVal} {c : Int} (hs : f.safe a = true)
    (hm : a.Mem (.int c)) : f.inDomain c = true := by
  obtain ⟨b, hb, hc⟩ := hm
  simp only [FMath.safe, hb, Option.all_some, Bool.and_eq_true] at hs
  simp only [FMath.inDomain, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨?_, .inl ?_⟩
  · cases hl : f.lo? with
    | none => rfl
    | some l =>
      simp only [hl, Option.all_some] at hs
      simpa using Bound.allGe_le hs.1 hc
  · cases hh : f.hi? with
    | none => rfl
    | some h =>
      simp only [hh, Option.all_some] at hs
      simpa using Bound.le_allLe hs.2 hc

theorem BinFn.domainSafe_atan2 {a b : AVal} (hs : BinFn.domainSafe .fatan2 a b = true) {i j : Int}
    (hi : a.Mem (.int i)) (hj : b.Mem (.int j)) : (atan2? i j).isSome = true := by
  obtain ⟨x, hx, hi⟩ := hi
  obtain ⟨y, hy, hj⟩ := hj
  simp only [BinFn.domainSafe, hx, hy, Option.all_some, Bool.or_eq_true, Bool.not_eq_true'] at hs
  simp only [atan2?]
  split
  · rename_i h0
    rcases hs with hs | hs
    · exact absurd h0.1 (Bound.ne_zero hi hs)
    · exact absurd h0.2 (Bound.ne_zero hj hs)
  · rfl

theorem BinFn.domainSafe_logb {a b : AVal} (hs : BinFn.domainSafe .flogb a b = true) {i j : Int}
    (hi : a.Mem (.int i)) (hj : b.Mem (.int j)) : (logb? i j).isSome = true := by
  obtain ⟨x, hx, hi⟩ := hi
  obtain ⟨y, hy, hj⟩ := hj
  simp only [BinFn.domainSafe, hx, hy, Option.all_some, Bool.and_eq_true, Bool.or_eq_true] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have := Bound.allGe_le h1 hi
  have := Bound.allGe_le h2 hj
  have hne : j ≠ FloatCode.one := by
    rcases h3 with h3 | h3
    · have := Bound.allGe_le h3 hj; omega
    · have := Bound.le_allLe h3 hj; omega
  have hc : 0 < i ∧ 0 < j ∧ j ≠ FloatCode.one := ⟨by omega, by omega, hne⟩
  simp only [logb?, hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte, Option.isSome_some]

theorem BinFn.domainSafe_bit {op : BitOp} {a b : AVal} (hs : BinFn.domainSafe (.bit op) a b = true)
    {i j : Int} (hj : b.Mem (.int j)) : (op.apply i j).isSome = true := by
  obtain ⟨y, hy, hj⟩ := hj
  cases op <;> simp only [BinFn.domainSafe, BitOp.isShift, hy, Option.all_some, Bool.not_true,
    Bool.false_or, Bool.and_eq_true] at hs <;> simp only [BitOp.apply, Option.isSome_some]
  all_goals
    have := Bound.allGe_le hs.1 hj
    have := Bound.le_allLe hs.2 hj
    have hc : 0 ≤ j ∧ j < 64 := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, Option.isSome_some]

theorem datePartAbs_sound (p : Time.DatePart) {a : AVal} {v : Value} (h : a.Mem v) :
    (datePartAbs p a).Mem (UnFn.apply (.datePart p) v) := by
  mem_cases h with ts b hb hi
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
      simp only [AVal.Mem, datePartAbs, hb, Bool.or_eq_true, Bool.not_eq_true']
      right
      obtain ⟨bl, bh⟩ := b
      simp only [Bound.Mem] at hi
      cases bl <;> cases bh <;> simp_all [AVal.within, Bound.within, Bound.allGe, Bound.allLe] <;> omega
  all_goals simp_all [datePartAbs, UnFn.apply, AVal.Mem, AVal.nonInt]

theorem Text.strpos_nonneg (s t : String) : 0 ≤ Text.strpos s t := by
  unfold Text.strpos; apply Text.capped_nonneg; split <;> omega

theorem Text.strpos_le (s t : String) : Text.strpos s t ≤ Text.sizeCap := Text.capped_le _

theorem Text.capped_nat_nonneg (n : Nat) : 0 ≤ Text.capped n := Text.capped_nonneg (by omega)

theorem Text.ascii_nonneg (s : String) : 0 ≤ Text.ascii s := by
  unfold Text.ascii; split <;> omega

theorem convAbs_sound (c : FloatCode.FiniteMonoConv) {f : UnFn}
    (hf : ∀ v, f.apply v = Value.mapInt c.conv v) {a : AVal} {v : Value} (h : a.Mem v) :
    (convAbs c a).Mem (f.apply v) := by
  rw [hf]
  mem_cases h with i b hb hi
  · simp [convAbs, Value.mapInt, AVal.Mem, AVal.nonInt, hn]
  · have : FloatCode.negInf < c.conv i ∧ c.conv i < FloatCode.posInf := c.bounds i
    refine ⟨⟨some (b.lo.elim (FloatCode.negInf + 1) c.conv), some (b.hi.elim (FloatCode.posInf - 1) c.conv)⟩,
      by simp [convAbs, hb], ?_, ?_⟩ <;> intro x hx <;>
      simp only [Option.some.injEq] at hx <;> subst hx
    · cases hl : b.lo with
      | none => simp only [Option.elim]; omega
      | some l => exact c.mono (hi.1 l hl)
    · cases hh : b.hi with
      | none => simp only [Option.elim]; omega
      | some u => exact c.mono (hi.2 u hh)
  all_goals simp_all [convAbs, Value.mapInt, AVal.Mem, AVal.nonInt]

/-- `CAST(x AS INT)` of `n` bits: the integer, or NULL where it does not fit. -/
theorem narrowAbs_sound {n : Nat} {f : UnFn}
    (hf : ∀ v, f.apply v = match v with | .int i => if fitsBits n i then .int i else .null | _ => .null)
    {a : AVal} {v : Value} (h : a.Mem v) : (narrowAbs n a).Mem (f.apply v) := by
  rw [hf]
  mem_cases h with i b hb hi
  · simp_all [narrowAbs, AVal.Mem, AVal.nonInt]
  · dsimp only
    split
    · exact ⟨b, hb, hi⟩
    · rename_i hfit
      cases hfb : b.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1)
      · simp [AVal.Mem, narrowAbs, AVal.within, hb, hfb]
      · exact absurd (Bound.within_mem hfb hi) hfit
  all_goals simp_all [narrowAbs, AVal.Mem, AVal.nonInt]

theorem UnFn.abs_sound (f : UnFn) {a : AVal} {v : Value} (h : a.Mem v) :
    (f.abs a).Mem (f.apply v) := by
  cases f
  case bbox n =>
    refine BlackBox.scalarAbs_mem fun hs => ?_
    cases v <;> simp_all [AVal.Mem]
  case ffloor => exact monoAbs_sound FloatCode.floor_mono (fun v => by cases v <;> rfl) h
  case fceil => exact monoAbs_sound FloatCode.ceil_mono (fun v => by cases v <;> rfl) h
  case fround => exact monoAbs_sound FloatCode.round_mono (fun v => by cases v <;> rfl) h
  case ftoi => exact ftoiAbs_sound h
  case narrow n | narrowOrNull n => exact narrowAbs_sound (fun v => by cases v <;> rfl) h
  case ftoiOrNull =>
    have hf := ftoiAbs_sound h
    mem_cases h with c b hb hc
    · simp [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nullable]
    · simp only [UnFn.abs, UnFn.apply] at hf ⊢
      split at hf
      · split
        · exact AVal.mem_nullable hf
        · simp [AVal.Mem, AVal.nullable]
      · simp [AVal.Mem, AVal.nullable]
    all_goals simp [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nullable]
  case wrap => simpa [UnFn.abs, UnFn.apply] using h
  case decimal => simpa [UnFn.abs, UnFn.apply] using h
  case dkind => simpa [UnFn.abs, UnFn.apply] using h
  case dround k => exact topAbs_sound (fun v => by cases v <;> rfl) h
  case dtrunc k => exact topAbs_sound (fun v => by cases v <;> rfl) h
  case dtof s => exact convAbs_sound _ (fun v => by cases v <;> rfl) h
  case ftod s =>
    have hp := partialAbs_sound (g := fun c => FloatCode.toDecimal? c s) (f := .ftod s) (safe := false)
      (fun v => by cases v <;> rfl) (fun hs => by simp at hs) h
    simp only [UnFn.abs, ftodAbs]
    split
    · rename_i l u hb
      split
      · rename_i x y hx hy
        mem_cases h with i b hb' hi
        · simp [UnFn.apply, AVal.Mem, AVal.nonInt, hn]
        · rw [hb] at hb'; cases hb'
          obtain ⟨q, hq, hxq, hqy⟩ :=
            FloatCode.toDecimal?_between (hi.1 l rfl) (hi.2 u rfl) hx hy
          simp only [UnFn.apply, hq]
          exact ⟨_, rfl, fun z hz => by cases hz; exact hxq, fun z hz => by cases hz; exact hqy⟩
        all_goals simp_all [UnFn.apply, AVal.Mem, AVal.nonInt]
      · exact hp
    · exact hp
  case itof => exact convAbs_sound _ (fun v => by cases v <;> rfl) h
  case froundTo d => exact topAbs_sound (fun v => by cases v <;> rfl) h
  case fmath f =>
    exact partialAbs_sound (fun v => by cases v <;> rfl)
      (fun hs c hm => by simp [FMath.apply, FMath.inDomain_of_safe hs hm]) h
  case itos =>
    mem_cases h with i b hb hi <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonInt]
  case datePart p => exact datePartAbs_sound p h
  case dateTrunc u => exact monoAbs_sound (Time.trunc_mono u) (fun v => by cases v <;> rfl) h
  case toDate => exact monoAbs_sound Time.days_mono (fun v => by cases v <;> rfl) h
  case dayPart p =>
    have hm := monoAbs_mem (g := (· * Time.usPerDay))
      (fun hxy => Int.mul_le_mul_of_nonneg_right hxy (by decide)) h
    have := datePartAbs_sound p hm
    have he : UnFn.apply (.dayPart p) v = UnFn.apply (.datePart p)
        (Value.mapInt (· * Time.usPerDay) v) := by
      cases v <;> rfl
    simp only [UnFn.abs]; rw [he]; exact this
  case dayTrunc u => exact monoAbs_sound (Time.truncDay_mono u) (fun v => by cases v <;> rfl) h
  case addMonths m t =>
    cases t
    · exact monoAbs_sound (Time.addMonths_mono m) (fun v => by cases v <;> rfl) h
    · exact topAbs_sound (fun v => by cases v <;> rfl) h
  case asTime => exact monoAbs_sound (fun h => h) (fun v => by cases v <;> rfl) h
  case dateTime =>
    exact monoAbs_sound (fun hxy => Int.mul_le_mul_of_nonneg_right hxy (by decide))
      (fun v => by cases v <;> rfl) h
  case epochUs => exact monoAbs_sound (fun h => h) (fun v => by cases v <;> rfl) h
  case bucket k o => exact monoAbs_sound (Time.bucket_mono k o) (fun v => by cases v <;> rfl) h
  case timeOfDay =>
    mem_cases h with i b hb hi
    · simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonInt]
    · have := Time.timeOfDay_range i
      refine ⟨⟨some 0, some (Time.usPerDay - 1)⟩, by simp [UnFn.abs, hb], ?_⟩
      exact ⟨fun l hl => by simp at hl; omega, fun u hu => by simp at hu; omega⟩
    all_goals simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonInt]
  case strftime fmt =>
    mem_cases h with i b hb hi <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonInt]
  case upper | lower | length | reverse | ascii | replace | regexExtract | regexReplace | md5 | sha256 =>
    mem_cases h with i b hb hi <;>
      simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonStr, Bound.Mem, Text.ascii_nonneg,
        Text.capped_le, Text.capped_nonneg]
  case structField | listElement | fit | flatten => exact AVal.mem_top _
  case raise => cases v <;> rfl
  case isNum => cases v <;> rfl
  case cardinality =>
    cases v <;> simp [UnFn.abs, UnFn.apply, AVal.Mem, Bound.ge, Bound.Mem]
  case regexMatch p =>
    mem_cases h with i b hb hi <;>
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
  mem_cases₂ ha hb <;>
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

theorem ddivBound_sound {x y : Bound} {i j : Int} (hi : x.Mem i) (hj : y.Mem j) (hj0 : j ≠ 0) :
    (ddivBound x y).Mem (roundDiv i j) := by
  unfold ddivBound
  split
  · rename_i hpos
    obtain ⟨yl, yh⟩ := y
    cases yl with
    | none => simp at hpos
    | some l =>
      simp only [Option.any_some, decide_eq_true_eq] at hpos
      have hj1 := hj.1 l rfl
      obtain ⟨h₁, h₂⟩ := roundDiv_between (a := i) (b := j) (by omega)
      obtain ⟨xl, xh⟩ := x
      refine ⟨fun l' hl' => ?_, fun u' hu' => ?_⟩
      · simp only [Bound.signHull, Option.map_eq_some_iff] at hl'
        obtain ⟨l₀, h₀, rfl⟩ := hl'; have := hi.1 l₀ h₀; omega
      · simp only [Bound.signHull, Option.map_eq_some_iff] at hu'
        obtain ⟨u₀, h₀, rfl⟩ := hu'; have := hi.2 u₀ h₀; omega
  · exact Bound.mem_absHull hi (roundDiv_natAbs_le hj0)

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
  mem_cases₂ ha hb <;>
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
  mem_cases₂ ha hb <;>
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

/-- A comparison of two lists may be TRUE, FALSE or NULL; so may a value
whose abstraction allows all three. -/
theorem Value.ofLt3_ne_int (o : Option Bool) (i : Int) : Value.ofLt3 o ≠ .int i := by
  cases o <;> simp [Value.ofLt3]

theorem Value.ofLt3_ne_str (o : Option Bool) (s : String) : Value.ofLt3 o ≠ .str s := by
  cases o <;> simp [Value.ofLt3]

theorem Value.ofLt3_ne_list (o : Option Bool) (vs : List Value) : Value.ofLt3 o ≠ .list vs := by
  cases o <;> simp [Value.ofLt3]

theorem AVal.mem_ofLt3 {a : AVal} {o : Option Bool} (hn : a.null = true)
    (ht : a.tt = true) (hf : a.ff = true) : a.Mem (Value.ofLt3 o) := by
  cases o with
  | none => exact hn
  | some r => cases r <;> assumption

theorem joinInt_mem_left {x y : Option Bound} {i : Int} (h : ∃ b, x = some b ∧ b.Mem i) :
    ∃ b, joinInt x y = some b ∧ b.Mem i := by
  obtain ⟨b, rfl, hm⟩ := h
  cases y <;> simp [joinInt, hm, Bound.mem_join_left hm]

theorem joinInt_mem_right {x y : Option Bound} {i : Int} (h : ∃ b, y = some b ∧ b.Mem i) :
    ∃ b, joinInt x y = some b ∧ b.Mem i := by
  obtain ⟨b, rfl, hm⟩ := h
  cases x <;> simp [joinInt, hm, Bound.mem_join_right hm]

theorem pickAbs_sound {both : Bound → Bound → Bound} {better : Value → Value → Bool}
    (hboth : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j →
      (both x y).Mem (if better (.int i) (.int j) then j else i))
    (hmix : ∀ i w, (∀ j, w ≠ .int j) → better (.int i) w = false)
    (hmix' : ∀ v j, (∀ i, v ≠ .int i) → better v (.int j) = false)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (pickAbs both a b).Mem (Value.pick better v w) := by
  rcases v with _ | (_ | _) | i | s | l <;> rcases w with _ | (_ | _) | j | t | m <;>
    simp only [Value.pick] <;> (try split) <;>
    simp_all only [AVal.Mem, pickAbs, AVal.nonInt, Bool.and_eq_true, Bool.or_eq_true,
      true_or, or_true, and_self, reduceCtorEq, ne_eq, not_false_eq_true, implies_true,
      Option.all_none]
  -- What is left: an integer result.
  all_goals first
    -- A comparison of an integer with another kind is FALSE.
    | (exfalso; simp_all; done)
    -- Two integers: `both`.
    | (obtain ⟨x, hx, hm⟩ := ha; obtain ⟨y, hy, hm'⟩ := hb
       have h := hboth hm hm'
       refine joinInt_mem_right (joinInt_mem_right ⟨both x y, ?_, ?_⟩)
       · simp [hx, hy]
       · simpa [*] using h)
    -- `NULL` and an integer: the integer.
    | (obtain ⟨y, hy, hm⟩ := hb
       refine joinInt_mem_right (joinInt_mem_left ⟨y, ?_, hm⟩); simp [hy]; done)
    -- An integer and a `NULL`, or a value of another kind: the integer.
    | (obtain ⟨x, hx, hm⟩ := ha
       refine joinInt_mem_left ⟨x, ?_, hm⟩; simp_all; done)

theorem le_of_natAbs_le {z : Int} {n : Nat} (h : z.natAbs ≤ n) : -(n : Int) ≤ z ∧ z ≤ n := by
  omega

theorem natAbs_le_endsMag {l h s : Int} (h1 : l ≤ s) (h2 : s ≤ h) : s.natAbs ≤ endsMag l h := by
  unfold endsMag; omega

theorem finEnds_mem {x : Bound} {i la ha : Int} (hx : x.Mem i) (h : finEnds x = some (la, ha)) :
    FloatCode.IsFin i ∧ la ≤ FloatCode.scaled i ∧ FloatCode.scaled i ≤ ha ∧
      (FloatCode.scaled i).natAbs ≤ endsMag la ha := by
  unfold finEnds at h
  cases hxl : x.lo with
  | none => simp [hxl] at h
  | some l =>
    cases hxh : x.hi with
    | none => simp [hxl, hxh] at h
    | some hh =>
      simp only [hxl, hxh] at h
      by_cases hc : FloatCode.negInf < l ∧ hh < FloatCode.posInf
      · simp only [hc, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := hx.1 l hxl
        have h2 := hx.2 hh hxh
        have m1 := FloatCode.scaled_mono h1
        have m2 := FloatCode.scaled_mono h2
        exact ⟨⟨by omega, by omega⟩, m1, m2, natAbs_le_endsMag m1 m2⟩
      · simp [hc] at h

theorem codeBound_mem {l h s : Int} {c : Int} (hs : FloatCode.scaled c = s) (hl : l ≤ s) (hh : s ≤ h) :
    (codeBound l h).Mem c := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · cases hx; exact FloatCode.codeLo_le (by omega)
  · cases hx; exact FloatCode.le_codeHi (by omega)

theorem add_ends {la ha lb hb si sj sr : Int} {k e : Nat} (li : la ≤ si) (hi : si ≤ ha)
    (lj : lb ≤ sj) (hj : sj ≤ hb) (he : -(k : Int) ≤ sr - (si + sj) ∧ sr - (si + sj) ≤ k)
    (hke : k ≤ e) : la + lb - e ≤ sr ∧ sr ≤ ha + hb + e := by omega

theorem sub_ends {la ha lb hb si sj sr : Int} {k e : Nat} (li : la ≤ si) (hi : si ≤ ha)
    (lj : lb ≤ sj) (hj : sj ≤ hb) (he : -(k : Int) ≤ sr - (si - sj) ∧ sr - (si - sj) ≤ k)
    (hke : k ≤ e) : la - hb - e ≤ sr ∧ sr ≤ ha - lb + e := by omega

theorem faddBound_mem' (sub : Bool) {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    {r : Int} (hr : sub = false → r = FloatCode.lift₂ (· + ·) i j)
    (hr' : sub = true → r = FloatCode.lift₂ (· - ·) i j) :
    (faddBound sub x y).Mem r := by
  unfold faddBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hS
      have hle : (FloatCode.scaled i).natAbs + (FloatCode.scaled j).natAbs ≤
          endsMag la ha + endsMag lb hb := Nat.add_le_add mi mj
      have hke := Nat.add_le_add_right (Nat.div_le_div_right (c := 2 ^ 50) hle) 1
      cases sub
      · obtain ⟨-, he⟩ := FloatCode.add_scaled fi fj (Nat.le_trans hle hS)
        obtain ⟨b1, b2⟩ := add_ends li hi lj hj (le_of_natAbs_le he) hke
        rw [hr rfl]
        exact codeBound_mem rfl b1 b2
      · obtain ⟨-, he⟩ := FloatCode.sub_scaled fi fj (Nat.le_trans hle hS)
        obtain ⟨b1, b2⟩ := sub_ends li hi lj hj (le_of_natAbs_le he) hke
        rw [hr' rfl]
        exact codeBound_mem rfl b1 b2
    · exact Bound.mem_top _
  · exact Bound.mem_top _

theorem mul_ends {l h p q : Int} {k E : Nat} {K : Int} (hK : 0 < K) (hl : l ≤ p) (hh : p ≤ h)
    {sr : Int} (hq : K * sr = q) (he : -(k : Int) ≤ q - p ∧ q - p ≤ k) (hkE : k ≤ E) :
    (l - E) / K ≤ sr ∧ sr ≤ (h + E) / K := by
  have a1 : l - E ≤ sr * K := by rw [Int.mul_comm, hq]; omega
  have a2 : sr * K ≤ h + E := by rw [Int.mul_comm, hq]; omega
  exact ⟨Int.ediv_le_of_le_mul hK a1, Int.le_ediv_of_mul_le hK a2⟩

theorem fmulBound_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fmulBound x y).Mem (FloatCode.lift₂ (· * ·) i j) := by
  unfold fmulBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hP
      have hle : (FloatCode.scaled i).natAbs * (FloatCode.scaled j).natAbs ≤
          endsMag la ha * endsMag lb hb := Nat.mul_le_mul mi mj
      have hkE := Nat.add_le_add_right (Nat.div_le_div_right (c := 2 ^ 50) hle) (2 ^ 1074)
      obtain ⟨-, he⟩ := FloatCode.mul_scaled fi fj (Nat.le_trans hle hP)
      have hm : (Bound.mul ⟨some la, some ha⟩ ⟨some lb, some hb⟩).Mem
          (FloatCode.scaled i * FloatCode.scaled j) :=
        Bound.mem_mul ⟨fun _ h => by cases h; exact li, fun _ h => by cases h; exact hi⟩
          ⟨fun _ h => by cases h; exact lj, fun _ h => by cases h; exact hj⟩
      split
      · rename_i l h hb'
        rw [hb'] at hm
        have hK : (0 : Int) < ((2 ^ 1074 : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos 1074
        have hc : ((2 ^ 1074 : Nat) : Int) = 2 ^ 1074 := Int.natCast_pow 2 1074
        obtain ⟨b1, b2⟩ := mul_ends hK (hm.1 l rfl) (hm.2 h rfl) (by rw [hc]) (le_of_natAbs_le he) hkE
        exact codeBound_mem rfl b1 b2
      · exact Bound.mem_top _
    · exact Bound.mem_top _
  · exact Bound.mem_top _

theorem endsMin_le {lb hb s : Int} (hl : lb ≤ s) (hh : s ≤ hb) : endsMin lb hb ≤ s.natAbs := by
  unfold endsMin; split
  · omega
  · split <;> omega

set_option exponentiation.threshold 3200 in
theorem fdivBound_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fdivBound x y).Mem (FloatCode.lift₂ (· / ·) i j) := by
  unfold fdivBound
  split
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, li, hi, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, mj⟩ := finEnds_mem hy hfb
    dsimp only
    split
    · rename_i hc
      obtain ⟨hmb, hM⟩ := hc
      have hmin := endsMin_le lj hj
      have hj0 : FloatCode.scaled j ≠ 0 := by
        intro h0; rw [h0] at hmin; simp at hmin; omega
      have hguard : (FloatCode.scaled i).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (FloatCode.scaled j).natAbs :=
        Nat.le_trans (Nat.mul_le_mul_right _ mi) (Nat.le_trans hM (Nat.mul_le_mul_left _ hmin))
      obtain ⟨-, he⟩ := FloatCode.div_scaled fi fj hj0 hguard
      have h1 : (FloatCode.scaled i).natAbs * (2 ^ 1074 + 2 ^ 1024) / (FloatCode.scaled j).natAbs ≤
          endsMag la ha * (2 ^ 1074 + 2 ^ 1024) / endsMin lb hb :=
        Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_right _ mi))
          (Nat.div_le_div_left hmin hmb)
      obtain ⟨b1, b2⟩ := le_of_natAbs_le (Nat.le_trans he (Nat.add_le_add_right h1 1))
      exact codeBound_mem rfl b1 b2
    · exact Bound.mem_top _
  · exact Bound.mem_top _

set_option exponentiation.threshold 3200 in
theorem faddOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : faddOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧
      (FloatCode.scaled i).natAbs + (FloatCode.scaled j).natAbs ≤ 2 ^ 2097 := by
  unfold faddOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, -, -, mj⟩ := finEnds_mem hy hfb
    exact ⟨fi, fj, Nat.le_trans (Nat.add_le_add mi mj) (of_decide_eq_true hok)⟩
  · simp at hok

set_option exponentiation.threshold 3200 in
theorem fmulOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : fmulOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧
      (FloatCode.scaled i).natAbs * (FloatCode.scaled j).natAbs ≤ 2 ^ 3171 := by
  unfold fmulOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, -, -, mj⟩ := finEnds_mem hy hfb
    exact ⟨fi, fj, Nat.le_trans (Nat.mul_le_mul mi mj) (of_decide_eq_true hok)⟩
  · simp at hok

set_option exponentiation.threshold 3200 in
theorem fdivOk_guard {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    (hok : fdivOk x y = true) : FloatCode.IsFin i ∧ FloatCode.IsFin j ∧ FloatCode.scaled j ≠ 0 ∧
      (FloatCode.scaled i).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (FloatCode.scaled j).natAbs := by
  unfold fdivOk at hok
  split at hok
  · rename_i la ha lb hb hfa hfb
    obtain ⟨fi, -, -, mi⟩ := finEnds_mem hx hfa
    obtain ⟨fj, lj, hj, -⟩ := finEnds_mem hy hfb
    obtain ⟨hmb, hM⟩ := of_decide_eq_true hok
    have hmin := endsMin_le lj hj
    have hj0 : FloatCode.scaled j ≠ 0 := by
      intro h0; rw [h0] at hmin; simp at hmin; omega
    exact ⟨fi, fj, hj0,
      Nat.le_trans (Nat.mul_le_mul_right _ mi) (Nat.le_trans hM (Nat.mul_le_mul_left _ hmin))⟩
  · simp at hok

theorem faddBoundS_mem (sub : Bool) {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j)
    {r : Int} (hr : sub = false → r = FloatCode.lift₂ (· + ·) i j)
    (hr' : sub = true → r = FloatCode.lift₂ (· - ·) i j) :
    (faddBoundS sub x y).Mem r := by
  have hm := faddBound_mem' sub hx hy hr hr'
  unfold faddBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hs, hxn⟩, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hg⟩ := faddOk_guard hx hy hok
    have h0 : 0 ≤ r := by
      rw [hr hs]
      exact FloatCode.add_nonneg fi fj hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn)
    exact Bound.mem_atLeast0 hm h0
  · exact hm

theorem fmulBoundS_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fmulBoundS x y).Mem (FloatCode.lift₂ (· * ·) i j) := by
  have hm := fmulBound_mem hx hy
  unfold fmulBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hxn, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hg⟩ := fmulOk_guard hx hy hok
    exact Bound.mem_atLeast0 hm
      (FloatCode.mul_nonneg fi fj hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn))
  · exact hm

theorem fdivBoundS_mem {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) :
    (fdivBoundS x y).Mem (FloatCode.lift₂ (· / ·) i j) := by
  have hm := fdivBound_mem hx hy
  unfold fdivBoundS
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hxn, hyn⟩, hok⟩ := hc
    obtain ⟨fi, fj, hj0, hg⟩ := fdivOk_guard hx hy hok
    exact Bound.mem_atLeast0 hm
      (FloatCode.div_nonneg fi fj hj0 hg (Bound.nonneg_mem hx hxn) (Bound.nonneg_mem hy hyn))
  · exact hm

theorem BinFn.abs_sound (f : BinFn) {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (f.abs a b).Mem (f.apply v w) := by
  cases f
  case bbox2 n =>
    refine BlackBox.scalarAbs_mem fun hs => ?_
    cases v <;> cases w <;> simp_all [AVal.Mem]
  case pair => exact AVal.mem_top _
  case listFn => exact AVal.mem_top _
  case greatest =>
    exact pickAbs_sound (fun hx hy => by simpa [Value.ltB] using Bound.mem_greatest hx hy)
      (fun _ w hw => by cases w <;> simp_all [Value.ltB])
      (fun v _ hv => by cases v <;> simp_all [Value.ltB]) ha hb
  case least =>
    exact pickAbs_sound (fun hx hy => by simpa [Value.ltB] using Bound.mem_least hx hy)
      (fun _ w hw => by cases w <;> simp_all [Value.ltB])
      (fun v _ hv => by cases v <;> simp_all [Value.ltB]) ha hb
  case add => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case sub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case dateDiff => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case dateAdd => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case mul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case dadd => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case dsub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case dmul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case ddiv =>
    refine divAbs_sound ddivBound_sound (fun v w => ?_) ha hb
    cases v <;> cases w <;> try rfl
    rename_i i j
    by_cases hj : j = 0
    · simp [BinFn.apply, roundDivInt?, hj]
    · simp [BinFn.apply, roundDiv, roundDivInt?, hj]
  case fadd =>
    exact arith_sound (f := FloatCode.lift₂ (· + ·))
      (fun hx hy => faddBoundS_mem false hx hy (fun _ => rfl) (fun h => by cases h))
      (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fsub =>
    exact arith_sound (f := FloatCode.lift₂ (· - ·))
      (fun hx hy => faddBoundS_mem true hx hy (fun h => by cases h) (fun _ => rfl))
      (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fmul => exact arith_sound fmulBoundS_mem (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fdiv => exact arith_sound fdivBoundS_mem (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fmod => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case fpow => exact arith_sound (fun _ _ => Bound.mem_top _) (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case idiv => exact divAbs_sound divBound_sound (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case imod => exact divAbs_sound modBound_sound (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case ipow => exact powAbs_sound ha hb
  case fatan2 =>
    exact partialAbs₂_sound (fun v w => by cases v <;> cases w <;> rfl)
      (fun hs _ _ hi hj => BinFn.domainSafe_atan2 hs hi hj) ha hb
  case flogb =>
    exact partialAbs₂_sound (fun v w => by cases v <;> cases w <;> rfl)
      (fun hs _ _ hi hj => BinFn.domainSafe_logb hs hi hj) ha hb
  case bit op =>
    exact partialAbs₂_sound (fun v w => by cases v <;> cases w <;> rfl)
      (fun hs _ _ _ hj => BinFn.domainSafe_bit hs hj) ha hb
  case concat | trim | strpos | startsWith | endsWith | like | substr | strRepeat | ilike
    | levenshtein =>
    mem_cases₂ ha hb <;>
    simp_all [BinFn.abs, BinFn.apply, AVal.Mem, AVal.nonStr, AVal.nonInt, Bound.Mem,
      Text.strpos_nonneg, Text.strpos_le, Text.capped_le, Text.capped_nat_nonneg]
    all_goals split <;> simp_all
  case eq =>
    mem_cases₂ ha hb <;>
    simp only [BinFn.abs, BinFn.apply, AVal.Mem]
    all_goals first | (simp_all; done) | skip
    -- What is left: two integers, or two strings.
    · by_cases hij : i = j
      · subst hij
        have : (i == i) = true := by simp
        rw [this]; simp [intEq_of hx hy hi hj]
      · have : (i == j) = false := by simpa using hij
        rw [this]; simp [intNe_of hx hy hi hj hij]
    · by_cases hss : s = s'
      · subst hss; simp [strMayEq_of h h']
      · have : (s == s') = false := by simpa using hss
        rw [this]; simp [strMayNe_of h h' hss]
    -- Two lists.
    · rename_i vs ws
      by_cases hv : vs = ws <;> simp [hv, h.1, h.2.1, h'.1, h'.2.1]
  all_goals
    mem_cases₂ ha hb <;>
    try simp_all [BinFn.abs, BinFn.apply, and3, or3, AVal.Mem, AVal.nonBool, AVal.nonInt]
  -- Two lists (`Value.listLt3`): TRUE, FALSE or NULL, all of which the
  -- abstraction of a comparison of non-integers allows.
  all_goals first | (apply AVal.mem_ofLt3 <;> split <;> first | rfl | (split <;> rfl)) | skip
  all_goals (first | (split <;> simp_all [canLt, canGe]) | skip)
  -- What is left: comparisons of two integers against their intervals, and
  -- of two strings.
  all_goals first
    | (obtain ⟨xl, xh⟩ := x
       obtain ⟨yl, yh⟩ := y
       simp only [Bound.Mem] at hi hj
       cases xl <;> cases xh <;> cases yl <;> cases yh <;> simp_all <;> omega)
    | (split <;> rfl)
    -- Two lists: a comparison is TRUE, FALSE or NULL.
    | (exfalso; simp_all [Value.ofLt3_ne_int, Value.ofLt3_ne_str, Value.ofLt3_ne_list]; done)
    | (split <;> rfl)
    | (rcases hai : a.int with _ | _ <;> rcases hbi : b.int with _ | _ <;>
       split <;> (try rfl) <;>
       (exfalso; simp_all [Value.ofLt3_ne_int, Value.ofLt3_ne_str, Value.ofLt3_ne_list]))

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
          rcases AVal.mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        exact Expr.abs_sound h e
  | .hof f _ _ => HoFn.abs_sound f _ _

/-! ## Constant decimals

A decimal constant is its unscaled integer under `UnFn.decimal`, possibly
brought to another scale by `Parse.upscale` (`· 10ᵏ`): `0.05` compared with a
`DECIMAL(15, 4)` column is `DECIMAL_3_2(5) * 100`. The refinements below
recognize integer literals, so conditions are first written with such
constants folded (`Expr.normConst`, #27). -/

/-- The integer a constant decimal expression evaluates to. -/
def Expr.constInt? : Expr → Option Int
  | .lit (.int k) => some k
  | .un (.decimal _ _) a => a.constInt?
  | .bin .dmul a b => a.constInt?.bind fun x => b.constInt?.map (x * ·)
  | _ => none

theorem Expr.constInt?_eval (row : Row) :
    ∀ (e : Expr) {k : Int}, e.constInt? = some k → e.eval row = .int k := by
  intro e
  induction e with
  | lit v => intro k h; cases v <;> simp_all [Expr.constInt?, Expr.eval]
  | field => intro k h; simp [Expr.constInt?] at h
  | un f a ih =>
    intro k h
    cases f
    case decimal => simp only [Expr.constInt?] at h; simp [Expr.eval, ih h, UnFn.apply]
    all_goals simp [Expr.constInt?] at h
  | bin f a b iha ihb =>
    intro k h
    cases f
    case dmul =>
      cases ha : a.constInt? <;> cases hb : b.constInt? <;> simp [Expr.constInt?, ha, hb] at h
      subst h
      simp [Expr.eval, iha ha, ihb hb, BinFn.apply]
    all_goals simp [Expr.constInt?] at h
  | ifThen => intro k h; simp [Expr.constInt?] at h
  | hof => intro k h; simp [Expr.constInt?] at h

/-- `e` with its constant decimals folded to integer literals. -/
def Expr.normConst : Expr → Expr
  | .un f a => match (Expr.un f a).constInt? with
    | some k => .lit (.int k)
    | none => .un f a.normConst
  | .bin f a b => match (Expr.bin f a b).constInt? with
    | some k => .lit (.int k)
    | none => .bin f a.normConst b.normConst
  | .ifThen c t e => .ifThen c.normConst t.normConst e.normConst
  | e => e

theorem Expr.eval_normConst (row : Row) : ∀ e : Expr, e.normConst.eval row = e.eval row := by
  intro e
  induction e with
  | un f a ih =>
    simp only [Expr.normConst]
    split
    · rename_i k hk; rw [Expr.constInt?_eval row _ hk]; rfl
    · simp [Expr.eval, ih]
  | bin f a b iha ihb =>
    simp only [Expr.normConst]
    split
    · rename_i k hk; rw [Expr.constInt?_eval row _ hk]; rfl
    · simp [Expr.eval, iha, ihb]
  | ifThen c t e ihc iht ihe => simp [Expr.normConst, Expr.eval, ihc, iht, ihe]
  | lit | field | hof => rfl

/-! ## Refinement by filter conditions -/

/-- A column known to be a non-NULL integer, with its interval transformed. -/
def AVal.nonNullInt (a : AVal) (f : Bound → Bound) : AVal := ⟨false, a.int.map f, false, false, false, none⟩

/-- `a` without NULL: what an operand of a TRUE `<` can be. -/
def AVal.nonNullOrd (a : AVal) : AVal := { a with null := false }

/-- An integer, a string, a boolean or a list: what `<` compares. -/
def Value.isOrd : Value → Bool
  | .int _ | .str _ | .bool _ | .list _ => true
  | _ => false

/-- The strings both lists allow. -/
def meetStrs : Option (List String) → Option (List String) → Option (List String)
  | some l, some m => some (l.filter m.contains)
  | some l, none => some l
  | none, m => m

theorem meetStrs_mem {x y : Option (List String)} {s : String} (hx : x.all (·.contains s) = true)
    (hy : y.all (·.contains s) = true) : (meetStrs x y).all (·.contains s) = true := by
  cases x <;> cases y <;> simp_all [meetStrs]

/-- What a value known to equal (SQL `=`, so non-NULL) a value in `b` can be. -/
def AVal.meetEq (a b : AVal) : AVal :=
  ⟨false, (match a.int, b.int with | some x, some y => some (x.meet y) | _, _ => none),
   a.tt && b.tt, a.ff && b.ff, a.str && b.str, meetStrs a.strs b.strs⟩

theorem AVal.meetEq_mem {a b : AVal} {v : Value} (ha : a.Mem v) (hb : b.Mem v) (hn : v ≠ .null) :
    (a.meetEq b).Mem v := by
  match v, ha, hb with
  | .null, _, _ => exact absurd rfl hn
  | .int i, ⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩ =>
      exact ⟨x.meet y, by simp [AVal.meetEq, hx, hy], Bound.mem_meet hxi hyi⟩
  | .bool true, ha, hb | .bool false, ha, hb =>
      simp_all [AVal.Mem, AVal.meetEq]
  | .str _, ha, hb =>
      simp only [AVal.Mem, AVal.meetEq, Bool.and_eq_true] at *
      exact ⟨⟨ha.1, hb.1⟩, meetStrs_mem ha.2 hb.2⟩
  | .list _, ha, hb =>
      simp only [AVal.Mem, AVal.meetEq] at *
      exact ⟨by simp [ha.1, hb.1], by simp [ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩

/-- A value known to be the string `k` (#708). -/
def AVal.strIs (k : String) (a : AVal) : AVal :=
  ⟨false, none, false, false, a.str, meetStrs a.strs (some [k])⟩

/-- A value known not to be the string `k`. -/
def AVal.strNot (k : String) (a : AVal) : AVal := { a with strs := a.strs.map (·.filter (· != k)) }

theorem AVal.strIs_mem {a : AVal} {k : String} (h : a.Mem (.str k)) : (a.strIs k).Mem (.str k) := by
  simp only [AVal.Mem, AVal.strIs, Bool.and_eq_true] at *
  exact ⟨h.1, meetStrs_mem h.2 (by simp)⟩

theorem AVal.strNot_mem {a : AVal} {k : String} {v : Value} (h : a.Mem v)
    (hv : ∀ s, v = .str s → s ≠ k) : (a.strNot k).Mem v := by
  cases v with
  | str s =>
      have := hv s rfl
      cases hA : a.strs <;> simp_all [AVal.Mem, AVal.strNot]
  | bool b => cases b <;> simp_all [AVal.Mem, AVal.strNot]
  | _ => simp_all [AVal.Mem, AVal.strNot]

def refineCol (env : List AVal) (i : Nat) (f : AVal → AVal) : List AVal :=
  env.set i (f (env.getD i AVal.top))

/-- What a row that makes `e` TRUE satisfies, for constants that are integer
literals (`Expr.refine` folds the others first). Recognizes conjunctions,
disjunctions, comparisons of a column with an integer constant, `IS NULL`
and `IS NOT NULL`. -/
def Expr.refineL (env : List AVal) : Expr → List AVal
  | .bin .and p q => q.refineL (p.refineL env)
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
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  | .un .not (.un .isNull (.bin .sub a b)) =>
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  | .un .not (.un .isNull (.bin .mul a b)) =>
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  -- `p OR q` (e.g. `x IN (1, 2)`): what `p` gives, or what `q` gives.
  | .bin .or p q => List.zipWith AVal.join (p.refineL env) (q.refineL env)
  -- `x IS NULL`: only NULL (so `x IS NULL OR x >= 0` keeps the bound).
  | .un .isNull (.field i) => refineCol env i fun a => ⟨a.null, none, false, false, false, none⟩
  -- A string column equal to a constant, or not (#708).
  | .bin .eq (.field i) (.lit (.str k)) => refineCol env i (AVal.strIs k)
  | .un .not (.bin .eq (.field i) (.lit (.str k))) => refineCol env i (AVal.strNot k)
  -- `NOT (p OR q)`: neither is TRUE, so `x NOT IN ('a', 'b')` leaves the others.
  | .un .not (.bin .or p q) => (Expr.un .not q).refineL ((Expr.un .not p).refineL env)
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

theorem Expr.refineL_length (env : List AVal) (e : Expr) :
    (e.refineL env).length = env.length := by
  fun_induction Expr.refineL env e <;> simp_all [refineCol_length]

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

theorem eq_str {v : Value} {k : String} (h : (BinFn.apply .eq v (.str k)).isTrue = true) :
    v = .str k := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]
  rename_i x; by_cases hx : x = k <;> simp_all

theorem not_eq_str {v : Value} {k : String}
    (h : (UnFn.apply .not (BinFn.apply .eq v (.str k))).isTrue = true) :
    ∀ s, v = .str s → s ≠ k := by
  rintro s rfl rfl
  simp [BinFn.apply, UnFn.apply, Value.isTrue] at h

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

/-- `<` with a NULL side is never TRUE, nor is its negation; by `rfl` on each
value, without unfolding `BinFn.apply` under `simp`. -/
theorem lt_null_left (w : Value) : (BinFn.apply .lt .null w).isTrue = false := by
  cases w <;> rfl

theorem lt_null_right (v : Value) : (BinFn.apply .lt v .null).isTrue = false := by
  cases v <;> rfl

theorem not_lt_null_left (w : Value) :
    (UnFn.apply .not (BinFn.apply .lt .null w)).isTrue = false := by
  cases w <;> rfl

theorem not_lt_null_right (v : Value) :
    (UnFn.apply .not (BinFn.apply .lt v .null)).isTrue = false := by
  cases v <;> rfl

theorem lt_fields_ord {v w : Value} (h : (BinFn.apply .lt v w).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  refine ⟨?_, ?_⟩
  · cases v <;> first | rfl | (rw [lt_null_left] at h; cases h)
  · cases w <;> first | rfl | (rw [lt_null_right] at h; cases h)

theorem not_lt_fields_ord {v w : Value}
    (h : (UnFn.apply .not (BinFn.apply .lt v w)).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  refine ⟨?_, ?_⟩
  · cases v <;> first | rfl | (rw [not_lt_null_left] at h; cases h)
  · cases w <;> first | rfl | (rw [not_lt_null_right] at h; cases h)

theorem nonNullOrd_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : v.isOrd = true) :
    a.nonNullOrd.Mem v := by
  cases v with
  | bool x => cases x <;> simp_all [AVal.nonNullOrd, AVal.Mem]
  | _ => simp_all [Value.isOrd, AVal.nonNullOrd, AVal.Mem]

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

theorem Expr.refineL_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refineL env) row := by
  fun_induction Expr.refineL env e
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
  case case17 env i k =>
    have hx := eq_str (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact AVal.strIs_mem this
  case case18 env i k =>
    refine refineCol_sound h (AVal.strNot_mem (h i) ?_)
    exact not_eq_str (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
  case case19 env p q ihp ihq =>
    have ht' : (UnFn.apply .not (or3 (p.eval row) (q.eval row))).isTrue = true := by
      simpa [eval, BinFn.apply] using ht
    obtain ⟨h₁, h₂⟩ := not_or3_true ht'
    exact ihq (ihp h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case20 => exact h

/-- What a row that makes `e` TRUE satisfies (`refineL`), with constant
decimals folded first (`Expr.normConst`). -/
def Expr.refine (env : List AVal) (e : Expr) : List AVal := e.normConst.refineL env

theorem Expr.refine_length (env : List AVal) (e : Expr) : (e.refine env).length = env.length :=
  Expr.refineL_length env _

theorem Expr.refine_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refine env) row :=
  Expr.refineL_sound env _ h (by rwa [Expr.eval_normConst])

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
  /-- A string in `l`; if `strict`, certainly a (non-NULL) string (#708). -/
  | strIn (l : List String) (strict : Bool)
  /-- Not the string `k` (but maybe NULL or not a string). -/
  | strNe (k : String)

def Cstr.Holds : Cstr → Value → Prop
  | .null, v => v = .null
  | .notNull, v => v ≠ .null
  | .intIn b true, v => ∃ j, v = .int j ∧ b.Mem j
  | .intIn b false, v => ∀ j, v = .int j → b.Mem j
  | .ne k, v => ∀ j, v = .int j → j ≠ k
  | .strIn l true, v => ∃ s, v = .str s ∧ s ∈ l
  | .strIn l false, v => ∀ s, v = .str s → s ∈ l
  | .strNe k, v => ∀ s, v = .str s → s ≠ k

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
  | .bin .eq s (.lit (.str k)) => some (s, if pos then .strIn [k] true else .strNe k)
  | .un .not (.bin .eq s (.lit (.str k))) => some (s, if pos then .strNe k
      else .strIn [k] false)
  | _ => none

/-- Narrow an abstract value by a constraint. -/
def Cstr.apply : Cstr → AVal → AVal
  | .null, a => ⟨a.null, none, false, false, false, none⟩
  | .notNull, a => { a with null := false }
  | .intIn b true, a => ⟨false, a.int.map (·.meet b), false, false, false, none⟩
  | .intIn b false, a => { a with int := a.int.map (·.meet b) }
  -- Intervals cannot exclude a single value.
  | .ne _, a => a
  | .strIn l true, a => ⟨false, none, false, false, a.str, meetStrs a.strs (some l)⟩
  | .strIn l false, a => { a with strs := meetStrs a.strs (some l) }
  | .strNe k, a => a.strNot k

/-- The constraint on `-v` (integer or double negation) given one on `v`. -/
def Cstr.neg : Cstr → Option Cstr
  | .null => some .null
  | .notNull => none
  | .intIn b strict => some (.intIn b.neg strict)
  | .ne k => some (.ne (-k))
  | .strIn _ _ | .strNe _ => none

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
  mem_cases ha with j x hx hm
  all_goals cases k with
    | null => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
    | notNull => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
    | intIn b strict =>
      cases strict <;> simp_all [Cstr.Holds, Cstr.apply, AVal.Mem] <;> exact Bound.mem_meet hm hk
    | ne k => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
    | strIn l strict =>
      cases strict <;> cases hA : a.strs <;> simp_all [Cstr.Holds, Cstr.apply, AVal.Mem, meetStrs]
    | strNe k => exact AVal.strNot_mem (by simp_all [AVal.Mem]) hk

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
  | .strIn _ _, _, h | .strNe _, _, h => simp [Cstr.neg] at h

/-- Constraints known to hold on the current row, each on the value of an
expression (the conditions of the enclosing `CASE` branches and `OR`s). -/
abbrev Assumptions := List (Expr × Cstr)

def KsHold (ks : Assumptions) (row : Row) : Prop := ∀ p ∈ ks, p.2.Holds (p.1.eval row)

/-- `c`'s constraint when it is TRUE (`pos`) or not, as assumptions. -/
def Expr.cstrs (pos : Bool) (c : Expr) : Assumptions := (c.normConst.cstr pos).toList

theorem KsHold.cons_cstrs {pos : Bool} {c : Expr} {ks : Assumptions} {row : Row}
    (ht : (c.eval row).isTrue = pos) (hks : KsHold ks row) : KsHold (c.cstrs pos ++ ks) row := by
  intro p hp
  simp only [List.mem_append, Expr.cstrs] at hp
  rcases hp with hp | hp
  · cases hc : c.normConst.cstr pos with
    | none => simp [hc] at hp
    | some sk => simp only [hc, Option.toList_some, List.mem_singleton] at hp; subst hp;
                 exact Expr.cstr_sound hc (by rwa [Expr.eval_normConst])
  · exact hks p hp

/-! ### Alternatives (#702)

`AND` that is not TRUE says one of its sides is not TRUE, which no single
constraint states. `Expr.cstrAlts` keeps such a condition as alternatives:
on every row where it is (not) TRUE, every assumption of one alternative
holds. The DuckDB lift guards `a * b` on doubles with
`CASE WHEN (a = ∞ OR a = -∞) AND b = 0 THEN NaN …`, and the `ELSE` branch
then knows `a ≠ ±∞` or `b ≠ 0`, which rules out the NaN of `0 · ∞`. -/

/-- One alternative of each list, together. -/
def altsProd (xs ys : List Assumptions) : List Assumptions :=
  xs.flatMap fun x => ys.map (x ++ ·)

/-- At most eight alternatives; beyond that, none of them (`[[]]`, which
always holds). -/
def altsCapped (as : List Assumptions) : List Assumptions :=
  if as.length ≤ 8 then as else [[]]

/-- Does one alternative hold on the row? -/
def AltsHold (as : List Assumptions) (row : Row) : Prop := ∃ ks ∈ as, KsHold ks row

theorem KsHold.append {ks ks' : Assumptions} {row : Row} (h : KsHold ks row)
    (h' : KsHold ks' row) : KsHold (ks ++ ks') row := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem KsHold.of_append_left {ks ks' : Assumptions} {row : Row} (h : KsHold (ks ++ ks') row) :
    KsHold ks row := fun p hp => h p (List.mem_append_left _ hp)

theorem KsHold.of_append_right {ks ks' : Assumptions} {row : Row} (h : KsHold (ks ++ ks') row) :
    KsHold ks' row := fun p hp => h p (List.mem_append_right _ hp)

theorem AltsHold.prod {xs ys : List Assumptions} {row : Row} (hx : AltsHold xs row)
    (hy : AltsHold ys row) : AltsHold (altsProd xs ys) row := by
  obtain ⟨x, hx, hkx⟩ := hx
  obtain ⟨y, hy, hky⟩ := hy
  exact ⟨x ++ y, List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩, hkx.append hky⟩

theorem AltsHold.capped {as : List Assumptions} {row : Row} (h : AltsHold as row) :
    AltsHold (altsCapped as) row := by
  unfold altsCapped
  split
  · exact h
  · exact ⟨[], by simp, fun _ hp => by simp at hp⟩

/-- What `c` being TRUE (`pos`) or not TRUE says, as alternatives. -/
def Expr.cstrAltsL (pos : Bool) : Expr → List Assumptions
  | .bin .and p q => altsCapped (if pos then altsProd (p.cstrAltsL true) (q.cstrAltsL true)
      else p.cstrAltsL false ++ q.cstrAltsL false)
  | .bin .or p q => altsCapped (if pos then p.cstrAltsL true ++ q.cstrAltsL true
      else altsProd (p.cstrAltsL false) (q.cstrAltsL false))
  | e => [(e.cstr pos).toList]

theorem Expr.cstrAltsL_sound {row : Row} (pos : Bool) (c : Expr)
    (ht : (c.eval row).isTrue = pos) : AltsHold (c.cstrAltsL pos) row := by
  fun_induction Expr.cstrAltsL pos c
  case case1 pos p q ihpt ihqt ihpf ihqf =>
    refine AltsHold.capped ?_
    simp only [eval, BinFn.apply, isTrue_and3] at ht
    cases pos
    · simp only [Bool.and_eq_false_iff] at ht
      simp only [Bool.false_eq_true, ite_false]
      rcases ht with ht | ht
      · obtain ⟨k, hk, h⟩ := ihpf ht
        exact ⟨k, List.mem_append_left _ hk, h⟩
      · obtain ⟨k, hk, h⟩ := ihqf ht
        exact ⟨k, List.mem_append_right _ hk, h⟩
    · simp only [Bool.and_eq_true] at ht
      simp only [ite_true]
      exact (ihpt ht.1).prod (ihqt ht.2)
  case case2 pos p q ihpt ihqt ihpf ihqf =>
    refine AltsHold.capped ?_
    simp only [eval, BinFn.apply, isTrue_or3] at ht
    cases pos
    · simp only [Bool.or_eq_false_iff] at ht
      simp only [Bool.false_eq_true, ite_false]
      exact (ihpf ht.1).prod (ihqf ht.2)
    · simp only [Bool.or_eq_true] at ht
      simp only [ite_true]
      rcases ht with ht | ht
      · obtain ⟨k, hk, h⟩ := ihpt ht
        exact ⟨k, List.mem_append_left _ hk, h⟩
      · obtain ⟨k, hk, h⟩ := ihqt ht
        exact ⟨k, List.mem_append_right _ hk, h⟩
  case case3 pos e _ _ =>
    refine ⟨(e.cstr pos).toList, by simp, ?_⟩
    intro p hp
    cases hc : e.cstr pos with
    | none => simp [hc] at hp
    | some sk =>
      simp only [hc, Option.toList_some, List.mem_singleton] at hp
      subst hp
      exact Expr.cstr_sound hc ht

/-- `cstrAltsL`, with constant decimals folded first (as `cstrs`). -/
def Expr.cstrAlts (pos : Bool) (c : Expr) : List Assumptions := c.normConst.cstrAltsL pos

theorem Expr.cstrAlts_sound {row : Row} {pos : Bool} {c : Expr}
    (ht : (c.eval row).isTrue = pos) : AltsHold (c.cstrAlts pos) row :=
  Expr.cstrAltsL_sound pos _ (by rwa [Expr.eval_normConst])

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
def Expr.refineNegL (env : List AVal) : Expr → List AVal
  | .bin .or p q => q.refineNegL (p.refineNegL env)
  | .bin .and p q => List.zipWith AVal.join (p.refineNegL env) (q.refineNegL env)
  | e => match e.cstr false with
    | some (.field i, k) => refineCol env i k.apply
    | _ => env

theorem Expr.refineNegL_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = false) : EnvMem (e.refineNegL env) row := by
  fun_induction Expr.refineNegL env e
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

/-- What a row that makes `e` FALSE or NULL satisfies (`refineNegL`), with
constant decimals folded first. -/
def Expr.refineNeg (env : List AVal) (e : Expr) : List AVal := e.normConst.refineNegL env

theorem Expr.refineNeg_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = false) : EnvMem (e.refineNeg env) row :=
  Expr.refineNegL_sound env _ h (by rwa [Expr.eval_normConst])

/-! ## Whole conditions on a row (#597)

A precondition that relates columns (`a <= 0 OR b < 0`) says nothing about
one column on its own. Kept whole, it proves itself where the plan carries it
through unchanged (`Fact.holds`), and it narrows a column once the other
disjuncts are ruled out on a path (`Expr.refineOr`). -/

/-- Does `p` hold for every column the expression reads? A lambda's body
reads its parameter as field 0 and the row from field 1 (D28). -/
def Expr.allFields (p : Nat → Bool) : Expr → Bool
  | .lit _ => true
  | .field i => p i
  | .un _ a => a.allFields p
  | .bin _ a b => a.allFields p && b.allFields p
  | .ifThen c t e => c.allFields p && t.allFields p && e.allFields p
  | .hof _ l b => l.allFields p && b.allFields (liftPred p)

/-- Read column `g i` wherever the expression reads column `i`. -/
def Expr.mapFields (g : Nat → Nat) : Expr → Expr
  | .lit v => .lit v
  | .field i => .field (g i)
  | .un f a => .un f (a.mapFields g)
  | .bin f a b => .bin f (a.mapFields g) (b.mapFields g)
  | .ifThen c t e => .ifThen (c.mapFields g) (t.mapFields g) (e.mapFields g)
  | .hof f l b => .hof f (l.mapFields g) (b.mapFields (liftIdx g))

theorem Expr.allFields_true : ∀ e : Expr, e.allFields (fun _ => true) = true
  | .lit _ | .field _ => rfl
  | .un _ a => Expr.allFields_true a
  | .bin _ a b => by simp [allFields, Expr.allFields_true a, Expr.allFields_true b]
  | .ifThen c t e => by
      simp [allFields, Expr.allFields_true c, Expr.allFields_true t, Expr.allFields_true e]
  | .hof _ l b => by simp [allFields, Expr.allFields_true l, Expr.allFields_true b]

theorem Expr.allFields_and {p q : Nat → Bool} :
    ∀ {e : Expr}, e.allFields p = true → e.allFields q = true → e.allFields (fun i => p i && q i) = true
  | .lit _, _, _ => rfl
  | .field _, hp, hq => by simp_all [allFields]
  | .un _ a, hp, hq => Expr.allFields_and (e := a) hp hq
  | .bin _ a b, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      exact ⟨Expr.allFields_and hp.1 hq.1, Expr.allFields_and hp.2 hq.2⟩
  | .ifThen c t e, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨Expr.allFields_and hp.1.1 hq.1.1, Expr.allFields_and hp.1.2 hq.1.2⟩,
        Expr.allFields_and hp.2 hq.2⟩
  | .hof _ l b, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      refine ⟨Expr.allFields_and hp.1 hq.1, ?_⟩
      rw [liftPred_and]; exact Expr.allFields_and hp.2 hq.2

theorem Expr.mapFields_id : ∀ e : Expr, e.mapFields id = e
  | .lit _ | .field _ => rfl
  | .un f a => by simp [mapFields, Expr.mapFields_id a]
  | .bin f a b => by simp [mapFields, Expr.mapFields_id a, Expr.mapFields_id b]
  | .ifThen c t e => by
      simp [mapFields, Expr.mapFields_id c, Expr.mapFields_id t, Expr.mapFields_id e]
  | .hof f l b => by simp [mapFields, Expr.mapFields_id l, Expr.mapFields_id b]

/-- Moving the columns an expression reads, with their values, keeps its
value. -/
theorem Expr.eval_mapFields {p : Nat → Bool} {g : Nat → Nat} {row row' : Row}
    (hg : ∀ i, p i = true → row'.getD (g i) .null = row.getD i .null) :
    ∀ {e : Expr}, e.allFields p = true → (e.mapFields g).eval row' = e.eval row
  | .lit _, _ => rfl
  | .field i, h => hg i h
  | .un f a, h => by simp only [mapFields, eval, Expr.eval_mapFields hg (e := a) h]
  | .bin f a b, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1, Expr.eval_mapFields hg h.2]
  | .ifThen c t e, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1.1, Expr.eval_mapFields hg h.1.2,
        Expr.eval_mapFields hg h.2]
  | .hof f l b, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1]
      congr 1; funext x
      exact Expr.eval_mapFields (liftIdx_getD x hg) h.2

/-- The same expression on a row that agrees on the columns it reads. -/
theorem Expr.eval_congr {p : Nat → Bool} {row row' : Row}
    (hg : ∀ i, p i = true → row'.getD i .null = row.getD i .null) {e : Expr}
    (h : e.allFields p = true) : e.eval row' = e.eval row := by
  simpa [Expr.mapFields_id] using Expr.eval_mapFields (g := id) hg h

theorem AVal.not_isTrue {a : AVal} {v : Value} (hm : a.Mem v) (ht : a.tt = false) :
    v.isTrue = false := by
  match v, hm with
  | .bool true, hm => simp_all [AVal.Mem]
  | .bool false, _ | .null, _ | .int _, _ | .str _, _ | .list _, _ => rfl

/-- What a row on which `e` is TRUE satisfies, by cases: a disjunct that
cannot be TRUE under `env` is dropped, so under `a > 0` the condition
`a <= 0 OR b < 0` narrows `b` to `b < 0`. A `CASE` (`ibis.ifelse`) whose
condition is decided under `env` is its branch. A disjunct that is NULL is
not TRUE either, so a NULL operand is dropped with the FALSE ones. -/
def Expr.refineOr (env : List AVal) : Expr → List AVal
  | .bin f p q =>
      if f = .or then
        if (p.abs env).tt = false then q.refineOr env
        else if (q.abs env).tt = false then p.refineOr env
        else List.zipWith AVal.join (p.refineOr env) (q.refineOr env)
      else (Expr.bin f p q).refine env
  | .ifThen c t e =>
      if (c.abs env).tt = false then e.refineOr env
      else if (c.abs env).certainlyTrue then t.refineOr env
      else env
  | e => e.refine env

theorem Expr.refineOr_length (env : List AVal) : ∀ e : Expr, (e.refineOr env).length = env.length
  | .bin f p q => by
      simp only [refineOr]
      split
      · split
        · exact Expr.refineOr_length env q
        · split
          · exact Expr.refineOr_length env p
          · simp [Expr.refineOr_length env p, Expr.refineOr_length env q]
      · exact Expr.refine_length env _
  | .ifThen c t e => by
      simp only [refineOr]
      split
      · exact Expr.refineOr_length env e
      · split
        · exact Expr.refineOr_length env t
        · rfl
  | .lit _ | .field _ | .un _ _ | .hof _ _ _ => Expr.refine_length env _

theorem Expr.refineOr_sound {row : Row} (env : List AVal) (h : EnvMem env row) :
    ∀ (e : Expr), (e.eval row).isTrue = true → EnvMem (e.refineOr env) row
  | .bin f p q, ht => by
      simp only [refineOr]
      split
      · rename_i hf
        subst hf
        simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht
        split
        · rename_i hp
          exact Expr.refineOr_sound env h q
            (ht.resolve_left (by simp [AVal.not_isTrue (Expr.abs_sound h p) hp]))
        · split
          · rename_i _ hq
            exact Expr.refineOr_sound env h p
              (ht.resolve_right (by simp [AVal.not_isTrue (Expr.abs_sound h q) hq]))
          · rcases ht with hp | hq
            · exact EnvMem.zip_left (Expr.refineOr_sound env h p hp)
            · exact EnvMem.zip_right (Expr.refineOr_sound env h q hq)
      · exact Expr.refine_sound env _ h ht
  | .ifThen c t e, ht => by
      simp only [refineOr]
      have hc := Expr.abs_sound h c
      split
      · rename_i hct
        have hnc := AVal.not_isTrue hc hct
        simp only [eval, hnc] at ht
        exact Expr.refineOr_sound env h e ht
      · split
        · rename_i _ hcert
          have hcv := AVal.certainlyTrue_mem hcert hc
          simp only [eval, hcv, Value.isTrue, ite_true] at ht
          exact Expr.refineOr_sound env h t ht
        · exact h
  | .lit _, ht | .field _, ht | .un _ _, ht | .hof _ _ _, ht => Expr.refine_sound env _ h ht

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
  /-- If columns `s` and `c` hold integers `x` and `n`, then `n` is positive
  and `x` is a sum of `n` integers in `b`: the `SUM` and `COUNT` of a decimal
  `AVG` (`Parse.decimalAvgs`, #237). -/
  | ratio (s c : Nat) (b : Bound)
  /-- The condition is TRUE on the row: a precondition or filter condition
  kept whole, whatever its shape (#597). -/
  | holds (e : Expr)
  deriving Repr, DecidableEq

def Fact.Holds (row : Row) : Fact → Prop
  | .diff i j b => ∀ x y, row.getD i .null = .int x → row.getD j .null = .int y → b.Mem (x - y)
  | .ne i k => row.getD i .null ≠ .int k
  | .ratio s c b => ∀ x n, row.getD s .null = .int x → row.getD c .null = .int n →
      0 < n ∧ (∀ l, b.lo = some l → n * l ≤ x) ∧ (∀ h, b.hi = some h → x ≤ n * h)
  | .holds e => (e.eval row).isTrue = true

def FactsHold (fs : List Fact) (row : Row) : Prop := ∀ f ∈ fs, f.Holds row

theorem FactsHold.append {fs gs : List Fact} {row : Row} (h₁ : FactsHold fs row)
    (h₂ : FactsHold gs row) : FactsHold (fs ++ gs) row := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h₁ f hf
  · exact h₂ f hf

theorem FactsHold.filter {fs : List Fact} {row : Row} (h : FactsHold fs row) (p : Fact → Bool) :
    FactsHold (fs.filter p) row := fun f hf => h f (List.mem_filter.mp hf).1

/-- Narrow `env` by every whole condition among the facts. -/
def useFacts (fs : List Fact) (env : List AVal) : List AVal :=
  fs.foldl (fun env f => match f with | .holds e => e.refineOr env | _ => env) env

theorem useFacts_length : ∀ (fs : List Fact) (env : List AVal), (useFacts fs env).length = env.length
  | [], _ => rfl
  | f :: fs, env => by
      simp only [useFacts, List.foldl_cons]
      rw [← useFacts, useFacts_length fs]
      split
      · exact Expr.refineOr_length env _
      · rfl

theorem useFacts_sound {row : Row} :
    ∀ {fs : List Fact} {env : List AVal}, FactsHold fs row → EnvMem env row →
      EnvMem (useFacts fs env) row
  | [], _, _, h => h
  | f :: fs, env, hfs, h => by
      simp only [useFacts, List.foldl_cons]
      rw [← useFacts]
      refine useFacts_sound (fun g hg => hfs g (by simp [hg])) ?_
      split
      · rename_i e
        exact Expr.refineOr_sound env h e (hfs (.holds e) (by simp))
      · exact h

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
  | .diff a b _ | .ratio a b _ => a == i || b == i
  | .ne a _ => a == i
  -- A whole condition may be about NULLs.
  | .holds _ => false

/-- Facts that hold where `x IS NULL` (`q`), from the facts `fs` of the
other side of an `OR`: those about `x` (facts only constrain non-NULL values). -/
def orNullFacts (fs : List Fact) : Expr → List Fact
  | .un .isNull (.field i) => fs.filter (·.mentions i)
  | _ => []

/-- `t < a OR b < t` with `a ≤ b`: `t` is not in `[a, b]`, so not `0` when
`0` is in it, and not `a`. -/
def orGapFacts : Expr → Expr → List Fact
  | .bin .lt t (.lit (.int a)), .bin .lt (.lit (.int b)) t' =>
    if t == t' && a ≤ b then (if a ≤ 0 && 0 ≤ b then neFact t 0 else []) ++ neFact t a else []
  | _, _ => []

def Expr.factsCore : Expr → List Fact
  | .bin .and p q => p.factsCore ++ q.factsCore
  | .un .not (.bin .eq t (.lit (.int k))) => neFact t k
  | .un .not (.bin .eq (.lit (.int k)) t) => neFact t k
  | .bin .eq t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => .exact (c₂ - c₁)
  | .bin .lt t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => ⟨none, some (c₂ - c₁ - 1)⟩
  | .un .not (.bin .lt t₁ t₂) => diffFact t₁ t₂ fun c₁ c₂ => ⟨some (c₂ - c₁), none⟩
  -- NOT (p OR q) is NOT p AND NOT q.
  | .un .not (.bin .or p q) => (Expr.un .not p).factsCore ++ (Expr.un .not q).factsCore
  -- NOT (x IS NOT NULL AND q): either x is NULL, or NOT q. Facts about x hold
  -- in both cases, since facts only constrain non-NULL values. (Ibis writes
  -- `~x.isnan()` this way.)
  | .un .not (.bin .and (.un .not (.un .isNull (.field i))) q) =>
      (Expr.un .not q).factsCore.filter (·.mentions i)
  -- `p OR q`: the facts of both, those of one about `x` if the other is
  -- `x IS NULL`, and the value a gap `t < a OR b < t` leaves out.
  | .bin .or p q =>
      let fp := p.factsCore
      let fq := q.factsCore
      fp.filter (fq.contains ·) ++ orNullFacts fp q ++ orNullFacts fq p ++
        orGapFacts p q ++ orGapFacts q p
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

theorem not_and3_notnull_true {x w : Value} (hx : x ≠ .null)
    (h : (UnFn.apply .not (and3 (UnFn.apply .not (UnFn.apply .isNull x)) w)).isTrue = true) :
    (UnFn.apply .not w).isTrue = true := by
  have : UnFn.apply .not (UnFn.apply .isNull x) = .bool true := by
    cases x <;> first | exact absurd rfl hx | rfl
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
  | ratio a b _ =>
    simp only [Fact.mentions, Bool.or_eq_true, beq_iff_eq] at hm
    intro x y hx hy
    rcases hm with rfl | rfl
    · rw [hn] at hx; cases hx
    · rw [hn] at hy; cases hy
  | holds _ => simp [Fact.mentions] at hm

theorem orNullFacts_sound {fs : List Fact} {p q : Expr} {row : Row}
    (hp : (p.eval row).isTrue = true → FactsHold fs row)
    (hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true) {f : Fact}
    (hf : f ∈ orNullFacts fs q) : f.Holds row := by
  unfold orNullFacts at hf
  split at hf
  · rename_i i
    simp only [List.mem_filter] at hf
    rcases hpq with hp' | hq
    · exact hp hp' f hf.1
    · have hn : row.getD i .null = .null := by
        simp only [Expr.eval, List.getD_eq_getElem?_getD] at hq ⊢
        generalize row[i]?.getD Value.null = v at hq ⊢
        cases v <;> simp_all [UnFn.apply, Value.isTrue]
      exact Fact.holds_of_null hf.2 hn
  · simp at hf

theorem orGapFacts_sound {p q : Expr} {row : Row}
    (hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true) {f : Fact}
    (hf : f ∈ orGapFacts p q) : f.Holds row := by
  unfold orGapFacts at hf
  split at hf
  · rename_i t a b t'
    split at hf
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨rfl, hab⟩ := hc
      -- `t`'s value is below `a` or above `b`.
      have hout : ∀ u, t.eval row = .int u → u < a ∨ b < u := by
        intro u hu
        rcases hpq with h | h <;>
          simp only [Expr.eval, hu, BinFn.apply, Value.isTrue] at h <;>
          split at h <;> simp_all <;> omega
      simp only [List.mem_append] at hf
      rcases hf with hf | hf
      · split at hf
        · rename_i h0
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
          exact neFact_sound (fun hv => by have := hout 0 hv; omega) f hf
        · simp at hf
      · exact neFact_sound (fun hv => by have := hout a hv; omega) f hf
    · simp at hf
  · simp at hf

theorem Expr.factsCore_sound {row : Row} (e : Expr) (ht : (e.eval row).isTrue = true) :
    FactsHold e.factsCore row := by
  fun_induction Expr.factsCore e
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
  case case9 p q fp fq ihp ihq =>
    have hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true := by
      simpa [eval, BinFn.apply, isTrue_or3] using ht
    intro f hf
    simp only [List.mem_append, List.mem_filter] at hf
    rcases hf with (((⟨hfp, hfq⟩ | hf) | hf) | hf) | hf
    · rcases hpq with hp | hq
      · exact ihp hp f hfp
      · exact ihq hq f (List.contains_iff_mem.mp hfq)
    · exact orNullFacts_sound ihp hpq hf
    · exact orNullFacts_sound ihq hpq.symm hf
    · exact orGapFacts_sound hpq hf
    · exact orGapFacts_sound hpq.symm hf
  case case10 => intro f hf; simp at hf

/-- The conjuncts of a condition. -/
def Expr.conjuncts : Expr → List Expr
  | .bin f p q => if f = .and then p.conjuncts ++ q.conjuncts else [.bin f p q]
  | e => [e]

theorem Expr.conjuncts_sound {row : Row} :
    ∀ (e : Expr), (e.eval row).isTrue = true → ∀ c ∈ e.conjuncts, (c.eval row).isTrue = true
  | .bin f p q, ht, c, hc => by
      simp only [conjuncts] at hc
      split at hc
      · rename_i hf
        subst hf
        simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact Expr.conjuncts_sound p ht.1 c hc
        · exact Expr.conjuncts_sound q ht.2 c hc
      · simp only [List.mem_singleton] at hc; subst hc; exact ht
  | .lit _, ht, c, hc | .field _, ht, c, hc | .un _ _, ht, c, hc | .ifThen _ _ _, ht, c, hc
  | .hof _ _ _, ht, c, hc => by
      simp only [conjuncts, List.mem_singleton] at hc; subst hc; exact ht

/-- Facts that hold on every row where `e` is TRUE: each conjunct kept whole,
and what `factsCore` derives. -/
def Expr.factsOf (e : Expr) : List Fact := e.conjuncts.map .holds ++ e.factsCore

theorem Expr.factsOf_sound {row : Row} (e : Expr) (ht : (e.eval row).isTrue = true) :
    FactsHold e.factsOf row := by
  refine FactsHold.append ?_ (e.factsCore_sound ht)
  intro f hf
  simp only [List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  exact Expr.conjuncts_sound e ht c hc

/-! ### Facts through a plan -/

def Fact.inRange (n : Nat) : Fact → Bool
  | .diff i j _ | .ratio i j _ => i < n && j < n
  | .ne i _ => i < n
  | .holds e => e.allFields (· < n)

def Fact.shift (n : Nat) : Fact → Fact
  | .diff i j b => .diff (n + i) (n + j) b
  | .ne i k => .ne (n + i) k
  | .ratio i j b => .ratio (n + i) (n + j) b
  | .holds e => .holds (e.mapFields (n + ·))

/-- Does the fact only constrain integers (so it holds where its columns are
NULL)? -/
def Fact.intsOnly : Fact → Bool
  | .holds _ => false
  | _ => true

/-- Re-index a fact: column `i` of the input appears at every position in `σ i`. -/
def Fact.rename (σ : Nat → List Nat) : Fact → List Fact
  | .diff i j b => (σ i).flatMap fun p => (σ j).map fun q => .diff p q b
  | .ne i k => (σ i).map fun p => .ne p k
  | .ratio i j b => (σ i).flatMap fun p => (σ j).map fun q => .ratio p q b
  -- At the first place each column it reads appears, if they all do.
  | .holds e =>
      if e.allFields (fun i => !(σ i).isEmpty) then [.holds (e.mapFields fun i => (σ i).headD 0)] else []

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
  | _ => []

/-- Facts about the window columns appended after `n` input columns. -/
def winFacts (part : List Nat) (sort : List SortKey) (strict : Bool) (n : Nat) (fns : List WinFn) :
    List Fact :=
  fns.zipIdx.flatMap fun (f, t) => winFact part sort strict (n + t) f

/-! ### Facts about the measures of one group

Measures of the same values on one group are related (#372): `MIN ≤ MAX`, and
an integer `AVG` with an integer result lies between them (`AggFn.iavg`). An
`AVG` of doubles rounds, and may step past them, so it has no such fact. -/

/-- Facts relating measure `mi` (column `ci`) to measure `mj` (column `cj`). -/
def pairFacts (ci cj : Nat) (mi mj : Measure) : List Fact :=
  if mi.filter ≠ mj.filter ∨ mj.arg ≠ mi.arg then [] else
  if mi.fn = .min ∧ mj.fn = .max then [.diff cj ci ⟨some 0, none⟩]
  else if mi.fn = .min ∧ mj.fn = .iavg then [.diff cj ci ⟨some 0, none⟩]
  else if mi.fn = .max ∧ mj.fn = .iavg then [.diff ci cj ⟨some 0, none⟩]
  else []

/-- Facts relating the measures `ms`, which follow `g` grouping columns. -/
def aggFacts (g : Nat) (ms : List Measure) : List Fact :=
  (List.range ms.length).flatMap fun i => (List.range ms.length).flatMap fun j =>
    match ms[i]?, ms[j]? with
    | some mi, some mj => pairFacts (g + i) (g + j) mi mj
    | _, _ => []

/-- Does the fact mention a column at or after `n`? -/
def Fact.rightOf (n : Nat) : Fact → Bool
  | .diff i j _ | .ratio i j _ => decide (n ≤ i) || decide (n ≤ j)
  | .ne i _ => decide (n ≤ i)
  | .holds _ => false

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
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++
        ((b.facts cat F T).filter Fact.intsOnly).map (·.shift (a.arity cat)) ++
        on.factsOf.filter (·.rightOf (a.arity cat))
  | .fetch r _ _ => r.facts cat F T
  | .unionAll a b => (a.facts cat F T).filter ((b.facts cat F T).contains ·)
  | .window r part sort fns =>
      (r.facts cat F T).filter (·.inRange (r.arity cat)) ++
        winFacts part sort (T r part sort) (r.arity cat) fns
  -- Some of the left rows, or all of the rows in another order or once each.
  | .semi a _ _ _ => a.facts cat F T
  | .orderBy r _ | .distinct r => r.facts cat F T
  | .aggregate _ gs ms => aggFacts gs.length ms
  | .unnest _ _ => []

theorem headD_mem_of {l : List Nat} (h : (!l.isEmpty) = true) : l.headD 0 ∈ l := by
  cases l with
  | nil => simp at h
  | cons p ps => simp

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
  | .ratio i j _, h, g, hg => by
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i p hp ▸ hx) (hσ j q hq ▸ hy)
  | .holds e, h, g, hg => by
      simp only [Fact.rename] at hg
      split at hg
      · rename_i hall
        simp only [List.mem_singleton] at hg; subst hg
        simp only [Fact.Holds] at h ⊢
        rw [Expr.eval_mapFields (fun i hi => hσ i _ (headD_mem_of hi)) hall]; exact h
      · simp at hg

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
  | .ratio i j _, hr, h => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      intro x y hx hy
      exact h x y (hpre i hr.1 ▸ hx) (hpre j hr.2 ▸ hy)
  | .holds e, hr, h => by
      simp only [Fact.inRange] at hr
      simp only [Fact.Holds] at h ⊢
      rw [Expr.eval_congr (fun i hi => hpre i (by simpa using hi)) hr]; exact h

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
  | ratio i j _ => intro x y hx hy; exact this x y (hsh i ▸ hx) (hsh j ▸ hy)
  | holds e =>
      simp only [Fact.shift, Fact.Holds] at this ⊢
      rw [Expr.eval_mapFields (fun i _ => hsh i) (Expr.allFields_true e)]; exact this

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
  | .ratio i j _, hr, h, g, hg => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i hr.1 p hp ▸ hx) (hσ j hr.2 q hq ▸ hy)
  | .holds e, hr, h, g, hg => by
      simp only [Fact.inRange] at hr
      simp only [Fact.rename] at hg
      split at hg
      · rename_i hall
        simp only [List.mem_singleton] at hg; subst hg
        simp only [Fact.Holds] at h ⊢
        rw [Expr.eval_mapFields (p := fun i => decide (i < n) && !(σ i).isEmpty)
          (fun i hi => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
            exact hσ i hi.1 _ (headD_mem_of hi.2))
          (Expr.allFields_and hr hall)]
        exact h
      · simp at hg

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
    (hnull : ∀ i, row.getD (n + i) .null = .null) :
    FactsHold ((fs.filter Fact.intsOnly).map (·.shift n)) row := by
  intro g hg
  simp only [List.mem_map, List.mem_filter] at hg
  obtain ⟨f, ⟨_, hio⟩, rfl⟩ := hg
  cases f with
  | holds _ => simp [Fact.intsOnly] at hio
  | diff i j b => intro x y hx _; rw [hnull i] at hx; cases hx
  | ne i k => intro hx; rw [hnull i] at hx; cases hx
  | ratio i j _ => intro x y hx _; rw [hnull i] at hx; cases hx

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
  | ratio i j _ =>
    simp only [Fact.rightOf, Bool.or_eq_true, decide_eq_true_eq] at hf
    rcases hf.2 with h | h
    · exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i h)
    · exact Fact.holds_of_null (i := j) (by simp [Fact.mentions]) (hn j h)
  | holds _ => simp [Fact.rightOf] at hf

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
  | rowNumber | rank _ | denseRank _ | percentRank _ | cumeDist _ | ntile _ | agg _ _ _
  | firstValue _ _ _ | lastValue _ _ _ | nthValue _ _ _ _ => intro g hg; simp [winFact] at hg
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

/-- The values of `MIN`, `MAX` and integer `AVG` measures of one group: the
bounds `pairFacts` states. -/
theorem pairFacts_sound {ci cj : Nat} {mi mj : Measure} {grp : Relation} {row : Row}
    (hi : row.getD ci .null = mi.eval grp) (hj : row.getD cj .null = mj.eval grp) :
    FactsHold (pairFacts ci cj mi mj) row := by
  -- The measures here do not sort their rows.
  have evi : ∀ f, mi.fn = f → f.sorts = false → mi.eval grp = f.apply (mi.inputs grp) :=
    fun f h hs => by rw [Measure.eval_eq (h ▸ hs), h]
  have evj : ∀ f, mj.fn = f → f.sorts = false → mj.eval grp = f.apply (mj.inputs grp) :=
    fun f h hs => by rw [Measure.eval_eq (h ▸ hs), h]
  -- `MIN` is one of the values and at most each integer among them; `MAX` at least.
  have minle : mi.fn = .min → ∀ {Y}, row.getD ci .null = .int Y →
      .int Y ∈ mi.inputs grp ∧ ∀ t, .int t ∈ mi.inputs grp → Y ≤ t := fun h Y hY => by
    rw [hi, evi _ h rfl] at hY
    obtain ⟨hm, hle⟩ := AggFn.apply_min hY (by simp)
    exact ⟨hm, fun t ht => Value.le_int.1 (hle _ ht)⟩
  have maxge : mi.fn = .max → ∀ {X}, row.getD ci .null = .int X →
      .int X ∈ mi.inputs grp ∧ ∀ t, .int t ∈ mi.inputs grp → t ≤ X := fun h X hX => by
    rw [hi, evi _ h rfl] at hX
    obtain ⟨hm, hle⟩ := AggFn.apply_max hX (by simp)
    exact ⟨hm, fun t ht => Value.le_int.1 (hle _ ht)⟩
  -- An integer `AVG` lies between two of its integers.
  have avg : mj.fn = .iavg → ∀ {A}, row.getD cj .null = .int A →
      intsOf (mj.inputs grp) ≠ [] →
      (∃ l ∈ intsOf (mj.inputs grp), l ≤ A) ∧ (∃ h ∈ intsOf (mj.inputs grp), A ≤ h) :=
    fun hf A hA hne => by
      obtain ⟨a, ha, hl, hh⟩ := AggFn.apply_iavg_between hne
      rw [hj, evj _ hf rfl, ha] at hA; cases hA
      exact ⟨hl, hh⟩
  have ne_of : ∀ {t : Int}, .int t ∈ mj.inputs grp → intsOf (mj.inputs grp) ≠ [] :=
    fun h => List.ne_nil_of_mem (mem_intsOf.2 h)
  have ge0 : ∀ {d : Int}, 0 ≤ d → Bound.Mem ⟨some 0, none⟩ d :=
    fun h => ⟨fun l hl => by cases hl; exact h, fun _ hh => by cases hh⟩
  unfold pairFacts
  split
  · intro f hf; simp at hf
  rename_i hc0
  simp only [not_or, Decidable.not_not] at hc0
  obtain ⟨hfil, harg⟩ := hc0
  have hiff := Measure.mem_inputs_iff harg hfil.symm grp
  split
  · -- `MIN ≤ MAX`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro X Y hX hY
    rw [hj, evj _ hfj rfl] at hX
    obtain ⟨hm, -⟩ := AggFn.apply_max hX (by simp)
    exact ge0 (by have := (minle hfi hY).2 X ((hiff _).1 hm); omega)
  split
  · -- `MIN ≤ AVG`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro A Y hA hY
    have hY' := minle hfi hY
    obtain ⟨⟨l, hl, hla⟩, -⟩ := avg hfj hA (ne_of ((hiff _).2 hY'.1))
    exact ge0 (by have := hY'.2 l ((hiff _).1 (mem_intsOf.1 hl)); omega)
  split
  · -- `AVG ≤ MAX`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro X A hX hA
    have hX' := maxge hfi hX
    obtain ⟨-, ⟨h, hh, hah⟩⟩ := avg hfj hA (ne_of ((hiff _).2 hX'.1))
    exact ge0 (by have := hX'.2 h ((hiff _).1 (mem_intsOf.1 hh)); omega)
  · intro f hf; simp at hf

theorem aggFacts_sound {g : Nat} {ms : List Measure} {grp : Relation} {k : Row}
    (hk : k.length = g) : FactsHold (aggFacts g ms) (k ++ ms.map (·.eval grp)) := by
  intro f hf
  simp only [aggFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, hi, j, hj, hf⟩ := hf
  have col : ∀ i (m : Measure), ms[i]? = some m →
      (k ++ ms.map (·.eval grp)).getD (g + i) .null = m.eval grp := fun i m h => by
    rw [← hk, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  split at hf
  · rename_i mi mj hmi hmj
    exact pairFacts_sound (col i mi hmi) (col j mj hmj) f hf
  · simp at hf

/-- The facts relating two measures are about measures that do not sort. -/
theorem pairFacts_sorts {ci cj : Nat} {mi mj : Measure} (h : pairFacts ci cj mi mj ≠ []) :
    mi.fn.sorts = false ∧ mj.fn.sorts = false := by
  unfold pairFacts at h
  repeat' split at h
  all_goals first | exact absurd rfl h | (simp_all [AggFn.sorts])

/-- `aggFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem aggFacts_sound_of {g : Nat} {ms : List Measure} {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp) :
    FactsHold (aggFacts g ms) row := by
  intro f hf
  simp only [aggFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    have hs := pairFacts_sorts (List.ne_nil_of_mem hf)
    exact pairFacts_sound (col i mi hmi hs.1) (col j mj hmj hs.2) f hf
  · simp at hf

/-- The measures' columns of an aggregate's row, for `aggFacts_sound_of`. -/
theorem aggCol {ms : List Measure} {grp : Relation} {k : Row} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) :
    ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      (k ++ vs).getD (k.length + i) .null = m.eval grp := by
  intro i m hm hs
  rw [getD_append_right']
  rcases hv.getElem? i with ⟨a, v, ha, hb, hr⟩ | ⟨ha, _⟩
  · rw [hm] at ha; cases ha
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
    obtain ⟨_, _, _, h⟩ := hr.eval
    exact h hs
  · rw [hm] at ha; cases ha

/-- **The facts hold on every row of every order.** -/
theorem Rel.facts_sound_all {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.facts cat F T) row
  | .read t, _, _, h, row, hr => hF t row (h.mem_iff.mp hr)
  | .values _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact (facts_sound_all hcat hF hT hwf.1 hi row hr.1).append (c.factsOf_sound hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      have hfx := facts_sound_all hcat hF hT hwf.1 hi x hx
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
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (facts_sound_all hcat hF hT hwf.1 hi x hx).rename fun i p hp => positions_getD hp
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact ((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2 hy v hv).shift fun i => hlen ▸ getD_append_right' i)
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact (((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2.1 hy v hv).shift fun i => hlen ▸ getD_append_right' i)).append
        (on.factsOf_sound ht)
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      have hfx := facts_sound_all hcat hF hT hwf.1 hx u hu
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
        obtain ⟨⟨v, hv, rfl⟩, ht⟩ := h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (((facts_sound_all hcat hF hT hwf.2.1 hy v hv).filter _).shift
            fun i => hlen ▸ getD_append_right' i)).append
          fun f hf => on.factsOf_sound ht f (List.mem_filter.mp hf).1
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := facts_sound_all hcat hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      facts_sound_all hcat hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      simp only [Rel.facts]
      exact aggFacts_sound_of (grp := grp) (hkl ▸ aggCol hv)
  | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      intro f hf
      simp only [Rel.facts, List.mem_filter, List.contains_iff_mem] at hf
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact facts_sound_all hcat hF hT hwf.1 hx row h f hf.1
      · exact facts_sound_all hcat hF hT hwf.2.1 hy row h f hf.2
  | .window r part sort _, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, he, rfl, hb, ha, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hx := hp.mem_iff.mp (hin x (.inl rfl))
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      simp only [Rel.facts]
      refine ((facts_sound_all hcat hF hT hwf.1 hi x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        (winFacts_sound hlen hwf.2.2.2 hb ha fun hT' y hy _ => ?_)
      -- With a key, rows at different positions of the sorted input differ on it.
      have hk := (hT _ _ _ hT' hwf.1 hi).perm hp.symm fun h => Ne.symm h
      unfold KeyOn at hk
      rw [he, List.pairwise_append, List.pairwise_cons] at hk
      rcases hy with hy | hy
      · exact hk.2.2 y hy x (by simp)
      · exact Ne.symm (hk.2.1.1 y hy)

theorem Rel.facts_sound {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) : ∀ row ∈ r.eval cat, FactsHold (r.facts cat F T) row :=
  Rel.facts_sound_all hcat hF hT hwf (r.eval_orderAllowed cat)

/-- A bound on `x - y` for columns `i` and `j`, from the facts. -/
def Fact.diffBound (i j : Nat) : Fact → Option Bound
  | .diff i' j' b => if i' = i ∧ j' = j then some b else if i' = j ∧ j' = i then some b.neg else none
  | .ne _ _ | .ratio _ _ _ | .holds _ => none

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

/-- The difference, from the facts, within what interval arithmetic gives
(which keeps the bound that shows it fits its width, #202). -/
def subSharpen : Option Bound → AVal → AVal
  | some d, base => { base with int := base.int.map fun b => b.meet d }
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

/-- The bound of a `ratio` fact about columns `s` and `c`. -/
def ratioOf (fs : List Fact) (s c : Nat) : Option Bound :=
  fs.findSome? fun | .ratio s' c' b => if s' = s ∧ c' = c then some b else none | _ => none

/-- A decimal `AVG`, `ddiv(sum · 10ᵏ, count)`, is within its values' bound,
scaled (#237). -/
def ratioSharpen (fs : List Fact) (a b : Expr) (base : AVal) : AVal :=
  match a, b with
  | .bin .dmul (.field s) (.lit (.int k)), .field c =>
    match ratioOf fs s c with
    | some bd =>
      if 0 < k then { base with int := base.int.map (·.meet ⟨bd.lo.map (· * k), bd.hi.map (· * k)⟩) }
      else base
    | none => base
  | _, _ => base

/-- Sharpen the abstract result of `f a b` using facts about `a` and `b`
(`aa` is the abstract value of `a`). -/
def sharpen (fs : List Fact) (f : BinFn) (a b : Expr) (aa base : AVal) : AVal :=
  match f with
  | .ddiv => ratioSharpen fs a b base
  | .sub => subSharpen (termDiff fs a b) base
  -- Facts are about integers; strings compare by themselves.
  | .lt => if aa.intOrNull then ltSharpen (termDiff fs a b) base else base
  | .eq =>
      match termDiff fs a b with
      | some d => if aa.intOrNull then eqSharpen d base else base
      | none => neSharpen fs a b base
  | _ => base

/-- `FALSE OR v`: `v` if it is a boolean, else NULL. -/
def AVal.orFalse (a : AVal) : AVal := ⟨a.null || a.int.isSome || a.str, none, a.tt, a.ff, false, none⟩

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
def AVal.orNull (a : AVal) : AVal := ⟨a.null || a.ff || a.int.isSome || a.str, none, a.tt, false, false, none⟩

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
        orSplit (a.absD env fs ks)
          (b.absD (useFacts fs ((Expr.un .not a).refine env)) fs (a.cstrs false ++ ks))
      else if f = .or ∧ (a.absD env fs ks).int.isNone = true ∧ (a.absD env fs ks).str = false then
        orSplitNull (a.absD env fs ks)
          (b.absD (useFacts fs ((a.refineNeg env).map AVal.prune)) fs (a.cstrs false ++ ks))
      else sharpen fs f a b (a.absD env fs ks) (f.abs (a.absD env fs ks) (b.absD env fs ks))
  -- Each branch is evaluated knowing whether `c` is TRUE.
  | .ifThen c t e => narrowAll ks (.ifThen c t e) <|
      let ac := c.absD env fs ks
      (if ac.tt then t.absD (useFacts fs (c.refine env)) fs (c.cstrs true ++ ks) else AVal.bot).join
        (if ac.nonBool || ac.ff then e.absD (useFacts fs (c.refineNeg env)) fs (c.cstrs false ++ ks)
         else AVal.bot)
  | .hof f l b => narrowAll ks (.hof f l b) f.abs

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
  | ne _ _ | ratio _ _ _ | holds _ => simp [Fact.diffBound] at hg
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
    obtain ⟨b₀, hb₀, hm⟩ := hbase
    exact ⟨b₀.meet d, by simp [hb₀], Bound.mem_meet hm (termDiff_sound hd hfs hva hvb)⟩

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
    -- Strings and booleans are ruled out by `hint`.
    all_goals try (simp_all [AVal.intOrNull, AVal.Mem]; done)
    all_goals try (rename_i x y; cases x <;> cases y <;> simp_all [AVal.intOrNull, AVal.Mem]; done)
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

theorem ratioOf_mem {fs : List Fact} {s c : Nat} {b : Bound} (h : ratioOf fs s c = some b) :
    Fact.ratio s c b ∈ fs := by
  obtain ⟨f, hf, he⟩ := List.exists_of_findSome?_eq_some h
  cases f <;> simp at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  exact hf

theorem ratioSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .ddiv (a.eval row) (b.eval row))) :
    (ratioSharpen fs a b base).Mem (BinFn.apply .ddiv (a.eval row) (b.eval row)) := by
  unfold ratioSharpen
  split
  · rename_i s k c
    split
    · rename_i bd hbd
      split
      · rename_i hk
        -- Only the integer part changes.
        generalize hv : BinFn.apply .ddiv _ _ = v at hbase ⊢
        cases v with
        | int q =>
          obtain ⟨B, hB, hq⟩ := hbase
          refine ⟨B.meet ⟨bd.lo.map (· * k), bd.hi.map (· * k)⟩, by simp [hB], Bound.mem_meet hq ?_⟩
          have ea : (Expr.bin .dmul (.field s) (.lit (.int k))).eval row =
              BinFn.apply .dmul (row.getD s .null) (.int k) := rfl
          have eb : (Expr.field c).eval row = row.getD c .null := rfl
          rw [ea, eb] at hv
          cases hx : row.getD s .null <;> cases hn : row.getD c .null <;> rw [hx, hn] at hv <;>
            simp only [BinFn.apply, reduceCtorEq] at hv
          rename_i x n
          split at hv
          · rename_i r hr; cases hv
            have hn0 : n ≠ 0 := by intro h0; subst h0; simp [roundDivInt?] at hr
            obtain ⟨hpos, hlo, hhi⟩ := hfs _ (ratioOf_mem hbd) x n hx hn
            have hrd : roundDiv (x * k) n = q := by simp [roundDiv, hr]
            obtain ⟨hL, hH⟩ := roundDiv_bounds (a := x * k) hpos
            constructor
            · intro l hl
              obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.mp hl
              rw [← hrd]; apply hL
              have := Int.mul_le_mul_of_nonneg_right (hlo l0 hl0) (Int.le_of_lt hk)
              rwa [Int.mul_assoc] at this
            · intro h hh
              obtain ⟨h0, hh0, rfl⟩ := Option.map_eq_some_iff.mp hh
              rw [← hrd]; apply hH
              have := Int.mul_le_mul_of_nonneg_right (hhi h0 hh0) (Int.le_of_lt hk)
              rwa [Int.mul_assoc] at this
          · cases hv
        | null | str _ | list _ => exact hbase
        | bool bb => cases bb <;> exact hbase
      · exact hbase
    · exact hbase
  · exact hbase

theorem sharpen_sound {fs : List Fact} {row : Row} (f : BinFn) (a b : Expr) {aa base : AVal}
    (hfs : FactsHold fs row) (haa : aa.Mem (a.eval row))
    (hbase : base.Mem (f.apply (a.eval row) (b.eval row))) :
    (sharpen fs f a b aa base).Mem (f.apply (a.eval row) (b.eval row)) := by
  cases f
  case ddiv => exact ratioSharpen_sound hfs hbase
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
        rcases AVal.mem_cases ha with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
        · simp [AVal.nonBool, hn] at hnb
        · simp [AVal.nonBool, hb] at hnb
        · rw [hv]
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hr := Expr.refine_sound env (.un .not a) h (by simp [eval, hv, UnFn.apply, Value.isTrue])
          have hks' := KsHold.cons_cstrs (c := a) (pos := false)
            (by simp [hv, Value.isTrue]) hks
          have hq := Expr.absD_sound (useFacts_sound hfs hr) hfs hks' b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases AVal.mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ | ⟨_, hv', hs⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem]
        · simp [AVal.nonBool, hs] at hnb
        · simp [AVal.nonBool, hs] at hnb
      split
      · rename_i _ hc
        obtain ⟨rfl, hni, hns⟩ := hc
        have ha := Expr.absD_sound h hfs hks a
        rcases AVal.mem_cases ha with ⟨hv, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ |
            ⟨_, _, hs⟩
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env a h hnt).prune) hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hn]
          rcases AVal.mem_cases hq with ⟨hv', hn'⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
              ⟨_, hv', hs⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orNull, AVal.Mem]
        · simp [hb] at hni
        · rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env a h hnt).prune) hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases AVal.mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
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
        exact Expr.absD_sound (useFacts_sound hfs (Expr.refine_sound env c h hct)) hfs
          (KsHold.cons_cstrs hct hks) t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.absD env fs ks).nonBool || (c.absD env fs ks).ff) = true := by
          rcases AVal.mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        have hf : (c.eval row).isTrue = false := by simpa using hct
        exact Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env c h hf)) hfs
          (KsHold.cons_cstrs hf hks) e
  | .hof f _ _ => narrowAll_sound hks (HoFn.abs_sound f _ _)

/-- `absD`, and TRUE for a condition the facts carry whole (#597): an
`ensures` that restates a `requires` the plan keeps. -/
def Expr.absF (env : List AVal) (fs : List Fact) (e : Expr) : AVal :=
  if fs.contains (.holds e) then AVal.ofValue (.bool true) else e.absD env fs

theorem Expr.absF_sound {env : List AVal} {fs : List Fact} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (e : Expr) :
    (e.absF env fs).Mem (e.eval row) := by
  unfold absF
  split
  · rename_i hc
    have ht : (e.eval row).isTrue = true := hfs _ (List.contains_iff_mem.mp hc)
    rw [Value.eq_true_of_isTrue ht]; exact AVal.mem_ofValue _
  · exact Expr.absD_sound h hfs (ks := []) (by simp [KsHold]) e

/-! ## Abstract plan evaluation -/

/-- Exactly `n` columns: missing ones are unknown. -/
def fit (n : Nat) (env : List AVal) : List AVal := (List.range n).map (env.getD · AVal.top)



/-- Sums of integers in `b` keep their sign. -/
def sumBound (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
   b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩

/-- A non-empty sum of integers in `b`: at least `b`'s lower bound where that
is not negative (the other terms are not negative), at most its upper bound
where that is not positive. -/
def sumBoundPos (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some l else none,
   b.hi.bind fun h => if h ≤ 0 then some h else none⟩

/-- A sum of at most `n` integers in `b` (#470): at least `n` times its lower
bound where that is negative, and 0 otherwise (no terms sum to 0); at most
`n` times its upper bound where that is positive, and 0 otherwise. -/
def sumCap (b : Bound) (n : Nat) : Bound :=
  ⟨b.lo.map fun l => min 0 (n * l), b.hi.map fun h => max 0 (n * h)⟩

/-- Admits integers and NULL only: no booleans, strings or lists. -/
def AVal.intsOnly (a : AVal) : Bool := !a.tt && !a.ff && !a.str

/-- Some double, or NULL. -/
def AVal.double : AVal := ⟨true, some Bound.top, false, false, false, none⟩

/-! ### Row counts and float error bounds (#85) -/

/-- An upper bound on the number of rows of a plan. Reads have none of their
own: `sverify` wraps the reads of tables with a `max_rows` precondition in a
`FETCH` of that many rows (`Rel.capReads`), which keeps their rows. -/
def Rel.maxRows : Rel → Option Nat
  | .read _ => none
  | .values _ rows => some rows.length
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r | .semi r _ _ _
  | .window r _ _ _ => r.maxRows
  | .fetch r _ cnt => match cnt, r.maxRows with
    | some k, some n => some (min k n)
    | some k, none => some k
    | none, n => n
  | .cross a b | .join a b .inner _ => a.maxRows.bind fun n => b.maxRows.map (n * ·)
  | .join _ _ .left _ => none
  | .unionAll a b => a.maxRows.bind fun n => b.maxRows.map (n + ·)
  | .aggregate r gs _ => if gs.isEmpty then some 1 else r.maxRows
  | .unnest _ _ => none

theorem length_crossRows (xs ys : Relation) : (crossRows xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [crossRows]
  | cons x xs ih =>
    simp only [crossRows, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-- **Row bounds hold on every order**, `Rel.eval`'s among them. -/
theorem Rel.maxRows_sound_all {cat : Catalog} :
    ∀ {r : Rel} {n : Nat}, r.maxRows = some n → ∀ {out : Relation}, r.OrderAllowed cat out →
      out.length ≤ n
  | .read _, _, h, _, _ => by simp [maxRows] at h
  | .values _ _, _, h, _, ho => by
    simp only [maxRows, Option.some.injEq] at h; rw [ho.length_eq, h]; exact Nat.le_refl _
  | .filter r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .project r _, _, h, _, ⟨i, hi, rfl⟩ | .emit r _, _, h, _, ⟨i, hi, rfl⟩ => by
    simp only [maxRows] at h; simp only [List.length_map]; exact maxRows_sound_all (r := r) h hi
  | .orderBy r _, _, h, _, ⟨i, hi, hp, _⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]; exact maxRows_sound_all (r := r) h hi
  | .distinct r, _, h, _, ⟨i, hi, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans (dedup_length_le _) (maxRows_sound_all (r := r) h hi)
  | .semi r _ _ _, _, h, _, ⟨i, _, hi, _, hp⟩ => by
    simp only [maxRows] at h; rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _) (maxRows_sound_all (r := r) h hi)
  | .window r _ _ _, _, h, _, ⟨i, hi, s, hs, _, hp⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq, windowRows_length, hs.length_eq]
    exact maxRows_sound_all (r := r) h hi
  | .fetch r _ cnt, n, h, _, ⟨i, hi, rfl⟩ => by
    cases cnt with
    | none =>
      simp only [maxRows] at h
      have := maxRows_sound_all (cat := cat) h hi
      simp only [List.length_drop]; omega
    | some k =>
      cases hr : r.maxRows with
      | none =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h; simp only [List.length_take]; exact Nat.min_le_left _ _
      | some m =>
        simp only [maxRows, hr, Option.some.injEq] at h
        subst h
        have := maxRows_sound_all (cat := cat) hr hi
        simp only [List.length_take, List.length_drop]; omega
  | .cross a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, length_crossRows]
    exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .join a b .inner _, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq]
    exact Nat.le_trans (List.length_filter_le _ _)
      (by rw [length_crossRows]; exact Nat.mul_le_mul (maxRows_sound_all ha hx) (maxRows_sound_all hb hy))
  | .join _ _ .left _, _, h, _, _ => by simp [maxRows] at h
  | .unionAll a b, n, h, _, ⟨x, y, hx, hy, hp⟩ => by
    simp only [maxRows, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨na, ha, nb, hb, rfl⟩ := h
    rw [hp.length_eq, List.length_append]
    exact Nat.add_le_add (maxRows_sound_all ha hx) (maxRows_sound_all hb hy)
  | .aggregate r gs _, n, h, _, ⟨i, hi, o, hp, ho⟩ => by
    simp only [maxRows] at h
    rw [hp.length_eq]
    unfold aggOrderAllowed at ho
    split at h
    · rename_i hg
      simp only [Option.some.injEq] at h; subst h
      simp only [hg, ite_true] at ho
      obtain ⟨_, rfl, _⟩ := ho; exact Nat.le_refl _
    · rename_i hg
      simp only [hg, Bool.false_eq_true, ite_false] at ho
      rw [← ho.length_eq]
      exact Nat.le_trans (dedup_length_le _) (by simpa using maxRows_sound_all (r := r) h hi)
  | .unnest _ _, _, h, _, _ => by simp [maxRows] at h

theorem Rel.maxRows_sound {cat : Catalog} {r : Rel} {n : Nat} (h : r.maxRows = some n) :
    (r.eval cat).length ≤ n :=
  Rel.maxRows_sound_all h (r.eval_orderAllowed cat)

/-- Each read of a table with a row cap, as a `FETCH` of at most that many
rows. On tables within their caps it changes nothing (`Rel.capReads_eval`),
and `Rel.maxRows` sees the caps. -/
def Rel.capReads (caps : String → Option Nat) : Rel → Rel
  | .read t => match caps t with
    | some n => .fetch (.read t) 0 (some n)
    | none => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (r.capReads caps) c
  | .project r es => .project (r.capReads caps) es
  | .emit r m => .emit (r.capReads caps) m
  | .cross a b => .cross (a.capReads caps) (b.capReads caps)
  | .join a b ty on => .join (a.capReads caps) (b.capReads caps) ty on
  | .fetch r o c => .fetch (r.capReads caps) o c
  | .unionAll a b => .unionAll (a.capReads caps) (b.capReads caps)
  | .window r p s fns => .window (r.capReads caps) p s fns
  | .semi a b anti on => .semi (a.capReads caps) (b.capReads caps) anti on
  | .orderBy r k => .orderBy (r.capReads caps) k
  | .distinct r => .distinct (r.capReads caps)
  | .aggregate r gs ms => .aggregate (r.capReads caps) gs ms
  | .unnest r c => .unnest (r.capReads caps) c

theorem Rel.capReads_arity (caps : String → Option Nat) (cat : Catalog) :
    ∀ r : Rel, (r.capReads caps).arity cat = r.arity cat
  | .read t => by unfold capReads; split <;> rfl
  | .values _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ => by
    simp only [capReads, arity]; exact capReads_arity caps cat r
  | .project r es => by simp only [capReads, arity, capReads_arity caps cat r]
  | .emit _ _ => rfl
  | .cross a b | .join a b _ _ => by
    simp only [capReads, arity, capReads_arity caps cat a, capReads_arity caps cat b]
  | .unionAll a _ => by simp only [capReads, arity, capReads_arity caps cat a]
  | .window r _ _ _ => by simp only [capReads, arity, capReads_arity caps cat r]
  | .aggregate _ _ _ => rfl
  | .unnest r _ => by simp only [capReads, arity, capReads_arity caps cat r]

/-- **Capping reads changes nothing** on tables within their caps. -/
theorem Rel.capReads_eval {caps : String → Option Nat} {cat : Catalog}
    (h : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ r : Rel, (r.capReads caps).eval cat = r.eval cat
  | .read t => by
    unfold capReads
    split
    · rename_i n hn
      simp only [eval, List.drop_zero]
      exact List.take_of_length_le (h t n hn)
    · rfl
  | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .window r _ _ _ | .unnest r _ | .aggregate r _ _ => by
    simp only [capReads, eval, capReads_eval h r]
  | .cross a b | .unionAll a b | .semi a b _ _ => by
    simp only [capReads, eval, capReads_eval h a, capReads_eval h b]
  | .join a b ty _ => by
    cases ty <;> simp only [capReads, eval, capReads_eval h a, capReads_eval h b,
      capReads_arity caps cat b]

/-- The mean of the doubles `cs`, as `AggFn.avg` computes it. -/
def avgCode (cs : List Int) : Int :=
  FloatCode.lift₂ (· / ·) (floatSum (cs.map .int)) (FloatCode.ofInt cs.length)

/-- The codes a `SUM` (`avg = false`) or an `AVG` of doubles in `b` lies in:
signs are exact (`floatSum_sign`), and with at most `rows` values, finite
bounds and at most `2³²` rows, the result is within the proved tolerance of
the exact one (`floatSum_mem`, `floatAvg_mem`). -/
def floatBound (avg : Bool) (b : Bound) (rows : Option Nat) : Bound :=
  let signed : Bound :=
    ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
     b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩
  match b.lo, b.hi, rows with
  | some cl, some ch, some n =>
    let lo := FloatCode.scaled cl
    let hi := FloatCode.scaled ch
    if n ≤ 2 ^ 32 ∧ lo.natAbs ≤ 2 ^ 1474 ∧ hi.natAbs ≤ 2 ^ 1474 then
      let Bs := max lo.natAbs hi.natAbs
      if avg then
        let t : Int := FloatCode.avgTolScaled n Bs
        signed.meet ⟨some (FloatCode.codeLo (lo - t)), some (FloatCode.codeHi (hi + t))⟩
      else
        let t : Int := FloatCode.sumTolScaled n Bs
        signed.meet ⟨some (FloatCode.codeLo (min lo (n * lo) - t)),
          some (FloatCode.codeHi (max hi (n * hi) + t))⟩
    else signed
  | _, _, _ => signed

theorem floatBound_sound {avg : Bool} {b : Bound} {rows : Option Nat} {cs : List Int}
    (hne : cs ≠ []) (hb : ∀ c ∈ cs, b.Mem c) (hrows : ∀ n, rows = some n → cs.length ≤ n) :
    (floatBound avg b rows).Mem (if avg then avgCode cs else floatSum (cs.map .int)) := by
  obtain ⟨blo, bhi⟩ := b
  have hsign := floatSum_sign hne
  have hsigned : (Bound.mk (blo.bind fun l => if 0 ≤ l then some 0 else none)
      (bhi.bind fun h => if h ≤ 0 then some 0 else none)).Mem
      (if avg then avgCode cs else floatSum (cs.map .int)) := by
    constructor
    · intro l hl
      simp only [Option.bind_eq_some_iff] at hl
      obtain ⟨l', hl', h⟩ := hl
      split at h
      · rename_i h0
        cases h
        have := (hsign.1 fun c hc => Int.le_trans h0 ((hb c hc).1 l' hl'))
        cases avg <;> simp only [Bool.false_eq_true, ↓reduceIte, avgCode] <;> omega
      · simp at h
    · intro u hu
      simp only [Option.bind_eq_some_iff] at hu
      obtain ⟨u', hu', h⟩ := hu
      split at h
      · rename_i h0
        cases h
        have := (hsign.2 fun c hc => Int.le_trans ((hb c hc).2 u' hu') h0)
        cases avg <;> simp only [Bool.false_eq_true, ↓reduceIte, avgCode] <;> omega
      · simp at h
  rcases blo with _ | cl
  · exact hsigned
  rcases bhi with _ | ch
  · exact hsigned
  rcases rows with _ | n
  · exact hsigned
  have hlen := hrows n rfl
  have hsc : ∀ c ∈ cs, FloatCode.scaled cl ≤ FloatCode.scaled c ∧
      FloatCode.scaled c ≤ FloatCode.scaled ch := fun c hc =>
    ⟨FloatCode.scaled_mono ((hb c hc).1 cl rfl), FloatCode.scaled_mono ((hb c hc).2 ch rfl)⟩
  simp only [floatBound]
  split
  · rename_i hok
    obtain ⟨h32, hlo, hhi⟩ := hok
    cases avg
    · simp only [Bool.false_eq_true, ↓reduceIte] at hsigned ⊢
      obtain ⟨l, u⟩ := floatSum_mem hne hlen h32 hlo hhi hsc
      refine Bound.mem_meet hsigned ⟨?_, ?_⟩
      · intro x hx; cases hx; exact FloatCode.codeLo_le l
      · intro x hx; cases hx; exact FloatCode.le_codeHi u
    · simp only [↓reduceIte] at hsigned ⊢
      obtain ⟨l, u⟩ := floatAvg_mem hne hlen h32 hlo hhi hsc
      refine Bound.mem_meet hsigned ⟨?_, ?_⟩
      · intro x hx; cases hx; exact FloatCode.codeLo_le l
      · intro x hx; cases hx; exact FloatCode.le_codeHi u
  · exact hsigned

/-- A measure over rows described by `env` and `fs`: a count is a natural
number, a sum of integers keeps their sign, `MIN`, `MAX` and an integer
`AVG` are within the argument's values, and the other measures are doubles. All but
`COUNT` may be NULL, unless a group has a value (`grouped`, #372). -/
def Measure.abs (env : List AVal) (fs : List Fact) (m : Measure) (grouped : Bool := false)
    (rows : Option Nat := none) : AVal :=
  let a := m.arg.absD env fs
  -- A group has a row (`grouped`), so a measure of a never-NULL argument
  -- without a filter has a value: `COUNT(*)` per group is at least 1.
  let valued := grouped && m.filter.isNone && !a.null
  match m.fn with
  | .count => ⟨false, some (Bound.ge (if valued then 1 else 0)), false, false, false, none⟩
  -- A sum is over at least one input (none: NULL), so with integer inputs
  -- it is at least the smallest one, if that is not negative.
  -- With at most `rows` rows, at most `rows` times the largest value (#470).
  | .sum => ⟨!valued, some (match a.int with
      | some b => (if a.intsOnly then sumBoundPos b else sumBound b).meet
          (match rows with
            | some n => sumCap b n
            | none => Bound.top)
      | none => Bound.top), false, false, false, none⟩
  -- Doubles round: within the proved error bound of the exact sum or mean
  -- when the values are finite and there are at most `rows` of them (#85).
  | .fsum => ⟨!valued,
      some (if a.intsOnly then floatBound false (a.int.getD Bound.top) rows else Bound.top),
      false, false, false, none⟩
  | .avg => ⟨!valued,
      some (if a.intsOnly then floatBound true (a.int.getD Bound.top) rows else Bound.top),
      false, false, false, none⟩
  -- Between the smallest and the largest value (`AggFn.iavg`, #237).
  | .iavg =>
    ⟨!valued, some (if a.intsOnly then a.int.getD Bound.top else Bound.top), false, false, false, none⟩
  | .cov _ | .corr => AVal.double
  -- Some double that is not negative (NaN is above every number), or NULL.
  | .var _ _ => ⟨true, some ⟨some 0, none⟩, false, false, false, none⟩
  | .bit _ => ⟨true, some Bound.top, false, false, false, none⟩
  | .min | .max => if valued then a else a.nullable
  -- One of the values, in the measure's order (#55).
  | .pick _ => a.nullable
  -- A string, or NULL without values.
  | .concat _ => ⟨true, none, false, false, true, none⟩
  -- One of the values (#53).
  | .quantile false _ _ | .mode => a.nullable
  -- A double between two of the values: within the argument's interval.
  | .quantile true _ _ => ⟨true, a.int, false, false, false, none⟩
  | .collect => AVal.top
  -- A black box's laws over values; its `empty` value without (#325).
  | .bbox n => BlackBox.aggAbs n valued

/-- `ROW_NUMBER` and the ranks are positive integers, at most `Text.rowCap`
by the size hypothesis for relations (`Rel.Small`) when `sz` says to use
it; `LAG`/`LEAD` read a
value of the same column of another input row, or give the default;
`PERCENT_RANK` and `CUME_DIST` are doubles. An aggregate over a frame is
described like one over a group (`Measure.abs`); `FIRST_VALUE` and friends
may be anything. -/
def WinFn.abs (sz : Bool) (env : List AVal) : WinFn → AVal
  | .rowNumber | .rank _ | .denseRank _ | .ntile _ =>
    ⟨false, some ⟨some 1, if sz then some Text.rowCap else none⟩, false, false, false, none⟩
  | .percentRank _ | .cumeDist _ => ⟨false, some Bound.top, false, false, false, none⟩
  -- An aggregate over a frame, rows of the input: a sum of non-negative
  -- integers is not negative, `MIN` and `MAX` are among the inputs (#229).
  | .agg m _ _ => m.abs env []
  | .firstValue _ _ _ | .lastValue _ _ _ | .nthValue _ _ _ _ => AVal.top
  | .lag c _ d | .lead c _ d => (env.getD c AVal.top).join (AVal.ofValue d)

/-- `ratio` facts for a `SUM` and a `COUNT` of the same values, which a
decimal `AVG` divides (`Parse.decimalAvgs`, #237): the sum is of as many
integers as the count, each within the bound `env` and `fs` give the values. -/
def ratioFacts (g : Nat) (env : List AVal) (fs : List Fact) (ms : List Measure) : List Fact :=
  (List.range ms.length).flatMap fun i => (List.range ms.length).flatMap fun j =>
    match ms[i]?, ms[j]? with
    | some mi, some mj =>
      let a := mi.arg.absD env fs
      if mi.fn = .sum ∧ mj.fn = .count ∧ mj.arg = mi.arg ∧ mj.filter = mi.filter ∧
          mj.distinct = mi.distinct ∧ a.intsOnly = true then
        match a.int with
        | some b => [.ratio (g + i) (g + j) b]
        | none => []
      else []
    | _, _ => []


mutual
/-- Abstract evaluation. `A t` describes the columns of table `t`; `F t` holds
facts about its rows. Computed columns use the facts of their input. -/
def Rel.aeval (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool := false) : Rel → List AVal
  | .read t => useFacts (F t) (fit (cat t).arity (A t))
  | .values n _ => List.replicate n AVal.top
  | .filter r c => useFacts (r.facts cat F T ++ c.factsOf) (c.refine (r.aeval cat A F T sz))
  -- The input's description is bound once: inside the lambda it would be
  -- recomputed per expression, exponentially in the depth of projections (#825).
  | .project r es =>
      let env := r.aeval cat A F T sz
      let fs := r.facts cat F T ++ r.ratioPart cat A F T sz
      env ++ es.map (·.absF env fs)
  | .emit r m => m.map ((r.aeval cat A F T sz).getD · AVal.top)
  | .cross a b => a.aeval cat A F T sz ++ b.aeval cat A F T sz
  | .join a b .inner on => on.refine (a.aeval cat A F T sz ++ b.aeval cat A F T sz)
  | .join a b .left _ => a.aeval cat A F T sz ++ (b.aeval cat A F T sz).map AVal.nullable
  | .fetch r _ _ => r.aeval cat A F T sz
  | .unionAll a b => List.zipWith AVal.join (a.aeval cat A F T sz) (b.aeval cat A F T sz)
  | .window r _ _ fns =>
      let env := r.aeval cat A F T sz
      env ++ fns.map (WinFn.abs sz env)
  | .semi a _ _ _ => a.aeval cat A F T sz
  | .orderBy r _ | .distinct r => r.aeval cat A F T sz
  | .unnest r c => (r.aeval cat A F T sz).set c AVal.top
  | .aggregate r gs ms =>
      let env := r.aeval cat A F T sz
      let fs := r.facts cat F T
      let n := r.maxRows
      gs.map (·.absD env fs) ++ ms.map fun m => Measure.abs env fs m (!gs.isEmpty) n

/-- Facts about an aggregate's rows that need its input's description: the
`ratio` facts of its sums and counts, for the decimal `AVG`s a projection
divides (#237). -/
def Rel.ratioPart (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) : Rel → List Fact
  | .aggregate r gs ms => ratioFacts gs.length (r.aeval cat A F T sz) (r.facts cat F T) ms
  | _ => []
end

/-! ### One pass (#903)

`Rel.aeval` asks its input for its facts at every filter and projection, and
`Rel.facts` and `Rel.arity` walk the input again each time: a plan of depth
`d` is walked `O(d)` times per node. `Rel.lane` computes the arity, facts,
description, `ratio` facts and row bound of every subplan once, bottom-up,
from its inputs' lanes. `Rel.lane_eq` proves each field is the analysis it
replaces, and the `@[csimp]` lemmas make compiled code run the lane wherever
it calls `Rel.aeval` or `Rel.ratioPart`. Proofs keep reasoning about the
definitions above. -/

/-- The analyses of one subplan, computed together. -/
structure Rel.Lane where
  arity : Nat
  facts : List Fact
  env : List AVal
  ratio : List Fact
  rows : Option Nat
  deriving Inhabited

/-- One node's lane from its inputs' lanes (`l`, `l₂`; unused ones are ignored). -/
def Rel.laneStep (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool) : Rel → Rel.Lane → Rel.Lane → Rel.Lane
  | .read t, _, _ => ⟨(cat t).arity, F t, useFacts (F t) (fit (cat t).arity (A t)), [], none⟩
  | .values n rows, _, _ => ⟨n, [], List.replicate n AVal.top, [], some rows.length⟩
  | .filter _ c, l, _ =>
      ⟨l.arity, l.facts ++ c.factsOf, useFacts (l.facts ++ c.factsOf) (c.refine l.env), [], l.rows⟩
  | .project _ es, l, _ =>
      ⟨l.arity + es.length,
        (l.facts.filter (·.inRange l.arity)).flatMap (Fact.rename (copyCols l.arity es)) ++
          linFacts l.arity l.arity es,
        l.env ++ es.map (·.absF l.env (l.facts ++ l.ratio)), [], l.rows⟩
  | .emit _ m, l, _ =>
      ⟨m.length, l.facts.flatMap (Fact.rename (positions m)), m.map (l.env.getD · AVal.top), [],
        l.rows⟩
  | .cross _ _, la, lb =>
      ⟨la.arity + lb.arity, la.facts.filter (·.inRange la.arity) ++ lb.facts.map (·.shift la.arity),
        la.env ++ lb.env, [], la.rows.bind fun n => lb.rows.map (n * ·)⟩
  | .join _ _ .inner on, la, lb =>
      ⟨la.arity + lb.arity,
        la.facts.filter (·.inRange la.arity) ++ lb.facts.map (·.shift la.arity) ++ on.factsOf,
        on.refine (la.env ++ lb.env), [], la.rows.bind fun n => lb.rows.map (n * ·)⟩
  | .join _ _ .left on, la, lb =>
      ⟨la.arity + lb.arity,
        la.facts.filter (·.inRange la.arity) ++
          (lb.facts.filter Fact.intsOnly).map (·.shift la.arity) ++
          on.factsOf.filter (·.rightOf la.arity),
        la.env ++ lb.env.map AVal.nullable, [], none⟩
  | .fetch _ _ cnt, l, _ =>
      ⟨l.arity, l.facts, l.env, [], match cnt, l.rows with
        | some k, some n => some (min k n)
        | some k, none => some k
        | none, n => n⟩
  | .unionAll _ _, la, lb =>
      ⟨la.arity, la.facts.filter (lb.facts.contains ·), List.zipWith AVal.join la.env lb.env, [],
        la.rows.bind fun n => lb.rows.map (n + ·)⟩
  | .window r part sort fns, l, _ =>
      ⟨l.arity + fns.length,
        l.facts.filter (·.inRange l.arity) ++ winFacts part sort (T r part sort) l.arity fns,
        l.env ++ fns.map (WinFn.abs sz l.env), [], l.rows⟩
  | .semi _ _ _ _, l, _ =>
      ⟨l.arity, l.facts, l.env, [], l.rows⟩
  | .orderBy _ _, l, _ | .distinct _, l, _ =>
      ⟨l.arity, l.facts, l.env, [], l.rows⟩
  | .aggregate _ gs ms, l, _ =>
      ⟨gs.length + ms.length, aggFacts gs.length ms,
        gs.map (·.absD l.env l.facts) ++ ms.map fun m => Measure.abs l.env l.facts m (!gs.isEmpty) l.rows,
        ratioFacts gs.length l.env l.facts ms, if gs.isEmpty then some 1 else l.rows⟩
  | .unnest _ c, l, _ =>
      ⟨l.arity, [], l.env.set c AVal.top, [], none⟩


/-- The analyses of every subplan in one bottom-up pass. -/
def Rel.lane (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (sz : Bool) : Rel → Rel.Lane
  | r@(.filter a _) | r@(.project a _) | r@(.emit a _) | r@(.fetch a _ _) | r@(.window a _ _ _)
  | r@(.semi a _ _ _) | r@(.orderBy a _) | r@(.distinct a) | r@(.aggregate a _ _) | r@(.unnest a _) =>
      r.laneStep cat A F T sz (a.lane cat A F T sz) default
  | r@(.cross a b) | r@(.join a b _ _) | r@(.unionAll a b) =>
      r.laneStep cat A F T sz (a.lane cat A F T sz) (b.lane cat A F T sz)
  | r@(.read _) | r@(.values _ _) => r.laneStep cat A F T sz default default

/-- **The lane is the analyses**, field by field. -/
theorem Rel.lane_eq (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool) (r : Rel) :
    r.lane cat A F T sz = ⟨r.arity cat, r.facts cat F T, r.aeval cat A F T sz,
      r.ratioPart cat A F T sz, r.maxRows⟩ := by
  induction r with
  | join a b ty on iha ihb =>
    cases ty <;> simp only [Rel.lane, Rel.laneStep, iha, ihb, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart,
      Rel.maxRows]
  | fetch r _ cnt ih =>
    cases cnt <;> simp only [Rel.lane, Rel.laneStep, ih, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart,
      Rel.maxRows]
  | _ => simp_all only [Rel.lane, Rel.laneStep, Rel.arity, Rel.facts, Rel.aeval, Rel.ratioPart, Rel.maxRows]

/-- `Rel.aeval` by the lane. -/
def Rel.aevalLane (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) (r : Rel) : List AVal :=
  (r.lane cat A F T sz).env

/-- `Rel.ratioPart` by the lane. -/
def Rel.ratioPartLane (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (sz : Bool := false) (r : Rel) : List Fact :=
  (r.lane cat A F T sz).ratio

@[csimp] theorem Rel.aeval_csimp : @Rel.aeval = @Rel.aevalLane := by
  funext cat A F T sz r; simp only [Rel.aevalLane, Rel.lane_eq]

@[csimp] theorem Rel.ratioPart_csimp : @Rel.ratioPart = @Rel.ratioPartLane := by
  funext cat A F T sz r; simp only [Rel.ratioPartLane, Rel.lane_eq]

theorem Rel.aeval_length {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
    {T : WindowKeys} {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (r.aeval cat A F T sz).length = r.arity cat
  | .read _, _ => by simp [aeval, fit, arity, useFacts_length]
  | .values _ _, _ => by simp [aeval, arity]
  | .filter r _, h => by
      simp [aeval, arity, useFacts_length, Expr.refine_length, aeval_length (r := r) h.1]
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

theorem EnvMem.mapF {env : List AVal} {fs : List Fact} {row : Row} (h : EnvMem env row)
    (hfs : FactsHold fs row) (es : List Expr) :
    EnvMem (es.map (·.absF env fs)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.absF_sound h hfs]

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

theorem sumBoundPos_sound {b : Bound} {v : Value} {vs : List Value}
    (h : ∀ w ∈ v :: vs, ∃ i, w = .int i ∧ b.Mem i) : (sumBoundPos b).Mem (intSum (v :: vs)) := by
  obtain ⟨i, rfl, hi⟩ := h v (by simp)
  have hrest : ∀ j, .int j ∈ vs → b.Mem j := fun j hj => by
    obtain ⟨j', hj', hm⟩ := h (.int j) (by simp [hj]); cases hj'; exact hm
  simp only [intSum]
  constructor
  · intro l hl
    cases hb : b.lo with
    | none => simp [sumBoundPos, hb] at hl
    | some l₀ =>
      simp only [sumBoundPos, hb, Option.bind_some] at hl
      split at hl
      · simp only [Option.some.injEq] at hl; subst hl
        have := hi.1 l₀ hb
        have := intSum_nonneg (vs := vs) fun j hj => by have := (hrest j hj).1 l₀ hb; omega
        omega
      · cases hl
  · intro u hu
    cases hb : b.hi with
    | none => simp [sumBoundPos, hb] at hu
    | some h₀ =>
      simp only [sumBoundPos, hb, Option.bind_some] at hu
      split at hu
      · simp only [Option.some.injEq] at hu; subst hu
        have := hi.2 h₀ hb
        have := intSum_nonpos (vs := vs) fun j hj => by have := (hrest j hj).2 h₀ hb; omega
        omega
      · cases hu

theorem sumCap_sound {b : Bound} :
    ∀ {vs : List Value} {n : Nat}, (∀ i, .int i ∈ vs → b.Mem i) → vs.length ≤ n →
      (sumCap b n).Mem (intSum vs)
  | [], _, _, _ => by
    constructor
    · intro l hl; simp only [sumCap, Option.map_eq_some_iff] at hl
      obtain ⟨_, _, rfl⟩ := hl; simp [intSum]; omega
    · intro u hu; simp only [sumCap, Option.map_eq_some_iff] at hu
      obtain ⟨_, _, rfl⟩ := hu; simp [intSum]; omega
  | v :: vs, n, h, hlen => by
    have hrest : ∀ i, .int i ∈ vs → b.Mem i := fun i hi => h i (List.mem_cons_of_mem _ hi)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hlen; omega⟩
    have hlen' : vs.length ≤ n' := by simp at hlen; omega
    have hlen'' : vs.length ≤ n' + 1 := by omega
    have ih := sumCap_sound hrest hlen'
    have ih' := sumCap_sound hrest hlen''
    have hcast : ((n' + 1 : Nat) : Int) = (n' : Int) + 1 := by simp
    constructor
    · intro l hl
      simp only [sumCap, Option.map_eq_some_iff] at hl
      obtain ⟨l₀, hb, rfl⟩ := hl
      have hi := ih.1 (min 0 ((n' : Int) * l₀)) (by simp [sumCap, hb])
      have hi' := ih'.1 (min 0 (((n' + 1 : Nat) : Int) * l₀)) (by simp [sumCap, hb])
      rw [hcast, Int.add_mul, Int.one_mul]
      rw [hcast, Int.add_mul, Int.one_mul] at hi'
      have hs1 : 0 ≤ l₀ → 0 ≤ (n' : Int) * l₀ := fun h0 => Int.mul_nonneg (by omega) h0
      have hs2 : l₀ ≤ 0 → (n' : Int) * l₀ ≤ 0 := fun h0 =>
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h0
      cases v with
      | int i =>
        have := (h i (by simp)).1 l₀ hb
        simp only [intSum]; omega
      | _ => simp only [intSum]; omega
    · intro u hu
      simp only [sumCap, Option.map_eq_some_iff] at hu
      obtain ⟨h₀, hb, rfl⟩ := hu
      have hi := ih.2 (max 0 ((n' : Int) * h₀)) (by simp [sumCap, hb])
      have hi' := ih'.2 (max 0 (((n' + 1 : Nat) : Int) * h₀)) (by simp [sumCap, hb])
      rw [hcast, Int.add_mul, Int.one_mul]
      rw [hcast, Int.add_mul, Int.one_mul] at hi'
      have hs1 : 0 ≤ h₀ → 0 ≤ (n' : Int) * h₀ := fun h0 => Int.mul_nonneg (by omega) h0
      have hs2 : h₀ ≤ 0 → (n' : Int) * h₀ ≤ 0 := fun h0 =>
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h0
      cases v with
      | int i =>
        have := (h i (by simp)).2 h₀ hb
        simp only [intSum]; omega
      | _ => simp only [intSum]; omega

theorem AVal.intsOnly_mem {a : AVal} (ho : a.intsOnly = true) {v : Value} (hm : a.Mem v)
    (hn : v ≠ .null) : ∃ i b, v = .int i ∧ a.int = some b ∧ b.Mem i := by
  simp only [AVal.intsOnly, Bool.and_eq_true, Bool.not_eq_true'] at ho
  obtain ⟨⟨htt, hff⟩, hstr⟩ := ho
  match v, hm with
  | .null, _ => exact absurd rfl hn
  | .int i, ⟨b, hb, hi⟩ => exact ⟨i, b, rfl, hb, hi⟩
  | .bool true, hm | .bool false, hm | .str _, hm => simp_all [AVal.Mem]
  | .list _, hm => simp_all [AVal.Mem]

theorem Bound.mem_between {b : Bound} {l h r : Int} (hl : b.Mem l) (hh : b.Mem h) (hlr : l ≤ r)
    (hrh : r ≤ h) : b.Mem r :=
  ⟨fun x hx => Int.le_trans (hl.1 x hx) hlr, fun x hx => Int.le_trans hrh (hh.2 x hx)⟩

/-- A measure without a filter, of an argument that is never NULL, over a
group with a row, has an input. -/
theorem Measure.inputs_ne_nil {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) {m : Measure} (hg : grp ≠ [])
    (hf : m.filter = none) (hnn : (m.arg.absD env fs).null = false) : m.inputs grp ≠ [] := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil grp hg
  have hv := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) m.arg
  have : m.arg.eval y ≠ .null := fun h0 => by rw [h0] at hv; simp_all [AVal.Mem]
  simp only [Measure.inputs, Measure.kept, hf]
  have hm : m.arg.eval y ∈ (grp.map m.arg.eval).filter (· != .null) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨y, hy, rfl⟩, by simpa using this⟩
  split
  · exact List.ne_nil_of_mem (mem_dedup.mpr hm)
  · exact List.ne_nil_of_mem hm

theorem Measure.abs_sound {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (m : Measure) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    (m.abs env fs grouped rows).Mem (m.eval grp) := by
  have hin : ∀ v ∈ m.inputs grp, (m.arg.absD env fs).Mem v := by
    intro v hv
    obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
    exact Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) m.arg
  have inputs_ne_null : ∀ {v}, v ∈ m.inputs grp → v ≠ .null := fun hv => (Measure.mem_inputs hv).1
  -- A group with a row has a value, when the argument is never NULL and nothing is filtered.
  have valued_ne_nil : (grouped && m.filter.isNone && !(m.arg.absD env fs).null) = true →
      m.inputs grp ≠ [] := fun hv => by
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hv
    exact Measure.inputs_ne_nil hall (hne hv.1.1) hv.1.2 hv.2
  have novalue : m.inputs grp = [] →
      (!(grouped && m.filter.isNone && !(m.arg.absD env fs).null)) = true := fun hvs => by
    cases hv : (grouped && m.filter.isNone && !(m.arg.absD env fs).null)
    · rfl
    · exact absurd hvs (valued_ne_nil hv)
  unfold Measure.abs Measure.eval
  cases hf : m.fn <;> dsimp only
  case collect => exact AVal.mem_top _
  case bbox n => exact BlackBox.aggAbs_mem valued_ne_nil
  case concat sep =>
    cases m.inputs (List.mergeSort grp (sortLe m.sort)) <;> simp [AggFn.apply, AVal.Mem]
  case count =>
    refine ⟨_, rfl, fun l hl => ?_, fun u hu => by simp [Bound.ge] at hu⟩
    simp only [Bound.ge, Option.some.injEq] at hl
    subst hl
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hc
      obtain ⟨⟨hg, hf⟩, hnn⟩ := hc
      have hne' := Measure.inputs_ne_nil hall (hne hg) hf hnn
      cases h : m.inputs grp with
      | nil => exact absurd h hne'
      | cons _ _ => simp only [List.length_cons]; omega
    · omega
  case sum =>
    cases hvs : m.inputs grp with
    | nil =>
      simp only [AggFn.apply, AVal.Mem]
      cases hg : grouped <;> cases hfi : m.filter <;> cases hn : (m.arg.absD env fs).null <;>
        simp
      exact Measure.inputs_ne_nil hall (hne hg) hfi hn hvs
    | cons v vs =>
      simp only [AggFn.apply]
      refine ⟨_, rfl, ?_⟩
      cases ha : (m.arg.absD env fs).int with
      | none => exact Bound.mem_top _
      | some b =>
        simp only
        refine Bound.mem_meet ?_ ?cap
        case cap =>
          cases rows with
          | none => exact Bound.mem_top _
          | some n =>
            refine sumCap_sound (fun i hi => ?_) ?_
            · obtain ⟨b', hb', hm⟩ := hin (.int i) (hvs ▸ hi)
              rw [ha] at hb'; cases hb'; exact hm
            · rw [← hvs]
              exact Nat.le_trans (Measure.inputs_length_le m grp) (hrows n rfl)
        split
        · -- Every input is an integer in `b`.
          rename_i honly
          simp only [AVal.intsOnly, Bool.and_eq_true, Bool.not_eq_true'] at honly
          refine sumBoundPos_sound fun w hw => ?_
          have hm := hin w (hvs ▸ hw)
          have hnn : w ≠ .null := by
            have : w ∈ m.inputs grp := hvs ▸ hw
            simp only [Measure.inputs] at this
            split at this <;> simp_all [mem_dedup]
          rcases AVal.mem_cases hm with ⟨rfl, _⟩ | ⟨i, b', rfl, hb', hi⟩ | ⟨rfl, ht⟩ | ⟨rfl, hf'⟩ |
              ⟨_, rfl, hs⟩ | ⟨_, rfl, ht, _, _⟩
          · exact absurd rfl hnn
          · rw [ha] at hb'; cases hb'; exact ⟨i, rfl, hi⟩
          all_goals simp_all
        · refine sumBound_sound fun i hi => ?_
          have := hin (.int i) (hvs ▸ hi)
          obtain ⟨b', hb', hm⟩ := this
          rw [ha] at hb'; cases hb'; exact hm
  case cov sample =>
    simp only [AggFn.apply]
    cases m.inputs grp with
    | nil => rfl
    | cons v vs => simp only [covOf]; split <;> first | rfl | exact ⟨_, rfl, Bound.mem_top _⟩
  case corr =>
    cases m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [AggFn.apply, corrOf]; split <;> first | rfl | exact ⟨_, rfl, Bound.mem_top _⟩
  case bit =>
    cases m.inputs grp <;> simp only [AggFn.apply] <;> first | rfl | exact ⟨_, rfl, Bound.mem_top _⟩
  case fsum =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem]; exact novalue hvs
    | cons v vs =>
      refine ⟨_, rfl, ?_⟩
      split
      · rename_i honly
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .int i ∧ (m.arg.absD env fs).int = some b ∧ b.Mem i :=
          fun w hw => AVal.intsOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        have hcs : v :: vs = (intsOf (v :: vs)).map .int := ints_map_intsOf fun w hw => by
          obtain ⟨i, _, rfl, _⟩ := hint w hw; exact ⟨i, rfl⟩
        have hne' : intsOf (v :: vs) ≠ [] := by
          intro h; rw [h] at hcs; simp at hcs
        have hb : ∀ c ∈ intsOf (v :: vs), ((m.arg.absD env fs).int.getD Bound.top).Mem c := by
          intro c hc
          obtain ⟨_, b, he, hb, hm⟩ := hint _ (mem_intsOf.1 hc)
          cases he; rw [hb]; exact hm
        have hlen : ∀ n, rows = some n → (intsOf (v :: vs)).length ≤ n := by
          intro n hn
          have := hrows n hn
          have h1 : (intsOf (v :: vs)).length = (v :: vs).length := by
            conv => rhs; rw [hcs]
            simp
          have h2 : (m.inputs grp).length ≤ grp.length := Measure.inputs_length_le m grp
          rw [hvs] at h2; omega
        have key := floatBound_sound (avg := false) hne' hb hlen
        have e : floatSum (v :: vs) = floatSum ((intsOf (v :: vs)).map .int) := congrArg floatSum hcs
        rw [e]; simpa using key
      · exact Bound.mem_top _
  case avg =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem]; exact novalue hvs
    | cons v vs =>
      refine ⟨_, rfl, ?_⟩
      split
      · rename_i honly
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .int i ∧ (m.arg.absD env fs).int = some b ∧ b.Mem i :=
          fun w hw => AVal.intsOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        have hcs : v :: vs = (intsOf (v :: vs)).map .int := ints_map_intsOf fun w hw => by
          obtain ⟨i, _, rfl, _⟩ := hint w hw; exact ⟨i, rfl⟩
        have hne' : intsOf (v :: vs) ≠ [] := by
          intro h; rw [h] at hcs; simp at hcs
        have hb : ∀ c ∈ intsOf (v :: vs), ((m.arg.absD env fs).int.getD Bound.top).Mem c := by
          intro c hc
          obtain ⟨_, b, he, hb, hm⟩ := hint _ (mem_intsOf.1 hc)
          cases he; rw [hb]; exact hm
        have hlen : ∀ n, rows = some n → (intsOf (v :: vs)).length ≤ n := by
          intro n hn
          have := hrows n hn
          have h1 : (intsOf (v :: vs)).length = (v :: vs).length := by
            conv => rhs; rw [hcs]
            simp
          have h2 : (m.inputs grp).length ≤ grp.length := Measure.inputs_length_le m grp
          rw [hvs] at h2; omega
        have key := floatBound_sound (avg := true) hne' hb hlen
        have e := congrArg (fun l => FloatCode.lift₂ (· / ·) (floatSum l) (FloatCode.ofInt l.length)) hcs
        simp only [List.length_map] at e
        rw [e]; simpa [avgCode] using key
      · exact Bound.mem_top _
  case iavg =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem]; exact novalue hvs
    | cons v vs =>
      split
      · rename_i honly
        -- Every value is an integer in the argument's interval `b`.
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .int i ∧ (m.arg.absD env fs).int = some b ∧ b.Mem i :=
          fun w hw => AVal.intsOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        obtain ⟨i₀, b, rfl, hb, -⟩ := hint v (List.mem_cons_self ..)
        obtain ⟨r, hr, ⟨l, hl, hlr⟩, ⟨h, hh, hrh⟩⟩ := AggFn.apply_iavg_between
          (vs := .int i₀ :: vs) (List.ne_nil_of_mem (mem_intsOf.2 (List.mem_cons_self ..)))
        rw [hr]
        have memb : ∀ c ∈ intsOf (.int i₀ :: vs), b.Mem c := fun c hc => by
          obtain ⟨_, b', he, hb', hm⟩ := hint _ (mem_intsOf.1 hc)
          cases he; rw [hb] at hb'; cases hb'; exact hm
        refine ⟨b, by simp [hb], Bound.mem_between (memb l hl) (memb h hh) hlr hrh⟩
      · exact ⟨_, rfl, Bound.mem_top _⟩
  case var sample sqrt =>
    cases m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [AggFn.apply, varOf]
      split
      · rfl
      · exact ⟨_, rfl, fun l hl => by cases hl; omega, fun h hh => by cases hh⟩
  case min | max =>
    split
    · -- A group with a value: one of the values.
      rename_i hv
      cases hvs : m.inputs grp with
      | nil => exact absurd hvs (valued_ne_nil hv)
      | cons v vs =>
        simp only [AggFn.apply]
        exact hin _ (hvs ▸ pickFold_mem _ _ _)
    · have hmm := AggFn.apply_minmax (f := m.fn) (by simp [hf]) (vs := m.inputs grp)
      rw [hf] at hmm
      rcases hmm with h | h
      · rw [h]; rfl
      · exact AVal.mem_nullable (hin _ h)
  case pick last =>
    -- The sorted rows are the group's rows.
    have hin' : ∀ v ∈ m.inputs (grp.mergeSort (sortLe m.sort)), (m.arg.absD env fs).Mem v := by
      intro v hv
      obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
      have hy' := (List.mergeSort_perm grp (sortLe m.sort)).mem_iff.mp hy
      exact Expr.absD_sound (hall y hy').1 (hall y hy').2 (ks := []) (by simp [KsHold]) m.arg
    rcases AggFn.apply_pick last (m.inputs (grp.mergeSort (sortLe m.sort))) with h | h
    · rw [h]; rfl
    · exact AVal.mem_nullable (hin' _ h)
  case mode =>
    have hin' : ∀ v ∈ m.inputs (grp.mergeSort (sortLe m.sort)), (m.arg.absD env fs).Mem v := by
      intro v hv
      obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
      have hy' := (List.mergeSort_perm grp (sortLe m.sort)).mem_iff.mp hy
      exact Expr.absD_sound (hall y hy').1 (hall y hy').2 (ks := []) (by simp [KsHold]) m.arg
    rcases AggFn.apply_mode (m.inputs (grp.mergeSort (sortLe m.sort))) with h | h
    · rw [h]; rfl
    · exact AVal.mem_nullable (hin' _ h)
  case quantile cont num scale =>
    cases cont
    · rcases AggFn.apply_disc num scale (m.inputs grp) with h | h
      · rw [h]; rfl
      · exact AVal.mem_nullable (hin _ h)
    · rcases AggFn.apply_cont num scale (m.inputs grp) with h | ⟨c, l, h, hc, hl, hh, hb⟩
      · rw [h]; rfl
      · rw [hc]
        obtain ⟨b, hb1, hlb⟩ := hin _ hl
        obtain ⟨b', hb2, hhb⟩ := hin _ hh
        rw [hb1] at hb2; cases hb2
        refine ⟨b, hb1, ?_⟩
        rcases hb with rfl | rfl | ⟨h1, h2⟩
        · exact hlb
        · exact hhb
        · exact Bound.mem_between hlb hhb h1 h2

theorem intSum_bounds {b : Bound} :
    ∀ {vs : List Value}, (∀ w ∈ vs, ∃ i, w = .int i ∧ b.Mem i) →
      (∀ l, b.lo = some l → vs.length * l ≤ intSum vs) ∧
        (∀ h, b.hi = some h → intSum vs ≤ vs.length * h)
  | [], _ => by simp [intSum]
  | w :: ws, hall => by
    obtain ⟨i, rfl, hi⟩ := hall w (List.mem_cons_self ..)
    have ih := intSum_bounds (vs := ws) fun w hw => hall w (List.mem_cons_of_mem _ hw)
    simp only [intSum, List.length_cons]
    constructor
    · intro l hl
      have := hi.1 l hl; have := ih.1 l hl
      rw [Int.natCast_add, Int.add_mul]; omega
    · intro h hh
      have := hi.2 h hh; have := ih.2 h hh
      rw [Int.natCast_add, Int.add_mul]; omega

/-- The `ratio` facts hold on a group's row. -/
theorem ratioFacts_sound {g : Nat} {env : List AVal} {fs : List Fact} {ms : List Measure}
    {grp : Relation} {k : Row} (hk : k.length = g)
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) :
    FactsHold (ratioFacts g env fs ms) (k ++ ms.map (·.eval grp)) := by
  intro f hf
  simp only [ratioFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  have col : ∀ i (m : Measure), ms[i]? = some m →
      (k ++ ms.map (·.eval grp)).getD (g + i) .null = m.eval grp := fun i m h => by
    rw [← hk, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  split at hf
  · rename_i mi mj hmi hmj
    split at hf
    · rename_i hc
      obtain ⟨hsum, hcount, harg, hfil, hdis, honly⟩ := hc
      split at hf
      · rename_i b hb
        simp only [List.mem_singleton] at hf; subst hf
        intro x n hx hn
        rw [col i mi hmi, Measure.eval_eq (by rw [hsum]; rfl), hsum] at hx
        rw [col j mj hmj, Measure.eval_eq (by rw [hcount]; rfl), hcount] at hn
        have hsame : mj.inputs grp = mi.inputs grp := by
          simp only [Measure.inputs, Measure.kept, harg, hfil, hdis]
        rw [hsame] at hn
        cases hvs : mi.inputs grp with
        | nil => rw [hvs] at hx; simp [AggFn.apply] at hx
        | cons v vs =>
          rw [hvs] at hx hn
          simp only [AggFn.apply, Value.int.injEq] at hx hn
          subst hx hn
          have hint : ∀ w ∈ v :: vs, ∃ i, w = .int i ∧ b.Mem i := by
            intro w hw
            have hw' : w ∈ mi.inputs grp := hvs ▸ hw
            obtain ⟨hnn, y, hy, rfl⟩ := Measure.mem_inputs hw'
            have hm := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) mi.arg
            obtain ⟨i, b', he, hb', hi⟩ := AVal.intsOnly_mem honly hm hnn
            rw [hb] at hb'; cases hb'
            exact ⟨i, he, hi⟩
          obtain ⟨hlo, hhi⟩ := intSum_bounds hint
          exact ⟨by simp, hlo, hhi⟩
      · simp at hf
    · simp at hf
  · simp at hf

theorem EnvMem.measures {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (ms : List Measure) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    EnvMem (ms.map fun m => Measure.abs env fs m grouped rows) (ms.map (·.eval grp)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ms[j]? <;> simp [AVal.mem_top, Measure.abs_sound hall _ grouped hne rows hrows]

/-- **Soundness of abstract plan evaluation**: every row a well-formed plan
produces is described by `Rel.aeval`, provided the tables are. -/
theorem WinFn.abs_sound {env : List AVal} {part : List Nat} {b a : List Row} {x : Row}
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) {sz : Bool}
    (hn : sz = true → b.length + 1 + a.length < 2 ^ 62) :
    ∀ f : WinFn, (f.abs sz env).Mem (f.value part b a x)
  | .rowNumber => ⟨_, rfl, by
      have := List.length_filter_le (samePart part x) b
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩⟩
  | .rank _ => ⟨_, rfl, by
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (fun y => !peer ‹List SortKey› x y) (b.filter (samePart part x))
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩⟩
  | .denseRank sort => ⟨_, rfl, by
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (fun y => !peer sort x y) (b.filter (samePart part x))
      have h3 := dedup_length_le (((b.filter (samePart part x)).filter fun y => !peer sort x y).map
        fun y => sort.map (y.getD ·.col .null))
      simp only [List.length_map] at h3
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩⟩
  | .ntile k => ⟨_, rfl, by
      simp only [Bound.Mem, Option.some.injEq, Text.rowCap]
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (samePart part x) a
      generalize (List.filter (samePart part x) b).length = i at h1 ⊢
      generalize (List.filter (samePart part x) a).length = j at h2 ⊢
      have hm := ntileOf_le i k (i + 1 + j)
      have h1' := one_le_ntileOf i k (i + 1 + j)
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · subst hl; omega
      · cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩
  | .percentRank _ => by
      simp only [WinFn.abs, WinFn.value, WinFn.valueIn, floatRatio]
      split <;> exact ⟨_, rfl, Bound.mem_top _⟩
  | .cumeDist _ => ⟨_, rfl, Bound.mem_top _⟩
  | .agg m sort fr => by
      simp only [WinFn.abs, WinFn.value, WinFn.valueIn]
      refine Measure.abs_sound (fun y hy => ⟨?_, by simp [FactsHold]⟩) m
      have hy' := Frame.mem_rows hy
      simp only [List.mem_append, List.mem_cons, List.mem_filter] at hy'
      rcases hy' with ⟨hb, _⟩ | rfl | ⟨ha, _⟩
      · exact hall y (.inr (.inl hb))
      · exact hall y (.inl rfl)
      · exact hall y (.inr (.inr ha))
  | .firstValue _ _ _ | .lastValue _ _ _ | .nthValue _ _ _ _ => AVal.mem_top _
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
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) {sz : Bool}
    (hn : sz = true → b.length + 1 + a.length < 2 ^ 62) (fns : List WinFn) :
    EnvMem (fns.map (WinFn.abs sz env)) (fns.map (·.value part b a x)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases fns[j]? <;> simp [AVal.mem_top, WinFn.abs_sound hall hn]

/-- **The size hypothesis for relations** (trusted, #202): every relation a
window reads has fewer than `2⁶²` rows, which every engine's memory
guarantees. It bounds `ROW_NUMBER` and the ranks by `Text.rowCap`, so that
`ROW_NUMBER() - 1` is proved not to overflow. Every relation an aggregate
reads has fewer than `2⁶³` rows (#437): `COUNT(*)` of a group is a BIGINT,
in the reference and in every engine. It bounds a group's `SUM` by its
rows (`Rel.sumRows`), so that a `SUM` of values in `[-1, 1]` is proved to
fit 64 bits. -/
def Rel.Small (cat : Catalog) : Rel → Prop
  | .read _ | .values _ _ => True
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.Small cat
  | .aggregate r _ _ => (r.eval cat).length < 2 ^ 63 ∧ r.Small cat
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => a.Small cat ∧ b.Small cat
  | .window r _ _ _ => (r.eval cat).length < 2 ^ 62 ∧ r.Small cat

mutual
theorem Rel.aeval_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (sz = true → r.Small cat) → ∀ row ∈ r.eval cat,
      EnvMem (r.aeval cat A F T sz) row
  | .read t, _, _, row, h => useFacts_sound (hF t row h) ((hA t row h).fit _)
  | .values _ _, _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, hs, row, h => by
      simp only [eval, List.mem_filter] at h
      exact useFacts_sound ((Rel.facts_sound hcat hF hT hwf.1 row h.1).append (c.factsOf_sound h.2))
        (Expr.refine_sound _ c (aeval_sound hcat hA hF hT hwf.1 hs row h.1) h.2)
  | .project r es, hwf, hs, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hm := aeval_sound hcat hA hF hT hwf.1 hs x hx
      have hr := ratioPart_sound hcat hA hF hT hwf.1 hs x hx
      exact hm.append (hm.mapF ((Rel.facts_sound hcat hF hT hwf.1 x hx).append hr) es)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .emit r m, hwf, hs, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 hs x hx).emit m
  | .cross a b, hwf, hs, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx).append (aeval_sound hcat hA hF hT hwf.2 (fun h => (hs h).2) y hy)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .join a b .inner on, hwf, hs, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, ht⟩ := h
      exact Expr.refine_sound _ on ((aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx).append
        (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) y hy) (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])) ht
  | .join a b .left on, hwf, hs, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxm := aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx
      have hl : (a.aeval cat A F T sz).length = x.length := by
        rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hxm.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        exact hxm.append (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) y hy).nullable hl
  | .fetch r _ _, hwf, hs, row, h => by
      simp only [eval] at h
      have := aeval_sound hcat hA hF hT (r := r) hwf hs
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .semi a _ _ _, hwf, hs, row, h => by
      simp only [eval, List.mem_filter] at h
      exact aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) row h.1
  | .orderBy r _, hwf, hs, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf.1 hs row h
  | .distinct r, hwf, hs, row, h => by
      simp only [eval, mem_dedup] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf hs row h
  | .unnest r c, hwf, hs, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨_, v, _, _, rfl⟩ := mem_unnestRow h
      exact (aeval_sound hcat hA hF hT hwf.1 hs x hx).set_top c v
  | .aggregate r gs ms, hwf, hs, row, h => by
      obtain ⟨k, grp, rfl, hgrp, hk, hne, hglen⟩ := mem_aggregateEval_len h
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T sz) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hgrp y hy),
          Rel.facts_sound hcat hF hT hwf.1 y (hgrp y hy)⟩
      have hm := EnvMem.measures hall ms (!gs.isEmpty) (fun hg => hne (by simpa using hg))
        (rows := r.maxRows) (fun n hn => Nat.le_trans hglen (Rel.maxRows_sound hn))
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) hm (by simp)
      · exact (EnvMem.mapD (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) x hx)
          (Rel.facts_sound hcat hF hT hwf.1 x hx) gs).append hm (by simp)
  | .unionAll a b, hwf, hs, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) row h).zip_left
      · exact (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) row h).zip_right
  | .window r _ _ fns, hwf, hs, row, h => by
      obtain ⟨b, x, a, he, hx, rfl⟩ := mem_windowEval h
      obtain ⟨_, _, hin⟩ := sorted_split he
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T sz) y :=
        fun y hy => aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hin y hy)
      have hn : sz = true → b.length + 1 + a.length < 2 ^ 62 := by
        intro h
        have := (List.mergeSort_perm (r.eval cat) (sortLe ‹List SortKey›)).length_eq
        rw [he] at this; simp at this; have := (hs h).1; omega
      exact (hall x (.inl rfl)).append (EnvMem.window hall hn fns)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])

theorem Rel.ratioPart_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (sz = true → r.Small cat) → ∀ row ∈ r.eval cat,
      FactsHold (r.ratioPart cat A F T sz) row
  | .aggregate r gs ms, hwf, hs, row, h => by
      obtain ⟨k, grp, rfl, hgrp, hk, -⟩ := mem_aggregateEval_nonempty h
      refine ratioFacts_sound ?_ fun y hy => ⟨aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hgrp y hy),
        Rel.facts_sound hcat hF hT hwf.1 y (hgrp y hy)⟩
      rcases hk with ⟨rfl, rfl⟩ | ⟨z, _, rfl⟩ <;> simp [groupKey]
  | .read _, _, _, _, _ | .values _ _, _, _, _, _ | .filter _ _, _, _, _, _
  | .project _ _, _, _, _, _ | .emit _ _, _, _, _, _ | .cross _ _, _, _, _, _
  | .join _ _ _ _, _, _, _, _ | .fetch _ _ _, _, _, _, _ | .unionAll _ _, _, _, _, _
  | .window _ _ _ _, _, _, _, _ | .semi _ _ _ _, _, _, _, _ | .orderBy _ _, _, _, _, _
  | .distinct _, _, _, _, _ | .unnest _ _, _, _, _, _ => fun f hf => by simp [ratioPart] at hf
end

/-- `ratioFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem ratioFacts_sound_of {g : Nat} {env : List AVal} {fs : List Fact} {ms : List Measure}
    {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp)
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) :
    FactsHold (ratioFacts g env fs ms) row := by
  intro f hf
  simp only [ratioFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    split at hf
    · rename_i hc
      obtain ⟨hsum, hcount, harg, hfil, hdis, honly⟩ := hc
      split at hf
      · rename_i b hb
        simp only [List.mem_singleton] at hf; subst hf
        intro x n hx hn
        rw [col i mi hmi (by rw [hsum]; rfl), Measure.eval_eq (by rw [hsum]; rfl), hsum] at hx
        rw [col j mj hmj (by rw [hcount]; rfl), Measure.eval_eq (by rw [hcount]; rfl), hcount] at hn
        have hsame : mj.inputs grp = mi.inputs grp := by
          simp only [Measure.inputs, Measure.kept, harg, hfil, hdis]
        rw [hsame] at hn
        cases hvs : mi.inputs grp with
        | nil => rw [hvs] at hx; simp [AggFn.apply] at hx
        | cons v vs =>
          rw [hvs] at hx hn
          simp only [AggFn.apply, Value.int.injEq] at hx hn
          subst hx hn
          have hint : ∀ w ∈ v :: vs, ∃ i, w = .int i ∧ b.Mem i := by
            intro w hw
            have hw' : w ∈ mi.inputs grp := hvs ▸ hw
            obtain ⟨hnn, y, hy, rfl⟩ := Measure.mem_inputs hw'
            have hm := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) mi.arg
            obtain ⟨i, b', he, hb', hi⟩ := AVal.intsOnly_mem honly hm hnn
            rw [hb] at hb'; cases hb'
            exact ⟨i, he, hi⟩
          obtain ⟨hlo, hhi⟩ := intSum_bounds hint
          exact ⟨by simp, hlo, hhi⟩
      · simp at hf
    · simp at hf
  · simp at hf

theorem EnvMem.measures_all {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) {ms : List Measure} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    EnvMem (ms.map fun m => Measure.abs env fs m grouped rows) vs := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hv.getElem? j with ⟨m, v, hm, hb, hr⟩ | ⟨hm, hb⟩
  · obtain ⟨s, hp, rfl, _⟩ := hr.eval
    simp only [hm, hb, Option.map_some, Option.getD_some]
    exact Measure.abs_sound (grp := s) (fun y hy => hall y (hp.mem_iff.mp hy)) m grouped
      (fun hg hs => hne hg (List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, hs]; rfl))) rows
      (fun n hn => hp.length_eq ▸ hrows n hn)
  · simp [hm, hb, AVal.mem_top]

mutual
/-- **The abstract interpreter describes every row of every order.** -/
theorem Rel.aeval_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, EnvMem (r.aeval cat A F T) row
  | .read t, _, _, h, row, hr =>
      useFacts_sound (hF t row (h.mem_iff.mp hr)) ((hA t row (h.mem_iff.mp hr)).fit _)
  | .values _ _, _, _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact useFacts_sound ((Rel.facts_sound_all hcat hF hT hwf.1 hi row hr.1).append
        (c.factsOf_sound hr.2)) (Expr.refine_sound _ c (aeval_sound_all hcat hA hF hT hwf.1 hi row hr.1) hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hm := aeval_sound_all hcat hA hF hT hwf.1 hi x hx
      have hrp := ratioPart_sound_all hcat hA hF hT hwf.1 hi x hx
      exact hm.append (hm.mapF ((Rel.facts_sound_all hcat hF hT hwf.1 hi x hx).append hrp) es)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x hx])
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).emit m
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      exact (aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      exact Expr.refine_sound _ on ((aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])) ht
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hum := aeval_sound_all hcat hA hF hT hwf.1 hx u hu
      have hl : (a.aeval cat A F T).length = u.length := by
        rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hum.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨v, hv, rfl⟩, _⟩ := h
        exact hum.append (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv).nullable hl
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := aeval_sound_all hcat hA hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .unnest r c, hwf, _, ⟨i, hi, h⟩, row, hr => by
      obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      obtain ⟨_, v, _, _, rfl⟩ := mem_unnestRow h
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).set_top c v
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, hne, hglen⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
      have hm := EnvMem.measures_all hall hv (!gs.isEmpty) (fun hg => hne (by simpa using hg))
        (rows := r.maxRows) (fun n hn => Nat.le_trans hglen (Rel.maxRows_sound_all hn hi))
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) hm (by simp)
      · exact (EnvMem.mapD (aeval_sound_all hcat hA hF hT hwf.1 hi x hx)
          (Rel.facts_sound_all hcat hF hT hwf.1 hi x hx) gs).append hm (by simp)
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact (aeval_sound_all hcat hA hF hT hwf.1 hx row h).zip_left
      · exact (aeval_sound_all hcat hA hF hT hwf.2.1 hy row h).zip_right
  | .window r _ _ fns, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, _, rfl, _, _, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T) y :=
        fun y hy => aeval_sound_all hcat hA hF hT hwf.1 hi y (hp.mem_iff.mp (hin y hy))
      exact (hall x (.inl rfl)).append (EnvMem.window (sz := false) hall nofun fns)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp (hin x (.inl rfl)))])

theorem Rel.ratioPart_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.ratioPart cat A F T) row
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, -⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      exact ratioFacts_sound_of (hkl ▸ aggCol hv) fun y hy =>
        ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
  | .read _, _, _, _, _, _ | .values _ _, _, _, _, _, _ | .filter _ _, _, _, _, _, _
  | .project _ _, _, _, _, _, _ | .emit _ _, _, _, _, _, _ | .cross _ _, _, _, _, _, _
  | .join _ _ _ _, _, _, _, _, _ | .fetch _ _ _, _, _, _, _, _ | .unionAll _ _, _, _, _, _, _
  | .window _ _ _ _, _, _, _, _, _ | .semi _ _ _ _, _, _, _, _, _ | .orderBy _ _, _, _, _, _, _
  | .distinct _, _, _, _, _, _ | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [ratioPart] at hf
end

/-! ## Contracts -/

/-- Substitute expressions for field references. -/
def Expr.subst (cols : List Expr) : Expr → Expr
  | .lit v => .lit v
  | .field i => cols.getD i (.lit .null)
  | .un f a => .un f (a.subst cols)
  | .bin f a b => .bin f (a.subst cols) (b.subst cols)
  | .ifThen c t e => .ifThen (c.subst cols) (t.subst cols) (e.subst cols)
  | .hof f l b => .hof f (l.subst cols) (b.subst (.field 0 :: cols.map (·.shift 0)))

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
  | .hof f l b => by
      simp only [subst, eval, Expr.eval_subst cols row l]
      congr 1; funext x
      rw [Expr.eval_subst _ (x :: row) b]
      simp [eval, List.map_map, Function.comp_def, Expr.eval_shift_cons]

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

/-- **Contract soundness for every order.** Under `contract_sound`'s
hypotheses, every postcondition holds on every row of every order the
reference allows: for every way an engine breaks ties, takes the rows of a
`FETCH` or orders the rows of `FIRST`, `STRING_AGG` or a window. -/
theorem contract_sound_all {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out → ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  intro out hout row hrow v hv
  have hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold ((pre t).flatMap Expr.factsOf) row := by
    intro t row h f hf
    simp only [List.mem_flatMap] at hf
    obtain ⟨e, he, hf⟩ := hf
    exact Expr.factsOf_sound e (hpre t row h e he) f hf
  have hm := Q.aeval_sound_all hcat (fun t row h => tableEnv_sound (hS t row h) (hpre t row h)) hF
    hT hQ hout row hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : j < (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).length := by
    rw [Rel.aeval_length hQ, ← Rel.orderAllowed_arity hcat hQ hout row hrow]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen)
  have := hm j
  simp only [List.getElem?_eq_getElem hlen, Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

/-- **Contract soundness.** Suppose every row of every table matches its
schema and satisfies its preconditions, the postcondition plan `Q` (the
transformation followed by a select of the postconditions) is well-formed. If
the abstract evaluation shows every column of `Q` is certainly TRUE, then
every postcondition holds on every output row. -/
theorem contract_sound {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true :=
  contract_sound_all hcat hS hpre hQ hT hproved (Q.eval_orderAllowed cat)

end Substrait
