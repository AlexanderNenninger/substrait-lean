import SubstraitLean.OrderAllowed

/-!
# Contracts: Lattice

The lattice of the abstract interpreter: integer intervals (`Bound`), abstract
values (`AVal`) with their membership `AVal.Mem` and `AVal.join`, and numbers by
kind (#923).

Part of `SubstraitLean.Contracts`, which re-exports it. -/

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

/-- The kinds `date_part`, `date_trunc` and `time` read: a timestamp or a time
of day. -/
def tsOrTod : NumKind → Bool
  | .ts | .tod => true
  | _ => false

/-- The kinds the decimal operations read: an integer or a decimal. -/
def intOrDec : NumKind → Bool
  | .int | .dec _ => true
  | _ => false

/-- Two integers, to an integer. -/
def intsOnly : NumKind → NumKind → Option NumKind
  | .int, .int => some .int
  | _, _ => none

/-- Two doubles, to a double. -/
def floatsOnly : NumKind → NumKind → Option NumKind
  | .float, .float => some .float
  | _, _ => none

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
  /-- if `some k`, every number is of kind `k` (#923); `none`, of any kind. -/
  nk : Option NumKind
  deriving Repr, BEq

/-- The most strings an abstract value lists (#708); more, and any string may be. -/
def strCap : Nat := 64

/-- `i` is a number of kind `k` that `a` holds. -/
def AVal.MemNum (a : AVal) (k : NumKind) (i : Int) : Prop :=
  ∃ b, a.int = some b ∧ b.Mem i ∧ a.nk.all (· == k) = true

def AVal.Mem (a : AVal) : Value → Prop
  | .null => a.null = true
  -- A number by its integer, where `a` allows its kind (#923).
  | .int i => a.MemNum .int i
  | .float i => a.MemNum .float i
  | .date i => a.MemNum .date i
  | .ts i => a.MemNum .ts i
  | .tod i => a.MemNum .tod i
  | .dec s i => a.MemNum (.dec s) i
  | .bool true => a.tt = true
  | .bool false => a.ff = true
  | .str s => (a.str && a.strs.all (·.contains s)) = true
  -- The abstraction does not look into lists: a list is a member where the
  -- booleans and strings are. Functions of one type give NULL on the others,
  -- so each abstraction covers a list as it covers a value of another type.
  | .list _ | .struct _ => a.tt = true ∧ a.ff = true ∧ a.str = true

theorem AVal.memInt_intro {a : AVal} {b : Bound} {i : Int} (hb : a.int = some b)
    (hk : a.nk = some .int) (hi : b.Mem i) : a.Mem (.int i) :=
  ⟨b, hb, hi, by simp [hk]⟩

theorem AVal.mem_val {a : AVal} {k : NumKind} {i : Int} : a.Mem (k.val i) ↔ a.MemNum k i := by
  cases k <;> rfl

/-- Every integer `a` describes is in `[lo, hi]`. -/
def AVal.within (lo hi : Int) (a : AVal) : Bool := a.int.all (·.within lo hi)

theorem AVal.within_memNum {lo hi i : Int} {a : AVal} {k : NumKind} (h : a.within lo hi = true)
    (hm : a.MemNum k i) : between lo hi i = true := by
  obtain ⟨b, hb, hi, _⟩ := hm
  simp only [AVal.within, hb, Option.all_some] at h
  exact Bound.within_mem h hi

theorem AVal.within_mem {lo hi i : Int} {a : AVal} (h : a.within lo hi = true)
    (hm : a.Mem (.int i)) : between lo hi i = true := AVal.within_memNum h hm

def AVal.top : AVal := ⟨true, some Bound.top, true, true, true, none, none⟩
def AVal.bot : AVal := ⟨false, none, false, false, false, none, none⟩

/-- A number of kind `k` in `b`, maybe NULL. -/
def AVal.num (null : Bool) (b : Bound) (k : NumKind) : AVal :=
  ⟨null, some b, false, false, false, none, some k⟩

def AVal.ofValue : Value → AVal
  | .null => ⟨true, none, false, false, false, none, none⟩
  | .int i => .num false (.exact i) .int
  | .float i => .num false (.exact i) .float
  | .date i => .num false (.exact i) .date
  | .ts i => .num false (.exact i) .ts
  | .tod i => .num false (.exact i) .tod
  | .dec s i => .num false (.exact i) (.dec s)
  | .bool true => ⟨false, none, true, false, false, none, none⟩
  | .bool false => ⟨false, none, false, true, false, none, none⟩
  | .str s => ⟨false, none, false, false, true, some [s], none⟩
  | .list _ | .struct _ => ⟨false, none, true, true, true, none, none⟩

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

/-- The numbers' kind of either side: a side without numbers adds none. -/
def joinNk (a b : AVal) : Option NumKind :=
  if a.int.isNone then b.nk else if b.int.isNone then a.nk else if a.nk = b.nk then a.nk else none

def AVal.join (a b : AVal) : AVal :=
  ⟨a.null || b.null, joinInt a.int b.int, a.tt || b.tt, a.ff || b.ff, a.str || b.str, joinStrs a b,
    joinNk a b⟩

/-- May be something other than a (non-NULL) integer. -/
def AVal.nonInt (a : AVal) : Bool := a.null || a.tt || a.ff || a.str
/-- May be something other than a (non-NULL) number of kind `k`: a function of
`k` gives NULL there (#923). -/
def AVal.nonNum (k : NumKind) (a : AVal) : Bool := a.nonInt || (a.int.isSome && a.nk != some k)
/-- May be something other than a (non-NULL) boolean. -/
def AVal.nonBool (a : AVal) : Bool := a.null || a.int.isSome || a.str

/-- Certainly TRUE: the only value a satisfied condition can have. -/
def AVal.certainlyTrue (a : AVal) : Bool := !a.null && a.int.isNone && !a.ff && !a.str

/-- A number of another kind than `k` is a case of `nonNum k`. -/
theorem AVal.nonNum_of_memNum {a : AVal} {k k' : NumKind} {i : Int} (hm : a.MemNum k' i)
    (hk : k' ≠ k) : a.nonNum k = true := by
  obtain ⟨b, hb, _, hn⟩ := hm
  simp only [AVal.nonNum, hb, Option.isSome_some, Bool.true_and, Bool.or_eq_true, bne_iff_ne,
    ne_eq]
  right
  intro h
  rw [h] at hn
  simp only [Option.all_some, beq_iff_eq] at hn
  exact hk hn.symm

theorem AVal.memNum_kind {a : AVal} {k k' : NumKind} {i : Int} (hm : a.MemNum k' i)
    (hk : a.nonNum k = false) : k' = k := by
  if h : k' = k then exact h else
  rw [AVal.nonNum_of_memNum hm h] at hk
  exact Bool.noConfusion hk

theorem AVal.mem_top : ∀ v, AVal.top.Mem v
  | .null | .bool true | .bool false | .str _ => rfl
  | .list _ | .struct _ => by simp [AVal.Mem, AVal.top]
  | .int i | .float i | .date i | .ts i | .tod i | .dec _ i => ⟨_, rfl, Bound.mem_top i, rfl⟩

theorem AVal.mem_ofValue : ∀ v, (AVal.ofValue v).Mem v
  | .null | .bool true | .bool false => rfl
  | .str s => by simp [AVal.Mem, AVal.ofValue]
  | .list _ | .struct _ => by simp [AVal.Mem, AVal.ofValue]
  | .int i | .float i | .date i | .ts i | .tod i | .dec _ i =>
    ⟨_, rfl, Bound.mem_exact i, by simp [AVal.ofValue, AVal.num]⟩

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

theorem AVal.memNum_join_left {a b : AVal} {k : NumKind} {i : Int} (h : a.MemNum k i) :
    (a.join b).MemNum k i := by
  obtain ⟨x, hx, hm, hn⟩ := h
  have hk : (joinNk a b).all (· == k) = true := by
    simp only [joinNk, hx, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    split
    · exact hn
    · split
      · exact hn
      · rfl
  cases hb : b.int with
  | none => exact ⟨x, by simp [AVal.join, hx, hb, joinInt], hm, hk⟩
  | some y => exact ⟨x.join y, by simp [AVal.join, hx, hb, joinInt], Bound.mem_join_left hm, hk⟩

theorem AVal.memNum_join_right {a b : AVal} {k : NumKind} {i : Int} (h : b.MemNum k i) :
    (a.join b).MemNum k i := by
  obtain ⟨y, hy, hm, hn⟩ := h
  have hk : (joinNk a b).all (· == k) = true := by
    unfold joinNk
    split
    · exact hn
    · simp only [hy, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i he; rw [he]; exact hn
      · rfl
  cases ha : a.int with
  | none => exact ⟨y, by simp [AVal.join, hy, ha, joinInt], hm, hk⟩
  | some x => exact ⟨x.join y, by simp [AVal.join, hy, ha, joinInt], Bound.mem_join_right hm, hk⟩

theorem AVal.mem_join_left {a b : AVal} : ∀ {v}, a.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.join, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨.inl h.1, joinStrs_left h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
      simp_all [AVal.Mem, AVal.join]
  | .list _, h | .struct _, h => by
      simp only [AVal.Mem, AVal.join] at *
      exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩
  | .int _, h | .float _, h | .date _, h | .ts _, h | .tod _, h | .dec _ _, h =>
      AVal.memNum_join_left h

theorem AVal.mem_join_right {a b : AVal} : ∀ {v}, b.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.join, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨.inr h.1, joinStrs_right h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
      simp_all [AVal.Mem, AVal.join]
  | .list _, h | .struct _, h => by
      simp only [AVal.Mem, AVal.join] at *
      exact ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩
  | .int _, h | .float _, h | .date _, h | .ts _, h | .tod _, h | .dec _ _, h =>
      AVal.memNum_join_right h

theorem AVal.certainlyTrue_mem {a : AVal} {v : Value} (hc : a.certainlyTrue = true)
    (hm : a.Mem v) : v = .bool true := by
  simp only [AVal.certainlyTrue, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hc
  obtain ⟨⟨⟨hn, hi⟩, hf⟩, hs⟩ := hc
  match v, hm with
  | .null, hm => simp_all [AVal.Mem]
  | .int _, ⟨_, hb, _⟩ | .float _, ⟨_, hb, _⟩ | .date _, ⟨_, hb, _⟩ | .ts _, ⟨_, hb, _⟩
  | .tod _, ⟨_, hb, _⟩ | .dec _ _, ⟨_, hb, _⟩ => simp_all
  | .bool true, _ => rfl
  | .bool false, hm => simp_all [AVal.Mem]
  | .str _, hm | .list _, hm | .struct _, hm => simp_all [AVal.Mem]

/-- Shapes of a value, for case analysis in the binary soundness proofs. -/
theorem AVal.mem_cases {a : AVal} {v : Value} (h : a.Mem v) :
    (v = .null ∧ a.null = true) ∨
    (∃ k i b, v = k.val i ∧ a.int = some b ∧ b.Mem i ∧ a.nk.all (· == k) = true) ∨
    (v = .bool true ∧ a.tt = true) ∨ (v = .bool false ∧ a.ff = true) ∨
    (∃ s, v = .str s ∧ a.str = true ∧ a.strs.all (·.contains s) = true) ∨
    (∃ vs, (v = .list vs ∨ v = .struct vs) ∧ a.tt = true ∧ a.ff = true ∧ a.str = true) := by
  match v, h with
  | .null, h => exact .inl ⟨rfl, h⟩
  | .int i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.int, i, b, rfl, hb, hm, hk⟩)
  | .float i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.float, i, b, rfl, hb, hm, hk⟩)
  | .date i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.date, i, b, rfl, hb, hm, hk⟩)
  | .ts i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.ts, i, b, rfl, hb, hm, hk⟩)
  | .tod i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.tod, i, b, rfl, hb, hm, hk⟩)
  | .dec s i, ⟨b, hb, hm, hk⟩ => exact .inr (.inl ⟨.dec s, i, b, rfl, hb, hm, hk⟩)
  | .bool true, h => exact .inr (.inr (.inl ⟨rfl, h⟩))
  | .bool false, h => exact .inr (.inr (.inr (.inl ⟨rfl, h⟩)))
  | .str s, h =>
      simp only [AVal.Mem, Bool.and_eq_true] at h
      exact .inr (.inr (.inr (.inr (.inl ⟨s, rfl, h⟩))))
  | .list vs, h => exact .inr (.inr (.inr (.inr (.inr ⟨vs, .inl rfl, h⟩))))
  | .struct vs, h => exact .inr (.inr (.inr (.inr (.inr ⟨vs, .inr rfl, h⟩))))

/-- `mem_cases h with i b hb hi` splits `h : a.Mem v` into its six cases and
substitutes `v`: `hn` (NULL), a number `k.val i` of kind `k` with
`hb : a.int = some b`, `hi : b.Mem i` and `hk : a.nk.all (· == k)`, `ht`
(TRUE), `hf` (FALSE), `hs` (a string `s`, a list or a struct). -/
syntax "mem_cases " term " with " Lean.Parser.Tactic.rcasesPatLo Lean.Parser.Tactic.rcasesPatLo
  Lean.Parser.Tactic.rcasesPatLo Lean.Parser.Tactic.rcasesPatLo : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mem_cases $h with $i $b $hb $hi) => `(tactic|
      rcases AVal.mem_cases $h with ⟨rfl, hn⟩ | ⟨k, $i, $b, rfl, $hb, $hi, hk⟩ | ⟨rfl, ht⟩ |
        ⟨rfl, hf⟩ | ⟨s, rfl, hs⟩ | ⟨_, rfl | rfl, hs⟩)

/-- `mem_cases₂ ha hb` splits two memberships: `k i x hx hi hk` and
`k' j y hy hj hk'` for numbers, `h` and `h'` for the other cases (strings
`s`, `s'`). -/
syntax "mem_cases₂ " term:max term:max : tactic

set_option hygiene false in
macro_rules
  | `(tactic| mem_cases₂ $ha $hb) => `(tactic|
      rcases AVal.mem_cases $ha with ⟨rfl, h⟩ | ⟨k, i, x, rfl, hx, hi, hk⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
        ⟨s, rfl, h⟩ | ⟨_, rfl | rfl, h⟩ <;>
      rcases AVal.mem_cases $hb with ⟨rfl, h'⟩ | ⟨k', j, y, rfl, hy, hj, hk'⟩ | ⟨rfl, h'⟩ |
        ⟨rfl, h'⟩ | ⟨s', rfl, h'⟩ | ⟨_, rfl | rfl, h'⟩)

/-! ### Numbers by kind (#923)

A function of numbers reads a number of the kinds it takes and gives one of
its result's kind; a number of another kind gives NULL. `mapAbs` and
`mapAbs₂` abstract every such function, from its action on intervals. -/

/-- A function of one number: `g` on a number of a kind `ok` takes, of kind
`kout` of its kind; NULL elsewhere and where `g` has no value. -/
def Value.mapP (ok : NumKind → Bool) (kout : NumKind → NumKind) (g : Int → Option Int)
    (v : Value) : Value :=
  match v.numOf? with
  | some (k, c) => if ok k then (match g c with | some r => (kout k).val r | none => .null) else .null
  | none => .null

/-- A function of two numbers: `g` on numbers of kinds `tbl` takes, of the
kind it gives; NULL elsewhere and where `g` has no value. -/
def Value.mapP₂ (tbl : NumKind → NumKind → Option NumKind) (g : Int → Int → Option Int)
    (v w : Value) : Value :=
  match v.numOf?, w.numOf? with
  | some (k, x), some (k', y) =>
    match tbl k k', g x y with
    | some ko, some r => ko.val r
    | _, _ => .null
  | _, _ => .null

/-- May be something other than a (non-NULL) number of a kind `ok` takes. -/
def AVal.nonNumP (ok : NumKind → Bool) (a : AVal) : Bool :=
  a.nonInt || (a.int.isSome && !a.nk.any ok)

theorem AVal.ok_of_memNum {a : AVal} {ok : NumKind → Bool} {k : NumKind} {b : Bound}
    (hb : a.int = some b) (hk : a.nk.all (· == k) = true) (hn : a.nonNumP ok = false) :
    ok k = true := by
  simp only [AVal.nonNumP, hb, Option.isSome_some, Bool.true_and, Bool.or_eq_false_iff,
    Bool.not_eq_false'] at hn
  cases hnk : a.nk with
  | none => simp [hnk] at hn
  | some k' =>
    simp only [hnk, Option.all_some, beq_iff_eq] at hk
    simp only [hnk, Option.any_some] at hn
    subst hk; exact hn.2

/-- The abstraction of `Value.mapP`: `bf` of the interval, the kind mapped,
NULL where the argument may be of another kind or `extra` says `g` may fail. -/
def mapAbs (ok : NumKind → Bool) (kout : NumKind → NumKind) (bf : Bound → Bound)
    (extra : Option Bound → Bool) (a : AVal) : AVal :=
  ⟨a.nonNumP ok || extra a.int, a.int.map bf, false, false, false, none, a.nk.map kout⟩

theorem mapAbs_sound {ok : NumKind → Bool} {kout : NumKind → NumKind} {g : Int → Option Int}
    {bf : Bound → Bound} {extra : Option Bound → Bool} {f : UnFn}
    (hf : ∀ v, f.apply v = Value.mapP ok kout g v)
    (hb : ∀ b i r, b.Mem i → g i = some r → (bf b).Mem r)
    (hn : ∀ b i, b.Mem i → g i = none → extra (some b) = true)
    {a : AVal} {v : Value} (h : a.Mem v) : (mapAbs ok kout bf extra a).Mem (f.apply v) := by
  rw [hf]
  mem_cases h with i b hb' hi
  · simp [Value.mapP, Value.numOf?, mapAbs, AVal.Mem, AVal.nonNumP, AVal.nonInt, hn]
  · simp only [Value.mapP, NumKind.numOf?_val]
    cases hok : ok k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      show (mapAbs ok kout bf extra a).null = true
      simp only [mapAbs, Bool.or_eq_true]
      left
      cases hn' : a.nonNumP ok
      · rw [AVal.ok_of_memNum hb' hk hn'] at hok; cases hok
      · rfl
    · simp only [↓reduceIte]
      cases hg : g i with
      | some r =>
        simp only []
        rw [AVal.mem_val]
        refine ⟨bf b, by simp [mapAbs, hb'], hb b i r hi hg, ?_⟩
        cases hnk : a.nk with
        | none => simp [mapAbs, hnk]
        | some k' =>
          simp only [hnk, Option.all_some, beq_iff_eq] at hk
          subst hk; simp [mapAbs, hnk]
      | none =>
        show (mapAbs ok kout bf extra a).null = true
        simp [mapAbs, hb', hn b i hi hg]
  all_goals simp_all [Value.mapP, Value.numOf?, mapAbs, AVal.Mem, AVal.nonNumP, AVal.nonInt]

/-- The kind of a function of two numbers of kinds `a.nk` and `b.nk`. -/
def outKind (tbl : NumKind → NumKind → Option NumKind) (a b : AVal) : Option NumKind :=
  match a.nk, b.nk with
  | some ka, some kb => tbl ka kb
  | _, _ => none

/-- The abstraction of `Value.mapP₂`: `bf` of the intervals, of the table's
kind, NULL where an argument may be of another kind or `extra` says `g` may
fail. -/
def mapAbs₂ (tbl : NumKind → NumKind → Option NumKind) (bf : Bound → Bound → Bound)
    (extra : Option Bound → Option Bound → Bool) (a b : AVal) : AVal :=
  ⟨a.nonInt || b.nonInt || extra a.int b.int ||
      (a.int.isSome && b.int.isSome && (outKind tbl a b).isNone),
   (match a.int, b.int with | some x, some y => some (bf x y) | _, _ => none),
   false, false, false, none, outKind tbl a b⟩

theorem mapAbs₂_sound {tbl : NumKind → NumKind → Option NumKind} {g : Int → Int → Option Int}
    {bf : Bound → Bound → Bound} {extra : Option Bound → Option Bound → Bool} {f : BinFn}
    (hf : ∀ v w, f.apply v w = Value.mapP₂ tbl g v w)
    (hb : ∀ x y i j r, x.Mem i → y.Mem j → g i j = some r → (bf x y).Mem r)
    (hn : ∀ x y i j, x.Mem i → y.Mem j → g i j = none → extra (some x) (some y) = true)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb' : b.Mem w) :
    (mapAbs₂ tbl bf extra a b).Mem (f.apply v w) := by
  rw [hf]
  mem_cases₂ ha hb'
  case inr.inl.inr.inl =>
    simp only [Value.mapP₂, NumKind.numOf?_val]
    cases hout : outKind tbl a b with
    | none =>
      cases htb : tbl k k' <;> cases hg : g i j <;> simp only []
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · rename_i ko r
        rw [AVal.mem_val]
        exact ⟨bf x y, by simp [mapAbs₂, hx, hy], hb x y i j r hi hj hg, by simp [mapAbs₂, hout]⟩
    | some ko =>
      have hko : tbl k k' = some ko := by
        unfold outKind at hout
        cases hka : a.nk <;> cases hkb : b.nk <;> simp only [hka, hkb, reduceCtorEq] at hout
        rename_i ka kb
        simp only [hka, Option.all_some, beq_iff_eq] at hk
        simp only [hkb, Option.all_some, beq_iff_eq] at hk'
        subst hk hk'; exact hout
      simp only [hko]
      cases hg : g i j with
      | some r =>
        simp only []
        rw [AVal.mem_val]
        exact ⟨bf x y, by simp [mapAbs₂, hx, hy], hb x y i j r hi hj hg, by simp [mapAbs₂, hout]⟩
      | none =>
        show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hn x y i j hi hj hg]
  all_goals simp_all [Value.mapP₂, Value.numOf?, mapAbs₂, AVal.Mem, AVal.nonInt]

end Substrait
