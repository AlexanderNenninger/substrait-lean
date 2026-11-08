import Sverify.Core.OrderAllowed

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

/-- The set of values a column may hold, by kind (#925): NULL, numbers of a
kind in an interval, booleans, strings, lists whose elements one abstract
value describes, and structs whose fields a list of them does. Every field
has a default that admits nothing of its kind, so a literal names only what
it admits. -/
structure AVal where
  /-- may be NULL -/
  null : Bool := false
  /-- may be a number, its integer within this interval -/
  int : Option Bound := none
  /-- may be TRUE -/
  tt : Bool := false
  /-- may be FALSE -/
  ff : Bool := false
  /-- may be a string -/
  str : Bool := false
  /-- if `some l`, every string is in `l` (#708): the values of a status or a
  tag. At most `strCap` of them; past that, `none`. -/
  strs : Option (List String) := none
  /-- if `some k`, every number is of kind `k` (#923); `none`, of any kind. -/
  nk : Option NumKind := none
  /-- may be a list -/
  list : Bool := false
  /-- if `some e`, every element of a list is in `e`; `none`, any value. -/
  elems : Option AVal := none
  /-- every list's length is in this interval -/
  card : Bound := Bound.top
  /-- may be a struct -/
  struct : Bool := false
  /-- if `some fs`, a struct has a field for each of `fs`, in `fs`; `none`,
  any fields. -/
  fields : Option (List AVal) := none
  deriving Repr, BEq, Inhabited

/-- The most strings an abstract value lists (#708); more, and any string may be. -/
def strCap : Nat := 64

/-- `i` is a number of kind `k` that `a` holds. -/
def AVal.MemNum (a : AVal) (k : NumKind) (i : Int) : Prop :=
  ∃ b, a.int = some b ∧ b.Mem (k.norm i) ∧ a.nk.all (· == k) = true

mutual
/-- `AVal.Mem`, by recursion on the value. -/
def AVal.MemR (a : AVal) : Value → Prop
  | .null => a.null = true
  -- A number by its integer, where `a` allows its kind (#923).
  | .int i => a.MemNum .int i
  | .float i => a.MemNum .float i
  | .date i => a.MemNum .date i
  | .ts i => a.MemNum .ts i
  | .tod i => a.MemNum .tod i
  | .dec s i => a.MemNum (.dec s) i
  -- `cond`, not a match on the boolean: `simp` rewrites it where the
  -- boolean is not a literal (`a.Mem (.bool (s == t))`).
  | .bool b => cond b a.tt a.ff = true
  | .str s => (a.str && a.strs.all (·.contains s)) = true
  | .list vs => a.list = true ∧ a.card.Mem vs.length ∧
      (match a.elems with | some e => AVal.MemAll e vs | none => True)
  | .struct vs => a.struct = true ∧
      (match a.fields with | some fs => AVal.MemFields fs vs | none => True)

/-- Every value of `vs` is in `e`. -/
def AVal.MemAll (e : AVal) : List Value → Prop
  | [] => True
  | v :: vs => e.MemR v ∧ AVal.MemAll e vs

/-- `vs` has a value for each of `fs`, in it. -/
def AVal.MemFields : List AVal → List Value → Prop
  | [], [] => True
  | f :: fs, v :: vs => f.MemR v ∧ AVal.MemFields fs vs
  | _, _ => False
end

/-- `v` is one of the values `a` describes, by its constructor (#925). Not
recursive itself, so that unification compares two memberships by their
arguments. -/
def AVal.Mem (a : AVal) (v : Value) : Prop := a.MemR v

attribute [simp] AVal.MemR AVal.MemAll AVal.MemFields

theorem AVal.memAll_iff {e : AVal} : ∀ {vs : List Value}, AVal.MemAll e vs ↔ ∀ v ∈ vs, e.Mem v
  | [] => by simp
  | v :: vs => by simp [AVal.Mem, AVal.memAll_iff (vs := vs)]

theorem AVal.memInt_intro {a : AVal} {b : Bound} {i : Int} (hb : a.int = some b)
    (hk : a.nk = some .int) (hi : b.Mem i) : a.Mem (.int i) :=
  ⟨b, hb, hi, by simp [hk]⟩

theorem AVal.mem_val {a : AVal} {k : NumKind} {i : Int} : a.Mem (k.val i) ↔ a.MemNum k i := by
  cases k <;> rfl

/-- Every integer `a` describes is in `[lo, hi]`. -/
def AVal.within (lo hi : Int) (a : AVal) : Bool := a.int.all (·.within lo hi)

theorem AVal.within_memNum {lo hi i : Int} {a : AVal} {k : NumKind} (h : a.within lo hi = true)
    (hm : a.MemNum k i) : between lo hi (k.norm i) = true := by
  obtain ⟨b, hb, hi, _⟩ := hm
  simp only [AVal.within, hb, Option.all_some] at h
  exact Bound.within_mem h hi

theorem AVal.within_mem {lo hi i : Int} {a : AVal} (h : a.within lo hi = true)
    (hm : a.Mem (.int i)) : between lo hi i = true := AVal.within_memNum h hm

def AVal.top : AVal :=
  { null := true, int := some Bound.top, tt := true, ff := true, str := true, list := true,
    struct := true }
def AVal.bot : AVal := {}

/-- A number of kind `k` in `b`, maybe NULL. -/
def AVal.num (null : Bool) (b : Bound) (k : NumKind) : AVal := { null, int := some b, nk := some k }

/-- What a list's elements may be: `elems`, or any value. -/
def AVal.elemsOf (a : AVal) : AVal := a.elems.getD AVal.top

def AVal.ofValue : Value → AVal
  | .null => { null := true }
  | .int i => .num false (.exact i) .int
  | .float i => .num false (.exact (FloatCode.canon i)) .float
  | .date i => .num false (.exact i) .date
  | .ts i => .num false (.exact i) .ts
  | .tod i => .num false (.exact i) .tod
  | .dec s i => .num false (.exact i) (.dec s)
  | .bool true => { tt := true }
  | .bool false => { ff := true }
  | .str s => { str := true, strs := some [s] }
  | .list vs => { list := true, card := .exact vs.length }
  | .struct _ => { struct := true }

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

mutual
/-- The values of either side. A side that holds no list (no struct) adds
nothing to the elements and lengths (fields). -/
def AVal.join : AVal → AVal → AVal
  | a@⟨_, _, _, _, _, _, _, l, e, c, st, fs⟩, b =>
    { null := a.null || b.null, int := joinInt a.int b.int, tt := a.tt || b.tt,
      ff := a.ff || b.ff, str := a.str || b.str, strs := joinStrs a b, nk := joinNk a b,
      list := l || b.list,
      elems := if !l then b.elems else if !b.list then e else AVal.joinE e b.elems,
      card := if !l then b.card else if !b.list then c else c.join b.card,
      struct := st || b.struct,
      fields := if !st then b.fields else if !b.struct then fs else AVal.joinF fs b.fields }
  termination_by structural a => a

/-- Both elements' descriptions joined; any value where one is. -/
def AVal.joinE : Option AVal → Option AVal → Option AVal
  | some x, some y => some (x.join y)
  | _, _ => none
  termination_by structural x => x

/-- Both fields' descriptions joined, field by field; any fields where one
is, or where they differ in number. -/
def AVal.joinF : Option (List AVal) → Option (List AVal) → Option (List AVal)
  | some xs, some ys => AVal.joinL xs ys
  | _, _ => none
  termination_by structural x => x

def AVal.joinL : List AVal → List AVal → Option (List AVal)
  | [], [] => some []
  | x :: xs, y :: ys => (AVal.joinL xs ys).map (x.join y :: ·)
  | _, _ => none
  termination_by structural x => x
end

section
variable (a b : AVal)
@[simp] theorem AVal.join_null : (a.join b).null = (a.null || b.null) := by cases a; rfl
@[simp] theorem AVal.join_int : (a.join b).int = joinInt a.int b.int := by cases a; rfl
@[simp] theorem AVal.join_tt : (a.join b).tt = (a.tt || b.tt) := by cases a; rfl
@[simp] theorem AVal.join_ff : (a.join b).ff = (a.ff || b.ff) := by cases a; rfl
@[simp] theorem AVal.join_str : (a.join b).str = (a.str || b.str) := by cases a; rfl
@[simp] theorem AVal.join_strs : (a.join b).strs = joinStrs a b := by cases a; rfl
@[simp] theorem AVal.join_nk : (a.join b).nk = joinNk a b := by cases a; rfl
@[simp] theorem AVal.join_list : (a.join b).list = (a.list || b.list) := by cases a; rfl
@[simp] theorem AVal.join_elems : (a.join b).elems =
    if !a.list then b.elems else if !b.list then a.elems else AVal.joinE a.elems b.elems := by
  cases a; rfl
@[simp] theorem AVal.join_card : (a.join b).card =
    if !a.list then b.card else if !b.list then a.card else a.card.join b.card := by
  cases a; rfl
@[simp] theorem AVal.join_struct : (a.join b).struct = (a.struct || b.struct) := by cases a; rfl
@[simp] theorem AVal.join_fields : (a.join b).fields =
    if !a.struct then b.fields else if !b.struct then a.fields else AVal.joinF a.fields b.fields := by
  cases a; rfl
end

/-- May be a list or a struct. -/
def AVal.nested (a : AVal) : Bool := a.list || a.struct
/-- Admits numbers and NULL only: no booleans, strings, lists or structs. -/
def AVal.intsOnly (a : AVal) : Bool := !a.tt && !a.ff && !a.str && !a.nested
/-- May be something other than a (non-NULL) integer. -/
def AVal.nonInt (a : AVal) : Bool := a.null || a.tt || a.ff || a.str || a.nested
/-- May be something other than a (non-NULL) number of kind `k`: a function of
`k` gives NULL there (#923). -/
def AVal.nonNum (k : NumKind) (a : AVal) : Bool := a.nonInt || (a.int.isSome && a.nk != some k)
/-- May be something other than a (non-NULL) boolean. -/
def AVal.nonBool (a : AVal) : Bool := a.null || a.int.isSome || a.str || a.nested
/-- May be something other than a (non-NULL) list: a function of lists gives
NULL there. -/
def AVal.nonList (a : AVal) : Bool := a.null || a.int.isSome || a.tt || a.ff || a.str || a.struct
/-- May be something other than a (non-NULL) struct. -/
def AVal.nonStruct (a : AVal) : Bool := a.null || a.int.isSome || a.tt || a.ff || a.str || a.list

/-- Certainly TRUE: the only value a satisfied condition can have. -/
def AVal.certainlyTrue (a : AVal) : Bool :=
  !a.null && a.int.isNone && !a.ff && !a.str && !a.nested

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
  | .list _ | .struct _ => by simp [AVal.Mem, AVal.top, Bound.mem_top]
  | .int i | .date i | .ts i | .tod i | .dec _ i => ⟨_, rfl, Bound.mem_top i, rfl⟩
  | .float i => ⟨_, rfl, Bound.mem_top _, rfl⟩

/-- A list in `a` has its elements in `a.elemsOf`. -/
theorem AVal.mem_list {a : AVal} {vs : List Value} :
    a.Mem (.list vs) ↔ a.list = true ∧ a.card.Mem vs.length ∧ ∀ v ∈ vs, a.elemsOf.Mem v := by
  cases he : a.elems with
  | some e =>
    have : a.Mem (.list vs) ↔ a.list = true ∧ a.card.Mem vs.length ∧ AVal.MemAll e vs := by
      simp only [AVal.Mem, AVal.MemR, he]
    rw [this, AVal.memAll_iff, AVal.elemsOf, he]; rfl
  | none =>
    have : a.Mem (.list vs) ↔ a.list = true ∧ a.card.Mem vs.length ∧ True := by
      simp only [AVal.Mem, AVal.MemR, he]
    rw [this, AVal.elemsOf, he]; simp [AVal.mem_top]

theorem AVal.mem_ofValue : ∀ v, (AVal.ofValue v).Mem v
  | .null | .bool true | .bool false => rfl
  | .str s => by simp [AVal.Mem, AVal.ofValue]
  | .list _ => by simp [AVal.Mem, AVal.ofValue, Bound.mem_exact]
  | .struct _ => by simp [AVal.Mem, AVal.ofValue]
  | .int i | .date i | .ts i | .tod i | .dec _ i =>
    ⟨_, rfl, Bound.mem_exact i, by simp [AVal.ofValue, AVal.num]⟩
  | .float i => ⟨_, rfl, Bound.mem_exact _, by simp [AVal.ofValue, AVal.num]⟩

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
  | none => exact ⟨x, by simp [hx, hb, joinInt], hm, by simpa using hk⟩
  | some y => exact ⟨x.join y, by simp [hx, hb, joinInt], Bound.mem_join_left hm, by simpa using hk⟩

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
  | none => exact ⟨y, by simp [hy, ha, joinInt], hm, by simpa using hk⟩
  | some x => exact ⟨x.join y, by simp [hy, ha, joinInt], Bound.mem_join_right hm, by simpa using hk⟩

mutual
theorem AVal.mem_join_left {a b : AVal} : ∀ {v}, a.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at h
      simp only [AVal.Mem, AVal.MemR, AVal.join_str, AVal.join_strs, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨.inl h.1, joinStrs_left h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
      simp_all [AVal.Mem]
  | .list vs, ⟨hl, hc, he⟩ => by
      refine ⟨by simp [hl], ?_, ?_⟩
      · cases hb : b.list <;> simp [hl, hb, hc, Bound.mem_join_left hc]
      · cases hb : b.list
        · simpa [hl, hb] using he
        · simp only [AVal.join_elems, hl, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hA : a.elems <;> cases hB : b.elems <;> simp only [hA, AVal.joinE] at he ⊢
          exact AVal.memAll_join_left he
  | .struct vs, ⟨hs, hf⟩ => by
      refine ⟨by simp [hs], ?_⟩
      cases hb : b.struct
      · simpa [hs, hb] using hf
      · simp only [AVal.join_fields, hs, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hA : a.fields <;> cases hB : b.fields <;> simp only [hA, AVal.joinF] at hf ⊢
        cases hj : AVal.joinL _ _ with
        | none => trivial
        | some zs => exact AVal.memFields_join_left hf hj
  | .int _, h | .float _, h | .date _, h | .ts _, h | .tod _, h | .dec _ _, h =>
      AVal.memNum_join_left h

theorem AVal.memAll_join_left {x y : AVal} : ∀ {vs}, AVal.MemAll x vs → AVal.MemAll (x.join y) vs
  | [], _ => trivial
  | _ :: _, ⟨h, hs⟩ => ⟨AVal.mem_join_left h, AVal.memAll_join_left hs⟩

theorem AVal.memFields_join_left {xs ys zs : List AVal} : ∀ {vs}, AVal.MemFields xs vs →
    AVal.joinL xs ys = some zs → AVal.MemFields zs vs
  | [], h, hj => by
      cases xs <;> cases ys <;> simp_all [AVal.MemFields, AVal.joinL]
  | v :: vs, h, hj => by
      match xs, ys, h, hj with
      | x :: xs, y :: ys, ⟨hx, hxs⟩, hj =>
        simp only [AVal.joinL, Option.map_eq_some_iff] at hj
        obtain ⟨zs', hz, rfl⟩ := hj
        exact ⟨AVal.mem_join_left hx, AVal.memFields_join_left hxs hz⟩
      | [], _, h, _ => exact h.elim
      | _ :: _, [], _, hj => simp [AVal.joinL] at hj
end

mutual
theorem AVal.mem_join_right {a b : AVal} : ∀ {v}, b.Mem v → (a.join b).Mem v
  | .str _, h => by
      simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at h
      simp only [AVal.Mem, AVal.MemR, AVal.join_str, AVal.join_strs, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨.inr h.1, joinStrs_right h.1 h.2⟩
  | .null, h | .bool true, h | .bool false, h => by
      simp_all [AVal.Mem]
  | .list vs, ⟨hl, hc, he⟩ => by
      refine ⟨by simp [hl], ?_, ?_⟩
      · cases ha : a.list <;> simp [hl, ha, hc, Bound.mem_join_right hc]
      · cases ha : a.list
        · simpa [hl, ha] using he
        · simp only [AVal.join_elems, hl, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hA : a.elems <;> cases hB : b.elems <;> simp only [hB, AVal.joinE] at he ⊢
          exact AVal.memAll_join_right he
  | .struct vs, ⟨hs, hf⟩ => by
      refine ⟨by simp [hs], ?_⟩
      cases ha : a.struct
      · simpa [hs, ha] using hf
      · simp only [AVal.join_fields, hs, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hA : a.fields <;> cases hB : b.fields <;> simp only [hB, AVal.joinF] at hf ⊢
        cases hj : AVal.joinL _ _ with
        | none => trivial
        | some zs => exact AVal.memFields_join_right hf hj
  | .int _, h | .float _, h | .date _, h | .ts _, h | .tod _, h | .dec _ _, h =>
      AVal.memNum_join_right h

theorem AVal.memAll_join_right {x y : AVal} : ∀ {vs}, AVal.MemAll y vs → AVal.MemAll (x.join y) vs
  | [], _ => trivial
  | _ :: _, ⟨h, hs⟩ => ⟨AVal.mem_join_right h, AVal.memAll_join_right hs⟩

theorem AVal.memFields_join_right {xs ys zs : List AVal} : ∀ {vs}, AVal.MemFields ys vs →
    AVal.joinL xs ys = some zs → AVal.MemFields zs vs
  | [], h, hj => by
      cases xs <;> cases ys <;> simp_all [AVal.MemFields, AVal.joinL]
  | v :: vs, h, hj => by
      match xs, ys, h, hj with
      | x :: xs, y :: ys, ⟨hy, hys⟩, hj =>
        simp only [AVal.joinL, Option.map_eq_some_iff] at hj
        obtain ⟨zs', hz, rfl⟩ := hj
        exact ⟨AVal.mem_join_right hy, AVal.memFields_join_right hys hz⟩
      | _, [], h, _ => exact h.elim
      | [], _ :: _, _, hj => simp [AVal.joinL] at hj
end

theorem AVal.certainlyTrue_mem {a : AVal} {v : Value} (hc : a.certainlyTrue = true)
    (hm : a.Mem v) : v = .bool true := by
  simp only [AVal.certainlyTrue, AVal.nested, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, Bool.or_eq_false_iff] at hc
  obtain ⟨⟨⟨⟨hn, hi⟩, hf⟩, hs⟩, hl, hst⟩ := hc
  match v, hm with
  | .null, hm => simp_all [AVal.Mem]
  | .int _, ⟨_, hb, _⟩ | .float _, ⟨_, hb, _⟩ | .date _, ⟨_, hb, _⟩ | .ts _, ⟨_, hb, _⟩
  | .tod _, ⟨_, hb, _⟩ | .dec _ _, ⟨_, hb, _⟩ => simp_all
  | .bool true, _ => rfl
  | .bool false, hm => simp_all [AVal.Mem]
  | .str _, hm => simp_all [AVal.Mem]
  | .list _, hm | .struct _, hm => simp_all [AVal.Mem]

/-- Shapes of a value, for case analysis in the binary soundness proofs. A
list or a struct is one case: functions of scalars give NULL on both. -/
theorem AVal.mem_cases {a : AVal} {v : Value} (h : a.Mem v) :
    (v = .null ∧ a.null = true) ∨
    (∃ k i b, v = k.val i ∧ a.int = some b ∧ b.Mem (k.norm i) ∧ a.nk.all (· == k) = true) ∨
    (v = .bool true ∧ a.tt = true) ∨ (v = .bool false ∧ a.ff = true) ∨
    (∃ s, v = .str s ∧ a.str = true ∧ a.strs.all (·.contains s) = true) ∨
    (∃ vs, (v = .list vs ∨ v = .struct vs) ∧ a.nested = true) := by
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
      simp only [AVal.Mem, AVal.MemR, Bool.and_eq_true] at h
      exact .inr (.inr (.inr (.inr (.inl ⟨s, rfl, h⟩))))
  | .list vs, h => exact .inr (.inr (.inr (.inr (.inr ⟨vs, .inl rfl, by simp [AVal.nested, h.1]⟩))))
  | .struct vs, h =>
      exact .inr (.inr (.inr (.inr (.inr ⟨vs, .inr rfl, by simp [AVal.nested, h.1]⟩))))

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
  | some (k, c) =>
    if ok k then (match g (k.norm c) with | some r => (kout k).val r | none => .null) else .null
  | none => .null

/-- A function of two numbers: `g` on numbers of kinds `tbl` takes, of the
kind it gives; NULL elsewhere and where `g` has no value. -/
def Value.mapP₂ (tbl : NumKind → NumKind → Option NumKind) (g : Int → Int → Option Int)
    (v w : Value) : Value :=
  match v.numOf?, w.numOf? with
  | some (k, x), some (k', y) =>
    match tbl k k', g (k.norm x) (k'.norm y) with
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
NULL where the argument may be of another kind or `extra` says `g` may fail.
Irreducible, as is `mapAbs₂`, so that unification matches a function's
abstraction (`UnFn.abs`) with it by its arguments: it does not try them first
for a definition that is a structure instance. -/
@[irreducible] def mapAbs (ok : NumKind → Bool) (kout : NumKind → NumKind) (bf : Bound → Bound)
    (extra : Option Bound → Bool) (a : AVal) : AVal :=
  { null := a.nonNumP ok || extra a.int, int := a.int.map bf, nk := a.nk.map kout }

/-- Two values that are equal, or two doubles of one canonical code: an
operation on raw doubles and its abstraction on canonical ones agree up to
`canon` (D31). -/
def Value.CanonEq (x y : Value) : Prop :=
  x = y ∨ ∃ c c', x = .float c ∧ y = .float c' ∧ FloatCode.canon c = FloatCode.canon c'

/-- Two values that are equal, or two numbers of one kind. -/
def Value.ShapeEq (x y : Value) : Prop := x = y ∨ ∃ (k : NumKind) (c c' : Int), x = k.val c ∧ y = k.val c'

theorem Value.ShapeEq.trans {x y z : Value} (h : x.ShapeEq y) (h' : y.ShapeEq z) : x.ShapeEq z := by
  rcases h with rfl | ⟨k, c, c', rfl, rfl⟩
  · exact h'
  · rcases h' with rfl | ⟨k', d, d', e, rfl⟩
    · exact .inr ⟨k, c, c', rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := NumKind.val_inj₂ e
      exact .inr ⟨k, c, d', rfl, rfl⟩

/-- `a` holds a double by its canonical code (`NumKind.norm`). -/
theorem AVal.mem_of_canonEq {a : AVal} {x y : Value} (h : x.CanonEq y) (hy : a.Mem y) : a.Mem x := by
  rcases h with rfl | ⟨c, c', rfl, rfl, hc⟩
  · exact hy
  · have hy' : a.MemNum .float c' := hy
    obtain ⟨b, hb, hm, hk⟩ := hy'
    show a.MemNum .float c
    refine ⟨b, hb, ?_, hk⟩
    rw [NumKind.norm_float] at hm ⊢; rw [hc]; exact hm

/-- Where `a` bounds no number, any number of `a`'s kinds is in it. -/
theorem AVal.mem_of_shapeEq {a : AVal} {x y : Value} (h : x.ShapeEq y) (hy : a.Mem y)
    (htop : ∀ b, a.int = some b → b = Bound.top) : a.Mem x := by
  rcases h with rfl | ⟨k, c, c', rfl, rfl⟩
  · exact hy
  · obtain ⟨b, hb, _, hk⟩ := AVal.mem_val.mp hy
    exact AVal.mem_val.mpr ⟨b, hb, (htop b hb) ▸ Bound.mem_top _, hk⟩

/-- `mapAbs` holds `mapP`'s values. -/
theorem mapAbs_mem {ok : NumKind → Bool} {kout : NumKind → NumKind} {g : Int → Option Int}
    {bf : Bound → Bound} {extra : Option Bound → Bool}
    (hb : ∀ b i r, b.Mem i → g i = some r → (bf b).Mem r)
    (hn : ∀ b i, b.Mem i → g i = none → extra (some b) = true)
    {a : AVal} {v : Value} (h : a.Mem v)
    (hc : ∀ k i r, ok k = true → g (k.norm i) = some r → (kout k).norm r = r := by
      intro k _ _ hk _; cases k <;> first | rfl | exact absurd hk (by decide)) :
    (mapAbs ok kout bf extra a).Mem (Value.mapP ok kout g v) := by
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
      cases hg : g (k.norm i) with
      | some r =>
        simp only []
        rw [AVal.mem_val]
        refine ⟨bf b, by simp [mapAbs, hb'], by rw [hc k i r hok hg]; exact hb b _ r hi hg, ?_⟩
        cases hnk : a.nk with
        | none => simp [mapAbs, hnk]
        | some k' =>
          simp only [hnk, Option.all_some, beq_iff_eq] at hk
          subst hk; simp [mapAbs, hnk]
      | none =>
        show (mapAbs ok kout bf extra a).null = true
        simp [mapAbs, hb', hn b _ hi hg]
  all_goals (clear hc; simp_all [Value.mapP, Value.numOf?, mapAbs, AVal.Mem, AVal.nonNumP, AVal.nonInt])

/-- **A function of one number is sound by its abstraction** where it agrees
with `mapP` up to `canon` (`Value.CanonEq`): it runs on raw doubles, `mapP`
on canonical ones (D31). -/
theorem mapAbs_sound {ok : NumKind → Bool} {kout : NumKind → NumKind} {g : Int → Option Int}
    {bf : Bound → Bound} {extra : Option Bound → Bool} {f : UnFn}
    (hf : ∀ v, (f.apply v).CanonEq (Value.mapP ok kout g v))
    (hb : ∀ b i r, b.Mem i → g i = some r → (bf b).Mem r)
    (hn : ∀ b i, b.Mem i → g i = none → extra (some b) = true)
    {a : AVal} {v : Value} (h : a.Mem v)
    (hc : ∀ k i r, ok k = true → g (k.norm i) = some r → (kout k).norm r = r := by
      intro k _ _ hk _; cases k <;> first | rfl | exact absurd hk (by decide)) :
    (mapAbs ok kout bf extra a).Mem (f.apply v) :=
  AVal.mem_of_canonEq (hf v) (mapAbs_mem hb hn h hc)

/-- **A function whose abstraction bounds no double** is sound where it agrees
with `mapP` in shape only (`Value.ShapeEq`: NULL where it is NULL, a double
where it is a double). The functions of native doubles (`ROUND(x, d)`, the
elementary functions, `power`, `atan2`, `log`) need it: their values on
`-0.0` are the native library's, which the kernel cannot compute, and an
abstraction that bounds them by `Bound.top` claims nothing about them. -/
theorem mapP_shapeEq (ok : NumKind → Bool) (kout : NumKind → NumKind) (g : Int → Option Int) (v : Value) :
    (Value.mapP ok kout g v).ShapeEq (Value.mapP ok kout (fun i => (g i).map fun _ => 0) v) := by
  unfold Value.mapP
  cases v.numOf? with
  | none => exact .inl rfl
  | some p =>
    obtain ⟨k, c⟩ := p
    simp only []
    split
    · cases g (k.norm c) with
      | none => exact .inl rfl
      | some r => exact .inr ⟨kout k, r, 0, rfl, rfl⟩
    · exact .inl rfl

theorem mapAbs_top_sound {ok : NumKind → Bool} {kout : NumKind → NumKind} {g : Int → Option Int}
    {extra : Option Bound → Bool} {f : UnFn}
    (hf : ∀ v, (f.apply v).ShapeEq (Value.mapP ok kout g v))
    (hn : ∀ b i, b.Mem i → g i = none → extra (some b) = true)
    {a : AVal} {v : Value} (h : a.Mem v) :
    (mapAbs ok kout (fun _ => Bound.top) extra a).Mem (f.apply v) :=
  AVal.mem_of_shapeEq ((hf v).trans (mapP_shapeEq ok kout g v))
    (mapAbs_mem (g := fun i => (g i).map fun _ => 0) (fun _ _ _ _ _ => Bound.mem_top _)
      (fun b i hi hn' => hn b i hi (by cases hg : g i <;> simp_all))
      h (fun k i r _ hr => by
        cases hg : g (k.norm i) <;> simp only [hg, Option.map_none, Option.map_some,
          reduceCtorEq, Option.some.injEq] at hr
        subst hr; cases kout k <;> first | rfl | exact FloatCode.canon_zero))
    (fun b hb => by
      simp only [mapAbs] at hb
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hb; rfl)

/-- The kind of a function of two numbers of kinds `a.nk` and `b.nk`. -/
def outKind (tbl : NumKind → NumKind → Option NumKind) (a b : AVal) : Option NumKind :=
  match a.nk, b.nk with
  | some ka, some kb => tbl ka kb
  | _, _ => none

/-- The abstraction of `Value.mapP₂`: `bf` of the intervals, of the table's
kind, NULL where an argument may be of another kind or `extra` says `g` may
fail. -/
@[irreducible] def mapAbs₂ (tbl : NumKind → NumKind → Option NumKind) (bf : Bound → Bound → Bound)
    (extra : Option Bound → Option Bound → Bool) (a b : AVal) : AVal :=
  { null := a.nonInt || b.nonInt || extra a.int b.int ||
      (a.int.isSome && b.int.isSome && (outKind tbl a b).isNone),
    int := (match a.int, b.int with | some x, some y => some (bf x y) | _, _ => none),
    nk := outKind tbl a b }

theorem mapAbs₂_mem {tbl : NumKind → NumKind → Option NumKind} {g : Int → Int → Option Int}
    {bf : Bound → Bound → Bound} {extra : Option Bound → Option Bound → Bool}
    (hb : ∀ x y i j r, x.Mem i → y.Mem j → g i j = some r → (bf x y).Mem r)
    (hn : ∀ x y (k k' ko : NumKind) i j, tbl k k' = some ko → x.Mem (k.norm i) → y.Mem (k'.norm j) →
      g (k.norm i) (k'.norm j) = none → extra (some x) (some y) = true)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb' : b.Mem w)
    (hc : ∀ k k' ko i j r, tbl k k' = some ko → g (k.norm i) (k'.norm j) = some r → ko.norm r = r := by
      intro k k' ko _ _ _ h _
      cases ko <;> first | rfl | (cases k <;> cases k' <;> cases h)) :
    (mapAbs₂ tbl bf extra a b).Mem (Value.mapP₂ tbl g v w) := by
  mem_cases₂ ha hb'
  case inr.inl.inr.inl =>
    simp only [Value.mapP₂, NumKind.numOf?_val]
    cases hout : outKind tbl a b with
    | none =>
      cases htb : tbl k k' <;> cases hg : g (k.norm i) (k'.norm j) <;> simp only []
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hout]
      · rename_i ko r
        rw [AVal.mem_val]
        exact ⟨bf x y, by simp [mapAbs₂, hx, hy], by rw [hc k k' ko i j r htb hg]; exact hb x y _ _ r hi hj hg,
          by simp [mapAbs₂, hout]⟩
    | some ko =>
      have hko : tbl k k' = some ko := by
        unfold outKind at hout
        cases hka : a.nk <;> cases hkb : b.nk <;> simp only [hka, hkb, reduceCtorEq] at hout
        rename_i ka kb
        simp only [hka, Option.all_some, beq_iff_eq] at hk
        simp only [hkb, Option.all_some, beq_iff_eq] at hk'
        subst hk hk'; exact hout
      simp only [hko]
      cases hg : g (k.norm i) (k'.norm j) with
      | some r =>
        simp only []
        rw [AVal.mem_val]
        exact ⟨bf x y, by simp [mapAbs₂, hx, hy], by rw [hc k k' ko i j r hko hg]; exact hb x y _ _ r hi hj hg,
          by simp [mapAbs₂, hout]⟩
      | none =>
        show (mapAbs₂ tbl bf extra a b).null = true
        simp [mapAbs₂, hx, hy, hn x y k k' ko i j hko hi hj hg]
  all_goals (clear hc; simp_all [Value.mapP₂, Value.numOf?, mapAbs₂, AVal.Mem, AVal.nonInt])

/-- `mapAbs_sound` for a function of two numbers. -/
theorem mapAbs₂_sound {tbl : NumKind → NumKind → Option NumKind} {g : Int → Int → Option Int}
    {bf : Bound → Bound → Bound} {extra : Option Bound → Option Bound → Bool} {f : BinFn}
    (hf : ∀ v w, (f.apply v w).CanonEq (Value.mapP₂ tbl g v w))
    (hb : ∀ x y i j r, x.Mem i → y.Mem j → g i j = some r → (bf x y).Mem r)
    (hn : ∀ x y i j, x.Mem i → y.Mem j → g i j = none → extra (some x) (some y) = true)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb' : b.Mem w)
    (hc : ∀ k k' ko i j r, tbl k k' = some ko → g (k.norm i) (k'.norm j) = some r → ko.norm r = r := by
      intro k k' ko _ _ _ h _
      cases ko <;> first | rfl | (cases k <;> cases k' <;> cases h)) :
    (mapAbs₂ tbl bf extra a b).Mem (f.apply v w) :=
  AVal.mem_of_canonEq (hf v w)
    (mapAbs₂_mem hb (fun x y _ _ _ _ _ _ hi hj hg => hn x y _ _ hi hj hg) ha hb' hc)

theorem mapP₂_shapeEq (tbl : NumKind → NumKind → Option NumKind) (g : Int → Int → Option Int) (v w : Value) :
    (Value.mapP₂ tbl g v w).ShapeEq (Value.mapP₂ tbl (fun i j => (g i j).map fun _ => 0) v w) := by
  unfold Value.mapP₂
  cases v.numOf? with
  | none => exact .inl rfl
  | some p =>
    cases w.numOf? with
    | none => exact .inl rfl
    | some q =>
      obtain ⟨k, c⟩ := p; obtain ⟨k', d⟩ := q
      simp only []
      cases tbl k k' with
      | none => cases g (k.norm c) (k'.norm d) <;> exact .inl rfl
      | some ko =>
        cases g (k.norm c) (k'.norm d) with
        | none => exact .inl rfl
        | some r => exact .inr ⟨ko, r, 0, rfl, rfl⟩

/-- `mapAbs_top_sound` for a function of two numbers. -/
theorem mapAbs₂_top_sound {tbl : NumKind → NumKind → Option NumKind} {g : Int → Int → Option Int}
    {extra : Option Bound → Option Bound → Bool} {f : BinFn}
    (hf : ∀ v w, (f.apply v w).ShapeEq (Value.mapP₂ tbl g v w))
    (hn : ∀ x y (k k' ko : NumKind) i j, tbl k k' = some ko → x.Mem (k.norm i) → y.Mem (k'.norm j) →
      g (k.norm i) (k'.norm j) = none → extra (some x) (some y) = true)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb' : b.Mem w) :
    (mapAbs₂ tbl (fun _ _ => Bound.top) extra a b).Mem (f.apply v w) :=
  AVal.mem_of_shapeEq ((hf v w).trans (mapP₂_shapeEq tbl g v w))
    (mapAbs₂_mem (g := fun i j => (g i j).map fun _ => 0) (fun _ _ _ _ _ _ _ _ => Bound.mem_top _)
      (fun x y k k' ko i j htb hi hj hn' => hn x y k k' ko i j htb hi hj
        (by cases hg : g (k.norm i) (k'.norm j) <;> simp_all))
      ha hb' (fun k k' ko i j r _ hr => by
        cases hg : g (k.norm i) (k'.norm j) <;> simp only [hg, Option.map_none, Option.map_some,
          reduceCtorEq, Option.some.injEq] at hr
        subst hr; cases ko <;> first | rfl | exact FloatCode.canon_zero))
    (fun c hc' => by
      simp only [mapAbs₂] at hc'
      split at hc' <;> simp_all)

/-! ### Membership up to `canon` (D31)

The analysis bounds a double by its canonical code, so `-0.0` and `0.0`, and
the two NaNs, are in the same abstract values, in lists and structs too. -/

theorem Value.canonV_float (c : Int) : (Value.float c).canonV = .float (FloatCode.canon c) := by
  simp only [Value.canonV]
theorem Value.canonV_list (vs : List Value) : (Value.list vs).canonV = .list (vs.map Value.canonV) := by
  simp only [Value.canonV]
theorem Value.canonV_struct (vs : List Value) : (Value.struct vs).canonV = .struct (vs.map Value.canonV) := by
  simp only [Value.canonV]

mutual
theorem AVal.memR_canonV (a : AVal) : ∀ v : Value, a.MemR v.canonV ↔ a.MemR v
  | .float c => by
    rw [Value.canonV_float]
    show a.MemNum .float (FloatCode.canon c) ↔ a.MemNum .float c
    unfold AVal.MemNum
    rw [NumKind.norm_float, NumKind.norm_float, FloatCode.canon_idem]
  | .list vs => by
    rw [Value.canonV_list]
    simp only [AVal.MemR, List.length_map]
    cases a.elems with
    | none => exact Iff.rfl
    | some e => simp only []; rw [AVal.memAll_canonV e vs]
  | .struct vs => by
    rw [Value.canonV_struct]
    simp only [AVal.MemR]
    cases a.fields with
    | none => exact Iff.rfl
    | some fs => simp only []; rw [AVal.memFields_canonV fs vs]
  | .null | .bool _ | .int _ | .date _ | .ts _ | .tod _ | .dec _ _ | .str _ => by
    simp only [Value.canonV]
theorem AVal.memAll_canonV (e : AVal) : ∀ vs : List Value, AVal.MemAll e (vs.map Value.canonV) ↔ AVal.MemAll e vs
  | [] => Iff.rfl
  | v :: vs => by
    simp only [List.map_cons, AVal.MemAll]; rw [AVal.memR_canonV e v, AVal.memAll_canonV e vs]
theorem AVal.memFields_canonV : ∀ (fs : List AVal) (vs : List Value),
    AVal.MemFields fs (vs.map Value.canonV) ↔ AVal.MemFields fs vs
  | [], [] => Iff.rfl
  | f :: fs, v :: vs => by
    simp only [List.map_cons, AVal.MemFields]; rw [AVal.memR_canonV f v, AVal.memFields_canonV fs vs]
  | [], _ :: _ | _ :: _, [] => by simp [AVal.MemFields]
end


theorem Value.canonV_eq_null {v : Value} : v.canonV = .null ↔ v = .null := by
  cases v <;> simp [Value.canonV]

theorem AVal.mem_canonV {a : AVal} {v : Value} : a.Mem v.canonV ↔ a.Mem v := AVal.memR_canonV a v

theorem AVal.mem_of_canonV_eq {a : AVal} {v w : Value} (h : v.canonV = w.canonV) (hw : a.Mem w) :
    a.Mem v := AVal.mem_canonV.mp (h ▸ AVal.mem_canonV.mpr hw)

end Substrait
