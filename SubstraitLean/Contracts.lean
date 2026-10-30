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

/-- Multiplication is only tracked when one side is a constant. -/
def Bound.mul (a b : Bound) : Bound :=
  match a.point, b.point with
  | some k, _ => b.scale k
  | none, some k => a.scale k
  | none, none => Bound.top

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

theorem Bound.mem_mul {a b : Bound} {x y : Int} (ha : a.Mem x) (hb : b.Mem y) :
    (a.mul b).Mem (x * y) := by
  unfold Bound.mul
  match hpa : a.point, hpb : b.point with
  | some k, _ => simp only []; rw [Bound.point_mem hpa ha]; exact Bound.mem_scale k hb
  | none, some k =>
    simp only []; rw [Bound.point_mem hpb hb, Int.mul_comm]; exact Bound.mem_scale k ha
  | none, none => exact Bound.mem_top _

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

def AVal.top : AVal := ⟨true, some Bound.top, true, true, true⟩
def AVal.bot : AVal := ⟨false, none, false, false, false⟩

def AVal.ofValue : Value → AVal
  | .null => ⟨true, none, false, false, false⟩
  | .int i => ⟨false, some (.exact i), false, false, false⟩
  | .bool true => ⟨false, none, true, false, false⟩
  | .bool false => ⟨false, none, false, true, false⟩
  | .str _ => ⟨false, none, false, false, true⟩

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
  | .int i => ⟨_, rfl, Bound.mem_top i⟩

theorem AVal.mem_ofValue : ∀ v, (AVal.ofValue v).Mem v
  | .null | .bool true | .bool false | .str _ => rfl
  | .int i => ⟨_, rfl, Bound.mem_exact i⟩

theorem AVal.mem_join_left {a b : AVal} : ∀ {v}, a.Mem v → (a.join b).Mem v
  | .null, h | .bool true, h | .bool false, h | .str _, h => by
      simp_all [AVal.Mem, AVal.join]
  | .int i, ⟨x, hx, hm⟩ => by
      simp only [AVal.Mem, AVal.join, hx]
      cases b.int <;> simp [joinInt, hm, Bound.mem_join_left hm]

theorem AVal.mem_join_right {a b : AVal} : ∀ {v}, b.Mem v → (a.join b).Mem v
  | .null, h | .bool true, h | .bool false, h | .str _, h => by
      simp_all [AVal.Mem, AVal.join]
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
  | .str _, hm => simp_all [AVal.Mem]

/-! ## Abstract expression evaluation -/

def UnFn.abs : UnFn → AVal → AVal
  | .not, a => ⟨a.nonBool, none, a.ff, a.tt, false⟩
  | .isNull, a => ⟨false, none, a.null, a.int.isSome || a.tt || a.ff || a.str, false⟩
  | .neg, a => ⟨a.nonInt, a.int.map Bound.neg, false, false, false⟩
  -- Float results: some double (any code), or NULL.
  | .itof, a | .fneg, a => ⟨a.nonInt, a.int.map fun _ => Bound.top, false, false, false⟩

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
  | .fadd, a, b | .fsub, a, b | .fmul, a, b | .fdiv, a, b => arith (fun _ _ => Bound.top) a b
  | .eq, a, b =>
      let mismatch := a.null || b.null || (a.int.isSome && (b.tt || b.ff || b.str)) ||
        ((a.tt || a.ff) && (b.int.isSome || b.str)) || (a.str && (b.int.isSome || b.tt || b.ff))
      ⟨mismatch, none,
       intEq a b || (a.tt && b.tt) || (a.ff && b.ff) || (a.str && b.str),
       intNe a b || (a.tt && b.ff) || (a.ff && b.tt) || (a.str && b.str), false⟩
  | .lt, a, b =>
      match a.int, b.int with
      | some x, some y => ⟨a.nonInt || b.nonInt, none, canLt x y, canGe x y, false⟩
      | _, _ => ⟨true, none, false, false, false⟩

def Expr.abs (env : List AVal) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => env.getD i AVal.top
  | .un f a => f.abs (a.abs env)
  | .bin f a b => f.abs (a.abs env) (b.abs env)
  | .ifThen c t e =>
      let ac := c.abs env
      (if ac.tt then t.abs env else AVal.bot).join
        (if ac.nonBool || ac.ff then e.abs env else AVal.bot)

theorem UnFn.abs_sound (f : UnFn) {a : AVal} {v : Value} (h : a.Mem v) :
    (f.abs a).Mem (f.apply v) := by
  cases f <;> match v, h with
    | .null, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .int i, ⟨b, hb, hm⟩ =>
        simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt, Bound.mem_neg,
          Bound.mem_top]
    | .bool true, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .bool false, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]
    | .str _, h => simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt]

/-- Shapes of a value, for case analysis in the binary soundness proofs. -/
theorem mem_cases {a : AVal} {v : Value} (h : a.Mem v) :
    (v = .null ∧ a.null = true) ∨ (∃ i b, v = .int i ∧ a.int = some b ∧ b.Mem i) ∨
    (v = .bool true ∧ a.tt = true) ∨ (v = .bool false ∧ a.ff = true) ∨
    (∃ s, v = .str s ∧ a.str = true) := by
  match v, h with
  | .null, h => exact .inl ⟨rfl, h⟩
  | .int i, ⟨b, hb, hm⟩ => exact .inr (.inl ⟨i, b, rfl, hb, hm⟩)
  | .bool true, h => exact .inr (.inr (.inl ⟨rfl, h⟩))
  | .bool false, h => exact .inr (.inr (.inr (.inl ⟨rfl, h⟩)))
  | .str s, h => exact .inr (.inr (.inr (.inr ⟨s, rfl, h⟩)))

theorem arith_sound {op : Bound → Bound → Bound} {f : Int → Int → Int}
    (hop : ∀ {x y : Bound} {i j : Int}, x.Mem i → y.Mem j → (op x y).Mem (f i j))
    {g : BinFn} (hg : ∀ v w, g.apply v w =
      match v, w with | .int i, .int j => .int (f i j) | _, _ => .null)
    {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (arith op a b).Mem (g.apply v w) := by
  rw [hg]
  rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ <;>
  rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨s', rfl, h'⟩ <;>
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
  case eq =>
    rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ <;>
    rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨s', rfl, h'⟩ <;>
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
  all_goals
    rcases mem_cases ha with ⟨rfl, h⟩ | ⟨i, x, rfl, hx, hi⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨s, rfl, h⟩ <;>
    rcases mem_cases hb with ⟨rfl, h'⟩ | ⟨j, y, rfl, hy, hj⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨s', rfl, h'⟩ <;>
    simp_all [BinFn.abs, BinFn.apply, and3, or3, AVal.Mem, AVal.nonBool, AVal.nonInt]
  all_goals (split <;> simp_all [canLt, canGe])
  -- What is left: comparisons of two integers against their intervals.
  all_goals
    obtain ⟨xl, xh⟩ := x
    obtain ⟨yl, yh⟩ := y
    simp only [Bound.Mem] at hi hj
    cases xl <;> cases xh <;> cases yl <;> cases yh <;> simp_all <;> omega

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
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        exact Expr.abs_sound h e

/-! ## Refinement by filter conditions -/

/-- A column known to be a non-NULL integer, with its interval transformed. -/
def AVal.nonNullInt (a : AVal) (f : Bound → Bound) : AVal := ⟨false, a.int.map f, false, false, false⟩

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

def refineCol (env : List AVal) (i : Nat) (f : AVal → AVal) : List AVal :=
  env.set i (f (env.getD i AVal.top))

/-- What a row that makes `e` TRUE satisfies. Recognizes conjunctions,
comparisons of a column with an integer constant, and `IS NOT NULL`. -/
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
  -- Comparing two columns: TRUE only if both are non-NULL integers.
  | .bin .lt (.field i) (.field j) | .un .not (.bin .lt (.field i) (.field j)) =>
      refineCol (refineCol env i (·.nonNullInt id)) j (·.nonNullInt id)
  -- Arithmetic is NULL-propagating: a non-NULL `a - b` has non-NULL operands
  -- (DataFusion inlines computed columns such as `gap = ts - prev_ts`).
  | .un .not (.un .isNull (.bin .add a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
  | .un .not (.un .isNull (.bin .sub a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
  | .un .not (.un .isNull (.bin .mul a b)) =>
      (Expr.un .not (.un .isNull b)).refine ((Expr.un .not (.un .isNull a)).refine env)
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

theorem lt_fields_int {v w : Value} (h : (BinFn.apply .lt v w).isTrue = true) :
    (∃ x, v = .int x) ∧ (∃ y, w = .int y) := by
  cases v <;> cases w <;> simp_all [BinFn.apply, Value.isTrue]

theorem not_lt_fields_int {v w : Value}
    (h : (UnFn.apply .not (BinFn.apply .lt v w)).isTrue = true) :
    (∃ x, v = .int x) ∧ (∃ y, w = .int y) := by
  cases v <;> cases w <;> simp_all [BinFn.apply, UnFn.apply, Value.isTrue]

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
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := lt_fields_int (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := (·.nonNullInt id)) h (by
      have := h i; rw [hx] at this ⊢; exact nonNullInt_mem this fun _ hb => hb)
    refine refineCol_sound h₁ ?_
    have := h₁ j; rw [hy] at this ⊢; exact nonNullInt_mem this fun _ hb => hb
  case case11 env i j =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := not_lt_fields_int (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := (·.nonNullInt id)) h (by
      have := h i; rw [hx] at this ⊢; exact nonNullInt_mem this fun _ hb => hb)
    refine refineCol_sound h₁ ?_
    have := h₁ j; rw [hy] at this ⊢; exact nonNullInt_mem this fun _ hb => hb
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
  case case15 => exact h

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
  | .lt => ltSharpen (termDiff fs a b) base
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

def Expr.absD (env : List AVal) (fs : List Fact) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => env.getD i AVal.top
  | .un f a => f.abs (a.absD env fs)
  | .bin f a b =>
      if f = .or ∧ (a.absD env fs).nonBool = false then
        orSplit (a.absD env fs) (b.absD ((Expr.un .not a).refine env) fs)
      else sharpen fs f a b (a.absD env fs) (f.abs (a.absD env fs) (b.absD env fs))
  | .ifThen c t e =>
      let ac := c.absD env fs
      (if ac.tt then t.absD env fs else AVal.bot).join
        (if ac.nonBool || ac.ff then e.absD env fs else AVal.bot)

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

theorem ltSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .lt (a.eval row) (b.eval row))) :
    (ltSharpen (termDiff fs a b) base).Mem (BinFn.apply .lt (a.eval row) (b.eval row)) := by
  cases hd : termDiff fs a b with
  | none => exact hbase
  | some d =>
    simp only [ltSharpen]
    generalize hva : a.eval row = va at hbase ⊢
    generalize hvb : b.eval row = vb at hbase ⊢
    cases va <;> cases vb <;> simp only [BinFn.apply] at hbase ⊢ <;> try exact hbase
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
  case lt => exact ltSharpen_sound hfs hbase
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

theorem Expr.absD_sound {env : List AVal} {fs : List Fact} {row : Row} (h : EnvMem env row)
    (hfs : FactsHold fs row) : ∀ e : Expr, (e.absD env fs).Mem (e.eval row)
  | .lit v => AVal.mem_ofValue v
  | .field i => h i
  | .un f a => UnFn.abs_sound f (Expr.absD_sound h hfs a)
  | .bin f a b => by
      simp only [absD, eval]
      split
      · rename_i hc
        obtain ⟨rfl, hnb⟩ := hc
        have ha := Expr.absD_sound h hfs a
        rcases mem_cases ha with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩
        · simp [AVal.nonBool, hn] at hnb
        · simp [AVal.nonBool, hb] at hnb
        · rw [hv]
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hr := Expr.refine_sound env (.un .not a) h (by simp [eval, hv, UnFn.apply, Value.isTrue])
          have hq := Expr.absD_sound hr hfs b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ | ⟨_, hv', hs⟩ <;>
            rw [hv'] <;> simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem]
        · simp [AVal.nonBool, hs] at hnb
      · exact sharpen_sound f a b hfs (Expr.absD_sound h hfs a)
          (BinFn.abs_sound f (Expr.absD_sound h hfs a) (Expr.absD_sound h hfs b))
  | .ifThen c t e => by
      have hc := Expr.absD_sound h hfs c
      simp only [absD, eval]
      by_cases hct : (c.eval row).isTrue = true
      · rw [ite_eq_left hct]
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.absD env fs).tt = true := hc
        apply AVal.mem_join_left
        rw [ite_eq_left htt]
        exact Expr.absD_sound h hfs t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.absD env fs).nonBool || (c.absD env fs).ff) = true := by
          rcases mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        exact Expr.absD_sound h hfs e

/-! ## Abstract plan evaluation -/

/-- Exactly `n` columns: missing ones are unknown. -/
def fit (n : Nat) (env : List AVal) : List AVal := (List.range n).map (env.getD · AVal.top)

def AVal.nullable (a : AVal) : AVal := { a with null := true }

/-- `ROW_NUMBER` is a positive integer; `LAG`/`LEAD` read a value of the same
column of another input row, or give the default. -/
def WinFn.abs (env : List AVal) : WinFn → AVal
  | .rowNumber => ⟨false, some ⟨some 1, none⟩, false, false, false⟩
  | .lag c _ d | .lead c _ d => (env.getD c AVal.top).join (AVal.ofValue d)

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
  cases es[j]? <;> simp [AVal.mem_top, Expr.absD_sound h hfs]

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
  | .int _, h | .bool true, h | .bool false, h | .str _, h => h

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
  | .fetch _ _ _, _, _, h | .unionAll _ _, _, _, h | .window _ _ _ _, _, _, h => by
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
