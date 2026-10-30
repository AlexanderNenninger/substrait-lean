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
  if 0 ≤ k then ⟨b.lo.map (k * ·), b.hi.map (k * ·)⟩ else ⟨b.hi.map (k * ·), b.lo.map (k * ·)⟩

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
  · rename_i hk
    refine ⟨fun l h => ?_, fun u h => ?_⟩
    · obtain ⟨l0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonneg_left (hl l0 h0) hk
    · obtain ⟨u0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Int.mul_le_mul_of_nonneg_left (hh u0 h0) hk
  · rename_i hk
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
  | .eq, a, b =>
      let same := (a.int.isSome && b.int.isSome) || ((a.tt || a.ff) && (b.tt || b.ff)) ||
        (a.str && b.str)
      let mismatch := a.null || b.null || (a.int.isSome && (b.tt || b.ff || b.str)) ||
        ((a.tt || a.ff) && (b.int.isSome || b.str)) || (a.str && (b.int.isSome || b.tt || b.ff))
      ⟨mismatch, none, same, same, false⟩
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
        simp_all [UnFn.abs, UnFn.apply, AVal.Mem, AVal.nonBool, AVal.nonInt, Bound.mem_neg]
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

theorem BinFn.abs_sound (f : BinFn) {a b : AVal} {v w : Value} (ha : a.Mem v) (hb : b.Mem w) :
    (f.abs a b).Mem (f.apply v w) := by
  cases f
  case add => exact arith_sound Bound.mem_add (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case sub => exact arith_sound Bound.mem_sub (fun v w => by cases v <;> cases w <;> rfl) ha hb
  case mul => exact arith_sound Bound.mem_mul (fun v w => by cases v <;> cases w <;> rfl) ha hb
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
  | _ => env

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

theorem nonNullInt_mem {a : AVal} {x : Int} {f : Bound → Bound} (h : a.Mem (.int x))
    (hf : ∀ b, b.Mem x → (f b).Mem x) : (a.nonNullInt f).Mem (.int x) := by
  obtain ⟨b, hb, hm⟩ := h
  exact ⟨f b, by simp [AVal.nonNullInt, hb], hf b hm⟩

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
  case case8 => exact h

/-! ## Abstract plan evaluation -/

/-- Exactly `n` columns: missing ones are unknown. -/
def fit (n : Nat) (env : List AVal) : List AVal := (List.range n).map (env.getD · AVal.top)

def AVal.nullable (a : AVal) : AVal := { a with null := true }

def Rel.aeval (cat : Catalog) (A : String → List AVal) : Rel → List AVal
  | .read t => fit (cat t).arity (A t)
  | .values n _ => List.replicate n AVal.top
  | .filter r c => c.refine (r.aeval cat A)
  | .project r es => r.aeval cat A ++ es.map (·.abs (r.aeval cat A))
  | .emit r m => m.map ((r.aeval cat A).getD · AVal.top)
  | .cross a b => a.aeval cat A ++ b.aeval cat A
  | .join a b .inner on => on.refine (a.aeval cat A ++ b.aeval cat A)
  | .join a b .left _ => a.aeval cat A ++ (b.aeval cat A).map AVal.nullable
  | .fetch r _ _ => r.aeval cat A
  | .unionAll a b => List.zipWith AVal.join (a.aeval cat A) (b.aeval cat A)

theorem Rel.aeval_length {cat : Catalog} {A : String → List AVal} :
    ∀ {r : Rel}, r.WF cat → (r.aeval cat A).length = r.arity cat
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
theorem Rel.aeval_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row) :
    ∀ {r : Rel}, r.WF cat → ∀ row ∈ r.eval cat, EnvMem (r.aeval cat A) row
  | .read t, _, row, h => (hA t row h).fit _
  | .values _ _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact Expr.refine_sound _ c (aeval_sound hcat hA hwf.1 row h.1) h.2
  | .project r es, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hm := aeval_sound hcat hA hwf.1 x hx
      exact hm.append (hm.map es) (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .emit r m, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (aeval_sound hcat hA hwf.1 x hx).emit m
  | .cross a b, hwf, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      exact (aeval_sound hcat hA hwf.1 x hx).append (aeval_sound hcat hA hwf.2 y hy)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .join a b .inner on, hwf, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, ht⟩ := h
      exact Expr.refine_sound _ on ((aeval_sound hcat hA hwf.1 x hx).append
        (aeval_sound hcat hA hwf.2.1 y hy) (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])) ht
  | .join a b .left on, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxm := aeval_sound hcat hA hwf.1 x hx
      have hl : (a.aeval cat A).length = x.length := by
        rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hxm.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        exact hxm.append (aeval_sound hcat hA hwf.2.1 y hy).nullable hl
  | .fetch r _ _, hwf, row, h => by
      simp only [eval] at h
      have := aeval_sound hcat hA (r := r) hwf
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .unionAll a b, hwf, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact (aeval_sound hcat hA hwf.1 row h).zip_left
      · exact (aeval_sound hcat hA hwf.2.1 row h).zip_right

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
  | .fetch _ _ _, _, _, h | .unionAll _ _, _, _, h => by simp [colExprs] at h

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
    (hQ : Q.WF cat)
    (hproved : (Q.aeval cat fun t => tableEnv (S t) (pre t)).all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true := by
  intro row hrow v hv
  have hm := Q.aeval_sound hcat (fun t row h => tableEnv_sound (hS t row h) (hpre t row h)) hQ row hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : j < (Q.aeval cat fun t => tableEnv (S t) (pre t)).length := by
    rw [Rel.aeval_length hQ, ← Rel.eval_arity hcat hQ row hrow]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen)
  have := hm j
  simp only [List.getElem?_eq_getElem hlen, Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

end Substrait
