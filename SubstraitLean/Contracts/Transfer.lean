import SubstraitLean.Contracts.Lattice

/-!
# Contracts: Transfer

The transfer functions of abstract expression evaluation: rounding, division and
casts, domains, black boxes, double arithmetic and signs, ending in `UnFn.abs`,
`BinFn.abs` and `Expr.abs`. Their soundness is in `Contracts/TransferSound`.

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

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

/-- Takes numbers of kind `k` only. -/
def NumKind.is (k : NumKind) (k' : NumKind) : Bool := k' == k

/-- A number of kind `kin` by a monotone map to kind `kout` (`FLOOR`, a
date's truncation, ...). -/
def monoAbs (kin kout : NumKind) (g : Int → Int) (a : AVal) : AVal :=
  mapAbs kin.is (fun _ => kout) (·.mapMono g) (fun _ => false) a

/-- A conversion's interval to finite doubles: between the conversions of the
ends, or of `-∞` and `+∞`'s neighbours. -/
def convBound (c : FloatCode.FiniteMonoConv) (b : Bound) : Bound :=
  ⟨some (b.lo.elim (FloatCode.negInf + 1) c.conv), some (b.hi.elim (FloatCode.posInf - 1) c.conv)⟩

/-- A conversion of numbers that `ok` takes to finite doubles, monotone
(`FloatCode.FiniteMonoConv`). -/
def convAbs (ok : NumKind → Bool) (c : FloatCode.FiniteMonoConv) (a : AVal) : AVal :=
  mapAbs ok (fun _ => .float) (convBound c) (fun _ => false) a

/-- `CAST(x AS BIGINT)`'s interval: between the casts of the ends, if both are
finite. -/
def ftoiBound (b : Bound) : Bound :=
  match b with
  | ⟨some lo, some hi⟩ =>
    match FloatCode.toInt? lo, FloatCode.toInt? hi with
    | some x, some y => ⟨some x, some y⟩
    | _, _ => Bound.top
  | _ => Bound.top

/-- May `CAST(x AS BIGINT)` fail on the interval? Unless both ends cast. -/
def ftoiFails : Option Bound → Bool
  | some ⟨some lo, some hi⟩ => (FloatCode.toInt? lo).isNone || (FloatCode.toInt? hi).isNone
  | some _ => true
  | none => false

/-- `CAST(x AS BIGINT)` of a double: between the casts of the ends, if both
are finite; otherwise it may also fail (NULL here). -/
def ftoiAbs (a : AVal) : AVal :=
  mapAbs NumKind.float.is (fun _ => .int) ftoiBound ftoiFails a

/-- `a`, or NULL. -/
def AVal.nullable (a : AVal) : AVal := { a with null := true }

theorem AVal.mem_nullable {a : AVal} : ∀ {v}, a.Mem v → a.nullable.Mem v
  | .null, _ => rfl
  | .int _, h | .float _, h | .date _, h | .ts _, h | .tod _, h | .dec _ _, h
  | .bool true, h | .bool false, h | .str _, h | .list _, h | .struct _, h => h

/-- `CAST(x AS INT)`: the integer itself, or NULL where it may not fit. -/
def narrowAbs (n : Nat) (a : AVal) : AVal :=
  mapAbs NumKind.int.is (fun _ => .int) id
    (fun ob => !ob.all (·.within (-2 ^ (n - 1)) (2 ^ (n - 1) - 1))) a

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

/-- May an integer drawn from the interval be 0? -/
def mayZero (ob : Option Bound) : Bool := ob.all Bound.has0

/-- Division and remainder of numbers of kinds `tbl` takes: NULL for a NULL
operand, and (here) for a zero divisor, where DataFusion fails. -/
def divAbs (tbl : NumKind → NumKind → Option NumKind) (bound : Bound → Bound → Bound)
    (a b : AVal) : AVal :=
  mapAbs₂ tbl bound (fun _ y => mayZero y) a b

/-- Integer powers: `x²` is not negative; the exponent must be in `[0, 64]`
for a result. -/
def powBound (_ y : Bound) : Bound := if y.point == some 2 then ⟨some 0, none⟩ else Bound.top

/-- May the exponent be outside `[0, 64]`? -/
def powFails : Option Bound → Bool
  | some ⟨some l, some h⟩ => !(decide (0 ≤ l) && decide (h ≤ 64))
  | _ => true

def powAbs (a b : AVal) : AVal :=
  mapAbs₂ intsOnly powBound (fun _ y => powFails y) a b

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

/-- `date_part` of a timestamp or a time of day: NULL outside the timestamps
`chrono` represents. -/
def datePartAbs (p : Time.DatePart) (a : AVal) : AVal :=
  mapAbs tsOrTod (fun _ => .int) (partBound p)
    (fun ob => !ob.all (·.within Time.partMin Time.partMax)) a

/-! ## Domains

The elementary functions, `atan2`, `logb` and the shifts are `NULL` (an
error, `Issue.domain`) outside their domains (`SubstraitLean/Numeric.lean`).
Their results are "some double" or "some integer", or `NULL` where an
argument may be outside the domain. -/

/-- Is every double `a` describes in `f`'s domain? -/
def FMath.safe (f : FMath) (a : AVal) : Bool :=
  a.int.all fun b => f.lo?.all b.allGe && f.hi?.all b.allLe

/-- Is every pair of arguments the intervals describe in the function's
domain? -/
def BinFn.domainSafe : BinFn → Option Bound → Option Bound → Bool
  | .fatan2, x, y => x.all (!·.has0) || y.all (!·.has0)
  | .flogb, x, y => x.all (·.allGe 1) && y.all fun y =>
      y.allGe 1 && (y.allGe (FloatCode.one + 1) || y.allLe (FloatCode.one - 1))
  | .bit op, _, y => !op.isShift || y.all fun y => y.allGe 0 && y.allLe 63
  | _, _, _ => true

/-- Some number of the table's kind, or `NULL` unless the arguments are in
`f`'s domain. -/
def partialAbs₂ (tbl : NumKind → NumKind → Option NumKind) (f : BinFn) (a b : AVal) : AVal :=
  mapAbs₂ tbl (fun _ _ => Bound.top) (fun x y => !BinFn.domainSafe f x y) a b

/-- `CAST(x AS DECIMAL(_, s))`'s interval: between the casts of the double's
bounds, where both have a decimal (`FloatCode.toDecimal?_between`, #223). -/
def ftodBound (s : Nat) (b : Bound) : Bound :=
  match b with
  | ⟨some l, some h⟩ =>
    match FloatCode.toDecimal? l s, FloatCode.toDecimal? h s with
    | some x, some y => ⟨some x, some y⟩
    | _, _ => Bound.top
  | _ => Bound.top

/-- May `CAST(x AS DECIMAL(_, s))` fail on the interval? Unless both ends cast. -/
def ftodFails (s : Nat) : Option Bound → Bool
  | some ⟨some l, some h⟩ =>
    (FloatCode.toDecimal? l s).isNone || (FloatCode.toDecimal? h s).isNone
  | some _ => true
  | none => false

def ftodAbs (s : Nat) (a : AVal) : AVal :=
  mapAbs NumKind.float.is (fun _ => .int) (ftodBound s) (ftodFails s) a

/-! ## Black boxes (#325)

What a black box's row declares of its result (`SubstraitLean/BlackBox.lean`):
its type, and its laws, which hold of the model by construction
(`BlackBox.Scalar.call_ok`). -/

def BlackBox.Law.bound : BlackBox.Law → Bound
  | .atLeast k => ⟨some k, none⟩
  | .atMost k => ⟨none, some k⟩
  | .nonNull => Bound.top

/-- The numbers' kind of a black box's result type, where it has one. -/
def BlackBox.Ty.numKind : BlackBox.Ty → Option NumKind
  | .int => some .int
  | .double => some .float
  | .date => some .date
  | .timestamp => some .ts
  | _ => none

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
     result == .strs || result == .any, none, result.numKind⟩

theorem BlackBox.lawsBound_mem {set : Bool} {k : NumKind} {i : Int} :
    ∀ {laws : List BlackBox.Law}, (laws.all fun l => l.holds set (k.val i)) = true →
      (laws.foldr (fun l b => l.bound.meet b) Bound.top).Mem i
  | [], _ => Bound.mem_top i
  | l :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    refine Bound.mem_meet ?_ (lawsBound_mem h.2)
    cases l <;> cases k <;> simp_all [BlackBox.Law.holds, BlackBox.Law.bound, Bound.Mem, Bound.top,
      NumKind.val]

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
  | .int i | .float i | .date i | .ts i | .tod i | .dec _ i =>
    first
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .int) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .float) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .date) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .ts) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .tod) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
      | exact ⟨_, by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has],
          lawsBound_mem (k := .dec _) hl,
          by cases result <;> simp_all [BlackBox.lawsAbs, BlackBox.Ty.has, BlackBox.Ty.numKind]⟩
  | .bool true | .bool false | .str _ =>
    cases result <;> simp_all [AVal.Mem, BlackBox.lawsAbs, BlackBox.Ty.has]
  | .list _ | .struct _ =>
    cases result <;> simp_all [AVal.Mem, BlackBox.lawsAbs, BlackBox.Ty.has]

/-- A scalar black box's result, where no argument is NULL (`set`) or some may be. -/
def BlackBox.scalarAbs (name : String) (set : Bool) : AVal :=
  match BlackBox.scalar? name with
  | some f => BlackBox.lawsAbs f.result f.laws set
  | none => ⟨true, none, false, false, false, none, none⟩

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
  | none => ⟨true, none, false, false, false, none, none⟩

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

/-- The interval of a double function's result where `safe` says the
argument is in its domain: some double. -/
def FMath.safeB (f : FMath) (ob : Option Bound) : Bool :=
  ob.all fun b => f.lo?.all b.allGe && f.hi?.all b.allLe

/-- An integer in `[lo, hi]`. -/
def AVal.intIn (null : Bool) (b : Bound) : AVal := ⟨null, some b, false, false, false, none, some .int⟩

def UnFn.abs : UnFn → AVal → AVal
  | .not, a => ⟨a.nonBool, none, a.ff, a.tt, false, none, none⟩
  | .isNull, a => ⟨false, none, a.null, a.int.isSome || a.tt || a.ff || a.str, false, none, none⟩
  | .neg, a => mapAbs NumKind.int.is (fun _ => .int) Bound.neg (fun _ => false) a
  -- Double negation is code negation too (zero is `0`).
  | .fneg, a => mapAbs NumKind.float.is (fun _ => .float) Bound.neg (fun _ => false) a
  -- Float results: some double (any code), or NULL.
  | .itof, a => convAbs NumKind.int.is FloatCode.intConv a
  | .froundTo _, a => mapAbs NumKind.float.is (fun _ => .float) (fun _ => Bound.top) (fun _ => false) a
  | .ffloor, a => monoAbs .float .float FloatCode.floor a
  | .fceil, a => monoAbs .float .float FloatCode.ceil a
  | .fround, a => monoAbs .float .float FloatCode.round a
  | .ftoi, a => ftoiAbs a
  | .narrow n, a => narrowAbs n a
  -- `ftoi`'s value, or NULL where the cast fails (#58).
  | .ftoiOrNull, a => mapAbs NumKind.float.is (fun _ => .int) ftoiBound (fun _ => true) a
  | .narrowOrNull n, a => narrowAbs n a
  | .wrap _, a => a
  | .decimal _ s, a | .dkind _ s, a => mapAbs intOrDec (fun _ => .dec s) id (fun _ => false) a
  | .dround _, a | .dtrunc _, a =>
      mapAbs intOrDec (fun _ => .int) (fun _ => Bound.top) (fun _ => false) a
  | .dtof s, a => convAbs intOrDec (FloatCode.decConv s) a
  | .ftod s, a => ftodAbs s a
  | .itos, a => ⟨a.nonNum .int, none, false, false, a.int.isSome, none, none⟩
  | .widen, a => a
  | .upper, a | .lower, a | .reverse, a | .replace _ _, a | .regexExtract _ _, a
  | .regexReplace _ _ _, a | .md5, a | .sha256, a =>
    ⟨a.nonStr, none, false, false, a.str, none, none⟩
  -- Below `Text.sizeCap`, by the size hypothesis for strings.
  | .length, a | .ascii, a =>
    ⟨a.nonStr, if a.str then some ⟨some 0, some Text.sizeCap⟩ else none, false, false, false, none,
      some .int⟩
  -- `NULL` when the pattern does not match.
  | .regexMatch _, a =>
    ⟨true, if a.str then some (.ge 1) else none, false, false, false, none, some .int⟩
  | .datePart p, a => datePartAbs p a
  | .dateTrunc u, a => mapAbs tsOrTod id (·.mapMono (Time.trunc u)) (fun _ => false) a
  | .toDate, a => monoAbs .ts .date Time.days a
  | .dayPart p, a => mapAbs NumKind.date.is (fun _ => .int)
      (fun b => partBound p (b.mapMono (· * Time.usPerDay)))
      (fun ob => !ob.all fun b => (b.mapMono (· * Time.usPerDay)).within Time.partMin Time.partMax) a
  | .dayTrunc u, a => monoAbs .date .date (Time.truncDay u) a
  | .addMonths m false, a => monoAbs .date .date (Time.addMonths m) a
  | .addMonths _ true, a => mapAbs NumKind.ts.is (fun _ => .ts) (fun _ => Bound.top) (fun _ => false) a
  | .timeOfDay, a =>
      mapAbs tsOrTod (fun _ => .tod) (fun _ => ⟨some 0, some (Time.usPerDay - 1)⟩) (fun _ => false) a
  | .asTime, a => monoAbs .int .ts id a
  | .dateTime, a => monoAbs .date .ts (· * Time.usPerDay) a
  | .epochUs, a => monoAbs .ts .int id a
  | .strftime _, a => ⟨a.nonNum .ts, none, false, false, a.int.isSome, none, none⟩
  | .bucket k o, a => monoAbs .ts .ts (Time.bucket k o) a
  | .fmath f, a => mapAbs NumKind.float.is (fun _ => .float) (fun _ => Bound.top)
      (fun ob => !f.safeB ob) a
  -- The abstraction does not look into lists: an element or a field is
  -- anything.
  | .structField _, _ | .listElement _, _ | .flatten, _ => AVal.top
  | .cardinality, _ => ⟨true, some (.ge 0), false, false, false, none, some .int⟩
  | .raise _, _ => ⟨true, none, false, false, false, none, none⟩
  | .isNum _, _ => ⟨false, none, true, true, false, none, none⟩
  | .fit _ _, _ => AVal.top
  | .bbox n, a => BlackBox.scalarAbs n !a.null

/-- Arithmetic of numbers of kinds `tbl` takes, by `op` on the intervals. -/
def arith (tbl : NumKind → NumKind → Option NumKind) (op : Bound → Bound → Bound) (a b : AVal) :
    AVal :=
  mapAbs₂ tbl op (fun _ _ => false) a b

/-- `+`'s kinds: an interval (an integer) moves a timestamp, a date or a time
of day. -/
def addNK : NumKind → NumKind → Option NumKind
  | .int, .int => some .int
  | .ts, .int | .int, .ts => some .ts
  | .tod, .int | .int, .tod => some .tod
  | .date, .int | .int, .date => some .date
  | _, _ => none

/-- `-`'s kinds: as `+`'s, and two timestamps, dates or times of day differ by
an integer. -/
def subNK : NumKind → NumKind → Option NumKind
  | .int, .int => some .int
  | .ts, .int => some .ts
  | .tod, .int => some .tod
  | .date, .int => some .date
  | .ts, .ts | .tod, .tod | .date, .date => some .int
  | _, _ => none

/-- The decimal operations' kinds: integers or decimals, to an unscaled integer. -/
def decNK : NumKind → NumKind → Option NumKind
  | .int, .int | .int, .dec _ | .dec _, .int | .dec _, .dec _ => some .int
  | _, _ => none

def dateAddNK : NumKind → NumKind → Option NumKind
  | .date, .int => some .date
  | _, _ => none

def dateDiffNK : NumKind → NumKind → Option NumKind
  | .date, .date => some .int
  | _, _ => none

/-- `%`'s kinds: integers, and a time of day modulo a day. -/
def modNK : NumKind → NumKind → Option NumKind
  | .int, .int => some .int
  | .tod, .int => some .tod
  | _, _ => none

/-- Are the numbers of `a` and `b` of one known kind, so that they compare? -/
def sameNk (a b : AVal) : Bool :=
  match a.nk, b.nk with
  | some x, some y => x == y
  | _, _ => false

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
  -- Numbers of different kinds do not compare, so the first stays.
  let pair : Option Bound := match a.int, b.int with
    | some x, some y => some (if sameNk a b then both x y else x.join y)
    | _, _ => none
  let ints := joinInt (if b.nonInt then a.int else none) (joinInt (if a.null then b.int else none) pair)
  ⟨a.null && b.null, ints, a.tt || b.tt, a.ff || b.ff, a.str || b.str, none, joinNk a b⟩

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
       a.ff || b.ff, false, none, none⟩
  | .or, a, b =>
      ⟨(a.nonBool && (b.ff || b.nonBool)) || (a.ff && b.nonBool), none, a.tt || b.tt,
       a.ff && b.ff, false, none, none⟩
  | .add, a, b => arith addNK Bound.add a b
  | .sub, a, b => arith subNK Bound.sub a b
  | .dateDiff, a, b => arith dateDiffNK Bound.sub a b
  | .mul, a, b => arith intsOnly Bound.mul a b
  | .dadd, a, b => arith decNK Bound.add a b
  | .dsub, a, b => arith decNK Bound.sub a b
  | .dmul, a, b => arith decNK Bound.mul a b
  | .ddiv, a, b => divAbs decNK ddivBound a b
  | .dateAdd, a, b => arith dateAddNK Bound.add a b
  | .fadd, a, b => arith floatsOnly (faddBoundS false) a b
  | .fsub, a, b => arith floatsOnly (faddBoundS true) a b
  | .fmul, a, b => arith floatsOnly fmulBoundS a b
  | .fdiv, a, b => arith floatsOnly fdivBoundS a b
  | .fmod, a, b | .fpow, a, b => arith floatsOnly (fun _ _ => Bound.top) a b
  | .idiv, a, b => divAbs intsOnly divBound a b
  | .imod, a, b => divAbs modNK modBound a b
  | .ipow, a, b => powAbs a b
  | .fatan2, a, b => partialAbs₂ floatsOnly .fatan2 a b
  | .flogb, a, b => partialAbs₂ floatsOnly .flogb a b
  | .bit op, a, b => partialAbs₂ intsOnly (.bit op) a b
  | .concat, a, b | .trim _ _, a, b =>
      ⟨a.nonStr || b.nonStr, none, false, false, a.str && b.str, none, none⟩
  | .strpos, a, b | .levenshtein, a, b =>
      ⟨a.nonStr || b.nonStr, if a.str && b.str then some ⟨some 0, some Text.sizeCap⟩ else none,
        false, false, false, none, some .int⟩
  | .startsWith, a, b | .endsWith, a, b | .like, a, b | .ilike, a, b =>
      ⟨a.nonStr || b.nonStr, none, a.str && b.str, a.str && b.str, false, none, none⟩
  | .substr _ _, a, b | .strRepeat, a, b =>
      ⟨a.nonStr || b.nonNum .int, none, false, false, a.str && b.int.isSome, none, none⟩
  | .eq, a, b =>
      -- Numbers of different kinds do not compare (`Value.numPair`).
      let mismatch := a.null || b.null || (a.int.isSome && (b.tt || b.ff || b.str)) ||
        ((a.tt || a.ff) && (b.int.isSome || b.str)) || (a.str && (b.int.isSome || b.tt || b.ff)) ||
        (a.int.isSome && b.int.isSome && !sameNk a b)
      ⟨mismatch, none,
       intEq a b || (a.tt && b.tt) || (a.ff && b.ff) || strMayEq a b,
       intNe a b || (a.tt && b.ff) || (a.ff && b.tt) || strMayNe a b, false, none, none⟩
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
      | some x, some y =>
        ⟨a.nonInt || b.nonInt || !sameNk a b, none, canLt x y || t, canGe x y || f, false, none, none⟩
      | _, _ => ⟨true, none, t, f, false, none, none⟩

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
  | .anyMatch | .allMatch => ⟨true, none, true, true, false, none, none⟩
  | .transform | .filter => AVal.top

theorem or3_bool_or_null (a b : Value) : or3 a b = .null ∨ ∃ x, or3 a b = .bool x := by
  unfold or3; split <;> simp

theorem and3_bool_or_null (a b : Value) : and3 a b = .null ∨ ∃ x, and3 a b = .bool x := by
  unfold and3; split <;> simp

theorem HoFn.abs_sound (f : HoFn) (v : Value) (p : Value → Value) : f.abs.Mem (f.apply v p) := by
  have key : ∀ r : Value, (r = .null ∨ ∃ x, r = .bool x) →
      (⟨true, none, true, true, false, none, none⟩ : AVal).Mem r := by
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

/-- Proves a function's shape (`Value.mapP`, `Value.mapP₂`) on one value. -/
macro "hf_tac" : tactic => `(tactic| first
  | rfl
  | (simp only [UnFn.apply, BinFn.apply, Value.mapP, Value.mapP₂, Value.numOf?, NumKind.is,
      NumKind.val, Value.unscaled?, intsOnly, floatsOnly, addNK, subNK, decNK, dateAddNK,
      dateDiffNK, modNK, intOrDec, tsOrTod, beq_self_eq_true, ite_true, Function.comp]
     try (repeat' split) <;> first | rfl | simp_all))

end Substrait
