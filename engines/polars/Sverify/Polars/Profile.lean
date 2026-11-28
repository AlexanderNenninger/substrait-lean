import Sverify.Engines.Lowering
import Sverify.Polars.Shims

/-!
# Polars as a profile (#444)

`Profile.polars` is the semantics a plan verified with
`verify(semantics="polars")` is checked under: what Polars 2.1.0's streaming
engine computes, as its facts record it (`engines/polars/facts/`),
on the options where sverify models Polars's own choice, and the reference
elsewhere. Per option (D21, `docs/engine-profiles.md`, "Polars as a profile"):

* `division_type`: `FLOOR`, Polars's own. Integer `//` floors and `%` takes
  the divisor's sign (polars-int-divide, polars-int-modulus).
* `decimal_rescale`: `TIE_TO_EVEN`, Polars's own. A decimal cast to a smaller
  scale and a double cast to a decimal round half to even
  (polars-decimal-casts, ruling 278 and its addendum).
* `±∞`: a double that overflows is `±∞`, as in the reference (#575), with no
  precondition (polars-double-arith), as under DuckDB's profile.
* The error side stays the reference's: an integer that overflows, a zero
  divisor and NaN creation raise, where Polars wraps, gives NULL or NaN. A
  verified plan never reaches them, so Polars's own values there need no
  shim, and the profile is tighter than the engine (D21).
* Every other option is the reference's: there, the translation to Polars
  keeps its written arguments and shims (`Polars/Shims.lean`).

A plan states the choice it makes: integer `divide` and `modulus` with
`division_type: FLOOR`, which the parser reads as `Expr.floorDivOf` and
`Expr.floorModOf`, templates in the reference's truncating operations that
never overflow on 64-bit operands. `Write` writes them back as the calls, so
Polars runs its own `//` and `%` (on the translated route, until the generated
lowering of #271 gives the native one), and DuckDB, which has no `FLOOR`,
refuses them.

What is proved here:

* `Profile.polars`, an evaluable `Profile`: its `//` and `%` are the
  templates under the reference, and on 64-bit integers they are Polars's
  (`Polars.floorDiv`, `Polars.floorMod`, the trusted model of
  `Polars/Shims.lean`): `Profile.polars_idiv`, `Profile.polars_imod`. A zero
  divisor raises (`Profile.polars_zero_divisor`).
* `Polars.elaborate_eq`: evaluating an expression under `Profile.polars` is
  evaluating its elaboration (`Polars.elaborate`: each `//` and `%` replaced by
  its template) under the reference. So a contract the checker proves of the
  elaborated plan holds of the plan under `Profile.polars`, and the checker
  needs nothing new: it checks the plan the parser reads.
* `Profile.polars.table`'s choices refine the core (`Profile.polars_le_core`,
  `EngineTables.lean`), hence `Allowed_polars ⊆ Allowed_core`
  (`Rel.allowed_polars_core`).

Trusted, and tested: that Polars's `//` and `%` are `Polars.floorDiv` and
`Polars.floorMod` (the facts), and that the translation writes the calls
as Polars's operators (`tests/test_profiles_e2e.py`).
-/

namespace Substrait

namespace Polars

/-- Polars's `//` over the arguments as fields 0 and 1. -/
def floorDivT : Expr := Expr.floorDivOf (.field 0) (.field 1)

/-- Polars's `%` over the arguments as fields 0 and 1. -/
def floorModT : Expr := Expr.floorModOf (.field 0) (.field 1)

theorem floorDivT_subst (a b : Expr) : floorDivT.subst [a, b] = Expr.floorDivOf a b := rfl

theorem floorModT_subst (a b : Expr) : floorModT.subst [a, b] = Expr.floorModOf a b := rfl

/-- Polars's `%` of doubles over the arguments as fields 0 and 1:
`x - y * floor(x / y)` in the reference's double operations
(polars-double-modulus). A zero divisor raises (`fdiv`), and so does a finite
`x % ±∞` (`y * 0` is `∞ * 0`, a NaN), where Polars gives NaN: the error side
stays the reference's (D21). -/
def floorFmodT : Expr := Expr.floorFmodOf (.field 0) (.field 1)

theorem floorFmodT_subst (a b : Expr) : floorFmodT.subst [a, b] = Expr.floorFmodOf a b := rfl

/-- Polars's `%` of decimals over the arguments as fields 0 and 1: the floored
remainder of the unscaled integers (polars-decimal-modulus, D62). -/
def floorDModT : Expr := Expr.floorDModOf (.field 0) (.field 1)

theorem floorDModT_subst (a b : Expr) : floorDModT.subst [a, b] = Expr.floorDModOf a b := rfl

/-- Polars's `round` or `ceil` of the argument as field 0, as the translation
writes them (`round(mode='half_away_from_zero')`, `ceil`): the reference's,
but IEEE's `-0.0` for a negative value that rounds to zero (`round(-0.4)`,
`ceil(-0.4)`; polars-round, polars-round-digits), where the reference gives
`0.0` (`round_zero_sign`). -/
def negZeroT (f : UnFn) : Expr :=
  .ifThen (.bin .and (.bin .lt (.field 0) (.lit (.float 0)))
      (.bin .eq (.un f (.field 0)) (.lit (.float 0))))
    (.lit (.float FloatCode.negZero)) (.un f (.field 0))

/-- The product `x · 10ˢ` in doubles, of the argument as field 0: `10ˢ` rounded
to a double, then the product rounded, as Polars's `f64_to_dec128` and the
reference's `FloatCode.toDecimal?` compute it. -/
def ftodProduct (s : Nat) : Expr := .bin .fmul (.field 0) (.lit (.float (FloatCode.ofInt (10 ^ s))))

/-- Polars's cast of a double, the argument as field 0, to a decimal of scale `s`:
the product `x · 10ˢ` rounded half to even (polars-decimal-casts), where the
reference rounds it half away from zero (`decimal_rescale`, ruling 278). The two
differ only at an exact tie whose neighbour away from zero is odd, which is where
`round` and `round(mode='half_to_even')` of the product differ: there it is the
even neighbour, below `2⁵²` in magnitude, which the cast to an integer takes
exactly. Everywhere else, NaN, `±∞` and a product that overflows included, it is
the reference's cast. -/
def ftodEvenT (s : Nat) : Expr :=
  .ifThen (.un .not (.bin .eq (.un .fround (ftodProduct s)) (.un .froundEven (ftodProduct s))))
    (.un .ftoi (.un .froundEven (ftodProduct s))) (.un (.ftod s) (.field 0))

/-- Polars's cast of a decimal, the argument as field 0, to a scale `k` digits
smaller: half to even (polars-decimal-casts), where the reference rounds half
away from zero (`roundDiv10`, `decimal_rescale`, ruling 278's addendum). With
`t` the quotient truncated toward zero, the two differ only at an exact tie,
where the remainder `x - t·10ᵏ` is `±10ᵏ/2`, and `t` is even: there the cast
gives `t`. Everywhere else, `NULL` included, it is the reference's rescale. -/
def droundEvenT (k : Nat) : Expr :=
  let t : Expr := .un (.dtrunc k) (.field 0)
  let twiceRem : Expr :=
    .bin .dmul (.bin .dsub (.field 0) (.bin .dmul t (.lit (.int (10 ^ k))))) (.lit (.int 2))
  .ifThen (.bin .and
      (.bin .or (.bin .eq twiceRem (.lit (.int (10 ^ k)))) (.bin .eq twiceRem (.lit (.int (-(10 ^ k))))))
      (.bin .eq (.bin .imod t (.lit (.int 2))) (.lit (.int 0))))
    t (.un (.dround k) (.field 0))

end Polars

/-- The unary functions where Polars's profile differs from the reference: its
template, in the reference's operations. `round` and `ceil` give `-0.0`
(polars-round); a double cast to a decimal and a decimal cast to a smaller
scale round half to even (polars-decimal-casts). -/
def UnFn.polarsTmpl : UnFn → Option Expr
  | .fround => some (Polars.negZeroT .fround)
  | .froundEven => some (Polars.negZeroT .froundEven)
  | .fceil => some (Polars.negZeroT .fceil)
  | .ftod s => some (Polars.ftodEvenT s)
  | .dround k => some (Polars.droundEvenT k)
  | _ => none

/-- The functions where Polars's profile differs from the reference: its
template, in the reference's operations. -/
def BinFn.polarsTmpl : BinFn → Option Expr
  | .idiv => some Polars.floorDivT
  | .imod => some Polars.floorModT
  | .fmod => some Polars.floorFmodT
  | .dmod => some Polars.floorDModT
  | _ => none

variable [Boxes.Ambient]
/-- **Polars's profile**: `//` and `%` floor (`division_type` =
`FLOOR`), of integers and, for `%`, of doubles and decimals; `round` and `ceil` give `-0.0`
for a negative value that rounds to zero (`round_zero_sign`); a double cast to a
decimal rounds the product half to even, and a decimal cast to a smaller scale
rounds half to even (`decimal_rescale`); every other function is the
reference's. The product of decimals' unscaled integers (`dmul`) is the
reference's exact one, which Polars's Int128 `*` gives only below `2¹²⁷`: past
it Polars wraps (polars-int-arith), and the lowering's template raises before
(`Polars.dmul_bound`, ruling 282's T3). -/
def Profile.polars : Profile where
  un f v := match f.polarsTmpl with
    | some t => t.evalP Profile.reference [v]
    | none => Profile.reference.un f v
  bin f x y := match f.polarsTmpl with
    | some t => t.evalP Profile.reference [x, y]
    | none => Profile.reference.bin f x y

namespace Polars

/-! ## The templates are Polars's `//` and `%` on 64-bit integers -/

omit [Boxes.Ambient] in
theorem fdiv_fmod_neg_pos {a b : Int} (ha : a < 0) (hb : 0 < b) :
    a.fdiv b = (a + 1).tdiv b + -1 ∧ a.fmod b = (a + 1).tmod b + (b - 1) := by
  have h1 := Int.tmod_add_tdiv_mul (a + 1) b
  have h2 := Int.lt_tmod_of_pos (a + 1) hb
  have h3 : (a + 1).tmod b ≤ 0 := by
    have := Int.tmod_nonneg b (show 0 ≤ -(a + 1) by omega)
    rw [Int.neg_tmod] at this; omega
  have hu := (Int.ediv_emod_unique (a := a) (r := (a + 1).tmod b - 1 + b)
    (q := (a + 1).tdiv b - 1) hb).mpr ⟨by rw [Int.mul_sub, Int.mul_comm b]; omega, by omega, by omega⟩
  rw [Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hb), Int.fmod_eq_emod_of_nonneg a (Int.le_of_lt hb)]
  omega

omit [Boxes.Ambient] in
theorem fdiv_fmod_pos_neg {a b : Int} (ha : 0 < a) (hb : b < 0) :
    a.fdiv b = (a - 1).tdiv b + -1 ∧ a.fmod b = (a - 1).tmod b + (b + 1) := by
  have h := fdiv_fmod_neg_pos (a := -a) (b := -b) (by omega) (by omega)
  have e : -a + 1 = -(a - 1) := by omega
  rw [Int.neg_fdiv_neg, Int.neg_fmod_neg, e, Int.neg_tdiv, Int.tdiv_neg, Int.neg_tmod,
    Int.tmod_neg] at h
  omega

omit [Boxes.Ambient] in
theorem fdiv_fmod_same {a b : Int} (h1 : ¬(a < 0 ∧ 0 < b)) (h2 : ¬(0 < a ∧ b < 0)) :
    a.fdiv b = a.tdiv b ∧ a.fmod b = a.tmod b := by
  by_cases hb0 : b = 0
  · subst hb0; simp
  by_cases hb : 0 < b
  · have ha : 0 ≤ a := by omega
    exact ⟨Int.fdiv_eq_tdiv_of_nonneg ha (by omega), Int.fmod_eq_tmod_of_nonneg ha (by omega)⟩
  · have ha : a ≤ 0 := by omega
    have hd := Int.fdiv_eq_tdiv_of_nonneg (a := -a) (b := -b) (by omega) (by omega)
    have hm := Int.fmod_eq_tmod_of_nonneg (a := -a) (b := -b) (by omega) (by omega)
    rw [Int.neg_fdiv_neg, Int.neg_tdiv, Int.tdiv_neg] at hd
    rw [Int.neg_fmod_neg, Int.neg_tmod, Int.tmod_neg] at hm
    exact ⟨by omega, by omega⟩

omit [Boxes.Ambient] in
theorem inI64_iff (x : Int) : inI64 x = true ↔ -2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1 := by
  unfold inI64 between
  rw [Bool.and_eq_true]
  exact ⟨fun ⟨h1, h2⟩ => ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩,
    fun ⟨h1, h2⟩ => ⟨decide_eq_true h1, decide_eq_true h2⟩⟩

theorem ref_add_int (x y : Int) (h1 : -2 ^ 63 ≤ x + y) (h2 : x + y ≤ 2 ^ 63 - 1) :
    Profile.reference.bin .add (.int x) (.int y) = .ok (.int (x + y)) := by
  have h : inI64 (x + y) = true := (inI64_iff _).mpr ⟨h1, h2⟩
  have ha : BinFn.apply .add (.int x) (.int y) = .int (x + y) := rfl
  show raiseIf (BinFn.issue .add (.int x) (.int y)) (BinFn.apply .add (.int x) (.int y)) = _
  simp [raiseIf, BinFn.issue, wrapNum, Value.numOf?, wrapIf, h, ha]

theorem ref_sub_int (x y : Int) (h1 : -2 ^ 63 ≤ x - y) (h2 : x - y ≤ 2 ^ 63 - 1) :
    Profile.reference.bin .sub (.int x) (.int y) = .ok (.int (x - y)) := by
  have h : inI64 (x - y) = true := (inI64_iff _).mpr ⟨h1, h2⟩
  have ha : BinFn.apply .sub (.int x) (.int y) = .int (x - y) := rfl
  show raiseIf (BinFn.issue .sub (.int x) (.int y)) (BinFn.apply .sub (.int x) (.int y)) = _
  simp [raiseIf, BinFn.issue, wrapNum, Value.numOf?, wrapIf, h, ha]

theorem ref_idiv_int (x y : Int) (h0 : y ≠ 0) (h : inI64 (x.tdiv y) = true) :
    Profile.reference.bin .idiv (.int x) (.int y) = .ok (.int (x.tdiv y)) := by
  have ha : BinFn.apply .idiv (.int x) (.int y) = .int (x.tdiv y) := by
    simp only [BinFn.apply.eq_def]; simp [h0]
  show raiseIf (BinFn.issue .idiv (.int x) (.int y)) (BinFn.apply .idiv (.int x) (.int y)) = _
  simp [raiseIf, BinFn.issue, h0, h, ha]

theorem ref_lt_int (x y : Int) :
    Profile.reference.bin .lt (.int x) (.int y) = .ok (.bool (decide (x < y))) := by
  rw [Lowering.ref_lt]; rfl

omit [Boxes.Ambient] in
/-- The truncating quotient of 64-bit integers fits in 64 bits but for
`MIN / -1`. -/
theorem tdiv_inI64 {x y : Int} (hx : -2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1) (hy : y ≠ 0)
    (hov : ¬(x = -2 ^ 63 ∧ y = -1)) : inI64 (x.tdiv y) = true := by
  rw [inI64_iff]
  have hn : (x.tdiv y).natAbs = x.natAbs / y.natAbs := Int.natAbs_tdiv x y
  by_cases hy1 : y = -1
  · subst hy1; rw [Int.tdiv_neg, Int.tdiv_one]; omega
  by_cases hy2 : y = 1
  · subst hy2; rw [Int.tdiv_one]; omega
  have h2 : x.natAbs / y.natAbs ≤ x.natAbs / 2 := Nat.div_le_div_left (by omega) (by omega)
  omega

end Polars

omit [Boxes.Ambient] in
theorem Polars.isTrue_bool (z : Bool) : (Value.bool z).isTrue = z := by cases z <;> rfl

/-- **Polars's `%` on 64-bit integers** is its floored remainder
(`Polars.floorMod`, polars-int-modulus). -/
theorem Profile.polars_imod {a b : Int} (ha : inI64 a = true) (hb : inI64 b = true)
    (h0 : b ≠ 0) : Profile.polars.bin .imod (.int a) (.int b) = .ok (.int (Polars.floorMod a b)) := by
  have ha' := (Polars.inI64_iff _).mp ha
  have hb' := (Polars.inI64_iff _).mp hb
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorModT, Expr.floorModOf, Expr.evalP,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Polars.ref_lt_int, bind, Except.bind, Polars.floorMod, Polars.isTrue_bool, decide_eq_true_eq]
  by_cases c1 : a < 0 ∧ 0 < b
  · obtain ⟨_, hm⟩ := Polars.fdiv_fmod_neg_pos c1.1 c1.2
    have hr := Int.lt_tmod_of_pos (a + 1) c1.2
    have hr2 : (a + 1).tmod b ≤ 0 := by
      have := Int.tmod_nonneg b (show 0 ≤ -(a + 1) by omega)
      rw [Int.neg_tmod] at this; omega
    have hn : (-1 - a).tmod b = -(a + 1).tmod b := by
      rw [show -1 - a = -(a + 1) by omega, Int.neg_tmod]
    have e1 := Polars.ref_sub_int (-1) a (by omega) (by omega)
    have e2 := Lowering.ref_imod_int (-1 - a) b h0
    have e3 := Polars.ref_sub_int b 1 (by omega) (by omega)
    have e4 := Polars.ref_sub_int (b - 1) ((-1 - a).tmod b) (by omega) (by omega)
    rw [show (a + 1).tmod b + (b - 1) = b - 1 - (-1 - a).tmod b by omega] at hm
    simp only [c1.1, c1.2, ↓reduceIte, e1, e2, e3, e4, hm]
  by_cases c2 : 0 < a ∧ b < 0
  · obtain ⟨_, hm⟩ := Polars.fdiv_fmod_pos_neg c2.1 c2.2
    have hr := Int.tmod_nonneg b (show 0 ≤ a - 1 by omega)
    have hr2 := Int.tmod_lt_of_pos (a - 1) (show 0 < -b by omega)
    rw [Int.tmod_neg] at hr2
    have e1 := Polars.ref_sub_int a 1 (by omega) (by omega)
    have e2 := Lowering.ref_imod_int (a - 1) b h0
    have e3 := Polars.ref_add_int b 1 (by omega) (by omega)
    have e4 := Polars.ref_add_int ((a - 1).tmod b) (b + 1) (by omega) (by omega)
    simp only [show ¬a < 0 by omega, c2.1, c2.2, ↓reduceIte, e1, e2, e3, e4, hm]
  · obtain ⟨_, hm⟩ := Polars.fdiv_fmod_same c1 c2
    have e := Lowering.ref_imod_int a b h0
    by_cases d1 : a < 0 <;> by_cases d2 : 0 < b <;> by_cases d3 : b < 0 <;> by_cases d4 : 0 < a <;>
      simp only [d1, d2, d3, d4, ↓reduceIte, e, hm] <;> omega

/-- **Polars's `//` on 64-bit integers** is its floored quotient
(`Polars.floorDiv`, polars-int-divide), but for `MIN // -1`, which overflows
and raises, as in the reference. -/
theorem Profile.polars_idiv {a b : Int} (ha : inI64 a = true) (hb : inI64 b = true)
    (h0 : b ≠ 0) (hov : ¬(a = -2 ^ 63 ∧ b = -1)) :
    Profile.polars.bin .idiv (.int a) (.int b) = .ok (.int (Polars.floorDiv a b)) := by
  have ha' := (Polars.inI64_iff _).mp ha
  have hb' := (Polars.inI64_iff _).mp hb
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorDivT, Expr.floorDivOf, Expr.evalP,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Polars.ref_lt_int, bind, Except.bind, Polars.floorDiv, Polars.isTrue_bool, decide_eq_true_eq]
  by_cases c1 : a < 0 ∧ 0 < b
  · obtain ⟨hd, _⟩ := Polars.fdiv_fmod_neg_pos c1.1 c1.2
    have hq := Polars.tdiv_inI64 (x := a + 1) (y := b) ⟨by omega, by omega⟩ h0 (by omega)
    have hq' := (Polars.inI64_iff _).mp hq
    have hn := Int.natAbs_tdiv (a + 1) b
    have hle : ((a + 1).tdiv b).natAbs ≤ (a + 1).natAbs := by rw [hn]; exact Nat.div_le_self _ _
    have e1 := Polars.ref_add_int a 1 (by omega) (by omega)
    have e2 := Polars.ref_idiv_int (a + 1) b h0 hq
    have e3 := Polars.ref_add_int ((a + 1).tdiv b) (-1) (by omega) (by omega)
    simp only [c1.1, c1.2, ↓reduceIte, e1, e2, e3, hd]
  by_cases c2 : 0 < a ∧ b < 0
  · obtain ⟨hd, _⟩ := Polars.fdiv_fmod_pos_neg c2.1 c2.2
    have hq := Polars.tdiv_inI64 (x := a - 1) (y := b) ⟨by omega, by omega⟩ h0 (by omega)
    have hq' := (Polars.inI64_iff _).mp hq
    have hn := Int.natAbs_tdiv (a - 1) b
    have hle : ((a - 1).tdiv b).natAbs ≤ (a - 1).natAbs := by rw [hn]; exact Nat.div_le_self _ _
    have e1 := Polars.ref_sub_int a 1 (by omega) (by omega)
    have e2 := Polars.ref_idiv_int (a - 1) b h0 hq
    have e3 := Polars.ref_add_int ((a - 1).tdiv b) (-1) (by omega) (by omega)
    simp only [show ¬a < 0 by omega, c2.1, c2.2, ↓reduceIte, e1, e2, e3, hd]
  · obtain ⟨hd, _⟩ := Polars.fdiv_fmod_same c1 c2
    have e := Polars.ref_idiv_int a b h0 (Polars.tdiv_inI64 (x := a) (y := b) ha' h0 hov)
    by_cases d1 : a < 0 <;> by_cases d2 : 0 < b <;> by_cases d3 : b < 0 <;> by_cases d4 : 0 < a <;>
      simp only [d1, d2, d3, d4, ↓reduceIte, e, hd] <;> omega

/-- A zero divisor raises under `Profile.polars`, as in the reference (D21:
Polars gives `NULL`, which a verified plan never reaches). -/
theorem Profile.polars_zero_divisor (f : BinFn) (hf : f = .idiv ∨ f = .imod) (a : Int) :
    Profile.polars.bin f (.int a) (.int 0) = .error .divByZero := by
  have hz : ∀ g : BinFn, g = .idiv ∨ g = .imod →
      Profile.reference.bin g (.int a) (.int 0) = .error .divByZero := by
    rintro g (rfl | rfl) <;> rfl
  have c : ¬(0 : Int) < 0 := by omega
  rcases hf with rfl | rfl <;>
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorDivT, Polars.floorModT, Expr.floorDivOf,
    Expr.floorModOf, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Polars.ref_lt_int, bind, Except.bind, Polars.isTrue_bool, decide_eq_true_eq,
    c, ↓reduceIte, hz _ (.inl rfl), hz _ (.inr rfl), ite_self]

/-! ## The truncated remainder from Polars's floored one

`Polars.fmod_of_tmod` below is proved from these, which `Polars.Shims` held
before the generated lowering (#271) replaced its integer shims. -/

namespace Polars

omit [Boxes.Ambient] in
/-- `int_div_trunc`: one more than the floored quotient where the remainder is
not zero and the signs differ. -/
def intDivTrunc (a b : Int) : Int :=
  if floorMod a b ≠ 0 ∧ (decide (a < 0) ≠ decide (b < 0)) then floorDiv a b + 1 else floorDiv a b

omit [Boxes.Ambient] in
/-- `int_mod_trunc`: the divisor taken off where the remainder's sign is not
the dividend's. -/
def intModTrunc (a b : Int) : Int :=
  let r := floorMod a b
  if r ≠ 0 ∧ (decide (r < 0) ≠ decide (a < 0)) then r - b else r

omit [Boxes.Ambient] in
theorem fmod_eq_zero_iff {a b : Int} : a.fmod b = 0 ↔ b ∣ a := Int.dvd_iff_fmod_eq_zero.symm

omit [Boxes.Ambient] in
/-- The floored remainder has the divisor's sign. -/
theorem fmod_sign (a : Int) {b : Int} : (0 < b → 0 ≤ a.fmod b) ∧ (b < 0 → a.fmod b ≤ 0) := by
  refine ⟨fun h => Int.fmod_nonneg_of_pos a h, fun h => ?_⟩
  have := Int.fmod_nonneg_of_pos (-a) (b := -b) (by omega)
  rw [Int.neg_fmod_neg] at this
  omega

omit [Boxes.Ambient] in
/-- **`Polars.int_div_trunc`**: the shimmed quotient is the reference's
(`Int.tdiv`, `BinFn.idiv`). -/
theorem int_div_trunc (a : Int) {b : Int} (hb : b ≠ 0) : intDivTrunc a b = a.tdiv b := by
  unfold intDivTrunc floorDiv floorMod
  rw [Int.tdiv_eq_fdiv]
  by_cases hd : b ∣ a
  · have : a.fmod b = 0 := fmod_eq_zero_iff.mpr hd
    simp [hd, this]
  · have : a.fmod b ≠ 0 := fun h => hd (fmod_eq_zero_iff.mp h)
    simp only [hd, ite_false, ne_eq, this, not_false_eq_true, true_and]
    have hs : b.sign = if 0 < b then 1 else -1 := by
      rcases Int.lt_trichotomy b 0 with h | h | h
      · simp [Int.sign_eq_neg_one_of_neg h, show ¬ 0 < b by omega]
      · omega
      · simp [Int.sign_eq_one_of_pos h, h]
    by_cases ha : 0 ≤ a <;> by_cases hb' : 0 ≤ b <;> simp_all <;> omega

omit [Boxes.Ambient] in
/-- **`Polars.int_mod_trunc`**: the shimmed remainder is the reference's
(`Int.tmod`, `BinFn.imod`). -/
theorem int_mod_trunc (a : Int) {b : Int} (hb : b ≠ 0) : intModTrunc a b = a.tmod b := by
  have hq := int_div_trunc a hb
  have h1 := Int.fmod_add_mul_fdiv a b
  have h2 := Int.tmod_add_mul_tdiv a b
  unfold intDivTrunc floorDiv floorMod at hq
  unfold intModTrunc floorMod
  dsimp only
  -- The remainders differ by `b` exactly where the quotients differ by one.
  have hfm : a.fmod b ≠ 0 → (decide (a.fmod b < 0) ≠ decide (a < 0) ↔
      decide (a < 0) ≠ decide (b < 0)) := by
    intro hne
    have hsgn := fmod_sign a (b := b)
    by_cases hbp : 0 < b <;> simp_all <;> omega
  by_cases hc : a.fmod b ≠ 0 ∧ (decide (a < 0) ≠ decide (b < 0))
  · simp only [hc, ne_eq, not_false_eq_true, and_self, ite_true] at hq
    have hc' : a.fmod b ≠ 0 ∧ (decide (a.fmod b < 0) ≠ decide (a < 0)) :=
      ⟨hc.1, (hfm hc.1).mpr hc.2⟩
    simp only [hc', ne_eq, not_false_eq_true, and_self, ite_true]
    rw [← hq] at h2
    rw [Int.mul_add] at h2
    omega
  · simp only [hc, ite_false] at hq
    have hc' : ¬ (a.fmod b ≠ 0 ∧ (decide (a.fmod b < 0) ≠ decide (a < 0))) := by
      rintro ⟨h0, h⟩; exact hc ⟨h0, (hfm h0).mp h⟩
    simp only [hc', ite_false]
    rw [← hq] at h2
    omega

end Polars

omit [Boxes.Ambient] in
/-- The floored remainder from the truncated one: the divisor added where
the truncated remainder is not zero and its sign is not the divisor's. -/
theorem Polars.fmod_of_tmod (a : Int) {b : Int} (hb : b ≠ 0) :
    a.fmod b = if (a.tmod b < 0 ∧ 0 < b) ∨ (0 < a.tmod b ∧ b < 0) then a.tmod b + b
      else a.tmod b := by
  have h := Polars.int_mod_trunc a hb
  unfold Polars.intModTrunc Polars.floorMod at h
  have hs := Polars.fmod_sign a (b := b)
  have h1 : 0 < b → a.fmod b < b := Int.fmod_lt_of_pos a
  have h2 : b < 0 → b < a.fmod b := fun hb' => by
    have := Int.fmod_lt_of_pos (-a) (b := -b) (by omega)
    rw [Int.neg_fmod_neg] at this; omega
  have t1 : 0 ≤ a → 0 ≤ a.tmod b := fun ha => Int.tmod_nonneg b ha
  have t2 : a < 0 → a.tmod b ≤ 0 := fun ha => by
    have := Int.tmod_nonneg b (show 0 ≤ -a by omega); rw [Int.neg_tmod] at this; omega
  dsimp only at h
  split at h
  · rename_i c1
    have c1' : a.fmod b ≠ 0 ∧ ¬(a.fmod b < 0 ↔ a < 0) := by simpa using c1
    split <;> omega
  · rename_i c1
    have c1' : ¬(a.fmod b ≠ 0 ∧ ¬(a.fmod b < 0 ↔ a < 0)) := by simpa using c1
    split <;> omega

/-- **Polars's `%` of decimals** is the floored remainder of their unscaled
integers (`Polars.floorMod`, polars-decimal-modulus), for two decimals of one
scale as the parser brings them to (D62). -/
theorem Profile.polars_dmod {x y : Value} {a b : Int} (hx : x.unscaled? = some a)
    (hy : y.unscaled? = some b) (h0 : b ≠ 0) :
    Profile.polars.bin .dmod x y = .ok (.int (Polars.floorMod a b)) := by
  have er := Lowering.ref_dmod hx hy h0
  have ey : Profile.reference.bin .dadd y (.int 0) = .ok (.int b) := by
    rw [Lowering.ref_dadd]; simp only [BinFn.apply, hy]; simp
  have es : ∀ t, Profile.reference.bin .dadd (.int t) (.int b) = .ok (.int (t + b)) := fun t => by
    rw [Lowering.ref_dadd]; rfl
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorDModT, Expr.floorDModOf, Expr.evalP,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, er, ey, es,
    Polars.ref_lt_int, bind, Except.bind, Polars.isTrue_bool, decide_eq_true_eq, Polars.floorMod,
    Polars.fmod_of_tmod a h0]
  by_cases d1 : a.tmod b < 0 <;> by_cases d2 : 0 < b <;> by_cases d3 : 0 < a.tmod b <;>
    by_cases d4 : b < 0 <;> simp only [d1, d2, d3, d4, ↓reduceIte, and_true, and_false, or_false,
      false_or] <;> omega

/-- A zero divisor of a decimal `%` raises under `Profile.polars`, as on Polars
(polars-decimal-modulus) and in the reference. -/
theorem Profile.polars_dmod_zero {x y : Value} {a : Int} (hx : x.unscaled? = some a)
    (hy : y.unscaled? = some 0) : Profile.polars.bin .dmod x y = .error .divByZero := by
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorDModT, Expr.floorDModOf, Expr.evalP,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Lowering.ref_dmod_zero hx hy, bind, Except.bind]

/-- A decimal `%` with an operand that is not a number (`NULL`) is `NULL` under
`Profile.polars`, as in the reference. -/
theorem Profile.polars_dmod_null {x y : Value} (h : x.unscaled? = none ∨ y.unscaled? = none) :
    Profile.polars.bin .dmod x y = .ok .null := by
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorDModT, Expr.floorDModOf, Expr.evalP,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Lowering.ref_dmod_null h, Lowering.ref_lt, bind, Except.bind]
  rfl

/-! ## Evaluating under `Profile.polars` is evaluating the elaboration -/

namespace Polars

/-- A plan read with Polars's `//` and `%`, written in the reference's
operations: each integer `//` and `%` replaced by its template. -/
def elaborate : Expr → Expr
  | .lit v => .lit v
  | .field i => .field i
  | .un f a => match f.polarsTmpl with
    | some t => t.subst [elaborate a]
    | none => .un f (elaborate a)
  | .bin f a b => match f.polarsTmpl with
    | some t => t.subst [elaborate a, elaborate b]
    | none => .bin f (elaborate a) (elaborate b)
  | .ifThen c t e => .ifThen (elaborate c) (elaborate t) (elaborate e)
  | .hof f l b => .hof f (elaborate l) (elaborate b)

/-- A unary template evaluates its argument before anything that may raise. -/
theorem untmpl_subst_eval {f : UnFn} {t : Expr} (h : f.polarsTmpl = some t) (a : Expr) (row : Row) :
    (t.subst [a]).evalP Profile.reference row =
      (do let x ← a.evalP Profile.reference row
          t.evalP Profile.reference [x]) := by
  cases ha : a.evalP Profile.reference row with
  | error k =>
    cases f <;> simp only [UnFn.polarsTmpl, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      simp [negZeroT, ftodEvenT, ftodProduct, droundEvenT, Expr.subst, Expr.evalP, ha, bind,
        Except.bind]
  | ok x =>
    simp only [bind, Except.bind]
    exact Expr.evalP_subst (vs := [x]) (fun i => by
      rcases i with _ | i <;> simp [ha, Expr.evalP]) t

/-- A template evaluates its first argument, then its second, before
anything that may raise: substituting expressions is binding their
outcomes. -/
theorem tmpl_subst_eval {f : BinFn} {t : Expr} (h : f.polarsTmpl = some t) (a b : Expr) (row : Row) :
    (t.subst [a, b]).evalP Profile.reference row =
      (do let x ← a.evalP Profile.reference row
          let y ← b.evalP Profile.reference row
          t.evalP Profile.reference [x, y]) := by
  cases ha : a.evalP Profile.reference row with
  | error k =>
    cases f <;> simp only [BinFn.polarsTmpl, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      simp [floorDivT, floorModT, floorFmodT, floorDModT, Expr.floorDivOf, Expr.floorModOf,
        Expr.floorFmodOf, Expr.floorDModOf, Expr.subst, Expr.evalP,
        ha, bind, Except.bind]
  | ok x =>
    cases hb : b.evalP Profile.reference row with
    | error k =>
      cases f <;> simp only [BinFn.polarsTmpl, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
        simp [floorDivT, floorModT, floorFmodT, floorDModT, Expr.floorDivOf, Expr.floorModOf,
          Expr.floorFmodOf, Expr.floorDModOf, Expr.subst, Expr.evalP,
          ha, hb, bind, Except.bind, Lowering.ref_lt]
      all_goals split <;> rfl
    | ok y =>
      simp only [bind, Except.bind]
      exact Expr.evalP_subst (vs := [x, y]) (fun i => by
        rcases i with _ | _ | i <;> simp [ha, hb, Expr.evalP]) t

/-- **Evaluating under `Profile.polars` is evaluating the elaboration under
the reference**: the same value, or the same error. A contract proved of
`elaborate` of a plan holds of the plan under `Profile.polars`. -/
theorem elaborate_eq : ∀ (e : Expr) (row : Row),
    (elaborate e).evalP Profile.reference row = e.evalP Profile.polars row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, row => by
    cases h : f.polarsTmpl with
    | none =>
      simp only [elaborate, h, Expr.evalP, elaborate_eq a row]
      simp only [Profile.polars, h]
    | some t =>
      simp only [elaborate, h]
      rw [untmpl_subst_eval h, elaborate_eq a row]
      simp only [Expr.evalP, Profile.polars, h]
  | .bin f a b, row => by
    cases h : f.polarsTmpl with
    | none =>
      simp only [elaborate, h, Expr.evalP, elaborate_eq a row, elaborate_eq b row]
      simp only [Profile.polars, h]
    | some t =>
      simp only [elaborate, h]
      rw [tmpl_subst_eval h, elaborate_eq a row, elaborate_eq b row]
      simp only [Expr.evalP, Profile.polars, h]
  | .ifThen c t e, row => by simp only [elaborate, Expr.evalP, elaborate_eq c row, elaborate_eq t row, elaborate_eq e row]
  | .hof f l b, row => by
    simp only [elaborate, Expr.evalP, elaborate_eq l row]
    have : (fun x => (elaborate b).evalP Profile.reference (x :: row)) = fun x => b.evalP Profile.polars (x :: row) :=
      funext fun x => elaborate_eq b (x :: row)
    rw [this]

omit [Boxes.Ambient] in
/-- The parser reads a call that states `division_type: FLOOR` as the
template of Polars's `//` or `%` (of doubles too): the elaboration of the native call. -/
theorem elaborate_floor (a b : Expr) :
    elaborate (.bin .idiv a b) = Expr.floorDivOf (elaborate a) (elaborate b) ∧
    elaborate (.bin .imod a b) = Expr.floorModOf (elaborate a) (elaborate b) ∧
    elaborate (.bin .fmod a b) = Expr.floorFmodOf (elaborate a) (elaborate b) ∧
    elaborate (.bin .dmod a b) = Expr.floorDModOf (elaborate a) (elaborate b) := ⟨rfl, rfl, rfl, rfl⟩

end Polars

/-! ## Doubles: Polars's `%` is the floored remainder

`x % y` of doubles under `Profile.polars` is `x - y * floor(x / y)` in the
reference's double operations, which is Polars's `%` for a column divisor
(polars-double-modulus). A literal divisor takes the reciprocal kernel for
`/`, and `%` is that same formula over it (polars-scalar-divisor), so the
engine runs it on the translated route too. Where Polars gives NaN
(`x % 0`, a finite `x % ±∞`) the profile raises, as the reference does
(D21). The numeric rows of the fact are checked against Polars in
`engines/polars/tests/test_polars_profile.py`. -/

/-- **Polars's `%` of doubles** is `x - y * floor(x / y)`, in the reference's
operations. -/
theorem Profile.polars_fmod (a b : Int) :
    Profile.polars.bin .fmod (.float a) (.float b) =
      (do let q ← Profile.reference.bin .fdiv (.float a) (.float b)
          let q ← Profile.reference.un .ffloor q
          let p ← Profile.reference.bin .fmul (.float b) q
          Profile.reference.bin .fsub (.float a) p) := by
  simp only [Profile.polars, BinFn.polarsTmpl, Polars.floorFmodT, Expr.floorFmodOf, Expr.evalP, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, bind, Except.bind]
  rcases h1 : Profile.reference.bin .fdiv (.float a) (.float b) with _ | q <;> simp only []
  rcases h2 : Profile.reference.un .ffloor q with _ | f <;> simp only []

/-- A zero divisor of a double `%` raises under `Profile.polars`, as in the
reference (D21: Polars gives NaN, which a verified plan never reaches). -/
theorem Profile.polars_fmod_zero_divisor (a b : Int) (h : FloatCode.canon b = 0) :
    Profile.polars.bin .fmod (.float a) (.float b) = .error .divByZero := by
  rw [Profile.polars_fmod]
  have : Profile.reference.bin .fdiv (.float a) (.float b) = .error .divByZero := by
    simp [Profile.reference, BinFn.issue, h, raiseIf]; rfl
  simp [this, bind, Except.bind]

/-! ## `round` and `ceil`: IEEE's `-0.0` (`round_zero_sign`) -/

/-- Polars's `round` or `ceil` of a double (`Polars.negZeroT`), for `f` the
rounding `g` of the codes: `-0.0` for a negative value that rounds to zero,
else the reference's. -/
theorem Profile.polars_un_negZero {f : UnFn} {g : Int → Int}
    (hf : f.polarsTmpl = some (Polars.negZeroT f))
    (href : ∀ c, Profile.reference.un f (.float c) = .ok (.float (g c)))
    (hz : g FloatCode.negZero = FloatCode.negZero) (hn : g FloatCode.negNan = FloatCode.negNan)
    (hcan : ∀ c, FloatCode.canon c = c → FloatCode.canon (g c) = g c) (c : Int) :
    Profile.polars.un f (.float c) =
      (if c < 0 ∧ g c = 0 then some (Except.ok (.float FloatCode.negZero)) else none).getD
        (.ok (.float (g c))) := by
  have hlt' : ∀ a b : Int, BinFn.apply .lt (.float a) (.float b) =
      .bool (decide (FloatCode.canon a < FloatCode.canon b)) := fun _ _ => rfl
  have heq' : ∀ a b : Int, BinFn.apply .eq (.float a) (.float b) =
      .bool (FloatCode.canon a == FloatCode.canon b) := fun _ _ => rfl
  have hZ := FloatCode.negZero_eq'; have hY := FloatCode.negNan_eq'
  have hq : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  simp only [Profile.polars, hf, Polars.negZeroT, Expr.evalP, List.getD_cons_zero, Outcome.ok_bind,
    Lowering.ref_lt, Lowering.ref_eq, Lowering.ref_and, href, hlt']
  rcases FloatCode.canon_cases c with ⟨rfl, h0⟩ | ⟨rfl, h0⟩ | h0
  · have : ¬ (FloatCode.negZero = 0) := by omega
    simp [heq', this, h0, hz, FloatCode.canon_zero, and3, Value.isTrue]
  · have : ¬ (FloatCode.negNan = 0) := by omega
    have hn1 : ¬ (FloatCode.nan < 0) := by omega
    simp [heq', this, hn1, h0, hn, FloatCode.canon_zero, and3, Value.isTrue]
  · have hr := hcan c h0
    have hb : (g c == 0) = decide (g c = 0) := rfl
    by_cases hneg : c < 0 <;> by_cases hr0 : g c = 0 <;>
      simp [heq', h0, hr, hneg, hr0, hb, FloatCode.canon_zero, and3, Value.isTrue]

/-- On a value that is not a double, Polars's unary functions other than the
decimal rescale are the reference's. -/
theorem Profile.polars_un_not_float (f : UnFn) (v : Value) (hv : ∀ c, v ≠ .float c)
    (hd : ∀ k, f ≠ .dround k) :
    Profile.polars.un f v = Profile.reference.un f v := by
  unfold Profile.polars; dsimp only
  cases hf : f.polarsTmpl with
  | none => rfl
  | some t =>
    have : f = .fround ∨ f = .fceil ∨ f = .froundEven ∨ (∃ s, f = .ftod s) ∨ ∃ k, f = .dround k := by
      cases f <;> simp_all [UnFn.polarsTmpl]
    obtain rfl | rfl | rfl | ⟨s, rfl⟩ | ⟨k, rfl⟩ := this
    all_goals first
      | exact absurd rfl (hd _)
      | (simp only [UnFn.polarsTmpl, Option.some.injEq] at hf
         subst hf
         cases v <;> first | rfl | exact absurd rfl (hv _))

/-- `round` on Polars, through `Lowering.zeroTemplate`, agrees with the
reference: the lowering's entry for `round` (`round_zero_sign`). -/
theorem Polars.fround_agree (x : Value) :
    (Lowering.froundTemplate.evalP Profile.polars [x]).Agree (Profile.reference.un .fround x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (p := Profile.polars) (fun x y => Lowering.ref_lt x y) (fun x y => Lowering.ref_eq x y)
      (fun x y => Lowering.ref_and x y)
      (Profile.polars_un_negZero (f := .fround) rfl (fun _ => rfl) FloatCode.round_negZero FloatCode.round_negNan
        (fun _ h => FloatCode.canon_round h))
      (fun _ => rfl) FloatCode.round_negZero FloatCode.round_negNan (fun _ h => FloatCode.canon_round h) c
  all_goals rfl

/-- `round(mode='half_to_even')` on Polars, through `Lowering.zeroTemplate`, agrees with the
reference: the lowering's entry for `froundEven` (`round_zero_sign`). -/
theorem Polars.froundEven_agree (x : Value) :
    (Lowering.froundEvenTemplate.evalP Profile.polars [x]).Agree
      (Profile.reference.un .froundEven x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (p := Profile.polars) (fun x y => Lowering.ref_lt x y) (fun x y => Lowering.ref_eq x y)
      (fun x y => Lowering.ref_and x y)
      (Profile.polars_un_negZero (f := .froundEven) rfl (fun _ => rfl) FloatCode.roundEven_negZero
        FloatCode.roundEven_negNan (fun _ h => FloatCode.canon_roundEven h))
      (fun _ => rfl) FloatCode.roundEven_negZero FloatCode.roundEven_negNan
      (fun _ h => FloatCode.canon_roundEven h) c
  all_goals rfl

/-- `ceil` on Polars, through `Lowering.zeroTemplate`, agrees with the
reference. -/
theorem Polars.fceil_agree (x : Value) :
    (Lowering.fceilTemplate.evalP Profile.polars [x]).Agree (Profile.reference.un .fceil x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (p := Profile.polars) (fun x y => Lowering.ref_lt x y) (fun x y => Lowering.ref_eq x y)
      (fun x y => Lowering.ref_and x y)
      (Profile.polars_un_negZero (f := .fceil) rfl (fun _ => rfl) FloatCode.ceil_negZero FloatCode.ceil_negNan
        (fun _ h => FloatCode.canon_ceil h))
      (fun _ => rfl) FloatCode.ceil_negZero FloatCode.ceil_negNan (fun _ h => FloatCode.canon_ceil h) c
  all_goals rfl

-- Each case of `Profile.polars` against Polars's probed value (C1, ruling 235):
-- `round(-0.4)` and `ceil(-0.4)` are `-0.0` (polars-round), `round(-0.5)` is
-- `-1.0` (`mode='half_away_from_zero'`), `7 // -2` is `-4` and `7 % -2` is `-1`
-- (polars-int-divide, polars-int-modulus), `7.5 % -2.0` is `-0.5`
-- (polars-double-modulus).
#guard letI := Boxes.Ambient.none
  match Profile.polars.un .fround (.float (FloatCode.ofFloat (-0.4))) with
  | .ok (.float c) => c == FloatCode.negZero | _ => false
#guard letI := Boxes.Ambient.none
  match Profile.polars.un .fceil (.float (FloatCode.ofFloat (-0.4))) with
  | .ok (.float c) => c == FloatCode.negZero | _ => false
#guard letI := Boxes.Ambient.none
  match Profile.polars.un .fround (.float (FloatCode.ofFloat (-0.5))) with
  | .ok (.float c) => c == FloatCode.ofFloat (-1.0) | _ => false
#guard letI := Boxes.Ambient.none
  match Profile.polars.bin .idiv (.int 7) (.int (-2)) with
  | .ok (.int c) => c == -4 | _ => false
#guard letI := Boxes.Ambient.none
  match Profile.polars.bin .imod (.int 7) (.int (-2)) with
  | .ok (.int c) => c == -1 | _ => false
#guard letI := Boxes.Ambient.none
  match Profile.polars.bin .fmod (.float (FloatCode.ofFloat 7.5)) (.float (FloatCode.ofFloat (-2.0))) with
  | .ok (.float c) => c == FloatCode.ofFloat (-0.5) | _ => false

-- A double cast to a decimal (polars-decimal-casts, ruling 278): `0.125`,
-- `-0.125`, `0.375` and `0.625` at scale 2 are `0.12`, `-0.12`, `0.38` and `0.62`,
-- `2.5` and `-2.5` at scale 0 are `2` and `-2`, where the reference gives `0.13`,
-- `-0.13`, `0.38`, `0.63`, `3` and `-3`; the near-ties `1.005` and `-2.675`,
-- whose products are no ties, are `1.00` and `-2.68` on both.
#guard letI := Boxes.Ambient.none
  [(0.125, 2, 12, 13), (-0.125, 2, -12, -13), (0.375, 2, 38, 38), (0.625, 2, 62, 63),
    (2.5, 0, 2, 3), (-2.5, 0, -2, -3), (3.5, 0, 4, 4), (1.005, 2, 100, 100),
    (-2.675, 2, -268, -268)].all fun (x, s, polars, ref) =>
  (match Profile.polars.un (.ftod s) (.float (FloatCode.ofFloat x)) with
    | .ok (.int m) => m == polars | _ => false) &&
  (match Profile.reference.un (.ftod s) (.float (FloatCode.ofFloat x)) with
    | .ok (.int m) => m == ref | _ => false)

-- A decimal cast to a smaller scale (polars-decimal-casts, ruling 278's
-- addendum): `0.125` and `-0.125` at scale 3 to scale 2 are `0.12` and `-0.12`,
-- `0.250` at scale 3 to scale 1 is `0.2`, where the reference gives `0.13`,
-- `-0.13` and `0.3`; `0.135` is `0.14` on both. On every unscaled value of
-- `-300` to `300` and a rescale by 0 to 3 digits, the profile's cast is
-- `Polars.rescaleEven`, the trusted model of Polars's (`Polars/Shims.lean`).
#guard letI := Boxes.Ambient.none
  [(125, 1, 12, 13), (-125, 1, -12, -13), (250, 2, 2, 3), (135, 1, 14, 14)].all
    fun (i, k, polars, ref) =>
  (match Profile.polars.un (.dround k) (.dec 3 i) with
    | .ok (.int m) => m == polars | _ => false) &&
  (match Profile.reference.un (.dround k) (.dec 3 i) with
    | .ok (.int m) => m == ref | _ => false)
#guard letI := Boxes.Ambient.none
  (List.range 4).all fun k => (List.range 601).all fun j =>
    match Profile.polars.un (.dround k) (.dec 3 ((j : Int) - 300)) with
    | .ok (.int m) => m == Polars.rescaleEven k ((j : Int) - 300)
    | _ => false
#guard letI := Boxes.Ambient.none
  [Value.null, .str "a", .float 0].all fun v =>
    match Profile.polars.un (.dround 1) v with | .ok .null => true | _ => false

end Substrait
