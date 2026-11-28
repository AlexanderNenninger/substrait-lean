import Sverify.Polars.Profile

/-!
# Polars's lowering: the hand-written templates (#271)

The entries of Polars's generated lowering (`Sverify.Polars.LoweringOn`) that
the search does not reach: integer `//` and `%`, which floor on Polars
(`Profile.polars`, `division_type` = `FLOOR`) where the reference truncates.
Each template calls Polars's `//` or `%` only on operands of one sign, where
floored and truncated agree, and handles operands of opposite signs with
exact arithmetic (`dadd`, `dsub`, the 128-bit integers of decimals), so no
step raises where the reference gives a value, on integers of any width.
`round` and `ceil` are `Lowering.froundTemplate` and `fceilTemplate`
(`Polars.fround_agree`, `Polars.fceil_agree`). A decimal cast to a smaller
scale, which rounds half to even on Polars, is `Polars.droundAwayT`, the
reference's half away from zero from Polars's truncation (`Polars.droundEntry`,
ruling 278's addendum). `>>` and `<<`, which Polars lacks, are `Polars.shrTemplate`, the floor
division by `2ᵏ` (`Polars.bit_shr_agree`), and `Polars.shlTemplate`, the
low bits times `2ᵏ` with the next bit as the sign (`Polars.bit_shl_agree`).
-/

namespace Substrait

variable [Boxes.Ambient]

namespace Polars

/-! ## Polars's functions that are the reference's -/

theorem polars_lt_int (x y : Int) :
    Profile.polars.bin .lt (.int x) (.int y) = .ok (.bool (decide (x < y))) := ref_lt_int x y
theorem polars_and_bool (p q : Bool) :
    Profile.polars.bin .and (.bool p) (.bool q) = .ok (.bool (p && q)) := by
  show Profile.reference.bin .and _ _ = _
  rw [Lowering.ref_and]; cases p <;> cases q <;> rfl
theorem polars_or_bool (p q : Bool) :
    Profile.polars.bin .or (.bool p) (.bool q) = .ok (.bool (p || q)) := by
  show Profile.reference.bin .or _ _ = _
  rw [Lowering.ref_or]; cases p <;> cases q <;> rfl
theorem polars_dadd_int (x y : Int) :
    Profile.polars.bin .dadd (.int x) (.int y) = .ok (.int (x + y)) := Lowering.ref_dadd _ _
theorem polars_dsub_int (x y : Int) :
    Profile.polars.bin .dsub (.int x) (.int y) = .ok (.int (x - y)) := Lowering.ref_dsub _ _

/-- Polars's `//` of two integers of one sign (or a zero) is the reference's:
the floored and the truncated quotient agree. -/
theorem polars_idiv_same {x y : Int} (h1 : ¬(x < 0 ∧ 0 < y)) (h2 : ¬(y < 0 ∧ 0 < x)) :
    Profile.polars.bin .idiv (.int x) (.int y) = Profile.reference.bin .idiv (.int x) (.int y) := by
  simp only [Profile.polars, BinFn.polarsTmpl, floorDivT, Expr.floorDivOf, Expr.evalP, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ref_lt_int, bind,
    Except.bind, isTrue_bool, decide_eq_true_eq]
  by_cases hx : x < 0
  · simp only [hx, ↓reduceIte, show ¬(0 < y) by omega]
  · by_cases hy : y < 0
    · simp only [hx, hy, ↓reduceIte, show ¬(0 < x) by omega]
    · simp only [hx, hy, ↓reduceIte]

/-- Polars's `%` of two integers of one sign (or a zero) is the reference's. -/
theorem polars_imod_same {x y : Int} (h1 : ¬(x < 0 ∧ 0 < y)) (h2 : ¬(y < 0 ∧ 0 < x)) :
    Profile.polars.bin .imod (.int x) (.int y) = Profile.reference.bin .imod (.int x) (.int y) := by
  simp only [Profile.polars, BinFn.polarsTmpl, floorModT, Expr.floorModOf, Expr.evalP, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ref_lt_int, bind,
    Except.bind, isTrue_bool, decide_eq_true_eq]
  by_cases hx : x < 0
  · simp only [hx, ↓reduceIte, show ¬(0 < y) by omega]
  · by_cases hy : y < 0
    · simp only [hx, hy, ↓reduceIte, show ¬(0 < x) by omega]
    · simp only [hx, hy, ↓reduceIte]

/-! ## The truncated quotient from a quotient of one sign -/

omit [Boxes.Ambient] in
/-- `a // b` for `a < 0 < b` and `|a| ≥ b`, from `(-a - b) // b`, both
operands not negative. -/
theorem tdiv_apart_neg {a b : Int} (ha : a < 0) (hb : 0 < b) (hab : a + b ≤ 0) :
    (-a - b).tdiv b = -(a.tdiv b) - 1 := by
  have h1 : (-a - b).tdiv b = (-a - b) / b := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have h2 : a.tdiv b = -((-a) / b) := by
    rw [← Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -a), Int.neg_tdiv, Int.neg_neg]
  have h3 : (-a - b) / b = (-a) / b + -1 := by
    rw [show -a - b = -a + -1 * b by omega]
    exact Int.add_mul_ediv_right (-a) (-1) (by omega)
  rw [h1, h2, h3]; omega

omit [Boxes.Ambient] in
/-- `a // b` for `b < 0 < a` and `a ≥ |b|`, from `-(a + b) // b`, both
operands not positive. -/
theorem tdiv_apart_pos {a b : Int} (ha : 0 < a) (hb : b < 0) (hab : 0 ≤ a + b) :
    (-(a + b)).tdiv b = -(a.tdiv b) - 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = -c := ⟨-b, by omega⟩
  have e1 : (-(a + -c)).tdiv (-c) = -((a + -c).tdiv (-c)) := Int.neg_tdiv _ _
  have e2 : (a + -c).tdiv (-c) = -((a + -c).tdiv c) := Int.tdiv_neg _ _
  have e3 : a.tdiv (-c) = -(a.tdiv c) := Int.tdiv_neg _ _
  have e4 : (a + -c).tdiv c = (a + -c) / c := Int.tdiv_eq_ediv_of_nonneg hab
  have e5 : a.tdiv c = a / c := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have e6 : (a + -c) / c = a / c + -1 := by
    rw [show a + -c = a + -1 * c by omega]
    exact Int.add_mul_ediv_right a (-1) (by omega)
  omega

omit [Boxes.Ambient] in
theorem tdiv_small_neg {a b : Int} (ha : a < 0) (hab : 0 < a + b) : a.tdiv b = 0 := by
  rw [show a = -(-a) by omega, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega),
    Int.ediv_eq_zero_of_lt (by omega) (by omega)]; rfl

omit [Boxes.Ambient] in
theorem tdiv_small_pos {a b : Int} (ha : 0 < a) (_hb : b < 0) (hab : a + b < 0) : a.tdiv b = 0 := by
  rw [show b = -(-b) by omega, Int.tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega),
    Int.ediv_eq_zero_of_lt (by omega) (by omega)]; rfl

/-! ## The templates -/

/-- `a // b` truncated, on Polars: for `a < 0 < b`, `0` where `a + b > 0`,
else `-((-a - b) // b) - 1`; for `b < 0 < a`, `0` where `a + b < 0`, else
`-(-(a + b) // b) - 1`; otherwise Polars's `//`, whose operands have one sign.
The quotient of one sign is at most `2⁶³ - 1` exactly where the result is at
least `-2⁶³`, so it raises where the reference does. -/
def idivTemplate : Expr :=
  let a := Expr.field 0
  let b := Expr.field 1
  let z := Expr.lit (.int 0)
  let neg (e : Expr) := Expr.bin .dsub z e
  .ifThen (.bin .and (.bin .lt a z) (.bin .lt z b))
    (.ifThen (.bin .lt z (.bin .dadd a b)) z
      (.bin .dsub (neg (.bin .idiv (.bin .dsub (neg a) b) b)) (.lit (.int 1))))
    (.ifThen (.bin .and (.bin .lt b z) (.bin .lt z a))
      (.ifThen (.bin .lt (.bin .dadd a b) z) z
        (.bin .dsub (neg (.bin .idiv (neg (.bin .dadd a b)) b)) (.lit (.int 1))))
      (.bin .idiv a b))

/-- `a % b` truncated, on Polars: the remainder by `-b` where the signs
differ (`a % -b = a % b` truncated, and the operands then have one sign),
else Polars's `%`. -/
def imodTemplate : Expr :=
  let a := Expr.field 0
  let b := Expr.field 1
  let z := Expr.lit (.int 0)
  .ifThen (.bin .or (.bin .and (.bin .lt a z) (.bin .lt z b)) (.bin .and (.bin .lt b z) (.bin .lt z a)))
    (.bin .imod a (.bin .dsub z b)) (.bin .imod a b)

omit [Boxes.Ambient] in
theorem idivTemplate_must : 0 ∈ idivTemplate.must ∧ 1 ∈ idivTemplate.must := by
  simp [Expr.must, idivTemplate]

omit [Boxes.Ambient] in
theorem imodTemplate_must : 0 ∈ imodTemplate.must ∧ 1 ∈ imodTemplate.must := by
  simp [Expr.must, imodTemplate]

/-! ## They agree with the reference -/

theorem ref_idiv_eq (x y : Int) (h0 : y ≠ 0) :
    Profile.reference.bin .idiv (.int x) (.int y) =
      if inI64 (x.tdiv y) then .ok (.int (x.tdiv y)) else .error .overflow := by
  have ha : BinFn.apply .idiv (.int x) (.int y) = .int (x.tdiv y) := by
    simp only [BinFn.apply.eq_def]; simp [h0]
  show raiseIf (BinFn.issue .idiv (.int x) (.int y)) (BinFn.apply .idiv (.int x) (.int y)) = _
  by_cases h : inI64 (x.tdiv y) <;> simp [raiseIf, BinFn.issue, h0, h, ha, Issue.isError]

omit [Boxes.Ambient] in
/-- `-t - 1` is in 64 bits exactly where `t ≤ -1` is. -/
theorem inI64_neg_sub_one {t : Int} (ht : t ≤ -1) : inI64 (-t - 1) = inI64 t := by
  apply Bool.eq_iff_iff.mpr; rw [inI64_iff, inI64_iff]; omega

/-- On two integers. -/
theorem idivTemplate_int (a b : Int) :
    (idivTemplate.evalP Profile.polars [.int a, .int b]).Agree
      (Profile.reference.bin .idiv (.int a) (.int b)) := by
  simp only [idivTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_lt_int, polars_and_bool, polars_dadd_int, polars_dsub_int, bind,
    Except.bind, isTrue_bool, Bool.and_eq_true, decide_eq_true_eq]
  by_cases c1 : a < 0 ∧ 0 < b
  · have hb0 : b ≠ 0 := by omega
    simp only [eq_true c1, ↓reduceIte]
    by_cases c2 : 0 < a + b
    · simp only [eq_true c2, ↓reduceIte]
      rw [ref_idiv_eq a b hb0, tdiv_small_neg c1.1 c2]
      simp [Outcome.Agree, show inI64 0 = true from rfl]
    · simp only [eq_false c2, ↓reduceIte]
      rw [polars_idiv_same (by omega) (by omega), ref_idiv_eq _ _ hb0, ref_idiv_eq _ _ hb0]
      have hq := tdiv_apart_neg c1.1 c1.2 (by omega)
      have : 0 ≤ (-a - b).tdiv b := Int.tdiv_nonneg (by omega) (by omega)
      rw [show (0 : Int) - a - b = -a - b by omega, hq, inI64_neg_sub_one (by omega)]
      by_cases h : inI64 (a.tdiv b) = true
      · simp only [h, ↓reduceIte, polars_dsub_int, Outcome.Agree, Value.int.injEq]; omega
      · simp only [h, Bool.false_eq_true, ↓reduceIte, Outcome.Agree]
  · simp only [eq_false c1, ↓reduceIte]
    by_cases c3 : b < 0 ∧ 0 < a
    · have hb0 : b ≠ 0 := by omega
      simp only [eq_true c3, ↓reduceIte]
      by_cases c4 : a + b < 0
      · simp only [eq_true c4, ↓reduceIte]
        rw [ref_idiv_eq a b hb0, tdiv_small_pos c3.2 c3.1 c4]
        simp [Outcome.Agree, show inI64 0 = true from rfl]
      · simp only [eq_false c4, ↓reduceIte]
        rw [polars_idiv_same (by omega) (by omega), ref_idiv_eq _ _ hb0, ref_idiv_eq _ _ hb0]
        have hq := tdiv_apart_pos c3.2 c3.1 (by omega)
        have : 0 ≤ (-(a + b)).tdiv b := by
          have e1 : (-(a + b)).tdiv b = -((-(a + b)).tdiv (-b)) := by
            rw [Int.tdiv_neg, Int.neg_neg]
          have e2 : (-(a + b)).tdiv (-b) = -((a + b).tdiv (-b)) := Int.neg_tdiv _ _
          have e3 : 0 ≤ (a + b).tdiv (-b) := Int.tdiv_nonneg (by omega) (by omega)
          omega
        rw [show (0 : Int) - (a + b) = -(a + b) by omega, hq, inI64_neg_sub_one (by omega)]
        by_cases h : inI64 (a.tdiv b) = true
        · simp only [h, ↓reduceIte, polars_dsub_int, Outcome.Agree, Value.int.injEq]; omega
        · simp only [h, Bool.false_eq_true, ↓reduceIte, Outcome.Agree]
    · simp only [eq_false c3, ↓reduceIte]
      rw [polars_idiv_same c1 c3]
      exact Outcome.agree_refl _

/-- On two integers. -/
theorem imodTemplate_int (a b : Int) :
    (imodTemplate.evalP Profile.polars [.int a, .int b]).Agree
      (Profile.reference.bin .imod (.int a) (.int b)) := by
  simp only [imodTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_lt_int, polars_and_bool, polars_or_bool, polars_dsub_int, bind,
    Except.bind, isTrue_bool, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  by_cases c : (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a)
  · have hb0 : b ≠ 0 := by omega
    simp only [eq_true c, ↓reduceIte]
    rw [show (0 : Int) - b = -b by omega, polars_imod_same (by omega) (by omega),
      Lowering.ref_imod_int _ _ (by omega), Lowering.ref_imod_int _ _ hb0, Int.tmod_neg]
    exact Outcome.agree_refl _
  · simp only [eq_false c, ↓reduceIte]
    rw [polars_imod_same (fun h => c (.inl h)) (fun h => c (.inr h))]
    exact Outcome.agree_refl _

/-! ## A value that is not an integer

The comparisons of a template's guards with `0` are `NULL` there, so no guard
holds, and every function of the template gives `NULL`, as the reference's
`//` and `%` do. -/

/-- `v` is not an integer. -/
def NotInt (v : Value) : Prop := ∀ a, v ≠ .int a

theorem apply_lt_notInt_l {x : Value} (hx : NotInt x) (c : Int) : BinFn.apply .lt x (.int c) = .null := by
  cases x <;> first | rfl | exact absurd rfl (hx _)

theorem apply_lt_notInt_r {y : Value} (hy : NotInt y) (c : Int) : BinFn.apply .lt (.int c) y = .null := by
  cases y <;> first | rfl | exact absurd rfl (hy _)

omit [Boxes.Ambient] in
theorem isTrue_and3_null_l (v : Value) : (and3 .null v).isTrue = false := by
  cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

omit [Boxes.Ambient] in
theorem isTrue_and3_null_r (v : Value) : (and3 v .null).isTrue = false := by
  cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

omit [Boxes.Ambient] in
theorem isTrue_null : Value.null.isTrue = false := rfl

theorem ref_idiv_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    Profile.reference.bin .idiv x y = .ok .null := by
  rcases h with h | h <;> cases x <;> cases y <;>
    first | rfl | exact absurd rfl (h _)

/-- Polars's `//` of a value that is not an integer is `NULL`. -/
theorem polars_idiv_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    Profile.polars.bin .idiv x y = .ok .null := by
  simp only [Profile.polars, BinFn.polarsTmpl, floorDivT, Expr.floorDivOf, Expr.evalP, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Lowering.ref_lt, bind,
    Except.bind]
  rcases h with h | h
  · simp only [apply_lt_notInt_l h, apply_lt_notInt_r h, isTrue_null, Bool.false_eq_true, ↓reduceIte,
      ref_idiv_notInt (.inl h), ite_self]
  · simp only [apply_lt_notInt_l h, apply_lt_notInt_r h, isTrue_null, Bool.false_eq_true, ↓reduceIte,
      ref_idiv_notInt (.inr h), ite_self]

theorem polars_lt : Profile.polars.bin .lt = Profile.reference.bin .lt := rfl
theorem polars_and : Profile.polars.bin .and = Profile.reference.bin .and := rfl
theorem polars_or : Profile.polars.bin .or = Profile.reference.bin .or := rfl

theorem idivTemplate_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    (idivTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .idiv x y) := by
  simp only [idivTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_lt, polars_and, Lowering.ref_lt, Lowering.ref_and, bind, Except.bind]
  rcases id h with h' | h' <;>
    simp only [apply_lt_notInt_l h', apply_lt_notInt_r h', isTrue_and3_null_l, isTrue_and3_null_r,
      Bool.false_eq_true, ↓reduceIte, polars_idiv_notInt h, ref_idiv_notInt h] <;>
    exact Outcome.agree_refl _

/-- **Polars's lowering of `//`** (`idivTemplate`) agrees with the reference's
on every value. -/
theorem idiv_agree (x y : Value) :
    (idivTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .idiv x y) := by
  cases x
  case int a =>
    cases y
    case int b => exact idivTemplate_int a b
    all_goals exact idivTemplate_notInt (.inr fun _ h => by cases h)
  all_goals exact idivTemplate_notInt (.inl fun _ h => by cases h)


/-- Polars's `%` where an argument is not an integer is the reference's (`%`
of a time of day by an integer included). -/
theorem polars_imod_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    Profile.polars.bin .imod x y = Profile.reference.bin .imod x y := by
  simp only [Profile.polars, BinFn.polarsTmpl, floorModT, Expr.floorModOf, Expr.evalP, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Lowering.ref_lt, bind,
    Except.bind]
  rcases h with h | h <;>
    simp only [apply_lt_notInt_l h, apply_lt_notInt_r h, isTrue_null, Bool.false_eq_true, ↓reduceIte,
      ite_self]

omit [Boxes.Ambient] in
theorem and3_null_l (v : Value) : and3 .null v = .null ∨ and3 .null v = .bool false := by
  cases v <;> first | exact .inl rfl | (rename_i b; cases b <;> first | exact .inl rfl | exact .inr rfl)

omit [Boxes.Ambient] in
theorem and3_null_r (v : Value) : and3 v .null = .null ∨ and3 v .null = .bool false := by
  cases v <;> first | exact .inl rfl | (rename_i b; cases b <;> first | exact .inl rfl | exact .inr rfl)

omit [Boxes.Ambient] in
theorem isTrue_or3_not {v w : Value} (hv : v = .null ∨ v = .bool false)
    (hw : w = .null ∨ w = .bool false) : (or3 v w).isTrue = false := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> rfl

theorem imodTemplate_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    (imodTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .imod x y) := by
  simp only [imodTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_lt, polars_and, polars_or, Lowering.ref_lt, Lowering.ref_and,
    Lowering.ref_or, bind, Except.bind]
  rcases id h with h' | h'
  · simp only [apply_lt_notInt_l h', apply_lt_notInt_r h',
      isTrue_or3_not (and3_null_l _) (and3_null_r _), Bool.false_eq_true, ↓reduceIte,
      polars_imod_notInt h]
    exact Outcome.agree_refl _
  · simp only [apply_lt_notInt_l h', apply_lt_notInt_r h',
      isTrue_or3_not (and3_null_r _) (and3_null_l _), Bool.false_eq_true, ↓reduceIte,
      polars_imod_notInt h]
    exact Outcome.agree_refl _

/-- **Polars's lowering of `%`** (`imodTemplate`) agrees with the reference's
on every value. -/
theorem imod_agree (x y : Value) :
    (imodTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .imod x y) := by
  cases x
  case int a =>
    cases y
    case int b => exact imodTemplate_int a b
    all_goals exact imodTemplate_notInt (.inr fun _ h => by cases h)
  all_goals exact imodTemplate_notInt (.inl fun _ h => by cases h)

/-! ## Decimal `%` (D62)

Polars's decimal `%` floors (`Profile.polars_dmod`). The template takes the
remainder by the negated divisor where the operands' signs differ, so that
Polars's `%` sees operands of one sign, where floored and truncated agree: the
`int_mod_trunc` shim on the unscaled integers. The signs are read on the
unscaled integers (`a + 0`), since a decimal and the integer `0` do not
compare. -/

/-- `a % b` of decimals truncated, on Polars: Polars's `%` by `-b` where the
signs differ, else Polars's `%`. -/
def dmodTemplate : Expr :=
  let a := Expr.field 0
  let b := Expr.field 1
  let z := Expr.lit (.int 0)
  let x := Expr.bin .dadd a z
  let y := Expr.bin .dadd b z
  .ifThen (.bin .or (.bin .and (.bin .lt x z) (.bin .lt z y)) (.bin .and (.bin .lt y z) (.bin .lt z x)))
    (.bin .dmod a (.bin .dsub z y)) (.bin .dmod a b)

omit [Boxes.Ambient] in
theorem dmodTemplate_must : 0 ∈ dmodTemplate.must ∧ 1 ∈ dmodTemplate.must := by
  simp [Expr.must, dmodTemplate]

theorem polars_dadd_zero_some {x : Value} {a : Int} (hx : x.unscaled? = some a) :
    Profile.polars.bin .dadd x (.int 0) = .ok (.int a) := by
  show Profile.reference.bin .dadd _ _ = _
  rw [Lowering.ref_dadd]; simp only [BinFn.apply, hx]; simp

/-- On two numbers. -/
theorem dmodTemplate_num {x y : Value} {a b : Int} (hx : x.unscaled? = some a)
    (hy : y.unscaled? = some b) :
    (dmodTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .dmod x y) := by
  simp only [dmodTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_dadd_zero_some hx, polars_dadd_zero_some hy, polars_lt_int,
    polars_and_bool, polars_or_bool, polars_dsub_int, bind, Except.bind, isTrue_bool,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  by_cases c : (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a)
  · have hb0 : b ≠ 0 := by omega
    simp only [eq_true c, ↓reduceIte]
    rw [Profile.polars_dmod hx (show (Value.int (0 - b)).unscaled? = some (0 - b) from rfl) (by omega),
      Lowering.ref_dmod hx hy hb0, Polars.floorMod,
      (Polars.fdiv_fmod_same (a := a) (b := 0 - b) (by omega) (by omega)).2,
      show (0 : Int) - b = -b by omega, Int.tmod_neg]
    exact Outcome.agree_refl _
  · simp only [eq_false c, ↓reduceIte]
    by_cases hb0 : b = 0
    · subst hb0
      rw [Profile.polars_dmod_zero hx hy, Lowering.ref_dmod_zero hx hy]
      exact Outcome.agree_refl _
    · rw [Profile.polars_dmod hx hy hb0, Lowering.ref_dmod hx hy hb0, Polars.floorMod,
        (Polars.fdiv_fmod_same (a := a) (b := b) (by omega) (by omega)).2]
      exact Outcome.agree_refl _

/-- A guard of `dmodTemplate` with a `NULL` operand never holds. -/
theorem isTrue_signs_null {u v : Value} (h : u = .null ∨ v = .null) :
    (or3 (and3 (BinFn.apply .lt u (.int 0)) (BinFn.apply .lt (.int 0) v))
      (and3 (BinFn.apply .lt v (.int 0)) (BinFn.apply .lt (.int 0) u))).isTrue = false := by
  rcases h with rfl | rfl
  · exact isTrue_or3_not (and3_null_l _) (and3_null_r _)
  · exact isTrue_or3_not (and3_null_r _) (and3_null_l _)

theorem polars_dadd : Profile.polars.bin .dadd = Profile.reference.bin .dadd := rfl

/-- With an operand that is not a number (`NULL`). -/
theorem dmodTemplate_null {x y : Value} (h : x.unscaled? = none ∨ y.unscaled? = none) :
    (dmodTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .dmod x y) := by
  rw [Lowering.ref_dmod_null h]
  have hn : BinFn.apply .dadd x (.int 0) = .null ∨ BinFn.apply .dadd y (.int 0) = .null := by
    rcases h with h | h
    · left; simp only [BinFn.apply, h]
    · right; simp only [BinFn.apply, h]
  simp only [dmodTemplate, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, polars_dadd, Lowering.ref_dadd, polars_lt, polars_and, polars_or,
    Lowering.ref_lt, Lowering.ref_and, Lowering.ref_or, bind, Except.bind, isTrue_signs_null hn,
    Bool.false_eq_true, ↓reduceIte, Profile.polars_dmod_null h]
  exact Outcome.agree_refl _

/-- **Polars's lowering of decimal `%`** (`dmodTemplate`) agrees with the
reference's on every value. -/
theorem dmod_agree (x y : Value) :
    (dmodTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .dmod x y) := by
  cases hx : x.unscaled? with
  | none => exact dmodTemplate_null (.inl hx)
  | some a =>
    cases hy : y.unscaled? with
    | none => exact dmodTemplate_null (.inr hy)
    | some b => exact dmodTemplate_num hx hy

/-! ## A decimal cast to a smaller scale: half away from zero (ruling 278's addendum) -/

/-- The reference's decimal cast to a scale `k` digits smaller, from Polars's
functions, as `shims.decimal_round_half_away` writes it: `x ± 10ᵏ/2` in 128-bit
integers (`dadd`, `dsub`), by `x`'s sign, truncated toward zero (`dtrunc`).
Polars's own cast rounds half to even (`Profile.polars`, polars-decimal-casts).
The sign is that of `x + 0`, `x`'s unscaled value as an integer. -/
def droundAwayT (k : Nat) : Expr :=
  let h : Expr := .lit (.int ((10 ^ k / 2 : Nat) : Int))
  .ifThen (.bin .lt (.bin .dadd (.field 0) (.lit (.int 0))) (.lit (.int 0)))
    (.un (.dtrunc k) (.bin .dsub (.field 0) h)) (.un (.dtrunc k) (.bin .dadd (.field 0) h))

omit [Boxes.Ambient] in
/-- `roundDiv10` through truncation: `i ± 10ᵏ/2`, by `i`'s sign, truncated
toward zero. -/
theorem roundDiv10_tdiv (k : Nat) (i : Int) :
    roundDiv10 k i = if i < 0 then (i - ((10 ^ k / 2 : Nat) : Int)).tdiv (10 ^ k)
      else (i + ((10 ^ k / 2 : Nat) : Int)).tdiv (10 ^ k) := by
  have hp : ((10 ^ k : Nat) : Int) = 10 ^ k := by norm_cast
  unfold roundDiv10
  generalize 10 ^ k / 2 = H
  by_cases hi : i < 0
  · have hn : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
    have e : i - (H : Int) = -((i.natAbs + H : Nat) : Int) := by push_cast; omega
    simp only [hi, ↓reduceIte, e, Int.neg_tdiv, ← hp, Int.neg_inj]
    exact Int.ofNat_tdiv _ _
  · have hn : (i.natAbs : Int) = i := Int.natAbs_of_nonneg (by omega)
    have e : i + (H : Int) = ((i.natAbs + H : Nat) : Int) := by push_cast; omega
    simp only [hi, ↓reduceIte, e, ← hp]
    exact Int.ofNat_tdiv _ _

theorem apply_dadd_of {x : Value} {i : Int} (hx : x.unscaled? = some i) (j : Int) :
    BinFn.apply .dadd x (.int j) = .int (i + j) := by
  cases x <;> simp only [Value.unscaled?, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> rfl

theorem apply_dsub_of {x : Value} {i : Int} (hx : x.unscaled? = some i) (j : Int) :
    BinFn.apply .dsub x (.int j) = .int (i - j) := by
  cases x <;> simp only [Value.unscaled?, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> rfl

/-- `droundAwayT` of a decimal or an integer is the reference's rescale of its
unscaled value. -/
theorem droundAwayT_eval (k : Nat) {x : Value} {i : Int} (hx : x.unscaled? = some i) :
    (droundAwayT k).evalP Profile.polars [x] = .ok (.int (roundDiv10 k i)) := by
  have hdt : ∀ j : Int, Profile.polars.un (.dtrunc k) (.int j) = .ok (.int (j.tdiv (10 ^ k))) :=
    fun _ => rfl
  have hadd : ∀ j : Int, Profile.polars.bin .dadd x (.int j) = .ok (.int (i + j)) := fun j => by
    show Profile.reference.bin .dadd x (.int j) = _
    rw [Lowering.ref_dadd, apply_dadd_of hx]
  have hsub : ∀ j : Int, Profile.polars.bin .dsub x (.int j) = .ok (.int (i - j)) := fun j => by
    show Profile.reference.bin .dsub x (.int j) = _
    rw [Lowering.ref_dsub, apply_dsub_of hx]
  simp only [droundAwayT, Expr.evalP, List.getD_cons_zero, Outcome.ok_bind, hadd, hsub,
    polars_lt_int, hdt, isTrue_bool, Int.add_zero, roundDiv10_tdiv]
  by_cases hi : i < 0 <;> simp [hi]

/-- **Polars's lowering of a decimal cast to a smaller scale** (`droundAwayT`)
agrees with the reference's on every value: the shim
`decimal_round_half_away`, which `Polars.decimal_round_half_away` proves of the
written expression. -/
theorem dround_agree (k : Nat) (x : Value) :
    ((droundAwayT k).evalP Profile.polars [x]).Agree (Profile.reference.un (.dround k) x) := by
  cases x
  case int i => rw [droundAwayT_eval k (i := i) rfl]; rfl
  case dec s i => rw [droundAwayT_eval k (i := i) rfl]; rfl
  all_goals rfl

/-- **Polars's entry for a decimal cast to a smaller scale**, hand-built: the
generator's search does not reach `droundAwayT`, whose literals depend on the
scale (`LoweringSearch.polarsSchemas`). Exact on every value. -/
def droundEntry (k : Nat) : UnEntry Profile.polars (.dround k) :=
  .ofAgree (droundAwayT k) (by simp [droundAwayT, Expr.must]) (dround_agree k)

/-! ## `&`, `|` and `^`

Polars has them (`&`, `|`, `^` of Int64), but not `<<` and `>>`, so the
regeneration names `BinFn.bit` among the functions Polars lacks
(`scripts/RegenLoweringPolars.lean`) and these three take the native call as
a hand-written schema. -/

/-- `#0 & #1`. -/
def bitAndT : Expr := .bin (.bit .and) (.field 0) (.field 1)
/-- `#0 | #1`. -/
def bitOrT : Expr := .bin (.bit .or) (.field 0) (.field 1)
/-- `#0 ^ #1`. -/
def bitXorT : Expr := .bin (.bit .xor) (.field 0) (.field 1)

omit [Boxes.Ambient] in
theorem bitAndT_must : 0 ∈ bitAndT.must ∧ 1 ∈ bitAndT.must := by simp [bitAndT, Expr.must]
omit [Boxes.Ambient] in
theorem bitOrT_must : 0 ∈ bitOrT.must ∧ 1 ∈ bitOrT.must := by simp [bitOrT, Expr.must]
omit [Boxes.Ambient] in
theorem bitXorT_must : 0 ∈ bitXorT.must ∧ 1 ∈ bitXorT.must := by simp [bitXorT, Expr.must]

/-- Polars's bitwise functions are the reference's. -/
theorem bit_native_agree (op : BitOp) (x y : Value) :
    ((Expr.bin (.bit op) (.field 0) (.field 1)).evalP Profile.polars [x, y]).Agree
      (Profile.reference.bin (.bit op) x y) := by
  simp only [Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind]
  exact Outcome.agree_refl _

theorem bit_and_agree (x y : Value) : (bitAndT.evalP Profile.polars [x, y]).Agree
    (Profile.reference.bin (.bit .and) x y) := bit_native_agree .and x y
theorem bit_or_agree (x y : Value) : (bitOrT.evalP Profile.polars [x, y]).Agree
    (Profile.reference.bin (.bit .or) x y) := bit_native_agree .or x y
theorem bit_xor_agree (x y : Value) : (bitXorT.evalP Profile.polars [x, y]).Agree
    (Profile.reference.bin (.bit .xor) x y) := bit_native_agree .xor x y

/-! ## `>>` -/

/-- `#1 < 0 OR NOT #1 < n`. -/
def shrOutside (n : Int) : Expr :=
  .bin .or (.bin .lt (.field 1) (.lit (.int 0))) (.un .not (.bin .lt (.field 1) (.lit (.int n))))

/-- `2 ^ #1` for `#1` in `0`–`62`, else `2 ^ 0`. -/
def shrPow : Expr := .bin .ipow (.lit (.int 2)) (.ifThen (shrOutside 63) (.lit (.int 0)) (.field 1))

/-- `CASE WHEN #0 IS INT AND (#1 < 0 OR NOT #1 < 64) THEN error ELSE (CASE WHEN
#1 = 63 THEN (w // 2⁶²) // 2 ELSE w // 2 ^ #1 END) END` with `w = #0 & -1`:
the reference's `>>`, which raises outside `0`–`63`, from Polars's floored `//`,
since Polars has no shift (polars-int-shift). `w` is `#0` read at 64 bits, as
`BitOp.apply` reads it, and `2⁶³` does not fit, so a shift by 63 divides
twice. Polars computes every branch on every row, so the exponent is `0`
outside `0`–`62` (`shrPow`): `**` fails the whole query on a negative one
(polars-int-pow-exponent). -/
def shrTemplate : Expr :=
  let w := Expr.bin (.bit .and) (.field 0) (.lit (.int (-1)))
  .ifThen (.bin .and (.un (.isNum .int) (.field 0)) (shrOutside 64))
    (.un (.raise "domain error") (.field 1))
    (.ifThen (.bin .eq (.field 1) (.lit (.int 63)))
      (.bin .idiv (.bin .idiv w (.lit (.int (2 ^ 62)))) (.lit (.int 2)))
      (.bin .idiv w shrPow))

omit [Boxes.Ambient] in
theorem shrTemplate_must : 0 ∈ shrTemplate.must ∧ 1 ∈ shrTemplate.must := by
  simp [Expr.must, shrTemplate, shrOutside, shrPow]

/-! ### Its steps -/

omit [Boxes.Ambient] in
theorem ofInt_neg_one : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide

/-- `x & -1` is `x` read at 64 bits. -/
theorem polars_bitAnd_neg_one (a : Int) :
    Profile.polars.bin (.bit .and) (.int a) (.int (-1)) = .ok (.int (BitVec.ofInt 64 a).toInt) := by
  have h : BitOp.apply .and a (-1) = some (BitVec.ofInt 64 a).toInt := by
    simp only [BitOp.apply, ofInt_neg_one, BitVec.and_allOnes]
  show Profile.reference.bin (.bit .and) (.int a) (.int (-1)) = _
  simp [Profile.reference, raiseIf, BinFn.issue, domainIssue, BinFn.apply, h]

omit [Boxes.Ambient] in
theorem inI64_toInt (a : Int) : inI64 (BitVec.ofInt 64 a).toInt = true := by
  have h1 := BitVec.toInt_lt (x := BitVec.ofInt 64 a)
  have h2 := BitVec.le_toInt (x := BitVec.ofInt 64 a)
  rw [inI64_iff]; simp at h1 h2 ⊢; omega

theorem polars_ipow_two {b : Int} (h0 : 0 ≤ b) (h : b < 63) :
    Profile.polars.bin .ipow (.int 2) (.int b) = .ok (.int (2 ^ b.toNat)) := by
  show Profile.reference.bin .ipow (.int 2) (.int b) = _
  have hn : 2 ^ b.toNat ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp : (2 : Int) ^ b.toNat ≤ 2 ^ 62 := by exact_mod_cast hn
  have hp0 : 0 < (2 : Int) ^ b.toNat := by exact_mod_cast Nat.two_pow_pos b.toNat
  have hi : inI64 ((2 : Int) ^ b.toNat) = true := by rw [inI64_iff]; omega
  simp only [Profile.reference]
  simp [raiseIf, BinFn.issue, BinFn.apply, hi, show ¬ b < 0 by omega, show ¬ 64 < b by omega]

/-- Polars's `//` by a positive 64-bit divisor is the floor, `Int`'s `/`. -/
theorem polars_idiv_pos {w p : Int} (hw : inI64 w = true) (hp : inI64 p = true) (h0 : 0 < p) :
    Profile.polars.bin .idiv (.int w) (.int p) = .ok (.int (w / p)) := by
  rw [Profile.polars_idiv hw hp (by omega) (by omega), floorDiv, Int.fdiv_eq_ediv_of_nonneg _ (by omega)]

/-- The reference's `>>` inside `0`–`63`: the floor of `x` at 64 bits by `2ᵇ`. -/
theorem ref_shr_int (a b : Int) (h0 : 0 ≤ b) (h : b < 64) :
    Profile.reference.bin (.bit .shr) (.int a) (.int b) =
      .ok (.int ((BitVec.ofInt 64 a).toInt / 2 ^ b.toNat)) := by
  simp only [Profile.reference]
  simp [raiseIf, BinFn.issue, domainIssue, BitOp.apply, BinFn.apply, h0, h,
    BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]

omit [Boxes.Ambient] in
theorem inI64_two_pow {n : Nat} (h : n ≤ 62) : inI64 ((2 : Int) ^ n) = true := by
  have hn : 2 ^ n ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) h
  have hp : (2 : Int) ^ n ≤ 2 ^ 62 := by exact_mod_cast hn
  have hp0 : 0 < (2 : Int) ^ n := by exact_mod_cast Nat.two_pow_pos n
  rw [inI64_iff]; omega

theorem polars_isNum_ok (k : NumKind) (x : Value) :
    Profile.polars.un (.isNum k) x = .ok (.bool (x.isNum k)) := Lowering.ref_isNum k x
theorem polars_not_ok (x : Value) :
    Profile.polars.un .not x = .ok (match x with | .bool b => .bool !b | _ => .null) :=
  Lowering.ref_not x
theorem polars_raise_ok (m : String) (x : Value) : Profile.polars.un (.raise m) x = .error .raised :=
  Lowering.ref_raise m x
theorem polars_lt_ok (x y : Value) : Profile.polars.bin .lt x y = .ok (BinFn.apply .lt x y) :=
  Lowering.ref_lt x y
theorem polars_eq_ok (x y : Value) : Profile.polars.bin .eq x y = .ok (BinFn.apply .eq x y) :=
  Lowering.ref_eq x y
theorem polars_and_ok (x y : Value) : Profile.polars.bin .and x y = .ok (and3 x y) := Lowering.ref_and x y
theorem polars_or_ok (x y : Value) : Profile.polars.bin .or x y = .ok (or3 x y) := Lowering.ref_or x y

theorem apply_lt_int (a b : Int) : BinFn.apply .lt (.int a) (.int b) = .bool (decide (a < b)) := rfl
theorem apply_eq_int (a b : Int) : BinFn.apply .eq (.int a) (.int b) = .bool (a == b) := by
  simp [BinFn.apply]

omit [Boxes.Ambient] in
theorem and3_bool (p q : Bool) : and3 (.bool p) (.bool q) = .bool (p && q) := by
  cases p <;> cases q <;> rfl
omit [Boxes.Ambient] in
theorem or3_bool (p q : Bool) : or3 (.bool p) (.bool q) = .bool (p || q) := by
  cases p <;> cases q <;> rfl

omit [Boxes.Ambient] in
theorem inI64_ediv_two_pow_62 {w : Int} (hw : inI64 w = true) : inI64 (w / 2 ^ 62) = true := by
  rw [inI64_iff] at hw ⊢
  rw [show (2 : Int) ^ 62 = 4611686018427387904 from rfl]; omega

/-- On two integers. -/
theorem shr_int (a b : Int) :
    (shrTemplate.evalP Profile.polars [.int a, .int b]).Agree
      (Profile.reference.bin (.bit .shr) (.int a) (.int b)) := by
  simp only [shrTemplate, shrOutside, shrPow, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    polars_isNum_ok, polars_lt_ok, polars_or_ok, polars_not_ok, polars_and_ok, polars_raise_ok, polars_eq_ok,
    apply_lt_int, apply_eq_int, Value.isNum, polars_bitAnd_neg_one, and3_bool, or3_bool, isTrue_bool,
    Bool.true_and]
  have hw := inI64_toInt a
  by_cases hr : 0 ≤ b ∧ b < 64
  · rw [ref_shr_int a b hr.1 hr.2]
    have h1 : ¬ b < 0 := by omega
    by_cases h63 : b = 63
    · have e63 : (b == 63) = true := by simp [h63]
      simp only [h1, hr.2, e63, decide_false, decide_true, Bool.not_true, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte]
      rw [polars_idiv_pos (p := 2 ^ 62) hw rfl (by decide), Outcome.ok_bind,
        polars_idiv_pos (p := 2) (inI64_ediv_two_pow_62 hw) rfl (by decide),
        Int.ediv_ediv_of_nonneg (by decide), h63]
      rfl
    · have h2 : b < 63 := by omega
      have e63 : (b == 63) = false := by simp [h63]
      simp only [h1, h2, e63, hr.2, decide_false, decide_true, Bool.not_true, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte, Outcome.ok_bind]
      rw [polars_ipow_two hr.1 h2, Outcome.ok_bind, polars_idiv_pos hw (inI64_two_pow (by omega))
        (by exact_mod_cast Nat.two_pow_pos _)]
      exact Outcome.agree_refl _
  · have hc : (decide (b < 0) || !decide (b < 64)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    have hr' : Profile.reference.bin (.bit .shr) (.int a) (.int b) = .error .domain := by
      simp [Profile.reference, raiseIf, BinFn.issue, domainIssue, BitOp.apply, hr, Issue.isError]
    simp [hc, hr', Outcome.Agree]

theorem polars_bitAnd_notInt {x : Value} (h : NotInt x) :
    Profile.polars.bin (.bit .and) x (.int (-1)) = .ok .null := by
  cases x <;> first | rfl | exact absurd rfl (h _)

/-- `shrPow` never raises. -/
theorem shrPow_ok (x y : Value) : ∃ v, shrPow.evalP Profile.polars [x, y] = .ok v := by
  simp only [shrPow, shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, polars_lt_ok, polars_or_ok, polars_not_ok]
  cases y
  case int b =>
    simp only [apply_lt_int, or3_bool, isTrue_bool]
    by_cases h : b < 0 ∨ ¬ b < 63
    · have hc : (decide (b < 0) || !decide (b < 63)) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        exact h
      simp only [hc, ↓reduceIte, Outcome.ok_bind]
      exact ⟨_, polars_ipow_two (b := 0) (by decide) (by decide)⟩
    · have hc : (decide (b < 0) || !decide (b < 63)) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false',
          decide_eq_true_eq]
        omega
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Outcome.ok_bind]
      exact ⟨_, polars_ipow_two (by omega) (by omega)⟩
  all_goals exact ⟨_, rfl⟩

theorem shrOutside_ok (n : Int) (x y : Value) : ∃ g, (shrOutside n).evalP Profile.polars [x, y] = .ok g := by
  simp only [shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    polars_lt_ok, polars_or_ok, polars_not_ok]
  exact ⟨_, rfl⟩

theorem shrOutside_notInt (n : Int) (x : Value) {y : Value} (hy : NotInt y) :
    (shrOutside n).evalP Profile.polars [x, y] = .ok .null := by
  simp only [shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    polars_lt_ok, polars_or_ok, polars_not_ok, apply_lt_notInt_l hy]
  rfl

omit [Boxes.Ambient] in
theorem isTrue_and3_false (v : Value) : (and3 (.bool false) v).isTrue = false := by
  cases v <;> first | rfl | (rename_i b; cases b <;> rfl)

omit [Boxes.Ambient] in
theorem isNum_notInt {x : Value} (h : NotInt x) : x.isNum .int = false := by
  cases x <;> first | rfl | exact absurd rfl (h _)

theorem apply_eq_notInt {y : Value} (hy : NotInt y) (c : Int) : BinFn.apply .eq y (.int c) = .null := by
  cases y <;> first | rfl | exact absurd rfl (hy _)

/-- Where an argument is not an integer, every step gives `NULL`, as the
reference's `>>` does. -/
theorem shr_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    (shrTemplate.evalP Profile.polars [x, y]).Agree
      (Profile.reference.bin (.bit .shr) x y) := by
  have hr : Profile.reference.bin (.bit .shr) x y = .ok .null := by
    rcases h with h | h <;> cases x <;> cases y <;> first | rfl | exact absurd rfl (h _)
  rw [hr]
  have hnull : NotInt Value.null := fun _ h => by cases h
  simp only [shrTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    polars_isNum_ok, polars_and_ok, polars_eq_ok, polars_raise_ok]
  rcases h with hx | hy
  · obtain ⟨g, hg⟩ := shrOutside_ok 64 x y
    obtain ⟨v, hv⟩ := shrPow_ok x y
    simp only [hg, Outcome.ok_bind, isNum_notInt hx, isTrue_and3_false, Bool.false_eq_true,
      ↓reduceIte, polars_bitAnd_notInt hx, polars_idiv_notInt (.inl hnull), hv]
    split <;> exact Outcome.agree_refl _
  · have hv : shrPow.evalP Profile.polars [x, y] = .ok .null := by
      simp only [shrPow, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
        shrOutside_notInt 63 x hy, isTrue_null, Bool.false_eq_true, ↓reduceIte]
      cases y <;> first | rfl | exact absurd rfl (hy _)
    obtain ⟨w, hw⟩ : ∃ w, Profile.polars.bin (.bit .and) x (.int (-1)) = .ok w := by
      cases x <;> first | exact ⟨_, rfl⟩ | exact ⟨_, polars_bitAnd_neg_one _⟩
    simp only [shrOutside_notInt 64 x hy, Outcome.ok_bind, isTrue_and3_null_r, Bool.false_eq_true,
      ↓reduceIte, apply_eq_notInt hy, isTrue_null, hw, hv, polars_idiv_notInt (.inr hnull)]
    exact Outcome.agree_refl _

/-- **Polars's lowering of `>>`** (`shrTemplate`) agrees with the reference on
every value. -/
theorem bit_shr_agree (x y : Value) :
    (shrTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin (.bit .shr) x y) := by
  cases x
  case int a =>
    cases y
    case int b => exact shr_int a b
    all_goals exact shr_notInt (.inr fun _ h => by cases h)
  all_goals exact shr_notInt (.inl fun _ h => by cases h)

/-! ## `<<` -/

/-- `#1` where it is in `0`–`63`, else `0`. -/
def shlK : Expr := .ifThen (shrOutside 64) (.lit (.int 0)) (.field 1)

/-- `2 ^ (63 - k)` for `k = shlK` in `1`–`63`, else `2 ^ 0`. -/
def shlLow : Expr :=
  let j := Expr.bin .sub (.lit (.int 63)) shlK
  .bin .ipow (.lit (.int 2)) (.ifThen (.un .not (.bin .lt j (.lit (.int 63)))) (.lit (.int 0)) j)

/-- `CASE WHEN #0 IS INT AND (#1 < 0 OR NOT #1 < 64) THEN error WHEN #1 = 0 THEN w
WHEN (w // 2ʲ) % 2 = 1 THEN (w % 2ʲ) · 2ᵏ + MIN ELSE (w % 2ʲ) · 2ᵏ END`, with
`k = #1`, `j = 63 - k` and `w = #0 & -1`: the reference's `<<`, which drops
the bits shifted out and raises outside `0`–`63`, in Polars's 64-bit
functions, since Polars has no shift (polars-int-shift). The low `j` bits of
`w`, shifted, fit in 63 bits, and bit `j` becomes the sign (`shl_pieces`), so
no step wraps (Polars's `*` would, polars-int-arith, where the profile
raises). As in `shrTemplate`, every exponent is in `0`–`62`. -/
def shlTemplate : Expr :=
  let w := Expr.bin (.bit .and) (.field 0) (.lit (.int (-1)))
  let t := Expr.bin .imod w shlLow
  let c := Expr.bin .imod (.bin .idiv w shlLow) (.lit (.int 2))
  let lo := Expr.bin .mul t shrPow
  .ifThen (.bin .and (.un (.isNum .int) (.field 0)) (shrOutside 64))
    (.un (.raise "domain error") (.field 1))
    (.ifThen (.bin .eq (.field 1) (.lit (.int 0))) w
      (.ifThen (.bin .eq c (.lit (.int 1))) (.bin .add lo (.lit (.int (-2 ^ 63)))) lo))

omit [Boxes.Ambient] in
theorem shlTemplate_must : 0 ∈ shlTemplate.must ∧ 1 ∈ shlTemplate.must := by
  simp [Expr.must, shlTemplate, shrOutside, shrPow, shlLow, shlK]

omit [Boxes.Ambient] in
/-- `x` at 64 bits differs from `x` by a multiple of `2⁶⁴`. -/
theorem toInt_ofInt_eq (a : Int) : ∃ z, (BitVec.ofInt 64 a).toInt = a + 2 ^ 64 * z := by
  rw [BitVec.toInt_ofInt, Int.bmod_def, Int.emod_def]
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  split
  · exact ⟨-(a / 2 ^ 64), by grind⟩
  · exact ⟨-(a / 2 ^ 64) - 1, by grind⟩

omit [Boxes.Ambient] in
/-- **The left shift in 64-bit pieces**: `a · 2ᵏ` wrapped at 64 bits, for
`k` in `1`–`63` and `j = 63 - k`, is `(w mod 2ʲ) · 2ᵏ`, less `2⁶³` where bit
`j` of `w` is set, for `w` congruent to `a` modulo `2⁶⁴`. -/
theorem shl_pieces {a w z : Int} (hz : w = a + 2 ^ 64 * z) {k j : Nat} (hk : j + k = 63) :
    (a * 2 ^ k + 2 ^ 63) % 2 ^ 64 - 2 ^ 63 =
      if (w / 2 ^ j) % 2 = 1 then (w % 2 ^ j) * 2 ^ k - 2 ^ 63 else (w % 2 ^ j) * 2 ^ k := by
  have hP : (0 : Int) < 2 ^ j := by exact_mod_cast Nat.two_pow_pos j
  have hPX : (2 : Int) ^ j * 2 ^ k = 2 ^ 63 := by rw [← Int.pow_add, hk]
  have ht0 : 0 ≤ w % 2 ^ j := Int.emod_nonneg _ (by omega)
  have ht1 : w % 2 ^ j < 2 ^ j := Int.emod_lt_of_pos _ hP
  have hX : (0 : Int) < 2 ^ k := by exact_mod_cast Nat.two_pow_pos k
  have hu1 : (w % 2 ^ j) * 2 ^ k < 2 ^ 63 := by
    rw [← hPX]; exact Int.mul_lt_mul_of_pos_right ht1 hX
  have hu0 : 0 ≤ (w % 2 ^ j) * 2 ^ k := Int.mul_nonneg ht0 (by omega)
  have hc0 : 0 ≤ (w / 2 ^ j) % 2 := Int.emod_nonneg _ (by decide)
  have hc1 : (w / 2 ^ j) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  have hq := Int.emod_add_mul_ediv (w / 2 ^ j) 2
  have hw := Int.emod_add_mul_ediv w (2 ^ j)
  have e : a * 2 ^ k + 2 ^ 63 =
      ((2 ^ 63 * ((w / 2 ^ j) % 2) + (w % 2 ^ j) * 2 ^ k + 2 ^ 63)
        + 2 ^ 64 * ((w / 2 ^ j) / 2 - z * 2 ^ k)) := by
    generalize w / 2 ^ j = q at hq hw
    generalize w % 2 ^ j = t at hw
    generalize q / 2 = r at hq
    generalize q % 2 = c at hq
    generalize (2 : Int) ^ j = P at hPX hw
    generalize (2 : Int) ^ k = X at hPX
    have ha : a = w - 2 ^ 64 * z := by omega
    subst ha
    subst hw
    subst hq
    grind
  rw [e, Int.add_mul_emod_self_left]
  generalize (w / 2 ^ j) % 2 = c at hc0 hc1 ⊢
  generalize (w % 2 ^ j) * 2 ^ k = u at hu0 hu1 ⊢
  split <;> omega

/-! ### Its steps -/

theorem polars_imod_pos {x m : Int} (hx : inI64 x = true) (hm : inI64 m = true) (h0 : 0 < m) :
    Profile.polars.bin .imod (.int x) (.int m) = .ok (.int (x % m)) := by
  rw [Profile.polars_imod hx hm (by omega), floorMod, Int.fmod_eq_emod_of_nonneg _ (by omega)]

theorem polars_mul_i64 {x y : Int} (h : inI64 (x * y) = true) :
    Profile.polars.bin .mul (.int x) (.int y) = .ok (.int (x * y)) := by
  have ha : BinFn.apply .mul (.int x) (.int y) = .int (x * y) := rfl
  show raiseIf (BinFn.issue .mul (.int x) (.int y)) (BinFn.apply .mul (.int x) (.int y)) = _
  simp [raiseIf, BinFn.issue, wrapNum, Value.numOf?, wrapIf, h, ha]

theorem polars_add_i64 {x y : Int} (h : inI64 (x + y) = true) :
    Profile.polars.bin .add (.int x) (.int y) = .ok (.int (x + y)) := by
  have := (inI64_iff _).mp h; exact ref_add_int x y this.1 this.2

theorem polars_sub_i64 {x y : Int} (h : inI64 (x - y) = true) :
    Profile.polars.bin .sub (.int x) (.int y) = .ok (.int (x - y)) := by
  have := (inI64_iff _).mp h; exact ref_sub_int x y this.1 this.2

theorem ref_shl_int (a b : Int) (h0 : 0 ≤ b) (h : b < 64) :
    Profile.reference.bin (.bit .shl) (.int a) (.int b) =
      .ok (.int ((a * 2 ^ b.toNat + 2 ^ 63) % 2 ^ 64 - 2 ^ 63)) := by
  have hs := Lowering.shl_apply a b
  simp only [show ¬ b < 0 by omega, h, ite_false, ite_true] at hs
  simp [Profile.reference, raiseIf, BinFn.issue, domainIssue, BinFn.apply, hs]

omit [Boxes.Ambient] in
theorem inI64_ediv {w P : Int} (hw : inI64 w = true) (hP : 1 ≤ P) : inI64 (w / P) = true := by
  have hw' := (inI64_iff _).mp hw
  have h1 := Int.mul_ediv_add_emod w P
  have h2 := Int.emod_nonneg w (show P ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos w (show 0 < P by omega)
  rw [inI64_iff]
  generalize w / P = q at h1 ⊢
  generalize w % P = t at h1 h2 h3
  have e : (P - 1) * q = P * q - q := by rw [Int.sub_mul, Int.one_mul]
  by_cases hq : 0 ≤ q
  · have : 0 ≤ (P - 1) * q := Int.mul_nonneg (by omega) hq
    omega
  · have : (P - 1) * q ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have : P * q + t < P * q + P := by omega
    have e2 : P * (q + 1) = P * q + P := by rw [Int.mul_add, Int.mul_one]
    have : P * (q + 1) ≤ q + 1 := by
      have : (P - 1) * (q + 1) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have e3 : (P - 1) * (q + 1) = P * (q + 1) - (q + 1) := by rw [Int.sub_mul, Int.one_mul]
      omega
    omega

theorem shrPow_eval (x : Value) {b : Int} (h0 : 0 ≤ b) (h : b < 63) :
    shrPow.evalP Profile.polars [x, .int b] = .ok (.int (2 ^ b.toNat)) := by
  simp only [shrPow, shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, polars_lt_ok, polars_or_ok, polars_not_ok, apply_lt_int, or3_bool, isTrue_bool,
    show ¬ b < 0 by omega, h, decide_false, decide_true, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]
  exact polars_ipow_two h0 h

theorem shrPow_eval_63 (x : Value) : shrPow.evalP Profile.polars [x, .int 63] = .ok (.int 1) := by
  simp only [shrPow, shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, polars_lt_ok, polars_or_ok, polars_not_ok, apply_lt_int, or3_bool, isTrue_bool]
  exact polars_ipow_two (b := 0) (by decide) (by decide)

theorem shlLow_eval (x : Value) {b : Int} (h1 : 1 ≤ b) (h2 : b < 64) :
    shlLow.evalP Profile.polars [x, .int b] = .ok (.int (2 ^ (63 - b).toNat)) := by
  have hj : inI64 (63 - b) = true := by rw [inI64_iff]; omega
  simp only [shlLow, shlK, shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, polars_lt_ok, polars_or_ok, polars_not_ok, apply_lt_int, or3_bool, isTrue_bool,
    show ¬ b < 0 by omega, h2, decide_false, decide_true, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, polars_sub_i64 hj, show 63 - b < 63 by omega]
  exact polars_ipow_two (by omega) (by omega)

/-- On two integers. -/
theorem shl_int (a b : Int) :
    (shlTemplate.evalP Profile.polars [.int a, .int b]).Agree
      (Profile.reference.bin (.bit .shl) (.int a) (.int b)) := by
  simp only [shlTemplate, shrOutside, Expr.evalP, List.getD_cons_zero,
    List.getD_cons_succ, Outcome.ok_bind, polars_isNum_ok, polars_lt_ok, polars_or_ok, polars_not_ok,
    polars_and_ok, polars_raise_ok, polars_eq_ok, apply_lt_int, apply_eq_int, Value.isNum,
    polars_bitAnd_neg_one, and3_bool, or3_bool, isTrue_bool, Bool.true_and]
  have hw := inI64_toInt a
  obtain ⟨z, hz⟩ := toInt_ofInt_eq a
  by_cases hr : 0 ≤ b ∧ b < 64
  · rw [ref_shl_int a b hr.1 hr.2]
    have h1 : ¬ b < 0 := by omega
    simp only [h1, hr.2, decide_false, decide_true, Bool.not_true, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [show ((0 : Int) == 0) = true from rfl, ↓reduceIte, Outcome.Agree, Value.int.injEq]
      rw [BitVec.toInt_ofInt, Lowering.bmod_fit]; simp
    · have e0 : (b == 0) = false := by simp [hb0]
      obtain ⟨n, rfl⟩ : ∃ n : Nat, b = n := ⟨b.toNat, by omega⟩
      have hn : 1 ≤ n ∧ n < 64 := by omega
      have hP0 : (0 : Int) < 2 ^ (63 - n) := by exact_mod_cast Nat.two_pow_pos _
      have hPi : inI64 ((2 : Int) ^ (63 - n)) = true := inI64_two_pow (by omega)
      have hq : inI64 ((BitVec.ofInt 64 a).toInt / 2 ^ (63 - n)) = true := inI64_ediv hw hP0
      have hn' : ((n : Int) - 0).toNat = n := by omega
      simp only [e0, Bool.false_eq_true, ↓reduceIte, shlLow_eval _ (b := (n : Int)) (by omega) (by omega),
        Outcome.ok_bind, show ((63 : Int) - n).toNat = 63 - n by omega,
        polars_imod_pos hw hPi hP0, polars_idiv_pos hw hPi hP0, polars_imod_pos (m := 2) hq rfl (by decide),
        apply_eq_int]
      have hpc := shl_pieces (a := a) (z := z) hz (k := n) (j := 63 - n) (by omega)
      rw [show ((n : Int)).toNat = n by omega, hpc]
      have hX : (0 : Int) < 2 ^ n := by exact_mod_cast Nat.two_pow_pos n
      have hPX : (2 : Int) ^ (63 - n) * 2 ^ n = 2 ^ 63 := by
        rw [← Int.pow_add, show 63 - n + n = 63 by omega]
      generalize (BitVec.ofInt 64 a).toInt = w at hw hq ⊢
      have ht0 : 0 ≤ w % 2 ^ (63 - n) := Int.emod_nonneg _ (by omega)
      have ht1 : w % 2 ^ (63 - n) < 2 ^ (63 - n) := Int.emod_lt_of_pos _ hP0
      have hu1 : (w % 2 ^ (63 - n)) * 2 ^ n < 2 ^ 63 := by
        rw [← hPX]; exact Int.mul_lt_mul_of_pos_right ht1 hX
      have hu0 : 0 ≤ (w % 2 ^ (63 - n)) * 2 ^ n := Int.mul_nonneg ht0 (by omega)
      obtain ⟨F, hF, hTF⟩ : ∃ F, shrPow.evalP Profile.polars [.int a, .int (n : Int)] = .ok (.int F) ∧
          (w % 2 ^ (63 - n)) * F = (w % 2 ^ (63 - n)) * 2 ^ n := by
        by_cases h63 : n = 63
        · subst h63
          refine ⟨1, shrPow_eval_63 _, ?_⟩
          simp [Int.emod_one]
        · exact ⟨_, shrPow_eval _ (b := (n : Int)) (by omega) (by omega),
            by rw [show ((n : Int)).toNat = n by omega]⟩
      have hm : inI64 ((w % 2 ^ (63 - n)) * F) = true := by rw [hTF, inI64_iff]; omega
      rw [hF, Outcome.ok_bind, polars_mul_i64 hm, hTF]
      generalize (w % 2 ^ (63 - n)) * 2 ^ n = u at hu0 hu1 ⊢
      by_cases hc : w / 2 ^ (63 - n) % 2 = 1
      · have ha : inI64 (u + -2 ^ 63) = true := by rw [inI64_iff]; omega
        simp only [hc, beq_self_eq_true, isTrue_bool, ↓reduceIte, Outcome.ok_bind,
          polars_add_i64 ha, Outcome.Agree, Value.int.injEq]
        omega
      · have hc' : (w / 2 ^ (63 - n) % 2 == 1) = false := by simp [hc]
        simp only [hc, hc', isTrue_bool, Bool.false_eq_true, ↓reduceIte]
        exact Outcome.agree_refl _
  · have hc : (decide (b < 0) || !decide (b < 64)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    have hr' : Profile.reference.bin (.bit .shl) (.int a) (.int b) = .error .domain := by
      simp [Profile.reference, raiseIf, BinFn.issue, domainIssue, BitOp.apply, hr, Issue.isError]
    simp [hc, hr', Outcome.Agree]

theorem polars_imod_null_l (v : Value) : Profile.polars.bin .imod .null v = .ok .null := by
  rw [polars_imod_notInt (.inl fun _ h => by cases h)]; cases v <;> rfl
theorem polars_imod_null_r (x : Value) : Profile.polars.bin .imod x .null = .ok .null := by
  rw [polars_imod_notInt (.inr fun _ h => by cases h)]; cases x <;> rfl
theorem polars_mul_null_l (v : Value) : Profile.polars.bin .mul .null v = .ok .null := by
  cases v <;> rfl
theorem polars_add_null_l (v : Value) : Profile.polars.bin .add .null v = .ok .null := by
  cases v <;> rfl
theorem apply_eq_null_l (v : Value) : BinFn.apply .eq .null v = .null := by
  cases v <;> rfl

/-- `shlLow` never raises. -/
theorem shlLow_ok (x y : Value) : ∃ v, shlLow.evalP Profile.polars [x, y] = .ok v := by
  cases y
  case int b =>
    by_cases hr : 1 ≤ b ∧ b < 64
    · exact ⟨_, shlLow_eval x hr.1 hr.2⟩
    · simp only [shlLow, shlK, shrOutside, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
        Outcome.ok_bind, polars_lt_ok, polars_or_ok, polars_not_ok, apply_lt_int, or3_bool,
        isTrue_bool]
      by_cases ho : b < 0 ∨ ¬ b < 64
      · have hc : (decide (b < 0) || !decide (b < 64)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
          exact ho
        simp only [hc, ↓reduceIte, Outcome.ok_bind, polars_sub_i64 (x := 63) (y := 0) rfl,
          apply_lt_int]
        exact ⟨_, polars_ipow_two (b := 0) (by decide) (by decide)⟩
      · have hb : b = 0 := by omega
        subst hb
        simp only [show (decide ((0 : Int) < 0) || !decide ((0 : Int) < 64)) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, Outcome.ok_bind, polars_sub_i64 (x := 63) (y := 0) rfl,
          apply_lt_int]
        exact ⟨_, polars_ipow_two (b := 0) (by decide) (by decide)⟩
  all_goals exact ⟨_, rfl⟩

/-- Where an argument is not an integer, every step gives `NULL`, as the
reference's `<<` does. -/
theorem shl_notInt {x y : Value} (h : NotInt x ∨ NotInt y) :
    (shlTemplate.evalP Profile.polars [x, y]).Agree
      (Profile.reference.bin (.bit .shl) x y) := by
  have hr : Profile.reference.bin (.bit .shl) x y = .ok .null := by
    rcases h with h | h <;> cases x <;> cases y <;> first | rfl | exact absurd rfl (h _)
  rw [hr]
  have hnull : NotInt Value.null := fun _ h => by cases h
  obtain ⟨P, hP⟩ := shlLow_ok x y
  obtain ⟨F, hF⟩ := shrPow_ok x y
  simp only [shlTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    polars_isNum_ok, polars_and_ok, polars_eq_ok, polars_raise_ok, hP, hF]
  rcases h with hx | hy
  · obtain ⟨g, hg⟩ := shrOutside_ok 64 x y
    simp only [hg, Outcome.ok_bind, isNum_notInt hx, isTrue_and3_false, Bool.false_eq_true,
      ↓reduceIte, polars_bitAnd_notInt hx, polars_imod_null_l, polars_idiv_notInt (.inl hnull),
      apply_eq_null_l, isTrue_null, polars_mul_null_l]
    split <;> exact Outcome.agree_refl _
  · obtain ⟨w, hw⟩ : ∃ w, Profile.polars.bin (.bit .and) x (.int (-1)) = .ok w := by
      cases x <;> first | exact ⟨_, rfl⟩ | exact ⟨_, polars_bitAnd_neg_one _⟩
    have hP' : P = .null := by
      have : shlLow.evalP Profile.polars [x, y] = .ok .null := by
        simp only [shlLow, shlK, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
          Outcome.ok_bind, shrOutside_notInt 64 x hy, isTrue_null, Bool.false_eq_true, ↓reduceIte,
          polars_lt_ok, polars_not_ok]
        cases y <;> first | rfl | exact absurd rfl (hy _)
      rw [hP] at this; cases this; rfl
    subst hP'
    simp only [shrOutside_notInt 64 x hy, Outcome.ok_bind, isTrue_and3_null_r, Bool.false_eq_true,
      ↓reduceIte, apply_eq_notInt hy, isTrue_null, hw, polars_imod_null_r,
      polars_idiv_notInt (.inr hnull), polars_imod_null_l, apply_eq_null_l, polars_mul_null_l]
    exact Outcome.agree_refl _

/-- **Polars's lowering of `<<`** (`shlTemplate`) agrees with the reference on
every value. -/
theorem bit_shl_agree (x y : Value) :
    (shlTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin (.bit .shl) x y) := by
  cases x
  case int a =>
    cases y
    case int b => exact shl_int a b
    all_goals exact shl_notInt (.inr fun _ h => by cases h)
  all_goals exact shl_notInt (.inl fun _ h => by cases h)

/-! ## `sverify_split_first` and `strpos` (ruling 286)

Polars's split (polars-split-first) is the reference's `sverify_split_first` but
for a string and an empty pattern (`Polars.splitExcepted`), which `Profile.polars`
keeps as the reference's (ruling 290): every template passes that case through
before the split (`splitGuard`), so the split is reached only elsewhere
(`split_native_not_excepted`). `strpos` is one more than the
characters before the first `t` (`Polars.strpos_chars`), which the split gives
without Polars's `str.find`: for a non-empty `t`, `t` occurs exactly when the
prefix before it is not `s` itself (`splitFirstChars_eq_self`). -/

omit [Boxes.Ambient] in
theorem splitFirstChars_length (t : List Char) :
    ∀ cs, (Text.splitFirstChars t cs).length = splitFirstLen t cs
  | [] => rfl
  | c :: cs => by
    unfold Text.splitFirstChars splitFirstLen
    split <;> simp [splitFirstChars_length t cs]

omit [Boxes.Ambient] in
/-- The prefix before a non-empty `t` is `cs` itself exactly when `t` does not occur. -/
theorem splitFirstChars_eq_self {t : List Char} (ht : t ≠ []) :
    ∀ cs, Text.splitFirstChars t cs = cs ↔ occurs t cs = false
  | [] => by
    cases t with
    | nil => exact absurd rfl ht
    | cons _ _ => simp [Text.splitFirstChars, occurs, List.isPrefixOf]
  | c :: cs => by
    unfold Text.splitFirstChars occurs
    by_cases hp : t.isPrefixOf (c :: cs)
    · simp [hp]
    · simp only [hp, ite_false, Bool.false_or, List.cons.injEq, true_and, Bool.false_eq_true]
      exact splitFirstChars_eq_self ht cs

omit [Boxes.Ambient] in
theorem splitFirst_eq_self {s t : String} (ht : t ≠ "") :
    Text.splitFirst s t = s ↔ occurs t.toList s.toList = false := by
  have ht' : t.toList ≠ [] := fun h => ht (String.toList_eq_nil_iff.mp h)
  unfold Text.splitFirst
  simp only [String.isEmpty_iff, ht, ite_false]
  rw [← splitFirstChars_eq_self ht' s.toList]
  constructor
  · intro h; simpa using congrArg String.toList h
  · intro h; rw [h]; simp

omit [Boxes.Ambient] in
theorem splitFirst_length {s t : String} (ht : t ≠ "") :
    (Text.splitFirst s t).length = splitFirstLen t.toList s.toList := by
  unfold Text.splitFirst
  simp only [String.isEmpty_iff, ht, ite_false, String.length_ofList, splitFirstChars_length]

omit [Boxes.Ambient] in
theorem capped_length_eq_zero (s : String) : Text.capped s.length = 0 ↔ s = "" := by
  unfold Text.capped Text.sizeCap
  constructor
  · intro h; have : s.length = 0 := by omega
    exact String.length_eq_zero_iff.mp this
  · rintro rfl; rfl

/-- `length` of a value: the capped count of a string's characters, `NULL` otherwise. -/
def lenV : Value → Value
  | .str s => .int (Text.capped s.length)
  | _ => .null

theorem polars_length (v : Value) : Profile.polars.un .length v = .ok (lenV v) := by
  cases v <;> rfl

theorem polars_eq (x y : Value) : Profile.polars.bin .eq x y = .ok (BinFn.apply .eq x y) :=
  Lowering.ref_eq x y

theorem polars_isNum (k : NumKind) (x : Value) :
    Profile.polars.un (.isNum k) x = .ok (.bool (x.isNum k)) := Lowering.ref_isNum k x

theorem polars_and3 (x y : Value) : Profile.polars.bin .and x y = .ok (and3 x y) :=
  Lowering.ref_and x y

theorem polars_ltV (x y : Value) : Profile.polars.bin .lt x y = .ok (BinFn.apply .lt x y) :=
  Lowering.ref_lt x y

theorem eq_lenV_zero (v : Value) :
    BinFn.apply .eq (lenV v) (.int 0) = match v with
      | .str s => .bool (decide (s = ""))
      | _ => .null := by
  cases v <;> try rfl
  rename_i s
  simp only [lenV, BinFn.apply, Value.numPair]
  by_cases h : s = ""
  · subst h; rfl
  · have : ¬Text.capped s.length = 0 := fun e => h ((capped_length_eq_zero s).mp e)
    simp [h, this]

/-- **Polars's split**, as `Profile.polars` states it: the reference's (ruling 290). -/
theorem polars_splitFirst (x y : Value) :
    Profile.polars.bin .splitFirst x y = .ok (match x, y with
      | .str s, .str t => .str (Text.splitFirst s t)
      | _, _ => .null) := by
  show Profile.reference.bin .splitFirst x y = _
  cases x <;> cases y <;> rfl

/-- `length(#0)` is an integer (`#0` is a string) and `length(#1) = 0`: the case where
Polars's split is not the reference's (`Polars.splitExcepted`). -/
def splitGuard : Expr :=
  .bin .and (.un (.isNum .int) (.un .length (.field 0)))
    (.bin .eq (.un .length (.field 1)) (.lit (.int 0)))

/-- `CASE WHEN splitGuard THEN #0 ELSE split(#0, #1) END`: the reference's
`sverify_split_first`, which gives `s` for an empty pattern. -/
def splitFirstSchemaT : Expr := .ifThen splitGuard (.field 0) (.bin .splitFirst (.field 0) (.field 1))

theorem splitGuard_eval (x y : Value) : splitGuard.evalP Profile.polars [x, y] = .ok (match x, y with
    | .str _, .str t => .bool (decide (t = ""))
    | .str _, _ => .null
    | _, _ => .bool false) := by
  simp only [splitGuard, Expr.evalP, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, bind, Except.bind, polars_length, polars_isNum, polars_eq, polars_and3,
    eq_lenV_zero]
  cases x <;> cases y <;> simp [lenV, Value.isNum, and3] <;> (try rename_i t) <;>
    (try cases decide (t = "")) <;> rfl

/-- **P1 (ruling 290): the native split is reached only where it is the reference's.**
Where `splitGuard` does not hold, the arguments are not `Polars.splitExcepted`. -/
theorem split_native_not_excepted {x y : Value}
    (h : ∀ v, splitGuard.evalP Profile.polars [x, y] = .ok v → v.isTrue = false) :
    splitExcepted x y = false := by
  have := h _ (splitGuard_eval x y)
  cases x <;> cases y <;> simp_all [splitExcepted, Value.isTrue]
  rename_i t
  intro ht; subst ht; simp at this

omit [Boxes.Ambient] in
theorem splitFirstSchemaT_must : 0 ∈ splitFirstSchemaT.must ∧ 1 ∈ splitFirstSchemaT.must := by
  simp [Expr.must, splitFirstSchemaT, splitGuard]

theorem ref_splitFirst (x y : Value) :
    Profile.reference.bin .splitFirst x y = .ok (BinFn.apply .splitFirst x y) := by
  cases x <;> cases y <;> rfl

theorem splitFirst_agree (x y : Value) :
    (splitFirstSchemaT.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .splitFirst x y) := by
  simp only [splitFirstSchemaT, splitGuard, Expr.evalP, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, bind, Except.bind, polars_length, polars_isNum,
    polars_eq, polars_and3, eq_lenV_zero, polars_splitFirst, ref_splitFirst]
  cases x <;> cases y <;> simp [lenV, Value.isNum, Value.isTrue, BinFn.apply, Outcome.Agree]
  all_goals first
    | rfl
    | (rename_i s t; by_cases ht : t = "" <;> simp [ht, and3, Text.splitFirst])

/-- **`strpos` from the split** (ruling 286, amended): `1` for an empty `t` (of a
string `s`), `0` where the prefix before `t` is `s` itself, else one more than its
characters, capped as the reference caps positions. Polars's `str.find` is not
called. -/
def strposTemplate : Expr :=
  let sf := Expr.bin .splitFirst (.field 0) (.field 1)
  let lsf := Expr.un .length sf
  .ifThen splitGuard (.lit (.int 1))
    (.ifThen (.bin .eq sf (.field 0)) (.lit (.int 0))
      (.ifThen (.bin .lt lsf (.lit (.int Text.sizeCap))) (.bin .add lsf (.lit (.int 1))) lsf))

omit [Boxes.Ambient] in
theorem strposTemplate_must : 0 ∈ strposTemplate.must ∧ 1 ∈ strposTemplate.must := by
  simp [Expr.must, strposTemplate, splitGuard]

theorem ref_strpos (x y : Value) :
    Profile.reference.bin .strpos x y = .ok (BinFn.apply .strpos x y) := by
  cases x <;> cases y <;> rfl

theorem polars_add_int (a b : Int) (h1 : -2 ^ 63 ≤ a + b) (h2 : a + b ≤ 2 ^ 63 - 1) :
    Profile.polars.bin .add (.int a) (.int b) = .ok (.int (a + b)) := ref_add_int a b h1 h2

omit [Boxes.Ambient] in
theorem strpos_empty (s : String) : Text.strpos s "" = 1 := by
  rw [strpos_chars]; rfl

omit [Boxes.Ambient] in
theorem strpos_absent {s t : String} (ht : t ≠ "") (h : occurs t.toList s.toList = false) :
    Text.strpos s t = 0 := by
  have ht' : t.toList ≠ [] := fun e => ht (String.toList_eq_nil_iff.mp e)
  rw [strpos_chars]; simp [strposChars, ht', h, Text.capped, Text.sizeCap]; decide

omit [Boxes.Ambient] in
theorem strpos_found {s t : String} (ht : t ≠ "") (h : occurs t.toList s.toList = true) :
    Text.strpos s t = Text.capped ((Text.splitFirst s t).length + 1) := by
  have ht' : t.toList ≠ [] := fun e => ht (String.toList_eq_nil_iff.mp e)
  rw [strpos_chars, splitFirst_length ht]; simp [strposChars, ht', h]

theorem apply_eq_str (a b : String) : BinFn.apply .eq (.str a) (.str b) = .bool (a == b) := rfl

theorem strpos_agree (x y : Value) :
    (strposTemplate.evalP Profile.polars [x, y]).Agree (Profile.reference.bin .strpos x y) := by
  simp only [strposTemplate, splitGuard, Expr.evalP, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, bind, Except.bind, polars_length, polars_isNum,
    polars_eq, polars_and3, polars_ltV, eq_lenV_zero, polars_splitFirst, ref_strpos]
  cases x <;> cases y
  case str.str s t =>
    simp only [lenV, Value.isNum]
    by_cases ht : t = ""
    · subst ht
      simp [and3, Value.isTrue, Outcome.Agree, BinFn.apply, strpos_empty]
    · simp only [ht, decide_false, show and3 (.bool true) (.bool false) = .bool false from rfl,
        Polars.isTrue_bool, Bool.false_eq_true, ite_false, apply_eq_str]
      cases ho : occurs t.toList s.toList
      · have he : Text.splitFirst s t = s := (splitFirst_eq_self ht).mpr ho
        simp [he, Outcome.Agree, BinFn.apply, strpos_absent ht ho]
      · have he : Text.splitFirst s t ≠ s := fun e => by
          rw [(splitFirst_eq_self ht).mp e] at ho; cases ho
        simp only [beq_iff_eq, he, ite_false, apply_lt_int, Polars.isTrue_bool, decide_eq_true_eq]
        have hp : BinFn.apply .strpos (.str s) (.str t) = .int (Text.strpos s t) := rfl
        rw [hp, strpos_found ht ho]
        have h0 : (0 : Int) ≤ ((Text.splitFirst s t).length : Int) := Int.natCast_nonneg _
        generalize ((Text.splitFirst s t).length : Int) = n at h0 ⊢
        unfold Text.capped Text.sizeCap
        by_cases hn : n < 2 ^ 32
        · have hm : min n (2 ^ 32) = n := Int.min_eq_left (Int.le_of_lt hn)
          simp only [hm, hn, ↓reduceIte]
          rw [polars_add_int n 1 (by omega) (by omega)]
          simp only [Outcome.Agree, Value.int.injEq]
          omega
        · have hm : min n (2 ^ 32) = 2 ^ 32 := Int.min_eq_right (by omega)
          simp only [hm, Int.lt_irrefl, ↓reduceIte]
          simp only [Outcome.Agree, Value.int.injEq]
          omega
  all_goals simp [lenV, Value.isNum, and3, Value.isTrue, BinFn.apply, Outcome.Agree]

/-- **Polars's entry for `strpos`**, hand-built: `strposTemplate`, exact. -/
def strposEntry : BinEntry Profile.polars .strpos :=
  .ofAgree strposTemplate strposTemplate_must strpos_agree

end Polars

end Substrait
