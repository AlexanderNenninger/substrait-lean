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
ruling 278's addendum).
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

/-- The digits `round(x, d)` is generated for on Polars: from 0 to 22
(polars-round, polars-round-digits). Polars rounds to no negative digits, and
from `d = 23` its multiplier can differ from the reference's `10^d`, which
moves the rounding. -/
def roundDigitsMax : Int := 22

/-- **Polars's entry for `round(x, d)`**, hand-built and partial (ruling 282,
#2586): for `0 ≤ d ≤ 22`, Polars's own `round(d, mode=…)`, rendered with the
mode `Polars.asks` states, which `Profile.polars` states is the reference's
(polars-round's probes, M1); for any other `d`, none, so the lowering refuses
the plan before it runs. -/
def froundToEntry (d : Int) : Option (UnEntry Profile.polars (.froundTo d)) :=
  if 0 ≤ d ∧ d ≤ roundDigitsMax then some (.native (.froundTo d) fun _ => Outcome.agree_refl _)
  else none

-- The range, at its ends and just past them.
#guard letI := Boxes.Ambient.none; (froundToEntry 0).isSome && (froundToEntry 22).isSome
#guard letI := Boxes.Ambient.none; (froundToEntry 23).isNone && (froundToEntry (-1)).isNone

end Polars

end Substrait
