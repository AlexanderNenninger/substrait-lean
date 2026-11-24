import Sverify.Polars.Profile
import Sverify.Polars.Lowering
import Sverify.Polars.LoweringLemmas
import Sverify.Engines.LoweringRaises
import Sverify.Polars.Tables
import Sverify.Engines.Sound

/-!
# Polars's Engine value (#900)

`Engine.polars` runs the plan lowered by the generated table
(`Lowering.polars`, #271) with Polars's functions, `Polars.impl`:
`Profile.polars`'s value wherever the profile gives one, and Polars's own
result where the profile keeps the reference's raise (ruling 255): a wrapped
integer, `NULL` for a zero divisor, NaN. `Polars.impl_within` proves those
within Polars's table, and `Engine.polars_sound` that the run is sound under
guard elimination's side condition (`Engine.GuardFreeSide`), by
`Rel.polars_sound`.
-/

namespace Substrait

/-- The options at which `Polars.impl_within` uses Polars's table. -/
def Profile.polarsExtras : List (Functions.Ctor × String) :=
  [(.bin .add, "overflow"), (.bin .sub, "overflow"), (.bin .mul, "overflow"),
   (.bin .idiv, "on_division_by_zero"), (.bin .imod, "on_division_by_zero"),
   (.bin .idiv, "division_type"), (.bin .imod, "division_type"),
   (.bin .fpow, "on_domain_error"), (.bin .fadd, "nan_creation"), (.bin .fsub, "nan_creation"),
   (.bin .fmul, "nan_creation"), (.bin .fdiv, "nan_creation"), (.bin .fmod, "nan_creation")]

theorem Profile.polars_extras :
    (Profile.polarsExtras.all fun p => extraAtB Profile.polars.table p.1 p.2) = true := by
  decide

variable [Boxes.Ambient]

namespace Polars

/-- **Polars's own result where its profile raises** (D21: `Profile.polars`
keeps the reference's raise there): integer `+ - *` wrap around
(polars-int-arith), integer `//` and `%` by zero are `NULL`
(polars-int-divide, polars-int-modulus), and double operations are IEEE's, NaN
for `∞ - ∞`, `0 · ∞`, `∞ / ∞` and `power`'s domain (polars-double-arith).
Elsewhere the reference's function: no call reaches it where the profile
gives a value. -/
def errBin : BinFn → Value → Value → Value
  | .add, .int a, .int b => .int (wrap64 (a + b))
  | .sub, .int a, .int b => .int (wrap64 (a - b))
  | .mul, .int a, .int b => .int (wrap64 (a * b))
  | .idiv, .int a, .int b => if b = 0 then .null else BinFn.apply .idiv (.int a) (.int b)
  | .imod, .int a, .int b => if b = 0 then .null else BinFn.apply .imod (.int a) (.int b)
  | f, .float a, .float b =>
    if nanCase f a b then .float FloatCode.nan else f.apply (.float a) (.float b)
  | f, v, w => f.apply v w

/-- Polars's functions on the error side: `errBin`, and the reference's unary
ones. -/
def errImpl : Impl := ⟨UnFn.apply, errBin⟩

end Polars

/-- The functions at which `Polars.impl` is not `Profile.polars`'s value
(ruling 259): `%` of doubles. Polars computes it as `x - y * floor(x / y)`
(polars-double-modulus, `Profile.polars_fmod`), which rounds twice where the
reference's `fmod` is exact, and no option of `fp.mod` allows that; Polars's
lowering refuses it (`Lowering.polars_no_fmod`), so no run calls it. -/
def Polars.implExceptions : List BinFn := [.fmod]

/-- **Polars's functions**: `Profile.polars`'s value wherever the profile gives
one, Polars's own (`Polars.errImpl`) where it raises (ruling 255). The value
side is stated once, in the profile. At `Polars.implExceptions` the value is
the reference's, for a call no lowered plan makes (ruling 259). -/
def Polars.impl : Impl :=
  ⟨(Profile.polars.okImplOr Polars.errImpl).un, fun f v w =>
    if f ∈ Polars.implExceptions then f.apply v w
    else (Profile.polars.okImplOr Polars.errImpl).bin f v w⟩

/-- `Polars.impl` is the profile's functions with Polars's error side, at every
call but `Polars.implExceptions`'. -/
theorem Polars.impl_agreeOn {cs : List Functions.Ctor}
    (h : ∀ f ∈ Polars.implExceptions, Functions.Ctor.bin f ∉ cs) :
    Impl.AgreeOn cs Polars.impl (Profile.polars.okImplOr Polars.errImpl) := by
  refine ⟨fun _ _ _ => rfl, fun f hf v w => ?_⟩
  have : f ∉ Polars.implExceptions := fun hx => h f hx hf
  simp only [Polars.impl, this, ↓reduceIte]

/-- **Polars's own results on the error side are within its table**: wrapping
`+ - *` past 64 bits (`overflow`), `//` and `%` by zero
(`on_division_by_zero`), and NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞`
(`nan_creation`), each in its option's scope (D34). -/
theorem Polars.errBin_within (f : BinFn) (v w : Value) :
    Polars.errBin f v w = f.apply v w ∨ CallExtra Profile.polars.table (.bin f) [v, w] := by
  have ovf : ∀ {f : BinFn} {a b : Int}, f.issue (.int a) (.int b) = some .wraps →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int b] := fun hi hx =>
    callExtra_of_at hx (by simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, hi])
  have zero : ∀ {f : BinFn} {a : Int}, extraAtB Profile.polars.table (.bin f)
      "on_division_by_zero" = true →
      CallExtra Profile.polars.table (.bin f) [.int a, .int 0] := fun hx =>
    callExtra_of_at hx (by simp [optionScope, divisorZero])
  have wrap : ∀ {f : BinFn} {a b r : Int}, f.apply (.int a) (.int b) = .int r →
      extraAtB Profile.polars.table (.bin f) "overflow" = true →
      f.issue (.int a) (.int b) = wrapIf r →
      Value.int (Polars.wrap64 r) = f.apply (.int a) (.int b) ∨
        CallExtra Profile.polars.table (.bin f) [.int a, .int b] := by
    intro f a b r hr hx hi
    by_cases h64 : inI64 r = true
    · exact .inl (by rw [hr, Polars.wrap64_of_inI64 h64])
    · exact .inr (ovf (by rw [hi]; simp [wrapIf, h64]) hx)
  unfold Polars.errBin
  split
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · exact wrap rfl (extraAt_of_all Profile.polars_extras (by decide)) (by simp [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?])
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · exact .inl rfl
  · rename_i a b
    split
    · rename_i hb; subst hb; exact .inr (zero (extraAt_of_all Profile.polars_extras (by decide)))
    · exact .inl rfl
  · rename_i a b
    split
    · rename_i hn
      -- IEEE division's NaN is its own value (D39).
      by_cases hi : f = .fdivIeee
      · subst hi; left; simp only [BinFn.apply, fdiv_of_nanCase_ieee hn]
      right
      -- `power` has no `nan_creation`: its NaN is a domain error's.
      by_cases hp : f = .fpow
      · subst hp
        refine callExtra_of_at (o := "on_domain_error") (extraAt_of_all Profile.polars_extras (by decide)) ?_
        have : BinFn.issue .fpow (.float a) (.float b) = some .domain := by
          simp only [BinFn.issue, nanIssue, hn]; split <;> rfl
        simp [optionScope, Functions.Ctor.issue, BinFn.issueAll, this]
      · refine callExtra_of_at (o := "nan_creation") ?_ (by simp [optionScope, hn])
        cases f <;> simp [nanCase] at hn <;> first | exact extraAt_of_all Profile.polars_extras (by decide) | exact absurd rfl hp | exact absurd rfl hi
    · exact .inl rfl
  · exact .inl rfl

/-- **`Profile.polars`'s unary functions are within Polars's table** (S1,
ruling 235): each is the reference's, but `round` and `ceil`'s IEEE `-0.0`
for a negative value that rounds to zero, in the scope of `round_zero_sign`,
which Polars's table allows (`IEEE`, D34), and a double cast to a decimal and
a decimal cast to a smaller scale, in the scope of `decimal_rescale`
(`TIE_TO_EVEN`, ruling 278 and its addendum). -/
theorem Profile.polars_un_within (f : UnFn) (v w : Value) (h : Profile.polars.un f v = .ok w) :
    w = f.apply v ∨ CallExtra Profile.polars.table (.un f) [v] := by
  have hx : ∀ g : UnFn, g = .fround ∨ g = .froundEven ∨ g = .fceil →
      extraAtB Profile.polars.table (.un g) "round_zero_sign" = true := by
    rintro g (rfl | rfl | rfl) <;> decide
  cases hf : f.polarsTmpl with
  | none => simp only [Profile.polars, hf] at h; exact .inl (raiseIf_ok h)
  | some t =>
    have hfc : f = .fround ∨ f = .froundEven ∨ f = .fceil ∨ (∃ s, f = .ftod s) ∨
        ∃ k, f = .dround k := by
      cases f <;> simp only [UnFn.polarsTmpl, reduceCtorEq] at hf <;> simp
    rcases hfc with rfl | rfl | rfl | ⟨s, rfl⟩ | ⟨k, rfl⟩
    · cases v
      case float c =>
        rw [Profile.polars_un_negZero (f := .fround) rfl (fun _ => rfl) FloatCode.round_negZero
          FloatCode.round_negNan (fun _ h => FloatCode.canon_round h)] at h
        by_cases hc : c < 0 ∧ FloatCode.round c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inl rfl)) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)
        (fun _ h => by cases h)).symm.trans h))
    · cases v
      case float c =>
        rw [Profile.polars_un_negZero (f := .froundEven) rfl (fun _ => rfl) FloatCode.roundEven_negZero
          FloatCode.roundEven_negNan (fun _ h => FloatCode.canon_roundEven h)] at h
        by_cases hc : c < 0 ∧ FloatCode.roundEven c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inr (.inl rfl))) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)
        (fun _ h => by cases h)).symm.trans h))
    · cases v
      case float c =>
        rw [Profile.polars_un_negZero (f := .fceil) rfl (fun _ => rfl) FloatCode.ceil_negZero
          FloatCode.ceil_negNan (fun _ h => FloatCode.canon_ceil h)] at h
        by_cases hc : c < 0 ∧ FloatCode.ceil c = 0
        · simp only [hc, and_self, ↓reduceIte, Option.getD_some, Except.ok.injEq] at h
          subst h
          exact .inr (callExtra_of_at (hx _ (.inr (.inr rfl))) (by
            simp [optionScope, Functions.Ctor.result, UnFn.apply, Value.hasZero,
              FloatCode.isZeroCode, hc.2]))
        · simp only [hc, ↓reduceIte, Option.getD_none, Except.ok.injEq] at h
          exact .inl (by rw [← h]; rfl)
      all_goals exact .inl (raiseIf_ok ((Profile.polars_un_not_float _ _ (fun _ h => by cases h)
        (fun _ h => by cases h)).symm.trans h))
    · -- Every double cast to a decimal is in `decimal_rescale`'s scope.
      have hd : extraAtB Profile.polars.table (.un (.ftod s)) "decimal_rescale" = true :=
        (show extraAtB Profile.polars.table (.un (.ftod 0)) "decimal_rescale" = true by decide)
      exact .inr (callExtra_of_at hd (by simp [optionScope]))
    · -- Every decimal cast to a smaller scale is in `decimal_rescale`'s scope.
      have hd : extraAtB Profile.polars.table (.un (.dround k)) "decimal_rescale" = true :=
        (show extraAtB Profile.polars.table (.un (.dround 0)) "decimal_rescale" = true by decide)
      exact .inr (callExtra_of_at hd (by simp [optionScope]))

/-! ## `Profile.polars`'s binary functions are within Polars's table (S1) -/

/-- Where a profile function with a template gives a value, it is the
template's value in Lean's functions. -/
theorem Profile.polars_bin_ok {f : BinFn} {t : Expr} (ht : f.polarsTmpl = some t) {x y v : Value}
    (h : Profile.polars.bin f x y = .ok v) : v = t.eval [x, y] := by
  simp only [Profile.polars, ht] at h
  exact Expr.evalP_reference_ok h

theorem Polars.apply_lt_int (x y : Int) :
    BinFn.apply .lt (.int x) (.int y) = .bool (decide (x < y)) := rfl
theorem Polars.apply_add_int (x y : Int) : BinFn.apply .add (.int x) (.int y) = .int (x + y) := rfl
theorem Polars.apply_sub_int (x y : Int) : BinFn.apply .sub (.int x) (.int y) = .int (x - y) := rfl
theorem Polars.apply_idiv_ne {x y : Int} (hy : y ≠ 0) :
    BinFn.apply .idiv (.int x) (.int y) = .int (x.tdiv y) := by
  simp [BinFn.apply, hy]
theorem Polars.apply_imod_ne {x y : Int} (hy : y ≠ 0) :
    BinFn.apply .imod (.int x) (.int y) = .int (x.tmod y) := by
  simp [BinFn.apply, hy]
theorem Polars.apply_idiv_zero (x : Int) : BinFn.apply .idiv (.int x) (.int 0) = .null := by
  simp [BinFn.apply]
theorem Polars.apply_imod_zero (x : Int) : BinFn.apply .imod (.int x) (.int 0) = .null := by
  simp [BinFn.apply]
theorem Polars.apply_add_null_l (v : Value) : BinFn.apply .add .null v = .null := by
  cases v <;> rfl
theorem Polars.apply_add_null_r (v : Value) : BinFn.apply .add v .null = .null := by
  cases v <;> rfl
theorem Polars.apply_sub_null_r (v : Value) : BinFn.apply .sub v .null = .null := by
  cases v <;> rfl

/-- The floored quotient of integers, in Lean's functions: `NULL` by zero, else
`fdiv`. -/
theorem Polars.floorDivT_eval (a b : Int) :
    Polars.floorDivT.eval [.int a, .int b] = if b = 0 then .null else .int (a.fdiv b) := by
  by_cases hb : b = 0
  · subst hb
    simp only [Polars.floorDivT, Expr.floorDivOf, Expr.eval, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, ↓reduceIte, Polars.apply_add_int,
      Polars.apply_sub_int, Polars.apply_idiv_zero, Polars.apply_add_null_l, ite_self]
  · simp only [hb, ↓reduceIte, Polars.floorDivT, Expr.floorDivOf, Expr.eval, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Polars.apply_lt_int,
      Polars.apply_add_int, Polars.apply_sub_int, Polars.apply_idiv_ne hb, Polars.isTrue_bool,
      decide_eq_true_eq]
    by_cases c1 : a < 0 ∧ 0 < b
    · simp only [c1.1, c1.2, ↓reduceIte, (Polars.fdiv_fmod_neg_pos c1.1 c1.2).1]
    by_cases c2 : 0 < a ∧ b < 0
    · simp only [show ¬a < 0 by omega, c2.1, c2.2, ↓reduceIte,
        (Polars.fdiv_fmod_pos_neg c2.1 c2.2).1]
    · rw [(Polars.fdiv_fmod_same c1 c2).1]
      by_cases d1 : a < 0 <;> by_cases d2 : 0 < b <;> by_cases d3 : b < 0 <;>
        by_cases d4 : 0 < a <;> simp only [d1, d2, d3, d4, ↓reduceIte] <;> omega

/-- The floored remainder of integers, in Lean's functions. -/
theorem Polars.floorModT_eval (a b : Int) :
    Polars.floorModT.eval [.int a, .int b] = if b = 0 then .null else .int (a.fmod b) := by
  by_cases hb : b = 0
  · subst hb
    simp only [Polars.floorModT, Expr.floorModOf, Expr.eval, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, ↓reduceIte, Polars.apply_add_int,
      Polars.apply_sub_int, Polars.apply_imod_zero, Polars.apply_add_null_l,
      Polars.apply_sub_null_r, ite_self]
  · simp only [hb, ↓reduceIte, Polars.floorModT, Expr.floorModOf, Expr.eval, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Polars.apply_lt_int,
      Polars.apply_add_int, Polars.apply_sub_int, Polars.apply_imod_ne hb, Polars.isTrue_bool,
      decide_eq_true_eq]
    by_cases c1 : a < 0 ∧ 0 < b
    · have hn : (-1 - a).tmod b = -(a + 1).tmod b := by
        rw [show -1 - a = -(a + 1) by omega, Int.neg_tmod]
      simp only [c1.1, c1.2, ↓reduceIte, (Polars.fdiv_fmod_neg_pos c1.1 c1.2).2, hn,
        Value.int.injEq]
      omega
    by_cases c2 : 0 < a ∧ b < 0
    · simp only [show ¬a < 0 by omega, c2.1, c2.2, ↓reduceIte,
        (Polars.fdiv_fmod_pos_neg c2.1 c2.2).2]
    · rw [(Polars.fdiv_fmod_same c1 c2).2]
      by_cases d1 : a < 0 <;> by_cases d2 : 0 < b <;> by_cases d3 : b < 0 <;>
        by_cases d4 : 0 < a <;> simp only [d1, d2, d3, d4, ↓reduceIte] <;> omega

omit [Boxes.Ambient] in
/-- A floored quotient or remainder is the truncated one, or the call is in
`division_type`'s scope (`floorDiffers`: the signs differ and the division is
not exact). -/
theorem Polars.floor_or_differs {a b : Int} (h : floorDiffers [.int a, .int b] = false) :
    a.fdiv b = a.tdiv b ∧ a.fmod b = a.tmod b := by
  have hd : a * b < 0 → b ∣ a := fun hab => by
    simp only [floorDiffers, hab, decide_true, Bool.true_and, bne_eq_false_iff_eq] at h
    exact Int.dvd_of_tmod_eq_zero h
  have hdv : b ∣ a → a.fdiv b = a.tdiv b ∧ a.fmod b = a.tmod b := fun hd => by
    rw [Int.tdiv_eq_ediv_of_dvd hd, Int.fdiv_eq_ediv_of_dvd hd, Int.tmod_eq_zero_of_dvd hd,
      Int.fmod_eq_zero_of_dvd hd]
    exact ⟨rfl, rfl⟩
  by_cases c1 : a < 0 ∧ 0 < b
  · exact hdv (hd (Int.mul_neg_of_neg_of_pos c1.1 c1.2))
  by_cases c2 : 0 < a ∧ b < 0
  · exact hdv (hd (Int.mul_neg_of_pos_of_neg c2.1 c2.2))
  · exact Polars.fdiv_fmod_same c1 c2

/-- **`Profile.polars`'s binary functions are within Polars's table** (S1,
ruling 235): the reference's, but the floored `//` and `%` of integers whose
signs differ (`division_type`, `FLOOR`). -/
theorem Polars.idiv_notInt_within {x y v : Value} (hn : Polars.NotInt x ∨ Polars.NotInt y)
    (h : Profile.polars.bin .idiv x y = .ok v) : v = BinFn.apply .idiv x y := by
  rw [Polars.polars_idiv_notInt hn] at h
  cases h
  exact raiseIf_ok (Polars.ref_idiv_notInt hn)

theorem Polars.imod_notInt_within {x y v : Value} (hn : Polars.NotInt x ∨ Polars.NotInt y)
    (h : Profile.polars.bin .imod x y = .ok v) : v = BinFn.apply .imod x y := by
  rw [Polars.polars_imod_notInt hn] at h
  exact raiseIf_ok h

theorem Profile.polars_bin_within (f : BinFn) (v w x : Value) (h : Profile.polars.bin f v w = .ok x)
    (hne : f ≠ .fmod) : x = f.apply v w ∨ CallExtra Profile.polars.table (.bin f) [v, w] := by
  cases hf : f.polarsTmpl with
  | none => simp only [Profile.polars, hf] at h; exact .inl (raiseIf_ok h)
  | some t =>
    have hx := Profile.polars_bin_ok hf h
    have hfc : f = .idiv ∨ f = .imod ∨ f = .fmod := by
      cases f <;> simp only [BinFn.polarsTmpl, reduceCtorEq] at hf <;> simp
    rcases hfc with rfl | rfl | rfl
    rotate_left 2
    · exact absurd rfl hne
    · simp only [BinFn.polarsTmpl, Option.some.injEq] at hf; subst hf
      cases v
      case int a =>
        cases w
        case int b =>
          rw [Polars.floorDivT_eval] at hx; subst hx
          by_cases hb : b = 0
          · subst hb; exact .inl rfl
          by_cases hd : floorDiffers [.int a, .int b]
          · exact .inr (callExtra_of_at (o := "division_type")
              (extraAt_of_all Profile.polars_extras (by decide)) (by simp [optionScope, hd]))
          · left
            rw [(Polars.floor_or_differs (by simpa using hd)).1, Polars.apply_idiv_ne hb]
            simp [hb]
        all_goals exact .inl (Polars.idiv_notInt_within (.inr fun _ hc => by cases hc) h)
      all_goals exact .inl (Polars.idiv_notInt_within (.inl fun _ hc => by cases hc) h)
    · simp only [BinFn.polarsTmpl, Option.some.injEq] at hf; subst hf
      cases v
      case int a =>
        cases w
        case int b =>
          rw [Polars.floorModT_eval] at hx; subst hx
          by_cases hb : b = 0
          · subst hb; exact .inl rfl
          by_cases hd : floorDiffers [.int a, .int b]
          · exact .inr (callExtra_of_at (o := "division_type")
              (extraAt_of_all Profile.polars_extras (by decide)) (by simp [optionScope, hd]))
          · left
            rw [(Polars.floor_or_differs (by simpa using hd)).2, Polars.apply_imod_ne hb]
            simp [hb]
        all_goals exact .inl (Polars.imod_notInt_within (.inr fun _ hc => by cases hc) h)
      all_goals exact .inl (Polars.imod_notInt_within (.inl fun _ hc => by cases hc) h)

/-! ## Polars's lowering calls no `%` of doubles (ruling 259, R1) -/

theorem Lowering.polars_un_tmpl (f : UnFn) (en : UnEntry Profile.polars f)
    (h : Lowering.polars.un f = some en) : Functions.Ctor.bin .fmod ∉ en.tmpl.ctors := by
  cases f <;> simp only [Lowering.polars, polarsOn, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    simp [UnEntry.native, UnEntry.ofAgree, Expr.ctors, Lowering.froundTemplate, Lowering.froundEvenTemplate,
      Lowering.fceilTemplate, Lowering.zeroTemplate, Polars.droundEntry, Polars.droundAwayT]

theorem Lowering.polars_bin_tmpl (f : BinFn) (en : BinEntry Profile.polars f)
    (h : Lowering.polars.bin f = some en) : Functions.Ctor.bin .fmod ∉ en.tmpl.ctors := by
  cases f <;> simp only [Lowering.polars, polarsOn, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    simp [BinEntry.native, BinEntry.ofAgree, Expr.ctors, Polars.idivTemplate, Polars.imodTemplate]

/-- **Polars's lowering calls no `%` of doubles** (R1): the table has no entry
for it (`refusing`), and no template calls it, so no expression of a plan it
lowers does. -/
theorem Lowering.polars_no_fmod {r r' : Rel} (hr : Lowering.polars.lowerRel? r = .ok r') :
    ∀ e ∈ r'.mappedExprs, Functions.Ctor.bin .fmod ∉ e.ctors := fun e' he' => by
  obtain ⟨e, t, ht, rfl⟩ := Lowering.mem_lowerRel? hr he'
  exact Lowering.lower_not_mem_ctors (Lowering.polars_un_tmpl) (Lowering.polars_bin_tmpl) ht

/-- **`Polars.impl` is within Polars's table**: where the profile gives a
value, the profile's (`Profile.polars_un_within`, `Profile.polars_bin_within`),
and Polars's own elsewhere (`Polars.errBin_within`). -/
theorem Polars.impl_within : Polars.impl.Within Profile.polars.table := by
  refine ⟨fun f v => ?_, fun f v w => ?_⟩
  · show (match Profile.polars.un f v with | .ok w => w | .error _ => UnFn.apply f v) = _ ∨ _
    cases hu : Profile.polars.un f v with
    | ok w => exact Profile.polars_un_within f v w hu
    | error _ => exact .inl rfl
  · by_cases hx : f ∈ Polars.implExceptions
    · exact .inl (by simp [Polars.impl, hx])
    simp only [Polars.impl, hx, ↓reduceIte]
    show (match Profile.polars.bin f v w with | .ok x => x | .error _ => Polars.errBin f v w) = _ ∨ _
    cases hb : Profile.polars.bin f v w with
    | ok x => exact Profile.polars_bin_within f v w x hb (by simpa [Polars.implExceptions] using hx)
    | error _ => exact Polars.errBin_within f v w

/-- **A plan Polars's table lowers runs correctly on Polars, or raises**
(ruling 277's second branch, 256 B; for Polars ruling 282): with every guard
kept, the lowered plan gives `Rel.eval`'s rows wherever it does not raise
under Polars's profile, where `Polars.impl` is the profile's
(`Expr.evalOkOr_of_evalP`) and the lowering exact (`Lowering.lowerRel?_sound`).
A raise is a template's own guard (a one-sided entry's, as `dmul`'s), which
the translation checks: no guarantee rests on Polars raising (D70). -/
theorem Rel.polars_sound_or_raises {cat : Catalog} {r r' : Rel}
    (hr : Lowering.polars.lowerRel? r = .ok r') (h1 : ¬r'.Raises Profile.polars cat) :
    r'.eval cat Polars.impl = r.eval cat := by
  have hI : ∀ {e : Expr} {row : Row} {v : Value}, Functions.Ctor.bin .fmod ∉ e.ctors →
      e.evalP Profile.polars row = .ok v → e.eval row Polars.impl = v := fun he hv => by
    rw [Expr.evalI_congr (Polars.impl_agreeOn fun f hf => by
      simp only [Polars.implExceptions, List.mem_singleton] at hf; subst hf; exact he)]
    exact Expr.evalOkOr_of_evalP hv
  rw [Rel.eval_congr_ok_on (Q := fun e => Functions.Ctor.bin .fmod ∉ e.ctors) hI
    (Lowering.polars_no_fmod hr) h1]
  exact Lowering.lowerRel?_sound Lowering.polars_noneOnDbl hr h1

/-- **A verified plan runs on Polars, guards dropped** (ruling 277's first
branch, 256 A). When `Rel.mayIssues` reports nothing but assumed issues
(whose guards the translation keeps), on every catalog that satisfies the
preconditions, a plan whose expressions Polars's table lowers exactly
(`Rel.ExactOnB`, false where it multiplies decimals: `dmul`'s entry is
one-sided) gives `Rel.eval`'s rows lowered, run with Polars's functions and
without its other guards. The reference raises nowhere
(`Rel.not_raises_of_assumed`), so the lowered plan raises nowhere under
Polars's profile (`Lowering.lowerRel?_raises`), and
`Rel.polars_sound_or_raises` gives the rows. -/
theorem Rel.polars_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r r' : Rel} (hr : Lowering.polars.lowerRel? r = .ok r') (hwf : r.WF cat)
    (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true)
    (hx : r.ExactOnB Lowering.polars = true) :
    r'.eval cat Polars.impl = r.eval cat := by
  have h0 := Rel.not_raises_of_assumed hcat hA hF hT hwf hsmall hs hm
  exact Rel.polars_sound_or_raises hr fun h =>
    h0 (Lowering.lowerRel?_raises Lowering.polars_noneOnDbl (Rel.exactOn_of_exactOnB hx) hr h)

/-- Polars: the plan lowered by `Lowering.polars`, run with `Polars.impl`. -/
def Engine.polars : Engine where
  name := "polars"
  profile := Profile.polars
  table := Profile.polars.table
  obs := Profile.polars.obs
  lower r := (Lowering.polars.lowerRel? r).toOption
  impl := Polars.impl
  within := Polars.impl_within

theorem Engine.polars_lower {r r' : Rel} (h : Engine.polars.lower r = some r') :
    Lowering.polars.lowerRel? r = .ok r' := by
  simp only [Engine.polars] at h
  cases hr : Lowering.polars.lowerRel? r <;> simp_all [Except.toOption]

/-- **Polars's side condition** (ruling 277's form, `Engine.ExactOrNoRaiseSide`):
the plan is lowered exactly (no decimal multiply) and runs guard-free, or the
lowered plan, every guard kept, does not raise. -/
def Engine.PolarsSide (cat : Catalog) (r : Rel) : Prop :=
  Engine.polars.ExactOrNoRaiseSide Lowering.polars cat r

/-- **Polars's run is sound** under `Engine.PolarsSide`: `Rel.polars_sound` on
the first branch, `Rel.polars_sound_or_raises` on the second. -/
theorem Engine.polars_sound : Engine.polars.Sound Engine.PolarsSide := by
  intro cat r r' hl hb
  have hr := Engine.polars_lower hl
  show r.Allowed cat (r'.eval cat Polars.impl)
  rcases hb with ⟨hx, _, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩ | hn
  · rw [Rel.polars_sound hcat hA hF hT hr hwf hsmall hs hm hx]; exact r.eval_allowed cat
  · rw [Rel.polars_sound_or_raises hr (hn r' hl)]; exact r.eval_allowed cat

end Substrait

namespace Substrait
section Example
attribute [local instance] Engine.exampleBoxes

/-- Polars on the example of `Sound.lean`: `Engine.contract_sound`'s hypotheses
hold (`Engine.example_contract`), so the postcondition holds on the rows
Polars's functions compute. -/
theorem Engine.polars_contract_example :
    ∀ row ∈ postRows Engine.examplePost [2]
        (Engine.examplePlan.eval Engine.exampleCat Engine.polars.impl),
      ∀ v ∈ row, v = .bool true := by
  exact Engine.example_contract Engine.polars_sound (T' := Engine.examplePlan) rfl
    (.inl ⟨rfl, Engine.guardFreeSide_example⟩)

end Example

-- Every function the generated lowering writes natively reads the reference's
-- behaviour from the table at each of its options (`nativeOffReference`, ruling
-- 278's addendum), but at the pending functions and options listed. Ruling 282 (F282)
-- accepts the list: it only shrinks (the guard fails on a new entry and on a fixed
-- one), and a pending function stays on the hand-written translation path until
-- its entry is resolved. The check reads options per function (C1) and skips those
-- the observation row absorbs (C2, C3); what is left is ruling 282's C4, likely real.
#guard letI := Boxes.Ambient.none
  nativeOffIs Profile.polars.table Profile.polars.obs Lowering.polars.nativeUn Lowering.polars.nativeBin
    [-- C4: `round(x, d)` half to even.
     (.un (.froundTo 0), "rounding"),
     -- C4: zero-based characters and bytes.
     (.bin .strpos, "string_positions"), (.bin (.substr none true), "string_positions"),
     -- C4: Polars's `*` of decimals rounds to `max(s₁, s₂)` half to even.
     (.bin .dmul, "decimal_rescale"),
     -- C4: a loose row whose first behaviour is `ERROR`.
     (.bin (.bit .shl), "shift_range"), (.bin (.bit .shr), "shift_range")]
    -- C7: `+` and `-` of decimals are at `max(s₁, s₂)` on Polars and never rescale.
    [(.bin .dadd, "decimal_rescale", "polars-decimal-arith"),
     (.bin .dsub, "decimal_rescale", "polars-decimal-arith")]

end Substrait
