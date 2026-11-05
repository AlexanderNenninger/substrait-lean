import SubstraitLean.Lowering
import SubstraitLean.PolarsShims
import SubstraitLean.Parse

/-!
# Polars as a profile (#444)

`Profile.polars` is the semantics a plan verified with
`verify(semantics="polars")` is checked under: what Polars 2.1.0's streaming
engine computes, as its facts record it (`characterization/polars/facts/`),
on the options where sverify models Polars's own choice, and the reference
elsewhere. Per option (D21, `docs/core-semantics.md`, "Polars as a profile"):

* `division_type`: `FLOOR`, Polars's own. Integer `//` floors and `%` takes
  the divisor's sign (polars-int-divide, polars-int-modulus).
* `±∞`: a double that overflows is `±∞`, as in the reference (#575), with no
  precondition (polars-double-arith), as under DuckDB's profile.
* The error side stays the reference's: an integer that overflows, a zero
  divisor and NaN creation raise, where Polars wraps, gives NULL or NaN. A
  verified plan never reaches them, so Polars's own values there need no
  shim, and the profile is tighter than the engine (D21).
* Every other option is the reference's: there, the translation to Polars
  keeps its written arguments and shims (`PolarsShims.lean`).

A plan states the choice it makes: integer `divide` and `modulus` with
`division_type: FLOOR`, which the parser reads as `Expr.floorDivOf` and
`Expr.floorModOf`, templates in the reference's truncating operations that
never overflow on 64-bit operands. `Write` writes them back as the calls, so
Polars runs its own `//` and `%` (the route `native`), and DuckDB, which has
no `FLOOR`, refuses them.

What is proved here:

* `Profile.polars`, an evaluable `Profile`: its `//` and `%` are the
  templates under the reference, and on 64-bit integers they are Polars's
  (`Polars.floorDiv`, `Polars.floorMod`, the trusted model of
  `PolarsShims.lean`): `Profile.polars_idiv`, `Profile.polars_imod`. A zero
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

end Polars

/-- The functions where Polars's profile differs from the reference: its
template, in the reference's operations. -/
def BinFn.polarsTmpl : BinFn → Option Expr
  | .idiv => some Polars.floorDivT
  | .imod => some Polars.floorModT
  | _ => none

/-- **Polars's profile**: integer `//` and `%` floor (`division_type` =
`FLOOR`), every other function is the reference's. -/
def Profile.polars : Profile where
  un := Profile.reference.un
  bin f x y := match f.polarsTmpl with
    | some t => t.evalP Profile.reference [x, y]
    | none => Profile.reference.bin f x y

namespace Polars

/-! ## The templates are Polars's `//` and `%` on 64-bit integers -/

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

theorem fdiv_fmod_pos_neg {a b : Int} (ha : 0 < a) (hb : b < 0) :
    a.fdiv b = (a - 1).tdiv b + -1 ∧ a.fmod b = (a - 1).tmod b + (b + 1) := by
  have h := fdiv_fmod_neg_pos (a := -a) (b := -b) (by omega) (by omega)
  have e : -a + 1 = -(a - 1) := by omega
  rw [Int.neg_fdiv_neg, Int.neg_fmod_neg, e, Int.neg_tdiv, Int.tdiv_neg, Int.neg_tmod,
    Int.tmod_neg] at h
  omega

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

theorem inI64_iff (x : Int) : inI64 x = true ↔ -2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1 := by
  unfold inI64 between
  rw [Bool.and_eq_true]
  exact ⟨fun ⟨h1, h2⟩ => ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩,
    fun ⟨h1, h2⟩ => ⟨decide_eq_true h1, decide_eq_true h2⟩⟩

theorem ref_add_int (x y : Int) (h1 : -2 ^ 63 ≤ x + y) (h2 : x + y ≤ 2 ^ 63 - 1) :
    Profile.reference.bin .add (.int x) (.int y) = .ok (.int (x + y)) := by
  have h : inI64 (x + y) = true := (inI64_iff _).mpr ⟨h1, h2⟩
  simp [Profile.reference, raiseIf, BinFn.issue, wrapIf, h, BinFn.apply]

theorem ref_sub_int (x y : Int) (h1 : -2 ^ 63 ≤ x - y) (h2 : x - y ≤ 2 ^ 63 - 1) :
    Profile.reference.bin .sub (.int x) (.int y) = .ok (.int (x - y)) := by
  have h : inI64 (x - y) = true := (inI64_iff _).mpr ⟨h1, h2⟩
  simp [Profile.reference, raiseIf, BinFn.issue, wrapIf, h, BinFn.apply]

theorem ref_idiv_int (x y : Int) (h0 : y ≠ 0) (h : inI64 (x.tdiv y) = true) :
    Profile.reference.bin .idiv (.int x) (.int y) = .ok (.int (x.tdiv y)) := by
  simp [Profile.reference, raiseIf, BinFn.issue, h0, h, BinFn.apply]

theorem ref_lt_int (x y : Int) :
    Profile.reference.bin .lt (.int x) (.int y) = .ok (.bool (decide (x < y))) := by
  rw [Lowering.ref_lt]; rfl

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

/-! ## Evaluating under `Profile.polars` is evaluating the elaboration -/

namespace Polars

/-- A plan read with Polars's `//` and `%`, written in the reference's
operations: each integer `//` and `%` replaced by its template. -/
def elaborate : Expr → Expr
  | .lit v => .lit v
  | .field i => .field i
  | .un f a => .un f (elaborate a)
  | .bin f a b => match f.polarsTmpl with
    | some t => t.subst [elaborate a, elaborate b]
    | none => .bin f (elaborate a) (elaborate b)
  | .ifThen c t e => .ifThen (elaborate c) (elaborate t) (elaborate e)
  | .hof f l b => .hof f (elaborate l) (elaborate b)

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
      simp [floorDivT, floorModT, Expr.floorDivOf, Expr.floorModOf, Expr.subst, Expr.evalP, ha,
        bind, Except.bind]
  | ok x =>
    cases hb : b.evalP Profile.reference row with
    | error k =>
      cases f <;> simp only [BinFn.polarsTmpl, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
        simp [floorDivT, floorModT, Expr.floorDivOf, Expr.floorModOf, Expr.subst, Expr.evalP, ha, hb,
          bind, Except.bind, Lowering.ref_lt]
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
  | .un f a, row => by simp only [elaborate, Expr.evalP, elaborate_eq a row]; rfl
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
    have : (fun x => (elaborate b).evalP Profile.reference [x]) = fun x => b.evalP Profile.polars [x] :=
      funext fun x => elaborate_eq b [x]
    rw [this]

/-- The parser reads a call that states `division_type: FLOOR` as the
template of Polars's `//` or `%`: the elaboration of the native call. -/
theorem elaborate_floor (a b : Expr) :
    elaborate (.bin .idiv a b) = Expr.floorDivOf (elaborate a) (elaborate b) ∧
    elaborate (.bin .imod a b) = Expr.floorModOf (elaborate a) (elaborate b) := ⟨rfl, rfl⟩

end Polars

end Substrait
