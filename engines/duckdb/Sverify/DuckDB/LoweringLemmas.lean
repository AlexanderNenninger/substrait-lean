import Sverify.Engines.Lowering
import Sverify.DuckDB.Functions

/-!
# Lemmas the DuckDB lowering's proofs compute with (#241)

The generated modules (`engines/duckdb/Sverify/DuckDB/LoweringOn`) use them;
`scripts/RegenLowering.lean` passes them to the generator (`using`).
-/

namespace Substrait

/-! ### `overflow` = `SILENT` or `SATURATE` (#241)

DuckDB has no function for `UnFn.fit`: its profile computes it as the
reference does, but the SQL printer has nothing to print, so every template
must avoid it (`excluding`). These lemmas let the proofs compute it. -/

variable [Boxes.Ambient]
/-- DuckDB's profile is the reference's on a function of doubles with an
argument that is not a double (`Value.double_cases`): what lets a generated
proof keep such an argument whole. -/
theorem Lowering.duck_bin_nondouble_l (s : DuckDBSettings) {f : BinFn} (hf : f.onFloats = true)
    {x : Value} (hx : x.isDouble = false) (y : Value) :
    (Profile.duckdb s).bin f x y = Profile.reference.bin f x y := by
  cases x <;> cases y <;> simp_all [Profile.duckdb, Value.isDouble]

theorem Lowering.duck_bin_nondouble_r (s : DuckDBSettings) {f : BinFn} (hf : f.onFloats = true)
    (x : Value) {y : Value} (hy : y.isDouble = false) :
    (Profile.duckdb s).bin f x y = Profile.reference.bin f x y := by
  cases x <;> cases y <;> simp_all [Profile.duckdb, Value.isDouble]

/-- The reference's function of doubles is NULL, with no issue, where an
argument is not a double. -/
theorem Lowering.ref_bin_nondouble_l {f : BinFn} (hf : f.onFloats = true) {x : Value}
    (hx : x.isDouble = false) (y : Value) : Profile.reference.bin f x y = .ok .null := by
  cases f <;> simp only [BinFn.onFloats, Bool.false_eq_true] at hf <;>
    cases x <;> simp only [Value.isDouble, Bool.true_eq_false] at hx <;> cases y <;> rfl

theorem Lowering.ref_bin_nondouble_r {f : BinFn} (hf : f.onFloats = true) (x : Value) {y : Value}
    (hy : y.isDouble = false) : Profile.reference.bin f x y = .ok .null := by
  cases f <;> simp only [BinFn.onFloats, Bool.false_eq_true] at hf <;>
    cases y <;> simp only [Value.isDouble, Bool.true_eq_false] at hy <;> cases x <;> rfl

theorem Lowering.duck_un_nondouble (s : DuckDBSettings) (f : UnFn) {x : Value}
    (hx : x.isDouble = false) : (Profile.duckdb s).un f x = Profile.reference.un f x := by
  cases x <;> simp_all [Profile.duckdb, Value.isDouble]

theorem Lowering.ref_fit (m : OverflowMode) (w : IntWidth) (x : Value) :
    Profile.reference.un (.fit m w) x = .ok (UnFn.apply (.fit m w) x) := by
  cases x <;> rfl

theorem Lowering.apply_fit_int (m : OverflowMode) (w : IntWidth) (i : Int) :
    UnFn.apply (.fit m w) (.int i) = .int (w.fit m i) := rfl
theorem Lowering.apply_fit_null (m : OverflowMode) (w : IntWidth) :
    UnFn.apply (.fit m w) .null = .null := rfl
theorem Lowering.apply_fit_bool (m : OverflowMode) (w : IntWidth) (b : Bool) :
    UnFn.apply (.fit m w) (.bool b) = .bool b := rfl
theorem Lowering.apply_fit_str (m : OverflowMode) (w : IntWidth) (s : String) :
    UnFn.apply (.fit m w) (.str s) = .str s := rfl
theorem Lowering.apply_fit_list (m : OverflowMode) (w : IntWidth) (vs : List Value) :
    UnFn.apply (.fit m w) (.list vs) = .list vs := rfl
theorem Lowering.apply_fit_struct (m : OverflowMode) (w : IntWidth) (vs : List Value) :
    UnFn.apply (.fit m w) (.struct vs) = .struct vs := rfl
theorem Lowering.apply_fit_float (m : OverflowMode) (w : IntWidth) (c : Int) :
    UnFn.apply (.fit m w) (.float c) = .float c := rfl
theorem Lowering.apply_fit_date (m : OverflowMode) (w : IntWidth) (c : Int) :
    UnFn.apply (.fit m w) (.date c) = .date c := rfl
theorem Lowering.apply_fit_ts (m : OverflowMode) (w : IntWidth) (c : Int) :
    UnFn.apply (.fit m w) (.ts c) = .ts c := rfl
theorem Lowering.apply_fit_tod (m : OverflowMode) (w : IntWidth) (c : Int) :
    UnFn.apply (.fit m w) (.tod c) = .tod c := rfl
theorem Lowering.apply_fit_dec (m : OverflowMode) (w : IntWidth) (s : Nat) (c : Int) :
    UnFn.apply (.fit m w) (.dec s c) = .dec s c := rfl

/-! ## The guards' functions in DuckDB: the reference's -/

theorem Lowering.duck_bin_ref {s : DuckDBSettings} {f : BinFn} (h : ∀ x y, duckBin s f x y = none)
    (v w : Value) : (Profile.duckdb s).bin f v w = Profile.reference.bin f v w := by
  unfold Profile.duckdb; dsimp only; split <;> (try split) <;> simp [h]

theorem Lowering.duck_un_ref {s : DuckDBSettings} {f : UnFn} (h : ∀ x, duckUn s f x = none)
    (v : Value) : (Profile.duckdb s).un f v = Profile.reference.un f v := by
  unfold Profile.duckdb; dsimp only; split <;> simp [h]

theorem Lowering.duck_lt (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .lt x y = .ok (BinFn.apply .lt x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_lt x y)
theorem Lowering.duck_eq (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .eq x y = .ok (BinFn.apply .eq x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_eq x y)
theorem Lowering.duck_and (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .and x y = .ok (and3 x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_and x y)
theorem Lowering.duck_or (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .or x y = .ok (or3 x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_or x y)
theorem Lowering.duck_dadd (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .dadd x y = .ok (BinFn.apply .dadd x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_dadd x y)
theorem Lowering.duck_dsub (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .dsub x y = .ok (BinFn.apply .dsub x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_dsub x y)
theorem Lowering.duck_dmul (s : DuckDBSettings) (x y : Value) :
    (Profile.duckdb s).bin .dmul x y = .ok (BinFn.apply .dmul x y) :=
  (Lowering.duck_bin_ref (fun _ _ => rfl) x y).trans (Lowering.ref_dmul x y)
theorem Lowering.duck_not (s : DuckDBSettings) (x : Value) :
    (Profile.duckdb s).un .not x = .ok (match x with | .bool b => .bool !b | _ => .null) :=
  (Lowering.duck_un_ref (fun _ => rfl) x).trans (Lowering.ref_not x)
theorem Lowering.duck_isNum (s : DuckDBSettings) (k : NumKind) (x : Value) :
    (Profile.duckdb s).un (.isNum k) x = .ok (.bool (x.isNum k)) :=
  (Lowering.duck_un_ref (fun _ => rfl) x).trans (Lowering.ref_isNum k x)
theorem Lowering.duck_raise (s : DuckDBSettings) (m : String) (x : Value) :
    (Profile.duckdb s).un (.raise m) x = .error .raised :=
  (Lowering.duck_un_ref (fun _ => rfl) x).trans (Lowering.ref_raise m x)

/-- `%` by a positive constant, which the wrap-arounds compute with: the
reference's, for every argument. -/
theorem Lowering.duck_imod_pos (s : DuckDBSettings) (x : Value) (m : Int) (hm : 0 < m) :
    (Profile.duckdb s).bin .imod x (.int m) = .ok (BinFn.apply .imod x (.int m)) := by
  have h0 : m ≠ 0 := by omega
  have h1 : m ≠ -1 := by omega
  cases x <;> simp [Profile.duckdb, BinFn.onFloats, duckBin, Profile.reference, raiseIf, BinFn.issue, h0, h1]

/-- `%` by `2⁶⁴`, which the wrap-around computes with. -/
theorem Lowering.duck_imod_pow64 (s : DuckDBSettings) (x : Value) :
    (Profile.duckdb s).bin .imod x (.int (2 ^ 64)) = .ok (BinFn.apply .imod x (.int (2 ^ 64))) := by
  have h0 : ¬((2 : Int) ^ 64 = 0) := by decide
  have h1 : ¬((2 : Int) ^ 64 = -1) := by decide
  cases x
  case int a =>
    simp only [Profile.duckdb, BinFn.onFloats, duckBin, h0, h1, false_and, ite_false, Bool.false_eq_true,
      Option.getD_none, Profile.reference, raiseIf, BinFn.issue]
  case tod a =>
    simp only [Profile.duckdb, Profile.reference, raiseIf, BinFn.issue, h0, ite_false]
  all_goals rfl

/-! ### `<<` (#241) -/

/-- `CASE WHEN #1 = k THEN 2ᵏ …` over `ks`, else NULL: `2ʸ` for a shift `y`, which
`<<`'s template multiplies by (`LoweringSearch.duckdbSchemas`). One lemma, by induction,
rather than a case per shift in every proof. -/
@[irreducible] def Lowering.pow2Chain (ks : List Nat) : Expr :=
  ks.foldr (fun (k : Nat) (e : Expr) =>
    .ifThen (.bin .eq (.field 1) (.lit (.int (k : Int)))) (.lit (.int ((2 : Int) ^ k))) e) (.lit .null)

theorem Lowering.pow2Chain_eval (s : DuckDBSettings) (x y : Value) (ks : List Nat) :
    (Lowering.pow2Chain ks).evalP (Profile.duckdb s) [x, y] =
      .ok (match y with
        | .int b => if 0 ≤ b ∧ b.toNat ∈ ks then .int (2 ^ b.toNat) else .null
        | _ => .null) := by
  induction ks with
  | nil => cases y <;> simp [Lowering.pow2Chain, Expr.evalP]
  | cons k ks ih =>
    simp only [Lowering.pow2Chain, List.foldr_cons] at ih ⊢
    simp only [Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
      Lowering.duck_eq, ih]
    cases y with
    | int b =>
      by_cases h : b = (k : Int)
      · subst h
        simp [BinFn.apply, Value.isTrue]
      · by_cases h0 : 0 ≤ b
        · have hk : b.toNat ≠ k := by omega
          simp [BinFn.apply, h, h0, hk, Value.isTrue]
        · simp [BinFn.apply, h, h0, Value.isTrue]
    | _ => rfl

/-- `<<` for DuckDB: a shift outside `0`–`63` raises; otherwise `x · 2ʸ`
(`Lowering.pow2Chain`) wrapped around at 64 bits in 128-bit arithmetic, as
`overflow` = `SILENT` does. -/
def Lowering.shlTemplate : Expr :=
  let h : Int := 2 ^ 63
  let m : Int := 2 ^ 64
  let wrap (x : Expr) : Expr :=
    .bin .dsub (.bin .imod (.bin .dadd (.bin .imod (.bin .dadd x (.lit (.int h))) (.lit (.int m)))
      (.lit (.int m))) (.lit (.int m))) (.lit (.int h))
  .ifThen (.bin .and (.un (.isNum .int) (.field 0))
      (.bin .or (.bin .lt (.field 1) (.lit (.int 0))) (.un .not (.bin .lt (.field 1) (.lit (.int 64))))))
    (.un (.raise "domain error") (.field 1))
    -- `dmul` reads decimals too: an integer only (#923).
    (.ifThen (.un (.isNum .int) (.field 0))
      (wrap (.bin .dmul (.field 0) (Lowering.pow2Chain (List.range 64)))) (.lit .null))

omit [Boxes.Ambient] in
/-- The template reads both arguments, for the entry's strictness. -/
theorem Lowering.shlTemplate_must : 0 ∈ Lowering.shlTemplate.must ∧ 1 ∈ Lowering.shlTemplate.must := by
  simp [Expr.must, Lowering.shlTemplate]

/-- `CAST(x AS VARCHAR)` of a `DECIMAL(p, p)` on DuckDB (D72, ruling 245 E2): DuckDB's own cast
prints it without the integer part (`.500`), so its only lowering is the text of the decimal
widened by one digit of precision, which has an integer part (`0.500`). -/
def Lowering.dtextFullTemplate : Expr := .un .dtext (.un .dwiden (.field 0))

omit [Boxes.Ambient] in
/-- The template reads its argument, for the entry's strictness. -/
theorem Lowering.dtextFullTemplate_must : 0 ∈ Lowering.dtextFullTemplate.must := by
  simp [Expr.must, Lowering.dtextFullTemplate]

/-- `dtextFullTemplate` agrees with the reference on every value: widening keeps the value, and
DuckDB's `dtext` is the reference's. -/
theorem Lowering.dtextFull_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.dtextFullTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .dtextFull x) := by
  cases x <;> rfl

/-- `round` on DuckDB, through `zeroTemplate`, agrees with the reference. -/
theorem Lowering.fround_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.froundTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .fround x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (Lowering.duck_lt s) (Lowering.duck_eq s) (Lowering.duck_and s)
      (fun _ => rfl) (fun _ => rfl) FloatCode.round_negZero
      FloatCode.round_negNan (fun _ h => FloatCode.canon_round h) c
  all_goals rfl

/-- `round_even` on DuckDB, through `zeroTemplate`, agrees with the reference. -/
theorem Lowering.froundEven_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.froundEvenTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .froundEven x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (Lowering.duck_lt s) (Lowering.duck_eq s) (Lowering.duck_and s)
      (fun _ => rfl) (fun _ => rfl) FloatCode.roundEven_negZero
      FloatCode.roundEven_negNan (fun _ h => FloatCode.canon_roundEven h) c
  all_goals rfl

/-- `ceil` on DuckDB, through `zeroTemplate`, agrees with the reference. -/
theorem Lowering.fceil_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.fceilTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .fceil x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (Lowering.duck_lt s) (Lowering.duck_eq s) (Lowering.duck_and s)
      (fun _ => rfl) (fun _ => rfl) FloatCode.ceil_negZero
      FloatCode.ceil_negNan (fun _ h => FloatCode.canon_ceil h) c
  all_goals rfl

/-- `power` on DuckDB: raise where the reference does (`negInfPow`, and a
negative finite base to a finite power that is not an integer, `nanCase`). -/
def Lowering.fpowTemplate : Expr :=
  let x := Expr.field 0; let y := Expr.field 1
  let ninf := Expr.lit (.float FloatCode.negInf); let pinf := Expr.lit (.float FloatCode.posInf)
  let yFrac := Expr.bin .and (.bin .and (.bin .lt ninf y) (.bin .lt y pinf))
    (.un .not (.bin .eq (.un .ffloor y) y))
  .ifThen (.bin .or (.bin .and (.bin .and (.bin .lt ninf x) (.bin .lt x (.lit (.float 0)))) yFrac)
      (.bin .and (.bin .eq x ninf) yFrac))
    (.un (.raise "domain error") y) (.bin .fpow x y)

omit [Boxes.Ambient] in
/-- The template reads both arguments, for the entry's strictness. -/
theorem Lowering.fpowTemplate_must : 0 ∈ Lowering.fpowTemplate.must ∧ 1 ∈ Lowering.fpowTemplate.must := by
  simp [Expr.must, Lowering.fpowTemplate]

/-- `fpowTemplate` agrees with the reference on two doubles, every code:
its guard, read through `canon`, is the reference's raise condition. -/
theorem Lowering.fpow_float (e' : Bool) (a b : Int) :
    (Lowering.fpowTemplate.evalP (Profile.duckdb ⟨e', true⟩) [.float a, .float b]).Agree
      (Profile.reference.bin .fpow (.float a) (.float b)) := by
  have hlt : ∀ a b : Int, BinFn.apply .lt (.float a) (.float b) =
      .bool (decide (FloatCode.canon a < FloatCode.canon b)) := fun _ _ => rfl
  have heq : ∀ a b : Int, BinFn.apply .eq (.float a) (.float b) =
      .bool (FloatCode.canon a == FloatCode.canon b) := fun _ _ => rfl
  have hfl : ∀ b, (Profile.duckdb ⟨e', true⟩).un .ffloor (.float b) =
      .ok (.float (FloatCode.floor b)) := fun _ => rfl
  have hduck : (Profile.duckdb ⟨e', true⟩).bin .fpow (.float a) (.float b) =
      (if negInfPow a b then some (Except.ok (.float (duckNegInfPow b)))
        else if nanCase .fpow a b then some (Except.ok (.float FloatCode.nan)) else none).getD
        (Profile.reference.bin .fpow (.float a) (.float b)) := rfl
  have href : Profile.reference.bin .fpow (.float a) (.float b) =
      if negInfPow a b || nanCase .fpow a b then .error .domain
      else .ok (.float (FloatCode.lift₂ Float.pow a b)) := by
    have hap : BinFn.apply .fpow (.float a) (.float b) = .float (FloatCode.lift₂ Float.pow a b) := rfl
    by_cases h1 : negInfPow a b <;> by_cases h2 : nanCase .fpow a b <;>
      simp [Profile.reference, raiseIf, BinFn.issue, nanIssue, hap, h1, h2, Issue.isError]
  -- The guard is true exactly where the reference raises, on every code.
  have hguard : ∀ G : Bool, G = (negInfPow a b || nanCase .fpow a b) →
      (Expr.ifThen (.lit (.bool G)) (.un (.raise "domain error") (.field 1))
        (.bin .fpow (.field 0) (.field 1)) |>.evalP (Profile.duckdb ⟨e', true⟩)
          [.float a, .float b]).Agree (Profile.reference.bin .fpow (.float a) (.float b)) := by
    intro G hG; subst hG
    rw [href]
    by_cases h1 : negInfPow a b <;> by_cases h2 : nanCase .fpow a b <;>
      simp [Expr.evalP, Outcome.ok_bind, Value.isTrue, h1, h2, hduck, href, Lowering.duck_raise, Outcome.Agree]
  -- The guard's value, from the canonical codes, is the reference's raise
  -- condition on the raw ones.
  have hb : ∀ p q : Int, (p == q) = decide (p = q) := fun _ _ => rfl
  have hP := FloatCode.posInf_eq; have hN := FloatCode.negInf_eq
  have hZ := FloatCode.negZero_eq'; have hY := FloatCode.negNan_eq'
  have hQ : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  have hcP := FloatCode.canon_posInf; have hcN := FloatCode.canon_negInf
  have hc0 := FloatCode.canon_zero
  have ha3 : ∀ p q : Bool, and3 (.bool p) (.bool q) = .bool (p && q) := by decide
  have ho3 : ∀ p q : Bool, or3 (.bool p) (.bool q) = .bool (p || q) := by decide
  have hn3 : ∀ p : Bool, (match Value.bool p with | .bool b => Value.bool !b | _ => .null) =
      .bool !p := fun _ => rfl
  have key : ((decide (FloatCode.canon FloatCode.negInf < FloatCode.canon a) &&
        decide (FloatCode.canon a < FloatCode.canon 0) &&
        (decide (FloatCode.canon FloatCode.negInf < FloatCode.canon b) &&
          decide (FloatCode.canon b < FloatCode.canon FloatCode.posInf) &&
          !decide (FloatCode.canon (FloatCode.floor b) = FloatCode.canon b))) ||
      (decide (FloatCode.canon a = FloatCode.canon FloatCode.negInf) &&
        (decide (FloatCode.canon FloatCode.negInf < FloatCode.canon b) &&
          decide (FloatCode.canon b < FloatCode.canon FloatCode.posInf) &&
          !decide (FloatCode.canon (FloatCode.floor b) = FloatCode.canon b)))) =
      (negInfPow a b || nanCase .fpow a b) := by
    simp only [negInfPow, nanCase, hcN, hcP, hc0]
    rw [Bool.eq_iff_iff]
    rcases FloatCode.canon_cases b with ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ | hb'
    · simp only [hb', FloatCode.floor_negZero]
      rcases FloatCode.canon_cases a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;> simp only [ha] <;>
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq, not_true_eq_false,
          and_false, or_false] <;> omega
    · simp only [hb', FloatCode.floor_negNan]
      rcases FloatCode.canon_cases a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;> simp only [ha] <;>
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq, not_true_eq_false,
          and_false, or_false] <;> omega
    · have hf := FloatCode.canon_floor hb'
      simp only [hb', hf]
      rcases FloatCode.canon_cases a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;> simp only [ha] <;>
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq] <;> omega
  have hG : (Expr.bin .or (.bin .and (.bin .and (.bin .lt (.lit (.float FloatCode.negInf)) (.field 0))
        (.bin .lt (.field 0) (.lit (.float 0))))
        (.bin .and (.bin .and (.bin .lt (.lit (.float FloatCode.negInf)) (.field 1))
          (.bin .lt (.field 1) (.lit (.float FloatCode.posInf))))
          (.un .not (.bin .eq (.un .ffloor (.field 1)) (.field 1)))))
      (.bin .and (.bin .eq (.field 0) (.lit (.float FloatCode.negInf)))
        (.bin .and (.bin .and (.bin .lt (.lit (.float FloatCode.negInf)) (.field 1))
          (.bin .lt (.field 1) (.lit (.float FloatCode.posInf))))
          (.un .not (.bin .eq (.un .ffloor (.field 1)) (.field 1)))))).evalP
        (Profile.duckdb ⟨e', true⟩) [.float a, .float b] =
      .ok (.bool (negInfPow a b || nanCase .fpow a b)) := by
    simp only [Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
      Lowering.duck_lt, Lowering.duck_eq, Lowering.duck_and, Lowering.duck_or, Lowering.duck_not,
      hlt, heq, hfl, hb, ha3, ho3]
    rw [key]
  have hif : ∀ c c' t e : Expr, c.evalP (Profile.duckdb ⟨e', true⟩) [.float a, .float b] =
      c'.evalP (Profile.duckdb ⟨e', true⟩) [.float a, .float b] →
      (Expr.ifThen c t e).evalP (Profile.duckdb ⟨e', true⟩) [.float a, .float b] =
        (Expr.ifThen c' t e).evalP (Profile.duckdb ⟨e', true⟩) [.float a, .float b] := by
    intro c c' t e h; unfold Expr.evalP; rw [h]
  unfold Lowering.fpowTemplate; dsimp only
  rw [hif _ (.lit (.bool (negInfPow a b || nanCase .fpow a b)))
    _ _ (by rw [hG]; rfl)]
  exact hguard _ rfl

omit [Boxes.Ambient] in
theorem Lowering.and3_eq_true {a b : Value} : and3 a b = .bool true ↔ a = .bool true ∧ b = .bool true := by
  unfold and3; split <;> simp_all

omit [Boxes.Ambient] in
theorem Lowering.or3_eq_true {a b : Value} : or3 a b = .bool true ↔ a = .bool true ∨ b = .bool true := by
  unfold or3; split <;> simp_all

omit [Boxes.Ambient] in
theorem Lowering.isTrue_eq_true {v : Value} : v.isTrue = true ↔ v = .bool true := by
  unfold Value.isTrue; split <;> simp_all

/-- Where an argument is not a double, `fpowTemplate`'s guard is not true and
both sides are NULL. -/
theorem Lowering.fpow_nondouble (e : Bool) {x y : Value}
    (h : x.isDouble = false ∨ y.isDouble = false) :
    (Lowering.fpowTemplate.evalP (Profile.duckdb ⟨e, true⟩) [x, y]).Agree
      (Profile.reference.bin .fpow x y) := by
  have hf : BinFn.onFloats .fpow = true := rfl
  obtain ⟨w, hw⟩ : ∃ w, (Profile.duckdb ⟨e, true⟩).un .ffloor y = .ok w := by
    cases y <;> exact ⟨_, rfl⟩
  have hr : Profile.reference.bin .fpow x y = .ok .null := by
    rcases h with h | h
    · exact Lowering.ref_bin_nondouble_l hf h y
    · exact Lowering.ref_bin_nondouble_r hf x h
  have hd : (Profile.duckdb ⟨e, true⟩).bin .fpow x y = .ok .null := by
    rw [← hr]; rcases h with h | h
    · exact Lowering.duck_bin_nondouble_l _ hf h y
    · exact Lowering.duck_bin_nondouble_r _ hf x h
  simp only [Lowering.fpowTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, Lowering.duck_lt, Lowering.duck_eq, Lowering.duck_and, Lowering.duck_or,
    Lowering.duck_not, hw, hd, hr]
  rcases h with h | h
  · simp [Lowering.isTrue_eq_true, Lowering.or3_eq_true, Lowering.and3_eq_true, BinFn.apply_lt_nondouble_l h,
      BinFn.apply_lt_nondouble_r h, BinFn.apply_eq_nondouble_l h, Outcome.Agree]
  · simp [Lowering.isTrue_eq_true, Lowering.or3_eq_true, Lowering.and3_eq_true, BinFn.apply_lt_nondouble_l h,
      BinFn.apply_lt_nondouble_r h, Outcome.Agree]

theorem Lowering.fpow_agree (e : Bool) (x y : Value) :
    (Lowering.fpowTemplate.evalP (Profile.duckdb ⟨e, true⟩) [x, y]).Agree
      (Profile.reference.bin .fpow x y) := by
  cases x
  case float a =>
    cases y
    case float b => exact Lowering.fpow_float e a b
    all_goals exact Lowering.fpow_nondouble e (.inr rfl)
  all_goals exact Lowering.fpow_nondouble e (.inl rfl)
theorem Lowering.bit_shl_agree (s : DuckDBSettings) (x y : Value) :
    (Lowering.shlTemplate.evalP (Profile.duckdb s) [x, y]).Agree
      (Profile.reference.bin (.bit .shl) x y) := by
  simp only [Lowering.shlTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Lowering.pow2Chain_eval, Outcome.ok_bind, Lowering.duck_lt, Lowering.duck_and, Lowering.duck_or,
    Lowering.duck_not, Lowering.duck_isNum, Lowering.duck_raise, Lowering.duck_dmul,
    Lowering.duck_dadd, Lowering.duck_dsub, Lowering.duck_imod_pow64]
  cases x
  case int a =>
    cases y
    case int b =>
      simp only [Profile.reference, BinFn.issue, BinFn.apply, Value.isNum, Lowering.shl_apply,
        domainIssue]
      by_cases h0 : b < 0
      · simp [h0, raiseIf, Value.isTrue, and3, or3, Outcome.Agree, Issue.isError]
      · by_cases h1 : b < 64
        · have hb : 0 ≤ b := by omega
          simp [h0, h1, hb, raiseIf, Value.isTrue, and3, or3, Outcome.Agree, Lowering.tmod_add_tmod]
        · simp [h0, h1, raiseIf, Value.isTrue, and3, or3, Outcome.Agree, Issue.isError]
    all_goals rfl
  all_goals (cases y <;> rfl)

/-- `<<`'s guard fires only on a shift outside `0`–`63` of an integer, where
the reference reports a domain error (`Lowering.GuardsFor`). -/
theorem Lowering.bit_shl_guards (s : DuckDBSettings) (x y : Value) :
    Lowering.shlTemplate.GuardsAt (Profile.duckdb s) (fun _ => false) ((BinFn.bit .shl).issue x y)
      [x, y] := by
  simp only [Lowering.shlTemplate, Expr.GuardsAt, Expr.raiseMsg?]
  refine ⟨fun _ => ?_, fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩⟩
  simp only [Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind, Lowering.duck_lt,
    Lowering.duck_and, Lowering.duck_or, Lowering.duck_not, Lowering.duck_isNum, Outcome.FiresOnly]
  cases x <;> cases y <;> simp [Value.isNum, BinFn.apply, and3, or3, Value.isTrue, BinFn.issue,
    domainIssue, Lowering.shl_apply, Issue.name]
  rename_i a b
  by_cases h0 : b < 0 <;> by_cases h1 : b < 64 <;> simp [h0, h1] <;>
    first | omega | exact ⟨.domain, ⟨fun _ => by omega, rfl⟩, rfl⟩

end Substrait

namespace Substrait

variable [Boxes.Ambient]

set_option exponentiation.threshold 2100

/-! ## A cast of a double to an integer truncates first (ruling 284 D2)

DuckDB's `CAST(x AS BIGINT)` rounds half to even (duckdb-R9). Of the value
truncated first, `CEIL` below zero and `FLOOR` elsewhere, it is the reference's
truncating cast: the truncated magnitude is integral, which half to even keeps
(`FloatCode.toInt?_roundEven_floor`, `toInt?_roundEven_ceil`). -/

/-- `f (CASE WHEN x < 0 THEN ceil(x) ELSE floor(x) END)`. -/
def Lowering.ftoiTruncT (f : UnFn) : Expr :=
  .un f (.ifThen (.bin .lt (.field 0) (.lit (.float 0))) (.un .fceil (.field 0)) (.un .ffloor (.field 0)))

omit [Boxes.Ambient] in
theorem Lowering.ftoiTruncT_must (f : UnFn) : 0 ∈ (Lowering.ftoiTruncT f).must := by
  simp [Expr.must, Lowering.ftoiTruncT]

/-- The templates as constants, for the generator (`LoweringSearch.duckdbSchemas`),
which finds a template's strictness by its name (`_must`). -/
def Lowering.ftoiTemplate : Expr := Lowering.ftoiTruncT .ftoi
def Lowering.ftoiOrNullTemplate : Expr := Lowering.ftoiTruncT .ftoiOrNull

omit [Boxes.Ambient] in
theorem Lowering.ftoiTemplate_must : 0 ∈ Lowering.ftoiTemplate.must := Lowering.ftoiTruncT_must _
omit [Boxes.Ambient] in
theorem Lowering.ftoiOrNullTemplate_must : 0 ∈ Lowering.ftoiOrNullTemplate.must :=
  Lowering.ftoiTruncT_must _

omit [Boxes.Ambient] in
theorem DuckDBSQL.castOut_congr {a b : Int}
    (h : FloatCode.toInt? (FloatCode.canon a) = FloatCode.toInt? (FloatCode.canon b)) :
    DuckDBSQL.castOut a = DuckDBSQL.castOut b := by
  unfold DuckDBSQL.castOut; rw [h]

omit [Boxes.Ambient] in
theorem DuckDBSQL.castOrNull_congr {a b : Int}
    (h : FloatCode.toInt? (FloatCode.canon a) = FloatCode.toInt? (FloatCode.canon b)) :
    DuckDBSQL.castOrNull a = DuckDBSQL.castOrNull b := by
  unfold DuckDBSQL.castOrNull; rw [h]

theorem DuckDBSQL.ref_ftoiOrNull_float (c : Int) :
    Profile.reference.un .ftoiOrNull (.float c) = .ok (DuckDBSQL.castOrNull c) := by
  simp only [Profile.reference, raiseIf, UnFn.issue, UnFn.apply, DuckDBSQL.castOrNull]
  cases FloatCode.toInt? (FloatCode.canon c) <;> rfl

theorem DuckDBSQL.ref_ftoi_castOut (c : Int) :
    Profile.reference.un .ftoi (.float c) = DuckDBSQL.castOut c := by
  simp only [Profile.reference, raiseIf, UnFn.issue, UnFn.apply, DuckDBSQL.castOut]
  cases FloatCode.toInt? (FloatCode.canon c) with
  | none => rfl
  | some x => by_cases h : inI64 x = true <;> simp [h, Issue.isError]

/-- The truncated value's half-even cast is the value's truncating one: the
code-level lemma for `ftoiTruncT`'s two branches, as DuckDB computes them
(its `CEIL` of a negative value that rounds to zero is `-0.0`). -/
theorem Lowering.duck_fceil_float (s : DuckDBSettings) (c : Int) :
    (Profile.duckdb s).un .fceil (.float c) =
      if c < 0 ∧ FloatCode.ceil c = 0 then .ok (.float FloatCode.negZero)
      else .ok (.float (FloatCode.ceil c)) := by
  simp only [Profile.duckdb, duckUn]; split <;> rfl

theorem Lowering.duck_ffloor_float (s : DuckDBSettings) (c : Int) :
    (Profile.duckdb s).un .ffloor (.float c) = .ok (.float (FloatCode.floor c)) := rfl

theorem Lowering.ftoiTrunc_code (s : DuckDBSettings) (c : Int) :
    ∃ d, ((Expr.ifThen (.bin .lt (.field 0) (.lit (.float 0))) (.un .fceil (.field 0))
        (.un .ffloor (.field 0))).evalP (Profile.duckdb s) [.float c]) = .ok (.float d) ∧
      FloatCode.toInt? (FloatCode.canon (FloatCode.roundEven d)) =
        FloatCode.toInt? (FloatCode.canon c) := by
  have hlt := Lowering.duck_lt s (.float c) (.float 0)
  simp only [BinFn.apply, FloatCode.canon_zero] at hlt
  simp only [Expr.evalP, bind, Except.bind, List.getD_cons_zero]
  rw [hlt]
  by_cases h0 : FloatCode.canon c < 0
  · obtain ⟨hc, -⟩ := FloatCode.lt_zero_of_canon_lt_zero h0
    simp only [h0, decide_true, Value.isTrue, ite_true, Lowering.duck_fceil_float]
    by_cases hz : FloatCode.ceil c = 0
    · refine ⟨FloatCode.negZero, by simp only [hc, hz, and_self, ite_true], ?_⟩
      rw [FloatCode.toInt?_canon_roundEven_negZero, ← FloatCode.toInt?_roundEven_ceil c h0, hz]
      rfl
    · exact ⟨FloatCode.ceil c, by simp only [hz, and_false, ite_false], FloatCode.toInt?_roundEven_ceil c h0⟩
  · simp only [h0, decide_false, Value.isTrue, Bool.false_eq_true, ite_false,
      Lowering.duck_ffloor_float]
    exact ⟨FloatCode.floor c, rfl, FloatCode.toInt?_roundEven_floor c h0⟩

/-- **`CAST(x AS BIGINT)` on DuckDB, truncated first, is the reference's.** -/
theorem Lowering.ftoi_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.ftoiTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .ftoi x) := by
  cases x
  case float c =>
    obtain ⟨d, hd, hcast⟩ := Lowering.ftoiTrunc_code s c
    simp only [Lowering.ftoiTemplate, Lowering.ftoiTruncT, Expr.evalP, bind, Except.bind] at hd ⊢
    rw [hd]
    simp only [Profile.duckdb, duckUn, Option.getD_some, DuckDBSQL.ref_ftoi_castOut,
      DuckDBSQL.castOut_congr hcast]
    exact Outcome.agree_refl _
  all_goals rfl

/-- **`TRY_CAST(x AS BIGINT)` on DuckDB, truncated first, is the reference's.** -/
theorem Lowering.ftoiOrNull_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.ftoiOrNullTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .ftoiOrNull x) := by
  cases x
  case float c =>
    obtain ⟨d, hd, hcast⟩ := Lowering.ftoiTrunc_code s c
    simp only [Lowering.ftoiOrNullTemplate, Lowering.ftoiTruncT, Expr.evalP, bind, Except.bind]
      at hd ⊢
    rw [hd]
    simp only [Profile.duckdb, duckUn, Option.getD_some, DuckDBSQL.ref_ftoiOrNull_float,
      DuckDBSQL.castOrNull_congr hcast]
    exact Outcome.agree_refl _
  all_goals rfl

end Substrait
