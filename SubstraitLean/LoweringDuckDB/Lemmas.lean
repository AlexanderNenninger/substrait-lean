import SubstraitLean.Lowering
import SubstraitLean.DuckDBProfile

/-!
# Lemmas the DuckDB lowering's proofs compute with (#241)

The generated modules (`SubstraitLean/LoweringDuckDB/On`) use them;
`scripts/RegenLowering.lean` passes them to the generator (`using`).
-/

namespace Substrait

/-! ### `overflow` = `SILENT` or `SATURATE` (#241)

DuckDB has no function for `UnFn.fit`: its profile computes it as the
reference does, but the SQL printer has nothing to print, so every template
must avoid it (`excluding`). These lemmas let the proofs compute it. -/

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

/-- The template reads both arguments, for the entry's strictness. -/
theorem Lowering.shlTemplate_must : 0 ∈ Lowering.shlTemplate.must ∧ 1 ∈ Lowering.shlTemplate.must := by
  simp [Expr.must, Lowering.shlTemplate]

/-- `CASE WHEN x < 0 AND f(x) = 0 THEN 0.0 ELSE f(x) END`: `round` or `ceil`
on DuckDB, which gives IEEE's `-0.0` for a negative value that rounds to zero
where the reference gives `0.0` (`round_zero_sign`). -/
def Lowering.zeroTemplate (f : UnFn) : Expr :=
  .ifThen (.bin .and (.bin .lt (.field 0) (.lit (.float 0)))
      (.bin .eq (.un f (.field 0)) (.lit (.float 0))))
    (.lit (.float 0)) (.un f (.field 0))

def Lowering.froundTemplate : Expr := Lowering.zeroTemplate .fround
def Lowering.fceilTemplate : Expr := Lowering.zeroTemplate .fceil

/-- The templates read their argument, for the entries' strictness. -/
theorem Lowering.froundTemplate_must : 0 ∈ Lowering.froundTemplate.must := by
  simp [Expr.must, Lowering.froundTemplate, Lowering.zeroTemplate]

theorem Lowering.fceilTemplate_must : 0 ∈ Lowering.fceilTemplate.must := by
  simp [Expr.must, Lowering.fceilTemplate, Lowering.zeroTemplate]

/-- `zeroTemplate f` agrees with the reference on a double, for `f` a rounding
`g` of the codes that DuckDB gives as `-0.0` below zero: `-0.0` and the
negative NaN stay, and a canonical code rounds to a canonical one. -/
theorem Lowering.zeroTemplate_float {s : DuckDBSettings} {f : UnFn} {g : Int → Int}
    (hun : ∀ c, (Profile.duckdb s).un f (.float c) =
      (if c < 0 ∧ g c = 0 then some (Except.ok (.float FloatCode.negZero)) else none).getD
        (.ok (.float (g c))))
    (href : ∀ c, Profile.reference.un f (.float c) = .ok (.float (g c)))
    (hz : g FloatCode.negZero = FloatCode.negZero) (hn : g FloatCode.negNan = FloatCode.negNan)
    (hcan : ∀ c, FloatCode.canon c = c → FloatCode.canon (g c) = g c) (c : Int) :
    ((Lowering.zeroTemplate f).evalP (Profile.duckdb s) [.float c]).Agree
      (Profile.reference.un f (.float c)) := by
  have hlt : ∀ a b : Int, BinFn.apply .lt (.float a) (.float b) =
      .bool (decide (FloatCode.canon a < FloatCode.canon b)) := fun _ _ => rfl
  have heq : ∀ a b : Int, BinFn.apply .eq (.float a) (.float b) =
      .bool (FloatCode.canon a == FloatCode.canon b) := fun _ _ => rfl
  have hZ := FloatCode.negZero_eq'; have hY := FloatCode.negNan_eq'
  have hq : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  simp only [Lowering.zeroTemplate, Expr.evalP, List.getD_cons_zero, Outcome.ok_bind,
    Lowering.duck_lt, Lowering.duck_eq, Lowering.duck_and, hun, href, hlt, heq]
  rcases FloatCode.canon_cases c with ⟨rfl, h0⟩ | ⟨rfl, h0⟩ | h0
  · have : ¬ (FloatCode.negZero = 0) := by omega
    simp [Outcome.ok_bind, heq, hlt, this, h0, hz, FloatCode.canon_zero, and3, Value.isTrue,
      Outcome.Agree]
  · have : ¬ (FloatCode.negNan = 0) := by omega
    have hn1 : ¬ (FloatCode.nan < 0) := by omega
    have hn2 : ¬ (FloatCode.nan = 0) := by omega
    simp [Outcome.ok_bind, heq, hlt, this, hn1, hn2, h0, hn, FloatCode.canon_zero, and3,
      Value.isTrue, Outcome.Agree]
  · have hr := hcan c h0
    have hb : (g c == 0) = decide (g c = 0) := rfl
    by_cases hneg : c < 0 <;> by_cases hr0 : g c = 0 <;>
      simp [Outcome.ok_bind, heq, hlt, h0, hr, hneg, hr0, hb, FloatCode.canon_zero,
        FloatCode.canon_negZero', and3, Value.isTrue, Outcome.Agree]

/-- `round` on DuckDB, through `zeroTemplate`, agrees with the reference. -/
theorem Lowering.fround_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.froundTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .fround x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (fun _ => rfl) (fun _ => rfl) FloatCode.round_negZero
      FloatCode.round_negNan (fun _ h => FloatCode.canon_round h) c
  all_goals rfl

/-- `ceil` on DuckDB, through `zeroTemplate`, agrees with the reference. -/
theorem Lowering.fceil_agree (s : DuckDBSettings) (x : Value) :
    (Lowering.fceilTemplate.evalP (Profile.duckdb s) [x]).Agree
      (Profile.reference.un .fceil x) := by
  cases x
  case float c =>
    exact Lowering.zeroTemplate_float (fun _ => rfl) (fun _ => rfl) FloatCode.ceil_negZero
      FloatCode.ceil_negNan (fun _ h => FloatCode.canon_ceil h) c
  all_goals rfl

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
