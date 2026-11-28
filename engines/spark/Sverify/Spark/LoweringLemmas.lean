import Sverify.Engines.Lowering
import Sverify.Spark.Profile
import Sverify.Core.FloatDbl

/-!
# Spark's lowering: the hand-written templates (#271)

The entries of Spark's lowering that the search does not reach, each a
template over the core's functions evaluated under `Profile.spark`, with its
proof that it agrees with the reference on every value:

* `<<` and `>>` raise on a count outside `0`–`63`, where Spark takes the count
  modulo 64 (spark-int-shift): `Spark.shiftTemplate`, `Spark.shift_agree`.
* `date_add` raises past the reference's dates, where Spark wraps the day
  count at 32 bits (spark-date-range, SP-2): `Spark.dateAddTemplate`,
  `Spark.dateAdd_agree`.

The guards Spark's IEEE operations need (a NaN where the reference raises,
`sparkBin`'s `nanCase` arms, and an elementary function outside its domain,
`sparkUn .fmath`) are engines-common's (`nanGuard`, `fmathGuard`), as on
DuckDB. IEEE division and `atan2` have no exact template from Spark's own
functions: both differ from the reference only in a zero's sign, which no
comparison of Spark's sees (`BinFn.apply .eq` and `.lt` compare canonical
codes).
-/

namespace Substrait

variable [Boxes.Ambient]

/-! ## An entry from another one -/

omit [Boxes.Ambient] in
theorem Outcome.agreeOrRaises_trans {o₁ o₂ o₃ : Outcome} (h₁ : o₁.AgreeOrRaises o₂)
    (h₂ : o₂.AgreeOrRaises o₃) : o₁.AgreeOrRaises o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all [Outcome.AgreeOrRaises]

/-- An entry for `f` from one for `g`, where the reference's `g` agrees with
its `f` or raises: not exact (ruling 249). -/
def BinEntry.weaken {p : Profile} {g f : BinFn} (en : BinEntry p g)
    (h : ∀ x y, (Profile.reference.bin g x y).AgreeOrRaises (Profile.reference.bin f x y)) :
    BinEntry p f :=
  ⟨en.tmpl, en.strict, false, en.onDbl,
    fun x y hd => Outcome.agreeOrRaises_trans (en.agree x y hd) (h x y), fun h => by cases h⟩

namespace Spark

/-! ## Spark's functions that are the reference's -/

theorem spark_un_ref {f : UnFn} (h : ∀ x, sparkUn f x = none) (x : Value) :
    Profile.spark.un f x = Profile.reference.un f x := by
  show (sparkUn f x).getD _ = _; rw [h]; rfl

theorem spark_un_ref' {f : UnFn} {x : Value} (h : sparkUn f x = none) :
    Profile.spark.un f x = Profile.reference.un f x := by
  show (sparkUn f x).getD _ = _; rw [h]; rfl

theorem spark_bin_ref {f : BinFn} (h : ∀ x y, sparkBin f x y = none) (x y : Value) :
    Profile.spark.bin f x y = Profile.reference.bin f x y := by
  show (sparkBin f x y).getD _ = _; rw [h]; rfl

theorem spark_lt (x y : Value) : Profile.spark.bin .lt x y = .ok (BinFn.apply .lt x y) := by
  rw [spark_bin_ref (fun _ _ => rfl), Lowering.ref_lt]
theorem spark_and (x y : Value) : Profile.spark.bin .and x y = .ok (and3 x y) := by
  rw [spark_bin_ref (fun _ _ => rfl), Lowering.ref_and]
theorem spark_or (x y : Value) : Profile.spark.bin .or x y = .ok (or3 x y) := by
  rw [spark_bin_ref (fun _ _ => rfl), Lowering.ref_or]
theorem spark_dateDiff (x y : Value) :
    Profile.spark.bin .dateDiff x y = .ok (BinFn.apply .dateDiff x y) := by
  rw [spark_bin_ref (fun _ _ => rfl)]; cases x <;> cases y <;> rfl
theorem spark_not (x : Value) :
    Profile.spark.un .not x = .ok (match x with | .bool b => .bool !b | _ => .null) := by
  rw [spark_un_ref (fun _ => rfl)]; cases x <;> rfl
theorem spark_isNum (k : NumKind) (x : Value) :
    Profile.spark.un (.isNum k) x = .ok (.bool (x.isNum k)) := by
  rw [spark_un_ref (fun _ => rfl), Lowering.ref_isNum]
theorem spark_raise (m : String) (x : Value) : Profile.spark.un (.raise m) x = .error .raised := by
  rw [spark_un_ref (fun _ => rfl), Lowering.ref_raise]

/-! ## Three-valued logic on known truth values -/

omit [Boxes.Ambient] in
theorem and3_bool (p q : Bool) : and3 (.bool p) (.bool q) = .bool (p && q) := by
  cases p <;> cases q <;> rfl
omit [Boxes.Ambient] in
theorem or3_bool (p q : Bool) : or3 (.bool p) (.bool q) = .bool (p || q) := by
  cases p <;> cases q <;> rfl
omit [Boxes.Ambient] in
theorem isTrue_bool (b : Bool) : (Value.bool b).isTrue = b := by cases b <;> rfl
theorem lt_int (a b : Int) : BinFn.apply .lt (.int a) (.int b) = .bool (decide (a < b)) := rfl
theorem lt_date (a b : Int) : BinFn.apply .lt (.date a) (.date b) = .bool (decide (a < b)) := rfl
theorem dateDiff_date (a b : Int) : BinFn.apply .dateDiff (.date a) (.date b) = .int (a - b) := rfl

/-! ## `<<` and `>>` -/

/-- `CASE WHEN #0 IS INT AND (#1 < 0 OR NOT #1 < 64) THEN error ELSE op(#0, #1)
END`: the reference's shift, which raises outside `0`–`63`, on Spark, which
takes the count modulo 64. -/
def shiftTemplate (op : BitOp) : Expr :=
  .ifThen (.bin .and (.un (.isNum .int) (.field 0))
      (.bin .or (.bin .lt (.field 1) (.lit (.int 0)))
        (.un .not (.bin .lt (.field 1) (.lit (.int 64))))))
    (.un (.raise "domain error") (.field 1)) (.bin (.bit op) (.field 0) (.field 1))

omit [Boxes.Ambient] in
theorem shiftTemplate_must (op : BitOp) :
    0 ∈ (shiftTemplate op).must ∧ 1 ∈ (shiftTemplate op).must := by
  simp [Expr.must, shiftTemplate]

/-- Spark's bitwise functions are the reference's but for a shift of an
integer by a count outside `0`–`63`. -/
theorem spark_bit {op : BitOp} {x y : Value}
    (h : ∀ a b, x = .int a → y = .int b → 0 ≤ b ∧ b < 64) :
    Profile.spark.bin (.bit op) x y = Profile.reference.bin (.bit op) x y := by
  show (sparkBin _ x y).getD _ = _
  cases op <;> cases x <;> cases y <;> try rfl
  all_goals
    rename_i a b
    have := h a b rfl rfl
    simp [sparkBin, this]

/-- **Spark's lowering of `<<` and `>>`** (`shiftTemplate`) agrees with the
reference on every value. -/
theorem shift_agree {op : BitOp} (hop : op = .shl ∨ op = .shr) (x y : Value) :
    ((shiftTemplate op).evalP Profile.spark [x, y]).Agree
      (Profile.reference.bin (.bit op) x y) := by
  simp only [shiftTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    spark_isNum, spark_lt, spark_or, spark_not, spark_and, spark_raise]
  cases x
  case int a =>
    cases y
    case int b =>
      simp only [Value.isNum, lt_int, or3_bool, and3_bool, isTrue_bool, Bool.true_and]
      by_cases hb : 0 ≤ b ∧ b < 64
      · have h1 : ¬ b < 0 := by omega
        have h2 : b < 64 := hb.2
        rw [spark_bit (fun _ _ h h' => by cases h; cases h'; exact hb)]
        simp [h1, h2, Outcome.agree_refl]
      · have hr : Profile.reference.bin (.bit op) (.int a) (.int b) = .error .domain := by
          rcases hop with rfl | rfl <;>
            simp [Profile.reference, raiseIf, BinFn.issue, domainIssue, BitOp.apply, hb,
              Issue.isError]
        have hc : (decide (b < 0) || !decide (b < 64)) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
          omega
        simp [hc, hr, Outcome.Agree]
    all_goals
      rw [spark_bit (fun _ _ h h' => by cases h' )]
      simp [Value.isNum, BinFn.apply, and3, or3, Value.isTrue, Outcome.agree_refl]
  all_goals
    rw [spark_bit (fun _ _ h _ => by cases h)]
    simp [Value.isNum, and3, Value.isTrue, Outcome.agree_refl]

/-! ## `date_add` -/

/-- `CASE WHEN #0 IS DATE AND #1 IS INT AND NOT (DATE dayMin ≤ #0 AND #0 ≤
DATE dayMax AND dayMin - #0 ≤ #1 AND #1 ≤ dayMax - #0) THEN error ELSE
date_add(#0, #1) END`, the differences as `dateDiff` of the bounds: the
reference's `date_add`, which raises past its dates, on Spark, which wraps
the day count at 32 bits. Inside the dates the count is less than `2³¹` in
size, where Spark's sum does not wrap. -/
def dateAddTemplate : Expr :=
  let a := Expr.field 0
  let b := Expr.field 1
  let lo := Expr.lit (.date Time.dayMin)
  let hi := Expr.lit (.date Time.dayMax)
  let le (x y : Expr) := Expr.un .not (.bin .lt y x)
  .ifThen (.bin .and (.un (.isNum .date) a) (.bin .and (.un (.isNum .int) b)
      (.un .not (.bin .and (.bin .and (le lo a) (le a hi))
        (.bin .and (le (.bin .dateDiff lo a) b) (le b (.bin .dateDiff hi a)))))))
    (.un (.raise "overflow") b) (.bin .dateAdd a b)

omit [Boxes.Ambient] in
theorem dateAddTemplate_must : 0 ∈ dateAddTemplate.must ∧ 1 ∈ dateAddTemplate.must := by
  simp [Expr.must, dateAddTemplate]

/-- Spark's `date_add` is the reference's on a date and a count that keep
the reference's dates. -/
theorem spark_dateAdd_in {a b : Int} (h1 : Time.dayMin ≤ a) (h2 : a ≤ Time.dayMax)
    (h3 : Time.dayMin ≤ a + b) (h4 : a + b ≤ Time.dayMax) :
    Profile.spark.bin .dateAdd (.date a) (.int b) = .ok (.date (a + b)) := by
  have hmin : Time.dayMin = -719162 := rfl
  have hmax : Time.dayMax = 2932896 := rfl
  have hb : -2 ^ 31 ≤ b ∧ b < 2 ^ 31 := by omega
  show (sparkBin _ _ _).getD _ = _
  simp only [sparkBin, hb, and_self, ↓reduceIte, Option.getD_some]
  rw [Spark.wrap32_of_small (by omega) (by omega)]

/-- Spark's `date_add` of anything but a date and an integer is the
reference's. -/
theorem spark_dateAdd_ne {x y : Value} (h : ∀ a b, x = .date a → y = .int b → False) :
    Profile.spark.bin .dateAdd x y = Profile.reference.bin .dateAdd x y := by
  show (sparkBin _ x y).getD _ = _
  cases x <;> cases y <;> try rfl
  exact (h _ _ rfl rfl).elim

theorem ref_dateAdd_out {a b : Int}
    (h : ¬ (Time.dayMin ≤ a ∧ a ≤ Time.dayMax ∧ Time.dayMin ≤ a + b ∧ a + b ≤ Time.dayMax)) :
    Profile.reference.bin .dateAdd (.date a) (.int b) = .error .overflow := by
  have : ¬ (between Time.dayMin Time.dayMax a = true ∧
      between Time.dayMin Time.dayMax (a + b) = true) := by
    simp only [between, Bool.and_eq_true, decide_eq_true_eq]; omega
  simp [Profile.reference, raiseIf, BinFn.issue, rangeIssue, this, Issue.isError]

/-- **Spark's lowering of `date_add`** (`dateAddTemplate`) agrees with the
reference on every value. -/
theorem dateAdd_agree (x y : Value) :
    (dateAddTemplate.evalP Profile.spark [x, y]).Agree (Profile.reference.bin .dateAdd x y) := by
  simp only [dateAddTemplate, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ,
    Outcome.ok_bind, spark_isNum, spark_lt, spark_and, spark_not, spark_dateDiff, spark_raise]
  cases x
  case date a =>
    cases y
    case int b =>
      simp only [Value.isNum, lt_int, lt_date, dateDiff_date, and3_bool, isTrue_bool,
        Bool.true_and]
      by_cases hr : Time.dayMin ≤ a ∧ a ≤ Time.dayMax ∧ Time.dayMin ≤ a + b ∧ a + b ≤ Time.dayMax
      · obtain ⟨h1, h2, h3, h4⟩ := hr
        have n1 : ¬ a < Time.dayMin := by omega
        have n2 : ¬ Time.dayMax < a := by omega
        have n3 : ¬ b < Time.dayMin - a := by omega
        have n4 : ¬ Time.dayMax - a < b := by omega
        simp [n1, n2, n3, n4, spark_dateAdd_in h1 h2 h3 h4, Profile.reference, raiseIf,
          BinFn.issue, rangeIssue, between, h1, h2, h3, h4, BinFn.apply, Outcome.Agree]
      · rw [ref_dateAdd_out hr]
        have : a < Time.dayMin ∨ Time.dayMax < a ∨ b < Time.dayMin - a ∨ Time.dayMax - a < b := by
          omega
        rcases this with n | n | n | n <;> simp [n, Outcome.Agree]
    all_goals
      rw [spark_dateAdd_ne (fun _ _ _ h => by cases h)]
      simp [Value.isNum, and3, Value.isTrue, Outcome.agree_refl]
  all_goals
    rw [spark_dateAdd_ne (fun _ _ h _ => by cases h)]
    simp [Value.isNum, and3, Value.isTrue, Outcome.agree_refl]

/-! ## IEEE division from `/`

The reference's `/` raises at a zero divisor of either sign, where IEEE
division gives `±∞`; elsewhere the two agree. So `/`'s entry, which raises
there as Spark does under ANSI, is IEEE division's, not exact (ruling 249). -/

/-- **The reference's `/` agrees with its IEEE division or raises.** -/
theorem ref_fdiv_fdivIeee (x y : Value) :
    (Profile.reference.bin .fdiv x y).AgreeOrRaises (Profile.reference.bin .fdivIeee x y) := by
  cases x <;> cases y
  case float.float a b =>
    show (raiseIf (BinFn.issue .fdiv (.float a) (.float b)) (BinFn.apply .fdiv (.float a) (.float b))).AgreeOrRaises
      (raiseIf (BinFn.issue .fdivIeee (.float a) (.float b)) (BinFn.apply .fdivIeee (.float a) (.float b)))
    simp only [BinFn.issue, BinFn.apply]
    by_cases hb : FloatCode.canon b = 0
    · simp [hb, raiseIf, Issue.isError, Outcome.AgreeOrRaises]
    · have hn : nanCase .fdivIeee a b = nanCase .fdiv a b := by
        simp [nanCase, hb]
      have hv : FloatCode.fdiv a (FloatCode.canon b) = FloatCode.fdiv a b := by
        rcases FloatCode.canon_cases b with ⟨_, h⟩ | ⟨rfl, h⟩ | h
        · exact absurd h hb
        · rw [h]; simp [FloatCode.fdiv, FloatCode.divI, FloatCode.isNanCode]
        · rw [h]
      simp only [hb, ↓reduceIte, nanIssue, hn, hv]
      split <;> simp [raiseIf, Issue.isError, Outcome.AgreeOrRaises]
  all_goals rfl

/-! ## `floor` and `ceil` (ruling 248)

Spark's `floor` and `ceil` give a `BIGINT`, which raises past `2⁶³`. A double
of `2⁵²` or more is an integer (`FloatCode.floor_dbl_big`), so the template
passes it through and floors the rest: exact on doubles' codes (`onDbl`). -/

set_option exponentiation.threshold 2200

/-- The code of `2⁵²`. -/
def big : Int := 2 * ((2 ^ 1126 : Nat) : Int) + 1

/-- `CASE WHEN #0 IS DOUBLE AND NOT (-2⁵² < #0 AND #0 < 2⁵²) THEN #0 ELSE f(#0) END`. -/
def wholeTemplate (f : UnFn) : Expr :=
  .ifThen (.bin .and (.un (.isNum .float) (.field 0))
      (.un .not (.bin .and (.bin .lt (.lit (.float (-big))) (.field 0))
        (.bin .lt (.field 0) (.lit (.float big))))))
    (.field 0) (.un f (.field 0))

omit [Boxes.Ambient] in
theorem wholeTemplate_must (f : UnFn) : 0 ∈ (wholeTemplate f).must := by
  simp [Expr.must, wholeTemplate]

omit [Boxes.Ambient] in
theorem canon_neg_big : FloatCode.canon (-big) = -big := by
  have := FloatCode.pow_le_maxMag (k := 1126) (by decide)
  apply fp64.canon_eq_self
  have hZ := fp64.negZero_eq; have hY := fp64.negNan_eq
  have e : (FloatCode.maxMag : Int) = fp64.maxMag := rfl
  constructor <;> (unfold big; omega)

omit [Boxes.Ambient] in
theorem canon_big : FloatCode.canon big = big := by
  have := FloatCode.pow_le_maxMag (k := 1126) (by decide)
  apply fp64.canon_eq_self
  have hZ := fp64.negZero_eq; have hY := fp64.negNan_eq
  constructor <;> (unfold big; omega)

omit [Boxes.Ambient] in
/-- Outside `(-2⁵², 2⁵²)`, a double's code that is no NaN or infinity has a
magnitude of `2⁵²` or more. -/
theorem mag_big {c : Int} (h : ¬(-big < c ∧ c < big)) : 2 ^ 52 * FloatCode.K ≤ FloatCode.mag c := by
  have e : 2 ^ 52 * FloatCode.K = 2 ^ 1126 := by unfold FloatCode.K; rw [← Nat.pow_add]
  rw [e]; unfold FloatCode.mag; unfold big at h; omega

/-- **The template agrees with the reference on doubles**, for a rounding `g`
that keeps the doubles of `2⁵²` or more, which Spark computes as the
reference does inside `(-2⁵², 2⁵²)`. -/
theorem wholeTemplate_agree {f : UnFn} {g : Int → Int}
    (href : ∀ c, Profile.reference.un f (.float c) = .ok (.float (g c)))
    (hg : ∀ c, FloatCode.Dbl c → (FloatCode.maxMag < FloatCode.mag c ∨
      2 ^ 52 * FloatCode.K ≤ FloatCode.mag c) → g c = c)
    (hsp : ∀ c, -big < FloatCode.canon c → FloatCode.canon c < big → sparkUn f (.float c) = none)
    (hnf : ∀ v, (∀ c, v ≠ .float c) → sparkUn f v = none)
    (x : Value) (hx : x.dbl = true) :
    ((wholeTemplate f).evalP Profile.spark [x]).Agree (Profile.reference.un f x) := by
  simp only [wholeTemplate, Expr.evalP, List.getD_cons_zero, Outcome.ok_bind, spark_isNum,
    spark_lt, spark_and, spark_not]
  cases x
  case float c =>
    have hlt : ∀ a b : Int, BinFn.apply .lt (.float a) (.float b) =
        .bool (decide (FloatCode.canon a < FloatCode.canon b)) := fun _ _ => rfl
    simp only [Value.isNum, hlt, canon_neg_big, canon_big, and3_bool, isTrue_bool, Bool.true_and]
    by_cases hin : -big < FloatCode.canon c ∧ FloatCode.canon c < big
    · have : (!(decide (-big < FloatCode.canon c) && decide (FloatCode.canon c < big))) = false := by
        simp [hin.1, hin.2]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      rw [spark_un_ref' (hsp c hin.1 hin.2)]
      exact Outcome.agree_refl _
    · have : (!(decide (-big < FloatCode.canon c) && decide (FloatCode.canon c < big))) = true := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp, decide_eq_true_eq,
          decide_eq_false_iff_not]
        intro h; exact fun h' => hin ⟨h, h'⟩
      simp only [this, ↓reduceIte, href, Outcome.Agree, Value.float.injEq]
      have hd : FloatCode.Dbl c := by simpa using hx
      refine (hg c hd ?_).symm
      by_cases hb : FloatCode.maxMag < FloatCode.mag c
      · exact .inl hb
      · refine .inr (mag_big ?_)
        obtain ⟨m0, m1, -⟩ := FloatCode.maxMag_lt_mag_special
        have hc : FloatCode.canon c = c := by
          apply fp64.canon_eq_self
          exact ⟨fun h => hb (by subst h; exact m0), fun h => hb (by subst h; exact m1)⟩
        rwa [hc] at hin
  all_goals
    simp only [Value.isNum, and3, Value.isTrue, Bool.false_eq_true, ↓reduceIte]
    rw [spark_un_ref' (hnf _ (fun _ h => by cases h))]
    exact Outcome.agree_refl _

omit [Boxes.Ambient] in
/-- `±2⁶³` as doubles lie beyond `±2⁵²`: through `±2⁵³`, which convert exactly. -/
theorem ofInt_2_63 : big < FloatCode.ofInt (2 ^ 63) ∧ FloatCode.ofInt (-(2 ^ 63)) < -big := by
  have h53 := FloatCode.ofInt_exact (i := 2 ^ 53) (by decide)
  have hm53 := FloatCode.ofInt_exact (i := -(2 ^ 53)) (by decide)
  have m1 := FloatCode.ofInt_mono (i := 2 ^ 53) (j := 2 ^ 63) (by decide)
  have m2 := FloatCode.ofInt_mono (i := -(2 ^ 63)) (j := -(2 ^ 53)) (by decide)
  have e1 : FloatCode.exactCode (2 ^ 53) = 2 * ((2 ^ 1127 : Nat) : Int) + 1 := by decide
  have e2 : FloatCode.exactCode (-(2 ^ 53)) = -(2 * ((2 ^ 1127 : Nat) : Int) + 1) := by decide
  have hb : (2 ^ 1126 : Nat) < 2 ^ 1127 := Nat.pow_lt_pow_right (by decide) (by decide)
  unfold big; rw [h53, e1] at m1; rw [hm53, e2] at m2; omega

omit [Boxes.Ambient] in
/-- Spark's `floor` and `ceil` are the reference's inside `(-2⁵², 2⁵²)`. -/
theorem sparkUn_whole {f : UnFn} (hf : f = .ffloor ∨ f = .fceil) {c : Int}
    (h1 : -big < FloatCode.canon c) (h2 : FloatCode.canon c < big) : sparkUn f (.float c) = none := by
  obtain ⟨o1, o2⟩ := ofInt_2_63
  have hP := FloatCode.posInf_eq; have hN := FloatCode.negInf_eq
  have hQ : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  have hZ := FloatCode.negZero_eq'; have hY := FloatCode.negNan_eq'
  have hk := FloatCode.pow_le_maxMag (k := 1126) (by decide)
  have hbig : big ≤ 2 * (FloatCode.maxMag : Int) + 1 := by unfold big; omega
  have hn : FloatCode.canon c ≠ FloatCode.nan := by omega
  have hi : isInfCode c = false := by
    rcases FloatCode.canon_cases c with ⟨rfl, _⟩ | ⟨rfl, h⟩ | h
    · simp [isInfCode]; omega
    · exact absurd h hn
    · rw [h] at h1 h2; simp [isInfCode]; omega
  have hr : ¬((FloatCode.ofInt (2 ^ 63) ≤ c ∧ c < FloatCode.posInf) ∨
      (FloatCode.negInf < c ∧ c < FloatCode.ofInt (-(2 ^ 63)))) := by
    rcases FloatCode.canon_cases c with ⟨rfl, _⟩ | ⟨rfl, h⟩ | h
    · omega
    · exact absurd h hn
    · rw [h] at h1 h2; omega
  have hc : ¬(isInfCode c = true ∨ (FloatCode.ofInt (2 ^ 63) ≤ c ∧ c < FloatCode.posInf) ∨
      (FloatCode.negInf < c ∧ c < FloatCode.ofInt (-(2 ^ 63)))) := by
    rintro (h | h)
    · rw [hi] at h; cases h
    · exact hr h
  rcases hf with rfl | rfl <;> simp only [sparkUn, hn, hc, ↓reduceIte]

omit [Boxes.Ambient] in
theorem floor_keeps {c : Int} (hd : FloatCode.Dbl c)
    (h : FloatCode.maxMag < FloatCode.mag c ∨ 2 ^ 52 * FloatCode.K ≤ FloatCode.mag c) :
    FloatCode.floor c = c := by
  rcases h with h | h
  · unfold FloatCode.floor; exact FloatCode.onMag_of_big h
  · exact FloatCode.floor_dbl_big hd h

omit [Boxes.Ambient] in
theorem ceil_keeps {c : Int} (hd : FloatCode.Dbl c)
    (h : FloatCode.maxMag < FloatCode.mag c ∨ 2 ^ 52 * FloatCode.K ≤ FloatCode.mag c) :
    FloatCode.ceil c = c := by
  rcases h with h | h
  · unfold FloatCode.ceil; exact FloatCode.onMag_of_big h
  · exact FloatCode.ceil_dbl_big hd h

omit [Boxes.Ambient] in
theorem sparkUn_nonfloat {f : UnFn} (hf : f = .ffloor ∨ f = .fceil) (v : Value)
    (hv : ∀ c, v ≠ .float c) : sparkUn f v = none := by
  rcases hf with rfl | rfl <;> cases v <;> first | rfl | exact absurd rfl (hv _)

/-- **Spark's `floor`**: exact on doubles' codes (`onDbl`, ruling 248). -/
def ffloorEntry : UnEntry Profile.spark .ffloor :=
  ⟨wholeTemplate .ffloor, wholeTemplate_must _, true, true,
    fun x hx => Outcome.agreeOrRaises_of_agree (wholeTemplate_agree (g := FloatCode.floor)
      (fun _ => rfl) (fun _ hd h => floor_keeps hd h) (fun _ h1 h2 => sparkUn_whole (.inl rfl) h1 h2)
      (sparkUn_nonfloat (.inl rfl)) x (hx rfl)),
    fun _ x hx => wholeTemplate_agree (g := FloatCode.floor)
      (fun _ => rfl) (fun _ hd h => floor_keeps hd h) (fun _ h1 h2 => sparkUn_whole (.inl rfl) h1 h2)
      (sparkUn_nonfloat (.inl rfl)) x (hx rfl)⟩

/-- **Spark's `ceil`**: exact on doubles' codes (`onDbl`, ruling 248). -/
def fceilEntry : UnEntry Profile.spark .fceil :=
  ⟨wholeTemplate .fceil, wholeTemplate_must _, true, true,
    fun x hx => Outcome.agreeOrRaises_of_agree (wholeTemplate_agree (g := FloatCode.ceil)
      (fun _ => rfl) (fun _ hd h => ceil_keeps hd h) (fun _ h1 h2 => sparkUn_whole (.inr rfl) h1 h2)
      (sparkUn_nonfloat (.inr rfl)) x (hx rfl)),
    fun _ x hx => wholeTemplate_agree (g := FloatCode.ceil)
      (fun _ => rfl) (fun _ hd h => ceil_keeps hd h) (fun _ h1 h2 => sparkUn_whole (.inr rfl) h1 h2)
      (sparkUn_nonfloat (.inr rfl)) x (hx rfl)⟩

/-! ## Arguments that are not doubles

What lets a generated proof keep such an argument whole, as DuckDB's
`Lowering.duck_bin_nondouble_l` does. -/

/-- The functions of doubles `sparkBin` overrides. -/
def _root_.Substrait.BinFn.sparkOnFloats : BinFn → Bool
  | .fadd | .fsub | .fmul | .fdiv | .fdivIeee | .fmod | .fpow | .fatan2 => true
  | _ => false

theorem spark_bin_nondouble_l {f : BinFn} (hf : f.sparkOnFloats = true) {x : Value}
    (hx : x.isDouble = false) (y : Value) :
    Profile.spark.bin f x y = Profile.reference.bin f x y := by
  show (sparkBin f x y).getD _ = _
  cases f <;> simp only [BinFn.sparkOnFloats, Bool.false_eq_true] at hf <;>
    cases x <;> simp only [Value.isDouble, Bool.true_eq_false] at hx <;> rfl

theorem spark_bin_nondouble_r {f : BinFn} (hf : f.sparkOnFloats = true) (x : Value) {y : Value}
    (hy : y.isDouble = false) :
    Profile.spark.bin f x y = Profile.reference.bin f x y := by
  show (sparkBin f x y).getD _ = _
  cases f <;> simp only [BinFn.sparkOnFloats, Bool.false_eq_true] at hf <;>
    cases y <;> simp only [Value.isDouble, Bool.true_eq_false] at hy <;> cases x <;> rfl

theorem ref_bin_nondouble_l {f : BinFn} (hf : f.sparkOnFloats = true) {x : Value}
    (hx : x.isDouble = false) (y : Value) : Profile.reference.bin f x y = .ok .null := by
  cases f <;> simp only [BinFn.sparkOnFloats, Bool.false_eq_true] at hf <;>
    cases x <;> simp only [Value.isDouble, Bool.true_eq_false] at hx <;> cases y <;> rfl

theorem ref_bin_nondouble_r {f : BinFn} (hf : f.sparkOnFloats = true) (x : Value) {y : Value}
    (hy : y.isDouble = false) : Profile.reference.bin f x y = .ok .null := by
  cases f <;> simp only [BinFn.sparkOnFloats, Bool.false_eq_true] at hf <;>
    cases y <;> simp only [Value.isDouble, Bool.true_eq_false] at hy <;> cases x <;> rfl

theorem spark_un_nondouble (f : UnFn) {x : Value} (hx : x.isDouble = false) :
    Profile.spark.un f x = Profile.reference.un f x := by
  show (sparkUn f x).getD _ = _
  cases x <;> simp only [Value.isDouble, Bool.true_eq_false] at hx <;> cases f <;> rfl

/-! ## The names the generator reads (`Schemas.proofs := Substrait.Spark`) -/

/-- `<<`'s template, named for the generator (`shlTemplate_must`). -/
def shlTemplate : Expr := shiftTemplate .shl
/-- `>>`'s template. -/
def shrTemplate : Expr := shiftTemplate .shr

omit [Boxes.Ambient] in
theorem shlTemplate_must : 0 ∈ shlTemplate.must ∧ 1 ∈ shlTemplate.must := shiftTemplate_must _
omit [Boxes.Ambient] in
theorem shrTemplate_must : 0 ∈ shrTemplate.must ∧ 1 ∈ shrTemplate.must := shiftTemplate_must _

theorem bit_shl_agree (x y : Value) :
    (shlTemplate.evalP Profile.spark [x, y]).Agree (Profile.reference.bin (.bit .shl) x y) :=
  shift_agree (.inl rfl) x y

theorem bit_shr_agree (x y : Value) :
    (shrTemplate.evalP Profile.spark [x, y]).Agree (Profile.reference.bin (.bit .shr) x y) :=
  shift_agree (.inr rfl) x y

/-! ## Casts of a double to `BIGINT` (ruling 290, #2630)

Spark's `CAST` and `TRY_CAST` saturate the double `2⁶³` (spark-cast-double-to-int),
which `Profile.spark` does not state (`Spark.ftoiExcepted`): the templates raise, or give
NULL, at `2⁶³` and above before the native cast, so it is called only below `2⁶³`, where
it is the reference's. The soundness does not rest on Spark evaluating only the `CASE`
branch a row takes (S4): the native branch's value is discarded where the guard holds.
There the native cast returns at `2⁶³` (spark-cast-double-to-int, ruling 290's P6), and it
raises only where the reference raises, past `2⁶³`, at NaN and `±∞`; `TRY_CAST` raises
nowhere. -/

/-- `#0` is a double of `2⁶³` or more, or NaN (canonical codes order NaN above `+∞`). -/
def ftoiGuard : Expr :=
  .bin .and (.un (.isNum .float) (.field 0))
    (.un .not (.bin .lt (.field 0) (.lit (.float Spark.code2_63))))

/-- `CASE WHEN ftoiGuard THEN error ELSE CAST(#0 AS BIGINT) END`. -/
def ftoiTemplate : Expr :=
  .ifThen ftoiGuard (.un (.raise "CAST to BIGINT out of range") (.field 0)) (.un .ftoi (.field 0))

/-- `CASE WHEN ftoiGuard THEN NULL ELSE TRY_CAST(#0 AS BIGINT) END`. -/
def ftoiOrNullTemplate : Expr :=
  .ifThen ftoiGuard (.lit .null) (.un .ftoiOrNull (.field 0))

omit [Boxes.Ambient] in
theorem ftoiTemplate_must : 0 ∈ ftoiTemplate.must := by simp [Expr.must, ftoiTemplate, ftoiGuard]
omit [Boxes.Ambient] in
theorem ftoiOrNullTemplate_must : 0 ∈ ftoiOrNullTemplate.must := by
  simp [Expr.must, ftoiOrNullTemplate, ftoiGuard]

omit [Boxes.Ambient] in
theorem canon_code2_63 : FloatCode.canon Spark.code2_63 = Spark.code2_63 := by
  have hb := FloatCode.big_lt_maxMag
  apply fp64.canon_eq_self
  have hZ := fp64.negZero_eq; have hY := fp64.negNan_eq
  have e : (FloatCode.maxMag : Int) = fp64.maxMag := rfl
  constructor <;> (unfold Spark.code2_63 FloatCode.castHi; omega)

omit [Boxes.Ambient] in
theorem toInt?_code2_63 : FloatCode.toInt? Spark.code2_63 = some (2 ^ 63) := by
  have hb := FloatCode.big_lt_maxMag
  have hK := FloatCode.K_pos
  have hm : FloatCode.mag Spark.code2_63 = 2 ^ 63 * FloatCode.K := by
    unfold FloatCode.mag Spark.code2_63 FloatCode.castHi; omega
  unfold FloatCode.toInt?
  rw [hm]
  simp only [show ¬ FloatCode.maxMag < 2 ^ 63 * FloatCode.K from by omega, ite_false,
    show ¬ Spark.code2_63 < 0 from by unfold Spark.code2_63 FloatCode.castHi; omega,
    Nat.mul_div_cancel _ hK]
  rfl

omit [Boxes.Ambient] in
/-- At `2⁶³` and above, the reference's truncation leaves 64 bits, or has no integer. -/
theorem toInt?_above {c : Int} (h : ¬ FloatCode.canon c < Spark.code2_63) :
    ∀ i, FloatCode.toInt? (FloatCode.canon c) = some i → 2 ^ 63 ≤ i := fun i hi =>
  FloatCode.toInt?_mono (by omega) toInt?_code2_63 hi

theorem spark_ftoi (v : Value) : Profile.spark.un .ftoi v = Profile.reference.un .ftoi v :=
  spark_un_ref (fun x => by cases x <;> rfl) v
theorem spark_ftoiOrNull (v : Value) :
    Profile.spark.un .ftoiOrNull v = Profile.reference.un .ftoiOrNull v :=
  spark_un_ref (fun x => by cases x <;> rfl) v

omit [Boxes.Ambient] in
theorem and3_true_bool (b : Bool) : and3 (.bool true) (.bool b) = .bool b := by cases b <;> rfl

theorem ftoiGuard_eval (v : Value) : ftoiGuard.evalP Profile.spark [v] = .ok (match v with
    | .float c => .bool (!decide (FloatCode.canon c < Spark.code2_63))
    | _ => .bool false) := by
  simp only [ftoiGuard, Expr.evalP, List.getD_cons_zero, Outcome.ok_bind, spark_isNum, spark_lt,
    spark_and, spark_not]
  cases v <;> simp [Value.isNum, BinFn.apply, canon_code2_63, and3_true_bool] <;> rfl

/-- **P1 (ruling 290): the native cast is reached only where Spark's is the reference's.**
Where `ftoiGuard` does not hold, the argument is not `Spark.ftoiExcepted`. -/
theorem ftoi_native_not_excepted {v : Value}
    (h : (ftoiGuard.evalP Profile.spark [v]) = .ok (.bool false)) : Spark.ftoiExcepted v = false := by
  rw [ftoiGuard_eval] at h
  cases v <;> simp_all [Spark.ftoiExcepted]
  omega

theorem ftoi_agree (v : Value) :
    (ftoiTemplate.evalP Profile.spark [v]).Agree (Profile.reference.un .ftoi v) := by
  simp only [ftoiTemplate, Expr.evalP, List.getD_cons_zero, ftoiGuard_eval, Outcome.ok_bind,
    spark_ftoi, spark_raise]
  cases v
  case float c =>
    by_cases hc : FloatCode.canon c < Spark.code2_63
    · simp [hc, Value.isTrue, Outcome.agree_refl]
    · simp only [hc, decide_false, Bool.not_false, Value.isTrue, ite_true]
      simp only [Profile.reference, UnFn.issue, raiseIf]
      cases ht : FloatCode.toInt? (FloatCode.canon c) with
      | none => simp [Outcome.Agree, Issue.isError]
      | some i =>
        have := toInt?_above hc i ht
        have hm : ¬ i ≤ FloatCode.maxI64 := by unfold FloatCode.maxI64; omega
        have hn : inI64 i = false := by simp [inI64, between, hm]
        simp [hn, Outcome.Agree, Issue.isError]
  all_goals simp [Value.isTrue, Outcome.agree_refl]

theorem ftoiOrNull_agree (v : Value) :
    (ftoiOrNullTemplate.evalP Profile.spark [v]).Agree (Profile.reference.un .ftoiOrNull v) := by
  simp only [ftoiOrNullTemplate, Expr.evalP, ftoiGuard_eval, Outcome.ok_bind, List.getD_cons_zero,
    spark_ftoiOrNull]
  cases v
  case float c =>
    by_cases hc : FloatCode.canon c < Spark.code2_63
    · simp [hc, Value.isTrue, Outcome.agree_refl]
    · simp only [hc, decide_false, Bool.not_false, Value.isTrue, ite_true]
      simp only [Profile.reference, UnFn.issue, raiseIf, UnFn.apply]
      cases ht : FloatCode.toInt? (FloatCode.canon c) with
      | none => simp [Outcome.Agree]
      | some i =>
        have := toInt?_above hc i ht
        have hn : fitsBits 64 i = false := by simp [fitsBits, between]; omega
        simp [hn, Outcome.Agree]
  all_goals simp [Value.isTrue, Outcome.agree_refl]

/-- **Spark's `CAST(x AS BIGINT)`**, hand-built: `ftoiTemplate`, exact. -/
def ftoiEntry : UnEntry Profile.spark .ftoi := .ofAgree ftoiTemplate ftoiTemplate_must ftoi_agree

/-- **Spark's `TRY_CAST(x AS BIGINT)`**, hand-built: `ftoiOrNullTemplate`, exact. -/
def ftoiOrNullEntry : UnEntry Profile.spark .ftoiOrNull :=
  .ofAgree ftoiOrNullTemplate ftoiOrNullTemplate_must ftoiOrNull_agree

end Spark

end Substrait
