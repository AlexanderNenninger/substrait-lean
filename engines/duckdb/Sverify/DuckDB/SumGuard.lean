import Sverify.DuckDB.SQL
import Sverify.Analysis.Safety
import Sverify.Engines.Lowering

/-!
# DuckDB's `SUM` and `AVG` of doubles, from three measures (#341)

DuckDB's `sum` and `avg` of doubles give NaN for `+∞` and `-∞` together, a NaN
among the values, and `±∞` for one kind of infinity. The reference's `SUM`
agrees (`AggFn.apply .fsum`), but a `sum` measure over values that may hold
both infinities makes a NaN, which the checker reports as a domain error
(`AggFn.makesNan`, D37). The lift therefore writes the aggregate as

* `s = fsum(CASE WHEN x < +∞ THEN x END)` (or `avg`): no `+∞`, no NaN, so no NaN
  is made, whatever the group (`SumGuard.noNan`);
* `hi = max(x)` and `lo = min(x)`: NaN compares greatest, `-∞` least;

finished by `CASE WHEN hi = NaN THEN NaN WHEN hi = +∞ AND lo = -∞ THEN NaN
WHEN hi = +∞ THEN +∞ ELSE s END`. `SumGuard.agree` proves that this is
`AggFn.apply` of the non-NULL values, for every group of doubles.
-/

namespace Substrait
open FloatCode

section
variable [Boxes.Ambient]

/-- The argument of the guarded measure: `CASE WHEN x < +∞ THEN x END`. -/
def SumGuard.arg : Expr :=
  .ifThen (.bin .lt (.field 0) (.lit (.float posInf))) (.field 0) (.lit .null)

/-- Is the value a double below `+∞` (by canonical code)? -/
def SumGuard.below : Value → Bool
  | .float c => decide (canon c < posInf)
  | _ => false

/-- A double of DuckDB's `DOUBLE`: what `DuckType.Has` says. -/
def SumGuard.Valid (c : Int) : Prop :=
  ((negInf ≤ c ∧ c ≤ posInf) ∨ c = nan) ∨ c = negZero ∨ c = negNan

omit [Boxes.Ambient] in
theorem SumGuard.canon_valid {c : Int} (h : SumGuard.Valid c) :
    (negInf ≤ canon c ∧ canon c ≤ posInf) ∨ canon c = nan := by
  rcases h with (⟨h1, h2⟩ | h) | h | h
  · by_cases a : c = negInf
    · subst a; left; rw [canon_negInf]; exact ⟨Int.le_refl _, h2⟩
    · by_cases b : c = posInf
      · subst b; left; rw [canon_posInf]; exact ⟨h1, Int.le_refl _⟩
      · left; rw [canon_of_bounds ⟨by omega, by omega⟩]; exact ⟨h1, h2⟩
  · right; subst h; exact DuckDBSQL.canon_nan
  · left; subst h; rw [show canon negZero = 0 from fp64.canon_negZero]
    have := negInf_lt_zero; have := one_lt_posInf; have := zero_lt_one; omega
  · right; subst h; exact fp64.canon_negNan

/-- A measure over field 0: no filter, no order. -/
def SumGuard.meas (fn : AggFn) (arg : Expr := .field 0) : Measure := ⟨fn, arg, false, none, []⟩

theorem SumGuard.eval_plain (fn : AggFn)
    (hfn : fn ≠ .collect ∧ (∀ b, fn ≠ .pick b) ∧ (∀ s, fn ≠ .concat s) ∧ fn ≠ .mode)
    (vs : List Value) :
    Measure.eval (vs.map ([·])) (SumGuard.meas fn) = fn.apply (vs.filter (· != .null)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hfn
  cases fn <;> simp_all [SumGuard.meas, Measure.eval, Measure.inputs, Measure.kept, Expr.eval,
    List.map_map, Function.comp_def]

theorem SumGuard.arg_null : SumGuard.arg.eval [Value.null] = .null := by
  simp [SumGuard.arg, Expr.eval, DuckDBSQL.apply_lt_null_l, Value.isTrue]

theorem SumGuard.arg_float (c : Int) :
    SumGuard.arg.eval [Value.float c] = if canon c < posInf then .float c else .null := by
  by_cases h : canon c < posInf <;>
    simp [SumGuard.arg, Expr.eval, DuckDBSQL.apply_lt_float, canon_posInf, Value.isTrue, h]

theorem SumGuard.inputs_guard (vs : List Value) (hv : ∀ v ∈ vs, v = .null ∨ ∃ c, v = .float c) :
    ((vs.map ([·])).map fun row => SumGuard.arg.eval row).filter (· != .null) =
      (vs.filter (· != .null)).filter SumGuard.below := by
  rw [List.map_map]
  have : ∀ v ∈ vs, (fun row => SumGuard.arg.eval row) ∘ (fun x => [x]) = fun x => SumGuard.arg.eval [x] :=
    fun _ _ => rfl
  show (vs.map fun x => SumGuard.arg.eval [x]).filter (· != .null) = _
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have ih := ih (fun w hw => hv w (List.mem_cons_of_mem _ hw)) (fun _ _ => rfl)
    rcases hv v List.mem_cons_self with rfl | ⟨c, rfl⟩
    · simp [SumGuard.arg_null, ih]
    · by_cases h : canon c < posInf
      · simp [SumGuard.arg_float, SumGuard.below, h, ih]
      · simp [SumGuard.arg_float, SumGuard.below, h, ih]

theorem SumGuard.eval_guard (fn : AggFn)
    (hfn : fn ≠ .collect ∧ (∀ b, fn ≠ .pick b) ∧ (∀ s, fn ≠ .concat s) ∧ fn ≠ .mode)
    (vs : List Value) (hv : ∀ v ∈ vs, v = .null ∨ ∃ c, v = .float c) :
    Measure.eval (vs.map ([·])) (SumGuard.meas fn SumGuard.arg) =
      fn.apply ((vs.filter (· != .null)).filter SumGuard.below) := by
  obtain ⟨h1, h2, h3, h4⟩ := hfn
  rw [← SumGuard.inputs_guard vs hv]
  cases fn <;> simp_all [SumGuard.meas, Measure.eval, Measure.inputs, Measure.kept]

/-- The finishing expression over `(s, hi, lo)`. -/
def SumGuard.finish : Expr :=
  .ifThen (.bin .eq (.field 1) (.lit (.float nan))) (.lit (.float nan))
    (.ifThen (.bin .and (.bin .eq (.field 1) (.lit (.float posInf)))
        (.bin .eq (.field 2) (.lit (.float negInf)))) (.lit (.float nan))
      (.ifThen (.bin .eq (.field 1) (.lit (.float posInf))) (.lit (.float posInf)) (.field 0)))

theorem SumGuard.finish_eval (s : Value) (h l : Int) :
    SumGuard.finish.evalP Profile.reference [s, .float h, .float l] =
      .ok (if canon h = nan then .float nan
        else if canon h = posInf ∧ canon l = negInf then .float nan
        else if canon h = posInf then .float posInf else s) := by
  simp only [SumGuard.finish, Expr.evalP, List.getD_cons_zero, List.getD_cons_succ, Outcome.ok_bind,
    Lowering.ref_eq, Lowering.ref_and, DuckDBSQL.apply_eq_float, DuckDBSQL.canon_nan, canon_posInf,
    canon_negInf]
  by_cases a : canon h = nan <;> by_cases b : canon h = posInf <;> by_cases d : canon l = negInf <;>
    (try have hpn : posInf ≠ nan := fun e => a (b.trans e)) <;>
    simp_all [and3, Value.isTrue]

omit [Boxes.Ambient] in
theorem SumGuard.anyCode_iff (p : Int → Bool) (ws : List Value) :
    anyCode p ws = true ↔ ∃ c, Value.float c ∈ ws ∧ p (canon c) = true := by
  simp only [anyCode, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x <;> simp at h
    exact ⟨_, hx, h⟩
  · rintro ⟨c, hc, h⟩; exact ⟨_, hc, by simpa using h⟩

omit [Boxes.Ambient] in
theorem SumGuard.nonFinite_extremes (ws : List Value) (hw : ∀ w ∈ ws, ∃ c, w = .float c ∧ SumGuard.Valid c)
    (h l : Int) (hh : Value.float h ∈ ws) (hl : Value.float l ∈ ws)
    (hmax : ∀ x ∈ ws, x.le (.float h) = true) (hmin : ∀ x ∈ ws, (Value.float l).le x = true) :
    nonFinite ws =
      if canon h = nan then some nan
      else if canon h = posInf ∧ canon l = negInf then some nan
      else if canon h = posInf then some posInf
      else if canon l = negInf then some negInf else none := by
  have pn : posInf < nan := fp64.posInf_lt_nan
  have ni : negInf < posInf := by
    have h1 : negInf < 0 := fp64.negInf_lt_zero
    have h2 : 0 < posInf := fp64.zero_lt_posInf
    omega
  have vh := SumGuard.canon_valid (let ⟨c, hc, v⟩ := hw _ hh; by cases hc; exact v)
  have vl := SumGuard.canon_valid (let ⟨c, hc, v⟩ := hw _ hl; by cases hc; exact v)
  have le_h : ∀ c, Value.float c ∈ ws → canon c ≤ canon h := fun c hc => by
    have := hmax _ hc; rw [Value.le_float] at this; simpa using this
  have l_le : ∀ c, Value.float c ∈ ws → canon l ≤ canon c := fun c hc => by
    have := hmin _ hc; rw [Value.le_float] at this; simpa using this
  have c1 : (anyCode (fun c => decide (nan ≤ c)) ws = true) ↔ canon h = nan := by
    rw [SumGuard.anyCode_iff]
    constructor
    · rintro ⟨c, hc, h1⟩
      have := le_h c hc; simp only [decide_eq_true_eq] at h1; omega
    · intro e; exact ⟨h, hh, by simp [e]⟩
  have c2 : ¬ canon h = nan → ((anyCode (fun c => decide (posInf ≤ c ∧ c < nan)) ws = true) ↔
      canon h = posInf) := fun hn => by
    rw [SumGuard.anyCode_iff]
    constructor
    · rintro ⟨c, hc, h1⟩
      have := le_h c hc; simp only [decide_eq_true_eq] at h1; omega
    · intro e; exact ⟨h, hh, by simp [e, pn]⟩
  have c3 : (anyCode (fun c => decide (c ≤ negInf)) ws = true) ↔ canon l = negInf := by
    rw [SumGuard.anyCode_iff]
    constructor
    · rintro ⟨c, hc, h1⟩
      have := l_le c hc; simp only [decide_eq_true_eq] at h1; omega
    · intro e; exact ⟨l, hl, by simp [e]⟩
  unfold nonFinite
  by_cases a : canon h = nan
  · simp [c1.mpr a, a]
  · have a' : ¬ (anyCode (fun c => decide (nan ≤ c)) ws = true) := fun x => a (c1.mp x)
    have a'' : anyCode (fun c => decide (nan ≤ c)) ws = false := by simpa using a'
    simp only [a'', Bool.false_or, a, ↓reduceIte, Bool.and_eq_true]
    simp only [c2 a, c3]

theorem SumGuard.apply_nonFinite (f : AggFn) (hf : f = .fsum ∨ f = .avg) (ws : List Value)
    (h : ws ≠ []) (k : Int) (hk : nonFinite ws = some k) : f.apply ws = .float k := by
  cases ws with
  | nil => exact absurd rfl h
  | cons w ws =>
    rcases hf with rfl | rfl <;> simp [AggFn.apply, floatSumCR, floatAvgCR, hk]

theorem SumGuard.agree (f : AggFn) (hf : f = .fsum ∨ f = .avg) (vs : List Value)
    (hv : ∀ v ∈ vs, DuckType.double.Has v) :
    (SumGuard.finish.evalP Profile.reference
      [Measure.eval (vs.map ([·])) (SumGuard.meas f SumGuard.arg),
       Measure.eval (vs.map ([·])) (SumGuard.meas .max),
       Measure.eval (vs.map ([·])) (SumGuard.meas .min)]).Agree
      (.ok (f.apply (vs.filter (· != .null)))) := by
  have hfn : ∀ g : AggFn, (g = .fsum ∨ g = .avg ∨ g = .max ∨ g = .min) →
      g ≠ .collect ∧ (∀ b, g ≠ .pick b) ∧ (∀ s, g ≠ .concat s) ∧ g ≠ .mode := by
    intro g hg; rcases hg with rfl | rfl | rfl | rfl <;> simp
  have hvn : ∀ v ∈ vs, v = .null ∨ ∃ c, v = .float c := fun v hm => by
    have := hv v hm; cases v <;> simp_all [DuckType.Has]
  have hfn' := hfn f (by rcases hf with h | h <;> simp [h])
  rw [SumGuard.eval_guard f hfn' vs hvn, SumGuard.eval_plain .max (hfn _ (by simp)) vs,
    SumGuard.eval_plain .min (hfn _ (by simp)) vs]
  generalize hws : vs.filter (· != .null) = ws
  have hw : ∀ w ∈ ws, ∃ c, w = .float c ∧ SumGuard.Valid c := by
    intro w hmem; rw [← hws, List.mem_filter] at hmem; obtain ⟨hm, hne⟩ := hmem
    have := hv w hm; cases w <;> simp_all [DuckType.Has, SumGuard.Valid]
  by_cases hnil : ws = []
  · subst hnil
    rcases hf with rfl | rfl <;>
      simp [AggFn.apply, SumGuard.finish, Expr.evalP, Lowering.ref_eq, Outcome.ok_bind,
        DuckDBSQL.apply_eq_null_l, Lowering.ref_and, and3, Value.isTrue, Outcome.Agree]
  · obtain ⟨w0, ws', hcons⟩ := List.exists_cons_of_ne_nil hnil
    have hmx : AggFn.max.apply ws ∈ ws := by rw [hcons]; exact pickFold_mem _ w0 ws'
    have hmn : AggFn.min.apply ws ∈ ws := by rw [hcons]; exact pickFold_mem _ w0 ws'
    obtain ⟨h, hHeq, -⟩ := hw _ hmx
    obtain ⟨l, hLeq, -⟩ := hw _ hmn
    have hmax := (AggFn.apply_max (vs := ws) rfl (by rw [hHeq]; simp)).2
    have hmin := (AggFn.apply_min (vs := ws) rfl (by rw [hLeq]; simp)).2
    rw [hHeq] at hmax hmx; rw [hLeq] at hmin hmn
    have nf := SumGuard.nonFinite_extremes ws hw h l hmx hmn hmax hmin
    rw [hHeq, hLeq, SumGuard.finish_eval]
    simp only [Outcome.Agree]
    by_cases a : canon h = nan
    · have := SumGuard.apply_nonFinite f hf ws hnil nan (by rw [nf]; simp [a])
      simp [a, this]
    · by_cases b : canon h = posInf
      · by_cases d : canon l = negInf
        · have := SumGuard.apply_nonFinite f hf ws hnil nan (by rw [nf]; simp [b, d])
          simp [b, d, this]
        · have pn : posInf < nan := fp64.posInf_lt_nan
          have := SumGuard.apply_nonFinite f hf ws hnil posInf
            (by rw [nf]; simp [b, d, Int.ne_of_lt pn])
          simp [b, d, this, Int.ne_of_lt pn]
      · have pn : posInf < nan := fp64.posInf_lt_nan
        have vh := SumGuard.canon_valid (let ⟨c, hc, v⟩ := hw _ hmx; by cases hc; exact v)
        have hlt : canon h < posInf := by omega
        have : ws.filter SumGuard.below = ws := List.filter_eq_self.mpr fun x hx => by
          obtain ⟨c, rfl, -⟩ := hw x hx
          have := hmax _ hx; rw [Value.le_float] at this
          simp only [SumGuard.below, decide_eq_true_eq]; simp at this; omega
        simp [a, b, this]

theorem SumGuard.inputs_meas_guard (fn : AggFn) (vs : List Value)
    (hv : ∀ v ∈ vs, v = .null ∨ ∃ c, v = .float c) :
    (SumGuard.meas fn SumGuard.arg).inputs (vs.map ([·])) =
      (vs.filter (· != .null)).filter SumGuard.below := by
  rw [← SumGuard.inputs_guard vs hv]
  simp [SumGuard.meas, Measure.inputs, Measure.kept]

/-- **No measure of the entry has a domain error** on any group (`AggFn.makesNan`): the guarded one
has no `+∞` among its inputs, the others are not sums. Overflow to `±∞` is not a domain error. -/
theorem SumGuard.noNan (f : AggFn) (hf : f = .fsum ∨ f = .avg) (vs : List Value)
    (hv : ∀ v ∈ vs, DuckType.double.Has v) :
    ∀ m ∈ [SumGuard.meas f SumGuard.arg, SumGuard.meas .max, SumGuard.meas .min],
      m.fn.makesNan (m.inputs (vs.map ([·]))) = false := by
  have hvn : ∀ v ∈ vs, v = .null ∨ ∃ c, v = .float c := fun v hm => by
    have := hv v hm; cases v <;> simp_all [DuckType.Has]
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · rw [SumGuard.inputs_meas_guard f vs hvn]
    rcases hf with rfl | rfl <;>
      simp [SumGuard.meas, AggFn.makesNan, AggFn.nanCase, SumGuard.below, canon_posInf]
  · simp [SumGuard.meas, AggFn.makesNan, AggFn.nanCase]
  · simp [SumGuard.meas, AggFn.makesNan, AggFn.nanCase]

theorem SumGuard.noNan_all (f : AggFn) (hf : f = .fsum ∨ f = .avg) (vs : List Value)
    (hv : ∀ v ∈ vs, DuckType.double.Has v) :
    [SumGuard.meas f SumGuard.arg, SumGuard.meas .max, SumGuard.meas .min].all
      (fun m => !m.fn.makesNan (m.inputs (vs.map ([·])))) = true := by
  simp only [List.all_eq_true, Bool.not_eq_true']
  exact SumGuard.noNan f hf vs hv

/-- The reference's own entry: the plain measure, whose value is `AggFn.apply`. -/
theorem SumGuard.agree_plain (f : AggFn) (hf : f = .fsum ∨ f = .avg) (vs : List Value) :
    ((Expr.field 0).evalP Profile.reference
      [Measure.eval (vs.map ([·])) (SumGuard.meas f)]).Agree
      (.ok (f.apply (vs.filter (· != .null)))) := by
  have hfn : f ≠ .collect ∧ (∀ b, f ≠ .pick b) ∧ (∀ s, f ≠ .concat s) ∧ f ≠ .mode := by
    rcases hf with rfl | rfl <;> simp
  rw [SumGuard.eval_plain f hfn vs]
  simp [Expr.evalP, Outcome.Agree]

end
end Substrait
