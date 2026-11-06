import SubstraitLean.ObsEquiv

/-!
# Robust postconditions (#898)

A postcondition proved on the reference's result holds on an engine's result
equal to it up to the observation `q` when the condition cannot tell the two
apart: it is **robust** under `q` (`Expr.Robust`). This module gives a
decidable sufficient condition, `Expr.robustB`, and its theorem.

* A condition that reads only columns `q` observes exactly is robust
  (`Expr.robust_of_robustB`): equal columns give equal values
  (`Expr.eval_congr_cols`). `ObsCtx.colIgnores` names, per column, the components
  `q` ignores there: the checker reports them, as `CheckedCondition.ignores`
  reads them.
* A comparison of a tolerated double column with a constant is robust once
  the tolerance is folded into the constant (`Expr.narrow`): `x ≤ c` becomes
  `x ≤ c - t`, and `Expr.narrow_sound` proves that the narrowed condition on
  one result gives the original on every result equal to it up to `q`.
  Conjunctions and disjunctions narrow componentwise; `=` has no narrowing.

The tolerance is abstract here (`Shift.Sound`): a shift of the constant that
moves a comparison past every pair of codes equal up to `q`. `Shift.codes t`
is the one for a tolerance of `t` codes; the one for `|x - y| ≤ ε` over the
reals is proved in `float-bounds` (#899). -/

namespace Substrait

/-! ## The columns an expression reads -/

/-- The columns `e` reads; a lambda's body reads none of the row's. -/
def Expr.cols : Expr → List Nat
  | .lit _ => []
  | .field i => [i]
  | .un _ a => a.cols
  | .bin _ a b => a.cols ++ b.cols
  | .ifThen c t e => c.cols ++ t.cols ++ e.cols
  | .hof _ l _ => l.cols

/-- An expression's value depends only on the columns it reads. -/
theorem Expr.eval_congr_cols {r r' : Row} :
    ∀ e : Expr, (∀ i ∈ e.cols, r.getD i .null = r'.getD i .null) → e.eval r = e.eval r'
  | .lit _, _ => rfl
  | .field i, h => h i (List.mem_singleton_self i)
  | .un _ a, h => by simp only [Expr.eval, Expr.eval_congr_cols a h]
  | .bin _ a b, h => by
    simp only [Expr.cols, List.mem_append] at h
    simp only [Expr.eval, Expr.eval_congr_cols a fun i hi => h i (.inl hi),
      Expr.eval_congr_cols b fun i hi => h i (.inr hi)]
  | .ifThen c t e, h => by
    simp only [Expr.cols, List.mem_append] at h
    simp only [Expr.eval, Expr.eval_congr_cols c fun i hi => h i (.inl (.inl hi)),
      Expr.eval_congr_cols t fun i hi => h i (.inl (.inr hi)), Expr.eval_congr_cols e fun i hi => h i (.inr hi)]
  | .hof _ l _, h => by simp only [Expr.eval, Expr.eval_congr_cols l h]

/-! ## Columns observed exactly -/

/-- The components `q` ignores in column `col`: the order of a list's
elements, a string's normal form, a double's last bits, the sign of its zero,
a timestamp's digits, a decimal's scale (the model keeps one scale per
column, so `decimals` is named where `q` coarsens it, which is safe). -/
def ObsCtx.colIgnores (ctx : ObsCtx) (q : Obs) (col : Nat) : List String :=
  (if q.elements = .sequence then [] else ["elements"]) ++
  match ctx.kind col with
  | .double => (if q.floats = .exact then [] else ["floats"]) ++
      (if q.zeros = .exact then [] else ["zeros"])
  | .timestamp => if q.times = .exact then [] else ["timestamps"]
  | .string => if q.strings = .exact then [] else ["strings"]
  | .decimal => if q.decimals = .exact then [] else ["decimals"]
  | .other => []

/-- `q` observes column `col` exactly. -/
def ObsCtx.exactCol (ctx : ObsCtx) (q : Obs) (col : Nat) : Bool := (ctx.colIgnores q col).isEmpty

section
variable {q : Obs} {ctx : ObsCtx} {col : Nat}

theorem ObsCtx.exactCol_parts (h : ctx.exactCol q col = true) :
    q.elements = .sequence ∧ (∀ a b, IntEquiv q ctx col a b → a = b) ∧
      (∀ a b, StrEquiv q ctx col a b → a = b) := by
  unfold ObsCtx.exactCol ObsCtx.colIgnores at h
  by_cases he : q.elements = .sequence
  · simp only [he, ite_true, List.nil_append] at h
    refine ⟨he, fun a b e => ?_, fun x y e => ?_⟩
    · unfold IntEquiv at e
      cases hk : ctx.kind col <;> simp only [hk] at h e
      · by_cases hf : q.floats = .exact <;> by_cases hz : q.zeros = .exact <;>
          simp_all [Obs.zeroNorm]
      · by_cases ht : q.times = .exact <;> simp_all
      all_goals exact e
    · unfold StrEquiv Obs.stringsAt at e
      by_cases hk : ctx.kind col = .string
      · simp only [hk, ite_true] at e h
        by_cases hs : q.strings = .exact
        · simp only [hs, StrEquivAt] at e; exact e
        · simp [hs] at h
      · simp only [hk, ite_false, StrEquivAt] at e; exact e
  · simp [he] at h

mutual
theorem Value.Equiv.eq_of_exactCol (h : ctx.exactCol q col = true) :
    ∀ a b, Value.Equiv q ctx col a b → a = b
  | .null, .null, _ => rfl
  | .bool _, .bool _, e => congrArg _ e
  | .int _, .int _, e => congrArg _ ((ObsCtx.exactCol_parts h).2.1 _ _ e)
  | .str _, .str _, e => congrArg _ ((ObsCtx.exactCol_parts h).2.2 _ _ e)
  | .list as, .list bs, e => by
    have hl := (ObsCtx.exactCol_parts h).1
    unfold Value.Equiv at e; simp only [hl] at e
    exact congrArg _ (Value.EquivList.eq_of_exactCol h as bs e)
  | .null, .bool _, e | .null, .int _, e | .null, .str _, e | .null, .list _, e
  | .bool _, .null, e | .bool _, .int _, e | .bool _, .str _, e | .bool _, .list _, e
  | .int _, .null, e | .int _, .bool _, e | .int _, .str _, e | .int _, .list _, e
  | .str _, .null, e | .str _, .bool _, e | .str _, .int _, e | .str _, .list _, e
  | .list _, .null, e | .list _, .bool _, e | .list _, .int _, e | .list _, .str _, e => e.elim

theorem Value.EquivList.eq_of_exactCol (h : ctx.exactCol q col = true) :
    ∀ as bs, Value.EquivList q ctx col as bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, ⟨e, t⟩ => by
    rw [Value.Equiv.eq_of_exactCol h a b e, Value.EquivList.eq_of_exactCol h as bs t]
  | [], _ :: _, e | _ :: _, [], e => e.elim
end

end

/-! ## Robust conditions -/

/-- **`e` is robust under `q`**: TRUE on a row stays TRUE on any row equal to
it up to `q`. -/
def Expr.Robust (q : Obs) (ctx : ObsCtx) (e : Expr) : Prop :=
  ∀ r r', Row.Equiv q ctx r r' → (e.eval r).isTrue = true → (e.eval r').isTrue = true

/-- Columns equal up to `q`, by position. -/
theorem Row.Equiv.getD {q : Obs} {ctx : ObsCtx} {r r' : Row} (h : Row.Equiv q ctx r r') (i : Nat) :
    Value.Equiv q ctx i (r.getD i .null) (r'.getD i .null) := by
  simpa using Row.EquivFrom.getD h i

/-- A comparison of a column with a constant: `x < c`, `x ≤ c`, `x > c`,
`x ≥ c`, as the parser writes them. -/
inductive Cmp | lt | le | gt | ge
  deriving Repr, DecidableEq

def Cmp.expr (k : Cmp) (i : Nat) (c : Int) : Expr :=
  match k with
  | .lt => .bin .lt (.field i) (.lit (.int c))
  | .gt => .bin .lt (.lit (.int c)) (.field i)
  | .le => .un .not (.bin .lt (.lit (.int c)) (.field i))
  | .ge => .un .not (.bin .lt (.field i) (.lit (.int c)))

/-- When the comparison holds of the integer `a`. -/
def Cmp.holds (k : Cmp) (a c : Int) : Prop :=
  match k with
  | .lt => a < c | .le => a ≤ c | .gt => c < a | .ge => c ≤ a

theorem BinFn.apply_lt_int (a b : Int) : BinFn.apply .lt (.int a) (.int b) = .bool (decide (a < b)) :=
  rfl

theorem UnFn.apply_not_bool (b : Bool) : UnFn.apply .not (.bool b) = .bool (!b) := rfl

/-- A comparison is TRUE exactly on an integer that satisfies it. -/
theorem Cmp.eval_isTrue (k : Cmp) (i : Nat) (c : Int) (r : Row) :
    ((k.expr i c).eval r).isTrue = true ↔ ∃ a, r.getD i .null = .int a ∧ k.holds a c := by
  generalize hv : r.getD i .null = v
  have e : (k.expr i c).eval r = match k with
      | .lt => BinFn.apply .lt v (.int c) | .gt => BinFn.apply .lt (.int c) v
      | .le => UnFn.apply .not (BinFn.apply .lt (.int c) v)
      | .ge => UnFn.apply .not (BinFn.apply .lt v (.int c)) := by
    cases k <;> simp only [Cmp.expr, Expr.eval, hv]
  rw [e]
  cases k <;> cases v
  all_goals first
    | (simp only [BinFn.apply_lt_int, UnFn.apply_not_bool, Cmp.holds, Value.int.injEq,
        exists_eq_left']
       rename_i x
       by_cases h1 : x < c <;> by_cases h2 : c < x <;> simp [Value.isTrue, h1, h2] <;> omega)
    | exact ⟨fun h => (by cases h), fun ⟨_, h, _⟩ => (by cases h)⟩

/-- The comparison `e` is, if it is one. -/
def Expr.cmp? : Expr → Option (Cmp × Nat × Int)
  | .bin .lt (.field i) (.lit (.int c)) => some (.lt, i, c)
  | .bin .lt (.lit (.int c)) (.field i) => some (.gt, i, c)
  | .un .not (.bin .lt (.lit (.int c)) (.field i)) => some (.le, i, c)
  | .un .not (.bin .lt (.field i) (.lit (.int c))) => some (.ge, i, c)
  | _ => none

theorem Expr.cmp?_spec {e : Expr} {k : Cmp} {i : Nat} {c : Int} (h : e.cmp? = some (k, i, c)) :
    e = k.expr i c := by
  unfold Expr.cmp? at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

/-- How a comparison with a constant is narrowed on one column: below with
`down` (`x < c`, `x ≤ c`), above with `up` (`x > c`, `x ≥ c`). -/
structure Shift where
  down : Int → Int
  up : Int → Int

def Cmp.shift (k : Cmp) (s : Shift) (c : Int) : Int :=
  match k with
  | .lt | .le => s.down c
  | .gt | .ge => s.up c

/-- **The shift is sound for column `col` under `q`**: a comparison that
holds of `a` against the shifted constant holds of every `b` equal to `a` up
to `q` against the constant. -/
def Shift.Sound (q : Obs) (ctx : ObsCtx) (col : Nat) (s : Shift) : Prop :=
  ∀ (k : Cmp) (a b c : Int), IntEquiv q ctx col a b → k.holds a (k.shift s c) → k.holds b c

/-- A tolerance of `t` codes: the constant moves by `t`. -/
def Shift.codes (t : Nat) : Shift := ⟨fun c => c - t, fun c => c + t⟩

theorem Shift.codes_sound {q : Obs} {ctx : ObsCtx} {col t : Nat}
    (h : ∀ a b, IntEquiv q ctx col a b → (a - b).natAbs ≤ t) : (Shift.codes t).Sound q ctx col := by
  intro k a b c e hk
  have := h a b e
  cases k <;> simp only [Cmp.holds, Cmp.shift, Shift.codes] at hk ⊢ <;> omega

/-- A comparison narrowed by the shift of its column, if it has one;
anything else as it is. -/
def Expr.narrowCmp (sh : Nat → Option Shift) (e : Expr) : Expr :=
  match e.cmp? with
  | some (k, i, c) => match sh i with
    | some s => k.expr i (k.shift s c)
    | none => e
  | none => e

/-- **`e` narrowed by the shifts**: each comparison of a column with a
constant under `AND` and `OR` moved inward by its column's shift. -/
def Expr.narrow (sh : Nat → Option Shift) : Expr → Expr
  | .bin f a b => if f = .and ∨ f = .or then .bin f (a.narrow sh) (b.narrow sh)
      else (Expr.bin f a b).narrowCmp sh
  | .lit v => (Expr.lit v).narrowCmp sh
  | .field i => (Expr.field i).narrowCmp sh
  | .un f a => (Expr.un f a).narrowCmp sh
  | .ifThen c t e => (Expr.ifThen c t e).narrowCmp sh
  | .hof f l b => (Expr.hof f l b).narrowCmp sh

/-- What `robustB` asks of a leaf: a comparison whose column has a shift,
or columns observed exactly. -/
def Expr.leafRobustB (q : Obs) (ctx : ObsCtx) (sh : Nat → Option Shift) (e : Expr) : Bool :=
  (match e.cmp? with
    | some (_, i, _) => (sh i).isSome
    | none => false) || e.cols.all (ctx.exactCol q)

/-- **A decidable sufficient condition for robustness**: under `AND` and
`OR`, each part is a comparison its column's shift narrows, or reads only
columns `q` observes exactly. -/
def Expr.robustB (q : Obs) (ctx : ObsCtx) (sh : Nat → Option Shift) : Expr → Bool
  | .bin f a b => if f = .and ∨ f = .or then a.robustB q ctx sh && b.robustB q ctx sh
      else (Expr.bin f a b).leafRobustB q ctx sh
  | .lit v => (Expr.lit v).leafRobustB q ctx sh
  | .field i => (Expr.field i).leafRobustB q ctx sh
  | .un f a => (Expr.un f a).leafRobustB q ctx sh
  | .ifThen c t e => (Expr.ifThen c t e).leafRobustB q ctx sh
  | .hof f l b => (Expr.hof f l b).leafRobustB q ctx sh

section
variable {q : Obs} {ctx : ObsCtx} {sh : Nat → Option Shift}

/-- The leaves. -/
theorem Expr.narrowCmp_sound (hsh : ∀ i s, sh i = some s → s.Sound q ctx i) {e : Expr}
    (hb : e.leafRobustB q ctx sh = true) {r r' : Row} (hr : Row.Equiv q ctx r r')
    (ht : ((e.narrowCmp sh).eval r).isTrue = true) : (e.eval r').isTrue = true := by
  have hexact : e.cols.all (ctx.exactCol q) = true → (e.eval r').isTrue = true := fun hx => by
    have : e.narrowCmp sh = e ∨ e.cmp?.isSome := by
      unfold Expr.narrowCmp; split
      · next k i c hc => right; simp [hc]
      · left; rfl
    have heq : e.eval r = e.eval r' := Expr.eval_congr_cols e fun i hi =>
      Value.Equiv.eq_of_exactCol (List.all_eq_true.1 hx i hi) _ _ (hr.getD i)
    rcases this with h | h
    · rw [h, heq] at ht; exact ht
    · -- A comparison with a shift: sound below; without one: unchanged.
      obtain ⟨⟨k, i, c⟩, hc⟩ := Option.isSome_iff_exists.1 h
      cases hs : sh i with
      | none => simp only [Expr.narrowCmp, hc, hs] at ht; rw [← heq]; exact ht
      | some s =>
        simp only [Expr.narrowCmp, hc, hs] at ht
        rw [Expr.cmp?_spec hc] at heq ⊢
        obtain ⟨a, ha, hk⟩ := (Cmp.eval_isTrue k i _ r).1 ht
        have hv := hr.getD i
        rw [ha] at hv
        generalize hb' : r'.getD i .null = v at hv
        cases v <;> try exact hv.elim
        exact (Cmp.eval_isTrue k i c r').2 ⟨_, hb', hsh i s hs k a _ c hv hk⟩
  unfold Expr.leafRobustB at hb
  cases hc : e.cmp? with
  | none => simp only [hc, Bool.false_or] at hb; exact hexact hb
  | some p =>
    obtain ⟨k, i, c⟩ := p
    simp only [hc] at hb
    cases hs : sh i with
    | none => simp only [hs, Option.isSome_none, Bool.false_or] at hb; exact hexact hb
    | some s =>
      simp only [Expr.narrowCmp, hc, hs] at ht
      rw [Expr.cmp?_spec hc]
      obtain ⟨a, ha, hk⟩ := (Cmp.eval_isTrue k i _ r).1 ht
      have hv := hr.getD i
      rw [ha] at hv
      generalize hb' : r'.getD i .null = v at hv
      cases v <;> try exact hv.elim
      exact (Cmp.eval_isTrue k i c r').2 ⟨_, hb', hsh i s hs k a _ c hv hk⟩

/-- **Narrowing is sound**: where the narrowed condition is TRUE on a row,
the original is TRUE on every row equal to it up to `q`. -/
theorem Expr.narrow_sound (hsh : ∀ i s, sh i = some s → s.Sound q ctx i) :
    ∀ (e : Expr), e.robustB q ctx sh = true → ∀ {r r' : Row}, Row.Equiv q ctx r r' →
      ((e.narrow sh).eval r).isTrue = true → (e.eval r').isTrue = true
  | .bin f a b, hb, r, r', hr, ht => by
    unfold Expr.robustB at hb; unfold Expr.narrow at ht
    by_cases hf : f = .and ∨ f = .or
    · simp only [hf, ite_true, Bool.and_eq_true] at hb ht
      rcases hf with rfl | rfl
      · simp only [Expr.eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht ⊢
        exact ⟨Expr.narrow_sound hsh a hb.1 hr ht.1, Expr.narrow_sound hsh b hb.2 hr ht.2⟩
      · simp only [Expr.eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht ⊢
        exact ht.imp (Expr.narrow_sound hsh a hb.1 hr) (Expr.narrow_sound hsh b hb.2 hr)
    · simp only [hf, ite_false] at hb ht
      exact Expr.narrowCmp_sound hsh hb hr ht
  | .lit _, hb, _, _, hr, ht | .field _, hb, _, _, hr, ht | .un _ _, hb, _, _, hr, ht
  | .ifThen _ _ _, hb, _, _, hr, ht | .hof _ _ _, hb, _, _, hr, ht =>
    Expr.narrowCmp_sound hsh hb hr ht

theorem Expr.narrowCmp_none (e : Expr) : e.narrowCmp (fun _ => none) = e := by
  unfold Expr.narrowCmp; split <;> rfl

theorem Expr.narrow_none : ∀ e : Expr, e.narrow (fun _ => none) = e
  | .bin f a b => by
    unfold Expr.narrow
    split
    · rw [Expr.narrow_none a, Expr.narrow_none b]
    · exact Expr.narrowCmp_none _
  | .lit _ | .field _ | .un _ _ | .ifThen _ _ _ | .hof _ _ _ => Expr.narrowCmp_none _

/-- **`robustB` without shifts proves robustness.** -/
theorem Expr.robust_of_robustB {e : Expr} (h : e.robustB q ctx (fun _ => none) = true) :
    e.Robust q ctx := fun _ _ hr ht =>
  Expr.narrow_sound (sh := fun _ => none) (fun _ _ h => nomatch h) e h hr
    (by rw [Expr.narrow_none]; exact ht)

end

/-! ## For the checker -/

/-- The components `q` ignores in the columns `e` reads: empty exactly when
`e` reads only columns `q` observes exactly, which makes it robust. -/
def Expr.ignores (q : Obs) (ctx : ObsCtx) (e : Expr) : List String :=
  e.cols.flatMap (ctx.colIgnores q)

theorem Expr.robust_of_ignores {q : Obs} {ctx : ObsCtx} {e : Expr} (h : e.ignores q ctx = []) :
    e.Robust q ctx := by
  apply Expr.robust_of_robustB
  have hall : e.cols.all (ctx.exactCol q) = true := by
    simp only [Expr.ignores, List.flatMap_eq_nil_iff] at h
    simpa [ObsCtx.exactCol, List.all_eq_true] using h
  have leaf : ∀ e : Expr, e.cols.all (ctx.exactCol q) = true →
      e.leafRobustB q ctx (fun _ => none) = true := fun e h => by
    simp [Expr.leafRobustB, h]
  clear h
  induction e with
  | bin f a b iha ihb =>
    unfold Expr.robustB
    split
    · simp only [Expr.cols, List.all_append, Bool.and_eq_true] at hall
      simp [iha hall.1, ihb hall.2]
    · exact leaf _ hall
  | lit _ | field _ | un _ _ | ifThen _ _ _ | hof _ _ _ => exact leaf _ hall

/-- The components that could tell two values of column `col` apart, whatever
the observation: the ones `colIgnores` names when the observation coarsens
them. Observation-free, so the checker reports it once and the caller
intersects it with the components its observation ignores
(`Expr.ignores_eq_filter`). -/
def ObsCtx.colDepends (ctx : ObsCtx) (col : Nat) : List String :=
  "elements" :: match ctx.kind col with
  | .double => ["floats", "zeros"]
  | .timestamp => ["timestamps"]
  | .string => ["strings"]
  | .decimal => ["decimals"]
  | .other => []

/-- Does `q` coarsen the component? -/
def Obs.coarsens (q : Obs) : String → Bool
  | "elements" => q.elements != .sequence
  | "floats" => q.floats != .exact
  | "zeros" => q.zeros != .exact
  | "timestamps" => q.times != .exact
  | "strings" => q.strings != .exact
  | "decimals" => q.decimals != .exact
  | _ => false

/-- The components the values `e` reads depend on. -/
def Expr.depends (ctx : ObsCtx) (e : Expr) : List String := e.cols.flatMap ctx.colDepends

theorem ObsCtx.colIgnores_eq (ctx : ObsCtx) (q : Obs) (col : Nat) :
    ctx.colIgnores q col = (ctx.colDepends col).filter q.coarsens := by
  unfold ObsCtx.colIgnores ObsCtx.colDepends
  cases ctx.kind col <;>
    simp only [List.filter_cons, List.filter_nil, Obs.coarsens, bne_iff_ne, ne_eq] <;>
    by_cases q.elements = .sequence <;> simp_all <;> split <;> simp_all <;> split <;> simp_all

theorem Expr.ignores_eq_filter (q : Obs) (ctx : ObsCtx) (e : Expr) :
    e.ignores q ctx = (e.depends ctx).filter q.coarsens := by
  simp only [Expr.ignores, Expr.depends, List.filter_flatMap]
  congr 1; funext c; exact ctx.colIgnores_eq q c

/-- **What the checker reports is enough**: a condition none of whose
components the observation coarsens is robust under it. -/
theorem Expr.robust_of_depends {q : Obs} {ctx : ObsCtx} {e : Expr}
    (h : (e.depends ctx).all (!q.coarsens ·) = true) : e.Robust q ctx := by
  apply Expr.robust_of_ignores
  rw [Expr.ignores_eq_filter, List.filter_eq_nil_iff]
  simpa [List.all_eq_true] using h

/-! ## Examples -/

/-- `x ≤ 100` on a double column within 3 codes, narrowed to `x ≤ 97`. -/
example : (Expr.un .not (.bin .lt (.lit (.int 100)) (.field 0))).narrow
    (fun i => if i = 0 then some (Shift.codes 3) else none) =
    .un .not (.bin .lt (.lit (.int 97)) (.field 0)) := by
  simp [Expr.narrow, Expr.narrowCmp, Expr.cmp?, Cmp.expr, Cmp.shift, Shift.codes]

/-- A condition on a string column depends on the strings' normal form under
`strings := .nfc`; one on an integer column does not. -/
example : (Expr.bin .eq (.field 0) (.lit (.str "é"))).ignores { strings := .nfc }
    { kind := fun i => if i = 0 then .string else .other } = ["strings"] := by
  decide

example : (Expr.bin .lt (.field 1) (.lit (.int 3))).ignores { strings := .nfc }
    { kind := fun i => if i = 0 then .string else .other } = [] := by
  decide

end Substrait
