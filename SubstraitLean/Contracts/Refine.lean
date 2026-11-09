import SubstraitLean.Contracts.TransferSound

/-!
# Contracts: Refine

Refinement by filter conditions: constant decimals, `Expr.refine` and
`Expr.refine_sound`, what a condition says about one expression (`Cstr`),
alternatives (#702) and whole conditions on a row (#597).

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

/-! ## Constant decimals

A decimal constant is its unscaled integer under `UnFn.decimal`, possibly
brought to another scale by `Parse.upscale` (`· 10ᵏ`): `0.05` compared with a
`DECIMAL(15, 4)` column is `DECIMAL_3_2(5) * 100`. The refinements below
recognize integer literals, so conditions are first written with such
constants folded (`Expr.normConst`, #27). -/

/-- The number a constant decimal expression evaluates to: a literal, a
decimal's type on one, or a product of two (`Parse.upscale`). -/
def Expr.constNum? : Expr → Option Value
  | .lit v => if v.numOf?.isSome then some v else none
  | .un (.decimal _ s) a | .un (.dkind _ s) a =>
    a.constNum?.bind fun v => v.unscaled?.map (.dec s)
  | .bin .dmul a b => a.constNum?.bind fun x => b.constNum?.bind fun y =>
    x.unscaled?.bind fun i => y.unscaled?.map fun j => .int (i * j)
  | _ => none

variable [Boxes.Ambient]
theorem Expr.constNum?_eval (row : Row) :
    ∀ (e : Expr) {v : Value}, e.constNum? = some v → e.eval row = v := by
  intro e
  induction e with
  | lit w => intro v h; simp only [Expr.constNum?] at h; split at h <;> simp_all [Expr.eval]
  | field => intro v h; simp [Expr.constNum?] at h
  | un f a ih =>
    intro v h
    cases f
    case decimal p s | dkind p s =>
      simp only [Expr.constNum?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, i, hi, rfl⟩ := h
      simp only [Expr.eval, ih hw, UnFn.apply, hi]
    all_goals simp [Expr.constNum?] at h
  | bin f a b iha ihb =>
    intro v h
    cases f
    case dmul =>
      simp only [Expr.constNum?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, y, hy, i, hi, j, hj, rfl⟩ := h
      simp only [Expr.eval, iha hx, ihb hy, BinFn.apply, hi, hj]
    all_goals simp [Expr.constNum?] at h
  | ifThen => intro v h; simp [Expr.constNum?] at h
  | hof => intro v h; simp [Expr.constNum?] at h

/-- `e` with its constant decimals folded to literals. -/
def Expr.normConst : Expr → Expr
  | .un f a => match (Expr.un f a).constNum? with
    | some v => .lit v
    | none => .un f a.normConst
  | .bin f a b => match (Expr.bin f a b).constNum? with
    | some v => .lit v
    | none => .bin f a.normConst b.normConst
  | .ifThen c t e => .ifThen c.normConst t.normConst e.normConst
  | e => e

theorem Expr.eval_normConst (row : Row) : ∀ e : Expr, e.normConst.eval row = e.eval row := by
  intro e
  induction e with
  | un f a ih =>
    simp only [Expr.normConst]
    split
    · rename_i v hv; rw [Expr.constNum?_eval row _ hv]; rfl
    · simp [Expr.eval, ih]
  | bin f a b iha ihb =>
    simp only [Expr.normConst]
    split
    · rename_i v hv; rw [Expr.constNum?_eval row _ hv]; rfl
    · simp [Expr.eval, iha, ihb]
  | ifThen c t e ihc iht ihe => simp [Expr.normConst, Expr.eval, ihc, iht, ihe]
  | lit | field | hof => rfl

/-! ## Refinement by filter conditions -/

/-- A column known to be a non-NULL number of kind `k`, with its interval
transformed. -/
def AVal.nonNullNum (k : NumKind) (a : AVal) (f : Bound → Bound) : AVal :=
  { int := a.int.map f, nk := some k }

/-- `a` without NULL: what an operand of a TRUE `<` can be. -/
def AVal.nonNullOrd (a : AVal) : AVal := { a with null := false }

/-- A number, a string, a boolean, a list or a struct: what `<` compares. -/
def Value.isOrd : Value → Bool
  | .null => false
  | _ => true

/-- The strings both lists allow. -/
def meetStrs : Option (List String) → Option (List String) → Option (List String)
  | some l, some m => some (l.filter m.contains)
  | some l, none => some l
  | none, m => m

omit [Boxes.Ambient] in
theorem meetStrs_mem {x y : Option (List String)} {s : String} (hx : x.all (·.contains s) = true)
    (hy : y.all (·.contains s) = true) : (meetStrs x y).all (·.contains s) = true := by
  cases x <;> cases y <;> simp_all [meetStrs]

/-- What a value known to equal (SQL `=`, so non-NULL) a value in `b` can be. -/
def AVal.meetEq (a b : AVal) : AVal :=
  { int := (match a.int, b.int with | some x, some y => some (x.meet y) | _, _ => none),
    tt := a.tt && b.tt, ff := a.ff && b.ff, str := a.str && b.str, strs := meetStrs a.strs b.strs,
    nk := a.nk.orElse fun _ => b.nk, list := a.list && b.list, elems := a.elems,
    card := a.card.meet b.card, struct := a.struct && b.struct, fields := a.fields }

omit [Boxes.Ambient] in
theorem AVal.meetEq_mem {a b : AVal} {v : Value} (ha : a.Mem v) (hb : b.Mem v) (hn : v ≠ .null) :
    (a.meetEq b).Mem v := by
  rcases AVal.mem_cases ha with ⟨rfl, _⟩ | ⟨k, i, x, rfl, hx, hxi, hk⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
    ⟨s, rfl, h⟩ | ⟨_, rfl | rfl, h⟩
  · exact absurd rfl hn
  · obtain ⟨y, hy, hyi, hk'⟩ := AVal.mem_val.mp hb
    rw [AVal.mem_val]
    refine ⟨x.meet y, by simp [AVal.meetEq, hx, hy], Bound.mem_meet hxi hyi, ?_⟩
    cases ha : a.nk <;> simp_all [AVal.meetEq]
  · simp_all [AVal.Mem, AVal.meetEq]
  · simp_all [AVal.Mem, AVal.meetEq]
  · simp_all [AVal.Mem, AVal.meetEq]
    exact meetStrs_mem h.2 hb.2
  · exact ⟨by simp [AVal.meetEq, ha.1, hb.1], Bound.mem_meet ha.2.1 hb.2.1, ha.2.2⟩
  · exact ⟨by simp [AVal.meetEq, ha.1, hb.1], ha.2⟩

/-- A value known to be the string `k` (#708). -/
def AVal.strIs (k : String) (a : AVal) : AVal :=
  { str := a.str, strs := meetStrs a.strs (some [k]) }

/-- A value known not to be the string `k`. -/
def AVal.strNot (k : String) (a : AVal) : AVal := { a with strs := a.strs.map (·.filter (· != k)) }

omit [Boxes.Ambient] in
theorem AVal.strIs_mem {a : AVal} {k : String} (h : a.Mem (.str k)) : (a.strIs k).Mem (.str k) := by
  simp only [AVal.Mem, AVal.MemR, AVal.strIs, Bool.and_eq_true] at *
  exact ⟨h.1, meetStrs_mem h.2 (by simp)⟩

omit [Boxes.Ambient] in
theorem AVal.strNot_mem {a : AVal} {k : String} {v : Value} (h : a.Mem v)
    (hv : ∀ s, v = .str s → s ≠ k) : (a.strNot k).Mem v := by
  cases v with
  | str s =>
      have := hv s rfl
      cases hA : a.strs <;> simp_all [AVal.Mem, AVal.strNot]
  | bool b => cases b <;> simp_all [AVal.Mem, AVal.strNot]
  | _ => simp_all [AVal.Mem, AVal.strNot, AVal.MemNum]

def refineCol (env : List AVal) (i : Nat) (f : AVal → AVal) : List AVal :=
  env.set i (f (env.getD i AVal.top))

/-- A column compared with the number `w`: of `w`'s kind, its interval
narrowed by `f` of `w`'s integer. -/
def refineNum (env : List AVal) (i : Nat) (w : Value) (f : Int → Bound → Bound) : List AVal :=
  match w.numOf? with
  | some (k, c) => refineCol env i (·.nonNullNum k (f (k.norm c)))
  | none => env

/-- A non-NULL list of `a`'s, its elements in `e` and its length in `card` (#925). -/
def AVal.listIn (a : AVal) (e : Option AVal) (card : Bound) : AVal := { list := a.list, elems := e, card }

/-- A column whose `cardinality` is compared with the integer `w`: a non-NULL
list, its length narrowed by `f` of `w` (#925). -/
def refineCard (env : List AVal) (i : Nat) (w : Value) (f : Int → Bound → Bound) : List AVal :=
  match w with
  | .int c => refineCol env i fun a => a.listIn a.elems (f c a.card)
  | _ => env

/-- A column whose `abs` is compared with the double `w`: a non-NULL double,
its code within `-c` and `c`, inclusive unless `strict`. -/
def refineAbs (env : List AVal) (i : Nat) (w : Value) (strict : Bool) : List AVal :=
  match w with
  | .float c =>
    let c := FloatCode.canon c
    refineCol env i
      (·.nonNullNum .float (·.meet (if strict then ⟨some (-c + 1), some (c - 1)⟩ else ⟨some (-c), some c⟩)))
  | _ => env

/-- What a row that makes `e` TRUE satisfies, for constants that are number
literals (`Expr.refine` folds the others first). Recognizes conjunctions,
disjunctions, comparisons of a column with a constant, `IS NULL` and
`IS NOT NULL`. A comparison is TRUE only of numbers of one kind (#923), so
a column compared with a number has the number's kind. -/
def Expr.refineL (env : List AVal) : Expr → List AVal
  | .bin .and p q => q.refineL (p.refineL env)
  -- A string column equal to a constant, or not (#708).
  | .bin .eq (.field i) (.lit (.str k)) => refineCol env i (AVal.strIs k)
  | .un .not (.bin .eq (.field i) (.lit (.str k))) => refineCol env i (AVal.strNot k)
  | .bin .lt (.field i) (.lit w) => refineNum env i w fun c => (·.atMost (c - 1))
  | .bin .lt (.lit w) (.field i) => refineNum env i w fun c => (·.atLeast (c + 1))
  | .un .not (.bin .lt (.field i) (.lit w)) => refineNum env i w fun c => (·.atLeast c)
  | .un .not (.bin .lt (.lit w) (.field i)) => refineNum env i w fun c => (·.atMost c)
  | .bin .eq (.field i) (.lit w) => refineNum env i w fun c _ => .exact c
  | .un .not (.un .isNull (.field i)) => refineCol env i fun a => { a with null := false }
  | .bin .eq (.field i) (.field j) =>
      let ai := env.getD i AVal.top
      let aj := env.getD j AVal.top
      refineCol (refineCol env i (·.meetEq aj)) j (·.meetEq ai)
  -- `x <> k` is TRUE only for a non-NULL number `x` of `k`'s kind.
  | .un .not (.bin .eq (.field i) (.lit w)) => refineNum env i w fun _ b => b
  -- Comparing two columns: TRUE only if both are non-NULL.
  | .bin .lt (.field i) (.field j) | .un .not (.bin .lt (.field i) (.field j)) =>
      refineCol (refineCol env i AVal.nonNullOrd) j AVal.nonNullOrd
  -- Arithmetic is NULL-propagating: a non-NULL `a - b` has non-NULL operands
  -- (DataFusion inlines computed columns such as `gap = ts - prev_ts`).
  | .un .not (.un .isNull (.bin .add a b)) =>
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  | .un .not (.un .isNull (.bin .sub a b)) =>
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  | .un .not (.un .isNull (.bin .mul a b)) =>
      (Expr.un .not (.un .isNull b)).refineL ((Expr.un .not (.un .isNull a)).refineL env)
  -- `p OR q` (e.g. `x IN (1, 2)`): what `p` gives, or what `q` gives.
  | .bin .or p q => List.zipWith AVal.join (p.refineL env) (q.refineL env)
  -- `x IS NULL`: only NULL (so `x IS NULL OR x >= 0` keeps the bound).
  | .un .isNull (.field i) => refineCol env i fun a => { null := a.null }
  -- `NOT (p OR q)`: neither is TRUE, so `x NOT IN ('a', 'b')` leaves the others.
  | .un .not (.bin .or p q) => (Expr.un .not q).refineL ((Expr.un .not p).refineL env)
  -- A list's length compared with an integer (#925).
  | .bin .lt (.un .cardinality (.field i)) (.lit w) => refineCard env i w fun c => (·.atMost (c - 1))
  | .bin .lt (.lit w) (.un .cardinality (.field i)) => refineCard env i w fun c => (·.atLeast (c + 1))
  | .un .not (.bin .lt (.un .cardinality (.field i)) (.lit w)) =>
      refineCard env i w fun c => (·.atLeast c)
  | .un .not (.bin .lt (.lit w) (.un .cardinality (.field i))) =>
      refineCard env i w fun c => (·.atMost c)
  -- `all_match(l, x -> b)` is TRUE: `l` is a list whose every element makes
  -- `b` TRUE, so what `b` says of its parameter holds of the elements (#925).
  | .hof .allMatch (.field i) b =>
      let a := env.getD i AVal.top
      refineCol env i fun _ => a.listIn (some ((b.refineL (a.elemsOf :: env)).getD 0 AVal.top)) a.card
  -- `abs(x) < c` and `abs(x) <= c` of a double, as the parser writes `abs`
  -- (`CASE WHEN x < 0.0 THEN -x ELSE x END`): `x` within `-c` and `c`.
  | .bin .lt (.ifThen (.bin .lt (.field i) (.lit (.float 0))) (.un .fneg (.field j)) (.field k))
      (.lit w) => if i = j ∧ i = k then refineAbs env i w true else env
  | .un .not (.bin .lt (.lit w)
      (.ifThen (.bin .lt (.field i) (.lit (.float 0))) (.un .fneg (.field j)) (.field k))) =>
      if i = j ∧ i = k then refineAbs env i w false else env
  | _ => env
termination_by e => sizeOf e

omit [Boxes.Ambient] in
theorem getD_top_eq (env : List AVal) (j : Nat) : env.getD j AVal.top = (env[j]?).getD AVal.top :=
  List.getD_eq_getElem?_getD

omit [Boxes.Ambient] in
theorem refineCol_sound {env : List AVal} {row : Row} {i : Nat} {f : AVal → AVal}
    (h : EnvMem env row) (hf : (f (env.getD i AVal.top)).Mem (row.getD i .null)) :
    EnvMem (refineCol env i f) row := by
  intro j
  have hj := h j
  simp only [refineCol, getD_top_eq, List.getElem?_set] at *
  by_cases hij : i = j
  · subst hij
    by_cases hlen : i < env.length
    · simpa [hlen] using hf
    · simpa [hlen] using hj
  · simpa [hij] using hj

omit [Boxes.Ambient] in
theorem refineCol_length (env : List AVal) (i : Nat) (f : AVal → AVal) :
    (refineCol env i f).length = env.length := by simp [refineCol]

omit [Boxes.Ambient] in
theorem EnvMem.zip_left {e₁ e₂ : List AVal} {row : Row} (h : EnvMem e₁ row) :
    EnvMem (List.zipWith AVal.join e₁ e₂) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_zipWith] at *
  split <;> simp_all [AVal.mem_top, AVal.mem_join_left]

omit [Boxes.Ambient] in
theorem EnvMem.zip_right {e₁ e₂ : List AVal} {row : Row} (h : EnvMem e₂ row) :
    EnvMem (List.zipWith AVal.join e₁ e₂) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_zipWith] at *
  split <;> simp_all [AVal.mem_top, AVal.mem_join_right]

omit [Boxes.Ambient] in
theorem refineNum_length (env : List AVal) (i : Nat) (w : Value) (f : Int → Bound → Bound) :
    (refineNum env i w f).length = env.length := by
  unfold refineNum; split <;> simp [refineCol_length]

omit [Boxes.Ambient] in
theorem refineCard_length (env : List AVal) (i : Nat) (w : Value) (f : Int → Bound → Bound) :
    (refineCard env i w f).length = env.length := by
  unfold refineCard; split <;> simp [refineCol_length]

omit [Boxes.Ambient] in
theorem refineAbs_length (env : List AVal) (i : Nat) (w : Value) (strict : Bool) :
    (refineAbs env i w strict).length = env.length := by
  unfold refineAbs; split <;> simp [refineCol_length]

omit [Boxes.Ambient] in
theorem Expr.refineL_length (env : List AVal) (e : Expr) :
    (e.refineL env).length = env.length := by
  fun_induction Expr.refineL env e <;> (try split) <;> simp_all [refineCol_length, refineNum_length, refineCard_length,
    refineAbs_length]

omit [Boxes.Ambient] in
@[simp] theorem Value.isTrue_ofBool (b : Bool) : (Value.bool b).isTrue = b := by cases b <;> rfl

/-- A comparison with a number is TRUE only of a number of its kind. -/
theorem cmp_num {f : BinFn} (hf : f = .eq ∨ f = .lt) {v : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply f v (k.val c)).isTrue = true) : ∃ x, v = k.val x ∧
      (BinFn.apply f (k.val x) (k.val c)).isTrue = true := by
  cases hv : v.numOf? with
  | none => rw [BinFn.cmp_other_num hf k c hv] at h; cases h
  | some p =>
    obtain ⟨k', x⟩ := p
    rw [Value.numOf?_some hv] at h ⊢
    rcases hf with rfl | rfl
    · rw [BinFn.eq_vals] at h
      split at h
      · subst_vars; exact ⟨x, rfl, by rw [BinFn.eq_vals]; simpa using h⟩
      · cases h
    · rw [BinFn.lt_vals] at h
      split at h
      · subst_vars; exact ⟨x, rfl, by rw [BinFn.lt_vals]; simpa using h⟩
      · cases h

theorem cmp_num' {f : BinFn} (hf : f = .eq ∨ f = .lt) {w : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply f (k.val c) w).isTrue = true) : ∃ x, w = k.val x ∧
      (BinFn.apply f (k.val c) (k.val x)).isTrue = true := by
  cases hw : w.numOf? with
  | none => rw [BinFn.cmp_num_other hf k c hw] at h; cases h
  | some p =>
    obtain ⟨k', x⟩ := p
    rw [Value.numOf?_some hw] at h ⊢
    rcases hf with rfl | rfl
    · rw [BinFn.eq_vals] at h
      split at h
      · subst_vars; exact ⟨x, rfl, by rw [BinFn.eq_vals]; simpa using h⟩
      · cases h
    · rw [BinFn.lt_vals] at h
      split at h
      · subst_vars; exact ⟨x, rfl, by rw [BinFn.lt_vals]; simpa using h⟩
      · cases h

theorem lt_num_right {v : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .lt v (k.val c)).isTrue = true) : ∃ x, v = k.val x ∧ k.norm x < k.norm c := by
  obtain ⟨x, rfl, h⟩ := cmp_num (.inr rfl) h
  rw [BinFn.lt_vals] at h; exact ⟨x, rfl, by simpa using h⟩

theorem lt_num_left {w : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .lt (k.val c) w).isTrue = true) : ∃ x, w = k.val x ∧ k.norm c < k.norm x := by
  obtain ⟨x, rfl, h⟩ := cmp_num' (.inr rfl) h
  rw [BinFn.lt_vals] at h; exact ⟨x, rfl, by simpa using h⟩

theorem not_lt_num_right {v : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt v (k.val c))).isTrue = true) :
    ∃ x, v = k.val x ∧ k.norm c ≤ k.norm x := by
  cases hv : v.numOf? with
  | none => rw [BinFn.cmp_other_num (.inr rfl) k c hv] at h; cases h
  | some p =>
    obtain ⟨k', x⟩ := p
    rw [Value.numOf?_some hv] at h ⊢
    rw [BinFn.lt_vals] at h
    split at h
    · rename_i hkk; subst k'; refine ⟨x, rfl, ?_⟩
      by_cases hx : k.norm x < k.norm c <;> simp_all [UnFn.apply, Value.isTrue] <;> omega
    · cases h

theorem not_lt_num_left {w : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt (k.val c) w)).isTrue = true) :
    ∃ x, w = k.val x ∧ k.norm x ≤ k.norm c := by
  cases hw : w.numOf? with
  | none => rw [BinFn.cmp_num_other (.inr rfl) k c hw] at h; cases h
  | some p =>
    obtain ⟨k', x⟩ := p
    rw [Value.numOf?_some hw] at h ⊢
    rw [BinFn.lt_vals] at h
    split at h
    · rename_i hkk; subst k'; refine ⟨x, rfl, ?_⟩
      by_cases hx : k.norm c < k.norm x <;> simp_all [UnFn.apply, Value.isTrue] <;> omega
    · cases h

/-- `v = c` is TRUE: `v` is a number of `c`'s kind with `c`'s canonical code. -/
theorem eq_num {v : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .eq v (k.val c)).isTrue = true) : ∃ x, v = k.val x ∧ k.norm x = k.norm c := by
  obtain ⟨x, rfl, h⟩ := cmp_num (.inl rfl) h
  rw [BinFn.eq_vals] at h
  exact ⟨x, rfl, by by_cases hx : k.norm x = k.norm c <;> simp_all⟩

theorem not_eq_num {v : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .eq v (k.val c))).isTrue = true) : ∃ x, v = k.val x := by
  cases hv : v.numOf? with
  | none => rw [BinFn.cmp_other_num (.inl rfl) k c hv] at h; cases h
  | some p =>
    obtain ⟨k', x⟩ := p
    rw [Value.numOf?_some hv] at h ⊢
    rw [BinFn.eq_vals] at h
    split at h
    · subst_vars; exact ⟨x, rfl⟩
    · cases h

theorem eq_str {v : Value} {k : String} (h : (BinFn.apply .eq v (.str k)).isTrue = true) :
    v = .str k := by
  cases v <;> simp_all [BinFn.apply, Value.isTrue]
  rename_i x; by_cases hx : x = k <;> simp_all

theorem not_eq_str {v : Value} {k : String}
    (h : (UnFn.apply .not (BinFn.apply .eq v (.str k))).isTrue = true) :
    ∀ s, v = .str s → s ≠ k := by
  rintro s rfl rfl
  simp [BinFn.apply, UnFn.apply, Value.isTrue] at h

theorem isNull_true {v : Value} (h : (UnFn.apply .isNull v).isTrue = true) : v = .null := by
  cases v <;> simp_all [UnFn.apply, Value.isTrue]

theorem not_isNull {v : Value} (h : (UnFn.apply .not (UnFn.apply .isNull v)).isTrue = true) :
    v ≠ .null := by
  cases v <;> simp_all [UnFn.apply, Value.isTrue]

omit [Boxes.Ambient] in
theorem Value.canonV_val (k : NumKind) (i : Int) : (k.val i).canonV = k.val (k.norm i) := by
  cases k <;> simp only [NumKind.val, Value.canonV, NumKind.norm_float, NumKind.norm_int,
    NumKind.norm_date, NumKind.norm_ts, NumKind.norm_tod, NumKind.norm_dec]

/-- SQL `v = w` is TRUE only when both are one non-NULL value up to `canon`
(`-0.0 = 0.0`, D31). -/
theorem eq_true_same {v w : Value} (h : (BinFn.apply .eq v w).isTrue = true) :
    v.canonV = w.canonV ∧ v ≠ .null := by
  cases hv : v.numOf? with
  | some p =>
    obtain ⟨k, i⟩ := p
    rw [Value.numOf?_some hv] at h ⊢
    obtain ⟨x, rfl, h⟩ := cmp_num' (.inl rfl) h
    rw [BinFn.eq_vals] at h
    have : k.norm i = k.norm x := by by_cases hx : k.norm i = k.norm x <;> simp_all
    exact ⟨by rw [Value.canonV_val, Value.canonV_val, this], NumKind.val_ne_null _ _⟩
  | none =>
    cases hw : w.numOf? with
    | some q =>
      obtain ⟨k', j⟩ := q
      rw [Value.numOf?_some hw, BinFn.cmp_other_num (.inl rfl) k' j hv] at h; cases h
    | none =>
      cases v <;> cases w <;> simp only [Value.numOf?, reduceCtorEq] at hv hw <;>
        simp [BinFn.apply, Value.isTrue, Value.canonV] at h ⊢
      all_goals
        rename_i x y
        first
        | (by_cases hxy : x = y
           · simp [hxy]
           · simp [hxy] at h)
        | (by_cases hxy : x.map Value.canonV = y.map Value.canonV
           · simp [hxy]
           · simp [hxy] at h)

/-- `<` with a NULL side is never TRUE, nor is its negation; by `rfl` on each
value, without unfolding `BinFn.apply` under `simp`. -/
theorem lt_null_left (w : Value) : (BinFn.apply .lt .null w).isTrue = false := by
  cases w <;> rfl

theorem lt_null_right (v : Value) : (BinFn.apply .lt v .null).isTrue = false := by
  cases v <;> rfl

theorem not_lt_null_left (w : Value) :
    (UnFn.apply .not (BinFn.apply .lt .null w)).isTrue = false := by
  cases w <;> rfl

theorem not_lt_null_right (v : Value) :
    (UnFn.apply .not (BinFn.apply .lt v .null)).isTrue = false := by
  cases v <;> rfl

theorem lt_fields_ord {v w : Value} (h : (BinFn.apply .lt v w).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  cases v <;> cases w <;> first | exact ⟨rfl, rfl⟩ |
    (simp_all [BinFn.apply, Value.isTrue, Value.numPair]; done)

theorem not_lt_fields_ord {v w : Value}
    (h : (UnFn.apply .not (BinFn.apply .lt v w)).isTrue = true) :
    v.isOrd = true ∧ w.isOrd = true := by
  cases v <;> cases w <;> first | exact ⟨rfl, rfl⟩ |
    (simp_all [BinFn.apply, UnFn.apply, Value.isTrue, Value.numPair]; done)

omit [Boxes.Ambient] in
theorem nonNullOrd_mem {a : AVal} {v : Value} (h : a.Mem v) (hv : v.isOrd = true) :
    a.nonNullOrd.Mem v := by
  cases v with
  | bool x => cases x <;> simp_all [AVal.nonNullOrd, AVal.Mem]
  | _ => simp_all [Value.isOrd, AVal.nonNullOrd, AVal.Mem, AVal.MemNum]

omit [Boxes.Ambient] in
theorem nonNullNum_mem {a : AVal} {k : NumKind} {x : Int} {f : Bound → Bound} (h : a.Mem (k.val x))
    (hf : ∀ b, b.Mem (k.norm x) → (f b).Mem (k.norm x)) : (a.nonNullNum k f).Mem (k.val x) := by
  obtain ⟨b, hb, hm, _⟩ := AVal.mem_val.mp h
  rw [AVal.mem_val]
  exact ⟨f b, by simp [AVal.nonNullNum, hb], hf b hm, by simp [AVal.nonNullNum]⟩

omit [Boxes.Ambient] in
/-- `refineNum` is sound where the row's column is a number of `w`'s kind whose
integer `f` keeps. -/
theorem refineNum_sound {env : List AVal} {row : Row} {i : Nat} {w : Value}
    {f : Int → Bound → Bound} (h : EnvMem env row)
    (hw : ∀ k c, w.numOf? = some (k, c) → ∃ x, row.getD i .null = k.val x ∧
      ∀ b, b.Mem (k.norm x) → (f (k.norm c) b).Mem (k.norm x)) :
    EnvMem (refineNum env i w f) row := by
  unfold refineNum
  split
  · rename_i k c hkc
    obtain ⟨x, hx, hf⟩ := hw k c hkc
    refine refineCol_sound h ?_
    have := h i; rw [hx] at this ⊢
    exact nonNullNum_mem this hf
  · exact h

theorem not_isNull_arith {f : BinFn} (hf : f = .add ∨ f = .sub ∨ f = .mul) {v w : Value}
    (h : (UnFn.apply .not (UnFn.apply .isNull (BinFn.apply f v w))).isTrue = true) :
    (UnFn.apply .not (UnFn.apply .isNull v)).isTrue = true ∧
      (UnFn.apply .not (UnFn.apply .isNull w)).isTrue = true := by
  rcases hf with rfl | rfl | rfl <;> cases v <;> cases w <;>
    simp_all [BinFn.apply, UnFn.apply, Value.isTrue]

theorem not_isTrue_eq {r : Value} (h : (UnFn.apply .not r).isTrue = true) : r = .bool false := by
  cases r <;> simp_all [UnFn.apply, Value.isTrue]
  rename_i b; cases b <;> simp_all

omit [Boxes.Ambient] in
theorem or3_eq_false {v w : Value} (h : or3 v w = .bool false) :
    v = .bool false ∧ w = .bool false := by
  unfold or3 at h; split at h <;> simp_all

theorem not_or3_true {v w : Value} (h : (UnFn.apply .not (or3 v w)).isTrue = true) :
    (UnFn.apply .not v).isTrue = true ∧ (UnFn.apply .not w).isTrue = true := by
  obtain ⟨rfl, rfl⟩ := or3_eq_false (not_isTrue_eq h)
  simp [UnFn.apply, Value.isTrue]

theorem card_of_int {v : Value} {x : Int} (h : UnFn.apply .cardinality v = NumKind.int.val x) :
    ∃ vs, v = .list vs ∧ x = vs.length := by
  cases v <;> simp_all [UnFn.apply, NumKind.val]

omit [Boxes.Ambient] in
theorem refineCard_sound {env : List AVal} {row : Row} {i : Nat} {w : Value}
    {f : Int → Bound → Bound} (h : EnvMem env row)
    (hw : ∀ c, w = .int c → ∃ vs, row.getD i .null = .list vs ∧
      ∀ b, b.Mem vs.length → (f c b).Mem vs.length) :
    EnvMem (refineCard env i w f) row := by
  unfold refineCard
  split
  · rename_i c
    obtain ⟨vs, hv, hf⟩ := hw c rfl
    refine refineCol_sound h ?_
    have hm := h i
    rw [hv] at hm ⊢
    exact ⟨hm.1, hf _ hm.2.1, hm.2.2⟩
  · exact h

omit [Boxes.Ambient] in
/-- `all_match` is TRUE only of a list whose every element makes the lambda TRUE. -/
theorem allMatch_true {v : Value} {p : Value → Value}
    (h : (HoFn.apply .allMatch v p).isTrue = true) :
    ∃ vs, v = .list vs ∧ ∀ x ∈ vs, (p x).isTrue = true := by
  cases v
  case list vs =>
    refine ⟨vs, rfl, ?_⟩
    simp only [HoFn.apply] at h
    induction vs with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldr_cons, isTrue_and3, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact ih h.2 x hx
  all_goals simp [HoFn.apply, Value.isTrue] at h

omit [Boxes.Ambient] in
/-- `-x` of a negative canonical code is its code negation (D31). -/
theorem canon_negI_of_neg {a : Int} (ha : FloatCode.canon a < 0) :
    FloatCode.canon (FloatCode.negI a) = -FloatCode.canon a := by
  rw [FloatCode.canon_negI_neg]
  have h0 : FloatCode.negZero = -(2 * (FloatCode.maxMag : Int) + 6) := fp64.negZero_eq
  have h1 : FloatCode.negNan = -(2 * (FloatCode.maxMag : Int) + 5) := fp64.negNan_eq
  apply fp64.canon_eq_self
  show -FloatCode.canon a ≠ FloatCode.negZero ∧ -FloatCode.canon a ≠ FloatCode.negNan
  constructor <;> omega

theorem absF_lt {v : Value} {c : Int}
    (h : (BinFn.apply .lt (if (BinFn.apply .lt v (.float 0)).isTrue then UnFn.apply .fneg v else v)
      (.float c)).isTrue = true) :
    ∃ a, v = .float a ∧ -FloatCode.canon c < FloatCode.canon a ∧ FloatCode.canon a < FloatCode.canon c := by
  cases v
  case float a =>
    refine ⟨a, rfl, ?_⟩
    have e := BinFn.lt_vals .float .float a 0
    simp only [NumKind.val] at e
    rw [NumKind.norm_float, NumKind.norm_float, FloatCode.canon_zero] at e
    by_cases ha : FloatCode.canon a < 0
    · have e2 := BinFn.lt_vals .float .float (FloatCode.negI a) c
      simp only [NumKind.val] at e2
      rw [NumKind.norm_float, NumKind.norm_float, canon_negI_of_neg ha] at e2
      simp [e, ha, UnFn.apply, e2] at h; omega
    · have e2 := BinFn.lt_vals .float .float a c
      simp only [NumKind.val] at e2
      rw [NumKind.norm_float, NumKind.norm_float] at e2
      simp [e, ha, e2] at h; omega
  all_goals simp [BinFn.apply, Value.numPair, Value.isTrue] at h

theorem absF_le {v : Value} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt (.float c)
      (if (BinFn.apply .lt v (.float 0)).isTrue then UnFn.apply .fneg v else v))).isTrue = true) :
    ∃ a, v = .float a ∧ -FloatCode.canon c ≤ FloatCode.canon a ∧ FloatCode.canon a ≤ FloatCode.canon c := by
  cases v
  case float a =>
    refine ⟨a, rfl, ?_⟩
    have e := BinFn.lt_vals .float .float a 0
    simp only [NumKind.val] at e
    rw [NumKind.norm_float, NumKind.norm_float, FloatCode.canon_zero] at e
    by_cases ha : FloatCode.canon a < 0
    · have e2 := BinFn.lt_vals .float .float c (FloatCode.negI a)
      simp only [NumKind.val] at e2
      rw [NumKind.norm_float, NumKind.norm_float, canon_negI_of_neg ha] at e2
      simp [e, ha, UnFn.apply, e2] at h; omega
    · have e2 := BinFn.lt_vals .float .float c a
      simp only [NumKind.val] at e2
      rw [NumKind.norm_float, NumKind.norm_float] at e2
      simp [e, ha, e2, UnFn.apply] at h; omega
  all_goals simp [BinFn.apply, Value.numPair, Value.isTrue, UnFn.apply] at h

omit [Boxes.Ambient] in
theorem refineAbs_sound {env : List AVal} {row : Row} {i : Nat} {w : Value} {strict : Bool}
    (h : EnvMem env row)
    (hw : ∀ c, w = .float c → ∃ a, row.getD i .null = .float a ∧
      (if strict then -FloatCode.canon c < FloatCode.canon a ∧ FloatCode.canon a < FloatCode.canon c
       else -FloatCode.canon c ≤ FloatCode.canon a ∧ FloatCode.canon a ≤ FloatCode.canon c)) :
    EnvMem (refineAbs env i w strict) row := by
  unfold refineAbs
  split
  · rename_i c
    obtain ⟨a, ha, hb⟩ := hw c rfl
    refine refineCol_sound h ?_
    have hm := h i
    rw [ha] at hm ⊢
    refine nonNullNum_mem (k := .float) hm fun b hmb => Bound.mem_meet hmb ?_
    rw [NumKind.norm_float]
    cases strict <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;>
      exact ⟨fun l hl => by cases hl; omega, fun u hu => by cases hu; omega⟩
  · exact h

theorem Expr.refineL_sound' (env : List AVal) (e : Expr) : ∀ {row : Row}, EnvMem env row →
    (e.eval row).isTrue = true → EnvMem (e.refineL env) row := by
  fun_induction Expr.refineL env e <;> intro row h ht
  case case1 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
    exact ihq (ihp h ht.1) ht.2
  case case2 env i k =>
    have hx := eq_str (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    rw [← List.getD_eq_getElem?_getD] at hx
    have := h i; rw [hx] at this ⊢
    exact AVal.strIs_mem this
  case case3 env i k =>
    refine refineCol_sound h (AVal.strNot_mem (h i) ?_)
    exact not_eq_str (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
  case case4 env i w =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx, hk⟩ := lt_num_right (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun b hb => Bound.mem_atMost hb (by omega)⟩
  case case5 env w i =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx, hk⟩ := lt_num_left (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun b hb => Bound.mem_atLeast hb (by omega)⟩
  case case6 env i w =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx, hk⟩ := not_lt_num_right (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun b hb => Bound.mem_atLeast hb hk⟩
  case case7 env w i =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx, hk⟩ := not_lt_num_left (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun b hb => Bound.mem_atMost hb hk⟩
  case case8 env i w =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx, hxc⟩ := eq_num (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun _ _ => hxc ▸ Bound.mem_exact _⟩
  case case9 env i =>
    have hn : row.getD i .null ≠ .null := by
      simpa [List.getD_eq_getElem?_getD] using not_isNull (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    have := h i
    generalize row.getD i .null = v at hn this ⊢
    cases v with
    | bool b => cases b <;> simp_all [AVal.Mem]
    | _ => simp_all [AVal.Mem, AVal.MemNum]
  case case10 env i j ai aj =>
    -- `a = b` is TRUE: both sides are the same non-NULL value.
    obtain ⟨hv, hn⟩ := eq_true_same (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD] at hv
    rw [← List.getD_eq_getElem?_getD] at hn
    -- Equal up to `canon` (D31): the abstract values of both sides hold both.
    have hn' : row.getD j .null ≠ .null := fun e => by
      rw [e, show Value.null.canonV = .null by simp [Value.canonV]] at hv
      exact hn (Value.canonV_eq_null.mp hv)
    have hi := h i
    have hj := h j
    have h₁ := refineCol_sound (f := (·.meetEq aj)) h
      (AVal.meetEq_mem hi (AVal.mem_of_canonV_eq hv hj) hn)
    refine refineCol_sound h₁ ?_
    have hj' := h₁ j
    exact AVal.meetEq_mem hj' (AVal.mem_of_canonV_eq hv.symm hi) hn'
  case case11 env i w =>
    refine refineNum_sound h fun k c hw => ?_
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx⟩ := not_eq_num (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨x, hx, fun _ hb => hb⟩
  case case12 env i j =>
    obtain ⟨hx, hy⟩ := lt_fields_ord (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := AVal.nonNullOrd) h (nonNullOrd_mem (h i) hx)
    exact refineCol_sound h₁ (nonNullOrd_mem (h₁ j) hy)
  case case13 env i j =>
    obtain ⟨hx, hy⟩ := not_lt_fields_ord (by simpa [eval] using ht)
    rw [← List.getD_eq_getElem?_getD] at hx hy
    have h₁ := refineCol_sound (f := AVal.nonNullOrd) h (nonNullOrd_mem (h i) hx)
    exact refineCol_sound h₁ (nonNullOrd_mem (h₁ j) hy)
  case case14 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .add (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inl rfl) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case15 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .sub (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inr (.inl rfl)) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case16 env a b iha ihb =>
    have ht' : (UnFn.apply .not (UnFn.apply .isNull
        (BinFn.apply .mul (a.eval row) (b.eval row)))).isTrue = true := by simpa [eval] using ht
    obtain ⟨h₁, h₂⟩ := not_isNull_arith (.inr (.inr rfl)) ht'
    exact ihb (iha h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case17 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · exact EnvMem.zip_left (ihp h ht)
    · exact EnvMem.zip_right (ihq h ht)
  case case18 env i =>
    have hn : row.getD i .null = .null := by
      simpa [List.getD_eq_getElem?_getD] using isNull_true (by simpa [eval] using ht)
    refine refineCol_sound h ?_
    have := h i
    rw [hn] at this ⊢
    simpa [AVal.Mem] using this
  case case19 env p q ihp ihq =>
    have ht' : (UnFn.apply .not (or3 (p.eval row) (q.eval row))).isTrue = true := by
      simpa [eval, BinFn.apply] using ht
    obtain ⟨h₁, h₂⟩ := not_or3_true ht'
    exact ihq (ihp h (by simpa [eval] using h₁)) (by simpa [eval] using h₂)
  case case20 env i w =>
    refine refineCard_sound h fun c hw => ?_
    subst hw
    obtain ⟨x, hx, hk⟩ := lt_num_right (k := .int) (by simpa [eval, List.getD_eq_getElem?_getD, NumKind.val] using ht)
    obtain ⟨vs, hv, rfl⟩ := card_of_int hx
    exact ⟨vs, by simpa [List.getD_eq_getElem?_getD] using hv, fun b hb => Bound.mem_atMost hb (by simp only [NumKind.norm_int] at *; omega)⟩
  case case21 env w i =>
    refine refineCard_sound h fun c hw => ?_
    subst hw
    obtain ⟨x, hx, hk⟩ := lt_num_left (k := .int) (by simpa [eval, List.getD_eq_getElem?_getD, NumKind.val] using ht)
    obtain ⟨vs, hv, rfl⟩ := card_of_int hx
    exact ⟨vs, by simpa [List.getD_eq_getElem?_getD] using hv, fun b hb => Bound.mem_atLeast hb (by simp only [NumKind.norm_int] at *; omega)⟩
  case case22 env i w =>
    refine refineCard_sound h fun c hw => ?_
    subst hw
    obtain ⟨x, hx, hk⟩ :=
      not_lt_num_right (k := .int) (by simpa [eval, List.getD_eq_getElem?_getD, NumKind.val] using ht)
    obtain ⟨vs, hv, rfl⟩ := card_of_int hx
    exact ⟨vs, by simpa [List.getD_eq_getElem?_getD] using hv, fun b hb => Bound.mem_atLeast hb hk⟩
  case case23 env w i =>
    refine refineCard_sound h fun c hw => ?_
    subst hw
    obtain ⟨x, hx, hk⟩ :=
      not_lt_num_left (k := .int) (by simpa [eval, List.getD_eq_getElem?_getD, NumKind.val] using ht)
    obtain ⟨vs, hv, rfl⟩ := card_of_int hx
    exact ⟨vs, by simpa [List.getD_eq_getElem?_getD] using hv, fun b hb => Bound.mem_atMost hb hk⟩
  case case24 env i b a ih =>
    obtain ⟨vs, hv, hall⟩ := allMatch_true (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    rw [← List.getD_eq_getElem?_getD] at hv
    refine refineCol_sound h ?_
    have hm := h i
    rw [hv] at hm ⊢
    obtain ⟨hl, hc, he⟩ := AVal.mem_list.mp hm
    refine ⟨hl, hc, ?_⟩
    simp only [AVal.listIn, AVal.memAll_iff]
    exact fun x hx => ih (h.cons (he x hx)) (hall x hx) 0
  case case25 env i j k w hij =>
    obtain ⟨rfl, rfl⟩ := hij
    refine refineAbs_sound h fun c hw => ?_
    subst hw
    obtain ⟨a, ha, hb⟩ := absF_lt (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨a, by simpa [List.getD_eq_getElem?_getD] using ha, by simpa using hb⟩
  case case26 => exact h
  case case27 env w i j k hij =>
    obtain ⟨rfl, rfl⟩ := hij
    refine refineAbs_sound h fun c hw => ?_
    subst hw
    obtain ⟨a, ha, hb⟩ := absF_le (by simpa [eval, List.getD_eq_getElem?_getD] using ht)
    exact ⟨a, by simpa [List.getD_eq_getElem?_getD] using ha, by simpa using hb⟩
  case case28 => exact h
  case case29 => exact h

theorem Expr.refineL_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refineL env) row :=
  Expr.refineL_sound' env e h ht

/-- What a row that makes `e` TRUE satisfies (`refineL`), with constant
decimals folded first (`Expr.normConst`). -/
def Expr.refine (env : List AVal) (e : Expr) : List AVal := e.normConst.refineL env

omit [Boxes.Ambient] in
theorem Expr.refine_length (env : List AVal) (e : Expr) : (e.refine env).length = env.length :=
  Expr.refineL_length env _

theorem Expr.refine_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = true) : EnvMem (e.refine env) row :=
  Expr.refineL_sound env _ h (by rwa [Expr.eval_normConst])

/-! ## What a condition says about one expression

`CASE WHEN c THEN t ELSE e END` evaluates `t` only where `c` is TRUE and `e`
only where it is not (FALSE or NULL). The rewrites of `GREATEST`, `LEAST`,
`ABS` and `NULLIF` branch on `IS NULL` and on comparisons with constants, so a
condition's *subject* (the expression it tests) is often the branch itself:
`CASE WHEN x < 0 THEN 0 ELSE x END` is `≥ 0` because in the `ELSE` branch
`x < 0` is not TRUE. -/

/-- A constraint on a value. -/
inductive Cstr where
  | null
  | notNull
  /-- A number of kind `k` in `b`; if `strict`, certainly a (non-NULL) number
  of kind `k`. -/
  | numIn (k : NumKind) (b : Bound) (strict : Bool)
  /-- Not the number `c` of kind `k` (but maybe NULL or another value). -/
  | ne (k : NumKind) (c : Int)
  /-- A string in `l`; if `strict`, certainly a (non-NULL) string (#708). -/
  | strIn (l : List String) (strict : Bool)
  /-- Not the string `k` (but maybe NULL or not a string). -/
  | strNe (k : String)

def Cstr.Holds : Cstr → Value → Prop
  | .null, v => v = .null
  | .notNull, v => v ≠ .null
  | .numIn k b true, v => ∃ j, v = k.val j ∧ b.Mem (k.norm j)
  | .numIn k b false, v => ∀ j, v = k.val j → b.Mem (k.norm j)
  | .ne k c, v => ∀ j, v = k.val j → k.norm j ≠ c
  | .strIn l true, v => ∃ s, v = .str s ∧ s ∈ l
  | .strIn l false, v => ∀ s, v = .str s → s ∈ l
  | .strNe k, v => ∀ s, v = .str s → s ≠ k

/-- A constraint on `s` from a comparison with the literal `w`, if a number. -/
def numCstr (s : Expr) (w : Value) (f : NumKind → Int → Cstr) : Option (Expr × Cstr) :=
  match w.numOf? with
  | some (k, c) => some (s, f k (k.norm c))
  | none => none

/-- What `c` being TRUE (`pos`) or not TRUE says about its subject. -/
def Expr.cstr (pos : Bool) : Expr → Option (Expr × Cstr)
  | .un .isNull s => some (s, if pos then .null else .notNull)
  | .un .not (.un .isNull s) => some (s, if pos then .notNull else .null)
  | .bin .eq s (.lit (.str k)) => some (s, if pos then .strIn [k] true else .strNe k)
  | .un .not (.bin .eq s (.lit (.str k))) => some (s, if pos then .strNe k
      else .strIn [k] false)
  | .bin .lt s (.lit w) => numCstr s w fun k c =>
      if pos then .numIn k ⟨none, some (c - 1)⟩ true else .numIn k ⟨some c, none⟩ false
  | .bin .lt (.lit w) s => numCstr s w fun k c =>
      if pos then .numIn k ⟨some (c + 1), none⟩ true else .numIn k ⟨none, some c⟩ false
  | .un .not (.bin .lt s (.lit w)) => numCstr s w fun k c =>
      if pos then .numIn k ⟨some c, none⟩ true else .numIn k ⟨none, some (c - 1)⟩ false
  | .un .not (.bin .lt (.lit w) s) => numCstr s w fun k c =>
      if pos then .numIn k ⟨none, some c⟩ true else .numIn k ⟨some (c + 1), none⟩ false
  | .bin .eq s (.lit w) => numCstr s w fun k c =>
      if pos then .numIn k (.exact c) true else .ne k c
  | .un .not (.bin .eq s (.lit w)) => numCstr s w fun k c =>
      if pos then .ne k c else .numIn k (.exact c) false
  | _ => none

/-- Narrow an abstract value by a constraint. A constraint that leaves other
values open narrows only an abstraction whose numbers are all of its kind. -/
def Cstr.apply : Cstr → AVal → AVal
  | .null, a => { null := a.null }
  | .notNull, a => { a with null := false }
  | .numIn k b true, a => { int := a.int.map (·.meet b), nk := some k }
  | .numIn k b false, a => if a.nk = some k then { a with int := a.int.map (·.meet b) } else a
  -- Intervals cannot exclude a single value.
  | .ne _ _, a => a
  | .strIn l true, a => { str := a.str, strs := meetStrs a.strs (some l) }
  | .strIn l false, a => { a with strs := meetStrs a.strs (some l) }
  | .strNe k, a => a.strNot k

/-- The constraint on `-v` (`kf`'s negation: integers, or doubles' codes) given
one on `v`. -/
def Cstr.neg (kf : NumKind) : Cstr → Option Cstr
  | .null => some .null
  | .notNull => none
  -- Integers only: `-NaN` is the NaN (D31), which no negated bound states.
  | .numIn k b strict => if k = kf ∧ kf = .int then some (.numIn k b.neg strict) else none
  | .ne k c => if k = kf ∧ kf = .int then some (.ne k (-c)) else none
  | .strIn _ _ | .strNe _ => none

omit [Boxes.Ambient] in
theorem Value.isTrue_bool (b : Bool) : (Value.bool b).isTrue = b := by cases b <;> rfl

omit [Boxes.Ambient] in
@[simp] theorem Value.isTrue_nullV : Value.null.isTrue = false := rfl

omit [Boxes.Ambient] in
theorem Bound.mem_lohi {l h : Option Int} {x : Int} (hl : ∀ a, l = some a → a ≤ x)
    (hh : ∀ b, h = some b → x ≤ b) : (⟨l, h⟩ : Bound).Mem x := ⟨hl, hh⟩

/-- A comparison with a number that is not TRUE says nothing of other values,
and of a number of its kind that the comparison does not hold. -/
theorem lt_false_right {v : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .lt v (k.val c)).isTrue = false) : ∀ j, v = k.val j → k.norm c ≤ k.norm j := by
  rintro j rfl; rw [BinFn.lt_vals] at h; simp at h; omega

theorem lt_false_left {w : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .lt (k.val c) w).isTrue = false) : ∀ j, w = k.val j → k.norm j ≤ k.norm c := by
  rintro j rfl; rw [BinFn.lt_vals] at h; simp at h; omega

theorem not_lt_false_right {v : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt v (k.val c))).isTrue = false) :
    ∀ j, v = k.val j → k.norm j ≤ k.norm c - 1 := by
  rintro j rfl; rw [BinFn.lt_vals] at h
  by_cases hj : k.norm j < k.norm c <;> simp_all [UnFn.apply] <;> omega

theorem not_lt_false_left {w : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .lt (k.val c) w)).isTrue = false) :
    ∀ j, w = k.val j → k.norm c + 1 ≤ k.norm j := by
  rintro j rfl; rw [BinFn.lt_vals] at h
  by_cases hj : k.norm c < k.norm j <;> simp_all [UnFn.apply] <;> omega

theorem eq_false_num {v : Value} {k : NumKind} {c : Int}
    (h : (BinFn.apply .eq v (k.val c)).isTrue = false) : ∀ j, v = k.val j → k.norm j ≠ k.norm c := by
  rintro j rfl; rw [BinFn.eq_vals] at h; intro hj; simp [hj] at h

theorem not_eq_false_num {v : Value} {k : NumKind} {c : Int}
    (h : (UnFn.apply .not (BinFn.apply .eq v (k.val c))).isTrue = false) :
    ∀ j, v = k.val j → (Bound.exact (k.norm c)).Mem (k.norm j) := by
  rintro j rfl; rw [BinFn.eq_vals] at h
  have : k.norm j = k.norm c := by
    by_cases hj : k.norm j = k.norm c
    · exact hj
    · simp [UnFn.apply, hj] at h
  rw [this]; exact Bound.mem_exact _

omit [Boxes.Ambient] in
theorem numCstr_eq {s s' : Expr} {w : Value} {f : NumKind → Int → Cstr} {k : Cstr}
    (h : numCstr s w f = some (s', k)) : ∃ kk c, w = kk.val c ∧ s' = s ∧ k = f kk (kk.norm c) := by
  unfold numCstr at h
  split at h
  · rename_i kk c hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨kk, c, Value.numOf?_some hw, h.1.symm, h.2.symm⟩
  · cases h

theorem Expr.cstr_sound {pos : Bool} {c s : Expr} {k : Cstr} {row : Row}
    (hc : c.cstr pos = some (s, k)) (ht : (c.eval row).isTrue = pos) : k.Holds (s.eval row) := by
  unfold Expr.cstr at hc
  split at hc
  -- `IS NULL`, `IS NOT NULL` and strings: as the values say.
  case h_1 | h_2 | h_3 | h_4 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [eval] at ht
    generalize Expr.eval row _ = v at ht ⊢
    cases pos <;> cases v <;> simp_all [UnFn.apply, BinFn.apply, Cstr.Holds, Value.numPair]
    all_goals (try rename_i x; by_cases hx : x = _ <;> simp_all)
  case h_11 => cases hc
  all_goals
    obtain ⟨kk, cc, rfl, rfl, rfl⟩ := numCstr_eq hc
    simp only [eval] at ht
    generalize Expr.eval row _ = v at ht ⊢
    cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte, Cstr.Holds]
  · exact fun j hj => Bound.mem_lohi (fun a ha => by cases ha; exact lt_false_right ht j hj)
      (fun b hb => by cases hb)
  · obtain ⟨x, rfl, hx⟩ := lt_num_right ht
    exact ⟨x, rfl, Bound.mem_lohi (fun a ha => by cases ha) (fun b hb => by cases hb; omega)⟩
  · exact fun j hj => Bound.mem_lohi (fun a ha => by cases ha)
      (fun b hb => by cases hb; exact lt_false_left ht j hj)
  · obtain ⟨x, rfl, hx⟩ := lt_num_left ht
    exact ⟨x, rfl, Bound.mem_lohi (fun a ha => by cases ha; omega) (fun b hb => by cases hb)⟩
  · exact fun j hj => Bound.mem_lohi (fun a ha => by cases ha)
      (fun b hb => by cases hb; exact not_lt_false_right ht j hj)
  · obtain ⟨x, rfl, hx⟩ := not_lt_num_right ht
    exact ⟨x, rfl, Bound.mem_lohi (fun a ha => by cases ha; omega) (fun b hb => by cases hb)⟩
  · exact fun j hj => Bound.mem_lohi (fun a ha => by cases ha; exact not_lt_false_left ht j hj)
      (fun b hb => by cases hb)
  · obtain ⟨x, rfl, hx⟩ := not_lt_num_left ht
    exact ⟨x, rfl, Bound.mem_lohi (fun a ha => by cases ha) (fun b hb => by cases hb; omega)⟩
  · exact eq_false_num ht
  · obtain ⟨x, hx, hxc⟩ := eq_num ht
    exact ⟨x, hx, hxc ▸ Bound.mem_exact _⟩
  · exact not_eq_false_num ht
  · obtain ⟨x, hx⟩ := not_eq_num ht
    intro j hj; rw [hx] at hj
    have hxj : x = j := by cases kk <;> simp_all [NumKind.val]
    subst hxj
    intro hc
    rw [hx, BinFn.eq_vals] at ht; simp [UnFn.apply, hc] at ht

theorem Cstr.apply_sound {k : Cstr} {a : AVal} {v : Value} (hh : k.Holds v) (ha : a.Mem v) :
    (k.apply a).Mem v := by
  cases k with
  | null => simp_all [Cstr.Holds, Cstr.apply, AVal.Mem]
  | notNull =>
    simp only [Cstr.Holds] at hh
    cases v <;> (try rename_i bb; cases bb) <;> simp_all [Cstr.apply, AVal.Mem, AVal.MemNum]
  | numIn kk b strict =>
    cases strict
    · simp only [Cstr.apply]
      split
      · rename_i hnk
        cases hv : v.numOf? with
        | none =>
          cases v <;> (try rename_i bb; cases bb) <;> simp_all [AVal.Mem, Value.numOf?]
        | some p =>
          obtain ⟨k', j⟩ := p
          rw [Value.numOf?_some hv] at ha hh ⊢
          obtain ⟨x, hx, hm, hk'⟩ := AVal.mem_val.mp ha
          have : k' = kk := by
            rw [hnk] at hk'; simp only [Option.all_some, beq_iff_eq] at hk'; exact hk'.symm
          subst this
          rw [AVal.mem_val]
          exact ⟨x.meet b, by simp [hx], Bound.mem_meet hm (hh j rfl), by simp [hnk]⟩
      · exact ha
    · obtain ⟨j, rfl, hj⟩ := hh
      obtain ⟨x, hx, hm, _⟩ := AVal.mem_val.mp ha
      rw [AVal.mem_val]
      exact ⟨x.meet b, by simp [Cstr.apply, hx], Bound.mem_meet hm hj, by simp [Cstr.apply]⟩
  | ne kk c => exact ha
  | strIn l strict =>
    cases strict <;> cases v <;> (try rename_i bb; cases bb) <;> cases hA : a.strs <;>
      simp_all [Cstr.Holds, Cstr.apply, AVal.Mem, meetStrs, AVal.MemNum]
  | strNe k => exact AVal.strNot_mem ha hh

theorem Cstr.neg_sound {k k' : Cstr} {f : UnFn} {kf : NumKind}
    (hf : (f = .neg ∧ kf = .int) ∨ (f = .fneg ∧ kf = .float)) {v : Value}
    (hk' : k.neg kf = some k') (hk : k.Holds v) : k'.Holds (f.apply v) := by
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · match k, k', hk' with
    | .null, _, rfl => simp_all [Cstr.Holds, UnFn.apply]
    | .numIn kk b strict, k', h =>
        simp only [Cstr.neg] at h
        split at h
        · rename_i hkk; obtain ⟨hkk, -⟩ := hkk; subst hkk
          simp only [Option.some.injEq] at h; subst h
          cases strict
          · intro j hj
            simp only [Cstr.Holds] at hk
            cases v <;> simp only [UnFn.apply, NumKind.val, reduceCtorEq, Value.int.injEq] at hj
            rename_i i; subst hj; simpa using Bound.mem_neg (hk i rfl)
          · obtain ⟨j, rfl, hj⟩ := hk
            exact ⟨-j, by simp [UnFn.apply, NumKind.val], by simpa using Bound.mem_neg hj⟩
        · cases h
    | .ne kk c, k', h =>
        simp only [Cstr.neg] at h
        split at h
        · rename_i hkk; obtain ⟨hkk, -⟩ := hkk; subst hkk
          simp only [Option.some.injEq] at h; subst h
          intro j hj
          simp only [Cstr.Holds] at hk
          cases v <;> simp only [UnFn.apply, NumKind.val, reduceCtorEq, Value.int.injEq] at hj
          rename_i i; subst hj; have := hk i rfl; simp only [NumKind.norm_int] at *; omega
        · cases h
    | .notNull, _, h | .strIn _ _, _, h | .strNe _, _, h => simp [Cstr.neg] at h
  · -- `-x` of doubles keeps only `IS NULL` (`Cstr.neg`).
    cases k <;> simp [Cstr.neg] at hk'
    subst hk'; simp_all [Cstr.Holds, UnFn.apply]

/-- Constraints known to hold on the current row, each on the value of an
expression (the conditions of the enclosing `CASE` branches and `OR`s). -/
abbrev Assumptions := List (Expr × Cstr)

def KsHold (ks : Assumptions) (row : Row) : Prop := ∀ p ∈ ks, p.2.Holds (p.1.eval row)

/-- `c`'s constraint when it is TRUE (`pos`) or not, as assumptions. -/
def Expr.cstrs (pos : Bool) (c : Expr) : Assumptions := (c.normConst.cstr pos).toList

theorem KsHold.cons_cstrs {pos : Bool} {c : Expr} {ks : Assumptions} {row : Row}
    (ht : (c.eval row).isTrue = pos) (hks : KsHold ks row) : KsHold (c.cstrs pos ++ ks) row := by
  intro p hp
  simp only [List.mem_append, Expr.cstrs] at hp
  rcases hp with hp | hp
  · cases hc : c.normConst.cstr pos with
    | none => simp [hc] at hp
    | some sk => simp only [hc, Option.toList_some, List.mem_singleton] at hp; subst hp;
                 exact Expr.cstr_sound hc (by rwa [Expr.eval_normConst])
  · exact hks p hp

/-! ### Alternatives (#702)

`AND` that is not TRUE says one of its sides is not TRUE, which no single
constraint states. `Expr.cstrAlts` keeps such a condition as alternatives:
on every row where it is (not) TRUE, every assumption of one alternative
holds. The DuckDB lift guards `a * b` on doubles with
`CASE WHEN (a = ∞ OR a = -∞) AND b = 0 THEN NaN …`, and the `ELSE` branch
then knows `a ≠ ±∞` or `b ≠ 0`, which rules out the NaN of `0 · ∞`. -/

/-- One alternative of each list, together. -/
def altsProd (xs ys : List Assumptions) : List Assumptions :=
  xs.flatMap fun x => ys.map (x ++ ·)

/-- At most eight alternatives; beyond that, none of them (`[[]]`, which
always holds). -/
def altsCapped (as : List Assumptions) : List Assumptions :=
  if as.length ≤ 8 then as else [[]]

/-- Does one alternative hold on the row? -/
def AltsHold (as : List Assumptions) (row : Row) : Prop := ∃ ks ∈ as, KsHold ks row

theorem KsHold.append {ks ks' : Assumptions} {row : Row} (h : KsHold ks row)
    (h' : KsHold ks' row) : KsHold (ks ++ ks') row := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem KsHold.of_append_left {ks ks' : Assumptions} {row : Row} (h : KsHold (ks ++ ks') row) :
    KsHold ks row := fun p hp => h p (List.mem_append_left _ hp)

theorem KsHold.of_append_right {ks ks' : Assumptions} {row : Row} (h : KsHold (ks ++ ks') row) :
    KsHold ks' row := fun p hp => h p (List.mem_append_right _ hp)

theorem AltsHold.prod {xs ys : List Assumptions} {row : Row} (hx : AltsHold xs row)
    (hy : AltsHold ys row) : AltsHold (altsProd xs ys) row := by
  obtain ⟨x, hx, hkx⟩ := hx
  obtain ⟨y, hy, hky⟩ := hy
  exact ⟨x ++ y, List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩, hkx.append hky⟩

theorem AltsHold.capped {as : List Assumptions} {row : Row} (h : AltsHold as row) :
    AltsHold (altsCapped as) row := by
  unfold altsCapped
  split
  · exact h
  · exact ⟨[], by simp, fun _ hp => by simp at hp⟩

/-- What `c` being TRUE (`pos`) or not TRUE says, as alternatives. -/
def Expr.cstrAltsL (pos : Bool) : Expr → List Assumptions
  | .bin .and p q => altsCapped (if pos then altsProd (p.cstrAltsL true) (q.cstrAltsL true)
      else p.cstrAltsL false ++ q.cstrAltsL false)
  | .bin .or p q => altsCapped (if pos then p.cstrAltsL true ++ q.cstrAltsL true
      else altsProd (p.cstrAltsL false) (q.cstrAltsL false))
  | e => [(e.cstr pos).toList]

theorem Expr.cstrAltsL_sound {row : Row} (pos : Bool) (c : Expr)
    (ht : (c.eval row).isTrue = pos) : AltsHold (c.cstrAltsL pos) row := by
  fun_induction Expr.cstrAltsL pos c
  case case1 pos p q ihpt ihqt ihpf ihqf =>
    refine AltsHold.capped ?_
    simp only [eval, BinFn.apply, isTrue_and3] at ht
    cases pos
    · simp only [Bool.and_eq_false_iff] at ht
      simp only [Bool.false_eq_true, ite_false]
      rcases ht with ht | ht
      · obtain ⟨k, hk, h⟩ := ihpf ht
        exact ⟨k, List.mem_append_left _ hk, h⟩
      · obtain ⟨k, hk, h⟩ := ihqf ht
        exact ⟨k, List.mem_append_right _ hk, h⟩
    · simp only [Bool.and_eq_true] at ht
      simp only [ite_true]
      exact (ihpt ht.1).prod (ihqt ht.2)
  case case2 pos p q ihpt ihqt ihpf ihqf =>
    refine AltsHold.capped ?_
    simp only [eval, BinFn.apply, isTrue_or3] at ht
    cases pos
    · simp only [Bool.or_eq_false_iff] at ht
      simp only [Bool.false_eq_true, ite_false]
      exact (ihpf ht.1).prod (ihqf ht.2)
    · simp only [Bool.or_eq_true] at ht
      simp only [ite_true]
      rcases ht with ht | ht
      · obtain ⟨k, hk, h⟩ := ihpt ht
        exact ⟨k, List.mem_append_left _ hk, h⟩
      · obtain ⟨k, hk, h⟩ := ihqt ht
        exact ⟨k, List.mem_append_right _ hk, h⟩
  case case3 pos e _ _ =>
    refine ⟨(e.cstr pos).toList, by simp, ?_⟩
    intro p hp
    cases hc : e.cstr pos with
    | none => simp [hc] at hp
    | some sk =>
      simp only [hc, Option.toList_some, List.mem_singleton] at hp
      subst hp
      exact Expr.cstr_sound hc ht

/-- `cstrAltsL`, with constant decimals folded first (as `cstrs`). -/
def Expr.cstrAlts (pos : Bool) (c : Expr) : List Assumptions := c.normConst.cstrAltsL pos

theorem Expr.cstrAlts_sound {row : Row} {pos : Bool} {c : Expr}
    (ht : (c.eval row).isTrue = pos) : AltsHold (c.cstrAlts pos) row :=
  Expr.cstrAltsL_sound pos _ (by rwa [Expr.eval_normConst])

/-- Narrow the abstract value `a` of `e` by an assumption about `e`, or about
`x` when `e` is `-x`. -/
def narrowBy (e : Expr) (a : AVal) (sk : Expr × Cstr) : AVal :=
  if sk.1 = e then sk.2.apply a
  else match e with
    | .un .neg y => if y = sk.1 then ((sk.2.neg .int).map (·.apply a)).getD a else a
    | .un .fneg y => if y = sk.1 then ((sk.2.neg .float).map (·.apply a)).getD a else a
    | _ => a

def narrowAll (ks : Assumptions) (e : Expr) (a : AVal) : AVal := ks.foldl (narrowBy e) a

theorem narrowBy_sound {e : Expr} {a : AVal} {sk : Expr × Cstr} {row : Row}
    (hk : sk.2.Holds (sk.1.eval row)) (ha : a.Mem (e.eval row)) :
    (narrowBy e a sk).Mem (e.eval row) := by
  unfold narrowBy
  split
  · rename_i hs; rw [← hs]; exact Cstr.apply_sound hk (hs ▸ ha)
  · split
    · split
      · rename_i y hy; subst hy
        cases hn : sk.2.neg .int with
        | none => exact ha
        | some k' => exact Cstr.apply_sound (Cstr.neg_sound (.inl ⟨rfl, rfl⟩) hn hk) ha
      · exact ha
    · split
      · rename_i y hy; subst hy
        cases hn : sk.2.neg .float with
        | none => exact ha
        | some k' => exact Cstr.apply_sound (Cstr.neg_sound (.inr ⟨rfl, rfl⟩) hn hk) ha
      · exact ha
    · exact ha

theorem narrowAll_sound {e : Expr} {row : Row} :
    ∀ {ks : Assumptions} {a : AVal}, KsHold ks row → a.Mem (e.eval row) →
      (narrowAll ks e a).Mem (e.eval row)
  | [], _, _, ha => ha
  | sk :: ks, _, hks, ha => by
      simp only [narrowAll, List.foldl_cons]
      exact narrowAll_sound (ks := ks) (fun p hp => hks p (by simp [hp]))
        (narrowBy_sound (hks sk (by simp)) ha)

/-- What a row on which `e` is *not* TRUE satisfies (the `ELSE` branch of a
`CASE`). Recognizes the constraints of `Expr.cstr` on columns, and `OR`
(neither side is TRUE) and `AND` (one side is not TRUE). -/
def Expr.refineNegL (env : List AVal) : Expr → List AVal
  | .bin .or p q => q.refineNegL (p.refineNegL env)
  | .bin .and p q => List.zipWith AVal.join (p.refineNegL env) (q.refineNegL env)
  | e => match e.cstr false with
    | some (.field i, k) => refineCol env i k.apply
    | _ => env

theorem Expr.refineNegL_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = false) : EnvMem (e.refineNegL env) row := by
  fun_induction Expr.refineNegL env e
  case case1 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_false_iff] at ht
    exact ihq (ihp h ht.1) ht.2
  case case2 env p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_false_iff] at ht
    rcases ht with ht | ht
    · exact EnvMem.zip_left (ihp h ht)
    · exact EnvMem.zip_right (ihq h ht)
  case case3 env e _ _ i k hc =>
    refine refineCol_sound h ?_
    have hk := Expr.cstr_sound hc ht
    exact Cstr.apply_sound (by simpa [eval] using hk) (h i)
  case case4 => exact h

/-- What a row that makes `e` FALSE or NULL satisfies (`refineNegL`), with
constant decimals folded first. -/
def Expr.refineNeg (env : List AVal) (e : Expr) : List AVal := e.normConst.refineNegL env

theorem Expr.refineNeg_sound {row : Row} (env : List AVal) (e : Expr) (h : EnvMem env row)
    (ht : (e.eval row).isTrue = false) : EnvMem (e.refineNeg env) row :=
  Expr.refineNegL_sound env _ h (by rwa [Expr.eval_normConst])

/-! ## Whole conditions on a row (#597)

A precondition that relates columns (`a <= 0 OR b < 0`) says nothing about
one column on its own. Kept whole, it proves itself where the plan carries it
through unchanged (`Fact.holds`), and it narrows a column once the other
disjuncts are ruled out on a path (`Expr.refineOr`). -/

/-- Does `p` hold for every column the expression reads? A lambda's body
reads its parameter as field 0 and the row from field 1 (D28). -/
def Expr.allFields (p : Nat → Bool) : Expr → Bool
  | .lit _ => true
  | .field i => p i
  | .un _ a => a.allFields p
  | .bin _ a b => a.allFields p && b.allFields p
  | .ifThen c t e => c.allFields p && t.allFields p && e.allFields p
  | .hof _ l b => l.allFields p && b.allFields (liftPred p)

/-- Read column `g i` wherever the expression reads column `i`. -/
def Expr.mapFields (g : Nat → Nat) : Expr → Expr
  | .lit v => .lit v
  | .field i => .field (g i)
  | .un f a => .un f (a.mapFields g)
  | .bin f a b => .bin f (a.mapFields g) (b.mapFields g)
  | .ifThen c t e => .ifThen (c.mapFields g) (t.mapFields g) (e.mapFields g)
  | .hof f l b => .hof f (l.mapFields g) (b.mapFields (liftIdx g))

omit [Boxes.Ambient] in
theorem Expr.allFields_true : ∀ e : Expr, e.allFields (fun _ => true) = true
  | .lit _ | .field _ => rfl
  | .un _ a => Expr.allFields_true a
  | .bin _ a b => by simp [allFields, Expr.allFields_true a, Expr.allFields_true b]
  | .ifThen c t e => by
      simp [allFields, Expr.allFields_true c, Expr.allFields_true t, Expr.allFields_true e]
  | .hof _ l b => by simp [allFields, Expr.allFields_true l, Expr.allFields_true b]

omit [Boxes.Ambient] in
theorem Expr.allFields_and {p q : Nat → Bool} :
    ∀ {e : Expr}, e.allFields p = true → e.allFields q = true → e.allFields (fun i => p i && q i) = true
  | .lit _, _, _ => rfl
  | .field _, hp, hq => by simp_all [allFields]
  | .un _ a, hp, hq => Expr.allFields_and (e := a) hp hq
  | .bin _ a b, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      exact ⟨Expr.allFields_and hp.1 hq.1, Expr.allFields_and hp.2 hq.2⟩
  | .ifThen c t e, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨Expr.allFields_and hp.1.1 hq.1.1, Expr.allFields_and hp.1.2 hq.1.2⟩,
        Expr.allFields_and hp.2 hq.2⟩
  | .hof _ l b, hp, hq => by
      simp only [allFields, Bool.and_eq_true] at hp hq ⊢
      refine ⟨Expr.allFields_and hp.1 hq.1, ?_⟩
      rw [liftPred_and]; exact Expr.allFields_and hp.2 hq.2

omit [Boxes.Ambient] in
theorem Expr.mapFields_id : ∀ e : Expr, e.mapFields id = e
  | .lit _ | .field _ => rfl
  | .un f a => by simp [mapFields, Expr.mapFields_id a]
  | .bin f a b => by simp [mapFields, Expr.mapFields_id a, Expr.mapFields_id b]
  | .ifThen c t e => by
      simp [mapFields, Expr.mapFields_id c, Expr.mapFields_id t, Expr.mapFields_id e]
  | .hof f l b => by simp [mapFields, Expr.mapFields_id l, Expr.mapFields_id b]

/-- Moving the columns an expression reads, with their values, keeps its
value. -/
theorem Expr.eval_mapFields {p : Nat → Bool} {g : Nat → Nat} {row row' : Row}
    (hg : ∀ i, p i = true → row'.getD (g i) .null = row.getD i .null) :
    ∀ {e : Expr}, e.allFields p = true → (e.mapFields g).eval row' = e.eval row
  | .lit _, _ => rfl
  | .field i, h => hg i h
  | .un f a, h => by simp only [mapFields, eval, Expr.eval_mapFields hg (e := a) h]
  | .bin f a b, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1, Expr.eval_mapFields hg h.2]
  | .ifThen c t e, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1.1, Expr.eval_mapFields hg h.1.2,
        Expr.eval_mapFields hg h.2]
  | .hof f l b, h => by
      simp only [allFields, Bool.and_eq_true] at h
      simp only [mapFields, eval, Expr.eval_mapFields hg h.1]
      congr 1; funext x
      exact Expr.eval_mapFields (liftIdx_getD x hg) h.2

/-- The same expression on a row that agrees on the columns it reads. -/
theorem Expr.eval_congr {p : Nat → Bool} {row row' : Row}
    (hg : ∀ i, p i = true → row'.getD i .null = row.getD i .null) {e : Expr}
    (h : e.allFields p = true) : e.eval row' = e.eval row := by
  simpa [Expr.mapFields_id] using Expr.eval_mapFields (g := id) hg h

omit [Boxes.Ambient] in
theorem AVal.not_isTrue {a : AVal} {v : Value} (hm : a.Mem v) (ht : a.tt = false) :
    v.isTrue = false := by
  match v, hm with
  | .bool true, hm => simp_all [AVal.Mem]
  | .bool false, _ | .null, _ | .int _, _ | .float _, _ | .date _, _ | .ts _, _ | .tod _, _
  | .dec _ _, _ | .str _, _ | .list _, _ | .struct _, _ => rfl

/-- What a row on which `e` is TRUE satisfies, by cases: a disjunct that
cannot be TRUE under `env` is dropped, so under `a > 0` the condition
`a <= 0 OR b < 0` narrows `b` to `b < 0`. A `CASE` (`ibis.ifelse`) whose
condition is decided under `env` is its branch. A disjunct that is NULL is
not TRUE either, so a NULL operand is dropped with the FALSE ones. -/
def Expr.refineOr (env : List AVal) : Expr → List AVal
  | .bin f p q =>
      if f = .or then
        if (p.abs env).tt = false then q.refineOr env
        else if (q.abs env).tt = false then p.refineOr env
        else List.zipWith AVal.join (p.refineOr env) (q.refineOr env)
      else (Expr.bin f p q).refine env
  | .ifThen c t e =>
      if (c.abs env).tt = false then e.refineOr env
      else if (c.abs env).certainlyTrue then t.refineOr env
      else env
  | e => e.refine env

theorem Expr.refineOr_length (env : List AVal) : ∀ e : Expr, (e.refineOr env).length = env.length
  | .bin f p q => by
      simp only [refineOr]
      split
      · split
        · exact Expr.refineOr_length env q
        · split
          · exact Expr.refineOr_length env p
          · simp [Expr.refineOr_length env p, Expr.refineOr_length env q]
      · exact Expr.refine_length env _
  | .ifThen c t e => by
      simp only [refineOr]
      split
      · exact Expr.refineOr_length env e
      · split
        · exact Expr.refineOr_length env t
        · rfl
  | .lit _ | .field _ | .un _ _ | .hof _ _ _ => Expr.refine_length env _

theorem Expr.refineOr_sound {row : Row} (env : List AVal) (h : EnvMem env row) :
    ∀ (e : Expr), (e.eval row).isTrue = true → EnvMem (e.refineOr env) row
  | .bin f p q, ht => by
      simp only [refineOr]
      split
      · rename_i hf
        subst hf
        simp only [eval, BinFn.apply, isTrue_or3, Bool.or_eq_true] at ht
        split
        · rename_i hp
          exact Expr.refineOr_sound env h q
            (ht.resolve_left (by simp [AVal.not_isTrue (Expr.abs_sound h p) hp]))
        · split
          · rename_i _ hq
            exact Expr.refineOr_sound env h p
              (ht.resolve_right (by simp [AVal.not_isTrue (Expr.abs_sound h q) hq]))
          · rcases ht with hp | hq
            · exact EnvMem.zip_left (Expr.refineOr_sound env h p hp)
            · exact EnvMem.zip_right (Expr.refineOr_sound env h q hq)
      · exact Expr.refine_sound env _ h ht
  | .ifThen c t e, ht => by
      simp only [refineOr]
      have hc := Expr.abs_sound h c
      split
      · rename_i hct
        have hnc := AVal.not_isTrue hc hct
        simp only [eval, hnc] at ht
        exact Expr.refineOr_sound env h e ht
      · split
        · rename_i _ hcert
          have hcv := AVal.certainlyTrue_mem hcert hc
          simp only [eval, hcv, Value.isTrue, ite_true] at ht
          exact Expr.refineOr_sound env h t ht
        · exact h
  | .lit _, ht | .field _, ht | .un _ _, ht | .hof _ _ _, ht => Expr.refine_sound env _ h ht

end Substrait
