import SubstraitLean.Contracts.Refine

/-!
# Contracts: Facts

Relational facts (`Fact`, `Fact.Holds`): facts through a plan, about window
columns and about the measures of one group, with `Rel.facts_sound`.

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

/-! ## Relational facts

Per-column descriptions cannot say "`t1` is exactly `Δ` after `t0`" or "`v` is
anything but -9999". `Fact`s can: they are collected alongside the column
descriptions and used when evaluating comparisons and differences. -/

/-- A fact about a row. -/
inductive Fact where
  /-- If columns `i` and `j` hold numbers `x` and `y` of one kind, then
  `x - y ∈ b`. -/
  | diff (i j : Nat) (b : Bound)
  /-- Column `i` does not hold the number `c` of kind `k`. -/
  | ne (i : Nat) (k : NumKind) (c : Int)
  /-- If columns `s` and `c` hold integers `x` and `n`, then `n` is positive
  and `x` is a sum of `n` integers in `b`: the `SUM` and `COUNT` of a decimal
  `AVG` (`Parse.decimalAvgs`, #237). -/
  | ratio (s c : Nat) (b : Bound)
  /-- The condition is TRUE on the row: a precondition or filter condition
  kept whole, whatever its shape (#597). -/
  | holds (e : Expr)
  deriving Repr, DecidableEq

def Fact.Holds (row : Row) : Fact → Prop
  -- Numbers by their canonical codes (`NumKind.norm`): `-0.0` is `0.0` (D31).
  | .diff i j b => ∀ (k : NumKind) x y, row.getD i .null = k.val x → row.getD j .null = k.val y →
      b.Mem (k.norm x - k.norm y)
  | .ne i k c => ∀ x, row.getD i .null = k.val x → k.norm x ≠ k.norm c
  | .ratio s c b => ∀ x n, (row.getD s .null).unscaled? = some x →
      (row.getD c .null).unscaled? = some n →
      0 < n ∧ (∀ l, b.lo = some l → n * l ≤ x) ∧ (∀ h, b.hi = some h → x ≤ n * h)
  | .holds e => (e.eval row).isTrue = true

def FactsHold (fs : List Fact) (row : Row) : Prop := ∀ f ∈ fs, f.Holds row

theorem FactsHold.append {fs gs : List Fact} {row : Row} (h₁ : FactsHold fs row)
    (h₂ : FactsHold gs row) : FactsHold (fs ++ gs) row := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h₁ f hf
  · exact h₂ f hf

theorem FactsHold.filter {fs : List Fact} {row : Row} (h : FactsHold fs row) (p : Fact → Bool) :
    FactsHold (fs.filter p) row := fun f hf => h f (List.mem_filter.mp hf).1

/-- Narrow `env` by every whole condition among the facts. -/
def useFacts (fs : List Fact) (env : List AVal) : List AVal :=
  fs.foldl (fun env f => match f with | .holds e => e.refineOr env | _ => env) env

theorem useFacts_length : ∀ (fs : List Fact) (env : List AVal), (useFacts fs env).length = env.length
  | [], _ => rfl
  | f :: fs, env => by
      simp only [useFacts, List.foldl_cons]
      rw [← useFacts, useFacts_length fs]
      split
      · exact Expr.refineOr_length env _
      · rfl

theorem useFacts_sound {row : Row} :
    ∀ {fs : List Fact} {env : List AVal}, FactsHold fs row → EnvMem env row →
      EnvMem (useFacts fs env) row
  | [], _, _, h => h
  | f :: fs, env, hfs, h => by
      simp only [useFacts, List.foldl_cons]
      rw [← useFacts]
      refine useFacts_sound (fun g hg => hfs g (by simp [hg])) ?_
      split
      · rename_i e
        exact Expr.refineOr_sound env h e (hfs (.holds e) (by simp))
      · exact h

/-- `e` is column `j` plus the constant `c`. -/
def Expr.linTerm : Expr → Option (Nat × Int)
  | .field j => some (j, 0)
  | .bin .add (.field j) (.lit (.int c)) => some (j, c)
  | .bin .add (.lit (.int c)) (.field j) => some (j, c)
  | .bin .sub (.field j) (.lit (.int c)) => some (j, -c)
  | _ => none

theorem Expr.linTerm_spec {e : Expr} {j : Nat} {c : Int} (h : e.linTerm = some (j, c)) :
    (e = .field j ∧ c = 0) ∨ e = .bin .add (.field j) (.lit (.int c)) ∨
      e = .bin .add (.lit (.int c)) (.field j) ∨ e = .bin .sub (.field j) (.lit (.int (-c))) := by
  unfold Expr.linTerm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp

/-- A column plus a constant that is not NULL: the column's number, moved
(timestamps, dates and times of day move by an integer; doubles and decimals
do not, and give NULL). -/
theorem Expr.linTerm_num {e : Expr} {j : Nat} {c y : Int} {k : NumKind} {row : Row}
    (h : e.linTerm = some (j, c)) (hy : row.getD j .null = k.val y) (hne : e.eval row ≠ .null) :
    e.eval row = k.val (y + c) := by
  rw [List.getD_eq_getElem?_getD] at hy
  rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl <;>
    cases k <;> simp_all [eval, BinFn.apply, NumKind.val, List.getD_eq_getElem?_getD] <;> omega

/-- A column plus a constant moves the canonical code by the constant: the
constant is 0 for a double (`+` of a double and an integer is NULL). -/
theorem Expr.linTerm_norm {e : Expr} {j : Nat} {c y : Int} {k : NumKind} {row : Row}
    (h : e.linTerm = some (j, c)) (hy : row.getD j .null = k.val y) (hne : e.eval row ≠ .null) :
    k.norm (y + c) = k.norm y + c ∧ ∀ d, k.norm (d - c) = k.norm d - c := by
  rw [List.getD_eq_getElem?_getD] at hy
  rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl
  · exact ⟨by simp, fun d => by simp⟩
  all_goals
    cases k <;> simp_all [eval, BinFn.apply, NumKind.val, List.getD_eq_getElem?_getD, NumKind.norm_int,
      NumKind.norm_date, NumKind.norm_ts, NumKind.norm_tod, NumKind.norm_dec]

theorem Expr.linTerm_of_num {e : Expr} {j : Nat} {c v : Int} {k : NumKind} {row : Row}
    (h : e.linTerm = some (j, c)) (hv : e.eval row = k.val v) :
    ∃ y, row.getD j .null = k.val y ∧ v = y + c := by
  have hne : e.eval row ≠ .null := by rw [hv]; exact NumKind.val_ne_null k v
  cases hr : (row.getD j .null).numOf? with
  | some p =>
    obtain ⟨k', y⟩ := p
    have hy := Value.numOf?_some hr
    have := Expr.linTerm_num h hy hne
    rw [hv] at this
    obtain ⟨rfl, rfl⟩ := NumKind.val_inj₂ this
    exact ⟨y, hy, rfl⟩
  | none =>
    exfalso; apply hne
    rw [List.getD_eq_getElem?_getD] at hr
    rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl <;>
      simp only [eval, List.getD_eq_getElem?_getD] at hv ⊢ <;>
      generalize row[j]?.getD Value.null = w at hr hv ⊢ <;>
      cases w <;> cases k <;> simp_all [Value.numOf?, BinFn.apply, NumKind.val]

def neFact (t : Expr) (k : NumKind) (c : Int) : List Fact :=
  match t.linTerm with | some (j, c') => [.ne j k (c - c')] | none => []

def diffFact (t₁ t₂ : Expr) (mk : Int → Int → Bound) : List Fact :=
  match t₁.linTerm, t₂.linTerm with
  | some (i, c₁), some (j, c₂) => [.diff i j (mk c₁ c₂)]
  | _, _ => []

/-- Facts that hold on every row where `e` is TRUE. -/
def Fact.mentions (i : Nat) : Fact → Bool
  | .diff a b _ | .ratio a b _ => a == i || b == i
  | .ne a _ _ => a == i
  -- A whole condition may be about NULLs.
  | .holds _ => false

/-- Facts that hold where `x IS NULL` (`q`), from the facts `fs` of the
other side of an `OR`: those about `x` (facts only constrain non-NULL values). -/
def orNullFacts (fs : List Fact) : Expr → List Fact
  | .un .isNull (.field i) => fs.filter (·.mentions i)
  | _ => []

/-- `t < a OR b < t` with `a ≤ b` numbers of one kind: `t` is not in
`[a, b]`, so not `0` when `0` is in it, and not `a`. -/
def orGapFacts : Expr → Expr → List Fact
  | .bin .lt t (.lit wa), .bin .lt (.lit wb) t' =>
    match wa.numOf?, wb.numOf? with
    | some (k, a), some (k', b) =>
      -- By canonical codes, as `<` compares (D31).
      if t == t' && k == k' && k.norm a ≤ k.norm b then
        (if k.norm a ≤ 0 && 0 ≤ k.norm b then neFact t k 0 else []) ++ neFact t k a else []
    | _, _ => []
  | _, _ => []

/-- `NOT (t = w)` for a number `w`: `t` is not `w`. -/
def neFactOf (t : Expr) (w : Value) : List Fact :=
  match w.numOf? with
  | some (k, c) => neFact t k c
  | none => []

def Expr.factsCore : Expr → List Fact
  | .bin .and p q => p.factsCore ++ q.factsCore
  | .un .not (.bin .eq t (.lit w)) => neFactOf t w
  | .un .not (.bin .eq (.lit w) t) => neFactOf t w
  | .bin .eq t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => .exact (c₂ - c₁)
  | .bin .lt t₁ t₂ => diffFact t₁ t₂ fun c₁ c₂ => ⟨none, some (c₂ - c₁ - 1)⟩
  | .un .not (.bin .lt t₁ t₂) => diffFact t₁ t₂ fun c₁ c₂ => ⟨some (c₂ - c₁), none⟩
  -- NOT (p OR q) is NOT p AND NOT q.
  | .un .not (.bin .or p q) => (Expr.un .not p).factsCore ++ (Expr.un .not q).factsCore
  -- NOT (x IS NOT NULL AND q): either x is NULL, or NOT q. Facts about x hold
  -- in both cases, since facts only constrain non-NULL values. (Ibis writes
  -- `~x.isnan()` this way.)
  | .un .not (.bin .and (.un .not (.un .isNull (.field i))) q) =>
      (Expr.un .not q).factsCore.filter (·.mentions i)
  -- `p OR q`: the facts of both, those of one about `x` if the other is
  -- `x IS NULL`, and the value a gap `t < a OR b < t` leaves out.
  | .bin .or p q =>
      let fp := p.factsCore
      let fq := q.factsCore
      fp.filter (fq.contains ·) ++ orNullFacts fp q ++ orNullFacts fq p ++
        orGapFacts p q ++ orGapFacts q p
  | _ => []
termination_by e => sizeOf e

theorem neFact_sound {t : Expr} {k : NumKind} {c : Int} {row : Row}
    (hne : ∀ u, t.eval row = k.val u → k.norm u ≠ k.norm c)
    (hnn : t.eval row ≠ .null) : FactsHold (neFact t k c) row := by
  unfold neFact
  split
  · rename_i j c' hl
    intro f hf
    simp only [List.mem_singleton] at hf; subst hf
    intro x hj
    have hv := hne _ (Expr.linTerm_num hl hj hnn)
    obtain ⟨h1, h2⟩ := Expr.linTerm_norm hl hj hnn
    rw [h1] at hv; rw [h2]; omega
  · intro f hf; simp at hf

/-- `NOT (t = w)` TRUE: `t` is a number of `w`'s kind other than `w`. -/
theorem neFactOf_sound {t : Expr} {w : Value} {row : Row}
    (ht : (UnFn.apply .not (BinFn.apply .eq (t.eval row) w)).isTrue = true) :
    FactsHold (neFactOf t w) row := by
  unfold neFactOf
  split
  · rename_i k c hw
    rw [Value.numOf?_some hw] at ht
    obtain ⟨x, hx⟩ := not_eq_num ht
    refine neFact_sound (fun u h hu => ?_) (by rw [hx]; exact NumKind.val_ne_null k x)
    rw [h, BinFn.eq_vals] at ht; simp [UnFn.apply, hu] at ht
  · intro f hf; simp at hf

theorem BinFn.eq_symm (v w : Value) : BinFn.apply .eq v w = BinFn.apply .eq w v := by
  cases v <;> cases w <;> simp only [BinFn.apply, Value.numPair] <;>
    first | rfl | (simp only [Bool.beq_comm]; done) | (simp only [eq_comm]; done) |
      (rename_i s₁ _ s₂ _
       by_cases hs : s₁ = s₂
       · subst hs; simp [Bool.beq_comm]
       · simp [hs, Ne.symm hs])

/-- A comparison that is not NULL has operands that are not NULL. -/
theorem cmp_nonnull {f : BinFn} (hf : f = .eq ∨ f = .lt) {v w : Value}
    (h : (BinFn.apply f v w).isTrue = true ∨ (BinFn.apply f v w) = .bool false) :
    v ≠ .null ∧ w ≠ .null := by
  rcases hf with rfl | rfl <;> constructor <;> intro hn <;> subst hn <;>
    first
      | (cases w <;> simp_all [BinFn.apply, Value.numPair])
      | (cases v <;> simp_all [BinFn.apply, Value.numPair])

/-- `NOT c` TRUE: `c` is FALSE. -/
theorem not_isTrue_any {v : Value} (h : (UnFn.apply .not v).isTrue = true) :
    v.isTrue = true ∨ v = .bool false := .inr (not_isTrue_eq h)

theorem diffFact_sound {t₁ t₂ : Expr} {mk : Int → Int → Bound} {row : Row} {P : Int → Int → Prop}
    (hn₁ : t₁.eval row ≠ .null) (hn₂ : t₂.eval row ≠ .null)
    (hP : ∀ (k : NumKind) u w, t₁.eval row = k.val u → t₂.eval row = k.val w → P (k.norm u) (k.norm w))
    (hmk : ∀ c₁ c₂ x y, P (x + c₁) (y + c₂) → (mk c₁ c₂).Mem (x - y)) :
    FactsHold (diffFact t₁ t₂ mk) row := by
  unfold diffFact
  split
  · rename_i i c₁ j c₂ h₁ h₂
    intro f hf
    simp only [List.mem_singleton] at hf; subst hf
    intro k x y hx hy
    have := hP k _ _ (Expr.linTerm_num h₁ hx hn₁) (Expr.linTerm_num h₂ hy hn₂)
    rw [(Expr.linTerm_norm h₁ hx hn₁).1, (Expr.linTerm_norm h₂ hy hn₂).1] at this
    exact hmk c₁ c₂ _ _ this
  · intro f hf; simp at hf

theorem not_and3_notnull_true {x w : Value} (hx : x ≠ .null)
    (h : (UnFn.apply .not (and3 (UnFn.apply .not (UnFn.apply .isNull x)) w)).isTrue = true) :
    (UnFn.apply .not w).isTrue = true := by
  have : UnFn.apply .not (UnFn.apply .isNull x) = .bool true := by
    cases x <;> first | exact absurd rfl hx | rfl
  rw [this] at h
  match w with
  | .bool false => simp [UnFn.apply, Value.isTrue]
  | .bool true => simp [and3, UnFn.apply, Value.isTrue] at h
  | .null | .int _ | .str _ => simp [and3, UnFn.apply, Value.isTrue] at h

theorem Fact.holds_of_null {f : Fact} {row : Row} {i : Nat} (hm : f.mentions i = true)
    (hn : row.getD i .null = .null) : f.Holds row := by
  cases f with
  | diff a b d =>
    simp only [Fact.mentions, Bool.or_eq_true, beq_iff_eq] at hm
    intro k x y hx hy
    rcases hm with rfl | rfl
    · rw [hn] at hx; exact absurd hx.symm (NumKind.val_ne_null k x)
    · rw [hn] at hy; exact absurd hy.symm (NumKind.val_ne_null k y)
  | ne a k c =>
    simp only [Fact.mentions, beq_iff_eq] at hm
    subst hm; intro x h; rw [hn] at h; exact absurd h.symm (NumKind.val_ne_null k x)
  | ratio a b _ =>
    simp only [Fact.mentions, Bool.or_eq_true, beq_iff_eq] at hm
    intro x y hx hy
    rcases hm with rfl | rfl
    · rw [hn] at hx; cases hx
    · rw [hn] at hy; cases hy
  | holds _ => simp [Fact.mentions] at hm

theorem orNullFacts_sound {fs : List Fact} {p q : Expr} {row : Row}
    (hp : (p.eval row).isTrue = true → FactsHold fs row)
    (hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true) {f : Fact}
    (hf : f ∈ orNullFacts fs q) : f.Holds row := by
  unfold orNullFacts at hf
  split at hf
  · rename_i i
    simp only [List.mem_filter] at hf
    rcases hpq with hp' | hq
    · exact hp hp' f hf.1
    · have hn : row.getD i .null = .null := by
        simp only [Expr.eval, List.getD_eq_getElem?_getD] at hq ⊢
        generalize row[i]?.getD Value.null = v at hq ⊢
        cases v <;> simp_all [UnFn.apply, Value.isTrue]
      exact Fact.holds_of_null hf.2 hn
  · simp at hf

theorem orGapFacts_sound {p q : Expr} {row : Row}
    (hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true) {f : Fact}
    (hf : f ∈ orGapFacts p q) : f.Holds row := by
  unfold orGapFacts at hf
  split at hf
  · rename_i t wa wb t'
    split at hf
    · rename_i k a k' b hwa hwb
      split at hf
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, rfl⟩, hab⟩ := hc
        rw [Value.numOf?_some hwa] at hpq
        rw [Value.numOf?_some hwb] at hpq
        -- `t` is a number of kind `k` below `a` or above `b`.
        have hnum : ∃ u, t.eval row = k.val u ∧ (k.norm u < k.norm a ∨ k.norm b < k.norm u) := by
          rcases hpq with h | h
          · obtain ⟨x, hx, hlt⟩ := lt_num_right (by simpa [Expr.eval] using h)
            exact ⟨x, hx, .inl hlt⟩
          · obtain ⟨x, hx, hlt⟩ := lt_num_left (by simpa [Expr.eval] using h)
            exact ⟨x, hx, .inr hlt⟩
        obtain ⟨u, hu, hout⟩ := hnum
        have hnn : t.eval row ≠ .null := by rw [hu]; exact NumKind.val_ne_null k u
        simp only [List.mem_append] at hf
        rcases hf with hf | hf
        · split at hf
          · rename_i h0
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
            refine neFact_sound (fun u' hv => ?_) hnn f hf
            rw [hu] at hv; obtain ⟨_, rfl⟩ := NumKind.val_inj₂ hv
            rw [NumKind.norm_zero]; omega
          · simp at hf
        · refine neFact_sound (fun u' hv => ?_) hnn f hf
          rw [hu] at hv; obtain ⟨_, rfl⟩ := NumKind.val_inj₂ hv; omega
      · simp at hf
    · simp at hf
  · simp at hf

theorem Expr.factsCore_sound {row : Row} (e : Expr) (ht : (e.eval row).isTrue = true) :
    FactsHold e.factsCore row := by
  fun_induction Expr.factsCore e
  case case1 p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
    exact (ihp ht.1).append (ihq ht.2)
  case case2 t w => exact neFactOf_sound (by simpa [eval] using ht)
  case case3 w t _ =>
    refine neFactOf_sound ?_
    simpa [eval, BinFn.eq_symm w] using ht
  case case4 t₁ t₂ =>
    have hsame := eq_true_same (by simpa [eval] using ht)
    have hn₂ : t₂.eval row ≠ .null := fun e => hsame.2 (Value.canonV_eq_null.mp
      (hsame.1.trans (by rw [e]; simp [Value.canonV])))
    refine diffFact_sound (P := fun u w => u = w) hsame.2 hn₂
      (fun k u w hu hw => ?_) (fun c₁ c₂ x y h => ?_)
    · have := hsame.1
      rw [hu, hw, Value.canonV_val, Value.canonV_val] at this; exact (NumKind.val_inj₂ this).2
    · simp only [Bound.Mem, Bound.exact, Option.some.injEq]
      constructor <;> intro _ h' <;> subst h' <;> omega
  case case5 t₁ t₂ =>
    have ht' : (BinFn.apply .lt (t₁.eval row) (t₂.eval row)).isTrue = true := by simpa [eval] using ht
    obtain ⟨hn₁, hn₂⟩ := cmp_nonnull (.inr rfl) (.inl ht')
    refine diffFact_sound (P := fun u w => u < w) hn₁ hn₂ (fun k u w hu hw => ?_)
      (fun c₁ c₂ x y h => ?_)
    · rw [hu, hw, BinFn.lt_vals] at ht'; simpa using ht'
    · simp only [Bound.Mem, Option.some.injEq, reduceCtorEq]
      constructor
      · intro _ h'; cases h'
      · intro _ h'; subst h'; omega
  case case6 t₁ t₂ =>
    have ht' : (UnFn.apply .not (BinFn.apply .lt (t₁.eval row) (t₂.eval row))).isTrue = true := by
      simpa [eval] using ht
    obtain ⟨hn₁, hn₂⟩ := cmp_nonnull (.inr rfl) (not_isTrue_any ht')
    refine diffFact_sound (P := fun u w => w ≤ u) hn₁ hn₂ (fun k u w hu hw => ?_)
      (fun c₁ c₂ x y h => ?_)
    · rw [hu, hw, BinFn.lt_vals] at ht'
      by_cases hlt : u < w <;> simp_all [UnFn.apply] <;> omega
    · simp only [Bound.Mem, Option.some.injEq, reduceCtorEq]
      constructor
      · intro _ h'; subst h'; omega
      · intro _ h'; cases h'
  case case7 p q ihp ihq =>
    obtain ⟨hp, hq⟩ := not_or3_true (v := p.eval row) (w := q.eval row)
      (by simpa [eval, BinFn.apply] using ht)
    exact (ihp (by simpa [eval] using hp)).append (ihq (by simpa [eval] using hq))
  case case8 i q ih =>
    intro f hf
    simp only [List.mem_filter] at hf
    by_cases hn : row.getD i .null = .null
    · exact Fact.holds_of_null hf.2 hn
    · have hq := not_and3_notnull_true (w := q.eval row) hn
        (by simpa [eval, BinFn.apply, List.getD_eq_getElem?_getD] using ht)
      exact ih (by simpa [eval] using hq) f hf.1
  case case9 p q fp fq ihp ihq =>
    have hpq : (p.eval row).isTrue = true ∨ (q.eval row).isTrue = true := by
      simpa [eval, BinFn.apply, isTrue_or3] using ht
    intro f hf
    simp only [List.mem_append, List.mem_filter] at hf
    rcases hf with (((⟨hfp, hfq⟩ | hf) | hf) | hf) | hf
    · rcases hpq with hp | hq
      · exact ihp hp f hfp
      · exact ihq hq f (List.contains_iff_mem.mp hfq)
    · exact orNullFacts_sound ihp hpq hf
    · exact orNullFacts_sound ihq hpq.symm hf
    · exact orGapFacts_sound hpq hf
    · exact orGapFacts_sound hpq.symm hf
  case case10 => intro f hf; simp at hf

/-- The conjuncts of a condition. -/
def Expr.conjuncts : Expr → List Expr
  | .bin f p q => if f = .and then p.conjuncts ++ q.conjuncts else [.bin f p q]
  | e => [e]

theorem Expr.conjuncts_sound {row : Row} :
    ∀ (e : Expr), (e.eval row).isTrue = true → ∀ c ∈ e.conjuncts, (c.eval row).isTrue = true
  | .bin f p q, ht, c, hc => by
      simp only [conjuncts] at hc
      split at hc
      · rename_i hf
        subst hf
        simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact Expr.conjuncts_sound p ht.1 c hc
        · exact Expr.conjuncts_sound q ht.2 c hc
      · simp only [List.mem_singleton] at hc; subst hc; exact ht
  | .lit _, ht, c, hc | .field _, ht, c, hc | .un _ _, ht, c, hc | .ifThen _ _ _, ht, c, hc
  | .hof _ _ _, ht, c, hc => by
      simp only [conjuncts, List.mem_singleton] at hc; subst hc; exact ht

/-- Facts that hold on every row where `e` is TRUE: each conjunct kept whole,
and what `factsCore` derives. -/
def Expr.factsOf (e : Expr) : List Fact := e.conjuncts.map .holds ++ e.factsCore

theorem Expr.factsOf_sound {row : Row} (e : Expr) (ht : (e.eval row).isTrue = true) :
    FactsHold e.factsOf row := by
  refine FactsHold.append ?_ (e.factsCore_sound ht)
  intro f hf
  simp only [List.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  exact Expr.conjuncts_sound e ht c hc

/-! ### Facts through a plan -/

def Fact.inRange (n : Nat) : Fact → Bool
  | .diff i j _ | .ratio i j _ => i < n && j < n
  | .ne i _ _ => i < n
  | .holds e => e.allFields (· < n)

def Fact.shift (n : Nat) : Fact → Fact
  | .diff i j b => .diff (n + i) (n + j) b
  | .ne i k c => .ne (n + i) k c
  | .ratio i j b => .ratio (n + i) (n + j) b
  | .holds e => .holds (e.mapFields (n + ·))

/-- Does the fact only constrain integers (so it holds where its columns are
NULL)? -/
def Fact.intsOnly : Fact → Bool
  | .holds _ => false
  | _ => true

/-- Re-index a fact: column `i` of the input appears at every position in `σ i`. -/
def Fact.rename (σ : Nat → List Nat) : Fact → List Fact
  | .diff i j b => (σ i).flatMap fun p => (σ j).map fun q => .diff p q b
  | .ne i k c => (σ i).map fun p => .ne p k c
  | .ratio i j b => (σ i).flatMap fun p => (σ j).map fun q => .ratio p q b
  -- At the first place each column it reads appears, if they all do.
  | .holds e =>
      if e.allFields (fun i => !(σ i).isEmpty) then [.holds (e.mapFields fun i => (σ i).headD 0)] else []

/-- Positions of input column `i` in an emit mapping. -/
def positions (m : List Nat) (i : Nat) : List Nat :=
  (List.range m.length).filter fun p => m[p]? == some i

/-- Where input column `i` appears in the output of `Project es` over `n`
columns: at `i` itself and wherever an expression copies it. -/
def copyCols (n : Nat) (es : List Expr) (i : Nat) : List Nat :=
  i :: ((List.range es.length).filter fun k => es[k]? == some (.field i)).map (n + ·)

/-- Facts about computed columns that are an input column plus a constant. -/
def linFacts (n : Nat) : Nat → List Expr → List Fact
  | _, [] => []
  | col, e :: es =>
      let here := match e with
        | .field _ => []
        | e => match e.linTerm with
          | some (j, c) => if j < n then [.diff col j (.exact c)] else []
          | none => []
      here ++ linFacts n (col + 1) es

/-! ### Facts about window columns

Window column `w` reads column `c` of another row of the partition. When that
row comes earlier (`LAG`) and `c` is the first sort key, ascending, then
`$c - $w ≥ 0`; `LEAD` and descending keys flip the sign. A partition column
read from the same partition is equal to the row's own. Only for a NULL
default: any other default could break both. -/

def orderFact (sort : List SortKey) (c w : Nat) (before : Bool) (gap : Int) : List Fact :=
  match sort with
  | k :: _ =>
    if k.col = c then
      if k.desc = before then [.diff w c ⟨some gap, none⟩] else [.diff c w ⟨some gap, none⟩]
    else []
  | [] => []

def partFact (part : List Nat) (c w : Nat) : List Fact :=
  if c ∈ part then [.diff c w (.exact 0)] else []

/-- How far apart a row and the one `offset` rows away are on the sort key: at
least `1` when the partition and the only sort key are a key of the input
(`strict`), else at least `0`. -/
def strictGap (strict : Bool) (sort : List SortKey) (offset : Nat) : Int :=
  if strict && sort.length == 1 && 1 ≤ offset then 1 else 0

def winFact (part : List Nat) (sort : List SortKey) (strict : Bool) (w : Nat) : WinFn → List Fact
  | .rowNumber => []
  | .lag c k d =>
      if d = .null then orderFact sort c w true (strictGap strict sort k) ++ partFact part c w else []
  | .lead c k d =>
      if d = .null then orderFact sort c w false (strictGap strict sort k) ++ partFact part c w else []
  | _ => []

/-- Facts about the window columns appended after `n` input columns. -/
def winFacts (part : List Nat) (sort : List SortKey) (strict : Bool) (n : Nat) (fns : List WinFn) :
    List Fact :=
  fns.zipIdx.flatMap fun (f, t) => winFact part sort strict (n + t) f

/-! ### Facts about the measures of one group

Measures of the same values on one group are related (#372): `MIN ≤ MAX`, and
an integer `AVG` with an integer result lies between them (`AggFn.iavg`). An
`AVG` of doubles rounds, and may step past them, so it has no such fact. -/

/-- Facts relating measure `mi` (column `ci`) to measure `mj` (column `cj`). -/
def pairFacts (ci cj : Nat) (mi mj : Measure) : List Fact :=
  if mi.filter ≠ mj.filter ∨ mj.arg ≠ mi.arg then [] else
  if mi.fn = .min ∧ mj.fn = .max then [.diff cj ci ⟨some 0, none⟩]
  else if mi.fn = .min ∧ mj.fn = .iavg then [.diff cj ci ⟨some 0, none⟩]
  else if mi.fn = .max ∧ mj.fn = .iavg then [.diff ci cj ⟨some 0, none⟩]
  else []

/-- Facts relating the measures `ms`, which follow `g` grouping columns. -/
def aggFacts (g : Nat) (ms : List Measure) : List Fact :=
  (List.range ms.length).flatMap fun i => (List.range ms.length).flatMap fun j =>
    match ms[i]?, ms[j]? with
    | some mi, some mj => pairFacts (g + i) (g + j) mi mj
    | _, _ => []

/-- Does the fact mention a column at or after `n`? -/
def Fact.rightOf (n : Nat) : Fact → Bool
  | .diff i j _ | .ratio i j _ => decide (n ≤ i) || decide (n ≤ j)
  | .ne i _ _ => decide (n ≤ i)
  | .holds _ => false

/-- Facts that hold on every output row of a plan, given facts `F t` about
each table. -/
def Rel.facts (cat : Catalog) (F : String → List Fact) (T : WindowKeys) : Rel → List Fact
  | .read t => F t
  | .values _ _ => []
  | .filter r c => r.facts cat F T ++ c.factsOf
  | .project r es =>
      let fs := (r.facts cat F T).filter (·.inRange (r.arity cat))
      fs.flatMap (Fact.rename (copyCols (r.arity cat) es)) ++ linFacts (r.arity cat) (r.arity cat) es
  | .emit r m => (r.facts cat F T).flatMap (Fact.rename (positions m))
  | .cross a b =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++ (b.facts cat F T).map (·.shift (a.arity cat))
  | .join a b .inner on =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++
        (b.facts cat F T).map (·.shift (a.arity cat)) ++ on.factsOf
  -- NULL padding keeps every fact true: facts only speak about integers. So
  -- are the condition's facts that mention a right column.
  | .join a b .left on =>
      (a.facts cat F T).filter (·.inRange (a.arity cat)) ++
        ((b.facts cat F T).filter Fact.intsOnly).map (·.shift (a.arity cat)) ++
        on.factsOf.filter (·.rightOf (a.arity cat))
  | .fetch r _ _ => r.facts cat F T
  | .unionAll a b => (a.facts cat F T).filter ((b.facts cat F T).contains ·)
  | .window r part sort fns =>
      (r.facts cat F T).filter (·.inRange (r.arity cat)) ++
        winFacts part sort (T r part sort) (r.arity cat) fns
  -- Some of the left rows, or all of the rows in another order or once each.
  | .semi a _ _ _ => a.facts cat F T
  | .orderBy r _ | .distinct r => r.facts cat F T
  | .aggregate _ gs ms => aggFacts gs.length ms
  | .unnest _ _ => []

theorem headD_mem_of {l : List Nat} (h : (!l.isEmpty) = true) : l.headD 0 ∈ l := by
  cases l with
  | nil => simp at h
  | cons p ps => simp

theorem Fact.rename_holds {σ : Nat → List Nat} {row row' : Row}
    (hσ : ∀ i, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    ∀ {f : Fact}, f.Holds row → ∀ g ∈ f.rename σ, g.Holds row'
  | .diff i j b, h, g, hg => by
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro k x y hx hy
      exact h k x y (hσ i p hp ▸ hx) (hσ j q hq ▸ hy)
  | .ne i k c, h, g, hg => by
      simp only [Fact.rename, List.mem_map] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      intro x hx
      exact h x (hσ i p hp ▸ hx)
  | .ratio i j _, h, g, hg => by
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i p hp ▸ hx) (hσ j q hq ▸ hy)
  | .holds e, h, g, hg => by
      simp only [Fact.rename] at hg
      split at hg
      · rename_i hall
        simp only [List.mem_singleton] at hg; subst hg
        simp only [Fact.Holds] at h ⊢
        rw [Expr.eval_mapFields (fun i hi => hσ i _ (headD_mem_of hi)) hall]; exact h
      · simp at hg

theorem FactsHold.rename {σ : Nat → List Nat} {fs : List Fact} {row row' : Row}
    (h : FactsHold fs row) (hσ : ∀ i, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    FactsHold (fs.flatMap (Fact.rename σ)) row' := by
  intro g hg
  simp only [List.mem_flatMap] at hg
  obtain ⟨f, hf, hg⟩ := hg
  exact Fact.rename_holds hσ (h f hf) g hg

/-- A fact whose columns are all `< n` only depends on the first `n` columns. -/
theorem Fact.holds_prefix {n : Nat} {row row' : Row}
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    ∀ {f : Fact}, f.inRange n = true → f.Holds row → f.Holds row'
  | .diff i j b, hr, h => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      intro k x y hx hy
      exact h k x y (hpre i hr.1 ▸ hx) (hpre j hr.2 ▸ hy)
  | .ne i k c, hr, h => by
      simp only [Fact.inRange, decide_eq_true_eq] at hr
      intro x hx; exact h x (hpre i hr ▸ hx)
  | .ratio i j _, hr, h => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      intro x y hx hy
      exact h x y (hpre i hr.1 ▸ hx) (hpre j hr.2 ▸ hy)
  | .holds e, hr, h => by
      simp only [Fact.inRange] at hr
      simp only [Fact.Holds] at h ⊢
      rw [Expr.eval_congr (fun i hi => hpre i (by simpa using hi)) hr]; exact h

theorem FactsHold.prefix {n : Nat} {fs : List Fact} {row row' : Row} (h : FactsHold fs row)
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    FactsHold (fs.filter (·.inRange n)) row' := by
  intro f hf
  simp only [List.mem_filter] at hf
  exact Fact.holds_prefix hpre hf.2 (h f hf.1)

theorem FactsHold.shift {n : Nat} {fs : List Fact} {row row' : Row} (h : FactsHold fs row)
    (hsh : ∀ i, row'.getD (n + i) .null = row.getD i .null) :
    FactsHold (fs.map (·.shift n)) row' := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  have := h f hf
  cases f with
  | diff i j b => intro k x y hx hy; exact this k x y (hsh i ▸ hx) (hsh j ▸ hy)
  | ne i k c => intro x hx; exact this x (hsh i ▸ hx)
  | ratio i j _ => intro x y hx hy; exact this x y (hsh i ▸ hx) (hsh j ▸ hy)
  | holds e =>
      simp only [Fact.shift, Fact.Holds] at this ⊢
      rw [Expr.eval_mapFields (fun i _ => hsh i) (Expr.allFields_true e)]; exact this

theorem getD_append_left' {x y : Row} {i : Nat} (h : i < x.length) :
    (x ++ y).getD i .null = x.getD i .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {x y : Row} (i : Nat) :
    (x ++ y).getD (x.length + i) .null = y.getD i .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem Fact.rename_holds_inRange {σ : Nat → List Nat} {row row' : Row} {n : Nat}
    (hσ : ∀ i < n, ∀ p ∈ σ i, row'.getD p .null = row.getD i .null) :
    ∀ {f : Fact}, f.inRange n = true → f.Holds row → ∀ g ∈ f.rename σ, g.Holds row'
  | .diff i j b, hr, h, g, hg => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro k x y hx hy
      exact h k x y (hσ i hr.1 p hp ▸ hx) (hσ j hr.2 q hq ▸ hy)
  | .ne i k c, hr, h, g, hg => by
      simp only [Fact.inRange, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_map] at hg
      obtain ⟨p, hp, rfl⟩ := hg
      intro x hx; exact h x (hσ i hr p hp ▸ hx)
  | .ratio i j _, hr, h, g, hg => by
      simp only [Fact.inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Fact.rename, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨p, hp, q, hq, rfl⟩ := hg
      intro x y hx hy
      exact h x y (hσ i hr.1 p hp ▸ hx) (hσ j hr.2 q hq ▸ hy)
  | .holds e, hr, h, g, hg => by
      simp only [Fact.inRange] at hr
      simp only [Fact.rename] at hg
      split at hg
      · rename_i hall
        simp only [List.mem_singleton] at hg; subst hg
        simp only [Fact.Holds] at h ⊢
        rw [Expr.eval_mapFields (p := fun i => decide (i < n) && !(σ i).isEmpty)
          (fun i hi => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
            exact hσ i hi.1 _ (headD_mem_of hi.2))
          (Expr.allFields_and hr hall)]
        exact h
      · simp at hg

theorem copyCols_getD {n : Nat} {es : List Expr} {row : Row} {i p : Nat}
    (hlen : row.length = n) (hi : i < n) (hp : p ∈ copyCols n es i) :
    (row ++ es.map (·.eval row)).getD p .null = row.getD i .null := by
  simp only [copyCols, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range,
    beq_iff_eq] at hp
  rcases hp with rfl | ⟨k, ⟨hk, hek⟩, rfl⟩
  · exact getD_append_left' (hlen ▸ hi)
  · rw [← hlen, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hek, Expr.eval]

theorem linFacts_sound {n : Nat} {row row' : Row}
    (hpre : ∀ i < n, row'.getD i .null = row.getD i .null) :
    ∀ (col : Nat) (es : List Expr),
      (∀ k < es.length, row'.getD (col + k) .null = (es[k]?.getD (.lit .null)).eval row) →
      FactsHold (linFacts n col es) row'
  | _, [], _ => fun f hf => by simp [linFacts] at hf
  | col, e :: es, hcols => by
      simp only [linFacts]
      refine FactsHold.append ?_ (linFacts_sound hpre (col + 1) es fun k hk => ?_)
      · have hcol : row'.getD col .null = e.eval row := by simpa using hcols 0 (by simp)
        split
        · intro f hf; simp at hf
        · split
          · rename_i j c hl
            split
            · rename_i hjn
              intro g hg
              simp only [List.mem_singleton] at hg; subst hg
              intro k x y hx hy
              rw [hcol] at hx
              obtain ⟨y', hy', hxy⟩ := Expr.linTerm_of_num hl hx
              rw [hpre j hjn, hy'] at hy
              obtain ⟨_, hy⟩ := NumKind.val_inj₂ hy; subst hy
              simp only [Bound.Mem, Bound.exact, Option.some.injEq]
              constructor <;> intro _ h <;> subst h <;> omega
            · intro g hg; simp at hg
          · intro g hg; simp at hg
      · have := hcols (k + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem FactsHold.shift_nulls {n : Nat} {fs : List Fact} {row : Row}
    (hnull : ∀ i, row.getD (n + i) .null = .null) :
    FactsHold ((fs.filter Fact.intsOnly).map (·.shift n)) row := by
  intro g hg
  simp only [List.mem_map, List.mem_filter] at hg
  obtain ⟨f, ⟨_, hio⟩, rfl⟩ := hg
  cases f with
  | holds _ => simp [Fact.intsOnly] at hio
  | diff i j b =>
    intro k x y hx _; rw [hnull i] at hx; exact absurd hx.symm (NumKind.val_ne_null k x)
  | ne i k c => intro hx; rw [hnull i] at hx; exact NumKind.val_ne_null k c hx.symm
  | ratio i j _ => intro x y hx _; rw [hnull i] at hx; cases hx

theorem positions_getD {m : List Nat} {row : Row} {i p : Nat} (hp : p ∈ positions m i) :
    (m.map (row.getD · .null)).getD p .null = row.getD i .null := by
  simp only [positions, List.mem_filter, List.mem_range, beq_iff_eq] at hp
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp.2]

/-- **Soundness of fact collection**: every row a well-formed plan produces
satisfies every fact `Rel.facts` collects, provided the table facts hold. -/
theorem FactsHold.rightOf_nulls {n : Nat} {fs : List Fact} {row : Row}
    (hn : ∀ i, n ≤ i → row.getD i .null = .null) : FactsHold (fs.filter (·.rightOf n)) row := by
  intro f hf
  simp only [List.mem_filter] at hf
  cases f with
  | diff i j b =>
    simp only [Fact.rightOf, Bool.or_eq_true, decide_eq_true_eq] at hf
    rcases hf.2 with h | h
    · exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i h)
    · exact Fact.holds_of_null (i := j) (by simp [Fact.mentions]) (hn j h)
  | ne i k c =>
    simp only [Fact.rightOf, decide_eq_true_eq] at hf
    exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i hf.2)
  | ratio i j _ =>
    simp only [Fact.rightOf, Bool.or_eq_true, decide_eq_true_eq] at hf
    rcases hf.2 with h | h
    · exact Fact.holds_of_null (i := i) (by simp [Fact.mentions]) (hn i h)
    · exact Fact.holds_of_null (i := j) (by simp [Fact.mentions]) (hn j h)
  | holds _ => simp [Fact.rightOf] at hf

theorem getD_pad_null {x : Row} {m i : Nat} (h : x.length ≤ i) :
    (x ++ List.replicate m Value.null).getD i .null = .null := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [getD_append_right']
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem orderFact_sound {sort : List SortKey} {c w : Nat} {before : Bool} {gap : Int} {row x : Row}
    (hgap : gap = 0 ∨ gap = 1) (hxc : row.getD c .null = x.getD c .null)
    (hv : ∀ (nk : NumKind) Y, row.getD w .null = nk.val Y → ∃ y, (y = x ∨
      (if before then sortLe sort y x else sortLe sort x y) = true) ∧ y.getD c .null = nk.val Y ∧
      (gap = 1 → ∀ k ∈ sort, y.getD k.col .null ≠ x.getD k.col .null)) :
    FactsHold (orderFact sort c w before gap) row := by
  match sort, hv with
  | [], _ => intro f hf; simp [orderFact] at hf
  | k :: ks, hv =>
    unfold orderFact
    by_cases hk : k.col = c
    · subst hk
      have key : ∀ (nk : NumKind) X Y, row.getD k.col .null = nk.val X →
          row.getD w .null = nk.val Y →
          if k.desc = before then gap ≤ Y - X else gap ≤ X - Y := by
        intro nk X Y hX hY
        obtain ⟨y, hy, hyc, hne⟩ := hv nk Y hY
        rw [hxc] at hX
        have hne' : gap = 1 → Y ≠ X := fun h1 he => by
          subst he; exact hne h1 k (by simp) (by rw [hyc, hX])
        rcases hy with rfl | hy
        · rw [hX] at hyc
          obtain ⟨_, hyc⟩ := NumKind.val_inj₂ hyc
          subst hyc
          rcases hgap with rfl | rfl
          · split <;> omega
          · exact absurd rfl (hne' rfl)
        · cases before
          · have := SortKey.le_val (lexLe_left (by simpa [sortLe] using hy)) hX hyc
            rcases hgap with rfl | rfl <;> have := hne' <;> cases hd : k.desc <;> simp_all <;> omega
          · have := SortKey.le_val (lexLe_left (by simpa [sortLe] using hy)) hyc hX
            rcases hgap with rfl | rfl <;> have := hne' <;> cases hd : k.desc <;> simp_all <;> omega
      simp only [↓reduceIte]
      intro f hf
      split at hf <;> simp only [List.mem_singleton] at hf <;> subst hf <;> intro nk X Y hX hY
      · rename_i hd; have := key nk Y X hY hX; simp only [hd, ↓reduceIte] at this
        simp [Bound.Mem]; omega
      · rename_i hd; have := key nk X Y hX hY; simp only [hd, ↓reduceIte] at this
        simp [Bound.Mem]; omega
    · intro f hf; simp [hk] at hf

theorem partFact_sound {part : List Nat} {c w : Nat} {row x : Row}
    (hxc : row.getD c .null = x.getD c .null)
    (hv : ∀ (nk : NumKind) Y, row.getD w .null = nk.val Y →
      ∃ y, (y = x ∨ samePart part x y = true) ∧ y.getD c .null = nk.val Y) :
    FactsHold (partFact part c w) row := by
  unfold partFact
  split
  · rename_i hc
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    intro nk X Y hX hY
    obtain ⟨y, hy, hyc⟩ := hv nk Y hY
    have : x.getD c .null = y.getD c .null := by
      rcases hy with rfl | hy
      · rfl
      · simp only [samePart, decide_eq_true_eq, List.map_inj_left] at hy; exact hy c hc
    rw [hxc, this, hyc] at hX
    obtain ⟨_, rfl⟩ := NumKind.val_inj₂ hX
    simp [Bound.Mem, Bound.exact]
  · intro f hf; simp at hf

theorem strictGap_cases (strict : Bool) (sort : List SortKey) (k : Nat) :
    strictGap strict sort k = 0 ∨ strictGap strict sort k = 1 := by
  unfold strictGap; split <;> simp

theorem strictGap_one {strict : Bool} {sort : List SortKey} {k : Nat}
    (h : strictGap strict sort k = 1) : strict = true ∧ sort.length = 1 ∧ 1 ≤ k := by
  unfold strictGap at h
  split at h
  · rename_i hc; simpa [and_assoc] using hc
  · cases h

/-- Rows of the same partition that differ on the key `part ++ sort` differ on
the only sort key. -/
theorem sort_ne_of_key {part : List Nat} {sort : List SortKey} {x y : Row}
    (hs : sort.length = 1) (hp : samePart part x y = true)
    (hk : keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    ∀ k ∈ sort, y.getD k.col .null ≠ x.getD k.col .null := by
  match sort, hs with
  | [k], _ =>
    intro k' hk' he
    simp only [List.mem_singleton] at hk'
    subst hk'
    apply hk
    simp only [samePart, decide_eq_true_eq] at hp
    simp only [keyOf, List.map_inj_left, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton]
    intro c hc
    rcases hc with hc | rfl
    · exact (List.map_inj_left.mp hp c hc).symm
    · exact he

theorem winFact_sound {part : List Nat} {sort : List SortKey} {strict : Bool} {n w : Nat}
    {b a : List Row} {x row : Row} {f : WinFn} (hf : f.refsLt n = true)
    (hpre : ∀ i < n, row.getD i .null = x.getD i .null)
    (hw : row.getD w .null = f.value part b a x)
    (hb : ∀ y ∈ b, sortLe sort y x = true) (ha : ∀ y ∈ a, sortLe sort x y = true)
    (hdist : strict = true → ∀ y, (y ∈ b ∨ y ∈ a) → samePart part x y = true →
      keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    FactsHold (winFact part sort strict w f) row := by
  cases f with
  | rowNumber | rank _ | denseRank _ | percentRank _ | cumeDist _ | ntile _ | agg _ _ _
  | firstValue _ _ _ | lastValue _ _ _ | nthValue _ _ _ _ => intro g hg; simp [winFact] at hg
  | lag c k d =>
    simp only [winFact]
    split
    · rename_i hd
      subst hd
      have hc : c < n := by simpa [WinFn.refsLt] using hf
      have hv : ∀ (nk : NumKind) Y, row.getD w .null = nk.val Y →
          ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ b ∧ samePart part x y = true)) ∧
            y.getD c .null = nk.val Y := by
        intro nk Y hY
        rcases WinFn.value_lag' (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
          (d := .null) with h | ⟨y, hy, h⟩
        · rw [hw, h] at hY; exact absurd hY.symm (NumKind.val_ne_null nk Y)
        · exact ⟨y, hy, by rw [← h, ← hw, hY]⟩
      refine FactsHold.append (orderFact_sound (strictGap_cases _ _ _) (hpre c hc) fun nk Y hY => ?_)
        (partFact_sound (hpre c hc) fun nk Y hY => ?_)
      · obtain ⟨y, hy | hy, hyc⟩ := hv nk Y hY
        · refine ⟨y, .inl hy.1, hyc, fun h1 => ?_⟩
          have := (strictGap_one h1).2.2; omega
        · refine ⟨y, .inr (by simpa using hb y hy.1), hyc, fun h1 => ?_⟩
          obtain ⟨hs, hl, _⟩ := strictGap_one h1
          exact sort_ne_of_key hl hy.2 (hdist hs y (.inl hy.1) hy.2)
      · obtain ⟨y, hy | hy, hyc⟩ := hv nk Y hY
        · exact ⟨y, .inl hy.1, hyc⟩
        · exact ⟨y, .inr hy.2, hyc⟩
    · intro g hg; simp at hg
  | lead c k d =>
    simp only [winFact]
    split
    · rename_i hd
      subst hd
      have hc : c < n := by simpa [WinFn.refsLt] using hf
      have hv : ∀ (nk : NumKind) Y, row.getD w .null = nk.val Y →
          ∃ y, ((y = x ∧ k = 0) ∨ (y ∈ a ∧ samePart part x y = true)) ∧
            y.getD c .null = nk.val Y := by
        intro nk Y hY
        rcases WinFn.value_lead' (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
          (d := .null) with h | ⟨y, hy, h⟩
        · rw [hw, h] at hY; exact absurd hY.symm (NumKind.val_ne_null nk Y)
        · exact ⟨y, hy, by rw [← h, ← hw, hY]⟩
      refine FactsHold.append (orderFact_sound (strictGap_cases _ _ _) (hpre c hc) fun nk Y hY => ?_)
        (partFact_sound (hpre c hc) fun nk Y hY => ?_)
      · obtain ⟨y, hy | hy, hyc⟩ := hv nk Y hY
        · refine ⟨y, .inl hy.1, hyc, fun h1 => ?_⟩
          have := (strictGap_one h1).2.2; omega
        · refine ⟨y, .inr (by simpa using ha y hy.1), hyc, fun h1 => ?_⟩
          obtain ⟨hs, hl, _⟩ := strictGap_one h1
          exact sort_ne_of_key hl hy.2 (hdist hs y (.inr hy.1) hy.2)
      · obtain ⟨y, hy | hy, hyc⟩ := hv nk Y hY
        · exact ⟨y, .inl hy.1, hyc⟩
        · exact ⟨y, .inr hy.2, hyc⟩
    · intro g hg; simp at hg

theorem winFacts_sound {part : List Nat} {sort : List SortKey} {strict : Bool} {n : Nat}
    {fns : List WinFn} {b a : List Row} {x : Row} (hx : x.length = n)
    (hf : ∀ f ∈ fns, f.refsLt n = true)
    (hb : ∀ y ∈ b, sortLe sort y x = true) (ha : ∀ y ∈ a, sortLe sort x y = true)
    (hdist : strict = true → ∀ y, (y ∈ b ∨ y ∈ a) → samePart part x y = true →
      keyOf (part ++ sort.map (·.col)) y ≠ keyOf (part ++ sort.map (·.col)) x) :
    FactsHold (winFacts part sort strict n fns) (x ++ fns.map (·.value part b a x)) := by
  intro g hg
  simp only [winFacts, List.mem_flatMap] at hg
  obtain ⟨⟨f, t⟩, hft, hg⟩ := hg
  have hget := List.mem_zipIdx_iff_getElem?.mp hft
  refine winFact_sound (hf f (List.mem_of_getElem? hget))
    (fun i hi => getD_append_left' (hx ▸ hi)) ?_ hb ha hdist g hg
  rw [← hx, getD_append_right']
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hget]

/-- The values of `MIN`, `MAX` and integer `AVG` measures of one group: the
bounds `pairFacts` states. -/
theorem pairFacts_sound {ci cj : Nat} {mi mj : Measure} {grp : Relation} {row : Row}
    (hi : row.getD ci .null = mi.eval grp) (hj : row.getD cj .null = mj.eval grp) :
    FactsHold (pairFacts ci cj mi mj) row := by
  -- The measures here do not sort their rows.
  have evi : ∀ f, mi.fn = f → f.sorts = false → mi.eval grp = f.apply (mi.inputs grp) :=
    fun f h hs => by rw [Measure.eval_eq (h ▸ hs), h]
  have evj : ∀ f, mj.fn = f → f.sorts = false → mj.eval grp = f.apply (mj.inputs grp) :=
    fun f h hs => by rw [Measure.eval_eq (h ▸ hs), h]
  -- `MIN` is one of the values and at most each integer among them; `MAX` at least.
  have minle : mi.fn = .min → ∀ {nk : NumKind} {Y}, row.getD ci .null = nk.val Y →
      nk.val Y ∈ mi.inputs grp ∧ ∀ t, nk.val t ∈ mi.inputs grp → Y ≤ t := fun h nk Y hY => by
    rw [hi, evi _ h rfl] at hY
    obtain ⟨hm, hle⟩ := AggFn.apply_min hY (NumKind.val_ne_null nk Y)
    exact ⟨hm, fun t ht => (Value.le_val nk).1 (hle _ ht)⟩
  have maxge : mi.fn = .max → ∀ {nk : NumKind} {X}, row.getD ci .null = nk.val X →
      nk.val X ∈ mi.inputs grp ∧ ∀ t, nk.val t ∈ mi.inputs grp → t ≤ X := fun h nk X hX => by
    rw [hi, evi _ h rfl] at hX
    obtain ⟨hm, hle⟩ := AggFn.apply_max hX (NumKind.val_ne_null nk X)
    exact ⟨hm, fun t ht => (Value.le_val nk).1 (hle _ ht)⟩
  -- An integer `AVG` is an integer between two of its integers.
  have avg : mj.fn = .iavg → ∀ {nk : NumKind} {A}, row.getD cj .null = nk.val A →
      intsOf (mj.inputs grp) ≠ [] →
      nk = .int ∧ (∃ l ∈ intsOf (mj.inputs grp), l ≤ A) ∧ (∃ h ∈ intsOf (mj.inputs grp), A ≤ h) :=
    fun hf nk A hA hne => by
      obtain ⟨a, ha, hl, hh⟩ := AggFn.apply_iavg_between hne
      rw [hj, evj _ hf rfl, ha] at hA
      obtain ⟨rfl, rfl⟩ := NumKind.val_inj₂ (k := .int) hA
      exact ⟨rfl, hl, hh⟩
  -- An integer `AVG` that is not NULL is an integer.
  have iavgKind : mj.fn = .iavg → ∀ {nk : NumKind} {A}, row.getD cj .null = nk.val A → nk = .int :=
    fun hf nk A hA => by
      rw [hj, evj _ hf rfl] at hA
      generalize mj.inputs grp = vs at hA
      cases vs with
      | nil => exact absurd hA.symm (NumKind.val_ne_null nk A)
      | cons v vs => simp only [AggFn.apply] at hA; exact (NumKind.val_inj₂ (k := .int) hA).1.symm
  have ne_of : ∀ {t : Int}, .int t ∈ mj.inputs grp → intsOf (mj.inputs grp) ≠ [] :=
    fun h => List.ne_nil_of_mem (mem_intsOf.2 h)
  have ge0 : ∀ {d : Int}, 0 ≤ d → Bound.Mem ⟨some 0, none⟩ d :=
    fun h => ⟨fun l hl => by cases hl; exact h, fun _ hh => by cases hh⟩
  unfold pairFacts
  split
  · intro f hf; simp at hf
  rename_i hc0
  simp only [not_or, Decidable.not_not] at hc0
  obtain ⟨hfil, harg⟩ := hc0
  have hiff := Measure.mem_inputs_iff harg hfil.symm grp
  split
  · -- `MIN ≤ MAX`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro nk X Y hX hY
    rw [hj, evj _ hfj rfl] at hX
    obtain ⟨hm, -⟩ := AggFn.apply_max hX (NumKind.val_ne_null nk X)
    exact ge0 (by have := (minle hfi hY).2 X ((hiff _).1 hm); omega)
  split
  · -- `MIN ≤ AVG`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro nk A Y hA hY
    obtain rfl := iavgKind hfj hA
    have hY' := minle hfi hY
    obtain ⟨-, ⟨l, hl, hla⟩, -⟩ := avg hfj hA (ne_of ((hiff _).2 hY'.1))
    exact ge0 (by have := hY'.2 l ((hiff _).1 (mem_intsOf.1 hl)); omega)
  split
  · -- `AVG ≤ MAX`
    rename_i hc
    obtain ⟨hfi, hfj⟩ := hc
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    intro nk X A hX hA
    obtain rfl := iavgKind hfj hA
    have hX' := maxge hfi hX
    obtain ⟨-, -, ⟨h, hh, hah⟩⟩ := avg hfj hA (ne_of ((hiff _).2 hX'.1))
    exact ge0 (by have := hX'.2 h ((hiff _).1 (mem_intsOf.1 hh)); omega)
  · intro f hf; simp at hf

theorem aggFacts_sound {g : Nat} {ms : List Measure} {grp : Relation} {k : Row}
    (hk : k.length = g) : FactsHold (aggFacts g ms) (k ++ ms.map (·.eval grp)) := by
  intro f hf
  simp only [aggFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, hi, j, hj, hf⟩ := hf
  have col : ∀ i (m : Measure), ms[i]? = some m →
      (k ++ ms.map (·.eval grp)).getD (g + i) .null = m.eval grp := fun i m h => by
    rw [← hk, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  split at hf
  · rename_i mi mj hmi hmj
    exact pairFacts_sound (col i mi hmi) (col j mj hmj) f hf
  · simp at hf

/-- The facts relating two measures are about measures that do not sort. -/
theorem pairFacts_sorts {ci cj : Nat} {mi mj : Measure} (h : pairFacts ci cj mi mj ≠ []) :
    mi.fn.sorts = false ∧ mj.fn.sorts = false := by
  unfold pairFacts at h
  repeat' split at h
  all_goals first | exact absurd rfl h | (simp_all [AggFn.sorts])

/-- `aggFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem aggFacts_sound_of {g : Nat} {ms : List Measure} {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp) :
    FactsHold (aggFacts g ms) row := by
  intro f hf
  simp only [aggFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    have hs := pairFacts_sorts (List.ne_nil_of_mem hf)
    exact pairFacts_sound (col i mi hmi hs.1) (col j mj hmj hs.2) f hf
  · simp at hf

/-- The measures' columns of an aggregate's row, for `aggFacts_sound_of`. -/
theorem aggCol {ms : List Measure} {grp : Relation} {k : Row} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) :
    ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      (k ++ vs).getD (k.length + i) .null = m.eval grp := by
  intro i m hm hs
  rw [getD_append_right']
  rcases hv.getElem? i with ⟨a, v, ha, hb, hr⟩ | ⟨ha, _⟩
  · rw [hm] at ha; cases ha
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
    obtain ⟨_, _, _, h⟩ := hr.eval
    exact h hs
  · rw [hm] at ha; cases ha

/-- **The facts hold on every row of every order.** -/
theorem Rel.facts_sound_all {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.facts cat F T) row
  | .read t, _, _, h, row, hr => hF t row (h.mem_iff.mp hr)
  | .values _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact (facts_sound_all hcat hF hT hwf.1 hi row hr.1).append (c.factsOf_sound hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      have hfx := facts_sound_all hcat hF hT hwf.1 hi x hx
      have hpre : ∀ i < r.arity cat, (x ++ es.map (·.eval x)).getD i .null = x.getD i .null :=
        fun i hi => getD_append_left' (hlen ▸ hi)
      simp only [Rel.facts]
      refine FactsHold.append ?_ (linFacts_sound hpre _ es fun k hk => ?_)
      · intro g hg
        simp only [List.mem_flatMap, List.mem_filter] at hg
        obtain ⟨f, ⟨hf, hfr⟩, hg⟩ := hg
        exact Fact.rename_holds_inRange (fun i hi p hp => copyCols_getD hlen hi hp) hfr (hfx f hf) g hg
      · rw [← hlen, getD_append_right']
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (facts_sound_all hcat hF hT hwf.1 hi x hx).rename fun i p hp => positions_getD hp
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact ((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2 hy v hv).shift fun i => hlen ▸ getD_append_right' i)
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      simp only [Rel.facts]
      exact (((facts_sound_all hcat hF hT hwf.1 hx u hu).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        ((facts_sound_all hcat hF hT hwf.2.1 hy v hv).shift fun i => hlen ▸ getD_append_right' i)).append
        (on.factsOf_sound ht)
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hlen := orderAllowed_arity hcat hwf.1 hx u hu
      have hfx := facts_sound_all hcat hF hT hwf.1 hx u hu
      simp only [Rel.facts]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (FactsHold.shift_nulls fun i => by
            rw [← hlen, getD_append_right']
            simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)).append
          (FactsHold.rightOf_nulls fun i hi => getD_pad_null (hlen ▸ hi))
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨v, hv, rfl⟩, ht⟩ := h
        exact ((hfx.prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
          (((facts_sound_all hcat hF hT hwf.2.1 hy v hv).filter _).shift
            fun i => hlen ▸ getD_append_right' i)).append
          fun f hf => on.factsOf_sound ht f (List.mem_filter.mp hf).1
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := facts_sound_all hcat hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      facts_sound_all hcat hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      facts_sound_all hcat hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .aggregate _ gs ms, _, _, ⟨_, _, _, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, _, hk, _⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      simp only [Rel.facts]
      exact aggFacts_sound_of (grp := grp) (hkl ▸ aggCol hv)
  | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [Rel.facts] at hf
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      intro f hf
      simp only [Rel.facts, List.mem_filter, List.contains_iff_mem] at hf
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact facts_sound_all hcat hF hT hwf.1 hx row h f hf.1
      · exact facts_sound_all hcat hF hT hwf.2.1 hy row h f hf.2
  | .window r part sort _, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, he, rfl, hb, ha, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hx := hp.mem_iff.mp (hin x (.inl rfl))
      have hlen := orderAllowed_arity hcat hwf.1 hi x hx
      simp only [Rel.facts]
      refine ((facts_sound_all hcat hF hT hwf.1 hi x hx).prefix fun i hi => getD_append_left' (hlen ▸ hi)).append
        (winFacts_sound hlen hwf.2.2.2 hb ha fun hT' y hy _ => ?_)
      -- With a key, rows at different positions of the sorted input differ on it.
      have hk := (hT _ _ _ hT' hwf.1 hi).perm hp.symm fun h => Ne.symm h
      unfold KeyOn at hk
      rw [he, List.pairwise_append, List.pairwise_cons] at hk
      rcases hy with hy | hy
      · exact hk.2.2 y hy x (by simp)
      · exact Ne.symm (hk.2.1.1 y hy)

theorem Rel.facts_sound {cat : Catalog} (hcat : cat.WF) {F : String → List Fact}
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) : ∀ row ∈ r.eval cat, FactsHold (r.facts cat F T) row :=
  Rel.facts_sound_all hcat hF hT hwf (r.eval_orderAllowed cat)

/-- A bound on `x - y` for columns `i` and `j`, from the facts. -/
def Fact.diffBound (i j : Nat) : Fact → Option Bound
  | .diff i' j' b => if i' = i ∧ j' = j then some b else if i' = j ∧ j' = i then some b.neg else none
  | .ne _ _ _ | .ratio _ _ _ | .holds _ => none

/-- What all facts together say about `$i - $j` (`ts_right <= ts` and
`ts_right >= ts - 10` give `0 ≤ ts - ts_right ≤ 10`). -/
def Fact.diffOf (fs : List Fact) (i j : Nat) : Option Bound :=
  match fs.filterMap (Fact.diffBound i j) with
  | [] => none
  | b :: bs => some (bs.foldl Bound.meet b)

/-- A bound on `a - b` for two linear terms, from the facts. -/
def termDiff (fs : List Fact) (a b : Expr) : Option Bound :=
  match a.linTerm, b.linTerm with
  | some (i, c₁), some (j, c₂) => (Fact.diffOf fs i j).map (·.add (.exact (c₁ - c₂)))
  | _, _ => none

/-- The difference, from the facts, within what interval arithmetic gives
(which keeps the bound that shows it fits its width, #202). -/
def subSharpen : Option Bound → AVal → AVal
  | some d, base => { base with int := base.int.map fun b => b.meet d }
  | none, base => base

def ltSharpen : Option Bound → AVal → AVal
  | some d, base => { base with tt := base.tt && canLt d (.exact 0), ff := base.ff && canGe d (.exact 0) }
  | none, base => base

def eqSharpen (d : Bound) (base : AVal) : AVal :=
  { base with tt := base.tt && canEq d (.exact 0), ff := base.ff && canNe d (.exact 0) }

/-- `t = k` cannot be TRUE when a fact excludes the value. -/
def neSharpen (fs : List Fact) (a b : Expr) (base : AVal) : AVal :=
  match a.linTerm, b with
  | some (j, c), .lit w => match w.numOf? with
    | some (kk, k) => if fs.contains (.ne j kk (k - c)) then { base with tt := false } else base
    | none => base
  | _, _ => base

/-- The bound of a `ratio` fact about columns `s` and `c`. -/
def ratioOf (fs : List Fact) (s c : Nat) : Option Bound :=
  fs.findSome? fun | .ratio s' c' b => if s' = s ∧ c' = c then some b else none | _ => none

/-- A decimal `AVG`, `ddiv(sum · 10ᵏ, count)`, is within its values' bound,
scaled (#237). -/
def ratioSharpen (fs : List Fact) (a b : Expr) (base : AVal) : AVal :=
  match a, b with
  | .bin .dmul (.field s) (.lit (.int k)), .field c =>
    match ratioOf fs s c with
    | some bd =>
      if 0 < k then { base with int := base.int.map (·.meet ⟨bd.lo.map (· * k), bd.hi.map (· * k)⟩) }
      else base
    | none => base
  | _, _ => base

/-- Sharpen the abstract result of `f a b` using facts about `a` and `b`
(`aa` is the abstract value of `a`). -/
def sharpen (fs : List Fact) (f : BinFn) (a b : Expr) (aa ab base : AVal) : AVal :=
  match f with
  | .ddiv => ratioSharpen fs a b base
  -- A fact bounds the difference of two numbers of one kind only.
  | .sub => if sameNk aa ab then subSharpen (termDiff fs a b) base else base
  -- Facts are about integers; strings compare by themselves.
  | .lt => if aa.intsOnly then ltSharpen (termDiff fs a b) base else base
  | .eq =>
      match termDiff fs a b with
      | some d => if aa.intsOnly then eqSharpen d base else base
      | none => neSharpen fs a b base
  | _ => base

/-- `FALSE OR v`: `v` if it is a boolean, else NULL. -/
def AVal.orFalse (a : AVal) : AVal := { null := a.nonBool, tt := a.tt, ff := a.ff }

/-- `p OR q` for a boolean `p`: TRUE where `p` is, else `q` on rows where
`NOT p` holds (`bq` is `q` under that refinement). This proves guarded
conditions such as `prev IS NULL OR prev <= ts`. -/
def orSplit (ap bq : AVal) : AVal :=
  (if ap.tt then AVal.ofValue (.bool true) else AVal.bot).join (if ap.ff then bq.orFalse else AVal.bot)

/-- An interval with values in it. -/
def Bound.nonEmpty (b : Bound) : Bool :=
  match b.lo, b.hi with
  | some l, some h => decide (l ≤ h)
  | _, _ => true

/-- `a` without an empty interval: such a value is no integer. -/
def AVal.prune (a : AVal) : AVal := { a with int := a.int.filter Bound.nonEmpty }

theorem AVal.prune_mem {a : AVal} {v : Value} (h : a.Mem v) : a.prune.Mem v := by
  cases hv : v.numOf? with
  | none => cases v <;> (try rename_i bb; cases bb) <;> simp_all [AVal.Mem, AVal.prune, Value.numOf?]
  | some p =>
    obtain ⟨k, i⟩ := p
    rw [Value.numOf?_some hv] at h ⊢
    obtain ⟨b, hb, hm, hk⟩ := AVal.mem_val.mp h
    rw [AVal.mem_val]
    refine ⟨b, ?_, hm, hk⟩
    have : b.nonEmpty = true := by
      unfold Bound.nonEmpty
      split
      · rename_i l h hl hh
        exact decide_eq_true (Int.le_trans (hm.1 l hl) (hm.2 h hh))
      · rfl
    simp [AVal.prune, hb, Option.filter, this]

theorem EnvMem.prune {env : List AVal} {row : Row} (h : EnvMem env row) :
    EnvMem (env.map AVal.prune) row := by
  intro i
  have htop : AVal.top.prune = AVal.top := by
    simp [AVal.prune, AVal.top, Bound.top, Option.filter, Bound.nonEmpty]
  have := AVal.prune_mem (h i)
  rw [← htop] at this ⊢
  cases hi : env[i]? <;> simp_all [List.getD_eq_getElem?_getD]

/-- `NULL OR v`: TRUE where `v` is, else NULL. -/
def AVal.orNull (a : AVal) : AVal := { null := a.nonBool || a.ff, tt := a.tt }

/-- `p OR q` for a `p` that is a boolean or NULL: as `orSplit`, and where `p`
is NULL, TRUE only where `q` is (`bq` is `q` where `p` is not TRUE). This
proves `x >= 0 OR x IS NULL` for a column `x` that may be NULL. -/
def orSplitNull (ap bq : AVal) : AVal :=
  (orSplit ap bq).join (if ap.null then bq.orNull else AVal.bot)

def Expr.absD (env : List AVal) (fs : List Fact) (ks : Assumptions := []) : Expr → AVal
  | .lit v => AVal.ofValue v
  | .field i => narrowAll ks (.field i) (env.getD i AVal.top)
  | .un f a => narrowAll ks (.un f a) (f.abs (a.absD env fs ks))
  | .bin f a b => narrowAll ks (.bin f a b) <|
      if f = .or ∧ (a.absD env fs ks).nonBool = false then
        orSplit (a.absD env fs ks)
          (b.absD (useFacts fs ((Expr.un .not a).refine env)) fs (a.cstrs false ++ ks))
      else if f = .or ∧ (a.absD env fs ks).int.isNone = true ∧ (a.absD env fs ks).str = false ∧
          (a.absD env fs ks).nested = false then
        orSplitNull (a.absD env fs ks)
          (b.absD (useFacts fs ((a.refineNeg env).map AVal.prune)) fs (a.cstrs false ++ ks))
      else sharpen fs f a b (a.absD env fs ks) (b.absD env fs ks)
        (f.abs (a.absD env fs ks) (b.absD env fs ks))
  -- Each branch is evaluated knowing whether `c` is TRUE.
  | .ifThen c t e => narrowAll ks (.ifThen c t e) <|
      let ac := c.absD env fs ks
      (if ac.tt then t.absD (useFacts fs (c.refine env)) fs (c.cstrs true ++ ks) else AVal.bot).join
        (if ac.nonBool || ac.ff then e.absD (useFacts fs (c.refineNeg env)) fs (c.cstrs false ++ ks)
         else AVal.bot)
  -- The body over an element of the list, without the row's facts and
  -- assumptions, which name the row's columns (#925).
  | .hof f l b => narrowAll ks (.hof f l b) <|
      let al := l.absD env fs ks
      f.abs al (b.absD (al.elemsOf :: env) [] [])

theorem Bound.mem_exact_iff {k i : Int} : (Bound.exact k).Mem i ↔ i = k := by
  simp only [Bound.Mem, Bound.exact, Option.some.injEq]
  constructor
  · intro ⟨h₁, h₂⟩; have := h₁ k rfl; have := h₂ k rfl; omega
  · rintro rfl; constructor <;> intro _ h <;> subst h <;> omega

theorem canLt_of_lt {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : i < j) :
    canLt x y = true := by
  obtain ⟨xl, xh⟩ := x
  obtain ⟨yl, yh⟩ := y
  simp only [Bound.Mem] at hx hy
  unfold canLt
  cases xl <;> cases yh <;> simp_all <;> omega

theorem canNe_of_ne {x y : Bound} {i j : Int} (hx : x.Mem i) (hy : y.Mem j) (h : i ≠ j) :
    canNe x y = true := by
  unfold canNe
  split
  · rename_i k k' hk hk'
    rw [← Bound.point_mem hk hx, ← Bound.point_mem hk' hy]
    simpa using h
  · rfl

theorem Fact.diffBound_sound {f : Fact} {row : Row} {i j : Nat} {d : Bound} {k : NumKind} {x y : Int}
    (hg : f.diffBound i j = some d) (hh : f.Holds row)
    (hx : row.getD i .null = k.val x) (hy : row.getD j .null = k.val y) : d.Mem (x - y) := by
  cases f with
  | ne _ _ _ | ratio _ _ _ | holds _ => simp [Fact.diffBound] at hg
  | diff i' j' b =>
    simp only [Fact.diffBound] at hg
    split at hg
    · rename_i h; obtain ⟨rfl, rfl⟩ := h
      cases hg; exact hh k x y hx hy
    · split at hg
      · rename_i _ h; obtain ⟨rfl, rfl⟩ := h
        cases hg
        have := Bound.mem_neg (hh k y x hy hx)
        simpa [Int.neg_sub] using this
      · cases hg

theorem foldl_meet_mem {z : Int} : ∀ {bs : List Bound} {b : Bound}, b.Mem z →
    (∀ b' ∈ bs, b'.Mem z) → (bs.foldl Bound.meet b).Mem z
  | [], _, hb, _ => hb
  | b' :: bs, _, hb, h => by
      rw [List.foldl_cons]
      exact foldl_meet_mem (Bound.mem_meet hb (h b' (by simp))) fun c hc => h c (by simp [hc])

theorem Fact.diffOf_sound {fs : List Fact} {row : Row} {i j : Nat} {d : Bound} {k : NumKind} {x y : Int}
    (hd : Fact.diffOf fs i j = some d) (hfs : FactsHold fs row)
    (hx : row.getD i .null = k.val x) (hy : row.getD j .null = k.val y) : d.Mem (x - y) := by
  have hall : ∀ b ∈ fs.filterMap (Fact.diffBound i j), b.Mem (x - y) := by
    intro b hb
    obtain ⟨f, hf, hg⟩ := List.mem_filterMap.mp hb
    exact Fact.diffBound_sound hg (hfs f hf) hx hy
  unfold Fact.diffOf at hd
  split at hd
  · cases hd
  · rename_i b bs h
    cases hd
    rw [h] at hall
    exact foldl_meet_mem (hall b (by simp)) fun c hc => hall c (by simp [hc])

theorem termDiff_sound {fs : List Fact} {row : Row} {a b : Expr} {d : Bound} {k : NumKind} {u w : Int}
    (hd : termDiff fs a b = some d) (hfs : FactsHold fs row)
    (hu : a.eval row = k.val u) (hw : b.eval row = k.val w) : d.Mem (u - w) := by
  unfold termDiff at hd
  split at hd
  · rename_i i c₁ j c₂ h₁ h₂
    obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨x, hx, rfl⟩ := Expr.linTerm_of_num h₁ hu
    obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_num h₂ hw
    have := Bound.mem_add (Fact.diffOf_sound hd₀ hfs hx hy) (Bound.mem_exact (c₁ - c₂))
    have heq : x + c₁ - (y + c₂) = x - y + (c₁ - c₂) := by omega
    rw [heq]; exact this
  · cases hd

theorem BinFn.sub_other_left {v w : Value} (hv : v.numOf? = none) : BinFn.apply .sub v w = .null := by
  cases v <;> simp only [Value.numOf?, reduceCtorEq] at hv <;> cases w <;> rfl

theorem BinFn.sub_other_right (k : NumKind) (i : Int) {w : Value} (hw : w.numOf? = none) :
    BinFn.apply .sub (k.val i) w = .null := by
  cases w <;> simp only [Value.numOf?, reduceCtorEq] at hw <;> cases k <;> rfl

/-- Two numbers of abstractions of one kind are of that kind. -/
theorem sameNk_kinds {aa ab : AVal} (hs : sameNk aa ab = true) {k k' : NumKind} {x y : Int}
    (ha : aa.Mem (k.val x)) (hb : ab.Mem (k'.val y)) : k = k' := by
  obtain ⟨_, _, _, hk⟩ := AVal.mem_val.mp ha
  obtain ⟨_, _, _, hk'⟩ := AVal.mem_val.mp hb
  unfold sameNk at hs
  cases hA : aa.nk <;> cases hB : ab.nk <;> simp_all

theorem subSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {aa ab base : AVal}
    (hfs : FactsHold fs row) (hs : sameNk aa ab = true) (haa : aa.Mem (a.eval row))
    (hab : ab.Mem (b.eval row))
    (hbase : base.Mem (BinFn.apply .sub (a.eval row) (b.eval row))) :
    (subSharpen (termDiff fs a b) base).Mem (BinFn.apply .sub (a.eval row) (b.eval row)) := by
  cases hd : termDiff fs a b with
  | none => exact hbase
  | some d =>
    simp only [subSharpen]
    cases hva : (a.eval row).numOf? with
    | none =>
      rw [BinFn.sub_other_left hva] at hbase ⊢; exact hbase
    | some p =>
      obtain ⟨k, u⟩ := p
      cases hvb : (b.eval row).numOf? with
      | none =>
        rw [Value.numOf?_some hva, BinFn.sub_other_right k u hvb] at hbase ⊢; exact hbase
      | some q =>
        obtain ⟨k', w⟩ := q
        have hu := Value.numOf?_some hva
        have hw := Value.numOf?_some hvb
        rw [hu] at haa; rw [hw] at hab
        obtain rfl := sameNk_kinds hs haa hab
        rw [hu, hw] at hbase ⊢
        have hm := termDiff_sound hd hfs hu hw
        -- `a - b` of one kind: an integer `u - w`, or NULL (doubles, decimals).
        cases k <;> simp only [BinFn.apply, NumKind.val] at hbase ⊢ <;> try exact hbase
        all_goals
          obtain ⟨b₀, hb₀, hb₀m, hk₀⟩ := hbase
          exact ⟨b₀.meet d, by simp [hb₀], Bound.mem_meet hb₀m hm, hk₀⟩

/-- A value of an abstraction with no booleans or strings that is not a
number is NULL. -/
theorem AVal.null_of_intsOnly {aa : AVal} {v : Value} (hint : aa.intsOnly = true) (h : aa.Mem v)
    (hv : v.numOf? = none) : v = .null := by
  simp only [AVal.intsOnly, AVal.nested, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hint
  cases v <;> (try rename_i bb; cases bb) <;> simp_all [AVal.Mem, Value.numOf?]

theorem ltSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {aa base : AVal}
    (hfs : FactsHold fs row) (hint : aa.intsOnly = true) (haa : aa.Mem (a.eval row))
    (hbase : base.Mem (BinFn.apply .lt (a.eval row) (b.eval row))) :
    (ltSharpen (termDiff fs a b) base).Mem (BinFn.apply .lt (a.eval row) (b.eval row)) := by
  cases hd : termDiff fs a b with
  | none => exact hbase
  | some d =>
    simp only [ltSharpen]
    cases hva : (a.eval row).numOf? with
    | some p =>
      obtain ⟨k, u⟩ := p
      cases hvb : (b.eval row).numOf? with
      | some q =>
        obtain ⟨k', w⟩ := q
        have hu := Value.numOf?_some hva
        have hw := Value.numOf?_some hvb
        rw [hu, hw, BinFn.lt_vals] at hbase ⊢
        split
        · rename_i hkk; subst hkk
          rw [ite_eq_left_of_eq_true _ _ (eq_self k)] at hbase
          have hm := termDiff_sound hd hfs hu hw
          by_cases hlt : u < w
          · simp only [hlt, decide_true, AVal.Mem, AVal.MemR, Bool.cond_true] at hbase ⊢
            simp [hbase, canLt_of_lt hm (Bound.mem_exact 0) (by omega)]
          · simp only [hlt, decide_false, AVal.Mem, AVal.MemR, Bool.cond_false] at hbase ⊢
            simp [hbase, canGe_of_le hm (Bound.mem_exact 0) (by omega)]
        · rename_i hkk; rw [ite_eq_right_of_eq_false _ _ (eq_false hkk)] at hbase; exact hbase
      | none =>
        rw [Value.numOf?_some hva, BinFn.cmp_num_other (.inr rfl) k u hvb] at hbase ⊢; exact hbase
    | none =>
      -- Not a number: NULL, whose comparison is NULL.
      rw [AVal.null_of_intsOnly hint haa hva] at hbase ⊢
      have : BinFn.apply .lt .null (b.eval row) = .null := by
        cases b.eval row <;> simp [BinFn.apply, Value.numPair]
      rw [this] at hbase ⊢; exact hbase

theorem BinFn.eq_bool_or_null (v w : Value) :
    BinFn.apply .eq v w = .null ∨ ∃ b, BinFn.apply .eq v w = .bool b := by
  cases v <;> cases w <;> simp only [BinFn.apply, Value.numPair] <;> (try split) <;> simp

theorem BinFn.ddiv_int_or_null (v w : Value) :
    BinFn.apply .ddiv v w = .null ∨ ∃ q, BinFn.apply .ddiv v w = .int q := by
  simp only [BinFn.apply]; split <;> (try split) <;> simp

theorem eqSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {aa base : AVal} {d : Bound}
    (hfs : FactsHold fs row) (hd : termDiff fs a b = some d) (hint : aa.intsOnly = true)
    (haa : aa.Mem (a.eval row)) (hbase : base.Mem (BinFn.apply .eq (a.eval row) (b.eval row))) :
    (eqSharpen d base).Mem (BinFn.apply .eq (a.eval row) (b.eval row)) := by
  simp only [eqSharpen]
  cases hva : (a.eval row).numOf? with
  | some p =>
    obtain ⟨k, u⟩ := p
    cases hvb : (b.eval row).numOf? with
    | some q =>
      obtain ⟨k', w⟩ := q
      have hu := Value.numOf?_some hva
      have hw := Value.numOf?_some hvb
      rw [hu, hw, BinFn.eq_vals] at hbase ⊢
      split
      · rename_i hkk; subst hkk
        rw [ite_eq_left_of_eq_true _ _ (eq_self k)] at hbase
        have hm := termDiff_sound hd hfs hu hw
        by_cases huw : u = w
        · subst huw
          simp only [beq_self_eq_true, AVal.Mem, AVal.MemR, Bool.cond_true] at hbase ⊢
          simp [hbase, canEq, canGe_of_le hm (Bound.mem_exact 0) (by omega),
            canGe_of_le (Bound.mem_exact 0) hm (by omega)]
        · have hne : (u == w) = false := by simpa using huw
          simp only [hne, AVal.Mem, AVal.MemR, Bool.cond_false] at hbase ⊢
          simp [hbase, canNe_of_ne hm (Bound.mem_exact 0) (by omega)]
      · rename_i hkk; rw [ite_eq_right_of_eq_false _ _ (eq_false hkk)] at hbase; exact hbase
    | none =>
      rw [Value.numOf?_some hva, BinFn.cmp_num_other (.inl rfl) k u hvb] at hbase ⊢; exact hbase
  | none =>
    rw [AVal.null_of_intsOnly hint haa hva] at hbase ⊢
    have : BinFn.apply .eq .null (b.eval row) = .null := by
      cases b.eval row <;> simp [BinFn.apply, Value.numPair]
    rw [this] at hbase ⊢; exact hbase

theorem neSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .eq (a.eval row) (b.eval row))) :
    (neSharpen fs a b base).Mem (BinFn.apply .eq (a.eval row) (b.eval row)) := by
  unfold neSharpen
  split
  · rename_i _ j c w hl
    split
    · rename_i kk k hw
      split
      · rename_i hne
        have hh := hfs _ (List.contains_iff_mem.mp hne)
        have hb : (Expr.lit w).eval row = kk.val k := Value.numOf?_some hw
        rw [hb] at hbase ⊢
        -- The comparison is not TRUE: a TRUE one makes `a` the excluded value.
        generalize hv : BinFn.apply .eq (a.eval row) (kk.val k) = v at hbase ⊢
        cases v with
        | bool r =>
          cases r
          · simpa [AVal.Mem] using hbase
          · exfalso
            have hx := eq_num (v := a.eval row) (by rw [hv]; rfl)
            obtain ⟨y, hy, rfl⟩ := Expr.linTerm_of_num hl hx
            exact hh (by rw [hy]; congr 1; omega)
        | null => exact hbase
        | _ =>
          exfalso
          rcases BinFn.eq_bool_or_null (a.eval row) (kk.val k) with h | ⟨r, h⟩ <;> rw [hv] at h <;>
            cases h
      · exact hbase
    · exact hbase
  · exact hbase

theorem ratioOf_mem {fs : List Fact} {s c : Nat} {b : Bound} (h : ratioOf fs s c = some b) :
    Fact.ratio s c b ∈ fs := by
  obtain ⟨f, hf, he⟩ := List.exists_of_findSome?_eq_some h
  cases f <;> simp at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  exact hf

theorem BinFn.dmul_ddiv {v w : Value} {k q : Int}
    (h : BinFn.apply .ddiv (BinFn.apply .dmul v (.int k)) w = .int q) :
    ∃ x n, v.unscaled? = some x ∧ w.unscaled? = some n ∧ roundDivInt? (x * k) n = some q := by
  cases hv : v.unscaled? with
  | none =>
    have : BinFn.apply .dmul v (.int k) = .null := by
      cases v <;> simp_all [BinFn.apply, Value.unscaled?]
    rw [this] at h; cases w <;> simp [BinFn.apply] at h
  | some x =>
    have : BinFn.apply .dmul v (.int k) = .int (x * k) := by
      cases v <;> simp_all [BinFn.apply, Value.unscaled?]
    rw [this] at h
    cases hw : w.unscaled? with
    | none => cases w <;> simp_all [BinFn.apply, Value.unscaled?]
    | some n =>
      refine ⟨x, n, rfl, rfl, ?_⟩
      cases w <;> simp_all [BinFn.apply, Value.unscaled?]
      all_goals (split at h <;> simp_all)

theorem ratioSharpen_sound {fs : List Fact} {row : Row} {a b : Expr} {base : AVal}
    (hfs : FactsHold fs row) (hbase : base.Mem (BinFn.apply .ddiv (a.eval row) (b.eval row))) :
    (ratioSharpen fs a b base).Mem (BinFn.apply .ddiv (a.eval row) (b.eval row)) := by
  unfold ratioSharpen
  split
  · rename_i s k c
    split
    · rename_i bd hbd
      split
      · rename_i hk
        -- Only the integer part changes, and `ddiv` gives an integer or NULL.
        generalize hv : BinFn.apply .ddiv _ _ = v at hbase ⊢
        cases v with
        | int q =>
          obtain ⟨B, hB, hq, hnk⟩ := hbase
          refine ⟨B.meet ⟨bd.lo.map (· * k), bd.hi.map (· * k)⟩, by simp [hB], Bound.mem_meet hq ?_, hnk⟩
          obtain ⟨x, n, hx, hn, hr⟩ := BinFn.dmul_ddiv hv
          have hn0 : n ≠ 0 := by intro h0; subst h0; simp [roundDivInt?] at hr
          obtain ⟨hpos, hlo, hhi⟩ := hfs _ (ratioOf_mem hbd) x n hx hn
          have hrd : roundDiv (x * k) n = q := by simp [roundDiv, hr]
          obtain ⟨hL, hH⟩ := roundDiv_bounds (a := x * k) hpos
          constructor
          · intro l hl
            obtain ⟨l0, hl0, rfl⟩ := Option.map_eq_some_iff.mp hl
            rw [← hrd]; apply hL
            have := Int.mul_le_mul_of_nonneg_right (hlo l0 hl0) (Int.le_of_lt hk)
            rwa [Int.mul_assoc] at this
          · intro h hh
            obtain ⟨h0, hh0, rfl⟩ := Option.map_eq_some_iff.mp hh
            rw [← hrd]; apply hH
            have := Int.mul_le_mul_of_nonneg_right (hhi h0 hh0) (Int.le_of_lt hk)
            rwa [Int.mul_assoc] at this
        | null => exact hbase
        | _ =>
          exfalso
          rcases BinFn.ddiv_int_or_null (Expr.eval row (.bin .dmul (.field s) (.lit (.int k))))
            ((Expr.field c).eval row) with h | ⟨r, h⟩ <;> rw [hv] at h <;> cases h
      · exact hbase
    · exact hbase
  · exact hbase

theorem sharpen_sound {fs : List Fact} {row : Row} (f : BinFn) (a b : Expr) {aa ab base : AVal}
    (hfs : FactsHold fs row) (haa : aa.Mem (a.eval row)) (hab : ab.Mem (b.eval row))
    (hbase : base.Mem (f.apply (a.eval row) (b.eval row))) :
    (sharpen fs f a b aa ab base).Mem (f.apply (a.eval row) (b.eval row)) := by
  cases f
  case ddiv => exact ratioSharpen_sound hfs hbase
  case sub =>
    simp only [sharpen]
    split
    · rename_i hs; exact subSharpen_sound hfs hs haa hab hbase
    · exact hbase
  case lt =>
    simp only [sharpen]
    split
    · rename_i hint; exact ltSharpen_sound hfs hint haa hbase
    · exact hbase
  case eq =>
    simp only [sharpen]
    cases hd : termDiff fs a b with
    | none => exact neSharpen_sound hfs hbase
    | some d =>
      simp only []
      split
      · rename_i hint; exact eqSharpen_sound hfs hd hint haa hbase
      · exact hbase
  all_goals exact hbase

theorem Expr.absD_sound {env : List AVal} {fs : List Fact} {ks : Assumptions} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (hks : KsHold ks row) :
    ∀ e : Expr, (e.absD env fs ks).Mem (e.eval row)
  | .lit v => AVal.mem_ofValue v
  | .field i => narrowAll_sound hks (h i)
  | .un f a => narrowAll_sound hks (UnFn.abs_sound f (Expr.absD_sound h hfs hks a))
  | .bin f a b => by
      simp only [absD]
      refine narrowAll_sound hks ?_
      simp only [eval]
      split
      · rename_i hc
        obtain ⟨rfl, hnb⟩ := hc
        have ha := Expr.absD_sound h hfs hks a
        rcases AVal.mem_cases ha with ⟨_, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
        · simp [AVal.nonBool, hn] at hnb
        · simp [AVal.nonBool, hb] at hnb
        · rw [hv]
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hr := Expr.refine_sound env (.un .not a) h (by simp [eval, hv, UnFn.apply, Value.isTrue])
          have hks' := KsHold.cons_cstrs (c := a) (pos := false)
            (by simp [hv, Value.isTrue]) hks
          have hq := Expr.absD_sound (useFacts_sound hfs hr) hfs hks' b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases AVal.mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ | ⟨_, hv', hs⟩ | ⟨_, hv' | hv', hs⟩ <;>
            rw [hv'] <;> (try cases ‹NumKind›) <;>
            simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem, NumKind.val, AVal.MemNum, AVal.nonBool,
              AVal.nested]
        · simp [AVal.nonBool, hs] at hnb
        · simp [AVal.nonBool, hs] at hnb
      split
      · rename_i _ hc
        obtain ⟨rfl, hni, hns, hnn⟩ := hc
        have ha := Expr.absD_sound h hfs hks a
        rcases AVal.mem_cases ha with ⟨hv, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, ht⟩ | ⟨hv, hf⟩ | ⟨_, _, hs⟩ |
            ⟨_, _, hs⟩
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env a h hnt).prune) hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_right
          rw [ite_eq_left hn]
          rcases AVal.mem_cases hq with ⟨hv', hn'⟩ | ⟨_, _, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
              ⟨_, hv', hs⟩ | ⟨_, hv' | hv', hs⟩ <;>
            rw [hv'] <;> (try cases ‹NumKind›) <;>
            simp_all [BinFn.apply, or3, AVal.orNull, AVal.Mem, NumKind.val, AVal.MemNum, AVal.nonBool,
              AVal.nested]
        · simp [hb] at hni
        · rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_left
          rw [ite_eq_left ht]
          exact AVal.mem_ofValue _
        · have hnt : (a.eval row).isTrue = false := by simp [hv, Value.isTrue]
          have hq := Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env a h hnt).prune) hfs
            (KsHold.cons_cstrs (c := a) (pos := false) hnt hks) b
          rw [hv]
          apply AVal.mem_join_left
          apply AVal.mem_join_right
          rw [ite_eq_left hf]
          rcases AVal.mem_cases hq with ⟨hv', hn⟩ | ⟨_, _, _, hv', hb, _⟩ | ⟨hv', ht⟩ | ⟨hv', hf'⟩ |
              ⟨_, hv', hs⟩ | ⟨_, hv' | hv', hs⟩ <;>
            rw [hv'] <;> (try cases ‹NumKind›) <;>
            simp_all [BinFn.apply, or3, AVal.orFalse, AVal.Mem, NumKind.val, AVal.MemNum, AVal.nonBool,
              AVal.nested]
        · simp [hs] at hns
        · simp [hs] at hnn
      · exact sharpen_sound f a b hfs (Expr.absD_sound h hfs hks a) (Expr.absD_sound h hfs hks b)
          (BinFn.abs_sound f (Expr.absD_sound h hfs hks a) (Expr.absD_sound h hfs hks b))
  | .ifThen c t e => by
      have hc := Expr.absD_sound h hfs hks c
      simp only [absD]
      refine narrowAll_sound hks ?_
      simp only [eval]
      by_cases hct : (c.eval row).isTrue = true
      · rw [ite_eq_left hct]
        rw [Value.eq_true_of_isTrue hct] at hc
        have htt : (c.absD env fs ks).tt = true := hc
        apply AVal.mem_join_left
        rw [ite_eq_left htt]
        exact Expr.absD_sound (useFacts_sound hfs (Expr.refine_sound env c h hct)) hfs
          (KsHold.cons_cstrs hct hks) t
      · rw [ite_eq_right hct]
        apply AVal.mem_join_right
        have : ((c.absD env fs ks).nonBool || (c.absD env fs ks).ff) = true := by
          rcases AVal.mem_cases hc with ⟨_, hn⟩ | ⟨_, _, _, _, hb, _⟩ | ⟨hv, _⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ |
            ⟨_, _, hs⟩
          · simp [AVal.nonBool, hn]
          · simp [AVal.nonBool, hb]
          · rw [hv] at hct; simp [Value.isTrue] at hct
          · simp [hf]
          · simp [AVal.nonBool, hs]
          · simp [AVal.nonBool, hs]
        rw [ite_eq_left this]
        have hf : (c.eval row).isTrue = false := by simpa using hct
        exact Expr.absD_sound (useFacts_sound hfs (Expr.refineNeg_sound env c h hf)) hfs
          (KsHold.cons_cstrs hf hks) e
  | .hof f l b => narrowAll_sound hks
      (HoFn.abs_sound f (Expr.absD_sound h hfs hks l) fun _ hx =>
        Expr.absD_sound (h.cons hx) (by simp [FactsHold]) (by simp [KsHold]) b)

/-- `absD`, and TRUE for a condition the facts carry whole (#597): an
`ensures` that restates a `requires` the plan keeps. -/
def Expr.absF (env : List AVal) (fs : List Fact) (e : Expr) : AVal :=
  if fs.contains (.holds e) then AVal.ofValue (.bool true) else e.absD env fs

theorem Expr.absF_sound {env : List AVal} {fs : List Fact} {row : Row}
    (h : EnvMem env row) (hfs : FactsHold fs row) (e : Expr) :
    (e.absF env fs).Mem (e.eval row) := by
  unfold absF
  split
  · rename_i hc
    have ht : (e.eval row).isTrue = true := hfs _ (List.contains_iff_mem.mp hc)
    rw [Value.eq_true_of_isTrue ht]; exact AVal.mem_ofValue _
  · exact Expr.absD_sound h hfs (ks := []) (by simp [KsHold]) e

end Substrait
