import SubstraitLean.Contracts.Plan

/-!
# Contracts: Sound

Soundness of abstract plan evaluation (`Rel.aeval_sound`,
`Rel.aeval_sound_all`) and the contract theorems `contract_sound_all` and
`contract_sound`.

Part of `SubstraitLean.Contracts`, which re-exports it. -/

namespace Substrait

theorem EnvMem.append {e₁ e₂ : List AVal} {r₁ r₂ : Row} (h₁ : EnvMem e₁ r₁) (h₂ : EnvMem e₂ r₂)
    (hl : e₁.length = r₁.length) : EnvMem (e₁ ++ e₂) (r₁ ++ r₂) := by
  intro j
  have := h₁ j; have := h₂ (j - r₁.length)
  simp only [List.getD_eq_getElem?_getD] at *
  by_cases hj : j < e₁.length
  · rwa [List.getElem?_append_left hj, List.getElem?_append_left (hl ▸ hj)]
  · rwa [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

theorem EnvMem.map {env : List AVal} {row : Row} (h : EnvMem env row) (es : List Expr) :
    EnvMem (es.map (·.abs env)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.abs_sound h]

theorem EnvMem.mapD {env : List AVal} {fs : List Fact} {row : Row} (h : EnvMem env row)
    (hfs : FactsHold fs row) (es : List Expr) :
    EnvMem (es.map (·.absD env fs)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.absD_sound h hfs (ks := []) (by simp [KsHold])]

theorem EnvMem.mapF {env : List AVal} {fs : List Fact} {row : Row} (h : EnvMem env row)
    (hfs : FactsHold fs row) (es : List Expr) :
    EnvMem (es.map (·.absF env fs)) (es.map (·.eval row)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases es[j]? <;> simp [AVal.mem_top, Expr.absF_sound h hfs]

theorem EnvMem.emit {env : List AVal} {row : Row} (h : EnvMem env row) (m : List Nat) :
    EnvMem (m.map (env.getD · AVal.top)) (m.map (row.getD · .null)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hm : m[j]? <;> simp [AVal.mem_top]
  have := h ‹Nat›
  simpa [getD_top_eq, List.getD_eq_getElem?_getD] using this

theorem EnvMem.fit {env : List AVal} {row : Row} (h : EnvMem env row) (n : Nat) :
    EnvMem (fit n env) row := by
  intro j
  simp only [_root_.Substrait.fit, getD_top_eq, List.getElem?_map]
  by_cases hj : j < n
  · simpa [hj, getD_top_eq] using h j
  · simp [hj, AVal.mem_top]

theorem EnvMem.replicate (n : Nat) (row : Row) : EnvMem (List.replicate n AVal.top) row := by
  intro j
  simp only [getD_top_eq, List.getElem?_replicate]
  split <;> simp [AVal.mem_top]

/-- An element of a list in column `c` in its place, as `UNNEST` gives it (#925). -/
theorem EnvMem.set_elem {env : List AVal} {row : Row} (h : EnvMem env row) {c : Nat}
    {vs : List Value} {v : Value} (hc : row.getD c .null = .list vs) (hv : v ∈ vs) :
    EnvMem (env.set c (env.getD c AVal.top).elemsOf) (row.set c v) := by
  intro j
  by_cases hj : c = j
  · subst hj
    have hm := h c
    rw [hc] at hm
    have he := (AVal.mem_list.mp hm).2.2 v hv
    have hlt : c < row.length := by
      rcases Nat.lt_or_ge c row.length with hl | hl
      · exact hl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hc; cases hc
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hlt, Option.getD_some]
    by_cases he' : c < env.length
    · simpa [List.getElem?_set_self he', List.getD_eq_getElem?_getD] using he
    · simp only [List.getElem?_set, show ¬c < env.length from he', ↓reduceIte]
      exact AVal.mem_top _
  · have := h j
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hj] using this

theorem EnvMem.nullable {env : List AVal} {row : Row} (h : EnvMem env row) :
    EnvMem (env.map AVal.nullable) row := by
  intro j
  have := h j
  simp only [getD_top_eq, List.getElem?_map] at *
  cases hj : env[j]? with
  | none => simp [AVal.mem_top]
  | some a =>
    simp only [hj, Option.map_some, Option.getD_some] at this ⊢
    exact AVal.mem_nullable this

theorem EnvMem.nulls (env : List AVal) (m : Nat) :
    EnvMem (env.map AVal.nullable) (List.replicate m .null) := by
  intro j
  simp only [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  cases env[j]? <;> split <;> simp [AVal.top, AVal.nullable, AVal.Mem]

theorem intSum_cons (v : Value) (vs : List Value) :
    intSum (v :: vs) = v.unscaled?.getD 0 + intSum vs := by
  cases v <;> simp [intSum]

theorem sumOf_unscaled {vs : List Value} {x : Int} (h : (sumOf vs).unscaled? = some x) :
    x = intSum vs := by
  rcases sumOf_cases vs with ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e] at h <;>
    simp_all [Value.unscaled?]

theorem intSum_nonneg : ∀ {vs : List Value}, (∀ v ∈ vs, ∀ i, v.unscaled? = some i → 0 ≤ i) →
    0 ≤ intSum vs
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    have := intSum_nonneg (vs := vs) fun w hw => h w (List.mem_cons_of_mem _ hw)
    rw [intSum_cons]
    cases hv : v.unscaled? with
    | none => simp; omega
    | some i => have := h v (by simp) i hv; simp; omega

theorem intSum_nonpos : ∀ {vs : List Value}, (∀ v ∈ vs, ∀ i, v.unscaled? = some i → i ≤ 0) →
    intSum vs ≤ 0
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    have := intSum_nonpos (vs := vs) fun w hw => h w (List.mem_cons_of_mem _ hw)
    rw [intSum_cons]
    cases hv : v.unscaled? with
    | none => simp; omega
    | some i => have := h v (by simp) i hv; simp; omega

theorem sumBound_sound {b : Bound} {vs : List Value}
    (h : ∀ v ∈ vs, ∀ i, v.unscaled? = some i → b.Mem i) :
    (sumBound b).Mem (intSum vs) := by
  constructor
  · intro l hl
    cases hb : b.lo with
    | none => simp [sumBound, hb] at hl
    | some l₀ =>
      simp only [sumBound, hb, Option.bind_some] at hl
      split at hl
      · cases hl; exact intSum_nonneg fun v hv i hi => by have := (h v hv i hi).1 l₀ hb; omega
      · cases hl
  · intro u hu
    cases hb : b.hi with
    | none => simp [sumBound, hb] at hu
    | some h₀ =>
      simp only [sumBound, hb, Option.bind_some] at hu
      split at hu
      · cases hu; exact intSum_nonpos fun v hv i hi => by have := (h v hv i hi).2 h₀ hb; omega
      · cases hu

theorem sumBoundPos_sound {b : Bound} {v : Value} {vs : List Value}
    (h : ∀ w ∈ v :: vs, ∃ i, w.unscaled? = some i ∧ b.Mem i) :
    (sumBoundPos b).Mem (intSum (v :: vs)) := by
  obtain ⟨i, hv, hi⟩ := h v (by simp)
  have hrest : ∀ w ∈ vs, ∀ j, w.unscaled? = some j → b.Mem j := fun w hw j hj => by
    obtain ⟨j', hj', hm⟩ := h w (by simp [hw]); rw [hj] at hj'; cases hj'; exact hm
  rw [intSum_cons, hv, Option.getD_some]
  constructor
  · intro l hl
    cases hb : b.lo with
    | none => simp [sumBoundPos, hb] at hl
    | some l₀ =>
      simp only [sumBoundPos, hb, Option.bind_some] at hl
      split at hl
      · simp only [Option.some.injEq] at hl; subst hl
        have := hi.1 l₀ hb
        have := intSum_nonneg (vs := vs) fun w hw j hj => by
          have := (hrest w hw j hj).1 l₀ hb; omega
        omega
      · cases hl
  · intro u hu
    cases hb : b.hi with
    | none => simp [sumBoundPos, hb] at hu
    | some h₀ =>
      simp only [sumBoundPos, hb, Option.bind_some] at hu
      split at hu
      · simp only [Option.some.injEq] at hu; subst hu
        have := hi.2 h₀ hb
        have := intSum_nonpos (vs := vs) fun w hw j hj => by
          have := (hrest w hw j hj).2 h₀ hb; omega
        omega
      · cases hu

theorem sumCap_sound {b : Bound} :
    ∀ {vs : List Value} {n : Nat}, (∀ v ∈ vs, ∀ i, v.unscaled? = some i → b.Mem i) →
      vs.length ≤ n → (sumCap b n).Mem (intSum vs)
  | [], _, _, _ => by
    constructor
    · intro l hl; simp only [sumCap, Option.map_eq_some_iff] at hl
      obtain ⟨_, _, rfl⟩ := hl; simp [intSum]; omega
    · intro u hu; simp only [sumCap, Option.map_eq_some_iff] at hu
      obtain ⟨_, _, rfl⟩ := hu; simp [intSum]; omega
  | v :: vs, n, h, hlen => by
    have hrest : ∀ w ∈ vs, ∀ i, w.unscaled? = some i → b.Mem i :=
      fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hlen; omega⟩
    have hlen' : vs.length ≤ n' := by simp at hlen; omega
    have hlen'' : vs.length ≤ n' + 1 := by omega
    have ih := sumCap_sound hrest hlen'
    have ih' := sumCap_sound hrest hlen''
    have hcast : ((n' + 1 : Nat) : Int) = (n' : Int) + 1 := by simp
    constructor
    · intro l hl
      simp only [sumCap, Option.map_eq_some_iff] at hl
      obtain ⟨l₀, hb, rfl⟩ := hl
      have hi := ih.1 (min 0 ((n' : Int) * l₀)) (by simp [sumCap, hb])
      have hi' := ih'.1 (min 0 (((n' + 1 : Nat) : Int) * l₀)) (by simp [sumCap, hb])
      rw [hcast, Int.add_mul, Int.one_mul]
      rw [hcast, Int.add_mul, Int.one_mul] at hi'
      have hs1 : 0 ≤ l₀ → 0 ≤ (n' : Int) * l₀ := fun h0 => Int.mul_nonneg (by omega) h0
      have hs2 : l₀ ≤ 0 → (n' : Int) * l₀ ≤ 0 := fun h0 =>
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h0
      rw [intSum_cons]
      cases hv : v.unscaled? with
      | some i => have := (h v (by simp) i hv).1 l₀ hb; simp only [Option.getD_some]; omega
      | none => simp only [Option.getD_none]; omega
    · intro u hu
      simp only [sumCap, Option.map_eq_some_iff] at hu
      obtain ⟨h₀, hb, rfl⟩ := hu
      have hi := ih.2 (max 0 ((n' : Int) * h₀)) (by simp [sumCap, hb])
      have hi' := ih'.2 (max 0 (((n' + 1 : Nat) : Int) * h₀)) (by simp [sumCap, hb])
      rw [hcast, Int.add_mul, Int.one_mul]
      rw [hcast, Int.add_mul, Int.one_mul] at hi'
      have hs1 : 0 ≤ h₀ → 0 ≤ (n' : Int) * h₀ := fun h0 => Int.mul_nonneg (by omega) h0
      have hs2 : h₀ ≤ 0 → (n' : Int) * h₀ ≤ 0 := fun h0 =>
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h0
      rw [intSum_cons]
      cases hv : v.unscaled? with
      | some i => have := (h v (by simp) i hv).2 h₀ hb; simp only [Option.getD_some]; omega
      | none => simp only [Option.getD_none]; omega

/-- An integer or a decimal `a` holds is in `a`'s interval. -/
theorem AVal.mem_unscaled {a : AVal} {v : Value} {i : Int} {b : Bound} (hm : a.Mem v)
    (ha : a.int = some b) (hv : v.unscaled? = some i) : b.Mem i := by
  cases v <;> simp only [Value.unscaled?, Option.some.injEq, reduceCtorEq] at hv <;> subst hv <;>
    obtain ⟨b', hb', hm', -⟩ := hm <;> rw [ha] at hb' <;> cases hb' <;> exact hm'

theorem AVal.kindOnly_mem {a : AVal} {k : NumKind} (ho : a.kindOnly k = true) {v : Value}
    (hm : a.Mem v) (hn : v ≠ .null) : ∃ i b, v = k.val i ∧ a.int = some b ∧ b.Mem i := by
  simp only [AVal.kindOnly, AVal.intsOnly, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at ho
  obtain ⟨⟨⟨⟨htt, hff⟩, hstr⟩, hnest⟩, hk⟩ := ho
  rcases AVal.mem_cases hm with ⟨rfl, _⟩ | ⟨k', i, b, rfl, hb, hi, hk'⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
      ⟨_, rfl, h, _⟩ | ⟨_, _, h⟩
  · exact absurd rfl hn
  · rw [hk] at hk'; simp only [Option.all_some, beq_iff_eq] at hk'; subst hk'
    exact ⟨i, b, rfl, hb, hi⟩
  all_goals simp_all

theorem AVal.unscaledOnly_mem {a : AVal} (ho : a.unscaledOnly = true) {v : Value} (hm : a.Mem v)
    (hn : v ≠ .null) : ∃ i b, v.unscaled? = some i ∧ a.int = some b ∧ b.Mem i := by
  simp only [AVal.unscaledOnly, AVal.intsOnly, Bool.and_eq_true, Bool.not_eq_true'] at ho
  obtain ⟨⟨⟨⟨htt, hff⟩, hstr⟩, hnest⟩, hk⟩ := ho
  rcases AVal.mem_cases hm with ⟨rfl, _⟩ | ⟨k, i, b, rfl, hb, hi, hk'⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
      ⟨_, rfl, h, _⟩ | ⟨_, _, h⟩
  · exact absurd rfl hn
  · refine ⟨i, b, ?_, hb, hi⟩
    cases hnk : a.nk with
    | none => simp [hnk] at hk
    | some k' =>
      rw [hnk] at hk hk'
      simp only [Option.all_some, beq_iff_eq] at hk'
      subst hk'
      cases k' <;> simp_all [NumKind.val]
  all_goals simp_all

theorem AVal.dec_kind {a : AVal} {k : NumKind} {s : Nat} {x : Int} (hk : a.nk = some k)
    (hm : a.Mem (.dec s x)) : k = .dec s := by
  obtain ⟨_, _, _, h⟩ := hm
  rw [hk] at h; simpa using h

/-- A `SUM` is an integer, or a decimal of its inputs' scale (`sumOf`). -/
theorem sumOf_mem {a : AVal} {vs : List Value} {n : Bool} {B : Bound} (hne : vs ≠ [])
    (hall : ∀ w ∈ vs, a.Mem w ∧ w ≠ .null) (hB : B.Mem (intSum vs)) :
    (({ null := n, int := some B, nk := sumKind a } : AVal)).Mem (sumOf vs) := by
  have hnone : sumKind a = none →
      (({ null := n, int := some B, nk := sumKind a } : AVal)).Mem (sumOf vs) := fun hs => by
    rw [hs]
    rcases sumOf_cases vs with ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact ⟨_, rfl, hB, rfl⟩
  cases hnk : a.nk with
  | none => exact hnone (by simp [sumKind, hnk])
  | some k =>
    cases k with
    | int =>
      have hs : sumKind a = some .int := by simp [sumKind, hnk]
      rw [hs]
      rcases sumOf_cases vs with ⟨s, h1, e⟩ | ⟨_, e⟩
      · exfalso
        simp only [allDecOf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h1
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil vs h1.1
        have hd := List.all_eq_true.mp h1.2 w hw
        cases w <;> simp [Value.isDecOf] at hd
        have := AVal.dec_kind hnk (hall _ hw).1; cases this
      · rw [e]; exact ⟨_, rfl, hB, rfl⟩
    | dec t =>
      by_cases hio : a.intsOnly = true
      · have hs : sumKind a = some (.dec t) := by simp [sumKind, hnk, hio]
        rw [hs]
        have hko : a.kindOnly (.dec t) = true := by simp [AVal.kindOnly, hio, hnk]
        have hallt : allDecOf t vs = true := by
          simp only [allDecOf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
          refine ⟨hne, List.all_eq_true.mpr fun w hw => ?_⟩
          obtain ⟨i, b, rfl, -⟩ := AVal.kindOnly_mem hko (hall w hw).1 (hall w hw).2
          simp [NumKind.val, Value.isDecOf]
        rcases sumOf_cases vs with ⟨s, h1, e⟩ | ⟨h1, _⟩
        · rw [e, allDecOf_scale h1 hallt]
          exact ⟨_, rfl, hB, by simp⟩
        · rw [h1 t] at hallt; cases hallt
      · exact hnone (by simp [sumKind, hnk, hio])
    | _ => exact hnone (by simp [sumKind, hnk])


theorem Bound.mem_between {b : Bound} {l h r : Int} (hl : b.Mem l) (hh : b.Mem h) (hlr : l ≤ r)
    (hrh : r ≤ h) : b.Mem r :=
  ⟨fun x hx => Int.le_trans (hl.1 x hx) hlr, fun x hx => Int.le_trans hrh (hh.2 x hx)⟩

/-- A measure without a filter, of an argument that is never NULL, over a
group with a row, has an input. -/
theorem Measure.inputs_ne_nil {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) {m : Measure} (hg : grp ≠ [])
    (hf : m.filter = none) (hnn : (m.arg.absD env fs).null = false) : m.inputs grp ≠ [] := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil grp hg
  have hv := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) m.arg
  have : m.arg.eval y ≠ .null := fun h0 => by rw [h0] at hv; simp_all [AVal.Mem]
  simp only [Measure.inputs, Measure.kept, hf]
  have hm : m.arg.eval y ∈ (grp.map m.arg.eval).filter (· != .null) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨y, hy, rfl⟩, by simpa using this⟩
  split
  · exact List.ne_nil_of_mem (mem_dedup.mpr hm)
  · exact List.ne_nil_of_mem hm

theorem Measure.abs_sound {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (m : Measure) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    (m.abs env fs grouped rows).Mem (m.eval grp) := by
  have hin : ∀ v ∈ m.inputs grp, (m.arg.absD env fs).Mem v := by
    intro v hv
    obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
    exact Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) m.arg
  have inputs_ne_null : ∀ {v}, v ∈ m.inputs grp → v ≠ .null := fun hv => (Measure.mem_inputs hv).1
  -- A group with a row has a value, when the argument is never NULL and nothing is filtered.
  have valued_ne_nil : (grouped && m.filter.isNone && !(m.arg.absD env fs).null) = true →
      m.inputs grp ≠ [] := fun hv => by
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hv
    exact Measure.inputs_ne_nil hall (hne hv.1.1) hv.1.2 hv.2
  have novalue : m.inputs grp = [] →
      (!(grouped && m.filter.isNone && !(m.arg.absD env fs).null)) = true := fun hvs => by
    cases hv : (grouped && m.filter.isNone && !(m.arg.absD env fs).null)
    · rfl
    · exact absurd hvs (valued_ne_nil hv)
  unfold Measure.abs Measure.eval
  cases hf : m.fn <;> dsimp only
  case collect =>
    have hc : ∀ vs : List Value, AggFn.collect.apply vs = if vs = [] then .null else .list vs := by
      intro vs; cases vs <;> rfl
    rw [hc]
    split
    · rfl
    · rename_i hvs
      refine ⟨rfl, ⟨fun l hl => ?_, fun u hu => by simp [Bound.ge] at hu⟩, ?_⟩
      · simp only [Bound.ge, Option.some.injEq] at hl; subst hl
        generalize m.inputs _ = vs at hvs
        cases vs with
        | nil => exact absurd rfl hvs
        | cons => simp only [List.length_cons]; omega
      · show AVal.MemAll _ _
        rw [AVal.memAll_iff]
        intro v hv
        obtain ⟨hn, y, hy, rfl⟩ := Measure.mem_inputs hv
        have := Expr.absD_sound (hall y (List.mem_mergeSort.mp hy)).1
          (hall y (List.mem_mergeSort.mp hy)).2 (ks := []) (by simp [KsHold]) m.arg
        generalize m.arg.eval y = w at this hn
        cases w <;> simp_all [AVal.Mem, AVal.MemNum]
  case bbox n => exact BlackBox.aggAbs_mem valued_ne_nil
  case concat sep =>
    cases m.inputs (List.mergeSort grp (sortLe m.sort)) <;> simp [AggFn.apply, AVal.Mem]
  case count =>
    refine ⟨_, rfl, ⟨fun l hl => ?_, fun u hu => by simp [Bound.ge] at hu⟩, rfl⟩
    simp only [Bound.ge, Option.some.injEq] at hl
    subst hl
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hc
      obtain ⟨⟨hg, hf⟩, hnn⟩ := hc
      have hne' := Measure.inputs_ne_nil hall (hne hg) hf hnn
      cases h : m.inputs grp with
      | nil => exact absurd h hne'
      | cons _ _ => simp only [List.length_cons]; omega
    · omega
  case sum =>
    cases hvs : m.inputs grp with
    | nil =>
      simp only [AggFn.apply, AVal.Mem, AVal.MemR]
      exact novalue hvs
    | cons v vs =>
      simp only [AggFn.apply]
      refine sumOf_mem (by simp) (fun w hw => ⟨hin w (hvs ▸ hw), inputs_ne_null (hvs ▸ hw)⟩) ?_
      cases ha : (m.arg.absD env fs).int with
      | none => exact Bound.mem_top _
      | some b =>
        have hun : ∀ w ∈ v :: vs, ∀ i, w.unscaled? = some i → b.Mem i := fun w hw i hi =>
          AVal.mem_unscaled (hin w (hvs ▸ hw)) ha hi
        simp only
        refine Bound.mem_meet ?_ ?cap
        case cap =>
          cases rows with
          | none => exact Bound.mem_top _
          | some n =>
            refine sumCap_sound hun ?_
            rw [← hvs]
            exact Nat.le_trans (Measure.inputs_length_le m grp) (hrows n rfl)
        split
        · -- Every input is an integer or a decimal in `b`.
          rename_i honly
          refine sumBoundPos_sound fun w hw => ?_
          obtain ⟨i, b', hi, hb', hm⟩ :=
            AVal.unscaledOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
          rw [ha] at hb'; cases hb'; exact ⟨i, hi, hm⟩
        · exact sumBound_sound hun
  case cov sample =>
    simp only [AggFn.apply]
    cases m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [covOf]
      split
      · rfl
      · split <;> exact ⟨_, rfl, Bound.mem_top _, rfl⟩
  case corr =>
    cases m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [AggFn.apply, corrOf]
      split
      · rfl
      · split <;> exact ⟨_, rfl, Bound.mem_top _, rfl⟩
  case bit =>
    cases m.inputs grp <;> simp only [AggFn.apply] <;>
      first | rfl | exact ⟨_, rfl, Bound.mem_top _, rfl⟩
  case fsum =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem, AVal.MemR]; exact novalue hvs
    | cons v vs =>
      refine ⟨_, rfl, ?_, rfl⟩
      split
      · rename_i honly
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .float i ∧ (m.arg.absD env fs).int = some b ∧
            b.Mem i :=
          fun w hw => AVal.kindOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        have hcs : v :: vs = (floatsOf (v :: vs)).map .float := floats_map_floatsOf fun w hw => by
          obtain ⟨i, _, rfl, _⟩ := hint w hw; exact ⟨i, rfl⟩
        have hne' : floatsOf (v :: vs) ≠ [] := by
          intro h; rw [h] at hcs; simp at hcs
        have hb : ∀ c ∈ floatsOf (v :: vs), ((m.arg.absD env fs).int.getD Bound.top).Mem c := by
          intro c hc
          obtain ⟨_, b, he, hb, hm⟩ := hint _ (mem_floatsOf.1 hc)
          cases he; rw [hb]; exact hm
        have hlen : ∀ n, rows = some n → (floatsOf (v :: vs)).length ≤ n := by
          intro n hn
          have := hrows n hn
          have h1 : (floatsOf (v :: vs)).length = (v :: vs).length := by
            conv => rhs; rw [hcs]
            simp
          have h2 : (m.inputs grp).length ≤ grp.length := Measure.inputs_length_le m grp
          rw [hvs] at h2; omega
        have key := floatBound_sound (avg := false) hne' hb hlen
        have e : floatSumCR (v :: vs) = floatSumCR ((floatsOf (v :: vs)).map .float) :=
          congrArg floatSumCR hcs
        rw [e]; simpa using key
      · exact Bound.mem_top _
  case avg =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem, AVal.MemR]; exact novalue hvs
    | cons v vs =>
      refine ⟨_, rfl, ?_, rfl⟩
      split
      · rename_i honly
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .float i ∧ (m.arg.absD env fs).int = some b ∧
            b.Mem i :=
          fun w hw => AVal.kindOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        have hcs : v :: vs = (floatsOf (v :: vs)).map .float := floats_map_floatsOf fun w hw => by
          obtain ⟨i, _, rfl, _⟩ := hint w hw; exact ⟨i, rfl⟩
        have hne' : floatsOf (v :: vs) ≠ [] := by
          intro h; rw [h] at hcs; simp at hcs
        have hb : ∀ c ∈ floatsOf (v :: vs), ((m.arg.absD env fs).int.getD Bound.top).Mem c := by
          intro c hc
          obtain ⟨_, b, he, hb, hm⟩ := hint _ (mem_floatsOf.1 hc)
          cases he; rw [hb]; exact hm
        have hlen : ∀ n, rows = some n → (floatsOf (v :: vs)).length ≤ n := by
          intro n hn
          have := hrows n hn
          have h1 : (floatsOf (v :: vs)).length = (v :: vs).length := by
            conv => rhs; rw [hcs]
            simp
          have h2 : (m.inputs grp).length ≤ grp.length := Measure.inputs_length_le m grp
          rw [hvs] at h2; omega
        have key := floatBound_sound (avg := true) hne' hb hlen
        have e := congrArg floatAvgCR hcs
        rw [e]; simpa [avgCode] using key
      · exact Bound.mem_top _
  case iavg =>
    cases hvs : m.inputs grp with
    | nil => simp only [AggFn.apply, AVal.Mem, AVal.MemR]; exact novalue hvs
    | cons v vs =>
      split
      · rename_i honly
        -- Every value is an integer in the argument's interval `b`.
        have hint : ∀ w ∈ v :: vs, ∃ i b, w = .int i ∧ (m.arg.absD env fs).int = some b ∧ b.Mem i :=
          fun w hw => AVal.kindOnly_mem honly (hin w (hvs ▸ hw)) (inputs_ne_null (hvs ▸ hw))
        obtain ⟨i₀, b, rfl, hb, -⟩ := hint v (List.mem_cons_self ..)
        obtain ⟨r, hr, ⟨l, hl, hlr⟩, ⟨h, hh, hrh⟩⟩ := AggFn.apply_iavg_between
          (vs := .int i₀ :: vs) (List.ne_nil_of_mem (mem_intsOf.2 (List.mem_cons_self ..)))
        rw [hr]
        have memb : ∀ c ∈ intsOf (.int i₀ :: vs), b.Mem c := fun c hc => by
          obtain ⟨_, b', he, hb', hm⟩ := hint _ (mem_intsOf.1 hc)
          cases he; rw [hb] at hb'; cases hb'; exact hm
        refine ⟨b, by simp [hb], Bound.mem_between (memb l hl) (memb h hh) hlr hrh, rfl⟩
      · obtain ⟨r, hr, -⟩ : ∃ r, AggFn.iavg.apply (v :: vs) = .int r ∧ True := ⟨_, rfl, trivial⟩
        rw [hr]; exact ⟨_, rfl, Bound.mem_top _, rfl⟩
  case var sample sqrt =>
    cases m.inputs grp with
    | nil => rfl
    | cons v vs =>
      simp only [AggFn.apply, varOf]
      split
      · rfl
      · -- D30: NaN, a rounded square root, or a rounded non-negative quotient.
        split
        · have := Substrait.nan_eq
          exact ⟨_, rfl, ⟨fun l hl => by cases hl; omega, fun h hh => by cases hh⟩, rfl⟩
        · split
          · exact ⟨_, rfl, ⟨fun l hl => by cases hl; exact FloatCode.posCode_nonneg _,
              fun h hh => by cases hh⟩, rfl⟩
          · have h0 := FloatCode.ofExactDiv_nonneg ((floatsOf (v :: vs)).length *
                (if sample = true then (floatsOf (v :: vs)).length - 1 else (floatsOf (v :: vs)).length) *
                  2 ^ 1074) (comomentNum_nonneg (floatsOf (v :: vs)))
            exact ⟨_, rfl, ⟨fun l hl => by cases hl; exact h0, fun h hh => by cases hh⟩, rfl⟩
  case min | max =>
    split
    · -- A group with a value: one of the values.
      rename_i hv
      cases hvs : m.inputs grp with
      | nil => exact absurd hvs (valued_ne_nil hv)
      | cons v vs =>
        simp only [AggFn.apply]
        exact hin _ (hvs ▸ pickFold_mem _ _ _)
    · have hmm := AggFn.apply_minmax (f := m.fn) (by simp [hf]) (vs := m.inputs grp)
      rw [hf] at hmm
      rcases hmm with h | h
      · rw [h]; rfl
      · exact AVal.mem_nullable (hin _ h)
  case pick last =>
    -- The sorted rows are the group's rows.
    have hin' : ∀ v ∈ m.inputs (grp.mergeSort (sortLe m.sort)), (m.arg.absD env fs).Mem v := by
      intro v hv
      obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
      have hy' := (List.mergeSort_perm grp (sortLe m.sort)).mem_iff.mp hy
      exact Expr.absD_sound (hall y hy').1 (hall y hy').2 (ks := []) (by simp [KsHold]) m.arg
    rcases AggFn.apply_pick last (m.inputs (grp.mergeSort (sortLe m.sort))) with h | h
    · rw [h]; rfl
    · exact AVal.mem_nullable (hin' _ h)
  case mode =>
    have hin' : ∀ v ∈ m.inputs (grp.mergeSort (sortLe m.sort)), (m.arg.absD env fs).Mem v := by
      intro v hv
      obtain ⟨_, y, hy, rfl⟩ := Measure.mem_inputs hv
      have hy' := (List.mergeSort_perm grp (sortLe m.sort)).mem_iff.mp hy
      exact Expr.absD_sound (hall y hy').1 (hall y hy').2 (ks := []) (by simp [KsHold]) m.arg
    rcases AggFn.apply_mode (m.inputs (grp.mergeSort (sortLe m.sort))) with h | h
    · rw [h]; rfl
    · exact AVal.mem_nullable (hin' _ h)
  case quantile cont num scale =>
    cases cont
    · rcases AggFn.apply_disc num scale (m.inputs grp) with h | h
      · rw [h]; rfl
      · exact AVal.mem_nullable (hin _ h)
    · rcases AggFn.apply_cont num scale (m.inputs grp) with h | ⟨c, l, h, hc, hl, hh, hb⟩
      · rw [h]; rfl
      · rw [hc]
        obtain ⟨b, hb1, hlb, -⟩ := hin _ hl
        obtain ⟨b', hb2, hhb, -⟩ := hin _ hh
        rw [hb1] at hb2; cases hb2
        refine ⟨b, hb1, ?_, rfl⟩
        rcases hb with rfl | rfl | ⟨h1, h2⟩
        · exact hlb
        · exact hhb
        · exact Bound.mem_between hlb hhb h1 h2

theorem intSum_bounds {b : Bound} :
    ∀ {vs : List Value}, (∀ w ∈ vs, ∃ i, w.unscaled? = some i ∧ b.Mem i) →
      (∀ l, b.lo = some l → vs.length * l ≤ intSum vs) ∧
        (∀ h, b.hi = some h → intSum vs ≤ vs.length * h)
  | [], _ => by simp [intSum]
  | w :: ws, hall => by
    obtain ⟨i, hw, hi⟩ := hall w (List.mem_cons_self ..)
    have ih := intSum_bounds (vs := ws) fun w hw => hall w (List.mem_cons_of_mem _ hw)
    rw [intSum_cons, hw, Option.getD_some, List.length_cons]
    constructor
    · intro l hl
      have := hi.1 l hl; have := ih.1 l hl
      rw [Int.natCast_add, Int.add_mul]; omega
    · intro h hh
      have := hi.2 h hh; have := ih.2 h hh
      rw [Int.natCast_add, Int.add_mul]; omega

/-- The `ratio` facts hold on a group's row. -/
theorem ratioFacts_sound {g : Nat} {env : List AVal} {fs : List Fact} {ms : List Measure}
    {grp : Relation} {k : Row} (hk : k.length = g)
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) :
    FactsHold (ratioFacts g env fs ms) (k ++ ms.map (·.eval grp)) := by
  intro f hf
  simp only [ratioFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  have col : ∀ i (m : Measure), ms[i]? = some m →
      (k ++ ms.map (·.eval grp)).getD (g + i) .null = m.eval grp := fun i m h => by
    rw [← hk, getD_append_right']
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  split at hf
  · rename_i mi mj hmi hmj
    split at hf
    · rename_i hc
      obtain ⟨hsum, hcount, harg, hfil, hdis, honly⟩ := hc
      split at hf
      · rename_i b hb
        simp only [List.mem_singleton] at hf; subst hf
        intro x n hx hn
        rw [col i mi hmi, Measure.eval_eq (by rw [hsum]; rfl), hsum] at hx
        rw [col j mj hmj, Measure.eval_eq (by rw [hcount]; rfl), hcount] at hn
        have hsame : mj.inputs grp = mi.inputs grp := by
          simp only [Measure.inputs, Measure.kept, harg, hfil, hdis]
        rw [hsame] at hn
        cases hvs : mi.inputs grp with
        | nil => rw [hvs] at hx; simp [AggFn.apply] at hx
        | cons v vs =>
          rw [hvs] at hx hn
          simp only [AggFn.apply] at hx hn
          have hx' := sumOf_unscaled hx
          simp only [Value.unscaled?, Option.some.injEq] at hn
          subst hx' hn
          have hint : ∀ w ∈ v :: vs, ∃ i, w.unscaled? = some i ∧ b.Mem i := by
            intro w hw
            have hw' : w ∈ mi.inputs grp := hvs ▸ hw
            obtain ⟨hnn, y, hy, rfl⟩ := Measure.mem_inputs hw'
            have hm := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) mi.arg
            obtain ⟨i, b', he, hb', hi⟩ := AVal.unscaledOnly_mem honly hm hnn
            rw [hb] at hb'; cases hb'
            exact ⟨i, he, hi⟩
          obtain ⟨hlo, hhi⟩ := intSum_bounds hint
          exact ⟨by simp, hlo, hhi⟩
      · simp at hf
    · simp at hf
  · simp at hf

theorem EnvMem.measures {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) (ms : List Measure) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    EnvMem (ms.map fun m => Measure.abs env fs m grouped rows) (ms.map (·.eval grp)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ms[j]? <;> simp [AVal.mem_top, Measure.abs_sound hall _ grouped hne rows hrows]

/-- **Soundness of abstract plan evaluation**: every row a well-formed plan
produces is described by `Rel.aeval`, provided the tables are. -/
theorem WinFn.abs_sound {env : List AVal} {part : List Nat} {b a : List Row} {x : Row}
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) {sz : Bool}
    (hn : sz = true → b.length + 1 + a.length < 2 ^ 62) :
    ∀ f : WinFn, (f.abs sz env).Mem (f.value part b a x)
  | .rowNumber => AVal.memInt_intro rfl rfl <| by
      have := List.length_filter_le (samePart part x) b
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩
  | .rank _ => AVal.memInt_intro rfl rfl <| by
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (fun y => !peer ‹List SortKey› x y) (b.filter (samePart part x))
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩
  | .denseRank sort => AVal.memInt_intro rfl rfl <| by
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (fun y => !peer sort x y) (b.filter (samePart part x))
      have h3 := dedup_length_le (((b.filter (samePart part x)).filter fun y => !peer sort x y).map
        fun y => sort.map (y.getD ·.col .null))
      simp only [List.length_map] at h3
      simp only [Bound.Mem, Text.rowCap, Option.some.injEq]
      exact ⟨fun l hl => by subst hl; omega, fun u hu => by
        cases sz <;> simp at hu
        subst hu; have := hn rfl; omega⟩
  | .ntile k => AVal.memInt_intro rfl rfl <| by
      simp only [Bound.Mem, Option.some.injEq, Text.rowCap]
      have h1 := List.length_filter_le (samePart part x) b
      have h2 := List.length_filter_le (samePart part x) a
      generalize (List.filter (samePart part x) b).length = i at h1 ⊢
      generalize (List.filter (samePart part x) a).length = j at h2 ⊢
      have hm := ntileOf_le i k (i + 1 + j)
      have h1' := one_le_ntileOf i k (i + 1 + j)
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · subst hl; omega
      · cases sz <;> simp at hu
        subst hu; have := hn rfl; omega
  | .percentRank _ => by
      simp only [WinFn.abs, WinFn.value, WinFn.valueIn, floatRatio]
      split <;> exact ⟨_, rfl, Bound.mem_top _, rfl⟩
  | .cumeDist _ => ⟨_, rfl, Bound.mem_top _, rfl⟩
  | .agg m sort fr => by
      simp only [WinFn.abs, WinFn.value, WinFn.valueIn]
      refine Measure.abs_sound (fun y hy => ⟨?_, by simp [FactsHold]⟩) m
      have hy' := Frame.mem_rows hy
      simp only [List.mem_append, List.mem_cons, List.mem_filter] at hy'
      rcases hy' with ⟨hb, _⟩ | rfl | ⟨ha, _⟩
      · exact hall y (.inr (.inl hb))
      · exact hall y (.inl rfl)
      · exact hall y (.inr (.inr ha))
  | .firstValue _ _ _ | .lastValue _ _ _ | .nthValue _ _ _ _ => AVal.mem_top _
  | .lag c k d => by
      simp only [WinFn.abs]
      rcases WinFn.value_lag (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
        (d := d) with h | ⟨y, hy, h⟩
      · rw [h]; exact AVal.mem_join_right (AVal.mem_ofValue d)
      · rw [h]
        exact AVal.mem_join_left (hall y (hy.elim .inl fun hy => .inr (.inl hy.1)) c)
  | .lead c k d => by
      simp only [WinFn.abs]
      rcases WinFn.value_lead (part := part) (b := b) (a := a) (x := x) (c := c) (k := k)
        (d := d) with h | ⟨y, hy, h⟩
      · rw [h]; exact AVal.mem_join_right (AVal.mem_ofValue d)
      · rw [h]
        exact AVal.mem_join_left (hall y (hy.elim .inl fun hy => .inr (.inr hy.1)) c)

theorem EnvMem.window {env : List AVal} {part : List Nat} {b a : List Row} {x : Row}
    (hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem env y) {sz : Bool}
    (hn : sz = true → b.length + 1 + a.length < 2 ^ 62) (fns : List WinFn) :
    EnvMem (fns.map (WinFn.abs sz env)) (fns.map (·.value part b a x)) := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases fns[j]? <;> simp [AVal.mem_top, WinFn.abs_sound hall hn]

/-- **The size hypothesis for relations** (trusted, #202): every relation a
window reads has fewer than `2⁶²` rows, which every engine's memory
guarantees. It bounds `ROW_NUMBER` and the ranks by `Text.rowCap`, so that
`ROW_NUMBER() - 1` is proved not to overflow. Every relation an aggregate
reads has fewer than `2⁶³` rows (#437): `COUNT(*)` of a group is a BIGINT,
in the reference and in every engine. It bounds a group's `SUM` by its
rows (`Rel.sumRows`), so that a `SUM` of values in `[-1, 1]` is proved to
fit 64 bits. -/
def Rel.Small (cat : Catalog) : Rel → Prop
  | .read _ | .values _ _ => True
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.Small cat
  | .aggregate r _ _ => (r.eval cat).length < 2 ^ 63 ∧ r.Small cat
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => a.Small cat ∧ b.Small cat
  | .window r _ _ _ => (r.eval cat).length < 2 ^ 62 ∧ r.Small cat

mutual
theorem Rel.aeval_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (sz = true → r.Small cat) → ∀ row ∈ r.eval cat,
      EnvMem (r.aeval cat A F T sz) row
  | .read t, _, _, row, h => useFacts_sound (hF t row h) ((hA t row h).fit _)
  | .values _ _, _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, hs, row, h => by
      simp only [eval, List.mem_filter] at h
      exact useFacts_sound ((Rel.facts_sound hcat hF hT hwf.1 row h.1).append (c.factsOf_sound h.2))
        (Expr.refine_sound _ c (aeval_sound hcat hA hF hT hwf.1 hs row h.1) h.2)
  | .project r es, hwf, hs, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      have hm := aeval_sound hcat hA hF hT hwf.1 hs x hx
      have hr := ratioPart_sound hcat hA hF hT hwf.1 hs x hx
      exact hm.append (hm.mapF ((Rel.facts_sound hcat hF hT hwf.1 x hx).append hr) es)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .emit r m, hwf, hs, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 hs x hx).emit m
  | .cross a b, hwf, hs, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      exact (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx).append (aeval_sound hcat hA hF hT hwf.2 (fun h => (hs h).2) y hy)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])
  | .join a b .inner on, hwf, hs, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, ht⟩ := h
      exact Expr.refine_sound _ on ((aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx).append
        (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) y hy) (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])) ht
  | .join a b .left on, hwf, hs, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxm := aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) x hx
      have hl : (a.aeval cat A F T sz).length = x.length := by
        rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hxm.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        exact hxm.append (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) y hy).nullable hl
  | .fetch r _ _, hwf, hs, row, h => by
      simp only [eval] at h
      have := aeval_sound hcat hA hF hT (r := r) hwf hs
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .semi a _ _ _, hwf, hs, row, h => by
      simp only [eval, List.mem_filter] at h
      exact aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) row h.1
  | .orderBy r _, hwf, hs, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf.1 hs row h
  | .distinct r, hwf, hs, row, h => by
      simp only [eval, mem_dedup] at h
      exact aeval_sound hcat hA hF hT (r := r) hwf hs row h
  | .unnest r c, hwf, hs, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨_, v, hc, hv, rfl⟩ := mem_unnestRow h
      exact (aeval_sound hcat hA hF hT hwf.1 hs x hx).set_elem hc hv
  | .aggregate r gs ms, hwf, hs, row, h => by
      obtain ⟨k, grp, rfl, hgrp, hk, hne, hglen⟩ := mem_aggregateEval_len h
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T sz) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hgrp y hy),
          Rel.facts_sound hcat hF hT hwf.1 y (hgrp y hy)⟩
      have hm := EnvMem.measures hall ms (!gs.isEmpty) (fun hg => hne (by simpa using hg))
        (rows := r.maxRows) (fun n hn => Nat.le_trans hglen (Rel.maxRows_sound hn))
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) hm (by simp)
      · exact (EnvMem.mapD (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) x hx)
          (Rel.facts_sound hcat hF hT hwf.1 x hx) gs).append hm (by simp)
  | .unionAll a b, hwf, hs, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact (aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).1) row h).zip_left
      · exact (aeval_sound hcat hA hF hT hwf.2.1 (fun h => (hs h).2) row h).zip_right
  | .window r _ _ fns, hwf, hs, row, h => by
      obtain ⟨b, x, a, he, hx, rfl⟩ := mem_windowEval h
      obtain ⟨_, _, hin⟩ := sorted_split he
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T sz) y :=
        fun y hy => aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hin y hy)
      have hn : sz = true → b.length + 1 + a.length < 2 ^ 62 := by
        intro h
        have := (List.mergeSort_perm (r.eval cat) (sortLe ‹List SortKey›)).length_eq
        rw [he] at this; simp at this; have := (hs h).1; omega
      exact (hall x (.inl rfl)).append (EnvMem.window hall hn fns)
        (by rw [aeval_length hwf.1, eval_arity hcat hwf.1 x hx])

theorem Rel.ratioPart_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {sz : Bool} :
    ∀ {r : Rel}, r.WF cat → (sz = true → r.Small cat) → ∀ row ∈ r.eval cat,
      FactsHold (r.ratioPart cat A F T sz) row
  | .aggregate r gs ms, hwf, hs, row, h => by
      obtain ⟨k, grp, rfl, hgrp, hk, -⟩ := mem_aggregateEval_nonempty h
      refine ratioFacts_sound ?_ fun y hy => ⟨aeval_sound hcat hA hF hT hwf.1 (fun h => (hs h).2) y (hgrp y hy),
        Rel.facts_sound hcat hF hT hwf.1 y (hgrp y hy)⟩
      rcases hk with ⟨rfl, rfl⟩ | ⟨z, _, rfl⟩ <;> simp [groupKey]
  | .read _, _, _, _, _ | .values _ _, _, _, _, _ | .filter _ _, _, _, _, _
  | .project _ _, _, _, _, _ | .emit _ _, _, _, _, _ | .cross _ _, _, _, _, _
  | .join _ _ _ _, _, _, _, _ | .fetch _ _ _, _, _, _, _ | .unionAll _ _, _, _, _, _
  | .window _ _ _ _, _, _, _, _ | .semi _ _ _ _, _, _, _, _ | .orderBy _ _, _, _, _, _
  | .distinct _, _, _, _, _ | .unnest _ _, _, _, _, _ => fun f hf => by simp [ratioPart] at hf
end

/-- `ratioFacts_sound` for any row whose measures that do not sort hold their
values over `grp`. -/
theorem ratioFacts_sound_of {g : Nat} {env : List AVal} {fs : List Fact} {ms : List Measure}
    {grp : Relation} {row : Row}
    (col : ∀ i (m : Measure), ms[i]? = some m → m.fn.sorts = false →
      row.getD (g + i) .null = m.eval grp)
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) :
    FactsHold (ratioFacts g env fs ms) row := by
  intro f hf
  simp only [ratioFacts, List.mem_flatMap, List.mem_range] at hf
  obtain ⟨i, _, j, _, hf⟩ := hf
  split at hf
  · rename_i mi mj hmi hmj
    split at hf
    · rename_i hc
      obtain ⟨hsum, hcount, harg, hfil, hdis, honly⟩ := hc
      split at hf
      · rename_i b hb
        simp only [List.mem_singleton] at hf; subst hf
        intro x n hx hn
        rw [col i mi hmi (by rw [hsum]; rfl), Measure.eval_eq (by rw [hsum]; rfl), hsum] at hx
        rw [col j mj hmj (by rw [hcount]; rfl), Measure.eval_eq (by rw [hcount]; rfl), hcount] at hn
        have hsame : mj.inputs grp = mi.inputs grp := by
          simp only [Measure.inputs, Measure.kept, harg, hfil, hdis]
        rw [hsame] at hn
        cases hvs : mi.inputs grp with
        | nil => rw [hvs] at hx; simp [AggFn.apply] at hx
        | cons v vs =>
          rw [hvs] at hx hn
          simp only [AggFn.apply] at hx hn
          have hx' := sumOf_unscaled hx
          simp only [Value.unscaled?, Option.some.injEq] at hn
          subst hx' hn
          have hint : ∀ w ∈ v :: vs, ∃ i, w.unscaled? = some i ∧ b.Mem i := by
            intro w hw
            have hw' : w ∈ mi.inputs grp := hvs ▸ hw
            obtain ⟨hnn, y, hy, rfl⟩ := Measure.mem_inputs hw'
            have hm := Expr.absD_sound (hall y hy).1 (hall y hy).2 (ks := []) (by simp [KsHold]) mi.arg
            obtain ⟨i, b', he, hb', hi⟩ := AVal.unscaledOnly_mem honly hm hnn
            rw [hb] at hb'; cases hb'
            exact ⟨i, he, hi⟩
          obtain ⟨hlo, hhi⟩ := intSum_bounds hint
          exact ⟨by simp, hlo, hhi⟩
      · simp at hf
    · simp at hf
  · simp at hf

theorem EnvMem.measures_all {env : List AVal} {fs : List Fact} {grp : Relation}
    (hall : ∀ y ∈ grp, EnvMem env y ∧ FactsHold fs y) {ms : List Measure} {vs : List Value}
    (hv : Forall2 (fun m v => m.OrderAllowed grp v) ms vs) (grouped : Bool := false)
    (hne : grouped = true → grp ≠ [] := by simp) (rows : Option Nat := none)
    (hrows : ∀ n, rows = some n → grp.length ≤ n := by simp) :
    EnvMem (ms.map fun m => Measure.abs env fs m grouped rows) vs := by
  intro j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hv.getElem? j with ⟨m, v, hm, hb, hr⟩ | ⟨hm, hb⟩
  · obtain ⟨s, hp, rfl, _⟩ := hr.eval
    simp only [hm, hb, Option.map_some, Option.getD_some]
    exact Measure.abs_sound (grp := s) (fun y hy => hall y (hp.mem_iff.mp hy)) m grouped
      (fun hg hs => hne hg (List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, hs]; rfl))) rows
      (fun n hn => hp.length_eq ▸ hrows n hn)
  · simp [hm, hb, AVal.mem_top]

mutual
/-- **The abstract interpreter describes every row of every order.** -/
theorem Rel.aeval_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, EnvMem (r.aeval cat A F T) row
  | .read t, _, _, h, row, hr =>
      useFacts_sound (hF t row (h.mem_iff.mp hr)) ((hA t row (h.mem_iff.mp hr)).fit _)
  | .values _ _, _, _, _, row, _ => EnvMem.replicate _ row
  | .filter r c, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      rw [List.mem_filter] at hr
      exact useFacts_sound ((Rel.facts_sound_all hcat hF hT hwf.1 hi row hr.1).append
        (c.factsOf_sound hr.2)) (Expr.refine_sound _ c (aeval_sound_all hcat hA hF hT hwf.1 hi row hr.1) hr.2)
  | .project r es, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hm := aeval_sound_all hcat hA hF hT hwf.1 hi x hx
      have hrp := ratioPart_sound_all hcat hA hF hT hwf.1 hi x hx
      exact hm.append (hm.mapF ((Rel.facts_sound_all hcat hF hT hwf.1 hi x hx).append hrp) es)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x hx])
  | .emit r m, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).emit m
  | .cross a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp (h.mem_iff.mp hr)
      exact (aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])
  | .join a b .inner on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨hc, ht⟩ := List.mem_filter.mp (h.mem_iff.mp hr)
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_crossRows.mp hc
      exact Expr.refine_sound _ on ((aeval_sound_all hcat hA hF hT hwf.1 hx u hu).append
        (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu])) ht
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      obtain ⟨u, hu, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      have hum := aeval_sound_all hcat hA hF hT hwf.1 hx u hu
      have hl : (a.aeval cat A F T).length = u.length := by
        rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hx u hu]
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hum.append (EnvMem.nulls _ _) hl
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨v, hv, rfl⟩, _⟩ := h
        exact hum.append (aeval_sound_all hcat hA hF hT hwf.2.1 hy v hv).nullable hl
  | .fetch r _ cnt, hwf, _, ⟨i, hi, rfl⟩, row, hr => by
      have := aeval_sound_all hcat hA hF hT (r := r) hwf hi
      cases cnt with
      | none => exact this row (List.mem_of_mem_drop hr)
      | some _ => exact this row (List.mem_of_mem_drop (List.mem_of_mem_take hr))
  | .semi a _ _ _, hwf, _, ⟨x, _, hx, _, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT hwf.1 hx row (List.mem_filter.mp (h.mem_iff.mp hr)).1
  | .orderBy r _, hwf, _, ⟨i, hi, h, _⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf.1 hi row (h.mem_iff.mp hr)
  | .distinct r, hwf, _, ⟨i, hi, h⟩, row, hr =>
      aeval_sound_all hcat hA hF hT (r := r) hwf hi row (mem_dedup.mp (h.mem_iff.mp hr))
  | .unnest r c, hwf, _, ⟨i, hi, h⟩, row, hr => by
      obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp (h.mem_iff.mp hr)
      obtain ⟨_, v, hc, hv, rfl⟩ := mem_unnestRow h
      exact (aeval_sound_all hcat hA hF hT hwf.1 hi x hx).set_elem hc hv
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, hne, hglen⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hall : ∀ y ∈ grp, EnvMem (r.aeval cat A F T) y ∧ FactsHold (r.facts cat F T) y :=
        fun y hy => ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
      have hm := EnvMem.measures_all hall hv (!gs.isEmpty) (fun hg => hne (by simpa using hg))
        (rows := r.maxRows) (fun n hn => Nat.le_trans hglen (Rel.maxRows_sound_all hn hi))
      rcases hk with ⟨rfl, rfl⟩ | ⟨x, hx, rfl⟩
      · exact EnvMem.append (by intro j; simp [AVal.mem_top]) hm (by simp)
      · exact (EnvMem.mapD (aeval_sound_all hcat hA hF hT hwf.1 hi x hx)
          (Rel.facts_sound_all hcat hF hT hwf.1 hi x hx) gs).append hm (by simp)
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, h⟩, row, hr => by
      rcases List.mem_append.mp (h.mem_iff.mp hr) with h | h
      · exact (aeval_sound_all hcat hA hF hT hwf.1 hx row h).zip_left
      · exact (aeval_sound_all hcat hA hF hT hwf.2.1 hy row h).zip_right
  | .window r _ _ fns, hwf, _, ⟨i, hi, s, hp, hs, h⟩, row, hr => by
      obtain ⟨b, x, a, _, rfl, _, _, hin⟩ := mem_windowRows_sorted hs (h.mem_iff.mp hr)
      have hall : ∀ y, (y = x ∨ y ∈ b ∨ y ∈ a) → EnvMem (r.aeval cat A F T) y :=
        fun y hy => aeval_sound_all hcat hA hF hT hwf.1 hi y (hp.mem_iff.mp (hin y hy))
      exact (hall x (.inl rfl)).append (EnvMem.window (sz := false) hall nofun fns)
        (by rw [aeval_length hwf.1, orderAllowed_arity hcat hwf.1 hi x (hp.mem_iff.mp (hin x (.inl rfl)))])

theorem Rel.ratioPart_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      ∀ row ∈ out, FactsHold (r.ratioPart cat A F T) row
  | .aggregate r gs ms, hwf, _, ⟨i, hi, o, h, ho⟩, row, hr => by
      obtain ⟨k, vs, grp, rfl, hv, hgrp, hk, -⟩ := mem_aggOrderAllowed ho (h.mem_iff.mp hr)
      have hkl : k.length = gs.length := by
        rcases hk with ⟨rfl, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [groupKey]
      exact ratioFacts_sound_of (hkl ▸ aggCol hv) fun y hy =>
        ⟨aeval_sound_all hcat hA hF hT hwf.1 hi y (hgrp y hy),
          Rel.facts_sound_all hcat hF hT hwf.1 hi y (hgrp y hy)⟩
  | .read _, _, _, _, _, _ | .values _ _, _, _, _, _, _ | .filter _ _, _, _, _, _, _
  | .project _ _, _, _, _, _, _ | .emit _ _, _, _, _, _, _ | .cross _ _, _, _, _, _, _
  | .join _ _ _ _, _, _, _, _, _ | .fetch _ _ _, _, _, _, _, _ | .unionAll _ _, _, _, _, _, _
  | .window _ _ _ _, _, _, _, _, _ | .semi _ _ _ _, _, _, _, _, _ | .orderBy _ _, _, _, _, _, _
  | .distinct _, _, _, _, _, _ | .unnest _ _, _, _, _, _, _ => fun f hf => by simp [ratioPart] at hf
end

/-! ## Contracts -/

/-- Substitute expressions for field references. -/
def Expr.subst (cols : List Expr) : Expr → Expr
  | .lit v => .lit v
  | .field i => cols.getD i (.lit .null)
  | .un f a => .un f (a.subst cols)
  | .bin f a b => .bin f (a.subst cols) (b.subst cols)
  | .ifThen c t e => .ifThen (c.subst cols) (t.subst cols) (e.subst cols)
  | .hof f l b => .hof f (l.subst cols) (b.subst (.field 0 :: cols.map (·.shift 0)))

theorem getD_map_eval (cols : List Expr) (row : Row) (i : Nat) :
    (cols.map (·.eval row)).getD i .null = (cols.getD i (.lit .null)).eval row := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cols[i]? <;> rfl

theorem Expr.eval_subst (cols : List Expr) (row : Row) :
    ∀ e : Expr, (e.subst cols).eval row = e.eval (cols.map (·.eval row))
  | .lit _ => rfl
  | .field i => (getD_map_eval cols row i).symm
  | .un f a => by simp [subst, eval, Expr.eval_subst cols row a]
  | .bin f a b => by simp [subst, eval, Expr.eval_subst cols row a, Expr.eval_subst cols row b]
  | .ifThen c t e => by
      simp [subst, eval, Expr.eval_subst cols row c, Expr.eval_subst cols row t,
        Expr.eval_subst cols row e]
  | .hof f l b => by
      simp only [subst, eval, Expr.eval_subst cols row l]
      congr 1; funext x
      rw [Expr.eval_subst _ (x :: row) b]
      simp [eval, List.map_map, Function.comp_def, Expr.eval_shift_cons]

/-- A plan that only computes columns of one table (`Read` under projects and
emits) as expressions over that table's columns. Preconditions are given as
such plans: `orders.select(amount >= 0, ...)`. -/
def Rel.colExprs (cat : Catalog) : Rel → Option (String × List Expr)
  | .read t => some (t, (List.range (cat t).arity).map .field)
  | .project r es => (r.colExprs cat).map fun (t, cs) => (t, cs ++ es.map (·.subst cs))
  | .emit r m => (r.colExprs cat).map fun (t, cs) => (t, m.map (cs.getD · (.lit .null)))
  | _ => none

/-- Such a plan computes its expressions row by row: so "every output column
of the precondition plan is TRUE" means each expression is TRUE on each row. -/
theorem Rel.colExprs_eval {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel} {t : String} {cs : List Expr}, r.colExprs cat = some (t, cs) →
      r.eval cat = (cat t).rows.map fun row => cs.map (·.eval row)
  | .read t', t, cs, h => by
      simp only [colExprs, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      conv => lhs; rw [← List.map_id (eval cat (read t'))]
      simp only [eval]
      apply List.map_congr_left
      intro row hrow
      simp only [List.map_map, Function.comp_def, Expr.eval, id]
      apply List.ext_getElem (by simp [hcat t' row hrow])
      intro i h₁ _
      simp [List.getD, List.getElem?_eq_getElem h₁]
  | .project r es, t, cs, h => by
      simp only [colExprs, Option.map_eq_some_iff] at h
      obtain ⟨⟨t', cs'⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [eval, colExprs_eval hcat hr, List.map_map]
      apply List.map_congr_left
      intro row _
      simp [List.map_append, Function.comp_def, Expr.eval_subst]
  | .emit r m, t, cs, h => by
      simp only [colExprs, Option.map_eq_some_iff] at h
      obtain ⟨⟨t', cs'⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [eval, colExprs_eval hcat hr, List.map_map]
      apply List.map_congr_left
      intro row _
      simp only [Function.comp_def]
      apply List.map_congr_left
      intro a _
      exact getD_map_eval cs' row a
  | .values _ _, _, _, h | .filter _ _, _, _, h | .cross _ _, _, _, h | .join _ _ _ _, _, _, h
  | .fetch _ _ _, _, _, h | .unionAll _ _, _, _, h | .window _ _ _ _, _, _, h
  | .semi _ _ _ _, _, _, h | .orderBy _ _, _, _, h | .distinct _, _, _, h
  | .unnest _ _, _, _, h => by
      simp [colExprs] at h

/-- What is known about a table: its schema, refined by its preconditions. -/
def tableEnv (schema : List AVal) (pre : List Expr) : List AVal := pre.foldl Expr.refine schema

theorem tableEnv_sound {row : Row} :
    ∀ {schema : List AVal} {pre : List Expr}, EnvMem schema row →
      (∀ e ∈ pre, (e.eval row).isTrue = true) → EnvMem (tableEnv schema pre) row
  | _, [], h, _ => h
  | _, e :: pre, h, hpre => by
      simp only [tableEnv, List.foldl_cons]
      exact tableEnv_sound (Expr.refine_sound _ e h (hpre e (by simp)))
        fun e' he' => hpre e' (by simp [he'])

/-- **Contract soundness for every order.** Under `contract_sound`'s
hypotheses, every postcondition holds on every row of every order the
reference allows: for every way an engine breaks ties, takes the rows of a
`FETCH` or orders the rows of `FIRST`, `STRING_AGG` or a window. -/
theorem contract_sound_all {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out → ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  intro out hout row hrow v hv
  have hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold ((pre t).flatMap Expr.factsOf) row := by
    intro t row h f hf
    simp only [List.mem_flatMap] at hf
    obtain ⟨e, he, hf⟩ := hf
    exact Expr.factsOf_sound e (hpre t row h e he) f hf
  have hm := Q.aeval_sound_all hcat (fun t row h => tableEnv_sound (hS t row h) (hpre t row h)) hF
    hT hQ hout row hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen : j < (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).length := by
    rw [Rel.aeval_length hQ, ← Rel.orderAllowed_arity hcat hQ hout row hrow]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen)
  have := hm j
  simp only [List.getElem?_eq_getElem hlen, Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

/-- **Contract soundness.** Suppose every row of every table matches its
schema and satisfies its preconditions, the postcondition plan `Q` (the
transformation followed by a select of the postconditions) is well-formed. If
the abstract evaluation shows every column of `Q` is certainly TRUE, then
every postcondition holds on every output row. -/
theorem contract_sound {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat)
    (hproved : (Q.aeval cat (fun t => tableEnv (S t) (pre t))
      (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true :=
  contract_sound_all hcat hS hpre hQ hT hproved (Q.eval_orderAllowed cat)

end Substrait
