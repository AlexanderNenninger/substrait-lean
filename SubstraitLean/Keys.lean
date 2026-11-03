import SubstraitLean.Contracts

/-!
# Keys: "at most one row per …"

A **key** of a relation is a list of columns on which no two rows agree. If
each input table has a key (the data producer guarantees one reading per
sensor and timestamp, say), `Rel.keys` derives keys of a plan's output.

* filters, fetches: keep every key (fewer rows); a fetch of at most one row,
  and a literal table of at most one row, have the empty key;
* windows: keep every key (the same rows, reordered, with columns appended);
* projections: keep keys on input columns; emits: re-index them;
* cross products: combine a key of each side;
* joins: keep the left side's keys when the join condition determines a key
  of the right side (`a.ts = b.ts` with `ts` a key of `b`, or
  `w1.ts = w0.ts + 60`), so each left row has at most one partner.

`Rel.keys_sound` proves every derived key holds. Equality here is equality of
values, so two NULLs count as equal: a stronger requirement than SQL `UNIQUE`.
-/

namespace Substrait

/-- At most one row: the empty list is a key. -/
theorem KeyOn.of_length_le_one {rows : Relation} (h : rows.length ≤ 1) : KeyOn [] rows := by
  match rows, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-- The empty key holds exactly when there is at most one row. -/
theorem KeyOn.nil_iff {rows : Relation} : KeyOn [] rows ↔ rows.length ≤ 1 := by
  refine ⟨fun h => ?_, KeyOn.of_length_le_one⟩
  match rows, h with
  | [], _ | [_], _ => simp
  | x :: y :: _, h =>
    simp only [KeyOn, keyOf, List.map_nil, ne_eq, not_true_eq_false, List.pairwise_cons] at h
    exact absurd (List.mem_cons_self ..) (h.1 y)

/-- A superset of a key is a key. -/
theorem KeyOn.superset {k k' : List Nat} {rows : Relation} (hk : KeyOn k rows)
    (hsub : ∀ c ∈ k, c ∈ k') : KeyOn k' rows :=
  hk.imp fun h heq => h (by
    simp only [keyOf, List.map_inj_left] at heq ⊢
    exact fun c hc => heq c (hsub c hc))

theorem keyOf_append_left {k : List Nat} {x y : Row} (h : ∀ c ∈ k, c < x.length) :
    keyOf k (x ++ y) = keyOf k x := by
  simp only [keyOf, List.map_inj_left]
  intro c hc
  exact getD_append_left' (h c hc)

theorem keyOf_take {k : List Nat} {n : Nat} {row : Row} (h : ∀ c ∈ k, c < n) :
    keyOf k (row.take n) = keyOf k row := by
  simp only [keyOf, List.map_inj_left]
  intro c hc
  simp [List.getD_eq_getElem?_getD, h c hc]

theorem keyOf_shift (k : List Nat) (x y : Row) :
    keyOf (k.map (x.length + ·)) (x ++ y) = keyOf k y := by
  unfold keyOf
  rw [List.map_map]
  exact List.map_congr_left fun c _ => getD_append_right' c

theorem keyOf_cross {ka kb : List Nat} {x y : Row} (h : ∀ c ∈ ka, c < x.length) :
    keyOf (ka ++ kb.map (x.length + ·)) (x ++ y) = keyOf ka x ++ keyOf kb y := by
  rw [keyOf, List.map_append, ← keyOf, ← keyOf, keyOf_append_left h, keyOf_shift]

/-! ## Join conditions that determine columns -/

/-- Column pairs `(i, j)` such that, on rows where `e` is TRUE, `i` determines
`j` and `j` determines `i` (`$i + c₁ = $j + c₂`). -/
def Expr.eqCols : Expr → List (Nat × Nat)
  | .bin .and p q => p.eqCols ++ q.eqCols
  | .bin .eq t₁ t₂ =>
      match t₁.linTerm, t₂.linTerm with
      | some (i, _), some (j, _) => [(i, j)]
      | _, _ => []
  | _ => []

theorem Expr.linTerm_congr {t : Expr} {i : Nat} {c : Int} {r r' : Row}
    (h : t.linTerm = some (i, c)) (hi : r.getD i .null = r'.getD i .null) :
    t.eval r = t.eval r' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hi
  rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl <;> simp [eval, hi]

theorem add_lit_inj {v w : Value} {c : Int} (he : BinFn.apply .add v (.int c) = BinFn.apply .add w (.int c))
    (hn : BinFn.apply .add v (.int c) ≠ .null) : v = w := by
  cases v <;> cases w <;> simp_all [BinFn.apply]

theorem lit_add_inj {v w : Value} {c : Int} (he : BinFn.apply .add (.int c) v = BinFn.apply .add (.int c) w)
    (hn : BinFn.apply .add (.int c) v ≠ .null) : v = w := by
  cases v <;> cases w <;> simp_all [BinFn.apply]

theorem sub_lit_inj {v w : Value} {c : Int} (he : BinFn.apply .sub v (.int c) = BinFn.apply .sub w (.int c))
    (hn : BinFn.apply .sub v (.int c) ≠ .null) : v = w := by
  cases v <;> cases w <;> simp_all [BinFn.apply] <;> omega

/-- A linear term with a non-NULL value pins down its column. -/
theorem Expr.linTerm_inj {t : Expr} {j : Nat} {c : Int} {r r' : Row}
    (h : t.linTerm = some (j, c)) (he : t.eval r = t.eval r') (hn : t.eval r ≠ .null) :
    r.getD j .null = r'.getD j .null := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Expr.linTerm_spec h with ⟨rfl, rfl⟩ | rfl | rfl | rfl
  · simpa [eval] using he
  · exact add_lit_inj (by simpa [eval] using he) (by simpa [eval] using hn)
  · exact lit_add_inj (by simpa [eval] using he) (by simpa [eval] using hn)
  · exact sub_lit_inj (by simpa [eval] using he) (by simpa [eval] using hn)

theorem Expr.eqCols_det {e : Expr} {r r' : Row} (ht : (e.eval r).isTrue = true)
    (ht' : (e.eval r').isTrue = true) :
    ∀ p ∈ e.eqCols, (r.getD p.1 .null = r'.getD p.1 .null → r.getD p.2 .null = r'.getD p.2 .null) ∧
      (r.getD p.2 .null = r'.getD p.2 .null → r.getD p.1 .null = r'.getD p.1 .null) := by
  fun_induction Expr.eqCols e
  case case1 p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht ht'
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ihp ht.1 ht'.1 x hx
    · exact ihq ht.2 ht'.2 x hx
  case case2 t₁ t₂ i c₁ j c₂ h₂ h₁ =>
    intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    obtain ⟨he, hn⟩ := eq_true_same (by simpa [eval] using ht)
    obtain ⟨he', _⟩ := eq_true_same (by simpa [eval] using ht')
    constructor
    · intro hi
      have := Expr.linTerm_congr h₁ hi
      exact Expr.linTerm_inj h₂ (by rw [← he, this, he']) (he ▸ hn)
    · intro hj
      have := Expr.linTerm_congr h₂ hj
      exact Expr.linTerm_inj h₁ (by rw [he, this, ← he']) hn
  all_goals (intro x hx; simp_all)

/-- Does `on` determine the right side's columns `kb` (shifted by `n`) from
left-side columns? -/
def determinedCol (on : Expr) (n c : Nat) : Bool :=
  on.eqCols.any fun (i, j) => (i < n && j == n + c) || (j < n && i == n + c)

def determines (on : Expr) (n : Nat) (kb : List Nat) : Bool := kb.all (determinedCol on n)

theorem determines_sound {on : Expr} {n : Nat} {kb : List Nat} {x y y' : Row}
    (hd : determines on n kb = true) (hx : x.length = n)
    (ht : (on.eval (x ++ y)).isTrue = true) (ht' : (on.eval (x ++ y')).isTrue = true) :
    keyOf kb y = keyOf kb y' := by
  simp only [determines, determinedCol, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
  simp only [keyOf, List.map_inj_left]
  intro c hc
  obtain ⟨⟨i, j⟩, hp, hij⟩ := hd c hc
  have hdet := Expr.eqCols_det ht ht' (i, j) hp
  rw [← getD_append_right' (x := x) c, ← getD_append_right' (x := x) c, hx]
  rcases hij with ⟨hi, rfl⟩ | ⟨hj, rfl⟩
  · exact hdet.1 (by rw [getD_append_left' (hx ▸ hi), getD_append_left' (hx ▸ hi)])
  · exact hdet.2 (by rw [getD_append_left' (hx ▸ hj), getD_append_left' (hx ▸ hj)])

/-! ## Keys through a plan -/

/-- Re-index a key for an emit: each column must still be present. -/
def emitKey (m : List Nat) : List Nat → Option (List Nat)
  | [] => some []
  | c :: k => do
      let p ← (positions m c).head?
      let k' ← emitKey m k
      return p :: k'

theorem emitKey_keyOf {m : List Nat} {row : Row} :
    ∀ {k k' : List Nat}, emitKey m k = some k' →
      keyOf k' (m.map (row.getD · .null)) = keyOf k row
  | [], k', h => by simp [emitKey] at h; subst h; rfl
  | c :: k, k', h => by
      simp only [emitKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, hp, k'', hk, rfl⟩ := h
      have hmem : p ∈ positions m c := List.mem_of_mem_head? hp
      simp only [keyOf, List.map_cons, List.cons.injEq] at *
      exact ⟨positions_getD hmem, emitKey_keyOf hk⟩

/-- Every way of replacing each key column `c` by one of `σ c`. -/
def variants (σ : Nat → List Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | c :: k => (σ c).flatMap fun p => (variants σ k).map (p :: ·)

theorem variants_keyOf {σ : Nat → List Nat} {row row' : Row} :
    ∀ {k k' : List Nat}, (∀ c ∈ k, ∀ p ∈ σ c, row'.getD p .null = row.getD c .null) →
      k' ∈ variants σ k → keyOf k' row' = keyOf k row
  | [], k', _, hk' => by simp [variants] at hk'; subst hk'; rfl
  | c :: k, k', hσ, hk' => by
      simp only [variants, List.mem_flatMap, List.mem_map] at hk'
      obtain ⟨p, hp, k'', hk'', rfl⟩ := hk'
      simp only [keyOf, List.map_cons, List.cons.injEq]
      exact ⟨hσ c (by simp) p hp,
        variants_keyOf (fun c' hc' => hσ c' (by simp [hc'])) hk''⟩

/-- `variants` for substitutes that are injective rather than equal: rows
that agree on a variant agree on the original key. -/
theorem variants_inj {σ : Nat → List Nat} {r₁ r₂ r₁' r₂' : Row} :
    ∀ {k k' : List Nat},
      (∀ c ∈ k, ∀ p ∈ σ c, r₁'.getD p .null = r₂'.getD p .null → r₁.getD c .null = r₂.getD c .null) →
      k' ∈ variants σ k → keyOf k' r₁' = keyOf k' r₂' → keyOf k r₁ = keyOf k r₂
  | [], _, _, _, _ => rfl
  | c :: k, k', hσ, hk', he => by
      simp only [variants, List.mem_flatMap, List.mem_map] at hk'
      obtain ⟨p, hp, k'', hk'', rfl⟩ := hk'
      simp only [keyOf, List.map_cons, List.cons.injEq] at he ⊢
      exact ⟨hσ c (by simp) p hp he.1, variants_inj (fun c' hc' => hσ c' (by simp [hc'])) hk'' he.2⟩

def AVal.intOnly (a : AVal) : Bool := !a.null && !a.tt && !a.ff && !a.str

theorem AVal.intOnly_mem {a : AVal} {v : Value} (h : a.intOnly = true) (hm : a.Mem v) :
    ∃ y, v = .int y := by
  simp only [AVal.intOnly, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases mem_cases hm with ⟨_, hn⟩ | ⟨i, _, rfl, _, _⟩ | ⟨_, ht⟩ | ⟨_, hf⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩
  · simp_all
  · exact ⟨i, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all

/-- Computed columns `$i + c` of a non-NULL integer column `i`: injective in
`i`, so they can stand in for it in a key (`ROW_NUMBER() - 1`, say). -/
def linCols (n : Nat) (es : List Expr) (env : List AVal) (i : Nat) : List Nat :=
  if (env.getD i AVal.top).intOnly then
    ((List.range es.length).filter fun q => ((es[q]?).bind Expr.linTerm).map (·.1) == some i).map (n + ·)
  else []

theorem linCols_inj {n : Nat} {es : List Expr} {env : List AVal} {x₁ x₂ : Row} {i p : Nat}
    (h₁ : x₁.length = n) (h₂ : x₂.length = n) (hm₁ : EnvMem env x₁) (hm₂ : EnvMem env x₂)
    (hp : p ∈ linCols n es env i)
    (he : (x₁ ++ es.map (·.eval x₁)).getD p .null = (x₂ ++ es.map (·.eval x₂)).getD p .null) :
    x₁.getD i .null = x₂.getD i .null := by
  unfold linCols at hp
  split at hp
  · rename_i hint
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hp
    obtain ⟨q, ⟨hq, hlin⟩, rfl⟩ := hp
    have hq' : es[q]? = some es[q] := List.getElem?_eq_getElem hq
    rw [hq'] at hlin
    obtain ⟨c, hl⟩ : ∃ c, es[q].linTerm = some (i, c) := by simpa using hlin
    obtain ⟨y₁, hy₁⟩ := AVal.intOnly_mem hint (hm₁ i)
    obtain ⟨y₂, hy₂⟩ := AVal.intOnly_mem hint (hm₂ i)
    have e₁ : (x₁ ++ es.map (·.eval x₁)).getD (n + q) .null = es[q].eval x₁ := by
      rw [← h₁, getD_append_right']; simp [List.getD_eq_getElem?_getD, List.getElem?_map, hq']
    have e₂ : (x₂ ++ es.map (·.eval x₂)).getD (n + q) .null = es[q].eval x₂ := by
      rw [← h₂, getD_append_right']; simp [List.getD_eq_getElem?_getD, List.getElem?_map, hq']
    rw [e₁, e₂, Expr.linTerm_int hl hy₁, Expr.linTerm_int hl hy₂] at he
    rw [hy₁, hy₂]
    simp only [Value.int.injEq] at he ⊢
    omega
  · simp at hp

/-- Columns `e` fixes to a constant on the rows where it is TRUE. -/
def Expr.pinned : Expr → List Nat
  | .bin .and p q => p.pinned ++ q.pinned
  | .bin .eq (.field i) (.lit _) => [i]
  | .bin .eq (.lit _) (.field i) => [i]
  | _ => []

theorem Expr.pinned_sound {e : Expr} {r r' : Row} (ht : (e.eval r).isTrue = true)
    (ht' : (e.eval r').isTrue = true) : ∀ i ∈ e.pinned, r.getD i .null = r'.getD i .null := by
  fun_induction Expr.pinned e
  case case1 p q ihp ihq =>
    simp only [eval, BinFn.apply, isTrue_and3, Bool.and_eq_true] at ht ht'
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ihp ht.1 ht'.1 x hx
    · exact ihq ht.2 ht'.2 x hx
  case case2 i v =>
    intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    obtain ⟨he, _⟩ := eq_true_same (by simpa [eval] using ht)
    obtain ⟨he', _⟩ := eq_true_same (by simpa [eval] using ht')
    simp_all [List.getD_eq_getElem?_getD]
  case case3 v i =>
    intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    obtain ⟨he, _⟩ := eq_true_same (by simpa [eval] using ht)
    obtain ⟨he', _⟩ := eq_true_same (by simpa [eval] using ht')
    simp_all [List.getD_eq_getElem?_getD]
  all_goals (intro x hx; simp_all)

/-- Keys of a join: a key of the left side, plus the columns of a right key
that the condition doesn't tie to the left side (`a.device = b.device` makes
`b.device` redundant once `a`'s row is fixed). -/
def joinKeys (n : Nat) (on : Expr) (ka kb : List (List Nat)) : List (List Nat) :=
  (ka.filter (·.all (· < n))).flatMap fun k =>
    kb.map fun k' => k ++ (k'.filter (!determinedCol on n ·)).map (n + ·)

/-- `ROW_NUMBER()` with the partition columns is a key of a window. -/
def windowKeys (part : List Nat) (n : Nat) (fns : List WinFn) : List (List Nat) :=
  fns.zipIdx.filterMap fun (f, t) => if f = .rowNumber then some (part ++ [n + t]) else none

def crossKeys (n : Nat) (ka kb : List (List Nat)) : List (List Nat) :=
  (ka.filter (·.all (· < n))).flatMap fun k => kb.map fun k' => k ++ k'.map (n + ·)

def Rel.keys (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → List (List Nat)
  | .read t => K t
  | .values _ rows => if rows.length ≤ 1 then [[]] else []
  -- Columns the condition pins to a constant are redundant in a key.
  | .filter r c => (r.keys cat A F K).map (·.filter (!c.pinned.contains ·))
  -- A key may use any copy of its columns (DataFusion copies join columns this way).
  | .project r es =>
      ((r.keys cat A F K).filter (·.all (· < r.arity cat))).flatMap
        (variants fun i => copyCols (r.arity cat) es i ++ linCols (r.arity cat) es (r.aeval cat A F .none) i)
  | .emit r m => (r.keys cat A F K).filterMap (emitKey m)
  | .cross a b => crossKeys (a.arity cat) (a.keys cat A F K) (b.keys cat A F K)
  | .join a b _ on => joinKeys (a.arity cat) on (a.keys cat A F K) (b.keys cat A F K)
  | .fetch r _ cnt => (if cnt.any (· ≤ 1) then [[]] else []) ++ r.keys cat A F K
  | .unionAll _ _ => []
  | .window r part _ fns =>
      (r.keys cat A F K).filter (·.all (· < r.arity cat)) ++ windowKeys part (r.arity cat) fns
  | .semi a _ _ _ => a.keys cat A F K
  | .orderBy r _ => r.keys cat A F K
  -- After `DISTINCT`, all columns together are a key.
  | .distinct r => List.range (r.arity cat) :: r.keys cat A F K
  -- The grouping columns are a key (without them, there is one row).
  | .aggregate _ gs _ => [List.range gs.length]
  -- An element can repeat.
  | .unnest _ _ => []

theorem crossRows_key {A B : Relation} {n : Nat} {ka kb : List Nat}
    (hA : ∀ x ∈ A, x.length = n) (hka : ∀ c ∈ ka, c < n)
    (hkA : KeyOn ka A) (hkB : KeyOn kb B) :
    KeyOn (ka ++ kb.map (n + ·)) (crossRows A B) := by
  unfold KeyOn crossRows
  rw [List.pairwise_flatMap]
  constructor
  · intro x hx
    rw [List.pairwise_map]
    refine hkB.imp fun hne heq => hne ?_
    rw [← hA x hx, keyOf_cross (fun c hc => hA x hx ▸ hka c hc),
      keyOf_cross (fun c hc => hA x hx ▸ hka c hc)] at heq
    exact List.append_cancel_left heq
  · refine List.Pairwise.imp_of_mem (fun {x x'} hx hx' hne r hr s hs heq => hne ?_) hkA
    simp only [List.mem_map] at hr hs
    obtain ⟨y, _, rfl⟩ := hr
    obtain ⟨y', _, rfl⟩ := hs
    rw [← hA x hx, keyOf_cross (fun c hc => hA x hx ▸ hka c hc)] at heq
    rw [hA x hx, ← hA x' hx', keyOf_cross (fun c hc => hA x' hx' ▸ hka c hc)] at heq
    exact (List.append_inj heq (by simp [keyOf])).1

/-- If `on` determines a key of the right side, each left row has at most one
partner, so left keys survive the join. -/
theorem join_key {A B : Relation} {n : Nat} {on : Expr} {ka kb : List Nat}
    (hA : ∀ x ∈ A, x.length = n) (hka : ∀ c ∈ ka, c < n) (hkA : KeyOn ka A)
    (hkB : KeyOn kb B) (hd : determines on n kb = true) :
    KeyOn ka (A.flatMap fun x => ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue)) := by
  unfold KeyOn
  rw [List.pairwise_flatMap]
  constructor
  · intro x hx
    rw [List.pairwise_filter, List.pairwise_map]
    exact hkB.imp fun hne ht ht' _ => hne (determines_sound hd (hA x hx) ht ht')
  · refine List.Pairwise.imp_of_mem (fun {x x'} hx hx' hne r hr s hs heq => hne ?_) hkA
    simp only [List.mem_filter, List.mem_map] at hr hs
    obtain ⟨⟨y, _, rfl⟩, _⟩ := hr
    obtain ⟨⟨y', _, rfl⟩, _⟩ := hs
    rwa [keyOf_append_left (fun c hc => hA x hx ▸ hka c hc),
      keyOf_append_left (fun c hc => hA x' hx' ▸ hka c hc)] at heq

theorem left_join_key {A B : Relation} {n m : Nat} {on : Expr} {ka kb : List Nat}
    (hA : ∀ x ∈ A, x.length = n) (hka : ∀ c ∈ ka, c < n) (hkA : KeyOn ka A)
    (hkB : KeyOn kb B) (hd : determines on n kb = true) :
    KeyOn ka (A.flatMap (leftJoinRow on m B)) := by
  unfold KeyOn
  rw [List.pairwise_flatMap]
  have hprefix : ∀ x ∈ A, ∀ r ∈ leftJoinRow on m B x, keyOf ka r = keyOf ka x := by
    intro x hx r hr
    unfold leftJoinRow at hr
    simp only [] at hr
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact keyOf_append_left fun c hc => hA x hx ▸ hka c hc
    · simp only [List.mem_filter, List.mem_map] at hr
      obtain ⟨⟨y, _, rfl⟩, _⟩ := hr
      exact keyOf_append_left fun c hc => hA x hx ▸ hka c hc
  constructor
  · intro x hx
    unfold leftJoinRow
    simp only []
    split
    · exact List.pairwise_singleton _ _
    · rw [List.pairwise_filter, List.pairwise_map]
      exact hkB.imp fun hne ht ht' _ => hne (determines_sound hd (hA x hx) ht ht')
  · refine List.Pairwise.imp_of_mem (fun {x x'} hx hx' hne r hr s hs heq => hne ?_) hkA
    rwa [hprefix x hx r hr, hprefix x' hx' s hs] at heq

/-- Join outputs come in one block per left row `x`, each row extending `x`:
a left key plus a key within each block is a key. -/
theorem flatMap_key {A : Relation} {ka kR : List Nat} {f : Row → Relation} (hkA : KeyOn ka A)
    (hpre : ∀ x ∈ A, ∀ r ∈ f x, keyOf ka r = keyOf ka x)
    (hblock : ∀ x ∈ A, (f x).Pairwise fun r s => keyOf kR r ≠ keyOf kR s) :
    KeyOn (ka ++ kR) (A.flatMap f) := by
  unfold KeyOn
  rw [List.pairwise_flatMap]
  have hsplit : ∀ r, keyOf (ka ++ kR) r = keyOf ka r ++ keyOf kR r := fun r => by simp [keyOf]
  constructor
  · intro x hx
    refine (hblock x hx).imp_of_mem fun hr hs hne heq => hne ?_
    rw [hsplit, hsplit, hpre x hx _ hr, hpre x hx _ hs] at heq
    exact List.append_cancel_left heq
  · refine List.Pairwise.imp_of_mem (fun {x x'} hx hx' hne r hr s hs heq => hne ?_) hkA
    rw [hsplit, hsplit] at heq
    have := (List.append_inj heq (by simp [keyOf])).1
    rwa [hpre x hx r hr, hpre x' hx' s hs] at this

/-- The partners of one left row differ on the right key's columns that the
condition doesn't tie to the left row. -/
theorem match_block {B : Relation} {n : Nat} {on : Expr} {kb : List Nat} {x : Row}
    (hx : x.length = n) (hkB : KeyOn kb B) :
    ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue).Pairwise fun r s =>
      keyOf ((kb.filter fun c => !determinedCol on n c).map (n + ·)) r ≠
        keyOf ((kb.filter fun c => !determinedCol on n c).map (n + ·)) s := by
  rw [List.pairwise_filter, List.pairwise_map]
  refine hkB.imp fun {y y'} hne ht ht' heq => hne ?_
  subst hx
  rw [keyOf_shift, keyOf_shift] at heq
  have hD := determines_sound (on := on) (kb := kb.filter (determinedCol on x.length))
    (by simp only [determines, List.all_eq_true, List.mem_filter]; exact fun c hc => hc.2) rfl ht ht'
  simp only [keyOf, List.map_inj_left, List.mem_filter, Bool.not_eq_true'] at heq hD ⊢
  intro c hc
  cases h : determinedCol on x.length c
  · exact heq c ⟨hc, h⟩
  · exact hD c ⟨hc, h⟩

theorem mem_windowRows_ext {part : List Nat} {fns : List WinFn} :
    ∀ {pre l : List Row} {row : Row}, row ∈ windowRows part fns pre l →
      ∃ b₀ x a, l = b₀ ++ x :: a ∧ row = x ++ fns.map (·.value part (pre ++ b₀) a x)
  | _, [], _, h => by simp [windowRows] at h
  | pre, y :: l, row, h => by
      simp only [windowRows, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨[], y, l, rfl, by simp⟩
      · obtain ⟨b₀, x, a, rfl, rfl⟩ := mem_windowRows_ext h
        exact ⟨y :: b₀, x, a, rfl, by simp⟩

theorem keyOf_window {part : List Nat} {fns : List WinFn} {n t : Nat} {x : Row}
    {g : WinFn → Value} (hx : x.length = n) (hpart : ∀ i ∈ part, i < n)
    (ht : fns[t]? = some WinFn.rowNumber) :
    keyOf (part ++ [n + t]) (x ++ fns.map g) = keyOf part x ++ [g .rowNumber] := by
  have hsplit : keyOf (part ++ [n + t]) (x ++ fns.map g) =
      keyOf part (x ++ fns.map g) ++ [(x ++ fns.map g).getD (n + t) .null] := by simp [keyOf]
  rw [hsplit, keyOf_append_left (fun c hc => hx ▸ hpart c hc), ← hx, getD_append_right']
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, ht]

/-- Row numbers differ within a partition. -/
theorem windowRows_rowNumber_key {part : List Nat} {fns : List WinFn} {n t : Nat}
    (hpart : ∀ i ∈ part, i < n) (ht : fns[t]? = some WinFn.rowNumber) :
    ∀ {pre l : List Row}, (∀ x ∈ l, x.length = n) →
      KeyOn (part ++ [n + t]) (windowRows part fns pre l)
  | _, [], _ => List.Pairwise.nil
  | pre, x :: l, hl => by
      unfold KeyOn
      simp only [windowRows]
      rw [List.pairwise_cons]
      refine ⟨fun s hs heq => ?_, windowRows_rowNumber_key hpart ht fun y hy => hl y (by simp [hy])⟩
      obtain ⟨b₀, y, a, rfl, rfl⟩ := mem_windowRows_ext hs
      rw [keyOf_window (hl x (by simp)) hpart ht, keyOf_window (hl y (by simp)) hpart ht] at heq
      obtain ⟨hpk, hrn⟩ := List.append_inj heq (by simp [keyOf])
      have hsame : samePart part y = samePart part x := by
        funext z
        simp only [samePart, keyOf] at hpk ⊢
        rw [hpk]
      simp only [WinFn.value, WinFn.valueIn, hsame, List.filter_append, List.filter_cons_of_pos (samePart_refl part x),
        List.filter_nil, List.cons.injEq, Value.int.injEq, List.length_append, List.length_cons,
        List.length_nil, and_true] at hrn
      omega

/-- All the columns of a row are the row. -/
theorem keyOf_range {x : Row} {n : Nat} (h : x.length = n) : keyOf (List.range n) x = x := by
  subst h
  apply List.ext_getElem (by simp [keyOf])
  intro i h₁ h₂
  simp [keyOf, List.getD, List.getElem?_eq_getElem h₂]

theorem keyOf_range_append {k rest : Row} : keyOf (List.range k.length) (k ++ rest) = k := by
  apply List.ext_getElem (by simp [keyOf])
  intro i h₁ h₂
  simp [keyOf, List.getD, List.getElem?_append_left h₂, List.getElem?_eq_getElem h₂]

theorem aggregateEval_key (gs : List Expr) (ms : List Measure) (rows : Relation) :
    KeyOn (List.range gs.length) (aggregateEval gs ms rows) := by
  unfold aggregateEval KeyOn
  split
  · simp
  · rw [List.pairwise_map]
    refine (dedup_pairwise _).imp_of_mem fun hx hy hne => ?_
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp (mem_dedup.mp hx)
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp (mem_dedup.mp hy)
    have hlx : (groupKey gs x).length = gs.length := by simp [groupKey]
    have hly : (groupKey gs y).length = gs.length := by simp [groupKey]
    rw [← hlx, keyOf_range_append]
    rw [hlx, ← hly, keyOf_range_append]
    exact hne

/-- **Soundness of key derivation.** -/
theorem Rel.keys_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → ∀ k ∈ r.keys cat A F K, KeyOn k (r.eval cat)
  | .read t, _, k, hk => hK t k hk
  | .values _ rows, _, k, hk => by
      simp only [Rel.keys] at hk
      split at hk
      · simp only [List.mem_singleton] at hk
        subst hk
        exact KeyOn.of_length_le_one ‹_›
      · simp at hk
  | .filter r c, hwf, k, hk => by
      simp only [Rel.keys, List.mem_map] at hk
      obtain ⟨k₀, hk₀, rfl⟩ := hk
      have := keys_sound hcat hA hF hK hwf.1 k₀ hk₀
      unfold KeyOn at *
      simp only [eval]
      rw [List.pairwise_filter]
      refine this.imp fun {x y} hne hx hy heq => hne ?_
      have hp := Expr.pinned_sound hx hy
      simp only [keyOf, List.map_inj_left, List.mem_filter, Bool.not_eq_true'] at heq ⊢
      intro i hi
      by_cases h : i ∈ c.pinned
      · exact hp i h
      · exact heq i ⟨hi, by simpa using h⟩
  | .project r es, hwf, k, hk => by
      simp only [Rel.keys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq] at hk
      obtain ⟨k₀, ⟨hk₀, hr⟩, hv⟩ := hk
      have := keys_sound hcat hA hF hK hwf.1 k₀ hk₀
      unfold KeyOn at *
      simp only [eval]
      rw [List.pairwise_map]
      refine this.imp_of_mem fun {x y} hx hy hne heq => hne ?_
      refine variants_inj (fun c hc p hp he => ?_) hv heq
      rcases List.mem_append.mp hp with hp | hp
      · rwa [copyCols_getD (eval_arity hcat hwf.1 _ hx) (hr c hc) hp,
          copyCols_getD (eval_arity hcat hwf.1 _ hy) (hr c hc) hp] at he
      · exact linCols_inj (eval_arity hcat hwf.1 _ hx) (eval_arity hcat hwf.1 _ hy)
          (aeval_sound hcat hA hF (WindowKeys.none_sound cat) (sz := false) hwf.1 nofun _ hx)
          (aeval_sound hcat hA hF (WindowKeys.none_sound cat) (sz := false) hwf.1 nofun _ hy) hp he
  | .emit r m, hwf, k, hk => by
      simp only [Rel.keys, List.mem_filterMap] at hk
      obtain ⟨k₀, hk₀, he⟩ := hk
      have := keys_sound hcat hA hF hK hwf.1 k₀ hk₀
      unfold KeyOn at *
      simp only [eval]
      rw [List.pairwise_map]
      refine this.imp fun hne heq => hne ?_
      rwa [emitKey_keyOf he, emitKey_keyOf he] at heq
  | .cross a b, hwf, k, hk => by
      simp only [Rel.keys, crossKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk
      exact crossRows_key (eval_arity hcat hwf.1) hkr (keys_sound hcat hA hF hK hwf.1 ka hka)
        (keys_sound hcat hA hF hK hwf.2 kb hkb)
  | .join a b .inner on, hwf, k, hk => by
      simp only [Rel.keys, joinKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk
      have hA' := eval_arity hcat hwf.1
      simp only [eval, crossRows, List.filter_flatMap]
      exact flatMap_key (keys_sound hcat hA hF hK hwf.1 ka hka)
        (fun x hx r hr => by
          simp only [List.mem_filter, List.mem_map] at hr
          obtain ⟨⟨y, _, rfl⟩, _⟩ := hr
          exact keyOf_append_left fun c hc => hA' x hx ▸ hkr c hc)
        (fun x hx => match_block (hA' x hx) (keys_sound hcat hA hF hK hwf.2.1 kb hkb))
  | .join a b .left on, hwf, k, hk => by
      simp only [Rel.keys, joinKeys, List.mem_flatMap, List.mem_filter, List.all_eq_true,
        decide_eq_true_eq, List.mem_map] at hk
      obtain ⟨ka, ⟨hka, hkr⟩, kb, hkb, rfl⟩ := hk
      have hA' := eval_arity hcat hwf.1
      simp only [eval]
      refine flatMap_key (keys_sound hcat hA hF hK hwf.1 ka hka) (fun x hx r hr => ?_) (fun x hx => ?_)
      · unfold leftJoinRow at hr
        simp only [] at hr
        split at hr
        · simp only [List.mem_singleton] at hr; subst hr
          exact keyOf_append_left fun c hc => hA' x hx ▸ hkr c hc
        · simp only [List.mem_filter, List.mem_map] at hr
          obtain ⟨⟨y, _, rfl⟩, _⟩ := hr
          exact keyOf_append_left fun c hc => hA' x hx ▸ hkr c hc
      · unfold leftJoinRow
        simp only []
        split
        · exact List.pairwise_singleton _ _
        · exact match_block (hA' x hx) (keys_sound hcat hA hF hK hwf.2.1 kb hkb)
  | .fetch r _ cnt, hwf, k, hk => by
      simp only [Rel.keys, List.mem_append] at hk
      rcases hk with hk | hk
      · split at hk
        · simp only [List.mem_singleton] at hk
          subst hk
          obtain ⟨n, rfl, hn⟩ : ∃ n, cnt = some n ∧ n ≤ 1 := by
            cases cnt <;> simp_all
          simp only [eval]
          exact KeyOn.of_length_le_one (Nat.le_trans (List.length_take_le _ _) hn)
        · simp at hk
      simp only [eval]
      have := keys_sound hcat hA hF hK (r := r) hwf k hk
      split
      · exact this.sublist (List.drop_sublist _ _)
      · exact this.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  | .unionAll _ _, _, k, hk => by simp [Rel.keys] at hk
  | .semi a _ _ _, hwf, k, hk =>
      (keys_sound hcat hA hF hK hwf.1 k hk).sublist List.filter_sublist
  | .orderBy r _, hwf, k, hk =>
      (keys_sound hcat hA hF hK (r := r) hwf.1 k hk).perm (List.mergeSort_perm _ _).symm
        fun h => Ne.symm h
  | .unnest _ _, _, k, hk => by simp [Rel.keys] at hk
  | .distinct r, hwf, k, hk => by
      simp only [Rel.keys, List.mem_cons] at hk
      rcases hk with rfl | hk
      · show (dedup (r.eval cat)).Pairwise _
        refine (dedup_pairwise (r.eval cat)).imp_of_mem fun hx hy hne => ?_
        rw [keyOf_range (eval_arity hcat (r := r) hwf _ (mem_dedup.mp hx)),
          keyOf_range (eval_arity hcat (r := r) hwf _ (mem_dedup.mp hy))]
        exact hne
      · exact (keys_sound hcat hA hF hK (r := r) hwf k hk).sublist (dedup_sublist _)
  | .aggregate r gs ms, _, k, hk => by
      simp only [Rel.keys, List.mem_singleton] at hk
      subst hk
      exact aggregateEval_key gs ms (r.eval cat)
  | .window r part sort fns, hwf, k, hk => by
      simp only [Rel.keys, List.mem_append] at hk
      rcases hk with hk | hk
      rotate_left
      · simp only [windowKeys, List.mem_filterMap] at hk
        obtain ⟨⟨f, t⟩, hft, hk⟩ := hk
        split at hk
        · rename_i hf
          subst hf
          simp only [Option.some.injEq] at hk
          subst hk
          exact windowRows_rowNumber_key hwf.2.1 (List.mem_zipIdx_iff_getElem?.mp hft)
            fun x hx => eval_arity hcat hwf.1 x (List.mem_mergeSort.mp hx)
        · simp at hk
      simp only [List.mem_filter, List.all_eq_true, decide_eq_true_eq] at hk
      have hs : KeyOn k ((r.eval cat).mergeSort (sortLe sort)) :=
        (keys_sound hcat hA hF hK hwf.1 k hk.1).perm (List.mergeSort_perm _ _).symm fun h => Ne.symm h
      have hmap : (windowEval part sort fns (r.eval cat)).map (keyOf k) =
          ((r.eval cat).mergeSort (sortLe sort)).map (keyOf k) := by
        have ht := windowRows_take (part := part) (fns := fns) (pre := []) (n := r.arity cat)
          (l := (r.eval cat).mergeSort (sortLe sort))
          (fun x hx => eval_arity hcat hwf.1 x (List.mem_mergeSort.mp hx))
        unfold windowEval
        conv => rhs; rw [← ht]
        rw [List.map_map]
        exact List.map_congr_left fun row _ => (keyOf_take hk.2).symm
      have h1 : List.Pairwise (· ≠ ·) (((r.eval cat).mergeSort (sortLe sort)).map (keyOf k)) :=
        List.pairwise_map.mpr hs
      rw [← hmap] at h1
      exact List.pairwise_map.mp h1

/-! ## Fan-out of a join on a key

A join whose condition determines a key of its right side gives each left
row at most one partner, so it has at most as many rows as its left side
(a left join keeps a row without partners as one row). Row bounds (#219) use
this where a product of the sides would be far too large. -/

theorem length_flatMap_le {α β : Type} {f : α → List β} {k : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).length ≤ k) → (l.flatMap f).length ≤ l.length * k
  | [], _ => by simp
  | x :: l, h => by
    have := length_flatMap_le (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem length_le_one_of_pairwise_false {α : Type} :
    ∀ {l : List α}, l.Pairwise (fun _ _ => False) → l.length ≤ 1
  | [], _ | [_], _ => by simp
  | _ :: b :: _, h => ((List.pairwise_cons.1 h).1 b (List.mem_cons_self ..)).elim

/-- On a key of the right side that the condition determines, a left row has
at most one partner. -/
theorem partners_le_one {B : Relation} {n : Nat} {on : Expr} {kb : List Nat} {x : Row}
    (hx : x.length = n) (hkB : KeyOn kb B) (hd : determines on n kb = true) :
    ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ 1 := by
  apply length_le_one_of_pairwise_false
  rw [List.pairwise_filter, List.pairwise_map]
  exact hkB.imp fun hne ht ht' => hne (determines_sound hd hx ht ht')

/-- Does the join condition determine a key of the right side? -/
def Rel.keyedJoin (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (a b : Rel) (on : Expr) : Bool :=
  (b.keys cat A F K).any (determines on (a.arity cat))

/-- **A join on a key does not fan out**: inner or left, it has at most as
many rows as its left side. -/
theorem Rel.join_length_le_of_keyed {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {a b : Rel} {ty : JoinType} {on : Expr}
    (hwf : (Rel.join a b ty on).WF cat) (hkey : Rel.keyedJoin cat A F K a b on = true) :
    ((Rel.join a b ty on).eval cat).length ≤ (a.eval cat).length := by
  obtain ⟨kb, hkb, hd⟩ := List.any_eq_true.1 hkey
  have hkB := Rel.keys_sound hcat hA hF hK hwf.2.1 kb hkb
  have hp : ∀ x ∈ a.eval cat,
      (((b.eval cat).map (x ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ 1 :=
    fun x hx => partners_le_one (Rel.eval_arity hcat hwf.1 x hx) hkB hd
  refine Nat.le_trans ?_ (Nat.le_of_eq (Nat.mul_one _))
  cases ty with
  | inner =>
    simp only [Rel.eval, crossRows, List.filter_flatMap]
    exact length_flatMap_le hp
  | left =>
    simp only [Rel.eval]
    refine length_flatMap_le fun x hx => ?_
    unfold leftJoinRow
    simp only []
    split
    · simp
    · exact hp x hx

end Substrait

/-! ## Deterministic windows

`Rel.eval` sorts a window's input with a stable merge sort; an engine may
break ties between rows with equal sort keys differently, and then `LAG`,
`LEAD` and `ROW_NUMBER` differ. When the partition and sort columns form a
key there are no ties within a partition: every sorted arrangement gives the
same rows (`window_tiebreak`). `Rel.windowsTotal` checks this for every
window of a plan with the derived keys. -/

namespace Substrait

theorem KeyOn.eq_of_keyOf {k : List Nat} : ∀ {rows : Relation}, KeyOn k rows →
    ∀ {x y : Row}, x ∈ rows → y ∈ rows → keyOf k x = keyOf k y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | z :: rows, h, x, y, hx, hy, he => by
      unfold KeyOn at h
      rw [List.pairwise_cons] at h
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exact absurd he (h.1 y hy)
      · exact absurd he.symm (h.1 x hx)
      · exact KeyOn.eq_of_keyOf h.2 hx hy he

theorem KeyOn.nodup {k : List Nat} {rows : Relation} (h : KeyOn k rows) : rows.Nodup :=
  h.imp fun hne heq => hne (by rw [heq])

/-- Two sorted arrangements of the same rows are equal when the order has
no ties between different rows. -/
theorem eq_of_perm_of_pairwise {le : Row → Row → Bool} :
    ∀ {l₁ l₂ : List Row}, l₁.Perm l₂ → l₁.Pairwise (le · · = true) → l₂.Pairwise (le · · = true) →
      (∀ x ∈ l₁, ∀ y ∈ l₁, le x y = true → le y x = true → x = y) → l₁ = l₂
  | [], _, hp, _, _, _ => (List.nil_perm.mp hp).symm
  | _ :: _, [], hp, _, _, _ => absurd hp.length_eq (by simp)
  | x :: t, y :: u, hp, h₁, h₂, ha => by
      rw [List.pairwise_cons] at h₁ h₂
      have hxy : x = y := by
        have hx : x ∈ y :: u := hp.subset (by simp)
        have hy : y ∈ x :: t := hp.symm.subset (by simp)
        simp only [List.mem_cons] at hx hy
        rcases hx with hx | hx
        · exact hx
        rcases hy with hy | hy
        · exact hy.symm
        exact ha x (by simp) y (by simp [hy]) (h₁.1 y hy) (h₂.1 x hx)
      subst hxy
      congr 1
      exact eq_of_perm_of_pairwise hp.cons_inv h₁.2 h₂.2
        fun a ha' b hb => ha a (by simp [ha']) b (by simp [hb])

/-- The rows of `P` before and after the first occurrence of `x`. -/
def splitAt (x : Row) (P : List Row) : List Row × List Row :=
  (P.takeWhile (· != x), (P.dropWhile (· != x)).drop 1)

theorem splitAt_eq {x : Row} : ∀ {B A : List Row}, x ∉ B → splitAt x (B ++ x :: A) = (B, A)
  | [], A, _ => by simp [splitAt]
  | y :: B, A, h => by
      simp only [List.mem_cons, not_or] at h
      have := splitAt_eq (A := A) h.2
      simp only [splitAt, Prod.mk.injEq] at this ⊢
      have hyx : (y != x) = true := bne_iff_ne.mpr (Ne.symm h.1)
      simp [hyx, this]

theorem WinFn.value_filter (part : List Nat) (b a : List Row) (x : Row) (f : WinFn) :
    f.value part b a x = f.value part (b.filter (samePart part x)) (a.filter (samePart part x)) x := by
  cases f <;> simp [WinFn.value, List.filter_filter]

/-- A window row computed from the row's partition alone. -/
def winRow (part : List Nat) (fns : List WinFn) (s : List Row) (x : Row) : Row :=
  let P := s.filter (samePart part x)
  x ++ fns.map (·.value part (splitAt x P).1 (splitAt x P).2 x)

theorem windowRows_eq_map {part : List Nat} {fns : List WinFn} {s : List Row} (hs : s.Nodup) :
    ∀ {pre l : List Row}, pre ++ l = s → windowRows part fns pre l = l.map (winRow part fns s)
  | _, [], _ => rfl
  | pre, x :: l, he => by
      simp only [windowRows, List.map_cons, List.cons.injEq]
      refine ⟨?_, windowRows_eq_map hs (by simp [← he])⟩
      have hx : x ∉ pre := by
        rw [← he] at hs
        exact fun h => (List.nodup_append.mp hs).2.2 x h x (by simp) rfl
      have hP : s.filter (samePart part x) =
          pre.filter (samePart part x) ++ x :: l.filter (samePart part x) := by
        rw [← he, List.filter_append, List.filter_cons_of_pos (samePart_refl part x)]
      simp only [winRow, hP, splitAt_eq (fun h => hx (List.mem_filter.mp h).1)]
      congr 1
      exact List.map_congr_left fun f _ => WinFn.value_filter part pre l x f

/-- **Tie-breaking doesn't matter** when the partition and sort columns form a
key: any arrangement `s` of the input sorted by the window's keys gives the
same rows as `Rel.eval`'s stable sort. -/
theorem window_tiebreak {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {rows : Relation} (hk : KeyOn (part ++ sort.map (·.col)) rows) {s : List Row}
    (hp : s.Perm rows) (hs : s.Pairwise (sortLe sort · · = true)) :
    (windowRows part fns [] s).Perm (windowEval part sort fns rows) := by
  have hp₀ := List.mergeSort_perm rows (sortLe sort)
  have hs₀ := List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total rows
  have hk' : KeyOn _ s := hk.perm hp.symm fun h => Ne.symm h
  have hk₀ : KeyOn _ (rows.mergeSort (sortLe sort)) := hk.perm hp₀.symm fun h => Ne.symm h
  have hpart : ∀ x, s.filter (samePart part x) = (rows.mergeSort (sortLe sort)).filter (samePart part x) := by
    intro x
    apply eq_of_perm_of_pairwise ((hp.trans hp₀.symm).filter _) (hs.filter _) (hs₀.filter _)
    intro y hy z hz hyz hzy
    simp only [List.mem_filter] at hy hz
    apply KeyOn.eq_of_keyOf hk' hy.1 hz.1
    simp only [keyOf, List.map_append, List.map_map]
    have h₁ := hy.2
    have h₂ := hz.2
    simp only [samePart, decide_eq_true_eq] at h₁ h₂
    rw [← h₁, ← h₂]
    congr 1
    simpa [Function.comp_def] using sortLe_antisymm hyz hzy
  unfold windowEval
  rw [windowRows_eq_map hk'.nodup (List.nil_append s),
    windowRows_eq_map hk₀.nodup (List.nil_append _)]
  have : s.map (winRow part fns s) = s.map (winRow part fns (rows.mergeSort (sortLe sort))) :=
    List.map_congr_left fun x _ => by simp only [winRow, hpart x]
  rw [this]
  exact (hp.trans hp₀.symm).map _

/-! ## Windows that do not depend on ties

A `COUNT` or a `SUM` of integers (or decimals) over the whole partition sees
the partition's rows as a bag: however ties are broken, every row gets the
same value (`window_orderFree`). Such a window needs no key. -/

/-- A window function whose value does not depend on how ties are broken. -/
def WinFn.orderFree : WinFn → Bool
  | .agg m _ fr => decide ((m.fn = .count ∨ m.fn = .sum) ∧ m.distinct = false ∧
      fr.lo = .unboundedPreceding ∧ fr.hi = .unboundedFollowing)
  | _ => false

private theorem intSum_perm_bag {l l' : List Value} (h : l.Perm l') : intSum l = intSum l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [intSum, ih]
  | swap x y l => cases x <;> cases y <;> simp [intSum] <;> omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem Measure.inputs_perm_bag {m : Measure} (hd : m.distinct = false) {rows rows' : Relation}
    (h : rows.Perm rows') : (m.inputs rows).Perm (m.inputs rows') := by
  have hk : (m.kept rows).Perm (m.kept rows') := by
    unfold Measure.kept; split
    · exact h
    · exact h.filter _
  simp only [Measure.inputs, hd, Bool.false_eq_true, ↓reduceIte]
  exact (hk.map _).filter _

/-- A `COUNT` or a `SUM` without `DISTINCT` sees its rows as a bag. -/
private theorem Measure.eval_perm_bag {m : Measure} (hf : m.fn = .count ∨ m.fn = .sum)
    (hd : m.distinct = false) {rows rows' : Relation} (h : rows.Perm rows') :
    m.eval rows = m.eval rows' := by
  have hc : m.fn.sorts = false := by rcases hf with hf | hf <;> rw [hf] <;> rfl
  rw [Measure.eval_eq hc, Measure.eval_eq hc]
  have hp := Measure.inputs_perm_bag hd h
  rcases hf with hf | hf
  · rw [hf]; simp [AggFn.apply, hp.length_eq]
  · rw [hf]
    cases hi : m.inputs rows with
    | nil => rw [hi] at hp; rw [List.nil_perm.mp hp]
    | cons v vs =>
      rw [hi] at hp
      cases hi' : m.inputs rows' with
      | nil => rw [hi'] at hp; exact absurd hp.length_eq (by simp)
      | cons w ws => rw [hi'] at hp; simp only [AggFn.apply, intSum_perm_bag hp]

/-- The frame of the whole partition. -/
theorem Frame.rows_all {fr : Frame} (hlo : fr.lo = .unboundedPreceding)
    (hhi : fr.hi = .unboundedFollowing) (sort : List SortKey) (pb : List Row) (x : Row)
    (pa : List Row) : fr.rows sort pb x pa = pb ++ x :: pa := by
  unfold Frame.rows
  simp only [hlo, hhi]
  split
  · exact List.filter_eq_self.mpr fun _ _ => rfl
  · rw [List.filter_eq_self.mpr fun ⟨_, j⟩ hj => by
        have := List.snd_lt_of_mem_zipIdx hj
        simp only [Nat.add_zero] at this
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega]
    exact List.zipIdx_map_fst 0 _

/-- An order-free function's value at `x`: from the rows of `x`'s partition. -/
def WinFn.wholeValue (part : List Nat) (all : List Row) (x : Row) : WinFn → Value
  | .agg m _ _ => m.eval (all.filter (samePart part x))
  | _ => .null

theorem WinFn.value_orderFree {f : WinFn} (hf : f.orderFree = true) (part : List Nat)
    (b a : List Row) (x : Row) : f.value part b a x = f.wholeValue part (b ++ x :: a) x := by
  match f, hf with
  | .agg m sort fr, hf =>
    simp only [WinFn.orderFree, decide_eq_true_eq] at hf
    simp only [WinFn.value, WinFn.valueIn, WinFn.wholeValue,
      Frame.rows_all hf.2.2.1 hf.2.2.2, List.filter_append, List.filter_cons, samePart_refl,
      ↓reduceIte]

theorem WinFn.wholeValue_perm {f : WinFn} (hf : f.orderFree = true) (part : List Nat)
    {all all' : List Row} (h : all.Perm all') (x : Row) :
    f.wholeValue part all x = f.wholeValue part all' x := by
  match f, hf with
  | .agg m _ _, hf =>
    simp only [WinFn.orderFree, decide_eq_true_eq] at hf
    exact Measure.eval_perm_bag hf.1 hf.2.1 (h.filter _)

theorem windowRows_orderFree {part : List Nat} {fns : List WinFn}
    (hf : fns.all WinFn.orderFree = true) :
    ∀ (pre l : List Row), windowRows part fns pre l =
      l.map fun x => x ++ fns.map (·.wholeValue part (pre ++ l) x)
  | _, [] => rfl
  | pre, x :: l => by
    simp only [windowRows, List.map_cons]
    rw [windowRows_orderFree hf (pre ++ [x]) l]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 1
    exact congrArg (x ++ ·) (List.map_congr_left fun f hfm =>
      WinFn.value_orderFree (List.all_eq_true.mp hf f hfm) part pre l x)

/-- **Ties don't matter** when every window function is order-free: any
arrangement `s` of the input gives the same rows as `Rel.eval`'s stable sort. -/
theorem window_orderFree {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {rows : Relation} (hf : fns.all WinFn.orderFree = true) {s : List Row} (hp : s.Perm rows) :
    (windowRows part fns [] s).Perm (windowEval part sort fns rows) := by
  unfold windowEval
  have hp' : s.Perm (rows.mergeSort (sortLe sort)) := hp.trans (List.mergeSort_perm rows _).symm
  rw [windowRows_orderFree hf, windowRows_orderFree hf]
  simp only [List.nil_append]
  rw [List.map_congr_left fun x _ => congrArg (x ++ ·) (List.map_congr_left fun f hfm =>
    WinFn.wholeValue_perm (List.all_eq_true.mp hf f hfm) part hp' x)]
  exact hp'.map _

/-! ## Windows partitioned by every column

`ROW_NUMBER() OVER (PARTITION BY` every column`)` numbers the copies of each
row, as the SQL lift writes `INTERSECT ALL` and `EXCEPT ALL` (#344). Rows tied
in such a partition are equal, so a row's window values depend only on how
many of its copies come before and after it, and the copies of a row take the
same values in any arrangement (`window_allColumns`). Such a window needs no
key. -/

/-- Each row of `l` (which comes after `pre`), with how many rows equal to it
come before it (in `pre` too) and after it. -/
def occurrences : List Row → List Row → List (Row × Nat × Nat)
  | _, [] => []
  | pre, x :: l => (x, pre.count x, l.count x) :: occurrences (pre ++ [x]) l

theorem occurrences_congr {pre pre' : List Row} (h : pre.Perm pre') :
    ∀ l, occurrences pre l = occurrences pre' l
  | [] => rfl
  | x :: l => by
    simp only [occurrences, h.count_eq x, occurrences_congr (h.append_right [x]) l]

theorem occurrences_perm {l l' : List Row} (h : l.Perm l') :
    ∀ pre, (occurrences pre l).Perm (occurrences pre l') := by
  induction h with
  | nil => intro; exact .refl _
  | cons x _ ih =>
    intro pre
    simp only [occurrences, (‹List.Perm _ _›).count_eq x]
    exact (ih (pre ++ [x])).cons _
  | swap x y l =>
    intro pre
    simp only [occurrences]
    rw [occurrences_congr (pre := pre ++ [y] ++ [x]) (pre' := pre ++ [x] ++ [y])
      (by simpa using (List.Perm.swap x y []).append_left pre) l]
    by_cases hxy : x = y
    · subst hxy; exact .refl _
    · have h1 : (x == y) = false := by simpa using hxy
      have h2 : (y == x) = false := by simpa using Ne.symm hxy
      simp only [List.count_cons, List.count_append, h1, h2,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact .swap _ _ _
  | trans _ _ ih₁ ih₂ => intro pre; exact (ih₁ pre).trans (ih₂ pre)

/-- The row `x` with its window values, where the rows tied with it in its
partition are `b` copies before it and `a` after. -/
def copiesRow (fns : List WinFn) (x : Row) (b a : Nat) : Row :=
  x ++ fns.map (·.valueIn (List.replicate b x) x (List.replicate a x))

theorem windowRows_eq_occurrences {part : List Nat} {fns : List WinFn} {S : List Row}
    (hS : ∀ x ∈ S, ∀ y ∈ S, samePart part x y = true → x = y) :
    ∀ (pre l : List Row), (∀ x ∈ pre ++ l, x ∈ S) →
      windowRows part fns pre l = (occurrences pre l).map fun o => copiesRow fns o.1 o.2.1 o.2.2
  | _, [], _ => rfl
  | pre, x :: l, hin => by
    simp only [windowRows, occurrences, List.map_cons, List.cons.injEq]
    refine ⟨?_, windowRows_eq_occurrences hS (pre ++ [x]) l fun y hy => hin y (by simpa using hy)⟩
    have hx : x ∈ S := hin x (by simp)
    have hf : ∀ m : List Row, (∀ y ∈ m, y ∈ S) →
        m.filter (samePart part x) = List.replicate (m.count x) x := by
      intro m hm
      rw [← List.filter_beq]
      apply List.filter_congr
      intro y hy
      by_cases h : samePart part x y = true
      · obtain rfl := hS x hx y (hm y hy) h
        simp [h]
      · have hne : (y == x) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact h (samePart_refl part y)
        simp [h, hne]
    simp only [copiesRow, WinFn.value, hf pre fun y hy => hin y (by simp [hy]),
      hf l fun y hy => hin y (by simp [hy])]

/-- **Windows partitioned by every column** do not depend on how ties are
broken: rows tied in such a partition are equal, so any arrangement `s` of
the input gives the rows `Rel.eval`'s stable sort gives, as a bag. -/
theorem window_allColumns {part : List Nat} {sort : List SortKey} {fns : List WinFn}
    {rows : Relation} {w : Nat} (hlen : ∀ x ∈ rows, x.length = w) (hpart : ∀ i < w, i ∈ part)
    {s : List Row} (hp : s.Perm rows) :
    (windowRows part fns [] s).Perm (windowEval part sort fns rows) := by
  have hS : ∀ x ∈ rows, ∀ y ∈ rows, samePart part x y = true → x = y := by
    intro x hx y hy h
    simp only [samePart, decide_eq_true_eq, List.map_inj_left] at h
    apply List.ext_getElem ((hlen x hx).trans (hlen y hy).symm)
    intro i h1 h2
    have := h i (hpart i (by rw [← hlen x hx]; exact h1))
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] using this
  have hm := List.mergeSort_perm rows (sortLe sort)
  unfold windowEval
  rw [windowRows_eq_occurrences hS [] s fun x hx => hp.subset (by simpa using hx),
    windowRows_eq_occurrences hS [] _ fun x hx => hm.subset (by simpa using hx)]
  exact (occurrences_perm (hp.trans hm.symm) []).map _

/-- Is every window deterministic: do its partition and sort columns contain
a derived key of its input (`Rel.window_deterministic`), or are its functions
order-free (`window_orderFree`), or does its partition cover every column
(`Rel.window_allColumns`)? -/
def Rel.windowsTotal (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.windowsTotal cat A F K
  -- `FIRST`/`LAST` (#55) pick a row by their order, and `STRING_AGG` joins the
  -- rows in it: unless the group's and the order's columns contain a key, ties
  -- make the result the engine's.
  | .aggregate r gs ms => r.windowsTotal cat A F K && ms.all fun m =>
      !(m.fn matches .pick _ || m.fn matches .concat _) || (r.keys cat A F K).any fun k =>
        k.all fun c => gs.contains (.field c) || m.sort.any (·.col == c)
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
      a.windowsTotal cat A F K && b.windowsTotal cat A F K
  | .window r part sort fns =>
      r.windowsTotal cat A F K && ((r.keys cat A F K).any (fun k => k.all (· ∈ part ++ sort.map (·.col))) ||
        fns.all WinFn.orderFree || (List.range (r.arity cat)).all (· ∈ part))

/-- The check at one window: then the engine's tie-breaking is irrelevant. -/
theorem Rel.window_deterministic {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {r : Rel} {part : List Nat}
    {sort : List SortKey} {fns : List WinFn} (hwf : r.WF cat)
    (h : (r.keys cat A F K).any (fun k => k.all (· ∈ part ++ sort.map (·.col))) = true)
    {s : List Row} (hp : s.Perm (r.eval cat)) (hs : s.Pairwise (sortLe sort · · = true)) :
    (windowRows part fns [] s).Perm ((Rel.window r part sort fns).eval cat) := by
  obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp h
  simp only [List.all_eq_true, decide_eq_true_eq] at hsub
  exact window_tiebreak ((keys_sound hcat hA hF hK hwf k hk).superset hsub) hp hs

/-- The check at one window whose partition covers every column: then too the
engine's tie-breaking is irrelevant. -/
theorem Rel.window_allColumns {cat : Catalog} (hcat : cat.WF) {r : Rel} {part : List Nat}
    {sort : List SortKey} {fns : List WinFn} (hwf : r.WF cat)
    (h : (List.range (r.arity cat)).all (· ∈ part) = true)
    {s : List Row} (hp : s.Perm (r.eval cat)) :
    (windowRows part fns [] s).Perm ((Rel.window r part sort fns).eval cat) := by
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact Substrait.window_allColumns (Rel.eval_arity hcat hwf) h hp

end Substrait

namespace Substrait

/-- The window-key oracle for strict window facts, from derived keys. -/
def Rel.keyedWindows (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : WindowKeys := fun r part sort =>
  (r.keys cat A F K).any fun k => k.all (· ∈ part ++ sort.map (·.col))

theorem Rel.keyedWindows_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) : (Rel.keyedWindows cat A F K).Sound cat := by
  intro r part sort h hwf
  obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp h
  simp only [List.all_eq_true, decide_eq_true_eq] at hsub
  exact (keys_sound hcat hA hF hK hwf k hk).superset hsub

end Substrait
