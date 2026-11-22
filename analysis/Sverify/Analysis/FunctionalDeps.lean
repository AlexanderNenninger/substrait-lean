import Sverify.Analysis.Contracts

/-!
# Functional dependencies (#1992, #1993; rulings 194 and 196)

A **functional dependency** `X → Y` of a relation: any two of its rows that
agree on the columns `X` agree on `Y`, both up to `canonV`, as keys are read
(`keyOf`, D31). A key `k` gives `k → every column`, and a key that an operator
loses can survive as a dependency: after `customers LEFT JOIN orders`,
`customer_id` is no key, yet it still gives `name`, since the left part of
every output row is a `customers` row. A later key makes the lost one a key
again (`KeyOn.of_fd`): grouping by `customer_id, name` has the key
`[customer_id, name]`, and `customer_id → name` makes `[customer_id]` one.

* `FDOn X Y rows` is stated over membership, so a join that repeats a left row
  keeps it (ruling 194, F1). A dependency in a list is a pair `(X, c)`, read
  `FDOn X [c]` (`FDsOn`).
* `FDOn.transfer` carries a dependency to an operator's output where each
  output row has an input row that agrees with it (F2); `FDsOn.append_left`,
  `FDsOn.append_right`, `FDsOn.agg` and `FDOn.of_subset` are its instances.
* `fdClosure` is the columns a list of dependencies derives from `X`
  (`fdClosure_sound`), and `closeKeys` adds the left sides whose closure covers
  a key (`closeKeys_sound`, ruling 196 P2).
* `Rel.fdsNode` is one node's dependencies from its inputs' arities, keys and
  dependencies: what `Rel.fds` (`analysis/Sverify/Analysis/Keys.lean`) and the
  one-pass `Rel.laneK` both compute.
-/

namespace Substrait

/-- Any two rows of `rows` that agree on the columns `X` agree on `Y`, up to
`canonV` (`keyOf`). -/
def FDOn (X Y : List Nat) (rows : Relation) : Prop :=
  ∀ r ∈ rows, ∀ s ∈ rows, keyOf X r = keyOf X s → keyOf Y r = keyOf Y s

theorem keyOf_eq_iff {k : List Nat} {r s : Row} :
    keyOf k r = keyOf k s ↔ ∀ c ∈ k, (r.getD c .null).canonV = (s.getD c .null).canonV := by
  simp only [keyOf, List.map_inj_left]

theorem keyOf_eq_of_subset {k k' : List Nat} {r s : Row} (h : keyOf k r = keyOf k s)
    (hs : ∀ c ∈ k', c ∈ k) : keyOf k' r = keyOf k' s :=
  keyOf_eq_iff.mpr fun c hc => keyOf_eq_iff.mp h c (hs c hc)

theorem keyOf_singleton {c : Nat} {r s : Row} :
    keyOf [c] r = keyOf [c] s ↔ (r.getD c .null).canonV = (s.getD c .null).canonV := by
  simp [keyOf_eq_iff]

/-! ## Armstrong's rules -/

/-- More columns on the left, fewer on the right. -/
theorem FDOn.mono {X Y X' Y' : List Nat} {rows : Relation} (h : FDOn X Y rows)
    (hX : ∀ c ∈ X, c ∈ X') (hY : ∀ c ∈ Y', c ∈ Y) : FDOn X' Y' rows :=
  fun r hr s hs he => keyOf_eq_of_subset (h r hr s hs (keyOf_eq_of_subset he hX)) hY

theorem FDOn.trans {X Y Z : List Nat} {rows : Relation} (h₁ : FDOn X Y rows)
    (h₂ : FDOn Y Z rows) : FDOn X Z rows :=
  fun r hr s hs he => h₂ r hr s hs (h₁ r hr s hs he)

theorem FDOn.union {X Y Z : List Nat} {rows : Relation} (h₁ : FDOn X Y rows)
    (h₂ : FDOn X Z rows) : FDOn X (Y ++ Z) rows := by
  intro r hr s hs he
  refine keyOf_eq_iff.mpr fun c hc => ?_
  rcases List.mem_append.mp hc with hc | hc
  · exact keyOf_eq_iff.mp (h₁ r hr s hs he) c hc
  · exact keyOf_eq_iff.mp (h₂ r hr s hs he) c hc

/-- **The transfer lemma** (ruling 194, F2): where each output row has an input
row that agrees with it, `X'` against `X` and `Y'` against `Y`, a dependency
`X → Y` of the input gives `X' → Y'` of the output. -/
theorem FDOn.transfer {X Y X' Y' : List Nat} {rows out : Relation}
    (h : ∀ o ∈ out, ∃ r ∈ rows, keyOf X' o = keyOf X r ∧ keyOf Y' o = keyOf Y r)
    (hd : FDOn X Y rows) : FDOn X' Y' out := by
  intro o₁ h₁ o₂ h₂ he
  obtain ⟨r₁, hr₁, hx₁, hy₁⟩ := h o₁ h₁
  obtain ⟨r₂, hr₂, hx₂, hy₂⟩ := h o₂ h₂
  rw [hy₁, hy₂]
  exact hd r₁ hr₁ r₂ hr₂ (by rw [← hx₁, ← hx₂, he])

/-- Fewer rows keep every dependency: filters, fetches, semi joins, sorts. -/
theorem FDOn.of_subset {X Y : List Nat} {rows out : Relation} (h : ∀ o ∈ out, o ∈ rows)
    (hd : FDOn X Y rows) : FDOn X Y out :=
  FDOn.transfer (fun o ho => ⟨o, h o ho, rfl, rfl⟩) hd

/-! ## Keys and dependencies -/

/-- Two rows of a keyed relation that agree on the key are the same row. -/
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

/-- A key determines every column. -/
theorem FDOn.of_key {k : List Nat} (Y : List Nat) {rows : Relation} (h : KeyOn k rows) :
    FDOn k Y rows :=
  fun _ hx _ hy he => by rw [KeyOn.eq_of_keyOf h hx hy he]

/-- **A dependency onto a key makes a key** (ruling 194, D1): rows equal on `X`
are equal on `Y`, so on the key `k ⊆ X ∪ Y`, so they are one row. -/
theorem KeyOn.of_fd {k X Y : List Nat} {rows : Relation} (hk : KeyOn k rows)
    (hd : FDOn X Y rows) (hc : ∀ c ∈ k, c ∈ X ∨ c ∈ Y) : KeyOn X rows := by
  unfold KeyOn at hk ⊢
  refine hk.imp_of_mem fun {r s} hr hs hne he => hne ?_
  have hy := hd r hr s hs he
  refine keyOf_eq_iff.mpr fun c hc' => ?_
  rcases hc c hc' with h | h
  · exact keyOf_eq_iff.mp he c h
  · exact keyOf_eq_iff.mp hy c h

/-- Columns that agree on every pair of rows determine each other. -/
theorem FDOn.of_eq {i j : Nat} {rows : Relation}
    (h : ∀ x ∈ rows, ∀ y ∈ rows, (x.getD i .null).canonV = (y.getD i .null).canonV →
      (x.getD j .null).canonV = (y.getD j .null).canonV) :
    FDOn [i] [j] rows :=
  fun x hx y hy he => keyOf_singleton.mpr (h x hx y hy (keyOf_singleton.mp he))

/-! ## Lists of dependencies

A dependency in a list is `(X, c)`: `X → c`. -/

/-- Every dependency of `fds` holds on `rows`. -/
def FDsOn (fds : List (List Nat × Nat)) (rows : Relation) : Prop :=
  ∀ fd ∈ fds, FDOn fd.1 [fd.2] rows

theorem FDsOn.nil {rows : Relation} : FDsOn [] rows := fun _ h => nomatch h

theorem FDsOn.append {f g : List (List Nat × Nat)} {rows : Relation} (hf : FDsOn f rows)
    (hg : FDsOn g rows) : FDsOn (f ++ g) rows := fun fd h => by
  rcases List.mem_append.mp h with h | h
  · exact hf fd h
  · exact hg fd h

theorem FDsOn.of_subset {f : List (List Nat × Nat)} {rows out : Relation}
    (h : ∀ o ∈ out, o ∈ rows) (hd : FDsOn f rows) : FDsOn f out :=
  fun fd hfd => (hd fd hfd).of_subset h

/-- A key determines every column. -/
def keyFds (ks : List (List Nat)) (n : Nat) : List (List Nat × Nat) :=
  ks.flatMap fun k => (List.range n).map (k, ·)

theorem keyFds_sound {ks : List (List Nat)} {n : Nat} {rows : Relation}
    (h : ∀ k ∈ ks, KeyOn k rows) : FDsOn (keyFds ks n) rows := by
  intro fd hfd
  simp only [keyFds, List.mem_flatMap, List.mem_map] at hfd
  obtain ⟨k, hk, c, _, rfl⟩ := hfd
  exact FDOn.of_key _ (h k hk)

/-- Column pairs `(i, j)` such that, on rows where `e` is TRUE, `i` determines
`j` and `j` determines `i` (`$i + c₁ = $j + c₂`). -/
def Expr.eqCols : Expr → List (Nat × Nat)
  | .bin .and p q => p.eqCols ++ q.eqCols
  | .bin .eq t₁ t₂ =>
      match t₁.linTerm, t₂.linTerm with
      | some (i, _), some (j, _) => [(i, j)]
      | _, _ => []
  | _ => []

/-- Columns a condition equates determine each other. -/
def eqFds (ps : List (Nat × Nat)) : List (List Nat × Nat) :=
  ps.flatMap fun p => [([p.1], p.2), ([p.2], p.1)]

def inRange (n : Nat) (fd : List Nat × Nat) : Bool := fd.1.all (· < n) && decide (fd.2 < n)

def shiftFd (n : Nat) (fd : List Nat × Nat) : List Nat × Nat := (fd.1.map (n + ·), n + fd.2)

/-- A position of column `x` in an emit. -/
def emitPos? (m : List Nat) (x : Nat) : Option Nat := (List.range m.length).find? (m[·]? == some x)

/-- A dependency through an emit, for every position of its column. -/
def emitFd (m : List Nat) (fd : List Nat × Nat) : List (List Nat × Nat) :=
  if fd.1.all fun x => (emitPos? m x).isSome then
    ((List.range m.length).filter (m[·]? == some fd.2)).map
      fun p => (fd.1.map fun x => (emitPos? m x).getD 0, p)
  else []

/-- A projected column `$j` and its copy determine each other. -/
def copyFds (n : Nat) (es : List Expr) : List (List Nat × Nat) :=
  es.zipIdx.flatMap fun (e, q) => match e with
    | .field j => if j < n then [([j], n + q), ([n + q], j)] else []
    | _ => []

/-- The position of the grouping column `$c`. -/
def gpos (gs : List Expr) (c : Nat) : Option Nat :=
  (List.range gs.length).find? fun q => gs[q]? == some (.field c)

/-- An input dependency among the plain column references `$c` of `gs`, at
their positions in `gs`: an aggregate's grouping columns, or the columns a
projection appends. -/
def aggFds (gs : List Expr) (fds : List (List Nat × Nat)) : List (List Nat × Nat) :=
  fds.filterMap fun fd => do
    let X ← fd.1.mapM (gpos gs)
    let c ← gpos gs fd.2
    some (X, c)

/-- An input's dependencies with those its keys give, `n` its arity: what
an operator above it can keep where its keys stop being keys. -/
def inputFds (n : Nat) (ks : List (List Nat)) (fds : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  fds ++ keyFds ks n

/-- Without the trivial ones (`c ∈ X`), deduplicated (ruling 194, F5). -/
def normFds (fds : List (List Nat × Nat)) : List (List Nat × Nat) :=
  (fds.filter fun fd => !fd.1.contains fd.2).eraseDups

theorem normFds_sound {fds : List (List Nat × Nat)} {rows : Relation} (h : FDsOn fds rows) :
    FDsOn (normFds fds) rows := fun fd hfd =>
  h fd (List.mem_filter.mp (List.mem_eraseDups.mp hfd)).1

/-- The columns that `X` determines, at most `fuel` rounds deep; it stops at a
fixed point. -/
def fdClosure (fds : List (List Nat × Nat)) : Nat → List Nat → List Nat
  | 0, X => X
  | fuel + 1, X =>
    let new := (fds.filter fun fd => fd.1.all (X.contains ·) && !X.contains fd.2).map (·.2)
    if new.isEmpty then X else fdClosure fds fuel (X ++ new.eraseDups)

theorem fdClosure_sound {fds : List (List Nat × Nat)} {rows : Relation}
    (h : FDsOn fds rows) {x y : Row} (hx : x ∈ rows) (hy : y ∈ rows) :
    ∀ (fuel : Nat) (X : List Nat), (∀ i ∈ X, (x.getD i .null).canonV = (y.getD i .null).canonV) →
      ∀ i ∈ fdClosure fds fuel X, (x.getD i .null).canonV = (y.getD i .null).canonV
  | 0, _, hX => hX
  | fuel + 1, X, hX => by
    simp only [fdClosure]
    split
    · exact hX
    · refine fdClosure_sound h hx hy fuel _ fun i hi => ?_
      rcases List.mem_append.mp hi with hi | hi
      · exact hX i hi
      · simp only [List.mem_eraseDups, List.mem_map, List.mem_filter, Bool.and_eq_true,
          List.all_eq_true, List.contains_iff_mem] at hi
        obtain ⟨fd, ⟨hfd, hsub, _⟩, rfl⟩ := hi
        exact keyOf_singleton.mp (h fd hfd x hx y hy (keyOf_eq_iff.mpr fun c hc => hX c (hsub c hc)))

/-- The keys with the left sides of the dependencies whose closure covers a
key, and no key already a subset of them (ruling 196, P2). -/
def closeKeys (ks : List (List Nat)) (fds : List (List Nat × Nat)) : List (List Nat) :=
  ks ++ ((fds.map (·.1)).eraseDups.filter fun X =>
    !ks.any (fun k => k.all X.contains) &&
      ks.any fun k => k.all (fdClosure fds (fds.length + 1) X).contains)

theorem closeKeys_sound {ks : List (List Nat)} {fds : List (List Nat × Nat)} {rows : Relation}
    (hk : ∀ k ∈ ks, KeyOn k rows) (hd : FDsOn fds rows) :
    ∀ k ∈ closeKeys ks fds, KeyOn k rows := by
  intro X hX
  rcases List.mem_append.mp hX with h | h
  · exact hk X h
  · simp only [List.mem_filter, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
      List.contains_iff_mem] at h
    obtain ⟨-, -, k, hk₀, hcov⟩ := h
    have := hk k hk₀
    unfold KeyOn at this ⊢
    refine this.imp_of_mem fun {r s} hr hs hne he => hne ?_
    exact keyOf_eq_iff.mpr fun c hc =>
      fdClosure_sound hd hr hs _ X (keyOf_eq_iff.mp he) c (hcov c hc)

/-! ## Through the operators -/

/-- Output rows that each begin with an input row of `n` columns keep its
dependencies within those columns: both joins' left sides, cross products,
windows. -/
theorem FDsOn.append_left {fds : List (List Nat × Nat)} {n : Nat} {rows out : Relation}
    (h : ∀ o ∈ out, ∃ x ∈ rows, ∃ y, o = x ++ y ∧ x.length = n) (hd : FDsOn fds rows) :
    FDsOn (fds.filter (inRange n)) out := by
  intro fd hfd
  obtain ⟨hfd, hr⟩ := List.mem_filter.mp hfd
  simp only [inRange, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
  refine FDOn.transfer (fun o ho => ?_) (hd fd hfd)
  obtain ⟨x, hx, y, rfl, hn⟩ := h o ho
  refine ⟨x, hx, keyOf_eq_iff.mpr fun c hc => ?_, keyOf_eq_iff.mpr fun c hc => ?_⟩
  · rw [getD_append_left' (hn ▸ hr.1 c hc)]
  · simp only [List.mem_singleton] at hc; subst hc
    rw [getD_append_left' (hn ▸ hr.2)]

/-- Output rows that each end with an input row, after `n` columns, keep its
dependencies, shifted by `n`: a cross product's or an inner join's right side. -/
theorem FDsOn.append_right {fds : List (List Nat × Nat)} {n : Nat} {rows out : Relation}
    (h : ∀ o ∈ out, ∃ x, ∃ y ∈ rows, o = x ++ y ∧ x.length = n) (hd : FDsOn fds rows) :
    FDsOn (fds.map (shiftFd n)) out := by
  intro fd hfd
  obtain ⟨fd₀, hfd₀, rfl⟩ := List.mem_map.mp hfd
  refine FDOn.transfer (fun o ho => ?_) (hd fd₀ hfd₀)
  obtain ⟨x, y, hy, rfl, rfl⟩ := h o ho
  refine ⟨y, hy, ?_, ?_⟩ <;>
  · simp only [shiftFd, keyOf, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      getD_append_right']

theorem emitPos?_spec {m : List Nat} {x p : Nat} (h : emitPos? m x = some p) : m[p]? = some x := by
  have := List.find?_some h
  simpa using this

theorem getD_emit {m : List Nat} {y : Row} {p x : Nat} (h : m[p]? = some x) :
    (m.map (y.getD · .null)).getD p .null = y.getD x .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

/-- An emit carries a dependency where all of its left side survives. -/
theorem FDsOn.emit {fds : List (List Nat × Nat)} {m : List Nat} {rows : Relation}
    (hd : FDsOn fds rows) : FDsOn (fds.flatMap (emitFd m))
      (rows.map fun y => m.map (y.getD · .null)) := by
  intro fd hfd
  obtain ⟨fd₀, h₀, hfd⟩ := List.mem_flatMap.mp hfd
  have ih := hd fd₀ h₀
  unfold emitFd at hfd
  split at hfd
  · rename_i hall
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfd
    have hp' : m[p]? = some fd₀.2 := by simpa using (List.mem_filter.mp hp).2
    have hk : ∀ y : Row, keyOf (fd₀.1.map fun x => (emitPos? m x).getD 0)
        (m.map (y.getD · .null)) = keyOf fd₀.1 y := fun y => by
      simp only [keyOf, List.map_map]
      refine List.map_congr_left fun x hx => ?_
      have := List.all_eq_true.mp hall x hx
      obtain ⟨p', hp''⟩ := Option.isSome_iff_exists.mp this
      simp only [Function.comp_apply, hp'', Option.getD_some]
      rw [getD_emit (emitPos?_spec hp'')]
    intro o ho o' ho' he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp ho'
    rw [hk, hk] at he
    refine keyOf_singleton.mpr ?_
    rw [getD_emit hp', getD_emit hp']
    exact keyOf_singleton.mp (ih y hy y' hy' he)
  · simp at hfd

theorem gpos_spec {gs : List Expr} {c q : Nat} (h : gpos gs c = some q) : gs[q]? = some (.field c) := by
  simpa using List.find?_some h

theorem mapM_some_mem {f : Nat → Option Nat} :
    ∀ {l l' : List Nat}, l.mapM f = some l' → ∀ c ∈ l, ∃ p ∈ l', f c = some p
  | [], _, _, c, hc => nomatch hc
  | a :: l, l', h, c, hc => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨p, hp, l'', hl'', rfl⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨p, List.mem_cons_self .., hp⟩
    · obtain ⟨q, hq, hfq⟩ := mapM_some_mem hl'' c hc
      exact ⟨q, List.mem_cons_of_mem _ hq, hfq⟩

/-- An aggregate's dependencies among its plain grouping columns: where each
output row agrees with an input row on every grouped column, at the group
position, up to `canonV`. -/
theorem FDsOn.agg {gs : List Expr} {fds : List (List Nat × Nat)} {rows out : Relation}
    (h : ∀ o ∈ out, ∃ x ∈ rows, ∀ {c q : Nat}, gs[q]? = some (.field c) →
      (o.getD q .null).canonV = (x.getD c .null).canonV)
    (hd : FDsOn fds rows) : FDsOn (aggFds gs fds) out := by
  intro fd hfd
  simp only [aggFds, List.mem_filterMap, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hfd
  obtain ⟨fd₀, h₀, X, hX, c, hc, rfl⟩ := hfd
  intro o₁ h₁ o₂ h₂ he
  obtain ⟨r₁, hr₁, hs₁⟩ := h o₁ h₁
  obtain ⟨r₂, hr₂, hs₂⟩ := h o₂ h₂
  have hx : keyOf fd₀.1 r₁ = keyOf fd₀.1 r₂ := keyOf_eq_iff.mpr fun c' hc' => by
    obtain ⟨p, hp, hfp⟩ := mapM_some_mem hX c' hc'
    have := keyOf_eq_iff.mp he p hp
    rwa [hs₁ (gpos_spec hfp), hs₂ (gpos_spec hfp)] at this
  refine keyOf_singleton.mpr ?_
  rw [hs₁ (gpos_spec hc), hs₂ (gpos_spec hc)]
  exact keyOf_singleton.mp (hd fd₀ h₀ r₁ hr₁ r₂ hr₂ hx)

/-- Where an equality condition holds on every row, the columns it equates
determine each other. `Expr.eqCols_det`, in `Keys.lean`, gives the premise. -/
theorem eqFds_sound_of {ps : List (Nat × Nat)} {rows : Relation}
    (h : ∀ x ∈ rows, ∀ y ∈ rows, ∀ p ∈ ps,
      ((x.getD p.1 .null).canonV = (y.getD p.1 .null).canonV →
        (x.getD p.2 .null).canonV = (y.getD p.2 .null).canonV) ∧
      ((x.getD p.2 .null).canonV = (y.getD p.2 .null).canonV →
        (x.getD p.1 .null).canonV = (y.getD p.1 .null).canonV)) :
    FDsOn (eqFds ps) rows := by
  intro fd hfd
  simp only [eqFds, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hfd
  obtain ⟨p, hp, rfl | rfl⟩ := hfd
  · exact FDOn.of_eq fun x hx y hy => (h x hx y hy p hp).1
  · exact FDOn.of_eq fun x hx y hy => (h x hx y hy p hp).2

variable [Boxes.Ambient]

/-- A projection's copies: a copied column `$j` and its copy agree on every row. -/
theorem copyFds_sound {n : Nat} {es : List Expr} {rows : Relation}
    (hn : ∀ x ∈ rows, x.length = n) :
    FDsOn (copyFds n es) (rows.map fun y => y ++ es.map (·.eval y)) := by
  intro fd h
  simp only [copyFds, List.mem_flatMap] at h
  obtain ⟨⟨e, q⟩, hq, h⟩ := h
  have heq := List.mem_zipIdx_iff_getElem?.mp hq
  cases e with
  | field j =>
    simp only at h
    split at h
    · rename_i hj
      have hc : ∀ row ∈ rows.map fun y => y ++ es.map (·.eval y),
          row.getD (n + q) .null = row.getD j .null := fun row hrow => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrow
        have hl := hn y hy
        rw [← hl, getD_append_right', getD_append_left' (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, heq, Expr.eval]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact FDOn.of_eq fun x hx y hy he => by rw [hc x hx, hc y hy]; exact he
      · exact FDOn.of_eq fun x hx y hy he => by rw [← hc x hx, ← hc y hy]; exact he
    · simp at h
  | _ => simp at h

/-- A projection's appended copies keep the input's dependencies among the
columns they copy, shifted past the input's `n` columns: an emit that keeps the
copies and drops the originals keeps them (#1992). -/
theorem copiedFds_sound {n : Nat} {es : List Expr} {fds : List (List Nat × Nat)}
    {rows : Relation} (hn : ∀ x ∈ rows, x.length = n) (hd : FDsOn fds rows) :
    FDsOn ((aggFds es fds).map (shiftFd n)) (rows.map fun y => y ++ es.map (·.eval y)) := by
  refine FDsOn.append_right (rows := rows.map fun y => es.map (·.eval y))
    (fun o ho => ?_) (FDsOn.agg (fun o ho => ?_) hd)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
    exact ⟨y, _, List.mem_map_of_mem hy, rfl, hn y hy⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
    refine ⟨y, hy, fun {c q} hq => ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hq, Expr.eval]

/-! ## One node's dependencies -/

/-- One node's dependencies from its inputs' arities (`na`, `nb`; at a read, the
table's), keys (`ka`, `kb`; at a read, the table's) and dependencies (`fa`, `fb`). Read keys give their dependencies, and at
the inputs of cross products, joins and aggregates the inputs' keys are made
dependencies, since a key can stop being one there while its dependency
survives (ruling 194, F5). Equalities of filters and inner joins give theirs;
a left join keeps the left side's only, since a padded row breaks the right
side's. -/
def Rel.fdsNode :
    Rel → Nat → Nat → List (List Nat) → List (List Nat) →
      List (List Nat × Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | .read _, na, _, ka, _, _, _ => keyFds ka na
  | .aggregate _ gs ms, na, _, ka, _, fa, _ =>
      keyFds [List.range gs.length] (gs.length + ms.length) ++
        (if gs.isEmpty then [] else normFds (aggFds gs (inputFds na ka fa)))
  | .filter _ c, _, _, _, _, fa, _ => fa ++ eqFds c.eqCols
  | .fetch .., _, _, _, _, fa, _ | .orderBy .., _, _, _, _, fa, _
  | .distinct _, _, _, _, _, fa, _ | .semi .., _, _, _, _, fa, _ => fa
  | .project _ es, na, _, _, _, fa, _ =>
      fa.filter (inRange na) ++ copyFds na es ++ (aggFds es fa).map (shiftFd na)
  | .window .., na, _, _, _, fa, _ => fa.filter (inRange na)
  | .emit _ m, _, _, _, _, fa, _ => fa.flatMap (emitFd m)
  | .cross .., na, nb, ka, kb, fa, fb =>
      normFds ((inputFds na ka fa).filter (inRange na) ++ (inputFds nb kb fb).map (shiftFd na))
  | .join _ _ .inner on, na, nb, ka, kb, fa, fb =>
      normFds ((inputFds na ka fa).filter (inRange na) ++ (inputFds nb kb fb).map (shiftFd na) ++
        eqFds on.eqCols)
  | .join _ _ .left _, na, _, ka, _, fa, _ => normFds ((inputFds na ka fa).filter (inRange na))
  | .values .., _, _, _, _, _, _ | .unionAll .., _, _, _, _, _, _ | .unnest .., _, _, _, _, _, _ => []

end Substrait
