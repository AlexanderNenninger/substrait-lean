import SubstraitLean.Keys
import SubstraitLean.Weighted

/-!
# Composing contracts

`sverify` proves each decorated transformation on its own, from its
preconditions (`contract_sound`, `Rel.keys_sound`). When the output of `g`
feeds an input `x` of `f`, the contracts compose by **assume-guarantee**
reasoning: `f`'s precondition on `x` becomes a proof obligation on `g`
(proved as extra postconditions of `g`, from `g`'s preconditions), and `f` is
proved assuming only what `g` guarantees.

The results are stated for *queries* in general (anything that turns a
catalog into a table) and on top of `contract_sound` and `Rel.keys_sound`,
so they need no induction over plans:

* `Triple.compose`: `{P} g {Q}` and `{Q} f {S}` give `{P} f ∘ g {S}`.
* `Triple.of_contract`, `Triple.of_keys`, `Triple.of_aeval`: what the
  checker proves (postconditions, keys, column facts) as triples.
-/

namespace Substrait

/-- A query, semantically: when it is well-formed on a catalog, the table it
produces, whose rows have the table's arity. -/
structure Query where
  WF : Catalog → Prop
  out : Catalog → Table
  out_wf : ∀ cat, cat.WF → WF cat → ∀ row ∈ (out cat).rows, row.length = (out cat).arity

def Rel.query (r : Rel) : Query where
  WF := r.WF
  out cat := ⟨r.arity cat, r.eval cat⟩
  out_wf _ hcat hwf row h := Rel.eval_arity hcat hwf row h

/-- `cat` with table `x` replaced by `tb`. -/
def Catalog.bind (cat : Catalog) (x : String) (tb : Table) : Catalog :=
  fun t => if t = x then tb else cat t

theorem Catalog.bind_wf {cat : Catalog} {x : String} {tb : Table} (hcat : cat.WF)
    (htb : ∀ row ∈ tb.rows, row.length = tb.arity) : (cat.bind x tb).WF := by
  intro t
  unfold Catalog.bind
  split
  · exact htb
  · exact hcat t

/-- `f ∘ g`: `f` reading the output of `g` as its table `x`. (Inlining `g`'s
plan into `f`'s at its `read x` has the same result; `sverify` does this when
it runs the composed Ibis expression.) -/
def Query.after (f : Query) (x : String) (g : Query) : Query where
  WF cat := g.WF cat ∧ f.WF (cat.bind x (g.out cat))
  out cat := f.out (cat.bind x (g.out cat))
  out_wf cat hcat h := f.out_wf _ (Catalog.bind_wf hcat (g.out_wf cat hcat h.1)) h.2

/-! ## Hoare triples -/

/-- Every table `t` of the catalog satisfies `A t`. -/
def Sat (A : String → Relation → Prop) (cat : Catalog) : Prop := ∀ t, A t (cat t).rows

/-- `{A} q {B}`: on every well-formed catalog whose tables satisfy `A`, the
output of `q` satisfies `B`. -/
def Triple (A : String → Relation → Prop) (q : Query) (B : Relation → Prop) : Prop :=
  ∀ cat, cat.WF → Sat A cat → q.WF cat → B (q.out cat).rows

theorem Triple.mono {A : String → Relation → Prop} {q : Query} {B B' : Relation → Prop}
    (h : Triple A q B) (hB : ∀ rows, B rows → B' rows) : Triple A q B' :=
  fun cat hcat hA hwf => hB _ (h cat hcat hA hwf)

theorem Triple.and {A : String → Relation → Prop} {q : Query} {B B' : Relation → Prop}
    (h : Triple A q B) (h' : Triple A q B') : Triple A q fun rows => B rows ∧ B' rows :=
  fun cat hcat hA hwf => ⟨h cat hcat hA hwf, h' cat hcat hA hwf⟩

/-- **Composition (assume-guarantee).** If `g` guarantees, under `A`, what
`f` assumes about its input `x` (`A' x`), and `A` implies what `f` assumes
about its other inputs, then `f ∘ g` satisfies `f`'s postcondition under `A`:
`{P} g {Q}`, `{Q} f {S}` ⊢ `{P} f ∘ g {S}`. -/
theorem Triple.compose {A A' : String → Relation → Prop} {f g : Query} {x : String}
    {B : Relation → Prop} (hg : Triple A g (A' x)) (hf : Triple A' f B)
    (hA : ∀ t, t ≠ x → ∀ rows, A t rows → A' t rows) : Triple A (f.after x g) B := by
  intro cat hcat hsat ⟨hgwf, hfwf⟩
  refine hf _ (Catalog.bind_wf hcat (g.out_wf cat hcat hgwf)) ?_ hfwf
  intro t
  by_cases ht : t = x
  · subst ht
    simp only [Catalog.bind]
    exact hg cat hcat hsat hgwf
  · simp only [Catalog.bind, ht]
    exact hA t ht _ (hsat t)

/-! ## Contracts as triples -/

/-- Every row satisfies every condition (is TRUE, not FALSE or NULL). -/
def RowsSat (es : List Expr) (rows : Relation) : Prop :=
  ∀ row ∈ rows, ∀ e ∈ es, (e.eval row).isTrue = true

/-- What the checker assumes about table `t`: its rows match the schema
`S t` and satisfy the preconditions `pre t`, and the columns of every
`k ∈ K t` are a key. -/
def Spec (S : String → List AVal) (pre : String → List Expr) (K : String → List (List Nat))
    (t : String) (rows : Relation) : Prop :=
  (∀ row ∈ rows, EnvMem (S t) row) ∧ RowsSat (pre t) rows ∧ ∀ k ∈ K t, KeyOn k rows

theorem Spec.intro {A : String → Relation → Prop} {q : Query} {S : String → List AVal}
    {pre : String → List Expr} {K : String → List (List Nat)} {x : String}
    (hS : Triple A q fun rows => ∀ row ∈ rows, EnvMem (S x) row) (hpre : Triple A q (RowsSat (pre x)))
    (hK : Triple A q fun rows => ∀ k ∈ K x, KeyOn k rows) : Triple A q (Spec S pre K x) :=
  fun cat hcat hA hwf => ⟨hS cat hcat hA hwf, hpre cat hcat hA hwf, hK cat hcat hA hwf⟩

/-- The abstract environment and facts the checker starts from. -/
def Spec.env (S : String → List AVal) (pre : String → List Expr) (t : String) : List AVal :=
  tableEnv (S t) (pre t)

def Spec.facts (pre : String → List Expr) (t : String) : List Fact :=
  (pre t).flatMap Expr.factsOf

theorem Spec.env_sound {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {cat : Catalog} (h : Sat (Spec S pre K) cat) :
    ∀ t, ∀ row ∈ (cat t).rows, EnvMem (Spec.env S pre t) row :=
  fun t row hr => tableEnv_sound ((h t).1 row hr) ((h t).2.1 row hr)

theorem Spec.facts_sound {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {cat : Catalog} (h : Sat (Spec S pre K) cat) :
    ∀ t, ∀ row ∈ (cat t).rows, FactsHold (Spec.facts pre t) row := by
  intro t row hr f hf
  simp only [Spec.facts, List.mem_flatMap] at hf
  obtain ⟨e, he, hf⟩ := hf
  exact Expr.factsOf_sound e ((h t).2.1 row hr e he) f hf

/-- The postcondition plan: the transformation followed by a select of the
postconditions (`n` is the transformation's arity). -/
def Rel.post (r : Rel) (n : Nat) (es : List Expr) : Rel :=
  .emit (.project r es) ((List.range es.length).map (n + ·))

theorem Rel.post_eval {cat : Catalog} (hcat : cat.WF) {r : Rel} (hwf : r.WF cat) (es : List Expr) :
    (r.post (r.arity cat) es).eval cat = (r.eval cat).map fun row => es.map (·.eval row) := by
  simp only [Rel.post, Rel.eval, List.map_map]
  apply List.map_congr_left
  intro row hrow
  have hlen := Rel.eval_arity hcat hwf row hrow
  simp only [Function.comp_def]
  have := map_range_getD_off (row ++ es.map (·.eval row)) (r.arity cat) es.length
    (by simp [hlen])
  rw [this, ← hlen, List.drop_left, List.take_of_length_le (by simp)]

/-- What `contract_sound` proves, as a triple: if the checker shows every
postcondition certainly TRUE (for some sound window-key oracle), then
`{Spec} r {RowsSat es}`. -/
theorem Triple.of_contract {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {r : Rel} {es : List Expr}
    (h : ∀ cat : Catalog, cat.WF → Sat (Spec S pre K) cat → r.WF cat →
      ∃ T : WindowKeys, T.Sound cat ∧ (r.post (r.arity cat) es).WF cat ∧
        ((r.post (r.arity cat) es).aeval cat (Spec.env S pre) (Spec.facts pre) T).all
          AVal.certainlyTrue = true) :
    Triple (Spec S pre K) r.query (RowsSat es) := by
  intro cat hcat hsat hwf row hrow e he
  obtain ⟨T, hT, hQ, hproved⟩ := h cat hcat hsat hwf
  have hall := contract_sound hcat (fun t => (hsat t).1) (fun t => (hsat t).2.1) hQ hT hproved
  rw [Rel.post_eval hcat hwf] at hall
  have hv := hall (es.map (·.eval row)) (List.mem_map.2 ⟨row, hrow, rfl⟩) (e.eval row)
    (List.mem_map.2 ⟨e, he, rfl⟩)
  simp [hv, Value.isTrue]

/-- What `Rel.keys_sound` proves, as a triple. -/
theorem Triple.of_keys {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {r : Rel} {ks : List (List Nat)}
    (h : ∀ cat : Catalog, cat.WF → Sat (Spec S pre K) cat → r.WF cat →
      ∀ k ∈ ks, k ∈ r.keys cat (Spec.env S pre) (Spec.facts pre) K) :
    Triple (Spec S pre K) r.query fun rows => ∀ k ∈ ks, KeyOn k rows :=
  fun cat hcat hsat hwf k hk =>
    Rel.keys_sound hcat (Spec.env_sound hsat) (Spec.facts_sound hsat) (fun t => (hsat t).2.2) hwf k
      (h cat hcat hsat hwf k hk)

/-- What `Rel.aeval_sound` proves, as a triple: the output rows match any
schema `Sx` that admits every value the abstract evaluation admits. -/
theorem Triple.of_aeval {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {r : Rel} {Sx : List AVal}
    (h : ∀ cat : Catalog, cat.WF → Sat (Spec S pre K) cat → r.WF cat →
      ∃ T : WindowKeys, T.Sound cat ∧ ∀ i v,
        ((r.aeval cat (Spec.env S pre) (Spec.facts pre) T).getD i AVal.top).Mem v →
          (Sx.getD i AVal.top).Mem v) :
    Triple (Spec S pre K) r.query fun rows => ∀ row ∈ rows, EnvMem Sx row := by
  intro cat hcat hsat hwf row hrow i
  obtain ⟨T, hT, hsub⟩ := h cat hcat hsat hwf
  exact hsub i _ (Rel.aeval_sound hcat (Spec.env_sound hsat) (Spec.facts_sound hsat) hT hwf row hrow i)

/-- **Composed contracts, as `sverify` checks them.** `g` is proved to
guarantee `f`'s whole contract on its input `x` (schema, preconditions and
keys, from `g`'s own preconditions); `f` is proved from that contract. Then
`f ∘ g` satisfies `f`'s postconditions whenever the base tables satisfy
`g`'s preconditions, and `f`'s other inputs satisfy `f`'s. -/
theorem Triple.compose_spec {S S' : String → List AVal} {pre pre' : String → List Expr}
    {K K' : String → List (List Nat)} {f g : Query} {x : String} {B : Relation → Prop}
    (hg : Triple (Spec S pre K) g (Spec S' pre' K' x)) (hf : Triple (Spec S' pre' K') f B)
    (hother : ∀ t, t ≠ x → ∀ rows, Spec S pre K t rows → Spec S' pre' K' t rows) :
    Triple (Spec S pre K) (f.after x g) B :=
  hg.compose hf hother

/-! ## Preconditions under updates

An incremental view keeps its base tables' preconditions true by checking
each batch of changes, not the tables. A batch deletes `del` from `old` and
inserts `ins`: `old ~ kept ++ del` and `new ~ kept ++ ins`. -/

/-- Row-level conditions survive deleting rows. -/
theorem RowsSat.of_subset {es : List Expr} {rows rows' : Relation} (h : RowsSat es rows)
    (hsub : ∀ row ∈ rows', row ∈ rows) : RowsSat es rows' :=
  fun row hr => h row (hsub row hr)

/-- Row-level conditions hold after a batch if they held before and hold on
the inserted rows. -/
theorem RowsSat.update {es : List Expr} {old kept del ins new : Relation} (hold : RowsSat es old)
    (hkept : (kept ++ del).Perm old) (hnew : new.Perm (kept ++ ins)) (hins : RowsSat es ins) :
    RowsSat es new := by
  intro row hr
  rcases List.mem_append.1 (hnew.subset hr) with h | h
  · exact hold.of_subset (fun r hr => hkept.subset (List.mem_append_left del hr)) row h
  · exact hins row h

theorem KeyOn.perm {k : List Nat} {rows rows' : Relation} (h : KeyOn k rows) (hp : rows.Perm rows') :
    KeyOn k rows' :=
  (hp.pairwise_iff fun hne heq => hne heq.symm).1 h

/-- **Keys under updates.** If the old table has key `k`, the inserted rows
agree on `k` with neither each other nor any row that the batch keeps, then
the new table has key `k`. -/
theorem KeyOn.update {k : List Nat} {old kept del ins new : Relation} (hold : KeyOn k old)
    (hkept : (kept ++ del).Perm old) (hnew : new.Perm (kept ++ ins)) (hins : KeyOn k ins)
    (hclash : ∀ x ∈ ins, ∀ y ∈ kept, keyOf k x ≠ keyOf k y) : KeyOn k new := by
  have hk : KeyOn k kept := (List.pairwise_append.1 (hold.perm hkept.symm)).1
  refine KeyOn.perm ?_ hnew.symm
  exact List.pairwise_append.2 ⟨hk, hins, fun y hy x hx heq => hclash x hx y hy heq.symm⟩

/-- A table's whole contract after a batch, from checks on the batch alone:
the inserted rows match the schema and satisfy the row conditions, and their
keys clash with neither each other nor the kept rows. -/
theorem Spec.update {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {t : String} {old kept del ins new : Relation}
    (hold : Spec S pre K t old) (hkept : (kept ++ del).Perm old) (hnew : new.Perm (kept ++ ins))
    (hS : ∀ row ∈ ins, EnvMem (S t) row) (hpre : RowsSat (pre t) ins)
    (hK : ∀ k ∈ K t, KeyOn k ins ∧ ∀ x ∈ ins, ∀ y ∈ kept, keyOf k x ≠ keyOf k y) :
    Spec S pre K t new := by
  refine ⟨fun row hr => ?_, hold.2.1.update hkept hnew hpre, fun k hk =>
    (hold.2.2 k hk).update hkept hnew (hK k hk).1 (hK k hk).2⟩
  rcases List.mem_append.1 (hnew.subset hr) with h | h
  · exact hold.1 row (hkept.subset (List.mem_append_left del h))
  · exact hS row h

/-- **A contracted view's guarantees hold in every state.** If every table
of the old catalog met its contract and every table's batch passed the checks
of `Spec.update`, the view's proved postconditions hold on the new catalog. -/
theorem Triple.maintained {S : String → List AVal} {pre : String → List Expr}
    {K : String → List (List Nat)} {q : Query} {B : Relation → Prop} {cat cat' : Catalog}
    (hq : Triple (Spec S pre K) q B) (hcat' : cat'.WF) (hwf : q.WF cat')
    (hold : Sat (Spec S pre K) cat)
    (hbatch : ∀ t, ∃ kept del ins, (kept ++ del).Perm (cat t).rows ∧
      (cat' t).rows.Perm (kept ++ ins) ∧ (∀ row ∈ ins, EnvMem (S t) row) ∧
      RowsSat (pre t) ins ∧ ∀ k ∈ K t, KeyOn k ins ∧ ∀ x ∈ ins, ∀ y ∈ kept, keyOf k x ≠ keyOf k y) :
    B (q.out cat').rows :=
  hq cat' hcat' (fun t => by
    obtain ⟨kept, del, ins, hkept, hnew, hS, hpre, hK⟩ := hbatch t
    exact Spec.update (hold t) hkept hnew hS hpre hK) hwf

/-! ## Views over views

A `Pipeline` materializes every view and hands its change to the views that
read it as their change table (DBSP's chain rule). The delta rule of the
downstream view needs nothing about the upstream one except that its change
table holds the upstream change (`hδ` of `Rel.delta_correct`); composing that
hypothesis with the upstream `Rel.delta_correct` stacks views. -/

/-- `c` with table `x` replaced by `z`. -/
def ZCatalog.bind (c : ZCatalog) (x : String) (z : ZSet) : ZCatalog :=
  fun t => if t = x then z else c t

/-- **Stacking a view on a materialized one.** `V` reads table `u`, which
holds a view's old state `old`, with its change `Δu` loaded as `δ u`; `V`'s
other inputs are as in `cat` and `Δ`. Then `V`'s delta plan computes `V`'s
change, and `V`'s new state is its old state plus that change, with `u` at
its new state `old ++ Δu`. `Δu` may be any change: an incremental view's
(`Rel.chain_sound`) or a recomputed view's diff (`ZSet.diff_correct`). -/
theorem Rel.stack_sound {C cat Δ : ZCatalog} {δ : String → String} {u : String} {old Δu : ZSet}
    {V : Rel} (hV : V.Incremental) (hu : C u = old) (hδu : C (δ u) = Δu)
    (hold : ∀ t ∈ V.tables, t ≠ u → C t = cat t) (hδ : ∀ t ∈ V.tables, t ≠ u → C (δ t) = Δ t) :
    (V.delta δ).zeval C = V.zdelta (cat.bind u old) (Δ.bind u Δu) ∧
      (V.zeval (cat.bind u old + Δ.bind u Δu)).Perm
        (V.zeval (cat.bind u old) ++ (V.delta δ).zeval C) := by
  have hold' : ∀ t ∈ V.tables, C t = cat.bind u old t := by
    intro t ht
    by_cases h : t = u
    · subst h; simp [ZCatalog.bind, hu]
    · simp [ZCatalog.bind, h, hold t ht h]
  have hδ' : ∀ t ∈ V.tables, C (δ t) = Δ.bind u Δu t := by
    intro t ht
    by_cases h : t = u
    · subst h; simp [ZCatalog.bind, hδu]
    · simp [ZCatalog.bind, h, hδ t ht h]
  exact ⟨Rel.delta_correct hV hold' hδ', Rel.incremental_sound hV hold' hδ'⟩

/-- **The chain rule.** View `U` reads base tables; view `V` reads `U`'s
materialized result as table `u`, and other base tables. If `U`'s change
(the output of its delta plan) is loaded as `V`'s change table `δ u`, then:
`U`'s new state is `U` on the new tables; `V`'s delta plan computes the change
of `V` caused by the base changes and `U`'s change; and `V`'s new state is its
old state plus that change. -/
theorem Rel.chain_sound {C cat Δ : ZCatalog} {δ : String → String} {u : String} {U V : Rel}
    (hU : U.Incremental) (hV : V.Incremental)
    (holdU : ∀ t ∈ U.tables, C t = cat t) (hδU : ∀ t ∈ U.tables, C (δ t) = Δ t)
    (hu : C u = U.zeval cat) (hδu : C (δ u) = (U.delta δ).zeval C)
    (hold : ∀ t ∈ V.tables, t ≠ u → C t = cat t) (hδ : ∀ t ∈ V.tables, t ≠ u → C (δ t) = Δ t) :
    (C u ++ C (δ u)).Perm (U.zeval (cat + Δ)) ∧
      (V.delta δ).zeval C = V.zdelta (cat.bind u (U.zeval cat)) (Δ.bind u (U.zdelta cat Δ)) ∧
      (V.zeval (cat.bind u (U.zeval cat) + Δ.bind u (U.zdelta cat Δ))).Perm
        (V.zeval (cat.bind u (U.zeval cat)) ++ (V.delta δ).zeval C) := by
  have hUδ : C (δ u) = U.zdelta cat Δ := hδu.trans (Rel.delta_correct hU holdU hδU)
  refine ⟨?_, Rel.stack_sound hV hu hUδ hold hδ⟩
  rw [hu, hUδ]
  exact (Rel.zeval_add hU).symm

/-- A row's total weight in a Z-set. -/
def ZSet.weight (z : ZSet) (r : Row) : Int :=
  ((List.filter (fun x : Row × Int => x.1 == r) z).map (·.2)).sum

def ZSet.neg (z : ZSet) : ZSet := List.map (fun x : Row × Int => (x.1, -x.2)) z

theorem ZSet.weight_append (a b : ZSet) (r : Row) : (a ++ b).weight r = a.weight r + b.weight r := by
  simp [ZSet.weight, List.filter_append, List.sum_append]

theorem ZSet.weight_neg (z : ZSet) (r : Row) : z.neg.weight r = -z.weight r := by
  induction z with
  | nil => simp [ZSet.neg, ZSet.weight]
  | cons x z ih =>
      simp only [ZSet.neg, ZSet.weight, List.map_cons, List.filter_cons] at ih ⊢
      split <;> simp_all <;> omega

/-- **Recompute and diff.** A view without a delta rule is recomputed (`new`)
and its change taken as `new - old`; its old state plus that change has the
weights of `new`, so it is a correct change for the views downstream. -/
theorem ZSet.diff_correct (old new : ZSet) (r : Row) :
    (old ++ (new ++ old.neg)).weight r = new.weight r := by
  simp only [ZSet.weight_append, ZSet.weight_neg]
  omega

end Substrait
