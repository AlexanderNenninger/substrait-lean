import SubstraitLean.Ties
import SubstraitLean.Rows
import SubstraitLean.AllowedAnalysis

/-!
# What the analysis knows of a relation (#902)

The checker's analyses describe a relation four ways: each column's abstract
value (`Rel.aeval`), facts relating columns (`Rel.facts`), keys (`Rel.keys`)
and a bound on its rows (`Rel.maxRows`). `Knowledge` holds the four, and
`Knowledge.Mem` says what it means for rows to fit them.

* `KnowledgeEnv` is what the checker receives of the input tables, and
  `KnowledgeEnv.Sound` its one hypothesis: every table's rows fit their
  knowledge. It replaces the separate hypotheses on schemas (`hA`), facts
  (`hF`), keys (`hK`) and the window-key oracle (`hT`), which
  `KnowledgeEnv.windows` now derives.
* `Rel.analyse` runs the four analyses, and `Rel.analyse_sound_all` proves
  the result holds of every result the reference allows under every tie
  order (`Rel.OrderAllowed`, D24); `Rel.analyse_sound` of `Rel.eval`.
* The consumers, stated on one hypothesis: `Knowledge.contract_sound`,
  `Knowledge.contract_sound_all`, `Knowledge.mayIssues_sound`,
  `Knowledge.guardFree_sound`, `Knowledge.duckdb_sound` (`DuckDBProfile.lean`),
  `Knowledge.allowed_perm_eval`, `Knowledge.refines_of_perm` and
  `Knowledge.eval_sharded`.

This step wraps the four analyses; EPIC2's step 4 (#904) merges them into one
recursion and removes the oracle.
-/

namespace Substrait

/-- What the analysis knows of a relation. -/
structure Knowledge where
  /-- Each column's abstract value. -/
  cols : List AVal
  /-- Facts every row satisfies. -/
  facts : List Fact
  /-- Column sets on which no two rows agree. -/
  keys : List (List Nat)
  /-- At most this many rows. -/
  rows : Option Nat := none

/-- The rows fit the knowledge. -/
def Knowledge.Mem (k : Knowledge) (rows : Relation) : Prop :=
  (∀ row ∈ rows, EnvMem k.cols row) ∧ (∀ row ∈ rows, FactsHold k.facts row) ∧
    (∀ key ∈ k.keys, KeyOn key rows) ∧ ∀ n, k.rows = some n → rows.length ≤ n

/-- The input tables' knowledge, as the checker receives it. -/
abbrev KnowledgeEnv := String → Knowledge

namespace KnowledgeEnv

/-- Every table's rows fit their knowledge. -/
def Sound (K : KnowledgeEnv) (cat : Catalog) : Prop := ∀ t, (K t).Mem (cat t).rows

abbrev cols (K : KnowledgeEnv) (t : String) : List AVal := (K t).cols
abbrev facts (K : KnowledgeEnv) (t : String) : List Fact := (K t).facts
abbrev keys (K : KnowledgeEnv) (t : String) : List (List Nat) := (K t).keys

/-- Which windows have a key of their input among their partition and sort
columns: derived from the keys, so no longer an oracle the caller supplies. -/
def windows (K : KnowledgeEnv) (cat : Catalog) : WindowKeys :=
  Rel.keyedWindows cat K.cols K.facts K.keys

variable {K : KnowledgeEnv} {cat : Catalog}

theorem Sound.cols (h : K.Sound cat) : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (K.cols t) row :=
  fun t => (h t).1

theorem Sound.facts (h : K.Sound cat) : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (K.facts t) row :=
  fun t => (h t).2.1

theorem Sound.keys (h : K.Sound cat) : ∀ t, ∀ k ∈ K.keys t, KeyOn k (cat t).rows :=
  fun t => (h t).2.2.1

theorem Sound.windows (hcat : cat.WF) (h : K.Sound cat) : (K.windows cat).SoundAll cat :=
  Rel.keyedWindows_soundAll hcat h.cols h.facts h.keys

/-- The knowledge `substrait-check --contract` starts from: each table's
schema refined by its preconditions, the facts they state, and its keys. -/
def ofSpec (S : String → List AVal) (pre : String → List Expr)
    (keys : String → List (List Nat)) : KnowledgeEnv :=
  fun t => ⟨tableEnv (S t) (pre t), (pre t).flatMap Expr.factsOf, keys t, none⟩

theorem ofSpec_sound {S : String → List AVal} {pre : String → List Expr}
    {keys : String → List (List Nat)}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hkeys : ∀ t, ∀ k ∈ keys t, KeyOn k (cat t).rows) : (ofSpec S pre keys).Sound cat :=
  fun t => ⟨fun row h => tableEnv_sound (hS t row h) (hpre t row h),
    fun row h f hf => by
      obtain ⟨e, he, hf⟩ := List.mem_flatMap.mp hf
      exact Expr.factsOf_sound e (hpre t row h e he) f hf,
    hkeys t, fun _ h => by simp [ofSpec] at h⟩

end KnowledgeEnv

/-- The analysis, as a wrapper over the four it replaces. `sz` is
`Rel.aeval`'s: whether the plan is small enough to bound float sums. -/
def Rel.analyse (cat : Catalog) (K : KnowledgeEnv) (sz : Bool := false) (r : Rel) : Knowledge :=
  ⟨r.aeval cat K.cols K.facts (K.windows cat) sz, r.facts cat K.facts (K.windows cat),
    r.keys cat K.cols K.facts K.keys, r.maxRows⟩

/-- **The analysis is sound under every tie order** (D24). -/
theorem Rel.analyse_sound_all {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) {r : Rel} (hwf : r.WF cat) {out : Relation}
    (ho : r.OrderAllowed cat out) : (r.analyse cat K).Mem out :=
  ⟨Rel.aeval_sound_all hcat hK.cols hK.facts (hK.windows hcat) hwf ho,
    Rel.facts_sound_all hcat hK.facts (hK.windows hcat) hwf ho,
    fun k hk => Rel.keys_sound_all hcat hK.cols hK.facts hK.keys hwf k hk ho,
    fun _ hn => Rel.maxRows_sound_all hn ho⟩

/-- **The analysis is sound** for `Rel.eval`, also with float sums bounded
on small plans. -/
theorem Rel.analyse_sound {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) {sz : Bool} {r : Rel} (hwf : r.WF cat) (hs : sz = true → r.Small cat) :
    (r.analyse cat K sz).Mem (r.eval cat) :=
  ⟨Rel.aeval_sound hcat hK.cols hK.facts (hK.windows hcat) hwf hs,
    Rel.facts_sound hcat hK.facts (hK.windows hcat) hwf,
    Rel.keys_sound hcat hK.cols hK.facts hK.keys hwf, fun _ hn => Rel.maxRows_sound hn⟩

namespace Knowledge

/-- A row of a well-formed plan whose every column the analysis proves true
is all `true`. -/
theorem allTrue {cat : Catalog} {K : KnowledgeEnv} {Q : Rel} (hQ : Q.WF cat)
    (hproved : (Q.analyse cat K).cols.all AVal.certainlyTrue = true) {row : Row}
    (hlen : row.length = Q.arity cat) (hm : EnvMem (Q.analyse cat K).cols row) :
    ∀ v ∈ row, v = .bool true := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hlen' : j < (Q.analyse cat K).cols.length := by
    simp only [Rel.analyse]; rw [Rel.aeval_length (cat := cat) hQ, ← hlen]; exact hj
  have hc := List.all_eq_true.mp hproved _ (List.getElem_mem hlen')
  have := hm j
  simp only [List.getElem?_eq_getElem hlen', Option.getD_some, List.getD,
    List.getElem?_eq_getElem hj] at this
  exact AVal.certainlyTrue_mem hc this

/-- **Soundness of the contract check** on one hypothesis: if the analysis
proves every column of `Q` true, every row of `Q` is all `true`. -/
theorem contract_sound {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat)
    {Q : Rel} (hQ : Q.WF cat)
    (hproved : (Q.analyse cat K).cols.all AVal.certainlyTrue = true) :
    ∀ row ∈ Q.eval cat, ∀ v ∈ row, v = .bool true := fun row hrow =>
  allTrue hQ hproved (Rel.eval_arity hcat hQ row hrow)
    ((Q.analyse_sound hcat hK (sz := false) hQ nofun).1 row hrow)

/-- `contract_sound` for every result under every tie order (D24). -/
theorem contract_sound_all {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) {Q : Rel} (hQ : Q.WF cat)
    (hproved : (Q.analyse cat K).cols.all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out → ∀ row ∈ out, ∀ v ∈ row, v = .bool true :=
  fun ho row hrow => allTrue hQ hproved (Rel.orderAllowed_arity hcat hQ ho row hrow)
    ((Q.analyse_sound_all hcat hK hQ ho).1 row hrow)

/-- `Rel.mayIssues_sound` on one hypothesis. -/
theorem mayIssues_sound {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat)
    {u : Bool} {r : Rel} (hwf : r.WF cat) (hsm : r.Small cat) {p : Issue × Expr}
    (h : r.HasIssue cat u p) : p ∈ r.mayIssues cat K.cols K.facts (K.windows cat) u :=
  Rel.mayIssues_sound hcat hK.cols hK.facts (hK.windows hcat) hwf hsm p h

/-- `Rel.guardFree_sound` on one hypothesis. -/
theorem guardFree_sound {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat K.cols K.facts (K.windows cat) false).all (·.1.assumed) = true)
    {I : Impl} (hI : I.Faithful) : r.eval cat I = r.eval cat :=
  Rel.guardFree_sound hcat hK.cols hK.facts (hK.windows hcat) hwf hsmall hs hm hI

/-- `Rel.allowed_perm_eval` on one hypothesis. -/
theorem allowed_perm_eval {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hd : r.detPlan cat K.cols K.facts K.keys = true)
    {out : Relation} (h : r.Allowed cat out) : out.Perm (r.eval cat) :=
  Rel.allowed_perm_eval hcat hK.cols hK.facts hK.keys hwf hd h

/-- `Rel.refines_of_perm` on one hypothesis. -/
theorem refines_of_perm {cat : Catalog} (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat)
    {q r : Rel} (hwf : q.WF cat) (hd : q.detPlan cat K.cols K.facts K.keys = true)
    (h : (q.eval cat).Perm (r.eval cat)) : q.RefinesBag cat r :=
  Rel.refines_of_perm hcat hK.cols hK.facts hK.keys hwf hd h

/-- `Rel.eval_sharded` with the window keys the knowledge derives. -/
theorem eval_sharded {S : String → Bool} {SK : String → Option (List Nat)} {cat : Catalog}
    (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat) {cs : List Catalog}
    (hs : Sharding S SK cat cs) {r : Rel} (hwf : r.WF cat)
    (hl : r.linear S SK (K.windows cat) cat = true) : (r.eval cat).Perm (cs.flatMap r.eval) :=
  Rel.eval_sharded hs (hK.windows hcat) hwf hl

end Knowledge

end Substrait
