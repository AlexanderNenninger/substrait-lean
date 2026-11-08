import Sverify.Core.Decomposable
import Sverify.Core.OrderAllowed
import Sverify.Core.StatProps
import Sverify.Core.ObsEquiv

/-!
# What the reference allows

The reference semantics is a relation: for each input it allows a set of
results (`Rel.Allowed`), and an engine is correct when it returns one of them
or raises. `Rel.eval` computes one allowed result, a witness
(`Rel.eval_allowed`).

The reference leaves these choices to the engine:

* the order of rows, except what an `ORDER BY` promises, how the ties of an
  `ORDER BY` or of a window's order are broken, and the order of a clustered
  sort key's groups;
* the order in which an aggregate takes its rows: `FIRST`/`LAST`, `collect`
  and `string_agg` take them in their sort order with ties broken any way,
  and without a sort in any order;
* none of an aggregate's value since D25 and D30: a double `SUM`, `AVG` and
  statistical aggregate are their exact values rounded once.

A double `SUM` or `AVG` is no choice (D25): it is the exact sum, or mean,
rounded once (`floatSumCR`, `core/Sverify/Core/FloatExact.lean`), whatever the
order of the rows. An engine's order of additions is a behaviour of its
profile (`SumOrder`, `core/Sverify/Core/AllowedP.lean`), within #85's bound of it
(`epsilon_sum_cr` in `float-bounds/`).

For a plan without these choices (`Rel.detPlan`, `SubstraitLean/AllowedAnalysis.lean`),
every allowed result is `Rel.eval`'s up to the order of rows
(`Rel.allowed_perm_eval`), so whatever is proved of `Rel.eval`'s rows holds
of every allowed result. A rewrite is
correct when it **refines** the plan up to an observation
(`Rel.RefinesUpTo`): every result it allows is, up to the observation, one
the plan allows. `Rel.Refines` is the exact case and `Rel.RefinesBag` the
one up to the order of rows. A rewrite to a plan without choices whose rows
are the original's refines it up to the order of rows (`Rel.refines_of_perm`),
and an unsorted plan refines its `ORDER BY` twin in that sense only
(`Rel.unsorted_refinesBag_not_refines`).
-/

namespace Substrait

/-! ## Aggregates -/

/-- What an aggregate of the values `vs`, taken in this order, may give. -/
def AggFn.Allowed (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  -- A double between the two neighbours (#53).
  | .quantile true num scale => if vs = [] then v = .null else contAllowed num scale (sortVals vs) v
  | _ => v = f.apply vs

theorem AggFn.apply_allowed (f : AggFn) (vs : List Value) : f.Allowed vs (f.apply vs) := by
  cases f
  case quantile cont num scale =>
    cases cont
    · rfl
    · cases vs with
      | nil => rfl
      | cons v vs => simp only [Allowed, reduceCtorEq, ite_false]; exact contValue_allowed _ _ _
  all_goals rfl

/-- An aggregate that combines in two phases is a function of its values. -/
theorem AggFn.allowed_iff {f : AggFn} (hf : f.orderFree = true) (vs : List Value) (v : Value) :
    f.Allowed vs v ↔ v = f.apply vs := by
  cases f <;> simp_all [orderFree, decomposable, Allowed]

/-- What a measure over a group's `rows` may give: its aggregate of the rows
in some order, sorted by the measure's own order where it takes one. -/
def Measure.Allowed (m : Measure) (rows : Relation) (v : Value) : Prop :=
  ∃ s, s.Perm rows ∧ (m.fn.sorts = true → s.Pairwise (sortLe m.sort · · = true)) ∧
    m.fn.Allowed (m.inputs s) v

theorem Measure.eval_allowed (m : Measure) (rows : Relation) : m.Allowed rows (m.eval rows) := by
  by_cases hs : m.fn.sorts = true
  · refine ⟨rows.mergeSort (sortLe m.sort), List.mergeSort_perm _ _, fun _ =>
      List.pairwise_mergeSort (sortLe_totalPre _).trans (sortLe_totalPre _).total rows, ?_⟩
    rw [Measure.eval_sorts hs]; exact AggFn.apply_allowed _ _
  · refine ⟨rows, .refl _, fun h => absurd h hs, ?_⟩
    rw [Measure.eval_eq (by simpa using hs)]; exact AggFn.apply_allowed _ _

/-- An order-free measure allows only its value. -/
theorem Measure.allowed_eq {m : Measure} (hm : m.orderFree = true) {rows : Relation} {v : Value}
    (h : m.Allowed rows v) : v = m.eval rows := by
  obtain ⟨s, hs, _, hv⟩ := h
  rw [AggFn.allowed_iff hm] at hv
  rw [hv, ← Measure.eval_eq (AggFn.ne_collect_of_orderFree hm), Measure.eval_perm hm hs]

/-- What an aggregate's output may be, for the input rows `rows` in this
order: a row per group (in their order of first appearance), each measure
one of its allowed values. -/
def aggAllowed (gs : List Expr) (ms : List Measure) (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.Allowed rows v) ms vs
  else Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.Allowed (groupRows gs rows k) v) ms vs)
    (dedup (rows.map (groupKey gs))) out

theorem aggregateEval_allowed (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggAllowed gs ms rows (aggregateEval gs ms rows) := by
  unfold aggAllowed aggregateEval
  split
  · exact ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_allowed m rows⟩
  · exact forall₂_map_self _ fun k _ =>
      ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_allowed m _⟩

theorem aggAllowed_eq {gs : List Expr} {ms : List Measure} (hms : ∀ m ∈ ms, m.orderFree = true)
    {rows out : Relation} (h : aggAllowed gs ms rows out) : out = aggregateEval gs ms rows := by
  have hvals : ∀ {rows : Relation} {vs : List Value},
      Forall2 (fun m v => m.Allowed rows v) ms vs → vs = ms.map (·.eval rows) := by
    intro rows vs hv
    apply eq_map_of_forall₂
    have : ∀ {ms' : List Measure}, (∀ m ∈ ms', m.orderFree = true) → ∀ {vs : List Value},
        Forall2 (fun m v => m.Allowed rows v) ms' vs →
          Forall2 (fun m v => v = m.eval rows) ms' vs := by
      intro ms' hms' vs hv
      induction hv with
      | nil => exact .nil
      | cons hmv _ ih =>
        exact .cons (Measure.allowed_eq (hms' _ (List.mem_cons_self ..)) hmv)
          (ih fun m hm => hms' m (List.mem_cons_of_mem _ hm))
    exact this hms hv
  unfold aggAllowed at h; unfold aggregateEval
  split at h
  · next hg => obtain ⟨vs, rfl, hv⟩ := h; rw [hvals hv]; simp [hg]
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    apply eq_map_of_forall₂
    have : ∀ {ks : List Row} {out : Relation}, Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
        Forall2 (fun m v => m.Allowed (groupRows gs rows k) v) ms vs) ks out →
        Forall2 (fun k row => row = k ++ ms.map (·.eval (groupRows gs rows k))) ks out := by
      intro ks out h
      induction h with
      | nil => exact .nil
      | cons hk _ ih =>
        obtain ⟨vs, rfl, hv⟩ := hk
        exact .cons (by rw [hvals hv]) ih
    exact this h

/-! ## Plans -/

/-- The results the reference allows for `r` on the catalog `cat`, as lists
of rows. A list's order is a result's only below an `ORDER BY`: elsewhere
any order is allowed. -/
def Rel.Allowed (cat : Catalog) : Rel → Relation → Prop
  | .read t, out => out.Perm (cat t).rows
  | .values _ rows, out => out.Perm rows
  | .filter r c, out => ∃ i, r.Allowed cat i ∧ out = i.filter fun row => (c.eval row).isTrue
  | .project r es, out => ∃ i, r.Allowed cat i ∧ out = i.map fun row => row ++ es.map (·.eval row)
  | .emit r m, out => ∃ i, r.Allowed cat i ∧ out = i.map fun row => m.map (row.getD · .null)
  | .cross a b, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧ out.Perm (crossRows x y)
  | .join a b .inner on, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧
      out.Perm ((crossRows x y).filter fun row => (on.eval row).isTrue)
  | .join a b .left on, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧
      out.Perm (x.flatMap (leftJoinRow on (b.arity cat) y))
  -- The first rows of an allowed order: any rows, unless an `ORDER BY` fixes it.
  | .fetch r off cnt, out => ∃ i, r.Allowed cat i ∧ out = match cnt with
      | none => i.drop off
      | some n => (i.drop off).take n
  | .unionAll a b, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧ out.Perm (x ++ y)
  -- The window functions over the input in any order its sort allows.
  | .window r part sort fns, out => ∃ i, r.Allowed cat i ∧ ∃ s, s.Perm i ∧
      s.Pairwise (sortLe sort · · = true) ∧ out.Perm (windowRows part fns [] s)
  | .semi a b anti on, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row != anti)
  -- The input sorted, ties and a clustered key's groups in any order.
  | .orderBy r keys, out => ∃ i, r.Allowed cat i ∧ out.Perm i ∧ SortAllowed keys out
  | .distinct r, out => ∃ i, r.Allowed cat i ∧ out.Perm (dedup i)
  | .aggregate r gs ms, out => ∃ i, r.Allowed cat i ∧ ∃ o, out.Perm o ∧ aggAllowed gs ms i o
  | .unnest r c, out => ∃ i, r.Allowed cat i ∧ out.Perm (i.flatMap (unnestRow c))

/-- **`Rel.eval` is a witness**: its result is one the reference allows. -/
theorem Rel.eval_allowed (cat : Catalog) : ∀ r : Rel, r.Allowed cat (r.eval cat)
  | .read _ | .values _ _ => .refl _
  | .filter r _ | .project r _ | .emit r _ => ⟨_, eval_allowed cat r, rfl⟩
  | .cross a b | .unionAll a b | .semi a b _ _ =>
    ⟨_, _, eval_allowed cat a, eval_allowed cat b, .refl _⟩
  | .join a b .inner _ | .join a b .left _ =>
    ⟨_, _, eval_allowed cat a, eval_allowed cat b, .refl _⟩
  | .fetch r _ cnt => ⟨_, eval_allowed cat r, by cases cnt <;> rfl⟩
  | .window r _ sort _ => ⟨_, eval_allowed cat r, _, List.mergeSort_perm _ _,
      List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total _, .refl _⟩
  | .orderBy r keys => ⟨_, eval_allowed cat r, List.mergeSort_perm _ _, .of_sorted <|
      List.pairwise_mergeSort (sortLe_totalPre keys).trans (sortLe_totalPre keys).total _⟩
  | .distinct r | .unnest r _ => ⟨_, eval_allowed cat r, .refl _⟩
  | .aggregate r gs ms => ⟨_, eval_allowed cat r, _, .refl _, aggregateEval_allowed gs ms _⟩

/-! ## Refinement -/

/-- **`q` refines `r` up to the observation `o`**: every result `q` allows
is, up to `o`, one `r` allows. A correct rewrite refines the plan it
rewrites: it may narrow the set of allowed results, never widen it.
`o = Obs.exact` keeps the order an `ORDER BY` fixes (`Rel.Refines`);
`o = {rows := .multiset}` forgets the order of rows (`Rel.RefinesBag`). -/
def Rel.RefinesUpTo (o : Obs) (ctx : ObsCtx) (cat : Catalog) (q r : Rel) : Prop :=
  ∀ out, q.Allowed cat out → ∃ out', r.Allowed cat out' ∧ Relation.Equiv o ctx out out'

/-- **`q` refines `r`**: every result `q` allows, `r` allows (`Rel.refines_iff`). -/
abbrev Rel.Refines (cat : Catalog) (q r : Rel) : Prop := Rel.RefinesUpTo Obs.exact {} cat q r

/-- `q` refines `r` up to the order of rows: every result `q` allows, `r`
allows in some order. An unsorted plan refines its `ORDER BY` twin in this
sense only. -/
abbrev Rel.RefinesBag (cat : Catalog) (q r : Rel) : Prop :=
  Rel.RefinesUpTo { rows := .multiset } {} cat q r

theorem Rel.refines_iff {cat : Catalog} {q r : Rel} :
    q.Refines cat r ↔ ∀ out, q.Allowed cat out → r.Allowed cat out :=
  ⟨fun h out ho => by obtain ⟨out', h', e⟩ := h out ho; rwa [Relation.Equiv_exact.1 e],
    fun h out ho => ⟨out, h out ho, Relation.Equiv_exact.2 rfl⟩⟩

theorem Rel.refinesBag_iff {cat : Catalog} {q r : Rel} :
    q.RefinesBag cat r ↔ ∀ out, q.Allowed cat out → ∃ out', r.Allowed cat out' ∧ out.Perm out' := by
  simp only [Rel.RefinesUpTo, Relation.Equiv_multiset_perm]

theorem Rel.RefinesUpTo.refl {o : Obs} {ctx : ObsCtx} (hc : ctx.WF) (cat : Catalog) (r : Rel) :
    r.RefinesUpTo o ctx cat r :=
  fun out h => ⟨out, h, .refl hc out⟩

theorem Rel.RefinesUpTo.trans {o : Obs} {c₁ c₂ c₃ : ObsCtx} (hc : ObsCtx.Comp c₁ c₂ c₃)
    {cat : Catalog} {p q r : Rel} (h₁ : p.RefinesUpTo o c₁ cat q) (h₂ : q.RefinesUpTo o c₂ cat r) :
    p.RefinesUpTo o c₃ cat r :=
  fun out h => by
    obtain ⟨o₁, h₁', e₁⟩ := h₁ out h
    obtain ⟨o₂, h₂', e₂⟩ := h₂ o₁ h₁'
    exact ⟨o₂, h₂', e₁.trans hc e₂⟩

/-- A refinement up to a finer observation is one up to a coarser one. -/
theorem Rel.RefinesUpTo_mono {o' o : Obs} {ctx : ObsCtx} (hc : ctx.WF) (h : o'.le o = true)
    {cat : Catalog} {q r : Rel} (hq : q.RefinesUpTo o' ctx cat r) : q.RefinesUpTo o ctx cat r :=
  fun out ho => by
    obtain ⟨out', h', e⟩ := hq out ho
    exact ⟨out', h', Relation.Equiv_mono hc h e⟩

theorem Rel.Refines.refl (cat : Catalog) (r : Rel) : r.Refines cat r :=
  Rel.RefinesUpTo.refl .default cat r

theorem Rel.Refines.trans {cat : Catalog} {p q r : Rel} (h₁ : p.Refines cat q)
    (h₂ : q.Refines cat r) : p.Refines cat r :=
  Rel.RefinesUpTo.trans (.self .default fun _ _ _ _ _ e₁ e₂ => e₁.trans e₂) h₁ h₂

theorem Rel.RefinesBag.trans {cat : Catalog} {p q r : Rel} (h₁ : p.RefinesBag cat q)
    (h₂ : q.RefinesBag cat r) : p.RefinesBag cat r :=
  Rel.RefinesUpTo.trans (.self .default fun _ _ _ _ _ e₁ e₂ => e₁.trans e₂) h₁ h₂

/-- A refinement is one up to the order of rows. -/
theorem Rel.Refines.bag {cat : Catalog} {q r : Rel} (h : q.Refines cat r) : q.RefinesBag cat r :=
  Rel.RefinesUpTo_mono .default (Obs.exact_le _) h

/-- **The order an `ORDER BY` fixes counts**: a plan's rows unsorted refine
its `ORDER BY` twin up to the order of rows and not exactly. -/
theorem Rel.unsorted_refinesBag_not_refines :
    let q : Rel := .values 1 [[.int 2], [.int 1]]
    let cat : Catalog := fun _ => { arity := 0, rows := [] }
    q.RefinesBag cat (.orderBy q [{ col := 0 }]) ∧ ¬ q.Refines cat (.orderBy q [{ col := 0 }]) := by
  intro q cat
  have hs : ¬ SortAllowed [{ col := 0 }] [[.int 2], [.int 1]] := by
    rintro ⟨cmp, -, h⟩
    simp [sortLeWith, SortKey.leWith, SortKey.valWith, SortKey.valLe, lexLe, nullRankOf, natLe,
      SortKey.firstNulls] at h
    revert h; decide +kernel
  refine ⟨Rel.refinesBag_iff.2 fun out ho => ⟨[[.int 1], [.int 2]], ⟨_, .refl _, .swap _ _ _,
    .of_sorted (by decide +kernel)⟩, ho.trans (.swap _ _ _)⟩, fun h => hs ?_⟩
  obtain ⟨i, -, -, hsort⟩ := Rel.refines_iff.1 h _ (List.Perm.refl _)
  exact hsort

end Substrait
