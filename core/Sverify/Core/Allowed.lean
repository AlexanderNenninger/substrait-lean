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

For a plan without these choices (`Rel.detPlan`, `analysis/Sverify/Analysis/AllowedAnalysis.lean`),
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
variable [Boxes.Ambient]

/-! ## Aggregates -/

/-- What an aggregate of the values `vs`, taken in this order, may give. -/
def AggFn.Allowed (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  -- A double between the two neighbours (#53).
  | .quantile true num scale => if vs = [] then v = .null else contAllowed num scale (sortVals vs) v
  -- `MIN` and `MAX`: any member of the value's class (D31).
  | _ => f.Picks vs v

theorem AggFn.apply_allowed (f : AggFn) (vs : List Value) : f.Allowed vs (f.apply vs) := by
  cases f
  case quantile cont num scale =>
    cases cont
    · exact AggFn.picks_apply _ _
    · cases vs with
      | nil => rfl
      | cons v vs => simp only [Allowed, reduceCtorEq, ite_false]; exact contValue_allowed _ _ _
  all_goals exact AggFn.picks_apply _ _

theorem AggFn.allowed_of_picks {f : AggFn} {vs : List Value} {v : Value} (h : f.Picks vs v) :
    f.Allowed vs v := by
  rcases h' : h with h₁ | ⟨hf, _⟩
  · rw [h₁]; exact AggFn.apply_allowed _ _
  · cases f with
    | quantile cont _ _ => cases cont
                           · exact h
                           · simp [AggFn.classPick] at hf
    | _ => exact h

/-- An aggregate that combines in two phases gives its value, or for `MIN`
and `MAX` another member of its class. -/
theorem AggFn.allowed_iff {f : AggFn} (hf : f.orderFree = true) (vs : List Value) (v : Value) :
    f.Allowed vs v ↔ f.Picks vs v := by
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

/-- A measure allows the same values on a permutation of its rows. -/
theorem Measure.Allowed.perm {m : Measure} {rows rows' : Relation} {v : Value}
    (h : m.Allowed rows v) (hp : rows.Perm rows') : m.Allowed rows' v :=
  let ⟨s, hs, ho, hv⟩ := h; ⟨s, hs.trans hp, ho, hv⟩

/-- An order-free measure allows its value, or for `MIN` and `MAX` another
member of its class. -/
theorem Measure.allowed_picks {m : Measure} (hm : m.orderFree = true) {rows : Relation}
    {v : Value} (h : m.Allowed rows v) : m.fn.Picks (m.inputs rows) v := by
  obtain ⟨s, hs, _, hv⟩ := h
  rw [AggFn.allowed_iff hm] at hv
  have hp := m.inputs_perm hs
  have he : m.fn.apply (m.inputs s) = m.fn.apply (m.inputs rows) := by
    rw [← Measure.eval_eq (AggFn.ne_collect_of_orderFree hm),
      ← Measure.eval_eq (AggFn.ne_collect_of_orderFree hm), Measure.eval_perm hm hs]
  rcases hv with hv | ⟨hf, hc, hm⟩
  · exact .inl (hv.trans he)
  · refine .inr ⟨hf, hc.trans (by rw [he]), ?_⟩
    rcases hm with hm | hm
    · exact .inl (hp.mem_iff.mp hm)
    · exact .inr (hm.trans (by rw [he]))

/-- An order-free measure other than `MIN` and `MAX` allows only its value. -/
theorem Measure.allowed_eq {m : Measure} (hm : m.orderFree = true) (hmin : m.fn ≠ .min)
    (hmax : m.fn ≠ .max) {rows : Relation} {v : Value} (h : m.Allowed rows v) : v = m.eval rows := by
  rcases Measure.allowed_picks hm h with hv | ⟨hf, -⟩
  · rw [hv, Measure.eval_eq (AggFn.ne_collect_of_orderFree hm)]
  · rcases AggFn.minmax_of_classPick hm hf with hf | hf <;> contradiction

/-- **A measure whose ties agree on its argument allows only its value**: the
reference fixes its order up to the ties (`sortLe`, no open comparison), and
the ties change none of its inputs. -/
theorem Measure.allowed_eq_of_ties {m : Measure} (hs : m.fn.sorts = true) {rows : Relation}
    (ht : m.TiesAgree rows) {v : Value} (h : m.Allowed rows v) : v = m.eval rows := by
  obtain ⟨s, hp, hsort, hv⟩ := h
  have hv' : v = m.fn.apply (m.inputs s) := by
    cases hf : m.fn <;> simp only [hf, AggFn.sorts, Bool.false_eq_true] at hs <;>
      simpa [hf, AggFn.Allowed, AggFn.Picks, AggFn.classPick] using hv
  have hm := List.mergeSort_perm rows (sortLe m.sort)
  rw [hv', Measure.eval_sorts hs, Measure.inputs_eq_of_sorted (hp.trans hm.symm) (hsort hs)
    (mergeSort_sorted _ _) (ht.perm hm)]

/-- What an aggregate's output may be, for the input rows `rows` in this
order: a row per group (in their order of first appearance), each measure
one of its allowed values. -/
def aggAllowed (gs : List Expr) (ms : List Measure) (rows out : Relation) : Prop :=
  if gs.isEmpty then ∃ vs, out = [vs] ∧ Forall2 (fun m v => m.Allowed rows v) ms vs
  -- One key per class of keys, any member (D31): `groupRows` is the same for each.
  else ∃ ks, IsReps Row.canon (rows.map (groupKey gs)) ks ∧ Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
      Forall2 (fun m v => m.Allowed (groupRows gs rows k) v) ms vs) ks out

theorem aggregateEval_allowed (gs : List Expr) (ms : List Measure) (rows : Relation) :
    aggAllowed gs ms rows (aggregateEval gs ms rows) := by
  unfold aggAllowed aggregateEval
  split
  · exact ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_allowed m rows⟩
  · exact ⟨_, canonReps_isReps Row.leRaw_rawOrder _, forall₂_map_self _ fun k _ =>
      ⟨_, rfl, forall₂_map_self ms fun m _ => Measure.eval_allowed m _⟩⟩

/-- **An aggregate allows only its rows**, in some order, when each measure
is order-free or its ties agree on its argument, and its keys and its `MIN`s'
and `MAX`s' arguments are alone in their classes (no doubles): then there is
no value to choose (D31). -/
theorem aggAllowed_eq {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (hms : ∀ m ∈ ms, m.orderFree = true ∨ (m.fn.sorts = true ∧ m.TiesAgreeIn gs rows))
    (hk : ∀ r ∈ rows, (groupKey gs r).Lone)
    (ha : ∀ m ∈ ms, (m.fn = .min ∨ m.fn = .max) → ∀ r ∈ rows, (m.arg.eval r).Lone)
    (h : aggAllowed gs ms rows out) : out.Perm (aggregateEval gs ms rows) := by
  have hvals : ∀ {grp : Relation}, (∀ r ∈ grp, r ∈ rows) →
      (∀ m : Measure, m.TiesAgreeIn gs rows → m.TiesAgree grp) → ∀ {vs : List Value},
      Forall2 (fun m v => m.Allowed grp v) ms vs → vs = ms.map (·.eval grp) := by
    intro grp hg hgt vs hv
    apply eq_map_of_forall₂
    have : ∀ {ms' : List Measure}, (∀ m ∈ ms', m ∈ ms) → ∀ {vs : List Value},
        Forall2 (fun m v => m.Allowed grp v) ms' vs →
          Forall2 (fun m v => v = m.eval grp) ms' vs := by
      intro ms' hms' vs hv
      induction hv with
      | nil => exact .nil
      | cons hmv _ ih =>
        have hmem := hms' _ List.mem_cons_self
        refine .cons ?_ (ih fun m' hm' => hms' m' (List.mem_cons_of_mem _ hm'))
        rcases hms _ hmem with hof | ⟨hs, ht⟩
        · have hp := Measure.allowed_picks hof hmv
          rw [Measure.eval_eq (AggFn.ne_collect_of_orderFree hof)]
          rcases hp' : hp with h | ⟨hf, _⟩
          · exact h
          refine AggFn.Picks.eq hp fun w hw => ?_
          obtain ⟨-, y, hy, rfl⟩ := Measure.mem_inputs hw
          exact ha _ hmem (AggFn.minmax_of_classPick hof hf) y (hg y hy)
        · exact Measure.allowed_eq_of_ties hs (hgt _ ht) hmv
    exact this (fun m hm => hm) hv
  unfold aggAllowed at h; unfold aggregateEval
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    rw [hvals (fun _ h => h) (fun m ht => by rw [List.isEmpty_iff.mp hg] at ht; exact ht.nil) hv]
    simp [hg]
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    obtain ⟨ks, hks, h⟩ := h
    have hrow : ∀ {ks : List Row} {out : Relation}, Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
        Forall2 (fun m v => m.Allowed (groupRows gs rows k) v) ms vs) ks out →
        out = ks.map fun k => k ++ ms.map (·.eval (groupRows gs rows k)) := by
      intro ks out h
      apply eq_map_of_forall₂
      induction h with
      | nil => exact .nil
      | cons hk _ ih =>
        obtain ⟨vs, rfl, hv⟩ := hk
        exact .cons (by rw [hvals (fun _ h => (List.mem_filter.mp h).1) (fun m ht => ht.group _) hv]; rfl) ih
    rw [hrow h]
    -- Keys alone in their classes: the representatives are the keys, once each.
    have hkl : ∀ k ∈ rows.map (groupKey gs), ∀ z, Row.canon z = Row.canon k → z = k := fun k hk' => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk'; exact hk r hr
    refine List.Perm.map _ ((hks.perm_dedup hkl).trans ?_)
    rw [distinctRows, canonReps_of_inj fun x hx y hy he => hkl y hy x he]

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
  -- The window functions over the input in any order its sort allows, a
  -- class-picking function any member of its class (D45, `WinFn.Allowed`).
  | .window r part sort fns, out => ∃ i, r.Allowed cat i ∧ ∃ s, s.Perm i ∧
      s.Pairwise (sortLe sort · · = true) ∧ ∃ o, out.Perm o ∧ windowRowsA part fns [] s o
  | .semi a b anti on, out => ∃ x y, a.Allowed cat x ∧ b.Allowed cat y ∧
      out.Perm (x.filter fun row => hasMatch on y row != anti)
  -- The input sorted, ties and a clustered key's groups in any order.
  | .orderBy r keys, out => ∃ i, r.Allowed cat i ∧ out.Perm i ∧ SortAllowed keys out
  -- One member of each class of rows, any member (D31).
  | .distinct r, out => ∃ i, r.Allowed cat i ∧ ∃ d, IsReps Row.canon i d ∧ out.Perm d
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
  | .window r part sort fns => ⟨_, eval_allowed cat r, _, List.mergeSort_perm _ _,
      List.pairwise_mergeSort (sortLe_totalPre sort).trans (sortLe_totalPre sort).total _, _, .refl _,
      windowRows_windowRowsA part fns [] _⟩
  | .orderBy r keys => ⟨_, eval_allowed cat r, List.mergeSort_perm _ _, .of_sorted <|
      List.pairwise_mergeSort (sortLe_totalPre keys).trans (sortLe_totalPre keys).total _⟩
  | .distinct r => ⟨_, eval_allowed cat r, _, canonReps_isReps Row.leRaw_rawOrder _, .refl _⟩
  | .unnest r _ => ⟨_, eval_allowed cat r, .refl _⟩
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
      SortKey.firstNulls, Value.le, Value.canonV] at h
    revert h; decide +kernel
  refine ⟨Rel.refinesBag_iff.2 fun out ho => ⟨[[.int 1], [.int 2]], ⟨_, .refl _, .swap _ _ _,
    .of_sorted (by simp [sortLe, SortKey.le, SortKey.valLe, SortKey.nullRank, lexLe, natLe,
      Value.le, Value.canonV, Value.leRaw_def, Value.leScalar])⟩, ho.trans (.swap _ _ _)⟩, fun h => hs ?_⟩
  obtain ⟨i, -, -, hsort⟩ := Rel.refines_iff.1 h _ (List.Perm.refl _)
  exact hsort

/-- **A clustered key leaves its groups in any order** (`SortAllowed`), so a
`FETCH` over it may take either row, even where its column is a key. -/
theorem Rel.fetch_clustered_open :
    let q : Rel := .fetch (.orderBy (.values 1 [[.int 1], [.int 2]])
      [{ col := 0, clustered := true }]) 0 (some 1)
    let cat : Catalog := fun _ => { arity := 0, rows := [] }
    q.Allowed cat [[.int 1]] ∧ q.Allowed cat [[.int 2]] := by
  intro q cat
  refine ⟨⟨_, ⟨_, .refl _, .refl _, .of_sorted ?_⟩, rfl⟩,
    ⟨[[.int 2], [.int 1]], ⟨_, .refl _, .swap _ _ _, fun a b => b.le a,
      ⟨Value.le_totalPre.flip, fun a b h₁ h₂ => Value.le_antisymm h₂ h₁⟩, ?_⟩, rfl⟩⟩
  · simp [sortLe, SortKey.le, SortKey.valLe, SortKey.nullRank, lexLe, natLe, SortKey.firstNulls,
      Value.le, Value.canonV, Value.leRaw_def, Value.leScalar]
  · simp [sortLeWith, SortKey.leWith, SortKey.valWith, lexLe, nullRankOf, natLe,
      SortKey.firstNulls, Value.le, Value.canonV, Value.leRaw_def, Value.leScalar]

/-- **`MODE` ordered by its argument is open over doubles**: `0.0` and `-0.0`
tie in the order (`sortLe`), and `MODE` returns the first of the values
that tie in count. -/
theorem Measure.mode_signed_zero_open :
    let m : Measure := { fn := .mode, arg := .field 0, sort := [{ col := 0 }] }
    let rows : Relation := [[.float 0], [.float FloatCode.negZero]]
    m.Allowed rows (.float 0) ∧ m.Allowed rows (.float FloatCode.negZero) := by
  intro m rows
  have hz : FloatCode.canon FloatCode.negZero = 0 := fp64.canon_negZero
  have hne : FloatCode.negZero ≠ 0 := by decide
  have h0 : fp64.canon 0 = 0 := by decide
  refine ⟨⟨rows, .refl _, fun _ => ?_, ?_⟩, ⟨rows.reverse, List.reverse_perm _, fun _ => ?_, ?_⟩⟩ <;>
    simp_all [m, rows, sortLe, SortKey.le, SortKey.valLe, SortKey.nullRank, lexLe, natLe,
      SortKey.firstNulls, Value.le, Value.canonV, Value.leRaw_def, Value.leScalar, Measure.inputs,
      Measure.kept, Expr.eval, AggFn.Allowed, AggFn.Picks, AggFn.apply, modeOf, pickFold, dedup,
      dedupN, List.count_cons, FloatCode.canon, eq_comm (a := (0 : Int))]

end Substrait
