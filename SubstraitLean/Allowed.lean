import SubstraitLean.Partition
import SubstraitLean.Profile
import SubstraitLean.StatProps
import SubstraitLean.ObsEquiv

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
* the order and grouping in which a double `SUM` or `AVG` adds its values
  (`FloatSums`); the error bound of #85 (`float-bounds/`) is a theorem about
  this set;
* the value of a statistical aggregate, within its generic properties
  (`StatProps`, `SubstraitLean/StatProps.lean`).

For a plan without these choices (`Rel.detPlan`), every allowed result is
`Rel.eval`'s up to the order of rows (`Rel.allowed_perm_eval`), so whatever
is proved of `Rel.eval`'s rows holds of every allowed result. A rewrite is
correct when it **refines** the plan (`Rel.Refines`): it may narrow the
allowed set, never widen it. A rewrite to a plan without choices whose rows
are the original's refines it (`Rel.refines_of_perm`).
-/

namespace Substrait

/-! ## Aggregates -/

/-- The doubles a `SUM` of `vs` may give: the values added one by one in any
order, or two such sums of a split of `vs` added together (a two-phase or a
tree sum). -/
inductive FloatSums : List Value → Int → Prop
  | seq {vs ws : List Value} : ws.Perm vs → FloatSums vs (floatSum ws)
  | split {vs xs ys : List Value} {a b : Int} : vs.Perm (xs ++ ys) → FloatSums xs a →
      FloatSums ys b → FloatSums vs (FloatCode.lift₂ (· + ·) a b)

/-- What an aggregate of the values `vs`, taken in this order, may give. -/
def AggFn.Allowed (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  | .fsum => if vs = [] then v = .null else ∃ c, FloatSums vs c ∧ v = .int c
  | .avg => if vs = [] then v = .null else
      ∃ c, FloatSums vs c ∧ v = .int (FloatCode.lift₂ (· / ·) c (FloatCode.ofInt vs.length))
  | .var _ _ | .cov _ | .corr => StatProps f vs v
  -- A double between the two neighbours (#53).
  | .quantile true num scale => if vs = [] then v = .null else contAllowed num scale (sortVals vs) v
  | _ => v = f.apply vs

theorem AggFn.apply_allowed (f : AggFn) (vs : List Value) : f.Allowed vs (f.apply vs) := by
  cases f
  case fsum | avg =>
    cases vs with
    | nil => simp [Allowed, apply]
    | cons v vs =>
      simp only [Allowed, reduceCtorEq, ite_false]
      exact ⟨_, .seq (.refl _), rfl⟩
  case var | cov | corr => simp only [Allowed]; exact StatProps.apply _ vs
  case quantile cont num scale =>
    cases cont
    · rfl
    · cases vs with
      | nil => rfl
      | cons v vs => simp only [Allowed, reduceCtorEq, ite_false]; exact contValue_allowed _ _ _
  all_goals rfl

/-- An aggregate that combines in two phases is a function of its values. -/
theorem AggFn.allowed_iff {f : AggFn} (hf : f.decomposable = true) (vs : List Value) (v : Value) :
    f.Allowed vs v ↔ v = f.apply vs := by
  cases f <;> simp_all [decomposable, Allowed]

/-- What a measure over a group's `rows` may give: its aggregate of the rows
in some order, sorted by the measure's own order where it takes one. -/
def Measure.Allowed (m : Measure) (rows : Relation) (v : Value) : Prop :=
  ∃ s, s.Perm rows ∧ (m.fn.sorts = true → s.Pairwise (sortLe m.sort · · = true)) ∧
    m.fn.Allowed (m.inputs s) v

theorem Measure.eval_sorts {m : Measure} (h : m.fn.sorts = true) (rows : Relation) :
    m.eval rows = m.fn.apply (m.inputs (rows.mergeSort (sortLe m.sort))) := by
  cases hf : m.fn <;> simp [Measure.eval, hf, AggFn.sorts] at h ⊢

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
  rw [hv, ← Measure.eval_eq (AggFn.ne_collect hm), Measure.eval_perm hm hs]

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

/-! ## Plans without choices -/

/-- Does `r` leave the engine no choice but the order of its rows? No
`FETCH` (which rows come first), each window's ties broken alike
(`Rel.windowsTotal`'s checks), and aggregates that are functions of their
values (`Measure.orderFree`: `COUNT`, integer `SUM`, `MIN`, `MAX`). -/
def Rel.detPlan (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.detPlan cat A F K
  | .fetch _ _ _ => false
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
      a.detPlan cat A F K && b.detPlan cat A F K
  | .window r part sort fns =>
      r.detPlan cat A F K && ((r.keys cat A F K).any (fun k => k.all (· ∈ part ++ sort.map (·.col))) ||
        fns.all (WinFn.tieFree sort) || (List.range (r.arity cat)).all (· ∈ part))
  | .aggregate r _ ms => r.detPlan cat A F K && ms.all (·.orderFree)

theorem crossRows_perm {xs xs' ys ys' : Relation} (hx : xs.Perm xs') (hy : ys.Perm ys') :
    (crossRows xs ys).Perm (crossRows xs' ys') :=
  (crossRows_perm_right hy).trans (hx.flatMap_right _)

/-- **A plan without choices allows only `Rel.eval`'s rows**, in any order. -/
theorem Rel.allowed_perm_eval {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → r.detPlan cat A F K = true → ∀ {out : Relation},
      r.Allowed cat out → out.Perm (r.eval cat)
  | .read _, _, _, _, h | .values _ _, _, _, _, h => h
  | .filter r _, hwf, hd, _, ⟨i, hi, rfl⟩ =>
    (allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).filter _
  | .project r _, hwf, hd, _, ⟨i, hi, rfl⟩ =>
    (allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).map _
  | .emit r _, hwf, hd, _, ⟨i, hi, rfl⟩ =>
    (allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).map _
  | .cross a b, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    exact h.trans (crossRows_perm (allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx)
      (allowed_perm_eval hcat hA hF hK hwf.2 hd.2 hy))
  | .join a b .inner _, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    exact h.trans ((crossRows_perm (allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx)
      (allowed_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy)).filter _)
  | .join a b .left _, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    have hx' := allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx
    have hy' := allowed_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy
    exact h.trans ((flatMap_perm_congr fun z _ => leftJoinRow_perm z hy').trans
      (hx'.flatMap_right _))
  | .fetch _ _ _, _, hd, _, _ => by simp [detPlan] at hd
  | .unionAll a b, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    exact h.trans ((allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx).append
      (allowed_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy))
  | .window r part sort fns, hwf, hd, _, ⟨i, hi, s, hs, hsort, h⟩ => by
    simp only [detPlan, Bool.and_eq_true, Bool.or_eq_true] at hd
    have hp : s.Perm (r.eval cat) := hs.trans (allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hi)
    refine h.trans ?_
    rcases hd.2 with (hk | hf) | hc
    · obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp hk
      simp only [List.all_eq_true, decide_eq_true_eq] at hsub
      exact window_tiebreak ((keys_sound hcat hA hF hK hwf.1 k hk).superset hsub) hp hsort
    · exact window_tieFree hf hp hsort
    · simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      exact Substrait.window_allColumns (Rel.eval_arity hcat hwf.1) hc hp
  | .semi a b _ on, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    have hx' := allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx
    have hy' := allowed_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy
    refine h.trans ?_
    rw [List.filter_congr fun z _ => by rw [hasMatch_perm z hy']]
    exact hx'.filter _
  | .orderBy r _, hwf, hd, _, ⟨i, hi, h, _⟩ =>
    h.trans ((allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).trans
      (List.mergeSort_perm _ _).symm)
  | .distinct r, hwf, hd, _, ⟨i, hi, h⟩ => by
    have hp := allowed_perm_eval hcat hA hF hK (r := r) hwf hd hi
    exact h.trans (dedup_perm_of_mem fun y => hp.mem_iff)
  | .aggregate r gs ms, hwf, hd, _, ⟨i, hi, o, h, ho⟩ => by
    simp only [detPlan, Bool.and_eq_true, List.all_eq_true] at hd
    have hp := allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd.1 hi
    rw [aggAllowed_eq hd.2 ho] at h
    exact h.trans (aggregateEval_perm hd.2 hp)
  | .unnest r _, hwf, hd, _, ⟨i, hi, h⟩ =>
    h.trans ((allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).flatMap_right _)

/-! ## Refinement -/

/-- **`q` refines `r`**: every result `q` allows, `r` allows too, up to the
order of rows. A correct rewrite refines the plan it rewrites: it may narrow
the set of allowed results, never widen it. -/
def Rel.Refines (cat : Catalog) (q r : Rel) : Prop :=
  ∀ out, q.Allowed cat out → ∃ out', r.Allowed cat out' ∧ out.Perm out'

theorem Rel.Refines.refl (cat : Catalog) (r : Rel) : r.Refines cat r :=
  fun out h => ⟨out, h, .refl _⟩

/-- A rewrite to a plan without choices whose rows are the original's
refines it, whatever choices the original leaves. -/
theorem Rel.refines_of_perm {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {q r : Rel} (hwf : q.WF cat)
    (hd : q.detPlan cat A F K = true) (h : (q.eval cat).Perm (r.eval cat)) : q.Refines cat r :=
  fun _ hq => ⟨r.eval cat, r.eval_allowed cat,
    (allowed_perm_eval hcat hA hF hK hwf hd hq).trans h⟩

/-! ## Engines

The theorems about engines conclude that an engine computes `Rel.eval`'s rows
(or raises); so it returns an allowed result. -/

/-- Guard elimination: the plan run without its row-level checks returns an
allowed result. -/
theorem Rel.guardFree_allowed {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true)
    {I : Impl} (hI : I.Faithful) : r.Allowed cat (r.evalI I cat) := by
  rw [Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm hI]; exact r.eval_allowed cat

end Substrait
