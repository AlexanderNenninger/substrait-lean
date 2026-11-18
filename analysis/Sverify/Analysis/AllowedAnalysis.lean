import Sverify.Core.AllowedNear
import Sverify.Analysis.Partition
import Sverify.Analysis.Guards

/-!
# What the analysis proves of the allowed results

`Rel.Allowed` (`core/Sverify/Core/Allowed.lean`) is the reference's relation;
this module states what the analysis proves of it. For a plan without
choices (`Rel.detPlan`, decided from the abstract values, facts and keys of
`analysis/Sverify/Analysis/Contracts.lean`), every allowed result is `Rel.eval`'s up to
the order of rows (`Rel.allowed_perm_eval`), so a rewrite to such a plan
with the original's rows refines it up to the order of rows
(`Rel.refines_of_perm`); and a plan run without its row-level checks returns
an allowed result (`Rel.guardFree_allowed`). A row cap keeps every order a
plan allows (`Rel.orderAllowed_capReads`), for the checker's capped reads
(`Rel.capReads`). A contract proved by the checker holds of every allowed
result, up to its observation (`contract_sound_allowed`, over
`core/Sverify/Core/AllowedNear.lean`'s closeness).
-/

namespace Substrait

/-! ## Plans without choices -/

variable [Boxes.Ambient]
/-- Does the order of the measure `m` (of an aggregate over `r` grouped by
`gs`) fix its inputs: do rows that tie in it agree on its argument? Its
argument is a sort column without doubles, or the group's and the sort's
columns contain a key (`Measure.keyedIn`). -/
def Measure.tiesFixed (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (gs : List Expr) (m : Measure) : Bool :=
  (m.sort.any (m.arg == .field ·.col) && (m.arg.abs (r.aeval cat A F .none)).noDoubles) ||
    m.keyedIn cat A F K r gs

/-- Is the measure `m` (of an aggregate over `r` grouped by `gs`) a function
of its group's rows: order-free, or sorting them in an order that fixes its
inputs? -/
def Measure.detIn (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (gs : List Expr) (m : Measure) : Bool :=
  m.orderFree || (m.fn.sorts && m.tiesFixed cat A F K r gs)

/-- Does the measure `m` over `r` pick one value: not a function that picks
any member of a class (`AggFn.classPick`: `MIN`, `MAX`, `QUANTILE_DISC`; D31,
D45), or over an argument without doubles? -/
def Measure.pickFixed (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (r : Rel)
    (m : Measure) : Bool :=
  !m.fn.classPick || (m.arg.abs (r.aeval cat A F .none)).noDoubles

/-- Does the window function `f` over `r` pick one value: a windowed
aggregate as `Measure.pickFixed` checks it (D45), every other function. -/
def WinFn.pickFixed (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (r : Rel) :
    WinFn → Bool
  | .agg m _ _ => m.pickFixed cat A F r
  | _ => true

/-- Does the window over `r` give one result for every order of its ties: do
its partition and sort columns contain a key of `r` (`window_tiebreak`), are
its functions tie-free (`window_tieFree`), or does its partition cover every
column, without doubles (`Rel.window_allColumns`)? -/
def Rel.windowDetAt (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) (part : List Nat) (sort : List SortKey)
    (fns : List WinFn) : Bool :=
  (r.keys cat A F K).any (fun k => k.all (· ∈ part ++ sort.map (·.col))) ||
    fns.all (WinFn.tieFree sort) ||
    ((List.range (r.arity cat)).all (· ∈ part) && (r.aeval cat A F .none).all AVal.noDoubles)

/-- Does `r` leave the engine no choice but the order of its rows? A `FETCH`
only over an `ORDER BY` whose columns contain a key and none clustered
(`Rel.fetchTotalAt`), each window's ties broken alike (`Rel.windowsTotal`'s
checks), and aggregates whose measures are functions of their values
(`Measure.orderFree`: `COUNT`, `SUM`, `AVG` of integers and of doubles
(D25), `MIN`, `MAX`) or sort their rows in an order that fixes their inputs
(`Measure.tiesFixed`). -/
def Rel.detPlan (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _
  | .unnest r _ => r.detPlan cat A F K
  -- `DISTINCT` keeps any member of a class of rows (D31): none to choose
  -- without doubles.
  | .distinct r => r.detPlan cat A F K && (r.aeval cat A F .none).all AVal.noDoubles
  | .fetch (.orderBy i keys) _ _ => i.detPlan cat A F K && Rel.fetchTotalAt cat A F K i keys
  | .fetch _ _ _ => false
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
      a.detPlan cat A F K && b.detPlan cat A F K
  -- A windowed `MIN`, `MAX` or `QUANTILE_DISC` keeps any member of a class
  -- (D45): none to choose without doubles.
  | .window r part sort fns => r.detPlan cat A F K && Rel.windowDetAt cat A F K r part sort fns &&
      fns.all (WinFn.pickFixed cat A F r)
  -- Keys and `MIN`/`MAX` keep any member of a class: none to choose without
  -- doubles.
  | .aggregate r gs ms => r.detPlan cat A F K &&
      ms.all (Measure.detIn cat A F K r gs) &&
      gs.all (fun g => (g.abs (r.aeval cat A F .none)).noDoubles) &&
      ms.all (Measure.pickFixed cat A F r)

omit [Boxes.Ambient] in
theorem crossRows_perm {xs xs' ys ys' : Relation} (hx : xs.Perm xs') (hy : ys.Perm ys') :
    (crossRows xs ys).Perm (crossRows xs' ys') :=
  (crossRows_perm_right hy).trans (hx.flatMap_right _)

/-- A measure whose order fixes its inputs: rows of one group that tie in it
agree on its argument. -/
theorem Measure.tiesAgreeIn_of_tiesFixed {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {r : Rel} (hwf : r.WF cat) {gs : List Expr}
    {m : Measure} (h : m.tiesFixed cat A F K r gs = true) {rows : Relation}
    (hp : rows.Perm (r.eval cat)) : m.TiesAgreeIn gs rows := by
  intro x hx y hy hg hxy hyx
  have hc := List.map_inj_left.mp (sortLe_antisymm hxy hyx)
  simp only [Measure.tiesFixed, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hs, hnd⟩ | hk
  · obtain ⟨kk, hkk, he⟩ := List.any_eq_true.mp hs
    have harg : m.arg = .field kk.col := by simpa using he
    have hlone : (m.arg.eval y).Lone := AVal.lone_of_noDoubles hnd (Expr.abs_sound
      (Rel.aeval_sound (sz := false) hcat hA hF (WindowKeys.none_soundAll cat) hwf
        (fun h => by cases h) y (hp.mem_iff.mp hy)) m.arg)
    exact hlone _ (by rw [harg]; simpa [Expr.eval] using hc kk hkk)
  · obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp hk
    have hK : KeyOn k rows := (Rel.keys_sound hcat hA hF hK hwf k hk).perm hp.symm fun h => Ne.symm h
    rw [KeyOn.eq_of_keyOf hK hx hy ?_]
    simp only [keyOf, List.map_inj_left]
    intro c hc'
    simp only [List.all_eq_true, Bool.or_eq_true] at hsub
    rcases hsub c hc' with hgc | hsc
    · have hgc : Expr.field c ∈ gs := by simpa using hgc
      have := List.map_inj_left.mp (by simpa [groupKey, Row.canon, List.map_map] using hg)
        (Expr.field c) hgc
      simpa [Expr.eval] using this
    · obtain ⟨kk, hkk, he⟩ := List.any_eq_true.mp hsc
      have he : kk.col = c := by simpa using he
      rw [← he]; exact hc kk hkk

/-- **A window whose ties fall alike gives `windowEval`'s rows** for every
sorted order of its input (`Rel.windowDetAt`). -/
theorem Rel.window_perm_of_detAt {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {r : Rel} {part : List Nat} {sort : List SortKey}
    {fns : List WinFn} (hwf : r.WF cat) (hd : Rel.windowDetAt cat A F K r part sort fns = true)
    {s : Relation} (hp : s.Perm (r.eval cat)) (hsort : s.Pairwise (sortLe sort · · = true)) :
    (windowRows part fns [] s).Perm ((Rel.window r part sort fns).eval cat) := by
  simp only [windowDetAt, Bool.or_eq_true, Bool.and_eq_true] at hd
  rcases hd with (hk | hf) | hc
  · obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp hk
    simp only [List.all_eq_true, decide_eq_true_eq] at hsub
    exact window_tiebreak ((keys_sound hcat hA hF hK hwf k hk).superset hsub) hp hsort
  · exact window_tieFree hf hp hsort
  · obtain ⟨hc, hnd⟩ := hc
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
    refine Substrait.window_allColumns (Rel.eval_arity hcat hwf) hc (fun x hx => ?_) hp
    exact Row.canon_of_env (Rel.aeval_sound (sz := false) hcat hA hF (WindowKeys.none_soundAll cat) hwf
      (fun h => by cases h) x hx) (by simpa using hnd)
      (by rw [Rel.aeval_length hwf, Rel.eval_arity hcat hwf x hx])

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
  | .fetch (.orderBy i keys) _ cnt, hwf, hd, _, ⟨o, ⟨i', hi', hpo, cmp, _, hsort⟩, he⟩ => by
    simp only [detPlan, Rel.fetchTotalAt, Bool.and_eq_true] at hd
    obtain ⟨hdi, hk, hcl⟩ := hd
    have hp : o.Perm (i.eval cat) := hpo.trans (allowed_perm_eval hcat hA hF hK hwf.1 hdi hi')
    rw [sortLeWith_unclustered cmp hcl] at hsort
    obtain ⟨k, hk, hsub⟩ := List.any_eq_true.mp hk
    have hko : KeyOn (keys.map (·.col)) o :=
      ((keys_sound hcat hA hF hK hwf.1 k hk).superset fun c hc => by
        obtain ⟨kk, hkk, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hsub c hc)
        exact List.mem_map.mpr ⟨kk, hkk, by simpa using he⟩).perm hp.symm fun h => Ne.symm h
    have ho : o = (i.eval cat).mergeSort (sortLe keys) :=
      eq_of_perm_of_pairwise (hp.trans (List.mergeSort_perm _ _).symm) hsort (mergeSort_sorted _ _)
        fun x hx y hy hxy hyx => KeyOn.eq_of_keyOf hko hx hy (by
          simpa [keyOf, Function.comp_def] using sortLe_antisymm hxy hyx)
    subst ho he
    cases cnt <;> exact .refl _
  | .fetch (.read _) _ _, _, hd, _, _ | .fetch (.values _ _) _ _, _, hd, _, _
  | .fetch (.filter _ _) _ _, _, hd, _, _ | .fetch (.project _ _) _ _, _, hd, _, _
  | .fetch (.emit _ _) _ _, _, hd, _, _ | .fetch (.cross _ _) _ _, _, hd, _, _
  | .fetch (.join _ _ _ _) _ _, _, hd, _, _ | .fetch (.fetch _ _ _) _ _, _, hd, _, _
  | .fetch (.unionAll _ _) _ _, _, hd, _, _ | .fetch (.window _ _ _ _) _ _, _, hd, _, _
  | .fetch (.semi _ _ _ _) _ _, _, hd, _, _ | .fetch (.distinct _) _ _, _, hd, _, _
  | .fetch (.aggregate _ _ _) _ _, _, hd, _, _ | .fetch (.unnest _ _) _ _, _, hd, _, _ => by
    simp [detPlan] at hd
  | .unionAll a b, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    exact h.trans ((allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hx).append
      (allowed_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy))
  | .window r part sort fns, hwf, hd, _, ⟨i, hi, s, hs, hsort, o, h, ho⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    obtain ⟨⟨hdr, hd⟩, hpf⟩ := hd
    have hp : s.Perm (r.eval cat) := hs.trans (allowed_perm_eval hcat hA hF hK hwf.1 hdr hi)
    -- No class to pick from: the reference allows `windowRows` alone.
    have hl : WinFn.ClassArgsLone fns ([] ++ s) := fun f hf m _ _ he hc x hx => by
      have := List.all_eq_true.mp hpf f hf
      subst he
      simp only [WinFn.pickFixed, Measure.pickFixed, hc, Bool.not_true, Bool.false_or] at this
      exact AVal.lone_of_noDoubles this (Expr.abs_sound (Rel.aeval_sound (sz := false) hcat hA hF
        (WindowKeys.none_soundAll cat) hwf.1 (fun h => by cases h) x
        (hp.mem_iff.mp (by simpa using hx))) m.arg)
    rw [windowRowsA_eq hl ho] at h
    exact h.trans (Rel.window_perm_of_detAt hcat hA hF hK hwf.1 hd hp hsort)
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
  | .distinct r, hwf, hd, _, ⟨i, hi, d, hdr, h⟩ => by
    simp only [detPlan, Bool.and_eq_true] at hd
    have hp := allowed_perm_eval hcat hA hF hK (r := r) hwf hd.1 hi
    -- Rows without doubles are alone in their classes.
    have hlone : ∀ x ∈ r.eval cat, x.Lone := fun x hx =>
      Row.lone_of_env (Rel.aeval_sound (sz := false) (r := r) hcat hA hF (WindowKeys.none_soundAll cat) hwf
        (fun h => by cases h) x hx) hd.2
        (by rw [Rel.aeval_length (r := r) hwf, Rel.eval_arity hcat (r := r) hwf x hx])
    refine h.trans ((hdr.perm_dedup fun x hx => hlone x (hp.mem_iff.mp hx)).trans ?_)
    simp only [eval, distinctRows]
    rw [canonReps_of_inj fun x hx y hy he => hlone y hy x he]
    exact dedup_perm_of_mem fun _ => hp.mem_iff
  | .aggregate r gs ms, hwf, hd, _, ⟨i, hi, o, h, ho⟩ => by
    simp only [detPlan, Bool.and_eq_true, List.all_eq_true] at hd
    obtain ⟨⟨⟨hd1, hof⟩, hgs⟩, hmm⟩ := hd
    have hp := allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd1 hi
    have hms : ∀ {rows : Relation}, rows.Perm (r.eval cat) → ∀ m ∈ ms,
        m.orderFree = true ∨ (m.fn.sorts = true ∧ m.TiesAgreeIn gs rows) := fun hrows m hm => by
      have := hof m hm
      simp only [Measure.detIn, Bool.or_eq_true, Bool.and_eq_true] at this
      exact this.imp_right fun h => ⟨h.1, Measure.tiesAgreeIn_of_tiesFixed hcat hA hF hK hwf.1 h.2 hrows⟩
    have henv : ∀ x ∈ i, EnvMem (r.aeval cat A F .none) x := fun x hx =>
      Rel.aeval_sound (sz := false) hcat hA hF (WindowKeys.none_soundAll cat) hwf.1
        (fun h => by cases h) x (hp.mem_iff.mp hx)
    have hk : ∀ x ∈ i, (groupKey gs x).Lone := fun x hx => by
      refine Row.lone_of_forall fun v hv => ?_
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
      exact AVal.lone_of_noDoubles (hgs g hg) (Expr.abs_sound (henv x hx) g)
    have ha : ∀ m ∈ ms, (m.fn = .min ∨ m.fn = .max) → ∀ x ∈ i,
        (m.arg.eval x).Lone := fun m hm hf x hx => by
      have := hmm m hm
      rcases hf with hf | hf <;>
        simp only [Measure.pickFixed, hf, AggFn.classPick, Bool.not_true, Bool.false_or] at this <;>
        exact AVal.lone_of_noDoubles this (Expr.abs_sound (henv x hx) m.arg)
    exact h.trans ((aggAllowed_eq (hms hp) hk ha ho).trans (aggregateEval_perm_of (hms .rfl) hp))
  | .unnest r _, hwf, hd, _, ⟨i, hi, h⟩ =>
    h.trans ((allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hd hi).flatMap_right _)

/-! ## Determined up to the class (D48)

`Rel.detPlan` is the exact level: every result the reference allows is
`Rel.eval`'s up to row order. `Rel.detClass` is the class level: up to row
order and the member of each class of D31 (`Row.canon`). A place that only
picks a member of a class (a `GROUP BY` or `DISTINCT` key over doubles, `MIN`,
`MAX`, `QUANTILE_DISC`, D45's windows) leaves a plan determined at the class
level. An operator above a pick must read its input up to the class; stage 1
admits only those with a congruence lemma: `emit`, `ORDER BY`, `DISTINCT`,
`UNION ALL`, a filter whose condition is `Expr.canonSafe`, and a projection of
columns and literals (`Expr.classCongr`). Any other operator needs inputs
determined exactly. -/

/-- Does the expression read a row only up to the class of each value: a
column or a literal? -/
def Expr.classCongr : Expr → Bool
  | .field _ | .lit _ => true
  | _ => false

/-- **Does `r` leave the engine no choice but the order of its rows and the
member of a class** (D31, D48)? `Rel.detPlan` without its three class guards
(`DISTINCT`'s and the `GROUP BY` keys' `noDoubles`, `Measure.pickFixed` and
`WinFn.pickFixed`), every tie condition kept, and above a class-level input
only operators that read it up to the class. -/
def Rel.detClass (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r c => r.detClass cat A F K && (r.detPlan cat A F K || c.canonSafe)
  | .project r es => r.detClass cat A F K && (r.detPlan cat A F K || es.all Expr.classCongr)
  | .emit r _ | .orderBy r _ | .distinct r => r.detClass cat A F K
  | .unionAll a b => a.detClass cat A F K && b.detClass cat A F K
  | .window r part sort fns => r.detPlan cat A F K && Rel.windowDetAt cat A F K r part sort fns
  | .aggregate r gs ms => r.detPlan cat A F K && ms.all (Measure.detIn cat A F K r gs)
  | r@(.fetch _ _ _) | r@(.cross _ _) | r@(.join _ _ _ _) | r@(.semi _ _ _ _)
  | r@(.unnest _ _) => r.detPlan cat A F K

/-- The exact level implies the class level. -/
theorem Rel.detClass_of_detPlan {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
    {K : String → List (List Nat)} :
    ∀ {r : Rel}, r.detPlan cat A F K = true → r.detClass cat A F K = true
  | .read _, _ | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h => by
    simp only [detPlan] at h
    simp [detClass, detClass_of_detPlan (r := r) h, h]
  | .emit r _, h | .orderBy r _, h => by
    simp only [detPlan] at h
    simp only [detClass]; exact detClass_of_detPlan (r := r) h
  | .distinct r, h => by
    simp only [detPlan, Bool.and_eq_true] at h
    simp only [detClass]; exact detClass_of_detPlan (r := r) h.1
  | .unionAll a b, h => by
    simp only [detPlan, Bool.and_eq_true] at h
    simp [detClass, detClass_of_detPlan (r := a) h.1, detClass_of_detPlan (r := b) h.2]
  | .window r _ _ _, h => by
    simp only [detPlan, Bool.and_eq_true] at h
    simp [detClass, h.1.1, h.1.2]
  | .aggregate r _ _, h => by
    simp only [detPlan, Bool.and_eq_true] at h
    simp [detClass, h.1.1.1, h.1.1.2]
  | .fetch _ _ _, h | .cross _ _, h | .join _ _ _ _, h | .semi _ _ _ _, h | .unnest _ _, h => by
    simpa [detClass] using h

omit [Boxes.Ambient] in
/-- **A map that reads its argument up to `c` carries a permutation up to
`c`.** -/
theorem perm_filterMap_of_perm_map {α β γ : Type} [DecidableEq α] {c : α → β}
    {F : α → Option γ} (hF : ∀ x y, c x = c y → F x = F y) :
    ∀ {l l' : List α}, (l.map c).Perm (l'.map c) → (l.filterMap F).Perm (l'.filterMap F)
  | [], l', h => by
    have : l' = [] := List.map_eq_nil_iff.mp (List.Perm.nil_eq h).symm
    subst this; exact .refl _
  | x :: l, l', h => by
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (h.subset List.mem_cons_self)
    have hl' := List.perm_cons_erase hy
    have h2 : (c x :: l.map c).Perm (c x :: (l'.erase y).map c) := by
      have := h.trans (hl'.map c); simpa only [List.map_cons, hyx] using this
    have ih := perm_filterMap_of_perm_map hF h2.cons_inv
    refine List.Perm.trans ?_ (hl'.filterMap F).symm
    rw [List.filterMap_cons, List.filterMap_cons, hF x y hyx.symm]
    cases F y with
    | none => exact ih
    | some b => exact ih.cons b

omit [Boxes.Ambient] in
theorem perm_map_of_perm_map {α β γ : Type} [DecidableEq α] {c : α → β} {F : α → γ}
    (hF : ∀ x y, c x = c y → F x = F y) {l l' : List α} (h : (l.map c).Perm (l'.map c)) :
    (l.map F).Perm (l'.map F) := by
  have := perm_filterMap_of_perm_map (F := fun x => some (F x)) (fun x y hxy => by rw [hF x y hxy]) h
  simpa [List.filterMap_eq_map] using this

omit [Boxes.Ambient] in
theorem filter_map_eq_filterMap {α γ : Type} (p : α → Bool) (f : α → γ) (l : List α) :
    (l.filter p).map f = l.filterMap fun x => if p x then some (f x) else none := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases hp : p x <;> simp [hp, ih]

omit [Boxes.Ambient] in
/-- Representatives of lists equal up to `c` are equal up to `c`. -/
theorem IsReps.map_subset {α : Type} {c : α → α} {l l' reps reps' : List α}
    (h : IsReps c l reps) (h' : IsReps c l' reps') (hs : ∀ z ∈ l.map c, z ∈ l'.map c) :
    ∀ z ∈ reps.map c, z ∈ reps'.map c := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  obtain ⟨y, hy, he⟩ := h.class_mem hx
  obtain ⟨y', hy', he'⟩ := List.mem_map.mp (hs _ (List.mem_map_of_mem hy))
  obtain ⟨x', hx', he''⟩ := h'.2.2 y' hy'
  exact List.mem_map.mpr ⟨x', hx', by rw [he'', he', he]⟩

omit [Boxes.Ambient] in
theorem IsReps.map_perm {α : Type} {c : α → α} {l l' reps reps' : List α}
    (h : IsReps c l reps) (h' : IsReps c l' reps') (hp : (l.map c).Perm (l'.map c)) :
    (reps.map c).Perm (reps'.map c) :=
  (List.perm_ext_iff_of_nodup (List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr h.1))
    (List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr h'.1))).mpr fun z =>
    ⟨h.map_subset h' (fun _ hz => hp.subset hz) z, h'.map_subset h (fun _ hz => hp.symm.subset hz) z⟩

omit [Boxes.Ambient] in
theorem Row.canon_append (a b : Row) : (a ++ b).canon = a.canon ++ b.canon := by
  simp [Row.canon]

/-- **An allowed measure is `Measure.eval`'s up to the class of its value.** -/
theorem Measure.allowed_canon {m : Measure} {grp : Relation}
    (hm : m.orderFree = true ∨ (m.fn.sorts = true ∧ m.TiesAgree grp)) {v : Value}
    (h : m.Allowed grp v) : v.canonV = (m.eval grp).canonV := by
  rcases hm with hof | ⟨hs, ht⟩
  · rw [Measure.eval_eq (AggFn.ne_collect_of_orderFree hof)]
    exact (Measure.allowed_picks hof h).canon
  · rw [Measure.allowed_eq_of_ties hs ht h]

/-- **An aggregate allows its rows up to the classes**: `aggAllowed_eq`
without its `Lone` hypotheses, the keys and the measures' values up to their
classes. -/
theorem aggAllowed_canon {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (hms : ∀ m ∈ ms, m.orderFree = true ∨ (m.fn.sorts = true ∧ m.TiesAgreeIn gs rows))
    (h : aggAllowed gs ms rows out) :
    (out.map Row.canon).Perm ((aggregateEval gs ms rows).map Row.canon) := by
  have hvals : ∀ {grp : Relation}, (∀ m : Measure, m.TiesAgreeIn gs rows → m.TiesAgree grp) →
      ∀ {vs : List Value}, Forall2 (fun m v => m.Allowed grp v) ms vs →
        vs.map Value.canonV = (ms.map (·.eval grp)).map Value.canonV := by
    intro grp hg vs hv
    have : ∀ {ms' : List Measure}, (∀ m ∈ ms', m ∈ ms) → ∀ {vs : List Value},
        Forall2 (fun m v => m.Allowed grp v) ms' vs →
          vs.map Value.canonV = (ms'.map (·.eval grp)).map Value.canonV := by
      intro ms' hsub vs hv
      induction hv with
      | nil => rfl
      | cons hmv _ ih =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨Measure.allowed_canon ((hms _ (hsub _ List.mem_cons_self)).imp_right
          fun ⟨hs, ht⟩ => ⟨hs, hg _ ht⟩) hmv, ih fun m hm => hsub m (List.mem_cons_of_mem _ hm)⟩
    exact this (fun m hm => hm) hv
  unfold aggAllowed at h; unfold aggregateEval
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    simp only [hg, ite_true, List.map_cons, List.map_nil, Row.canon]
    rw [hvals (fun m ht => by rw [List.isEmpty_iff.mp hg] at ht; exact ht.nil) hv]
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    obtain ⟨ks, hks, h⟩ := h
    let G : Row → Row := fun k => Row.canon (k ++ ms.map (·.eval (groupRows gs rows k)))
    have hgr : ∀ k k' : Row, k.canon = k'.canon → groupRows gs rows k = groupRows gs rows k' :=
      fun k k' he => by simp only [groupRows, he]
    have hG : ∀ k k' : Row, k.canon = k'.canon → G k = G k' := fun k k' he => by
      simp only [G, Row.canon_append, hgr k k' he]; rw [he]
    have hout : ∀ {ks : List Row} {out : Relation}, Forall2 (fun k row => ∃ vs, row = k ++ vs ∧
        Forall2 (fun m v => m.Allowed (groupRows gs rows k) v) ms vs) ks out →
        out.map Row.canon = ks.map G := by
      intro ks out h
      induction h with
      | nil => rfl
      | cons hk _ ih =>
        obtain ⟨vs, rfl, hv⟩ := hk
        simp only [List.map_cons, ih, G, Row.canon_append, List.cons.injEq, and_true]
        congr 1
        exact hvals (fun m ht => ht.group _) hv
    rw [hout h, List.map_map]
    exact perm_map_of_perm_map (c := Row.canon) hG
      (hks.map_perm (canonReps_isReps Row.leRaw_rawOrder _) (.refl _))

/-- **A plan determined up to the class allows only `Rel.eval`'s rows up to
row order and the member of each class** (D48). -/
theorem Rel.allowed_canon_perm_eval {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → r.detClass cat A F K = true → ∀ {out : Relation},
      r.Allowed cat out → (out.map Row.canon).Perm ((r.eval cat).map Row.canon)
  | .read _, _, _, _, h | .values _ _, _, _, _, h => h.map _
  | .filter r c, hwf, hd, _, ⟨i, hi, rfl⟩ => by
    simp only [detClass, Bool.and_eq_true, Bool.or_eq_true] at hd
    rcases hd.2 with hdp | hcs
    · exact ((allowed_perm_eval hcat hA hF hK hwf.1 hdp hi).filter _).map _
    · have ih := allowed_canon_perm_eval hcat hA hF hK hwf.1 hd.1 hi
      simp only [Rel.eval, filter_map_eq_filterMap]
      exact perm_filterMap_of_perm_map (c := Row.canon) (fun x y hxy => by
        rw [Expr.canonSafe_eval hxy c hcs, hxy]) ih
  | .project r es, hwf, hd, _, ⟨i, hi, rfl⟩ => by
    simp only [detClass, Bool.and_eq_true, Bool.or_eq_true] at hd
    rcases hd.2 with hdp | hcs
    · exact ((allowed_perm_eval hcat hA hF hK hwf.1 hdp hi).map _).map _
    · have ih := allowed_canon_perm_eval hcat hA hF hK hwf.1 hd.1 hi
      simp only [Rel.eval, List.map_map]
      refine perm_map_of_perm_map (c := Row.canon) (fun x y hxy => ?_) ih
      simp only [Function.comp_apply, Row.canon_append]
      rw [hxy]; congr 1
      simp only [Row.canon, List.map_map]
      refine List.map_congr_left fun e he => ?_
      have hc := List.all_eq_true.mp hcs e he
      cases e with
      | field j => exact getD_canonV_of_canon hxy j
      | lit v => rfl
      | _ => simp [Expr.classCongr] at hc
  | .emit r m, hwf, hd, _, ⟨i, hi, rfl⟩ => by
    simp only [detClass] at hd
    have ih := allowed_canon_perm_eval hcat hA hF hK hwf.1 hd hi
    simp only [Rel.eval, List.map_map]
    refine perm_map_of_perm_map (c := Row.canon) (fun x y hxy => ?_) ih
    simp only [Function.comp, Row.canon, List.map_map]
    exact List.map_congr_left fun j _ => getD_canonV_of_canon hxy j
  | .orderBy r keys, hwf, hd, _, ⟨i, hi, hp, _⟩ => by
    simp only [detClass] at hd
    exact (hp.map _).trans ((allowed_canon_perm_eval hcat hA hF hK hwf.1 hd hi).trans
      ((List.mergeSort_perm _ _).symm.map _))
  | .distinct r, hwf, hd, _, ⟨i, hi, d, hd', hp⟩ => by
    simp only [detClass] at hd
    exact (hp.map _).trans (hd'.map_perm (canonReps_isReps Row.leRaw_rawOrder _)
      (allowed_canon_perm_eval hcat hA hF hK (r := r) hwf hd hi))
  | .unionAll a b, hwf, hd, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [detClass, Bool.and_eq_true] at hd
    simp only [Rel.eval]
    exact (h.map _).trans (by
      rw [List.map_append, List.map_append]
      exact (allowed_canon_perm_eval hcat hA hF hK hwf.1 hd.1 hx).append
        (allowed_canon_perm_eval hcat hA hF hK hwf.2.1 hd.2 hy))
  | .window r part sort fns, hwf, hd, _, ⟨i, hi, s, hs, hsort, o, h, ho⟩ => by
    simp only [detClass, Bool.and_eq_true] at hd
    have hp : s.Perm (r.eval cat) := hs.trans (allowed_perm_eval hcat hA hF hK hwf.1 hd.1 hi)
    refine (h.map _).trans ?_
    rw [windowRowsA_map_canon ho Row.canon fun _ _ h => h]
    exact (Rel.window_perm_of_detAt hcat hA hF hK hwf.1 hd.2 hp hsort).map _
  | .aggregate r gs ms, hwf, hd, _, ⟨i, hi, o, h, ho⟩ => by
    simp only [detClass, Bool.and_eq_true, List.all_eq_true] at hd
    obtain ⟨hdr, hof⟩ := hd
    have hp := allowed_perm_eval hcat hA hF hK (r := r) hwf.1 hdr hi
    have hms : ∀ {rows : Relation}, rows.Perm (r.eval cat) → ∀ m ∈ ms,
        m.orderFree = true ∨ (m.fn.sorts = true ∧ m.TiesAgreeIn gs rows) := fun hrows m hm => by
      have := hof m hm
      simp only [Measure.detIn, Bool.or_eq_true, Bool.and_eq_true] at this
      exact this.imp_right fun h => ⟨h.1, Measure.tiesAgreeIn_of_tiesFixed hcat hA hF hK hwf.1 h.2 hrows⟩
    exact (h.map _).trans ((aggAllowed_canon (hms hp) ho).trans
      ((aggregateEval_perm_of (hms .rfl) hp).map _))
  | .fetch _ _ _, hwf, hd, _, h | .cross _ _, hwf, hd, _, h | .join _ _ _ _, hwf, hd, _, h
  | .semi _ _ _ _, hwf, hd, _, h | .unnest _ _, hwf, hd, _, h =>
    (allowed_perm_eval hcat hA hF hK hwf (by simpa [detClass] using hd) h).map _

/-- A rewrite to a plan without choices whose rows are the original's
refines it up to the order of rows, whatever choices the original leaves. -/
theorem Rel.refines_of_perm {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {q r : Rel} (hwf : q.WF cat)
    (hd : q.detPlan cat A F K = true) (h : (q.eval cat).Perm (r.eval cat)) : q.RefinesBag cat r :=
  Rel.refinesBag_iff.2 fun _ hq => ⟨r.eval cat, r.eval_allowed cat,
    (allowed_perm_eval hcat hA hF hK hwf hd hq).trans h⟩

/-! ## Engines

The theorems about engines conclude that an engine computes `Rel.eval`'s rows
(or raises); so it returns an allowed result. -/

/-- Guard elimination: the plan run without its row-level checks returns an
allowed result. -/
theorem Rel.guardFree_allowed {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true)
    {I : Impl} (hI : I.Faithful) : r.Allowed cat (r.eval cat I) := by
  rw [Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm hI]; exact r.eval_allowed cat

/-! ## Row caps -/

/-- On tables within their caps, every order of a plan is one of the plan
with capped reads (`Rel.capReads`), which the checker interprets. -/
theorem Rel.orderAllowed_capReads {caps : String → Option Nat} {cat : Catalog}
    (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel} {out : Relation}, r.OrderAllowed cat out → (r.capReads caps).OrderAllowed cat out
  | .read t, out, h => by
    unfold capReads
    split
    · rename_i n hn
      refine ⟨out, h, ?_⟩
      simp only [List.drop_zero]
      exact (List.take_of_length_le (h.length_eq ▸ hc t n hn)).symm
    · exact h
  | .values _ _, _, h => h
  | .filter r _, _, ⟨i, hi, h⟩ | .project r _, _, ⟨i, hi, h⟩ | .emit r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .fetch r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .cross a b, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, h⟩
  | .join a b .inner _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, h⟩
  | .join a b .left _, _, ⟨x, y, hx, hy, h⟩ => by
    refine ⟨x, y, orderAllowed_capReads hc (r := a) hx, orderAllowed_capReads hc (r := b) hy, ?_⟩
    rw [capReads_arity]; exact h
  | .window r _ _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .orderBy r _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .distinct r, _, ⟨i, hi, h⟩ | .unnest r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩
  | .aggregate r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_capReads hc (r := r) hi, h⟩

/-! ## Postconditions on every allowed result -/

/-- Column `j` of a selection `T.select(…)` over `n` columns: a column of
`T`, or the expression appended there. -/
def postExpr (n : Nat) (es : List Expr) (j : Nat) : Expr :=
  if j < n then .field j else es.getD (j - n) (.lit .null)

theorem postExpr_eval {n : Nat} {es : List Expr} {x : Row} (hx : x.length = n) (j : Nat) :
    (x ++ es.map (·.eval x)).getD j .null = (postExpr n es j).eval x := by
  unfold postExpr
  split
  · next h =>
    simp only [Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left (hx ▸ h)]
  · next h =>
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (l₁ := x) (by omega), hx,
      List.getElem?_map, List.getD_eq_getElem?_getD]
    cases es[j - n]? <;> rfl

omit [Boxes.Ambient] in
theorem postExpr_narrow (n : Nat) (es : List Expr) (sh : Nat → Option Shift) (j : Nat) :
    postExpr n (es.map (·.narrow sh)) j = (postExpr n es j).narrow sh := by
  unfold postExpr
  split
  · simp [Expr.narrow, Expr.narrowCmp, Expr.cmp?]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases es[j - n]? <;> simp [Expr.narrow, Expr.narrowCmp, Expr.cmp?]

omit [Boxes.Ambient] in
theorem Row.EquivFrom.length_eq {q : Obs} {ctx : ObsCtx} :
    ∀ {i : Nat} {r r' : Row}, Row.EquivFrom q ctx i r r' → r.length = r'.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, ⟨_, t⟩ => by simp [Row.EquivFrom.length_eq t]
  | _, [], _ :: _, h | _, _ :: _, [], h => h.elim

/-- **Contracts hold on a result near one of an order's.** On data meeting the
preconditions, the postconditions `es` of the transformation `T`, selected by
`mp`, hold on the rows `t`, when `t` is, under the observation `q` (rows as a
multiset), the result `t'` of one of the reference's orders, the
postconditions are `Expr.robustB` under `q` with the shifts `sh`, and the
checker proves them narrowed by `sh` on every order (`contract_sound_all`).
`contract_sound_allowed` takes `t` from `Rel.Allowed`, and an engine's run
takes it from its table (`Engine.contract_sound_runs_near`). -/
theorem contract_sound_near {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true)
    {t t' : Relation} (ht' : T.OrderAllowed cat t') (heq : Relation.Equiv q ctx t' t) :
    ∀ row ∈ (t.map fun row => row ++ es.map (·.eval row)).map (fun row => mp.map (row.getD · .null)),
      ∀ v ∈ row, v = .bool true := by
  intro row hrow v hv
  unfold Relation.Equiv at heq; rw [hq] at heq
  obtain ⟨p, hf, hpt⟩ := heq
  -- The row of `T` it comes from, and its partner in an order's result.
  simp only [List.map_map, List.mem_map, Function.comp] at hrow
  obtain ⟨x, hx, rfl⟩ := hrow
  obtain ⟨x', hx', hxx⟩ := Forall2.mem_right hf (hpt.mem_iff.mpr hx)
  have hlen' : x'.length = T.arity cat := Rel.orderAllowed_arity hcat hT ht' x' hx'
  have hlen : x.length = T.arity cat := (Row.EquivFrom.length_eq hxx).symm.trans hlen'
  -- The narrowed postconditions hold on the partner (`contract_sound_all`).
  have hall := contract_sound_all hcat hS hpre hQ hW hproved
    (out := (t'.map fun row => row ++ (es.map (·.narrow sh)).map (·.eval row)).map
      fun row => mp.map (row.getD · .null)) ⟨_, ⟨t', ht', rfl⟩, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
  have h' := hall (mp.map ((x' ++ (es.map (·.narrow sh)).map (·.eval x')).getD · .null))
    (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x', hx', rfl⟩, rfl⟩) _
    (List.mem_map.mpr ⟨j, hj, rfl⟩)
  rw [postExpr_eval hlen', postExpr_narrow] at h'
  rw [postExpr_eval hlen, ← Value.isTrue_iff]
  exact Expr.narrow_sound hsh _ (hrob j hj) hxx (Value.isTrue_iff.mpr h')

/-- **Contracts hold on every allowed result.** On data meeting the
preconditions, the postconditions `es` of the transformation `T`, selected
by `mp`, hold on every result the reference allows (`Rel.Allowed`, every
order and grouping of a double `SUM` or `AVG`), when

* `T` is `Rel.FloatOpenSafe` under the observation `q` (rows as a multiset),
* each postcondition is `Expr.robustB` under `q` with the shifts `sh`,
  sound for `q` (`Shift.Sound`), and
* the checker proves the postconditions narrowed by `sh` (`Expr.narrow`),
  as `contract_sound_all` proves them, on every order. -/
theorem contract_sound_allowed {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafe : T.FloatOpenSafe q ctx cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true) :
    ∀ {out : Relation}, (Rel.emit (.project T es) mp).Allowed cat out →
      ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  rintro out ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  obtain ⟨t', ht', heq⟩ := hsafe t ht
  exact contract_sound_near hcat hS hpre hT hq hsh hrob hQ hW hproved ht' heq

/-- **Contracts hold on every allowed result of a closed plan** (D25): the
side condition of `contract_sound_allowed` replaced by the decidable
`Rel.closedB`, which holds of every plan whose measures are not
`VAR_*`, `STDDEV_*`, `COVAR_*`, `CORR` or `QUANTILE_CONT` (a double `SUM` or
`AVG` is order-free since D25), for a context reflexive at `q`. -/
theorem contract_sound_allowed_closed {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset) (hc : ctx.ReflAt q)
    (hclosed : T.closedB = true) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true) :
    ∀ {out : Relation}, (Rel.emit (.project T es) mp).Allowed cat out →
      ∀ row ∈ out, ∀ v ∈ row, v = .bool true :=
  contract_sound_allowed hcat hS hpre hT hq (Rel.floatOpenSafe_of_closed hc hclosed) hsh hrob hQ hW
    hproved

end Substrait
