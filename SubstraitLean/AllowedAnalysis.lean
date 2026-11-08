import SubstraitLean.AllowedNear
import SubstraitLean.Partition
import SubstraitLean.Guards

/-!
# What the analysis proves of the allowed results

`Rel.Allowed` (`SubstraitLean/Allowed.lean`) is the reference's relation;
this module states what the analysis proves of it. For a plan without
choices (`Rel.detPlan`, decided from the abstract values, facts and keys of
`SubstraitLean/Contracts.lean`), every allowed result is `Rel.eval`'s up to
the order of rows (`Rel.allowed_perm_eval`), so a rewrite to such a plan
with the original's rows refines it up to the order of rows
(`Rel.refines_of_perm`); and a plan run without its row-level checks returns
an allowed result (`Rel.guardFree_allowed`). A row cap keeps every order a
plan allows (`Rel.orderAllowed_capReads`), for the checker's capped reads
(`Rel.capReads`). A contract proved by the checker holds of every allowed
result, up to its observation (`contract_sound_allowed`, over
`SubstraitLean/AllowedNear.lean`'s closeness).
-/

namespace Substrait

/-! ## Plans without choices -/

/-- Does `r` leave the engine no choice but the order of its rows? No
`FETCH` (which rows come first), each window's ties broken alike
(`Rel.windowsTotal`'s checks), and aggregates that are functions of their
values (`Measure.orderFree`: `COUNT`, `SUM`, `AVG` of doubles too (D25),
`MIN`, `MAX`). -/
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

theorem postExpr_narrow (n : Nat) (es : List Expr) (sh : Nat → Option Shift) (j : Nat) :
    postExpr n (es.map (·.narrow sh)) j = (postExpr n es j).narrow sh := by
  unfold postExpr
  split
  · simp [Expr.narrow, Expr.narrowCmp, Expr.cmp?]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases es[j - n]? <;> simp [Expr.narrow, Expr.narrowCmp, Expr.cmp?]

theorem Row.EquivFrom.length_eq {q : Obs} {ctx : ObsCtx} :
    ∀ {i : Nat} {r r' : Row}, Row.EquivFrom q ctx i r r' → r.length = r'.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, ⟨_, t⟩ => by simp [Row.EquivFrom.length_eq t]
  | _, [], _ :: _, h | _, _ :: _, [], h => h.elim

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
  rintro out ⟨_, ⟨t, ht, rfl⟩, rfl⟩ row hrow v hv
  obtain ⟨t', ht', heq⟩ := hsafe t ht
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
