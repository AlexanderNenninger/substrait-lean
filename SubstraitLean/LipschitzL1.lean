import SubstraitLean.Lipschitz

/-!
# The `M₁` fold (#929)

`Relation.NearL1 t a b` matches the rows of `a` and `b` so that, per double
column, the distances of the matched pairs sum to at most `t` of it: what a
downstream `SUM` over the column sees. This module folds a plan's `M₁`
budget from its sources' (`Rel.tol1`) and proves it (`Rel.plan_nearL1`):

* a filter on exact columns, `ORDER BY` and a semi-join keep the budget
  (fewer pairs sum to less);
* a projection and an emit give each column the budget of the column it
  copies, and an expression of exact columns is exact;
* `UNION ALL` adds its inputs' budgets (`M∞` takes the larger);
* a cross or inner join pairs every left row with every right row: the left
  columns' budget counts once per right row and the right's once per left
  row, at most the other side's row bound (`Rel.rowsK`);
* `DISTINCT` and an aggregate of exact keys and measures are exact.

`SUM` and `AVG` of a tolerated column in `M₁` add their group's distances and
one rounding per group; they follow.
-/

namespace Substrait

/-! ## Budgets -/

/-- Each output column's budget from the input column it copies (`none`:
exact). -/
def Tol.pull (src : Nat → Option Nat) (t : Tol) : Tol := fun j => (src j).bind t

/-- `n` times a budget. -/
def Tol.scale (n : Nat) (t : Tol) : Tol := fun c => (t c).map (n * ·)

section
variable {a b c d t t' : Tol}

theorem Tol.Le.add_left_le (h : (a.add b).Le t) : a.Le t := fun c => by
  have x := Tol.le_add_left a b c; have y := h c
  revert x y; cases a c <;> cases (a.add b) c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.Le.add_right_le (h : (a.add b).Le t) : b.Le t := fun c => by
  have x := Tol.le_add_right a b c; have y := h c
  revert x y; cases b c <;> cases (a.add b) c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.le_add_of_le_right (h : b.Le t) : b.Le (a.add t) := fun c => by
  have y := h c; revert y; simp only [Tol.add]
  cases a c <;> cases b c <;> cases t c <;> simp [OLe] <;> omega

theorem Tol.add_assoc_le : (a.add (b.add c)).Le ((a.add b).add c) := fun k => by
  simp only [Tol.add]; cases a k <;> cases b k <;> cases c k <;> simp [OLe] <;> omega

theorem Tol.pull_mono (src : Nat → Option Nat) (h : a.Le b) : (Tol.pull src a).Le (Tol.pull src b) :=
  fun j => by simp only [Tol.pull]; cases src j <;> simp [OLe]; exact h _

theorem Tol.pull_add (src : Nat → Option Nat) :
    ((Tol.pull src a).add (Tol.pull src b)).Le (Tol.pull src (a.add b)) := fun j => by
  unfold Tol.add Tol.pull
  cases src j with
  | none => simp [OLe]
  | some i => simp only [Option.bind_some]; cases a i <;> cases b i <;> simp [OLe]

theorem Tol.scale_mono {m n : Nat} (hmn : m ≤ n) (h : a.Le b) : (Tol.scale m a).Le (Tol.scale n b) :=
  fun k => by
    have x := h k; revert x; simp only [Tol.scale]
    cases a k <;> cases b k <;> simp [OLe]
    intro hx; exact Nat.mul_le_mul hmn hx

theorem Tol.scale_add (n : Nat) : ((Tol.scale n a).add (Tol.scale n b)).Le (Tol.scale n (a.add b)) :=
  fun k => by
    simp only [Tol.scale, Tol.add]; cases a k <;> cases b k <;> simp [OLe, Nat.mul_add]

theorem Tol.scale_succ (n : Nat) : (a.add (Tol.scale n a)).Le (Tol.scale (n + 1) a) := fun k => by
  simp only [Tol.scale, Tol.add]; cases a k <;> simp [OLe, Nat.succ_mul]; omega

theorem Tol.cat_add (n : Nat) :
    ((Tol.cat n a b).add (Tol.cat n c d)).Le (Tol.cat n (a.add c) (b.add d)) := fun k => by
  by_cases hk : k < n <;> simp only [Tol.cat, Tol.add, hk, ite_true, ite_false] <;> exact OLe.refl _

theorem Tol.cat_mono (n : Nat) (h₁ : a.Le c) (h₂ : b.Le d) : (Tol.cat n a b).Le (Tol.cat n c d) :=
  fun k => by simp only [Tol.cat]; split <;> first | exact h₁ _ | exact h₂ _

end

/-! ## Matchings through the operators -/

theorem PairsWithin.length_eq : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → a.length = p.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, _, _, h, _⟩ => by simp [PairsWithin.length_eq h]
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- Every pair is within the whole budget. -/
theorem PairsWithin.forall2 {T0 : Tol} : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t →
    t.Le T0 → Forall2 T0.Rows a p
  | [], [], _, _, _ => .nil
  | _ :: _, _ :: _, _, ⟨_, _, r, h, le⟩, ht =>
    .cons ⟨r.1, fun j => Tol.cell_transfer ((le.add_left_le.trans ht) j) (r.2 j)⟩
      (PairsWithin.forall2 h (le.add_right_le.trans ht))
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- **Fewer pairs** sum to less: a filter that reads the same on both rows of
a pair keeps the budget. `Q` holds of the right side's rows. -/
theorem PairsWithin.filter {T0 : Tol} {Q : Row → Prop} {P P' : Row → Bool}
    (hP : ∀ (tr : Tol) (x y : Row), tr.Le T0 → tr.Rows x y → Q y → P x = P' y) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → t.Le T0 → (∀ y ∈ p, Q y) →
      PairsWithin (a.filter P) (p.filter P') t
  | [], [], _, _, _, _ => trivial
  | x :: xs, y :: ys, t, ⟨tr, rest, r, h, le⟩, ht, hq => by
    have ih := PairsWithin.filter hP h (le.add_right_le.trans ht)
      fun z hz => hq z (List.mem_cons_of_mem _ hz)
    rw [List.filter_cons, List.filter_cons,
      hP tr x y (le.add_left_le.trans ht) r (hq y (List.mem_cons_self ..))]
    split
    · exact ⟨tr, rest, r, ih, le⟩
    · exact ih.mono le.add_right_le
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => h.elim

/-- **A row map** whose output columns copy input columns (`Tol.pull src`).
`Q` holds of the right side's rows. -/
theorem PairsWithin.map {T0 : Tol} {Q : Row → Prop} {src : Nat → Option Nat} {f g : Row → Row}
    (hf : ∀ (tr : Tol) (x y : Row), tr.Le T0 → tr.Rows x y → Q y →
      (Tol.pull src tr).Rows (f x) (g y)) :
    ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → t.Le T0 → (∀ y ∈ p, Q y) →
      PairsWithin (a.map f) (p.map g) (Tol.pull src t)
  | [], [], _, _, _, _ => trivial
  | x :: _, y :: _, _, ⟨tr, rest, r, h, le⟩, ht, hq =>
    ⟨Tol.pull src tr, Tol.pull src rest,
      hf tr x y (le.add_left_le.trans ht) r (hq y (List.mem_cons_self ..)),
      PairsWithin.map hf h (le.add_right_le.trans ht) fun z hz => hq z (List.mem_cons_of_mem _ hz),
      (Tol.pull_add src).trans (Tol.pull_mono src le)⟩
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => h.elim

/-- **`UNION ALL`**: budgets add. -/
theorem PairsWithin.append : ∀ {a p b q : List Row} {ta tb : Tol}, PairsWithin a p ta →
    PairsWithin b q tb → PairsWithin (a ++ b) (p ++ q) (ta.add tb)
  | [], [], _, _, _, _, _, h => h.mono (fun c => Tol.le_add_right _ _ c)
  | _ :: _, _ :: _, _, _, _, _, ⟨tr, rest, r, h, le⟩, h' =>
    ⟨tr, rest.add _, r, PairsWithin.append h h',
      Tol.add_assoc_le.trans (Tol.add_mono le (Tol.Le.refl _))⟩
  | [], _ :: _, _, _, _, _, h, _ | _ :: _, [], _, _, _, _, h, _ => h.elim

/-- One left pair against the right side's pairs: the left pair's budget
counts once per right row. -/
theorem PairsWithin.prefix {n : Nat} {x y : Row} {tr : Tol} (r : tr.Rows x y) (hy : y.length = n) :
    ∀ {b q : List Row} {tb : Tol}, PairsWithin b q tb →
      PairsWithin (b.map (x ++ ·)) (q.map (y ++ ·)) (Tol.cat n (Tol.scale b.length tr) tb)
  | [], [], _, _ => trivial
  | _ :: bs, _ :: _, _, ⟨tu, rest, ru, h, le⟩ =>
    ⟨Tol.cat n tr tu, Tol.cat n (Tol.scale bs.length tr) rest, Tol.rows_append r ru hy,
      PairsWithin.prefix r hy h,
      (Tol.cat_add n).trans (Tol.cat_mono n (by simpa using Tol.scale_succ bs.length) le)⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- **A cross**: the left columns' budget once per right row, the right's
once per left row. -/
theorem PairsWithin.cross {n : Nat} {b q : List Row} {tb : Tol} (hb : PairsWithin b q tb) :
    ∀ {a p : List Row} {ta : Tol}, PairsWithin a p ta → (∀ y ∈ p, y.length = n) →
      PairsWithin (crossRows a b) (crossRows p q)
        (Tol.cat n (Tol.scale b.length ta) (Tol.scale a.length tb))
  | [], [], _, _, _ => trivial
  | _ :: xs, y :: _, _, ⟨tr, rest, r, h, le⟩, hp => by
    have ih := PairsWithin.cross hb h fun z hz => hp z (List.mem_cons_of_mem _ hz)
    have hx := PairsWithin.prefix r (hp y (List.mem_cons_self ..)) hb
    simp only [crossRows, List.flatMap_cons] at ih ⊢
    refine (hx.append ih).mono ((Tol.cat_add n).trans (Tol.cat_mono n ?_ ?_))
    · exact (Tol.scale_add b.length).trans (Tol.scale_mono (Nat.le_refl _) le)
    · simpa [Nat.add_comm] using Tol.scale_succ (a := tb) xs.length
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-! ## The fold -/

/-- A projection's columns: the input's, then each expression's, a field
copying its column and anything else exact. -/
def projSrc (n : Nat) (es : List Expr) (j : Nat) : Option Nat :=
  if j < n then some j else
  match es[j - n]? with
  | some (.field i) => some i
  | _ => none

theorem Tol.exactOn_of_le {tr t : Tol} (h : tr.Le t) {cols : List Nat} (he : t.exactOn cols = true) :
    tr.exactOn cols = true := by
  simp only [Tol.exactOn, List.all_eq_true, Option.isNone_iff_eq_none] at he ⊢
  intro i hi
  have := h i; rw [he i hi] at this
  revert this; cases tr i <;> simp [OLe]

theorem Tol.rows_project {tr t : Tol} {n : Nat} {es : List Expr}
    (hes : es.all (fun e => (e.tol? t).isSome) = true) (hle : tr.Le t) {x y : Row}
    (r : tr.Rows x y) (hy : y.length = n) :
    (Tol.pull (projSrc n es) tr).Rows (x ++ es.map (·.eval x)) (y ++ es.map (·.eval y)) := by
  refine ⟨by simp [r.1], fun j => ?_⟩
  rw [getD_append_split, getD_append_split, r.1, hy]
  by_cases hj : j < n
  · simp only [hj, ite_true]
    exact Tol.cell_transfer (by simp [Tol.pull, projSrc, hj, OLe.refl]) (r.2 j)
  · simp only [hj, ite_false, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases he : es[j - n]? with
    | none => exact Tol.cell_null _ _
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      have hs : (e.tol? t).isSome = true := List.all_eq_true.1 hes e (List.mem_of_getElem? he)
      by_cases hf : ∃ i, e = .field i
      · obtain ⟨i, rfl⟩ := hf
        have hc : Tol.pull (projSrc n es) tr j = tr i := by simp [Tol.pull, projSrc, hj, he]
        exact Tol.cell_transfer (by rw [hc]; exact OLe.refl _) (r.2 i)
      · have hx : t.exactOn e.cols = true := by
          unfold Expr.tol? at hs
          split at hs
          · exact absurd ⟨_, rfl⟩ hf
          · split at hs <;> simp_all
        rw [Expr.eval_rows (Tol.exactOn_of_le hle hx) r]
        exact Tol.cell_refl _ _ _

/-- **The `M₁` budget of a plan's output**, each source `s` within `T s`. -/
def Rel.tol1 (cat : Catalog) (K : KnowledgeEnv) (T : String → Tol) : Rel → Option Tol
  | .read s => some (T s)
  | .values _ _ => some Tol.exact
  | .filter r c => (r.tol1 cat K T).bind fun t => if t.exactOn c.cols then some t else none
  | .project r es => (r.tol1 cat K T).bind fun t =>
      if es.all (fun e => (e.tol? t).isSome) then some (Tol.pull (projSrc (r.arity cat) es) t)
      else none
  | .emit r m => (r.tol1 cat K T).map (Tol.pull fun j => m[j]?)
  | .cross a b => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      (a.rowsK K).bind fun na => (b.rowsK K).map fun nb =>
        Tol.cat (a.arity cat) (Tol.scale nb ta) (Tol.scale na tb)
  | .join a b .inner on => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      (a.rowsK K).bind fun na => (b.rowsK K).bind fun nb =>
        let t := Tol.cat (a.arity cat) (Tol.scale nb ta) (Tol.scale na tb)
        if t.exactOn on.cols then some t else none
  | .unionAll a b => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).map fun tb => ta.add tb
  | .semi a b _ on => (a.tol1 cat K T).bind fun ta => (b.tol1 cat K T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some ta else none
  | .orderBy r _ => r.tol1 cat K T
  | .distinct r => (r.tol1 cat K T).bind fun t =>
      if t.exactBelow (r.arity cat) then some Tol.exact else none
  | .aggregate r gs ms => (r.tol1 cat K T).bind fun t =>
      if gs.all (fun g => t.exactOn g.cols) && ms.all (·.tolOk t) then some Tol.exact else none
  | .join _ _ .left _ | .fetch .. | .window .. | .unnest .. => none

theorem Relation.NearL1.nearT {t : Tol} {a b : Relation} (h : Relation.NearL1 t a b) :
    Relation.NearT t a b :=
  let ⟨p, w, hp⟩ := h; ⟨p, w.forall2 (Tol.Le.refl t), hp⟩

/-- **`plan_near` in `M₁` (#929)**: an engine's sources within `T` of the
reference's, budgets summed over matched rows, give a result within
`Rel.tol1 cat K T r` of the reference's. -/
theorem Rel.plan_nearL1 {cat cat' : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearL1 (T s) (cat' s).rows (cat s).rows) :
    ∀ {r : Rel} {t : Tol}, r.WF cat → r.tol1 cat K T = some t →
      Relation.NearL1 t (r.eval cat') (r.eval cat)
  | .read s, t, _, h => by
    simp only [Rel.tol1, Option.some.injEq] at h; subst h; exact hT s
  | .values _ _, t, _, h => by
    simp only [Rel.tol1, Option.some.injEq] at h; subst h; exact .refl _ _
  | .filter r c, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
      exact ⟨_, w.filter (Q := fun _ => True) (fun tr x y hle rxy _ => by
          rw [Expr.eval_rows (Tol.exactOn_of_le hle hc) rxy]) (Tol.Le.refl _) (fun _ _ => trivial),
        hp.filter _⟩
    · exact absurd h (by simp)
  | .project r es, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hes
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
      have hlen : ∀ y ∈ p, y.length = r.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      exact ⟨_, w.map (Q := fun y => y.length = r.arity cat)
          (fun tr x y hle rxy hy => Tol.rows_project hes hle rxy hy) (Tol.Le.refl _) hlen,
        hp.map _⟩
    · exact absurd h (by simp)
  | .emit r m, t, hwf, h => by
    simp only [Rel.tol1, Option.map_eq_some_iff] at h
    obtain ⟨t0, hr, rfl⟩ := h
    obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hr
    refine ⟨_, w.map (Q := fun _ => True) (fun tr x y _ rxy _ => ?_) (Tol.Le.refl _)
      (fun _ _ => trivial), hp.map _⟩
    have e : Tol.pull (fun j => m[j]?) tr = tr.emit m := by
      funext j; simp only [Tol.pull, Tol.emit]; cases m[j]? <;> rfl
    rw [e]; exact Tol.rows_emit rxy m
  | .cross a b, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, na, hna, nb, hnb, rfl⟩ := h
    obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
    obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2 htb
    have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
      Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
    have la : (a.eval cat').length ≤ na := by
      rw [wa.length_eq, hp.length_eq]; exact Rel.rowsK_sound hK hna
    have lb : (b.eval cat').length ≤ nb := by
      rw [wb.length_eq, hq.length_eq]; exact Rel.rowsK_sound hK hnb
    exact ⟨_, (wb.cross wa hlen).mono (Tol.cat_mono _ (Tol.scale_mono lb (Tol.Le.refl _))
      (Tol.scale_mono la (Tol.Le.refl _))), crossRows_perm hp hq⟩
  | .join a b .inner on, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, na, hna, nb, hnb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
      obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2.1 htb
      have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      have la : (a.eval cat').length ≤ na := by
        rw [wa.length_eq, hp.length_eq]; exact Rel.rowsK_sound hK hna
      have lb : (b.eval cat').length ≤ nb := by
        rw [wb.length_eq, hq.length_eq]; exact Rel.rowsK_sound hK hnb
      have wc := (wb.cross wa hlen).mono (Tol.cat_mono (a.arity cat)
        (Tol.scale_mono lb (Tol.Le.refl _)) (Tol.scale_mono la (Tol.Le.refl _)))
      refine ⟨_, wc.filter (Q := fun _ => True) (fun tr x y hle rxy _ => by
          rw [Expr.eval_rows (Tol.exactOn_of_le hle hon) rxy]) (Tol.Le.refl _) (fun _ _ => trivial),
        (crossRows_perm hp hq).filter _⟩
    · exact absurd h (by simp)
  | .join _ _ .left _, _, _, h | .fetch .., _, _, h | .window .., _, _, h | .unnest .., _, _, h => by
    simp [Rel.tol1] at h
  | .unionAll a b, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
    obtain ⟨q, wb, hq⟩ := plan_nearL1 hcat hK ha hT hwf.2.1 htb
    exact ⟨_, wa.append wb, hp.append hq⟩
  | .semi a b anti on, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, wa, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 hta
      obtain ⟨q, fq, hq⟩ := (plan_nearL1 hcat hK ha hT hwf.2.1 htb).nearT
      have hlen : ∀ y ∈ p, y.length = a.arity cat := fun y hy =>
        Rel.eval_arity hcat hwf.1 y (hp.mem_iff.1 hy)
      refine ⟨_, wa.filter (Q := fun y => y.length = a.arity cat) (fun tr x y hle rxy hy => ?_)
        (Tol.Le.refl _) hlen, hp.filter _⟩
      simp only [hasMatch]
      rw [fq.any_eq (p' := fun v => (on.eval (y ++ v)).isTrue) fun u v ruv => by
        rw [Expr.eval_rows (Tol.exactOn_of_le (Tol.cat_mono _ hle (Tol.Le.refl _)) hon)
          (Tol.rows_append rxy ruv hy)], hq.any_eq]
    · exact absurd h (by simp)
  | .orderBy r _, t, hwf, h => by
    simp only [Rel.tol1] at h
    obtain ⟨p, w, hp⟩ := plan_nearL1 hcat hK ha hT hwf.1 h
    obtain ⟨p', hpp, w'⟩ := PairsWithin.perm (List.mergeSort_perm _ _).symm w
    exact ⟨p', w', hpp.symm.trans (hp.trans (List.mergeSort_perm _ _).symm)⟩
  | .distinct r, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      have hw : r.WF cat := hwf
      obtain ⟨p, fp, hp⟩ := (plan_nearL1 hcat hK ha hT hw hr).nearT.forall2_mem (Rel.eval_arity hcat hw)
      have : r.eval cat' = p := Forall2.eq (fp.imp fun x y rxy => Tol.rows_eq he rxy.1 rxy.2)
      simp only [Rel.eval, this]
      exact ⟨_, PairsWithin.refl _ _, dedup_perm_of_mem fun z => hp.mem_iff⟩
    · exact absurd h (by simp)
  | .aggregate r gs ms, t, hwf, h => by
    simp only [Rel.tol1, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := (plan_nearL1 hcat hK ha hT hwf.1 hr).nearT
      have hof : ∀ m ∈ ms, m.orderFree = true := fun m hm => by
        have := List.all_eq_true.1 hok.2 m hm
        simp only [Measure.tolOk, Bool.and_eq_true] at this
        exact this.1.1.1
      simp only [Rel.eval]
      rw [aggregateEval_rows hok.1 hok.2 fp]
      exact ⟨_, PairsWithin.refl _ _, aggregateEval_perm hof hp⟩
    · exact absurd h (by simp)

/-! ## Examples

A table of three columns of at most 10 rows, the third a double with an
`M₁` budget of 8 codes. -/

private def exCat1 : Catalog := fun _ => ⟨3, []⟩
private def exK1 : KnowledgeEnv := fun _ => ⟨[], [], [], some 10⟩
private def exT1 : String → Tol := fun _ c => if c = 2 then some 8 else none
private def exB (r : Rel) : Option (List (Option Nat)) :=
  (r.tol1 exCat1 exK1 exT1).map fun t => (List.range 6).map t

-- A union adds the budgets; `M∞` would take the larger.
#guard exB (.unionAll (.read "t") (.read "t")) == some [none, none, some 16, none, none, none]
-- A cross counts each side's budget once per row of the other: 10 · 8.
#guard exB (.cross (.read "t") (.read "t")) == some [none, none, some 80, none, none, some 80]
-- A projection copies the budget of the column it reads.
#guard exB (.project (.read "t") [.field 2]) == some [none, none, some 8, some 8, none, none]
-- A filter on the double is refused, as in `M∞`.
#guard exB (.filter (.read "t") (.bin .lt (.field 2) (.lit (.int 5)))) == none

end Substrait
