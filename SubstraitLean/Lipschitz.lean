import SubstraitLean.Lipschitz.Arith
import Sverify.Analysis.AllowedAnalysis

/-!
# Tolerance composition along a plan (#929)

A result within `t c` codes of the reference in each double column `c`
(`Relation.Near`, #896) stays within a computed tolerance of it after every
operator the plan applies. This module gives the fold, its theorem and the
pipeline rule; its parts are `Lipschitz/Basic.lean` (cells, rows, matchings),
`Lipschitz/Measures.lean` (reference codes, `SUM` and `AVG`) and
`Lipschitz/Arith.lean` (arithmetic, `MIN`, `MAX`, groups):

* `Rel.tol cat K T r`: the tolerance of `r`'s output when each source `s` is
  within `T s` of the reference's: #929's table. Pass-through columns, emits,
  `UNION ALL` (the larger of its inputs'), crosses, joins and semi-joins on
  exact columns carry a tolerance with `M∞ = 1`; an expression of exact
  columns, a group key and an order-free measure of exact columns are exact.
  A `SUM` or `AVG` of a tolerated column has the table's `g·ε + r` and
  `ε + r` (`Measure.tolOut`), where the knowledge `K` of the reference's
  sources bounds the column's codes and the group's rows (`Rel.rowsK`); a
  `MIN` or `MAX` its argument's tolerance, `M∞ = 1` (`Measure.minMaxOut`). It
  is `none` where the plan compares a tolerated column (a filter, join or
  semi-join condition, a group key, `DISTINCT`, any other measure of it):
  #929's discontinuity rows, the `rows_exact` rule of #568. `FETCH` and
  windows read an order the multiset observation does not fix, and `UNNEST`
  is not in the table yet.
* `Rel.plan_near`: **the theorem.** An engine's sources within `T` of the
  reference's give a result within `Rel.tol cat K T r` of the reference's,
  `K` sound for the reference's sources. Distances are between canonical
  codes, so the tolerance takes `-0.0` for `+0.0` and the sources' codes need
  no condition.
* `Relation.NearT.add`: the triangle rule, and `Rel.pipeline_near`, the
  pipeline rule `εₖ = Lₖ·εₖ₋₁ + rₖ`: a node's bound is the next node's
  source tolerance (`Triple.ε` of #929), and the node's own rounding `rₖ`
  adds to what its plan carries.
* `Relation.NearL1`: the `M₁` metric, rows matched so that each column's
  distances sum within a budget (what a downstream `SUM` sees), with
  reflexivity, symmetry and the triangle rule.
* `Measure.fsum_near`, `Measure.avg_near`: a `SUM` or `AVG` of a tolerated
  column on groups within a tolerance, the table's `g·ε + r` and `ε + r`
  (`floatSumCR_near`, `floatAvgCR_near` in `FloatNear.lean`), with finite
  values and results as named hypotheses; `Measure.tolOut_cell` discharges
  them from the fold's checks.

The tolerance is in codes (`Tol`): a finite double's code is twice its
magnitude in units of `2⁻¹⁰⁷⁴`, plus one, with its sign (`FloatFormat`), so
codes measure absolute distance and a Lipschitz constant on codes is one on
values. The arithmetic rows (`x ± y`, `x · y`, `c · x`, `x / c`, and `x / y`
with `y`'s range clear of zero, `ClearOfZero`; exact since D31) are
`Expr.arithTol`, in a projection through `Expr.tolA`. The `M₁` fold is `LipschitzL1.lean`, where
arithmetic stays exact or refused for now.

A tolerance leaves its other columns exact, and compares them exactly:
`Tol.kind t` marks only the tolerated columns as doubles, so a filter on an
exact column reads one value on both sides (`Tol.cell_none`).
`Relation.NearT.near` gives `Relation.Near` under the plan's own column
kinds. -/

namespace Substrait

open FloatCode

/-! ## The fold and its theorem -/

variable [Boxes.Ambient]
/-- **The tolerance of a plan's output**, when each source `s` is within
`T s` of the reference's: the table of #929 on its constant-`1` rows. `none`
where the plan compares a tolerated column (a filter, join or semi-join
condition, a group key, `DISTINCT`, a measure's argument other than a `SUM`
or `AVG` the analysis bounds, `Measure.tolOut`), and for the operators whose
rows depend on an order the multiset observation does not fix (`FETCH`,
windows) or not yet in the table (`UNNEST`). `K` is the knowledge of the
reference's sources, which bounds a `SUM`'s values. -/
def Rel.tol (cat : Catalog) (K : KnowledgeEnv) (T : String → Tol) : Rel → Option Tol
  | .read s => some (T s)
  | .values _ _ => some Tol.exact
  | .filter r c => (r.tol cat K T).bind fun t => if t.exactOn c.cols then some t else none
  | .project r es => (r.tol cat K T).bind fun t =>
      if es.all (fun e => (e.tolA t (r.refCols cat) (r.analyse cat K).cols).isSome) then
        some (Tol.cat (r.arity cat) t (Tol.exprsA t (r.refCols cat) (r.analyse cat K).cols es))
      else none
  | .emit r m => (r.tol cat K T).map (Tol.emit · m)
  | .cross a b => (a.tol cat K T).bind fun ta => (b.tol cat K T).map fun tb => Tol.cat (a.arity cat) ta tb
  | .join a b _ on => (a.tol cat K T).bind fun ta => (b.tol cat K T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some (Tol.cat (a.arity cat) ta tb)
      else none
  | .fetch .. | .window .. | .unnest .. => none
  | .unionAll a b => (a.tol cat K T).bind fun ta => (b.tol cat K T).map fun tb => Tol.max ta tb
  | .semi a b _ on => (a.tol cat K T).bind fun ta => (b.tol cat K T).bind fun tb =>
      if (Tol.cat (a.arity cat) ta tb).exactOn on.cols then some ta else none
  | .orderBy r _ => r.tol cat K T
  | .distinct r => (r.tol cat K T).bind fun t =>
      if t.exactBelow (r.arity cat) then some Tol.exact else none
  | .aggregate r gs ms => (r.tol cat K T).bind fun t =>
      let os := ms.map (·.outTol t (r.refCols cat) (r.analyse cat K).cols (r.rowsK K))
      if gs.all (fun g => t.exactOn g.cols) && os.all Option.isSome then
        some (Tol.cat gs.length Tol.exact (Tol.ofOuts os))
      else none

/-- **`plan_near` (#929)**: an engine's sources within `T` of the
reference's give a result within `Rel.tol cat K T r` of the reference's,
rows as a multiset. `cat'` is the engine's catalog, with the reference's
arities; the reference's catalog is well-formed, and `K` sound for it. -/
theorem Rel.plan_near {cat cat' : Catalog} (hcat : cat.WF) {K : KnowledgeEnv}
    (hK : K.Sound cat) (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearT (T s) (cat' s).rows (cat s).rows) :
    ∀ {r : Rel} {t : Tol}, r.WF cat → r.tol cat K T = some t →
      Relation.NearT t (r.eval cat') (r.eval cat)
  | .read s, t, _, h => by
    simp only [Rel.tol, Option.some.injEq] at h; subst h; exact hT s
  | .values _ _, t, _, h => by
    simp only [Rel.tol, Option.some.injEq] at h; subst h; exact .refl _ _
  | .filter r c, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact (plan_near hcat hK ha hT hwf.1 hr).filter fun x y r => by rw [Expr.eval_rows (by assumption) r]
    · exact absurd h (by simp)
  | .project r es, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hes
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := (plan_near hcat hK ha hT hwf.1 hr).forall2_mem
        (P := fun y => y.length = r.arity cat ∧ EnvMem (r.analyse cat K).cols y)
        fun y hy => ⟨Rel.eval_arity hcat hwf.1 y hy,
          (Rel.analyse_sound hcat hK hwf.1 (sz := false) (by simp)).1 y hy⟩
      exact ⟨_, fp.map (f := fun row => row ++ es.map (·.eval row))
        (g := fun row => row ++ es.map (·.eval row)) fun x y hxy =>
          Tol.rows_append hxy.1 (Tol.rows_exprsA hes hxy.1 hxy.2.2) hxy.2.1,
        hp.map _⟩
    · exact absurd h (by simp)
  | .emit r m, t, hwf, h => by
    simp only [Rel.tol, Option.map_eq_some_iff] at h
    obtain ⟨t0, hr, rfl⟩ := h
    exact (plan_near hcat hK ha hT hwf.1 hr).map fun x y rxy => Tol.rows_emit rxy m
  | .cross a b, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    have hb := plan_near hcat hK ha hT hwf.2 htb
    exact (plan_near hcat hK ha hT hwf.1 hta).bind_of (Rel.eval_arity hcat hwf.1) fun x y rxy hy =>
      hb.map fun u v ruv => Tol.rows_append rxy ruv hy
  | .join a b jt on, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      have hA := plan_near hcat hK ha hT hwf.1 hta
      have hb := plan_near hcat hK ha hT hwf.2.1 htb
      have hcross : ∀ x y, ta.Rows x y → y.length = a.arity cat →
          Relation.NearT (Tol.cat (a.arity cat) ta tb) ((b.eval cat').map (x ++ ·))
            ((b.eval cat).map (y ++ ·)) :=
        fun x y rxy hy => hb.map fun u v ruv => Tol.rows_append rxy ruv hy
      cases jt with
      | inner =>
        exact (hA.bind_of (Rel.eval_arity hcat hwf.1) hcross).filter fun x y r => by
          rw [Expr.eval_rows hon r]
      | left =>
        simp only [Rel.eval]
        rw [Rel.arity_congr ha b]
        refine hA.bind_of (Rel.eval_arity hcat hwf.1) fun x y rxy hy => ?_
        have hms := (hcross x y rxy hy).filter (P := fun row => (on.eval row).isTrue)
          (P' := fun row => (on.eval row).isTrue) fun u v r => by rw [Expr.eval_rows hon r]
        have hl := hms.length_eq
        unfold leftJoinRow
        simp only
        cases h1 : ((b.eval cat').map (x ++ ·)).filter (fun row => (on.eval row).isTrue) with
        | nil =>
          cases h2 : ((b.eval cat).map (y ++ ·)).filter (fun row => (on.eval row).isTrue) with
          | nil =>
            exact ⟨_, .cons (Tol.rows_append rxy (Tol.rows_refl tb _) hy) .nil, .refl _⟩
          | cons _ _ => rw [h1, h2] at hl; simp at hl
        | cons r rs =>
          cases h2 : ((b.eval cat).map (y ++ ·)).filter (fun row => (on.eval row).isTrue) with
          | nil => rw [h1, h2] at hl; simp at hl
          | cons _ _ => rw [h1, h2] at hms; exact hms
    · exact absurd h (by simp)
  | .fetch .., _, _, h | .window .., _, _, h | .unnest .., _, _, h => by simp [Rel.tol] at h
  | .unionAll a b, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, rfl⟩ := h
    exact ((plan_near hcat hK ha hT hwf.1 hta).mono (Tol.le_max_left ta tb)).append
      ((plan_near hcat hK ha hT hwf.2.1 htb).mono (Tol.le_max_right ta tb))
  | .semi a b anti on, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨ta, hta, tb, htb, h⟩ := h
    split at h
    · rename_i hon
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := plan_near hcat hK ha hT hwf.2.1 htb
      refine (plan_near hcat hK ha hT hwf.1 hta).filter_of (Rel.eval_arity hcat hwf.1)
        fun x y rxy hy => ?_
      simp only [hasMatch]
      rw [fp.any_eq (p' := fun v => (on.eval (y ++ v)).isTrue) fun u v ruv => by
        rw [Expr.eval_rows hon (Tol.rows_append rxy ruv hy)], hp.any_eq]
    · exact absurd h (by simp)
  | .orderBy r _, t, hwf, h => by
    simp only [Rel.tol] at h
    exact ((plan_near hcat hK ha hT hwf.1 h).perm_left (List.mergeSort_perm _ _)).perm_right
      (List.mergeSort_perm _ _).symm
  | .distinct r, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h; subst h
      have hw : r.WF cat := hwf
      obtain ⟨p, fp, hp⟩ := (plan_near hcat hK ha hT hw hr).forall2_mem (Rel.eval_arity hcat hw)
      have : r.eval cat' = p := Forall2.eq (fp.imp fun x y rxy => Tol.rows_eq he rxy.1 rxy.2)
      simp only [Rel.eval, this]
      exact .of_perm (canonReps_perm Row.leRaw_rawOrder hp)
    · exact absurd h (by simp)
  | .aggregate r gs ms, t, hwf, h => by
    simp only [Rel.tol, Option.bind_eq_some_iff] at h
    obtain ⟨t0, hr, h⟩ := h
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨p, fp, hp⟩ := plan_near hcat hK ha hT hwf.1 hr
      have hof : ∀ m ∈ ms, m.orderFree = true := fun m hm => by
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hok.2 _ (List.mem_map_of_mem hm))
        exact Measure.outTol_orderFree ho
      have henv : ∀ row ∈ p, EnvMem (r.analyse cat K).cols row := fun row h' =>
        (Rel.analyse_sound hcat hK hwf.1 (sz := false) (by simp)).1 row (hp.mem_iff.1 h')
      have hN : ∀ n, r.rowsK K = some n → p.length ≤ n := fun n hn => by
        rw [hp.length_eq]; exact Rel.rowsK_sound hK hn
      simp only [Rel.eval]
      exact ⟨_, aggregateEval_near hok.1 hok.2 fp henv hN, aggregateEval_perm hof hp⟩
    · exact absurd h (by simp)

/-! ## The triangle rule and pipelines -/

omit [Boxes.Ambient] in
theorem Tol.le_add_left (t₁ t₂ : Tol) (c : Nat) : OLe (t₁ c) (t₁.add t₂ c) := by
  unfold Tol.add; cases t₁ c <;> cases t₂ c <;> simp [OLe]

omit [Boxes.Ambient] in
theorem Tol.le_add_right (t₁ t₂ : Tol) (c : Nat) : OLe (t₂ c) (t₁.add t₂ c) := by
  unfold Tol.add; cases t₁ c <;> cases t₂ c <;> simp [OLe]

/-- The context of `t` with every column a double. -/
def Tol.dctx (t : Tol) : ObsCtx := ObsCtx.ofTol (fun _ => .double) t

omit [Boxes.Ambient] in
/-- **Cells add along a chain.** -/
theorem Tol.cell_trans {t₁ t₂ : Tol} {i : Nat} {v w z : Value} (h₁ : t₁.Cell i v w)
    (h₂ : t₂.Cell i w z) : (t₁.add t₂).Cell i v z := by
  cases hi : t₁ i with
  | none =>
    rw [(Tol.cell_none hi).1 h₁]; exact Tol.cell_transfer (Tol.le_add_right t₁ t₂ i) h₂
  | some e₁ =>
    cases hj : t₂ i with
    | none =>
      rw [← (Tol.cell_none hj).1 h₂]; exact Tol.cell_transfer (Tol.le_add_left t₁ t₂ i) h₁
    | some e₂ =>
      have hs : ∀ s a b, (fun (_ : StringObs) (a b : String) => a = b) s a b →
          (fun (_ : StringObs) (a b : String) => a = b) s a b := fun _ _ _ x => x
      have hadd : (t₁.add t₂) i = some (e₁ + e₂) := by simp [Tol.add, hi, hj]
      have d₁ : Value.Equiv nearObs t₁.dctx i v w :=
        Value.Equiv.transfer (c := t₁.ctx) (c' := t₁.dctx) (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hi])
          (fun _ _ _ x => x) hs v w h₁
      have d₂ : Value.Equiv nearObs t₂.dctx i w z :=
        Value.Equiv.transfer (c := t₂.ctx) (c' := t₂.dctx) (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hj])
          (fun _ _ _ x => x) hs w z h₂
      have d₃ : Value.Equiv nearObs (t₁.add t₂).dctx i v z :=
        Value.Equiv.trans (c₁ := t₁.dctx) (c₂ := t₂.dctx) (c₃ := (t₁.add t₂).dctx)
          ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ x y => (Tol.near_add x y : (t₁.add t₂).near _ _ _),
            fun _ _ _ _ (x : _ = _) y => x.trans y⟩ v w z d₁ d₂
      exact Value.Equiv.transfer (c := (t₁.add t₂).dctx) (c' := (t₁.add t₂).ctx)
        (by simp [Tol.ctx, Tol.dctx, ObsCtx.ofTol, Tol.kind, hadd]) (fun _ _ _ x => x) hs v z d₃

omit [Boxes.Ambient] in
theorem Tol.rows_trans {t₁ t₂ : Tol} {x y z : Row} (h₁ : t₁.Rows x y) (h₂ : t₂.Rows y z) :
    (t₁.add t₂).Rows x z :=
  ⟨h₁.1.trans h₂.1, fun j => Tol.cell_trans (h₁.2 j) (h₂.2 j)⟩

omit [Boxes.Ambient] in
/-- **The triangle rule**: tolerances add along a chain of results. -/
theorem Relation.NearT.add {t₁ t₂ : Tol} {a b d : Relation} (h₁ : Relation.NearT t₁ a b)
    (h₂ : Relation.NearT t₂ b d) : Relation.NearT (t₁.add t₂) a d := by
  obtain ⟨p, f₁, hp⟩ := h₁
  obtain ⟨q, f₂, hq⟩ := h₂
  obtain ⟨m, hm, fm⟩ := Forall2.perm hp.symm f₂
  exact ⟨m, Forall2.trans (R := t₁.Rows) (S := t₂.Rows) (T := (t₁.add t₂).Rows)
    (fun _ _ _ r s => Tol.rows_trans r s) f₁ fm, hm.symm.trans hq⟩

omit [Boxes.Ambient] in
theorem Relation.NearT.symm {t : Tol} {a b : Relation} (h : Relation.NearT t a b) :
    Relation.NearT t b a := by
  obtain ⟨p, f, hp⟩ := h
  obtain ⟨m, hm, fm⟩ := Forall2.perm hp (f.flip.imp fun _ _ r => (⟨r.1.symm, fun j => Tol.cell_symm (r.2 j)⟩ : t.Rows _ _))
  exact ⟨m, fm, hm.symm⟩

omit [Boxes.Ambient] in
/-- `NearT` gives `Relation.Near` under the plan's own column kinds, as long
as they call every tolerated column a double. -/
theorem Relation.NearT.near {t : Tol} {kind : Nat → ColKind}
    (hk : ∀ c, (t c).isSome → kind c = .double) {a b : Relation} (h : Relation.NearT t a b) :
    Relation.Near kind t a b := by
  obtain ⟨p, f, hp⟩ := h
  refine ⟨p, f.imp fun x y r => ?_, hp⟩
  refine (Row.equivFrom_iff (i := 0)).2 ⟨r.1, fun j => ?_⟩
  simp only [Nat.zero_add]
  cases hj : t j with
  | none =>
    rw [(Tol.cell_none hj).1 (r.2 j)]
    exact Value.Equiv.refl ((ObsCtx.ofTol_wf kind t).reflAt _) _
  | some e =>
    exact Value.Equiv.transfer (c := t.ctx) (c' := ObsCtx.ofTol kind t)
      (by show t.kind j = kind j; simp [Tol.kind, hj, hk j (by simp [hj])])
      (fun _ _ _ x => x) (fun _ _ _ x => x) _ _ (r.2 j)

/-- **A pipeline (#929 `Triple.ε`).** Node `g`'s engine output `Eg` is
within `tg` of its reference output `Rg`; node `f` reads it as table `x`.
The engine's output `Ef` of `f`, within `rf` of the reference's `f` on the
engine's inputs (its own rounding, `contract_sound_allowed`'s `ε`), is within
`rf + Rel.tol` of the reference pipeline's output: `εₖ = Lₖ·εₖ₋₁ + rₖ`, with
`g`'s bound as `x`'s source tolerance. -/
theorem Rel.pipeline_near {cat cat' : Catalog} (hcat : cat.WF)
    (ha : ∀ s, (cat' s).arity = (cat s).arity) {T : String → Tol}
    (hT : ∀ s, Relation.NearT (T s) (cat' s).rows (cat s).rows)
    {x : String} {n : Nat} {Eg Rg : Relation} {tg : Tol} (hg : Relation.NearT tg Eg Rg)
    (hRg : ∀ row ∈ Rg, row.length = n) {K : KnowledgeEnv}
    (hK : K.Sound (cat.bind x ⟨n, Rg⟩))
    {f : Rel} (hf : f.WF (cat.bind x ⟨n, Rg⟩)) {tf : Tol}
    (htf : f.tol (cat.bind x ⟨n, Rg⟩) K (fun s => if s = x then tg else T s) = some tf)
    {rf : Tol} {Ef : Relation} (hE : Relation.NearT rf Ef (f.eval (cat'.bind x ⟨n, Eg⟩))) :
    Relation.NearT (rf.add tf) Ef (f.eval (cat.bind x ⟨n, Rg⟩)) := by
  refine hE.add (Rel.plan_near (Catalog.bind_wf hcat hRg) hK (fun s => ?_) (fun s => ?_) hf htf)
  · unfold Catalog.bind; split <;> simp [ha]
  · unfold Catalog.bind
    by_cases h : s = x
    · simp only [h, ite_true]; exact hg
    · simp only [h, ite_false]; exact hT s

/-! ## `M₁`: a budget summed over the matching -/

/-- `t` at least as tight as `t'` in every column. -/
def Tol.Le (t t' : Tol) : Prop := ∀ c, OLe (t c) (t' c)

/-- Matched rows whose distances sum, per column, within the budget `t`:
the first pair is within `tr`, the others within `rest`, and `tr + rest`
within `t`. A column `t` leaves exact is exact in every pair. -/
def PairsWithin : List Row → List Row → Tol → Prop
  | [], [], _ => True
  | x :: xs, y :: ys, t => ∃ tr rest : Tol, tr.Rows x y ∧ PairsWithin xs ys rest ∧ (tr.add rest).Le t
  | _, _, _ => False

/-- **The `M₁` metric (#929)**: a permutation, then rows matched pairwise
whose distances in each double column sum to at most `t` of it. What a
downstream `SUM` over the column sees: its value moves by at most the sum. -/
def Relation.NearL1 (t : Tol) (a b : Relation) : Prop :=
  ∃ p, PairsWithin a p t ∧ p.Perm b

section
variable {t t' t₁ t₂ : Tol}

omit [Boxes.Ambient] in
theorem Tol.Le.refl (t : Tol) : t.Le t := fun _ => OLe.refl _

omit [Boxes.Ambient] in
theorem Tol.Le.trans {t₃ : Tol} (h₁ : t₁.Le t₂) (h₂ : t₂.Le t₃) : t₁.Le t₃ := fun c => by
  have a := h₁ c; have b := h₂ c
  revert a b; cases t₁ c <;> cases t₂ c <;> cases t₃ c <;> simp [OLe] <;> omega

omit [Boxes.Ambient] in
theorem Tol.exact_add (t : Tol) : (Tol.exact.add t).Le t := fun c => by
  simp only [Tol.add, Tol.exact]; cases t c <;> simp [OLe]

omit [Boxes.Ambient] in
/-- Budgets in a different order. -/
theorem Tol.add_swap (a b r : Tol) : (a.add (b.add r)).Le (b.add (a.add r)) := fun c => by
  simp only [Tol.add]; cases a c <;> cases b c <;> cases r c <;> simp [OLe] <;> omega

omit [Boxes.Ambient] in
theorem Tol.add_mono {a b a' b' : Tol} (ha : a.Le a') (hb : b.Le b') : (a.add b).Le (a'.add b') :=
  fun c => by
    have x := ha c; have y := hb c
    revert x y; simp only [Tol.add]
    cases a c <;> cases b c <;> cases a' c <;> cases b' c <;> simp [OLe] <;> omega

omit [Boxes.Ambient] in
/-- Two chains' budgets, pair by pair. -/
theorem Tol.add_four (a b c d : Tol) : ((a.add c).add (b.add d)).Le ((a.add b).add (c.add d)) :=
  fun k => by
    simp only [Tol.add]; cases a k <;> cases b k <;> cases c k <;> cases d k <;> simp [OLe] <;> omega

omit [Boxes.Ambient] in
theorem PairsWithin.mono : ∀ {a p : List Row} {t t' : Tol}, PairsWithin a p t → t.Le t' →
    PairsWithin a p t'
  | [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _, _, ⟨tr, rest, r, h, le⟩, ht => ⟨tr, rest, r, h, le.trans ht⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

omit [Boxes.Ambient] in
theorem PairsWithin.refl : ∀ (a : List Row) (t : Tol), PairsWithin a a t
  | [], _ => trivial
  | x :: xs, t => ⟨Tol.exact, t, Tol.rows_refl _ x, PairsWithin.refl xs t, Tol.exact_add t⟩

omit [Boxes.Ambient] in
theorem PairsWithin.symm : ∀ {a p : List Row} {t : Tol}, PairsWithin a p t → PairsWithin p a t
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, _, ⟨tr, rest, r, h, le⟩ =>
    ⟨tr, rest, ⟨r.1.symm, fun j => Tol.cell_symm (r.2 j)⟩, PairsWithin.symm h, le⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

omit [Boxes.Ambient] in
/-- A permutation of the left side carries over to the right. -/
theorem PairsWithin.perm {a a' : List Row} (hp : a.Perm a') :
    ∀ {p : List Row} {t : Tol}, PairsWithin a p t → ∃ p', p.Perm p' ∧ PairsWithin a' p' t := by
  induction hp with
  | nil => intro p t h; cases p with
    | nil => exact ⟨[], .nil, trivial⟩
    | cons _ _ => exact h.elim
  | cons x _ ih =>
    intro p t h
    cases p with
    | nil => exact h.elim
    | cons y ys =>
      obtain ⟨tr, rest, r, h, le⟩ := h
      obtain ⟨q, hq, h'⟩ := ih h
      exact ⟨y :: q, hq.cons y, tr, rest, r, h', le⟩
  | swap x₁ x₂ l =>
    intro p t h
    match p, h with
    | y₂ :: y₁ :: ys, ⟨tr₂, rest₂, r₂, ⟨tr₁, rest₁, r₁, h, le₁⟩, le₂⟩ =>
      exact ⟨y₁ :: y₂ :: ys, .swap _ _ _, tr₁, tr₂.add rest₁, r₁,
        ⟨tr₂, rest₁, r₂, h, Tol.Le.refl _⟩,
        (Tol.add_swap tr₁ tr₂ rest₁).trans ((Tol.add_mono (Tol.Le.refl tr₂) le₁).trans le₂)⟩
  | trans _ _ ih₁ ih₂ =>
    intro p t h
    obtain ⟨q₁, hq₁, h₁⟩ := ih₁ h
    obtain ⟨q₂, hq₂, h₂⟩ := ih₂ h₁
    exact ⟨q₂, hq₁.trans hq₂, h₂⟩

omit [Boxes.Ambient] in
theorem PairsWithin.trans : ∀ {a b d : List Row} {t₁ t₂ : Tol}, PairsWithin a b t₁ →
    PairsWithin b d t₂ → PairsWithin a d (t₁.add t₂)
  | [], [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, _, _, ⟨tr₁, rest₁, r₁, h₁, le₁⟩, ⟨tr₂, rest₂, r₂, h₂, le₂⟩ =>
    ⟨tr₁.add tr₂, rest₁.add rest₂, Tol.rows_trans r₁ r₂, PairsWithin.trans h₁ h₂,
      (Tol.add_four tr₁ rest₁ tr₂ rest₂).trans (Tol.add_mono le₁ le₂)⟩
  | [], [], _ :: _, _, _, _, h | _ :: _, _ :: _, [], _, _, _, h => h.elim
  | [], _ :: _, _, _, _, h, _ | _ :: _, [], _, _, _, h, _ => h.elim

omit [Boxes.Ambient] in
theorem Relation.NearL1.refl (t : Tol) (a : Relation) : Relation.NearL1 t a a :=
  ⟨a, PairsWithin.refl a t, .refl a⟩

omit [Boxes.Ambient] in
theorem Relation.NearL1.symm {a b : Relation} (h : Relation.NearL1 t a b) : Relation.NearL1 t b a := by
  obtain ⟨p, hw, hp⟩ := h
  obtain ⟨q, hq, h'⟩ := PairsWithin.perm hp hw.symm
  exact ⟨q, h', hq.symm⟩

omit [Boxes.Ambient] in
/-- **The triangle rule in `M₁`**: budgets add along a chain of results. -/
theorem Relation.NearL1.add {a b d : Relation} (h₁ : Relation.NearL1 t₁ a b)
    (h₂ : Relation.NearL1 t₂ b d) : Relation.NearL1 (t₁.add t₂) a d := by
  obtain ⟨p, w₁, hp⟩ := h₁
  obtain ⟨q, w₂, hq⟩ := h₂
  obtain ⟨q', hq', w₂'⟩ := PairsWithin.perm hp.symm w₂
  exact ⟨q', w₁.trans w₂', hq'.symm.trans hq⟩

omit [Boxes.Ambient] in
theorem Relation.NearL1.mono (ht : t.Le t') {a b : Relation} (h : Relation.NearL1 t a b) :
    Relation.NearL1 t' a b :=
  let ⟨p, w, hp⟩ := h; ⟨p, w.mono ht, hp⟩

end

/-! ## Examples

A table `t` of three columns whose third, a double, is within 8 codes. -/

private def exCat : Catalog := fun _ => ⟨3, []⟩
private def exT : String → Tol := fun _ c => if c = 2 then some 8 else none
private def exCols (r : Rel) : Option (List (Option Nat)) :=
  (r.tol exCat (fun _ => ⟨[], [], [], none⟩) exT).map fun t => (List.range 4).map t

-- Pass-through and emit carry the tolerance; an exact filter keeps it.
#guard letI := Boxes.Ambient.none; exCols (.emit (.filter (.read "t") (.bin .lt (.field 0) (.lit (.int 5)))) [2, 0]) ==
  some [some 8, none, none, none]
-- A filter on the tolerated column is refused (#568, `rows_exact`).
#guard letI := Boxes.Ambient.none; exCols (.filter (.read "t") (.bin .lt (.field 2) (.lit (.int 5)))) == none
-- A projection: the column passes through, an expression of exact columns is exact.
#guard letI := Boxes.Ambient.none; exCols (.project (.read "t") [.field 2, .bin .add (.field 0) (.field 1)]) ==
  some [none, none, some 8, some 8]
-- `UNION ALL` takes the larger tolerance, a cross shifts the right side's.
#guard letI := Boxes.Ambient.none; exCols (.unionAll (.read "t") (.emit (.read "t") [2, 2, 2])) == some [some 8, some 8, some 8, none]
#guard letI := Boxes.Ambient.none; exCols (.cross (.read "t") (.read "t")) == some [none, none, some 8, none]
-- `COUNT` grouped by an exact column is exact; grouping by the double is refused.
#guard letI := Boxes.Ambient.none; exCols (.aggregate (.read "t") [.field 0] [{ fn := .count, arg := .lit (.int 1) }]) ==
  some [none, none, none, none]
#guard letI := Boxes.Ambient.none; exCols (.aggregate (.read "t") [.field 2] [{ fn := .count, arg := .lit (.int 1) }]) == none
-- `FETCH` reads an order the multiset observation does not fix.
#guard letI := Boxes.Ambient.none; exCols (.fetch (.read "t") 0 (some 1)) == none

/-- The table's knowledge: at most 1000 rows, the double in `[-10⁶, 10⁶]`. -/
private def exK : KnowledgeEnv := fun _ =>
  ⟨[AVal.top, AVal.top, AVal.num false ⟨some (FloatCode.ofFloat (-1.0e6)), some (FloatCode.ofFloat 1.0e6)⟩ .float],
    [], [], some 1000⟩
/-- Which of the first four output columns are tolerated, under `exK`. -/
private def exSum (r : Rel) : Option (List Bool) :=
  (r.tol exCat exK exT).map fun t => (List.range 4).map fun c => (t c).isSome

-- `SUM` and `AVG` of the tolerated double, grouped by an exact column, are tolerated.
#guard letI := Boxes.Ambient.none; exSum (.aggregate (.read "t") [.field 0] [{ fn := .fsum, arg := .field 2 }, { fn := .avg, arg := .field 2 }]) ==
  some [false, true, true, false]
-- Without a range for the double, or of a `DISTINCT` or a computed argument, refused.
#guard letI := Boxes.Ambient.none; exCols (.aggregate (.read "t") [.field 0] [{ fn := .fsum, arg := .field 2 }]) == none
#guard letI := Boxes.Ambient.none; exSum (.aggregate (.read "t") [] [{ fn := .fsum, arg := .field 2, distinct := true }]) == none
#guard letI := Boxes.Ambient.none; exSum (.aggregate (.read "t") [] [{ fn := .fsum, arg := .un .fneg (.field 2) }]) == none
-- `MIN` and `MAX` of the double, of doubles only in a range of reference codes, carry its tolerance.
#guard letI := Boxes.Ambient.none; exSum (.aggregate (.read "t") [] [{ fn := .min, arg := .field 2 }, { fn := .max, arg := .field 2 }]) ==
  some [true, true, false, false]
#guard letI := Boxes.Ambient.none; exCols (.aggregate (.read "t") [] [{ fn := .min, arg := .field 2 }]) == none

-- The arithmetic rows (D31): `x + x`, `2 · x`, `x / 4` of the tolerated double are tolerated,
-- and so is a `SUM` over a computed column; a product with an exact column of no range is refused.
#guard letI := Boxes.Ambient.none; exSum (.project (.read "t") [.bin .fadd (.field 2) (.field 2), .bin .fmul (.lit (.float (FloatCode.ofFloat 2.0))) (.field 2)]) ==
  some [false, false, true, true]
#guard letI := Boxes.Ambient.none; exSum (.project (.read "t") [.bin .fdiv (.field 2) (.lit (.float (FloatCode.ofFloat 4.0)))]) ==
  some [false, false, true, true]
#guard letI := Boxes.Ambient.none; exSum (.aggregate (.project (.read "t") [.bin .fmul (.lit (.float (FloatCode.ofFloat 2.0))) (.field 2)]) []
  [{ fn := .fsum, arg := .field 3 }]) == some [true, false, false, false]
#guard letI := Boxes.Ambient.none; exSum (.project (.read "t") [.bin .fmul (.field 0) (.field 2)]) == none

/-- As `exK`, with the first column a double in `[1, 100]`, clear of zero. -/
private def exK2 : KnowledgeEnv := fun _ =>
  ⟨[AVal.num false ⟨some (FloatCode.ofFloat 1.0), some (FloatCode.ofFloat 100.0)⟩ .float, AVal.top,
    AVal.num false ⟨some (FloatCode.ofFloat (-1.0e6)), some (FloatCode.ofFloat 1.0e6)⟩ .float],
    [], [], some 1000⟩
private def exSum2 (r : Rel) : Option (List Bool) :=
  (r.tol exCat exK2 exT).map fun t => (List.range 4).map fun c => (t c).isSome

-- `x / y` with `y`'s range clear of zero is tolerated; a divisor whose range holds zero is refused.
#guard letI := Boxes.Ambient.none; exSum2 (.project (.read "t") [.bin .fdiv (.field 2) (.field 0)]) == some [false, false, true, true]
#guard letI := Boxes.Ambient.none; exSum2 (.project (.read "t") [.bin .fdiv (.field 0) (.field 2)]) == none

private def tie : Tol := fun c => if c = 0 then some 2 else none

/-- A near tie (#929 step 6): the doubles of two rows with the same exact
column swap order under a perturbation of 2 codes. Sorting both results and
comparing row by row pairs `"a"` with `"b"`; the matching pairs each row with
its own. `allows_rows` decides the same (`tests/test_ties.py`). -/
example : Relation.NearT tie
    [[.int 100, .str "a"], [.int 102, .str "b"]] [[.int 102, .str "a"], [.int 100, .str "b"]] := by
  have hc : ∀ (x y : Int) (s : String), tie.Rows [.int x, .str s] [.int y, .str s] ↔
      (fp64.canon x - fp64.canon y).natAbs ≤ 2 := by
    intro x y s
    refine ⟨fun h => h.2 0, fun h => ⟨rfl, fun j => ?_⟩⟩
    match j with
    | 0 => exact h
    | 1 => exact (Tol.cell_none (by simp [tie])).2 rfl
    | _ + 2 => exact Tol.cell_null _ _
  refine ⟨[[.int 102, .str "a"], [.int 100, .str "b"]],
    .cons ((hc _ _ _).2 ?_) (.cons ((hc _ _ _).2 ?_) .nil), .refl _⟩ <;>
    rw [fp64.canon_eq_self (by have := fp64.negZero_eq; have := fp64.negNan_eq; omega),
      fp64.canon_eq_self (by have := fp64.negZero_eq; have := fp64.negNan_eq; omega)] <;> decide

end Substrait
