import Sverify.Engines.Lowering
import Sverify.Engines.Transfer

/-!
# Where a lowered plan raises

A lowered plan raises only where the reference may (`Lowering.lowerRel_raises`,
`Lowering.lowerRel?_raises` for a partial table), since each entry agrees with
the reference (`Lowering.lower_correct`). With `Rel.hasIssue_of_raises`
(`analysis/Sverify/Analysis/ProfileImpl.lean`), a report with only assumed issues
discharges an engine's no-raise side condition: DuckDB's (`Engine.duckdb_sound`)
and Polars's guard-free run (`Rel.polars_sound`).
-/

namespace Substrait

variable [Boxes.Ambient]

omit [Boxes.Ambient] in
theorem Measure.mem_mapExpr_exprs {f : Expr → Expr} (hf : ∀ i, f (.field i) = .field i)
    {m : Measure} {e' : Expr} (h : e' ∈ (m.mapExpr f).exprs) : ∃ e ∈ m.exprs, f e = e' := by
  rw [Measure.mapExpr_exprs] at h
  simp only [List.mem_cons, List.mem_append, List.mem_map] at h
  rcases h with (rfl | ⟨e, he, rfl⟩) | ⟨k, hk, rfl⟩
  · exact ⟨m.arg, List.mem_cons_self .., rfl⟩
  · exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), rfl⟩
  · exact ⟨.field k.col, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hk)), hf _⟩

/-- **A plan whose expressions raise only where the originals do raises only
where the original does.** With `q`'s functions giving `Rel.eval`'s rows
where `q` does not raise, the rows each translated expression is evaluated on
are rows the original one is evaluated on. `f` need only be exact on the
plan's own expressions (`Q`), as for a partial table, and only on the rows
they are evaluated on (`R`, `Rel.ExprRows`), as for entries stated on doubles
(`Rel.evalI_mapExprs_rows`). -/
theorem Rel.raises_mapExprs_rows {p q : Profile} {f : Expr → Expr} {Q : Expr → Prop}
    {R : Row → Prop} (hx : ∀ e, Q e → ∀ row, R row → Expr.ExactAt p (f e) e row)
    (hf : ∀ i, f (.field i) = .field i)
    (hr : ∀ e row, Q e → R row → (f e).RaisesOn p row → e.RaisesOn q row) {cat : Catalog}
    (hq : ∀ r : Rel, ¬r.Raises q cat → r.eval cat q.impl = r.eval cat) :
    ∀ {r : Rel}, r.ExprRows R cat → (∀ e ∈ r.mappedExprs, Q e) → (r.mapExprs f).Raises p cat →
      r.Raises q cat
  | .read _, _, _, h | .values _ _, _, _, h => h.elim
  | .filter r c, hR, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_cons_of_mem _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_rows hx hf hr hq hR.1 hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_rows hx hf hR.1 hQr (fun h' => h0 (ih h'))] at hrow
        exact ⟨row, by rw [hq r h0]; exact hrow,
          hr c row (hQ c (List.mem_cons_self ..)) (hR.2 row hrow) hc⟩
  | .project r es, hR, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_rows hx hf hr hq hR.1 hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_rows hx hf hR.1 hQr (fun h' => h0 (ih h'))] at hrow
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        exact ⟨row, by rw [hq r h0]; exact hrow, e, he,
          hr e row (hQ e (List.mem_append_left _ he)) (hR.2 row hrow) hc⟩
  | .emit r _, hR, hQ, h | .orderBy r _, hR, hQ, h | .distinct r, hR, hQ, h
  | .unnest r _, hR, hQ, h | .window r _ _ _, hR, hQ, h | .fetch r _ _, hR, hQ, h => by
    simp only [mapExprs, Raises] at h ⊢
    exact raises_mapExprs_rows hx hf hr hq hR (fun e he => hQ e he) h
  | .cross a b, hR, hQ, h | .unionAll a b, hR, hQ, h => by
    have hQa : ∀ e ∈ a.mappedExprs, Q e := fun e he => hQ e (List.mem_append_left _ he)
    have hQb : ∀ e ∈ b.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    exact h.imp (raises_mapExprs_rows hx hf hr hq hR.1 hQa)
      (raises_mapExprs_rows hx hf hr hq hR.2 hQb)
  | .join a b _ on, hR, hQ, h | .semi a b _ on, hR, hQ, h => by
    have hQa : ∀ e ∈ a.mappedExprs, Q e := fun e he =>
      hQ e (List.mem_cons_of_mem _ (List.mem_append_left _ he))
    have hQb : ∀ e ∈ b.mappedExprs, Q e := fun e he =>
      hQ e (List.mem_cons_of_mem _ (List.mem_append_right _ he))
    simp only [mapExprs, Raises] at h ⊢
    have iha := raises_mapExprs_rows hx hf hr hq hR.1 hQa
    have ihb := raises_mapExprs_rows hx hf hr hq hR.2.1 hQb
    by_cases ha : a.Raises q cat
    · exact .inl ha
    · by_cases hb : b.Raises q cat
      · exact .inr (.inl hb)
      · refine .inr (.inr ?_)
        rcases h with h | h | ⟨x, hx', y, hy, hc⟩
        · exact absurd (iha h) ha
        · exact absurd (ihb h) hb
        · rw [evalI_mapExprs_rows hx hf hR.1 hQa (fun h' => ha (iha h'))] at hx'
          rw [evalI_mapExprs_rows hx hf hR.2.1 hQb (fun h' => hb (ihb h'))] at hy
          exact ⟨x, by rw [hq a ha]; exact hx', y, by rw [hq b hb]; exact hy,
            hr on _ (hQ on (List.mem_cons_self ..)) (hR.2.2 x hx' y hy) hc⟩
  | .aggregate r gs ms, hR, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_rows hx hf hr hq hR.1 hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_rows hx hf hR.1 hQr (fun h' => h0 (ih h'))] at hrow
        have hRr := hR.2 row hrow
        refine ⟨row, by rw [hq r h0]; exact hrow, ?_⟩
        simp only [List.mem_append, List.mem_flatMap, List.mem_map] at he'
        rcases he' with ⟨e, he, rfl⟩ | ⟨m', hm', he'⟩
        · exact ⟨e, List.mem_append_left _ he,
            hr e row (hQ e (List.mem_append_left _ (List.mem_append_left _ he))) hRr hc⟩
        · obtain ⟨m, hm, rfl⟩ := hm'
          obtain ⟨e, he, rfl⟩ := Measure.mem_mapExpr_exprs hf he'
          have hme : e ∈ ms.flatMap Measure.exprs := List.mem_flatMap.mpr ⟨m, hm, he⟩
          exact ⟨e, List.mem_append_right _ hme,
            hr e row (hQ e (List.mem_append_left _ (List.mem_append_right _ hme))) hRr hc⟩

/-- `Rel.raises_mapExprs_rows` on every row: `f` exact on the plan's own
expressions. -/
theorem Rel.raises_mapExprs_on {p q : Profile} {f : Expr → Expr} {Q : Expr → Prop}
    (hx : ∀ e, Q e → Expr.Exact p (f e) e) (hf : ∀ i, f (.field i) = .field i)
    (hr : ∀ e row, Q e → (f e).RaisesOn p row → e.RaisesOn q row) {cat : Catalog}
    (hq : ∀ r : Rel, ¬r.Raises q cat → r.eval cat q.impl = r.eval cat) {r : Rel}
    (hQ : ∀ e ∈ r.mappedExprs, Q e) (h : (r.mapExprs f).Raises p cat) : r.Raises q cat :=
  raises_mapExprs_rows (R := fun _ => True) (fun e he row _ v hv => hx e he row v hv) hf
    (fun e row he _ => hr e row he) hq (Rel.exprRows_true cat r) hQ h

theorem Rel.raises_mapExprs {p q : Profile} {f : Expr → Expr} (hx : ∀ e, Expr.Exact p (f e) e)
    (hf : ∀ i, f (.field i) = .field i)
    (hr : ∀ e row, (f e).RaisesOn p row → e.RaisesOn q row) {cat : Catalog}
    (hq : ∀ r : Rel, ¬r.Raises q cat → r.eval cat q.impl = r.eval cat) {r : Rel}
    (h : (r.mapExprs f).Raises p cat) : r.Raises q cat :=
  raises_mapExprs_on (Q := fun _ => True) (fun e _ => hx e) hf (fun e row _ => hr e row) hq
    (fun _ _ => trivial) h

/-- A lowered expression raises only where the reference does (`agree`), for a
table whose entries are exact (ruling 252). -/
theorem Lowering.lowerE_raises {p : Profile} {L : Lowering p} (hL : L.Total) (hX : L.AllExact)
    (hN : L.NoneOnDbl) (e : Expr) (row : Row)
    (h : (L.lowerE e).RaisesOn p row) : e.RaisesOn Profile.reference row := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (lower_isSome hL e)
  have hc := L.lower_correct e t ht row (exactOn_of_allExact hX e) (.inl (dblFree_of_noneOnDbl hN e))
  simp only [lowerE, ht, Option.getD_some, Expr.RaisesOn] at h ⊢
  revert h hc
  cases t.evalP p row <;> cases e.evalP Profile.reference row <;>
    simp [Outcome.Agree, Outcome.err?]

/-- **A lowered plan raises only where the reference may.** -/
theorem Lowering.lowerRel_raises {p : Profile} {L : Lowering p} (hL : L.Total) (hX : L.AllExact)
    (hN : L.NoneOnDbl) {cat : Catalog} {r : Rel} (h : (L.lowerRel r).Raises p cat) :
    r.Raises Profile.reference cat :=
  Rel.raises_mapExprs (lowerE_exact hL hN) (fun _ => rfl) (lowerE_raises hL hX hN)
    (fun _ h => Rel.evalI_reference h) h

/-- A lowered expression raises only where the reference does, wherever the
partial table lowers it and its entries are exact. -/
theorem Lowering.lowerE_raises_of {p : Profile} (L : Lowering p) {e : Expr}
    (he : (L.lower e).isSome) (hX : L.exactOn e = true) (row : Row) (hD : L.ArgsOk e row)
    (h : (L.lowerE e).RaisesOn p row) : e.RaisesOn Profile.reference row := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp he
  have hc := L.lower_correct e t ht row hX hD
  simp only [lowerE, ht, Option.getD_some, Expr.RaisesOn] at h ⊢
  revert h hc
  cases t.evalP p row <;> cases e.evalP Profile.reference row <;>
    simp [Outcome.Agree, Outcome.err?]

/-- **A plan the partial table lowers raises only where the reference may**,
as `Lowering.lowerRel_raises` for a table that need not be total. -/
theorem Lowering.lowerRel?_raises {p : Profile} {L : Lowering p} (hX : L.AllExact)
    (hN : L.NoneOnDbl) {cat : Catalog} {r r' : Rel} (hr : L.lowerRel? r = .ok r')
    (h : r'.Raises p cat) : r.Raises Profile.reference cat := by
  unfold lowerRel? at hr
  split at hr
  · rename_i hall
    cases hr
    exact Rel.raises_mapExprs_on (Q := fun e => (L.lower e).isSome = true)
      (fun _ he => L.lowerE_exact_of hN he) (fun _ => rfl)
      (fun e row he => L.lowerE_raises_of he (exactOn_of_allExact hX e) row
        (.inl (dblFree_of_noneOnDbl hN e)))
      (fun _ h => Rel.evalI_reference h) (fun e he => List.all_eq_true.mp hall e he) h
  · cases hr

/-- Every expression of the plan is lowered by exact entries (`Lowering.exactOn`):
decidable, and for Spark's table false exactly where the plan calls IEEE
division, whose entry is one-sided (ruling 277). -/
def Rel.ExactOnB {p : Profile} (r : Rel) (L : Lowering p) : Bool := r.mappedExprs.all L.exactOn

theorem Rel.exactOn_of_exactOnB {p : Profile} {L : Lowering p} {r : Rel}
    (h : r.ExactOnB L = true) : ∀ e ∈ r.mappedExprs, L.exactOn e = true :=
  List.all_eq_true.mp h

/-- `Rel.ConstsDbl` as a check: the checker runs it on every plan (ruling 277 Q2). -/
def Rel.constsDblB (r : Rel) : Bool := r.litDbl && r.mappedExprs.all Expr.litDbl

omit [Boxes.Ambient] in
theorem Rel.constsDbl_of_constsDblB {r : Rel} (h : r.constsDblB = true) : r.ConstsDbl := by
  simp only [Rel.constsDblB, Bool.and_eq_true, List.all_eq_true] at h
  exact h

/-- **A plan the partial table lowers raises only where the reference may, on
doubles**: `Lowering.lowerRel?_raises` for a table whose entries need not all
be exact or stated on every value. The plan's own expressions are exact
(`exactOn`), and on a catalog of doubles a plan with doubles for constants is
evaluated on rows of doubles only (`Rel.exprRows_dbl`), where every entry
agrees (ruling 277). -/
theorem Lowering.lowerRel?_raises_dbl {p : Profile} {L : Lowering p} {cat : Catalog}
    (hcat : cat.Dbl) {r r' : Rel} (hc : r.ConstsDbl)
    (hx : ∀ e ∈ r.mappedExprs, L.exactOn e = true) (hr : L.lowerRel? r = .ok r')
    (h : r'.Raises p cat) : r.Raises Profile.reference cat := by
  unfold lowerRel? at hr
  split at hr
  · rename_i hall
    cases hr
    exact Rel.raises_mapExprs_rows
      (Q := fun e => (L.lower e).isSome = true ∧ e.litDbl = true ∧ L.exactOn e = true)
      (R := Row.Dbl) (fun _ he _ hrow => L.lowerE_exactAt_of he.1 (.inr ⟨hrow, he.2.1⟩))
      (fun _ => rfl)
      (fun e row he hrow => L.lowerE_raises_of he.1 he.2.2 row (.inr ⟨hrow, he.2.1⟩))
      (fun _ h => Rel.evalI_reference h) (Rel.exprRows_dbl hcat r hc.1)
      (fun e he => ⟨List.all_eq_true.mp hall e he, hc.2 e he, hx e he⟩) h
  · cases hr

omit [Boxes.Ambient] in
/-- Each expression of a mapped plan is the map of one of the plan's own (a
measure's sort keys stay columns). -/
theorem Rel.mem_mappedExprs_mapExprs {f : Expr → Expr} (hf : ∀ i, f (.field i) = .field i) :
    ∀ (r : Rel) {e' : Expr}, e' ∈ (r.mapExprs f).mappedExprs → ∃ e ∈ r.mappedExprs, f e = e'
  | .read _, _, h | .values _ _, _, h => by simp [mapExprs, mappedExprs] at h
  | .filter r c, _, h => by
    simp only [mapExprs, mappedExprs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, List.mem_cons_self .., rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf r h
      exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩
  | .project r es, _, h => by
    simp only [mapExprs, mappedExprs, List.mem_append, List.mem_map] at h
    rcases h with ⟨e, he, rfl⟩ | h
    · exact ⟨e, List.mem_append_left _ he, rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf r h
      exact ⟨e, List.mem_append_right _ he, rfl⟩
  | .emit r _, _, h | .fetch r _ _, _, h | .orderBy r _, _, h | .distinct r, _, h
  | .unnest r _, _, h | .window r _ _ _, _, h => by
    simp only [mapExprs, mappedExprs] at h
    exact mem_mappedExprs_mapExprs hf r h
  | .cross a b, _, h | .unionAll a b, _, h => by
    simp only [mapExprs, mappedExprs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf a h
      exact ⟨e, List.mem_append_left _ he, rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf b h
      exact ⟨e, List.mem_append_right _ he, rfl⟩
  | .join a b _ on, _, h | .semi a b _ on, _, h => by
    simp only [mapExprs, mappedExprs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact ⟨on, List.mem_cons_self .., rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf a h
      exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf b h
      exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_right _ he), rfl⟩
  | .aggregate r gs ms, _, h => by
    simp only [mapExprs, mappedExprs, List.mem_append, List.mem_flatMap, List.mem_map] at h
    rcases h with (⟨e, he, rfl⟩ | ⟨m', ⟨m, hm, rfl⟩, he'⟩) | h
    · exact ⟨e, List.mem_append_left _ (List.mem_append_left _ he), rfl⟩
    · obtain ⟨e, he, rfl⟩ := Measure.mem_mapExpr_exprs hf he'
      exact ⟨e, List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, he⟩)),
        rfl⟩
    · obtain ⟨e, he, rfl⟩ := mem_mappedExprs_mapExprs hf r h
      exact ⟨e, List.mem_append_right _ he, rfl⟩

/-- The expressions of a plan the partial table lowers are lowered ones. -/
theorem Lowering.mem_lowerRel? {p : Profile} {L : Lowering p} {r r' : Rel}
    (hr : L.lowerRel? r = .ok r') {e' : Expr} (he' : e' ∈ r'.mappedExprs) :
    ∃ e t, L.lower e = some t ∧ e' = t := by
  unfold lowerRel? at hr
  split at hr
  · rename_i hall
    cases hr
    obtain ⟨e, he, rfl⟩ := Rel.mem_mappedExprs_mapExprs (f := L.lowerE) (fun _ => rfl) _ he'
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall e he)
    exact ⟨e, t, ht, by simp [lowerE, ht]⟩
  · cases hr

/-! ## The functions a lowered expression calls -/

omit [Boxes.Ambient] in
theorem Expr.ctors_shift (n : Nat) : ∀ e : Expr, (e.shift n).ctors = e.ctors
  | .lit _ | .field _ => rfl
  | .un f a => by simp [Expr.shift, Expr.ctors, Expr.ctors_shift n a]
  | .bin f a b => by simp [Expr.shift, Expr.ctors, Expr.ctors_shift n a, Expr.ctors_shift n b]
  | .ifThen c t e => by
    simp [Expr.shift, Expr.ctors, Expr.ctors_shift n c, Expr.ctors_shift n t, Expr.ctors_shift n e]
  | .hof f l b => by simp [Expr.shift, Expr.ctors, Expr.ctors_shift n l, Expr.ctors_shift (n + 1) b]

omit [Boxes.Ambient] in
/-- A substitution calls only its template's functions and its arguments'. -/
theorem Expr.not_mem_ctors_subst {c : Functions.Ctor} :
    ∀ {t : Expr} {σ : List Expr}, c ∉ t.ctors → (∀ s ∈ σ, c ∉ s.ctors) → c ∉ (t.subst σ).ctors
  | .lit _, _, _, _ => by simp [Expr.subst, Expr.ctors]
  | .field i, σ, _, hσ => by
    simp only [Expr.subst, List.getD_eq_getElem?_getD]
    cases hi : σ[i]? with
    | none => simp [Expr.ctors]
    | some s => exact hσ s (List.mem_of_getElem? hi)
  | .un f a, σ, ht, hσ => by
    simp only [Expr.ctors, List.mem_cons, not_or] at ht
    simp only [Expr.subst, Expr.ctors, List.mem_cons, not_or]
    exact ⟨ht.1, not_mem_ctors_subst ht.2 hσ⟩
  | .bin f a b, σ, ht, hσ => by
    simp only [Expr.ctors, List.mem_cons, List.mem_append, not_or] at ht
    simp only [Expr.subst, Expr.ctors, List.mem_cons, List.mem_append, not_or]
    exact ⟨ht.1, not_mem_ctors_subst ht.2.1 hσ, not_mem_ctors_subst ht.2.2 hσ⟩
  | .ifThen c' t e, σ, ht, hσ => by
    simp only [Expr.ctors, List.mem_append, not_or] at ht
    simp only [Expr.subst, Expr.ctors, List.mem_append, not_or]
    exact ⟨⟨not_mem_ctors_subst ht.1.1 hσ, not_mem_ctors_subst ht.1.2 hσ⟩,
      not_mem_ctors_subst ht.2 hσ⟩
  | .hof f l b, σ, ht, hσ => by
    simp only [Expr.ctors, List.mem_append, not_or] at ht
    simp only [Expr.subst, Expr.ctors, List.mem_append, not_or]
    refine ⟨not_mem_ctors_subst ht.1 hσ, not_mem_ctors_subst ht.2 fun s hs => ?_⟩
    simp only [List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨s0, hs0, rfl⟩
    · simp [Expr.ctors]
    · rw [Expr.ctors_shift]; exact hσ s0 hs0

/-- **A lowered expression calls a function only where an entry's template
does**: a call `c` that no template makes is in no lowered expression. -/
theorem Lowering.lower_not_mem_ctors {p : Profile} {L : Lowering p} {c : Functions.Ctor}
    (hu : ∀ f en, L.un f = some en → c ∉ en.tmpl.ctors)
    (hb : ∀ f en, L.bin f = some en → c ∉ en.tmpl.ctors) :
    ∀ {e t : Expr}, L.lower e = some t → c ∉ t.ctors
  | .lit _, t, h | .field _, t, h => by
    simp only [lower, lowerWith, Option.some.injEq] at h; subst h; simp [Expr.ctors]
  | .un f a, t, h => by
    simp only [lower, lowerWith, Expr.keepGuards_all] at h
    cases hen : L.un f with
    | none => simp [hen] at h
    | some en =>
      cases ha : L.lowerWith (fun _ => true) a with
      | none => simp [hen, ha] at h
      | some a' =>
        simp [hen, ha] at h
        subst h
        exact Expr.not_mem_ctors_subst (hu f en hen)
          (by simpa using lower_not_mem_ctors hu hb (e := a) ha)
  | .bin f a b, t, h => by
    simp only [lower, lowerWith, Expr.keepGuards_all] at h
    cases hen : L.bin f with
    | none => simp [hen] at h
    | some en =>
      cases ha : L.lowerWith (fun _ => true) a with
      | none => simp [hen, ha] at h
      | some a' =>
        cases hb' : L.lowerWith (fun _ => true) b with
        | none => simp [hen, ha, hb'] at h
        | some b' =>
          simp [hen, ha, hb'] at h
          subst h
          refine Expr.not_mem_ctors_subst (hb f en hen) fun s hs => ?_
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
          rcases hs with rfl | rfl
          · exact lower_not_mem_ctors hu hb (e := a) ha
          · exact lower_not_mem_ctors hu hb (e := b) hb'
  | .ifThen c' t' e', t, h => by
    simp only [lower, lowerWith] at h
    cases hc : L.lowerWith (fun _ => true) c' with
    | none => simp [hc] at h
    | some c1 =>
      cases ht : L.lowerWith (fun _ => true) t' with
      | none => simp [hc, ht] at h
      | some t1 =>
        cases he : L.lowerWith (fun _ => true) e' with
        | none => simp [hc, ht, he] at h
        | some e1 =>
          simp [hc, ht, he] at h
          subst h
          simp only [Expr.ctors, List.mem_append, not_or]
          exact ⟨⟨lower_not_mem_ctors hu hb (e := c') hc, lower_not_mem_ctors hu hb (e := t') ht⟩,
            lower_not_mem_ctors hu hb (e := e') he⟩
  | .hof f l b, t, h => by
    simp only [lower, lowerWith] at h
    cases hl : L.lowerWith (fun _ => true) l with
    | none => simp [hl] at h
    | some l1 =>
      cases hb' : L.lowerWith (fun _ => true) b with
      | none => simp [hl, hb'] at h
      | some b1 =>
        simp [hl, hb'] at h
        subst h
        simp only [Expr.ctors, List.mem_append, not_or]
        exact ⟨lower_not_mem_ctors hu hb (e := l) hl, lower_not_mem_ctors hu hb (e := b) hb'⟩

end Substrait
