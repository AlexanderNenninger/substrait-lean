import Sverify.Engines.Lowering

/-!
# Where a lowered plan raises

A lowered plan raises only where the reference may (`Lowering.lowerRel_raises`,
`Lowering.lowerRel?_raises` for a partial table), since each entry agrees with
the reference (`Lowering.lower_correct`). With `Rel.hasIssue_of_raises`
(`analysis/Sverify/Analysis/Guards.lean`), a report with only assumed issues
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
plan's own expressions (`Q`), as for a partial table (`Rel.evalI_mapExprs_on`). -/
theorem Rel.raises_mapExprs_on {p q : Profile} {f : Expr → Expr} {Q : Expr → Prop}
    (hx : ∀ e, Q e → Expr.Exact p (f e) e) (hf : ∀ i, f (.field i) = .field i)
    (hr : ∀ e row, Q e → (f e).RaisesOn p row → e.RaisesOn q row) {cat : Catalog}
    (hq : ∀ r : Rel, ¬r.Raises q cat → r.eval cat q.impl = r.eval cat) :
    ∀ {r : Rel}, (∀ e ∈ r.mappedExprs, Q e) → (r.mapExprs f).Raises p cat → r.Raises q cat
  | .read _, _, h | .values _ _, _, h => h.elim
  | .filter r c, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_cons_of_mem _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_on hx hf hr hq hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_on hx hf hQr (fun h' => h0 (ih h'))] at hrow
        exact ⟨row, by rw [hq r h0]; exact hrow, hr c row (hQ c (List.mem_cons_self ..)) hc⟩
  | .project r es, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_on hx hf hr hq hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_on hx hf hQr (fun h' => h0 (ih h'))] at hrow
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        exact ⟨row, by rw [hq r h0]; exact hrow, e, he,
          hr e row (hQ e (List.mem_append_left _ he)) hc⟩
  | .emit r _, hQ, h | .orderBy r _, hQ, h | .distinct r, hQ, h | .unnest r _, hQ, h
  | .window r _ _ _, hQ, h | .fetch r _ _, hQ, h => by
    simp only [mapExprs, Raises] at h ⊢
    exact raises_mapExprs_on hx hf hr hq (fun e he => hQ e he) h
  | .cross a b, hQ, h | .unionAll a b, hQ, h => by
    have hQa : ∀ e ∈ a.mappedExprs, Q e := fun e he => hQ e (List.mem_append_left _ he)
    have hQb : ∀ e ∈ b.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    exact h.imp (raises_mapExprs_on hx hf hr hq hQa) (raises_mapExprs_on hx hf hr hq hQb)
  | .join a b _ on, hQ, h | .semi a b _ on, hQ, h => by
    have hQa : ∀ e ∈ a.mappedExprs, Q e := fun e he =>
      hQ e (List.mem_cons_of_mem _ (List.mem_append_left _ he))
    have hQb : ∀ e ∈ b.mappedExprs, Q e := fun e he =>
      hQ e (List.mem_cons_of_mem _ (List.mem_append_right _ he))
    simp only [mapExprs, Raises] at h ⊢
    have iha := raises_mapExprs_on hx hf hr hq hQa
    have ihb := raises_mapExprs_on hx hf hr hq hQb
    by_cases ha : a.Raises q cat
    · exact .inl ha
    · by_cases hb : b.Raises q cat
      · exact .inr (.inl hb)
      · refine .inr (.inr ?_)
        rcases h with h | h | ⟨x, hx', y, hy, hc⟩
        · exact absurd (iha h) ha
        · exact absurd (ihb h) hb
        · rw [evalI_mapExprs_on hx hf hQa (fun h' => ha (iha h'))] at hx'
          rw [evalI_mapExprs_on hx hf hQb (fun h' => hb (ihb h'))] at hy
          exact ⟨x, by rw [hq a ha]; exact hx', y, by rw [hq b hb]; exact hy,
            hr on _ (hQ on (List.mem_cons_self ..)) hc⟩
  | .aggregate r gs ms, hQ, h => by
    have hQr : ∀ e ∈ r.mappedExprs, Q e := fun e he => hQ e (List.mem_append_right _ he)
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs_on hx hf hr hq hQr
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs_on hx hf hQr (fun h' => h0 (ih h'))] at hrow
        refine ⟨row, by rw [hq r h0]; exact hrow, ?_⟩
        simp only [List.mem_append, List.mem_flatMap, List.mem_map] at he'
        rcases he' with ⟨e, he, rfl⟩ | ⟨m', hm', he'⟩
        · exact ⟨e, List.mem_append_left _ he,
            hr e row (hQ e (List.mem_append_left _ (List.mem_append_left _ he))) hc⟩
        · obtain ⟨m, hm, rfl⟩ := hm'
          obtain ⟨e, he, rfl⟩ := Measure.mem_mapExpr_exprs hf he'
          have hme : e ∈ ms.flatMap Measure.exprs := List.mem_flatMap.mpr ⟨m, hm, he⟩
          exact ⟨e, List.mem_append_right _ hme,
            hr e row (hQ e (List.mem_append_left _ (List.mem_append_right _ hme))) hc⟩

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

end Substrait
