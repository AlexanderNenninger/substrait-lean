import Sverify.Analysis.Semantic
import Sverify.Analysis.Contracts.Sound

/-!
# A LEFT JOIN on a foreign key, for the contracts (#2512, ruling 276)

A left join whose condition equates a left column with a right column, where
a declared foreign key (`sv.references`, a dbt `relationships` test) gives
every non-NULL left value a row of the table the right column is a group key
of, gives every left row a match: its right columns are as non-NULL as the
right side's own. `Rel.fkMatch` (`Semantic.lean`) is that test for the
rewrite to an inner join, stated for `Rel.eval`.

The contracts speak of every result the reference allows (`OrderAllowed`), so
the test has to hold there, and it does for the plans whose origin and cover
`Rel.originS` and `Rel.cover` follow. `Rel.fkLeft` rewrites such left joins in
a plan to inner joins; `Rel.fkLeft_orderAllowed` says every result the written
plan may give is one the rewritten plan may give, and `contract_sound_all_fk`
proves a contract on the rewritten plan. The rewrite is the analysis's view
only: the plan that runs stays the LEFT JOIN.
-/

namespace Substrait

theorem Forall2.mem_left' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab t, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := Forall2.mem_left' t h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

variable [Boxes.Ambient]

/-- `Rel.origin`, for the plans whose every allowed result keeps a column's
non-NULL values among a table's. -/
def Rel.originS (cat : Catalog) : Rel → Nat → Option (String × Nat)
  | .read t, i => some (t, i)
  | .filter r _, i | .fetch r _ _, i | .orderBy r _, i | .distinct r, i => r.originS cat i
  | .project r es, i =>
      if i < r.arity cat then r.originS cat i
      else match es[i - r.arity cat]? with
        | some (.field j) => r.originS cat j
        | _ => none
  | .emit r m, i => m[i]?.bind (r.originS cat)
  | _, _ => none

/-- A non-NULL value of column `i` of every allowed result is, up to canonical
codes, a value of the table column. -/
def OriginOkAll (cat : Catalog) (r : Rel) : Prop :=
  ∀ {i t c}, r.originS cat i = some (t, c) → ∀ {out : Relation}, r.OrderAllowed cat out →
    ∀ x ∈ out, x.getD i .null ≠ .null →
      ∃ y ∈ (cat t).rows, (y.getD c .null).canonV = (x.getD i .null).canonV

/-- Every non-NULL value of the table column is, up to canonical codes, in
column `j` of every allowed result. -/
def CoverOkAll (cat : Catalog) (r : Rel) : Prop :=
  ∀ {j t p}, r.cover cat j = some (t, p) → ∀ {out : Relation}, r.OrderAllowed cat out →
    ∀ y ∈ (cat t).rows, y.getD p .null ≠ .null →
      ∃ z ∈ out, (z.getD j .null).canonV = (y.getD p .null).canonV

omit [Boxes.Ambient] in
theorem Value.ne_null_of_canonV {v w : Value} (h : v.canonV = w.canonV) (hw : w ≠ .null) :
    v ≠ .null := by
  intro hv; subst hv; apply hw
  cases w <;> simp_all [Value.canonV]

omit [Boxes.Ambient] in
theorem Value.canonV_ne_null {v : Value} (h : v ≠ .null) : v.canonV ≠ .null := by
  cases v <;> simp_all [Value.canonV]


theorem Rel.originS_sound_all {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → OriginOkAll cat r
  | .read _, _ => fun h out hout x hx _ => by
      simp only [originS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, hout.mem_iff.mp hx, rfl⟩
  | .filter r _, hwf => fun h out ⟨i, hi, hout⟩ x hx hn => by
      subst hout
      rw [List.mem_filter] at hx
      exact originS_sound_all hcat hwf.1 h hi x hx.1 hn
  | .fetch r _ _, hwf => fun h out ⟨i, hi, hout⟩ x hx hn => by
      subst hout
      have hx' : x ∈ i := by
        split at hx
        · exact List.mem_of_mem_drop hx
        · exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
      exact originS_sound_all hcat (r := r) hwf h hi x hx' hn
  | .orderBy r _, hwf => fun h out ⟨i, hi, hp, _⟩ x hx hn =>
      originS_sound_all hcat hwf.1 h hi x (hp.mem_iff.mp hx) hn
  | .distinct r, hwf => fun h out ⟨i, hi, d, hd, hp⟩ x hx hn => by
      obtain ⟨y, hy, hxy, _⟩ := hd.2.1 x (hp.mem_iff.mp hx)
      have hc := getD_canonV_of_canon hxy
      have hyn : y.getD _ .null ≠ .null := Value.ne_null_of_canonV (hc _).symm hn
      obtain ⟨w, hw, hwy⟩ := originS_sound_all hcat (r := r) hwf h hi y hy hyn
      exact ⟨w, hw, hwy.trans (hc _).symm⟩
  | .project r es, hwf => fun h out ⟨i, hi, hout⟩ x hx hn => by
      rename_i i0 _ _ _
      subst hout
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
      have hl := Rel.orderAllowed_arity hcat hwf.1 hi row hrow
      simp only [originS] at h
      split at h
      · rename_i hlt
        rw [getD_append_left' (by omega)] at hn ⊢
        exact originS_sound_all hcat hwf.1 h hi row hrow hn
      · rename_i hlt
        obtain ⟨d, rfl⟩ : ∃ d, i0 = row.length + d := ⟨i0 - row.length, by omega⟩
        rw [← hl, Nat.add_sub_cancel_left] at h
        rw [getD_append_right'] at hn ⊢
        cases hg : es[d]? with
        | none => simp [hg] at h
        | some e =>
          cases e with
          | field j =>
            simp only [hg] at h
            have he : (es.map (·.eval row)).getD d .null = row.getD j .null := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_map, hg, Expr.eval]
            rw [he] at hn ⊢
            exact originS_sound_all hcat hwf.1 h hi row hrow hn
          | _ => simp [hg] at h
  | .emit r m, hwf => fun h out ⟨i, hi, hout⟩ x hx hn => by
      rename_i i0 _ _ _
      subst hout
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
      simp only [originS] at h
      cases hm : m[i0]? with
      | none => simp [hm] at h
      | some j =>
        simp only [hm, Option.bind_some] at h
        have he : (m.map (row.getD · .null)).getD i0 .null = row.getD j .null := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hm]
        rw [he] at hn ⊢
        exact originS_sound_all hcat hwf.1 h hi row hrow hn
  | .values _ _, _ | .unnest _ _, _ | .cross _ _, _ | .join _ _ _ _, _ | .unionAll _ _, _
  | .window _ _ _ _, _ | .semi _ _ _ _, _ | .aggregate _ _ _, _ => fun h => by simp [originS] at h


theorem Rel.cover_sound_all {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → CoverOkAll cat r
  | .read _, _ => fun h out hout y hy _ => by
      simp only [cover, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨y, hout.mem_iff.mpr hy, rfl⟩
  | .orderBy r _, hwf => fun h out ⟨i, hi, hp, _⟩ y hy hn => by
      obtain ⟨z, hz, he⟩ := cover_sound_all hcat hwf.1 h hi y hy hn
      exact ⟨z, hp.mem_iff.mpr hz, he⟩
  | .distinct r, hwf => fun h out ⟨i, hi, d, hd, hp⟩ y hy hn => by
      obtain ⟨z, hz, he⟩ := cover_sound_all hcat (r := r) hwf h hi y hy hn
      obtain ⟨w, hw, hwz⟩ := hd.2.2 z hz
      exact ⟨w, hp.mem_iff.mpr hw, (getD_canonV_of_canon hwz _).trans he⟩
  | .project r es, hwf => fun h out ⟨i, hi, hout⟩ y hy hn => by
      subst hout
      rename_i j _ _ _
      simp only [cover] at h
      split at h
      · rename_i hj
        obtain ⟨z, hz, he⟩ := cover_sound_all hcat hwf.1 h hi y hy hn
        refine ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
        rw [getD_append_left' (by rw [Rel.orderAllowed_arity hcat hwf.1 hi z hz]; exact hj), he]
      · simp at h
  | .emit r m, hwf => fun h out ⟨i, hi, hout⟩ y hy hn => by
      subst hout
      rename_i j _ _ _
      simp only [cover] at h
      cases hm : m[j]? with
      | none => simp [hm] at h
      | some j' =>
        simp only [hm, Option.bind_some] at h
        obtain ⟨z, hz, he⟩ := cover_sound_all hcat hwf.1 h hi y hy hn
        refine ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, hm] at he ⊢
        exact he
  | .aggregate r gs ms, hwf => fun h out ⟨i, hi, o, hp, hagg⟩ y hy hn => by
      rename_i j _ _ _
      simp only [cover] at h
      cases hg : gs[j]? with
      | none => simp [hg] at h
      | some e =>
        cases e with
        | field j' =>
          simp only [hg] at h
          obtain ⟨z, hz, he⟩ := cover_sound_all hcat hwf.1 h hi y hy hn
          have hne : gs.isEmpty = false := by
            cases gs with
            | nil => simp at hg
            | cons _ _ => rfl
          unfold aggOrderAllowed at hagg
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at hagg
          obtain ⟨ks, hks, hf⟩ := hagg
          obtain ⟨k, hk, hkc⟩ := hks.2.2 (groupKey gs z) (List.mem_map_of_mem hz)
          obtain ⟨row, hrow, vs, rfl, _⟩ := Forall2.mem_left' hf hk
          have hj : j < (groupKey gs z).length := by
            simp only [groupKey, List.length_map]
            exact (List.getElem?_eq_some_iff.mp hg).1
          have hkl : j < k.length := by
            have := congrArg List.length hkc
            simp only [Row.canon, List.length_map] at this
            rw [this]; exact hj
          refine ⟨k ++ vs, hp.mem_iff.mpr hrow, ?_⟩
          rw [getD_append_left' hkl, getD_canonV_of_canon hkc j]
          simp only [groupKey, List.getD_eq_getElem?_getD, List.getElem?_map, hg,
            Option.map_some, Option.getD_some, Expr.eval]
          exact he
        | _ => simp [hg] at h
  | .values _ _, _ | .filter _ _, _ | .cross _ _, _ | .join _ _ _ _, _ | .fetch _ _ _, _
  | .unionAll _ _, _ | .window _ _ _ _, _ | .semi _ _ _ _, _
  | .unnest _ _, _ => fun h => by simp [cover] at h


/-- Does every left row of `a ⟕ b ON on` have a match, by a foreign key, in
every result the reference allows? `Rel.fkMatch` over the plans `Rel.originS`
and `Rel.cover` follow, with the left key's non-NULL-ness from the analysis
under the window keys `T`. -/
def Rel.fkMatchS (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (R : ForeignKeys) (a b : Rel) (on : Expr) : Bool :=
  match eqPair (a.arity cat) on with
  | some (i, j) => match a.originS cat i, b.cover cat j with
    | some (t, c), some (s, p) =>
      (R t).contains (c, s, p) && !((a.aeval cat A F T).getD i AVal.top).null
    | _, _ => false
  | none => false

theorem Rel.fkMatchS_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact} (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {R : ForeignKeys} (hR : R.Hold cat) {a b : Rel} {on : Expr}
    (hm : Rel.fkMatchS cat A F T R a b on = true) (ha : a.WF cat) (hb : b.WF cat)
    {x y : Relation} (hx : a.OrderAllowed cat x) (hy : b.OrderAllowed cat y) :
    ∀ row ∈ x, ∃ z ∈ y, (on.eval (row ++ z)).isTrue = true := by
  intro row hrow
  unfold Rel.fkMatchS at hm
  split at hm
  · rename_i i j hij
    split at hm
    · rename_i t c s p ho hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hm
      obtain ⟨hfk, hnn⟩ := hm
      have hmem := Rel.aeval_sound_all hcat hA hF hT ha hx row hrow i
      have hxn : row.getD i .null ≠ .null := fun h0 => by
        rw [h0] at hmem
        simp only [AVal.Mem, AVal.MemR, List.getD_eq_getElem?_getD] at hmem hnn
        simp [hmem] at hnn
      obtain ⟨y0, hy0, hyx⟩ := Rel.originS_sound_all hcat ha ho hx row hrow hxn
      have hy0n : y0.getD c .null ≠ .null := Value.ne_null_of_canonV hyx hxn
      obtain ⟨w, hw, hwy⟩ := hR t _ hfk y0 hy0 hy0n
      obtain ⟨z, hz, hzw⟩ := Rel.cover_sound_all hcat hb hc hy w hw (by rw [hwy]; exact hy0n)
      refine ⟨z, hz, eqPair_sound hij (Rel.orderAllowed_arity hcat ha hx row hrow) ?_ hxn⟩
      rw [hzw, hwy, hyx]
    · simp at hm
  · simp at hm


/-- The plan with each left join the foreign keys `R` give a match for
(`Rel.fkMatchS`) an inner join. The analysis's view of the plan: the plan that
runs stays as written. -/
def Rel.fkLeft (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (R : ForeignKeys) : Rel → Rel
  | .read t => .read t
  | .values n rs => .values n rs
  | .filter r c => .filter (r.fkLeft cat A F T R) c
  | .project r es => .project (r.fkLeft cat A F T R) es
  | .emit r m => .emit (r.fkLeft cat A F T R) m
  | .cross a b => .cross (a.fkLeft cat A F T R) (b.fkLeft cat A F T R)
  | .join a b .inner on => .join (a.fkLeft cat A F T R) (b.fkLeft cat A F T R) .inner on
  | .join a b .left on =>
      .join (a.fkLeft cat A F T R) (b.fkLeft cat A F T R)
        (if Rel.fkMatchS cat A F T R a b on then .inner else .left) on
  | .fetch r o c => .fetch (r.fkLeft cat A F T R) o c
  | .unionAll a b => .unionAll (a.fkLeft cat A F T R) (b.fkLeft cat A F T R)
  | .window r p s fs => .window (r.fkLeft cat A F T R) p s fs
  | .semi a b an on => .semi (a.fkLeft cat A F T R) (b.fkLeft cat A F T R) an on
  | .orderBy r k => .orderBy (r.fkLeft cat A F T R) k
  | .distinct r => .distinct (r.fkLeft cat A F T R)
  | .aggregate r g m => .aggregate (r.fkLeft cat A F T R) g m
  | .unnest r c => .unnest (r.fkLeft cat A F T R) c

section
variable {cat : Catalog} {A : String → List AVal} {F : String → List Fact} {T : WindowKeys}
  {R : ForeignKeys}

theorem Rel.arity_fkLeft : ∀ r : Rel, (r.fkLeft cat A F T R).arity cat = r.arity cat
  | .read _ | .values _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ =>
      by simp only [fkLeft, arity, arity_fkLeft r]
  | .project r _ | .emit r _ | .aggregate r _ _ | .window r _ _ _ =>
      by simp only [fkLeft, arity, arity_fkLeft r]
  | .cross a b | .semi a b _ _ | .unionAll a b =>
      by simp only [fkLeft, arity, arity_fkLeft a, arity_fkLeft b]
  | .join a b .inner _ => by simp only [fkLeft, arity, arity_fkLeft a, arity_fkLeft b]
  | .join a b .left _ => by simp only [fkLeft, arity, arity_fkLeft a, arity_fkLeft b]

theorem Rel.fkLeft_wf : ∀ (r : Rel), r.WF cat → (r.fkLeft cat A F T R).WF cat
  | .read _, h => h
  | .values _ _, h => h
  | .filter r _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .project r _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .emit r _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .cross a b, h => ⟨fkLeft_wf _ h.1, fkLeft_wf _ h.2⟩
  | .join a b .inner _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, fkLeft_wf _ h.2.1, h.2.2⟩
  | .join a b .left _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, fkLeft_wf _ h.2.1, h.2.2⟩
  | .fetch r _ _, h => fkLeft_wf r h
  | .unionAll a b, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, fkLeft_wf _ h.2.1, h.2.2⟩
  | .window r _ _ _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .semi a b _ _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, fkLeft_wf _ h.2.1, h.2.2⟩
  | .orderBy r _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .distinct r, h => fkLeft_wf r h
  | .aggregate r _ _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩
  | .unnest r _, h => by
      simp only [fkLeft, WF, arity_fkLeft] at h ⊢; exact ⟨fkLeft_wf _ h.1, h.2⟩

/-- **Every result the written plan may give is one the rewritten plan may
give**, under foreign keys that hold. -/
theorem Rel.fkLeft_orderAllowed (hcat : cat.WF) (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hT : T.SoundAll cat)
    (hR : R.Hold cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      (r.fkLeft cat A F T R).OrderAllowed cat out
  | .read _, _, _, h => h
  | .values _ _, _, _, h => h
  | .filter r _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .project r _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .emit r _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .cross a b, hwf, _, ⟨x, y, hx, hy, e⟩ =>
      ⟨x, y, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hx,
        fkLeft_orderAllowed hcat hA hF hT hR hwf.2 hy, e⟩
  | .join a b .inner _, hwf, _, ⟨x, y, hx, hy, e⟩ =>
      ⟨x, y, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hx,
        fkLeft_orderAllowed hcat hA hF hT hR hwf.2.1 hy, e⟩
  | .join a b .left on, hwf, _, ⟨x, y, hx, hy, e⟩ => by
      have hx' := fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hx
      have hy' := fkLeft_orderAllowed hcat hA hF hT hR hwf.2.1 hy
      by_cases hm : Rel.fkMatchS cat A F T R a b on = true
      · simp only [fkLeft, hm, ↓reduceIte, Rel.OrderAllowed]
        refine ⟨x, y, hx', hy', ?_⟩
        rw [← leftJoin_eq_inner (k := b.arity cat)
          (Rel.fkMatchS_sound_all hcat hA hF hT hR hm hwf.1 hwf.2.1 hx hy)]
        exact e
      · have hm' : Rel.fkMatchS cat A F T R a b on = false := by simpa using hm
        simp only [fkLeft, hm', Bool.false_eq_true, ↓reduceIte, Rel.OrderAllowed]
        refine ⟨x, y, hx', hy', ?_⟩
        rw [arity_fkLeft]
        exact e
  | .fetch r _ _, hwf, _, ⟨i, hi, e⟩ =>
      ⟨i, fkLeft_orderAllowed hcat hA hF hT hR (r := r) hwf hi, e⟩
  | .unionAll a b, hwf, _, ⟨x, y, hx, hy, e⟩ =>
      ⟨x, y, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hx,
        fkLeft_orderAllowed hcat hA hF hT hR hwf.2.1 hy, e⟩
  | .window r _ _ _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .semi a b _ _, hwf, _, ⟨x, y, hx, hy, e⟩ =>
      ⟨x, y, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hx,
        fkLeft_orderAllowed hcat hA hF hT hR hwf.2.1 hy, e⟩
  | .orderBy r _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .distinct r, hwf, _, ⟨i, hi, e⟩ =>
      ⟨i, fkLeft_orderAllowed hcat hA hF hT hR (r := r) hwf hi, e⟩
  | .aggregate r _ _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩
  | .unnest r _, hwf, _, ⟨i, hi, e⟩ => ⟨i, fkLeft_orderAllowed hcat hA hF hT hR hwf.1 hi, e⟩

end

/-- **Contract soundness for every order, with the foreign keys that hold.**
A postcondition the analysis proves on the plan with its left joins on foreign
keys read as inner joins holds on every row of every order the reference allows
of the plan as written. -/
theorem contract_sound_all_fk {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {Q : Rel}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hQ : Q.WF cat) {T : WindowKeys} (hT : T.SoundAll cat) {R : ForeignKeys} (hR : R.Hold cat)
    (hproved : ((Q.fkLeft cat (fun t => tableEnv (S t) (pre t))
        (fun t => (pre t).flatMap Expr.factsOf) T R).aeval cat (fun t => tableEnv (S t) (pre t))
        (fun t => (pre t).flatMap Expr.factsOf) T).all AVal.certainlyTrue = true) :
    ∀ {out : Relation}, Q.OrderAllowed cat out → ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  intro out hout
  have hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold ((pre t).flatMap Expr.factsOf) row := by
    intro t row h f hf
    simp only [List.mem_flatMap] at hf
    obtain ⟨e, he, hf⟩ := hf
    exact Expr.factsOf_sound e (hpre t row h e he) f hf
  have hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (tableEnv (S t) (pre t)) row :=
    fun t row h => tableEnv_sound (hS t row h) (hpre t row h)
  exact contract_sound_all hcat hS hpre (Rel.fkLeft_wf Q hQ) hT hproved
    (Rel.fkLeft_orderAllowed hcat hA hF hT hR hQ hout)

end Substrait
