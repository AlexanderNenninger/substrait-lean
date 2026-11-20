import SubstraitLean.ContractCheck

/-!
# Every issue on every order is reported (#1484)

`check_issues_sound` covers `Rel.HasIssue`: the issues on `Rel.eval`'s rows,
with filter and join conditions on the loose rows. `Rel.HasIssueAll` adds
every order of the ties the reference allows and the views of a join's
inputs (`Rel.ViewAllowed`, #1484 R3): a condition an engine pushes into one
input runs on that input's rows, whatever the other holds, an empty one
included. `Rel.mayIssues_sound_all` proves the checker reports those; this
module carries the proof through the row caps (`Rel.issuesCapped`) to the
report (`check_issues_sound_all`).

The caps change nothing on data within them, on every order:

* capped reads have the same orders (`Rel.orderAllowed_of_capReads`, and
  `Rel.orderAllowed_capReads` the other way) and the same views;
* capped joins too (`Rel.orderAllowed_capJoins`,
  `Rel.orderAllowed_of_capJoins`): a join on a key of its right side has at
  most its left side's rows on every order;
* the bounds on rows per key hold on every order (`Rel.perKey_sound_all`), so
  an integer `SUM` that `Rel.sumsPer` leaves out fits on every order
  (`Rel.sumsPer_sound_all`).
-/

namespace Substrait

variable [Boxes.Ambient]

/-! ## Capped reads -/

section
variable {cat : Catalog} {caps : String → Option Nat}

/-- On tables within their caps, every order of the plan with capped reads
is one of the plan. -/
theorem Rel.orderAllowed_of_capReads (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel} {out : Relation}, (r.capReads caps).OrderAllowed cat out → r.OrderAllowed cat out
  | .read t, out, h => by
    unfold capReads at h
    split at h
    · rename_i n hn
      obtain ⟨i, hi, rfl⟩ := h
      simp only [List.drop_zero]
      rw [List.take_of_length_le (hi.length_eq ▸ hc t n hn)]
      exact hi
    · exact h
  | .values _ _, _, h => h
  | .filter r _, _, ⟨i, hi, h⟩ | .project r _, _, ⟨i, hi, h⟩ | .emit r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩
  | .fetch r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩
  | .cross a b, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_of_capReads hc (r := a) hx, orderAllowed_of_capReads hc (r := b) hy, h⟩
  | .join a b .inner _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_of_capReads hc (r := a) hx, orderAllowed_of_capReads hc (r := b) hy, h⟩
  | .join a b .left _, _, ⟨x, y, hx, hy, h⟩ => by
    refine ⟨x, y, orderAllowed_of_capReads hc (r := a) hx, orderAllowed_of_capReads hc (r := b) hy,
      ?_⟩
    rw [← capReads_arity caps cat b]; exact h
  | .window r _ _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩
  | .orderBy r _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩
  | .distinct r, _, ⟨i, hi, h⟩ | .unnest r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩
  | .aggregate r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_of_capReads hc (r := r) hi, h⟩

theorem Rel.capReads_smallAll (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel}, r.SmallAll cat → (r.capReads caps).SmallAll cat
  | .read t, h => by unfold capReads; split <;> trivial
  | .values _ _, h => h
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h
  | .unnest r _, h | .fetch r _ _, h | .distinct r, h => capReads_smallAll hc (r := r) h
  | .aggregate r _ _, h | .window r _ _ _, h =>
    ⟨fun i hi => h.1 i (orderAllowed_of_capReads hc hi), capReads_smallAll hc h.2⟩
  | .cross a b, h | .unionAll a b, h | .semi a b _ _, h | .join a b _ _, h =>
    ⟨capReads_smallAll hc h.1, capReads_smallAll hc h.2⟩

omit [Boxes.Ambient] in
theorem Rel.isPair_capReads : ∀ r : Rel, (r.capReads caps).isPair = r.isPair
  | .read t => by unfold capReads; split <;> rfl
  | .values _ _ | .filter _ _ | .project _ _ | .emit _ _ | .cross _ _ | .join _ _ _ _
  | .fetch _ _ _ | .unionAll _ _ | .window _ _ _ _ | .semi _ _ _ _ | .orderBy _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => rfl

/-- Outside a cross or a join, a view is an order. -/
theorem Rel.viewAllowed_of_not_pair {r : Rel} (hr : r.isPair = false) {cols : List Nat}
    {out : Relation} : r.ViewAllowed cat cols out ↔ r.OrderAllowed cat out := by
  cases r <;> simp_all [Rel.isPair, Rel.ViewAllowed]

theorem Rel.viewAllowed_capReads (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel} {cols : List Nat} {out : Relation}, r.ViewAllowed cat cols out →
      (r.capReads caps).ViewAllowed cat cols out
  | .cross a b, cols, out, h | .join a b _ _, cols, out, h => by
    simp only [capReads, ViewAllowed, capReads_arity] at h ⊢
    split
    · rename_i h1; simp only [h1, ↓reduceIte] at h
      obtain ⟨x, hx, rfl⟩ := h; exact ⟨x, viewAllowed_capReads hc hx, rfl⟩
    · rename_i h1; simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      split
      · rename_i h2; simp only [h2, ↓reduceIte] at h
        obtain ⟨y, hy, rfl⟩ := h; exact ⟨y, viewAllowed_capReads hc hy, rfl⟩
      · rename_i h2; simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ⟨x, y, viewAllowed_capReads hc hx, viewAllowed_capReads hc hy, rfl⟩
  | .read t, _, _, h | .values _ _, _, _, h | .filter _ _, _, _, h | .project _ _, _, _, h
  | .emit _ _, _, _, h | .fetch _ _ _, _, _, h | .unionAll _ _, _, _, h
  | .window _ _ _ _, _, _, h | .semi _ _ _ _, _, _, h | .orderBy _ _, _, _, h
  | .distinct _, _, _, h | .aggregate _ _ _, _, _, h | .unnest _ _, _, _, h => by
    rw [viewAllowed_of_not_pair (by rw [isPair_capReads]; rfl)]
    exact orderAllowed_capReads hc ((viewAllowed_of_not_pair rfl).mp h)

theorem Rel.viewIssue_capReads (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    {r : Rel} {e : Expr} {p : Issue × Expr} (h : r.ViewIssue cat e p) :
    (r.capReads caps).ViewIssue cat e p :=
  let ⟨d, hd, out, hv, hrow⟩ := h; ⟨d, hd, out, viewAllowed_capReads hc hv, hrow⟩

theorem Rel.orderAllowed_capReads_ite (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    (u : Bool) {r : Rel} {out : Relation} (h : (if u then r.loose else r).OrderAllowed cat out) :
    (if u then (r.capReads caps).loose else r.capReads caps).OrderAllowed cat out := by
  cases u
  · exact orderAllowed_capReads hc h
  · simp only [↓reduceIte, capReads_loose] at h ⊢; exact orderAllowed_capReads hc h

/-- An issue of the plan, on any order, is one of the plan with capped reads,
on tables within their caps. -/
theorem Rel.hasIssueAll_capReads (hc : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {u : Bool} {r : Rel} {p : Issue × Expr}, r.HasIssueAll cat u p →
      (r.capReads caps).HasIssueAll cat u p
  | _, .read _, _, h | _, .values _ _, _, h => h.elim
  | _, .filter r _, _, h => by
    simp only [HasIssueAll, capReads, capReads_loose] at h ⊢
    rcases h with h | ⟨i, hi, hrow⟩ | hv
    · exact .inl (hasIssueAll_capReads hc h)
    · exact .inr (.inl ⟨i, orderAllowed_capReads hc hi, hrow⟩)
    · exact .inr (.inr (viewIssue_capReads hc hv))
  | u, .project r _, _, h => by
    simp only [HasIssueAll, capReads] at h ⊢
    rcases h with h | ⟨i, hi, hrow⟩ | ⟨hu, e, he, hv⟩
    · exact .inl (hasIssueAll_capReads hc h)
    · exact .inr (.inl ⟨i, orderAllowed_capReads_ite hc u hi, hrow⟩)
    · rw [capReads_loose]; exact .inr (.inr ⟨hu, e, he, viewIssue_capReads hc hv⟩)
  | _, .emit r _, _, h | _, .fetch r _ _, _, h | _, .orderBy r _, _, h | _, .distinct r, _, h
  | _, .unnest r _, _, h => by
    simp only [HasIssueAll, capReads] at h ⊢
    exact hasIssueAll_capReads hc (r := r) h
  | _, .window r _ _ _, _, h => by
    simp only [HasIssueAll, capReads] at h ⊢
    rcases h with h | ⟨i, hi, h⟩
    · exact .inl (hasIssueAll_capReads hc h)
    · exact .inr ⟨i, orderAllowed_capReads hc hi, h⟩
  | _, .cross a b, _, h | _, .unionAll a b, _, h => by
    simp only [HasIssueAll, capReads] at h ⊢
    exact h.imp (hasIssueAll_capReads hc) (hasIssueAll_capReads hc)
  | _, .join a b _ _, _, h | _, .semi a b _ _, _, h => by
    simp only [HasIssueAll, capReads, capReads_loose] at h ⊢
    rcases h with h | h | ⟨xs, hxs, ys, hys, hrow⟩ | hv
    · exact .inl (hasIssueAll_capReads hc h)
    · exact .inr (.inl (hasIssueAll_capReads hc h))
    · exact .inr (.inr (.inl ⟨xs, orderAllowed_capReads hc hxs, ys, orderAllowed_capReads hc hys,
        hrow⟩))
    · exact .inr (.inr (.inr (viewIssue_capReads (r := Rel.cross _ _) hc hv)))
  | u, .aggregate r _ _, _, h => by
    simp only [HasIssueAll, capReads] at h ⊢
    rcases h with h | ⟨i, hi, hrow⟩ | ⟨i, hi, h⟩ | ⟨hu, e, he, hv⟩
    · exact .inl (hasIssueAll_capReads hc h)
    · exact .inr (.inl ⟨i, orderAllowed_capReads_ite hc u hi, hrow⟩)
    · exact .inr (.inr (.inl ⟨i, orderAllowed_capReads hc hi, h⟩))
    · rw [capReads_loose]; exact .inr (.inr (.inr ⟨hu, e, he, viewIssue_capReads hc hv⟩))

end

/-! ## Capped joins -/

section
variable {cat : Catalog} {A : String → List AVal} {F : String → List Fact} {K : TableCond}

/-- **A join on a key does not fan out, on any order**: a result of it has
at most as many rows as some order of its left side. -/
theorem Rel.join_length_le_of_keyed_all (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hK : K.Hold cat) {a b : Rel}
    {ty : JoinType} {on : Expr} (hwf : (Rel.join a b ty on).WF cat)
    (hkey : Rel.keyedJoin cat A F K a b on = true) {out : Relation}
    (h : (Rel.join a b ty on).OrderAllowed cat out) :
    ∃ x, a.OrderAllowed cat x ∧ out.length ≤ x.length := by
  cases ty with
  | inner =>
    obtain ⟨x, y, hx, hy, hp⟩ := h
    refine ⟨x, hx, ?_⟩
    rw [hp.length_eq]
    refine Nat.le_trans ?_ (Nat.le_of_eq (Nat.mul_one _))
    simp only [crossRows, List.filter_flatMap]
    exact length_flatMap_le fun r hr =>
      Rel.keyedJoin_partners_all hcat hA hF hK hwf.2.1 hkey hy (Rel.orderAllowed_arity hcat hwf.1 hx r hr)
  | left =>
    obtain ⟨x, y, hx, hy, hp⟩ := h
    refine ⟨x, hx, ?_⟩
    rw [hp.length_eq]
    refine Nat.le_trans ?_ (Nat.le_of_eq (Nat.mul_one _))
    refine length_flatMap_le fun r hr => ?_
    unfold leftJoinRow
    simp only []
    split
    · simp
    · exact Rel.keyedJoin_partners_all hcat hA hF hK hwf.2.1 hkey hy
        (Rel.orderAllowed_arity hcat hwf.1 hx r hr)

/-- **Capping joins keeps every order.** -/
theorem Rel.orderAllowed_capJoins (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hK : K.Hold cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, r.OrderAllowed cat out →
      (r.capJoins cat A F K).OrderAllowed cat out
  | .read _, _, _, h | .values _ _, _, _, h => h
  | .filter r _, hw, _, ⟨i, hi, h⟩ | .project r _, hw, _, ⟨i, hi, h⟩
  | .emit r _, hw, _, ⟨i, hi, h⟩ | .window r _ _ _, hw, _, ⟨i, hi, h⟩
  | .orderBy r _, hw, _, ⟨i, hi, h⟩ | .unnest r _, hw, _, ⟨i, hi, h⟩
  | .aggregate r _ _, hw, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capJoins hcat hA hF hK hw.1 hi, h⟩
  | .fetch r _ _, hw, _, ⟨i, hi, h⟩ | .distinct r, hw, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_capJoins hcat hA hF hK (r := r) hw hi, h⟩
  | .cross a b, hw, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capJoins hcat hA hF hK hw.1 hx, orderAllowed_capJoins hcat hA hF hK hw.2 hy,
      h⟩
  | .unionAll a b, hw, _, ⟨x, y, hx, hy, h⟩ | .semi a b _ _, hw, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_capJoins hcat hA hF hK hw.1 hx,
      orderAllowed_capJoins hcat hA hF hK hw.2.1 hy, h⟩
  | .join a b ty on, hw, out, h => by
    have hjwf : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).WF cat := by
      simp only [WF, capJoins_arity] at hw ⊢
      exact ⟨capJoins_wf hw.1, capJoins_wf hw.2.1, hw.2.2⟩
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).OrderAllowed cat out :=
      by
        cases ty with
        | inner =>
          obtain ⟨x, y, hx, hy, h⟩ := h
          exact ⟨x, y, orderAllowed_capJoins hcat hA hF hK hw.1 hx,
            orderAllowed_capJoins hcat hA hF hK hw.2.1 hy, h⟩
        | left =>
          obtain ⟨x, y, hx, hy, h⟩ := h
          refine ⟨x, y, orderAllowed_capJoins hcat hA hF hK hw.1 hx,
            orderAllowed_capJoins hcat hA hF hK hw.2.1 hy, ?_⟩
          rw [capJoins_arity]; exact h
    simp only [capJoins]
    split
    · rename_i hkey
      split
      · rename_i n hn
        refine ⟨out, hj, ?_⟩
        simp only [List.drop_zero]
        obtain ⟨x, hx, hle⟩ := join_length_le_of_keyed_all hcat hA hF hK hjwf hkey hj
        exact (List.take_of_length_le (Nat.le_trans hle (Rel.maxRows_sound_all hn hx))).symm
      · exact hj
    · exact hj

/-- Every order of the plan with capped joins is one of the plan. -/
theorem Rel.orderAllowed_of_capJoins (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hK : K.Hold cat) :
    ∀ {r : Rel}, r.WF cat → ∀ {out : Relation}, (r.capJoins cat A F K).OrderAllowed cat out →
      r.OrderAllowed cat out
  | .read _, _, _, h | .values _ _, _, _, h => h
  | .filter r _, hw, _, ⟨i, hi, h⟩ | .project r _, hw, _, ⟨i, hi, h⟩
  | .emit r _, hw, _, ⟨i, hi, h⟩ | .window r _ _ _, hw, _, ⟨i, hi, h⟩
  | .orderBy r _, hw, _, ⟨i, hi, h⟩ | .unnest r _, hw, _, ⟨i, hi, h⟩
  | .aggregate r _ _, hw, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_of_capJoins hcat hA hF hK hw.1 hi, h⟩
  | .fetch r _ _, hw, _, ⟨i, hi, h⟩ | .distinct r, hw, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_of_capJoins hcat hA hF hK (r := r) hw hi, h⟩
  | .cross a b, hw, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_of_capJoins hcat hA hF hK hw.1 hx,
      orderAllowed_of_capJoins hcat hA hF hK hw.2 hy, h⟩
  | .unionAll a b, hw, _, ⟨x, y, hx, hy, h⟩ | .semi a b _ _, hw, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_of_capJoins hcat hA hF hK hw.1 hx,
      orderAllowed_of_capJoins hcat hA hF hK hw.2.1 hy, h⟩
  | .join a b ty on, hw, out, h => by
    have hjwf : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).WF cat := by
      simp only [WF, capJoins_arity] at hw ⊢
      exact ⟨capJoins_wf hw.1, capJoins_wf hw.2.1, hw.2.2⟩
    have back : ∀ {o}, (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).OrderAllowed
        cat o → (Rel.join a b ty on).OrderAllowed cat o := fun h => by
      cases ty with
      | inner =>
        obtain ⟨x, y, hx, hy, h⟩ := h
        exact ⟨x, y, orderAllowed_of_capJoins hcat hA hF hK hw.1 hx,
          orderAllowed_of_capJoins hcat hA hF hK hw.2.1 hy, h⟩
      | left =>
        obtain ⟨x, y, hx, hy, h⟩ := h
        refine ⟨x, y, orderAllowed_of_capJoins hcat hA hF hK hw.1 hx,
          orderAllowed_of_capJoins hcat hA hF hK hw.2.1 hy, ?_⟩
        rw [← capJoins_arity (cat := cat) (A := A) (F := F) (K := K) b]; exact h
    simp only [capJoins] at h
    split at h
    · rename_i hkey
      split at h
      · rename_i n hn
        obtain ⟨i, hi, heq⟩ := h
        dsimp only at heq
        obtain ⟨x, hx, hle⟩ := join_length_le_of_keyed_all hcat hA hF hK hjwf hkey hi
        rw [heq, List.drop_zero, List.take_of_length_le (Nat.le_trans hle (Rel.maxRows_sound_all hn hx))]
        exact back hi
      · exact back h
    · exact back h



theorem Rel.capJoins_smallAll (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hK : K.Hold cat) :
    ∀ {r : Rel}, r.WF cat → r.SmallAll cat → (r.capJoins cat A F K).SmallAll cat
  | .read _, _, h | .values _ _, _, h => h
  | .filter r _, hw, h | .project r _, hw, h | .emit r _, hw, h | .orderBy r _, hw, h
  | .unnest r _, hw, h => capJoins_smallAll hcat hA hF hK (r := r) hw.1 h
  | .fetch r _ _, hw, h | .distinct r, hw, h => capJoins_smallAll hcat hA hF hK (r := r) hw h
  | .aggregate r _ _, hw, h | .window r _ _ _, hw, h =>
    ⟨fun i hi => h.1 i (orderAllowed_of_capJoins hcat hA hF hK hw.1 hi),
      capJoins_smallAll hcat hA hF hK hw.1 h.2⟩
  | .cross a b, hw, h =>
    ⟨capJoins_smallAll hcat hA hF hK hw.1 h.1, capJoins_smallAll hcat hA hF hK hw.2 h.2⟩
  | .unionAll a b, hw, h | .semi a b _ _, hw, h =>
    ⟨capJoins_smallAll hcat hA hF hK hw.1 h.1, capJoins_smallAll hcat hA hF hK hw.2.1 h.2⟩
  | .join a b ty on, hw, h => by
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).SmallAll cat :=
      ⟨capJoins_smallAll hcat hA hF hK hw.1 h.1, capJoins_smallAll hcat hA hF hK hw.2.1 h.2⟩
    simp only [capJoins]
    split
    · split
      · exact hj
      · exact hj
    · exact hj

theorem sumWraps_not_mem_issues {row : Row} {d e : Expr} (h : (Issue.sumWraps, e) ∈ d.issues row) :
    False := Expr.issues_ne_sumWraps h rfl

theorem Rel.viewIssue_ne_sumWraps {r : Rel} {d e : Expr} (h : r.ViewIssue cat d (.sumWraps, e)) :
    False :=
  let ⟨_, _, _, _, _, _, hp⟩ := h; sumWraps_not_mem_issues hp

/-- A `SUM` that overflows on some order of the plan overflows on that order
of the plan with capped joins. -/
theorem Rel.sumWraps_capJoins_all (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) (hK : K.Hold cat) :
    ∀ {u : Bool} {r : Rel} {e : Expr}, r.WF cat → r.HasIssueAll cat u (.sumWraps, e) →
      (r.capJoins cat A F K).HasIssueAll cat u (.sumWraps, e)
  | _, .read _, _, _, h | _, .values _ _, _, _, h => h.elim
  | _, .filter r _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    rcases h with h | ⟨_, _, _, _, hp⟩ | hv
    · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (viewIssue_ne_sumWraps hv).elim
  | _, .project r _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    rcases h with h | ⟨_, _, _, _, _, _, hp⟩ | ⟨_, _, _, hv⟩
    · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (viewIssue_ne_sumWraps hv).elim
  | _, .emit r _, _, hw, h | _, .orderBy r _, _, hw, h | _, .unnest r _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    exact sumWraps_capJoins_all hcat hA hF hK hw.1 h
  | _, .fetch r _ _, _, hw, h | _, .distinct r, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    exact sumWraps_capJoins_all hcat hA hF hK (r := r) hw h
  | _, .window r _ _ _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    rcases h with h | ⟨i, hi, h⟩
    · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
    · exact .inr ⟨i, orderAllowed_capJoins hcat hA hF hK hw.1 hi, h⟩
  | _, .cross a b, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    exact h.imp (sumWraps_capJoins_all hcat hA hF hK hw.1) (sumWraps_capJoins_all hcat hA hF hK hw.2)
  | _, .unionAll a b, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    exact h.imp (sumWraps_capJoins_all hcat hA hF hK hw.1)
      (sumWraps_capJoins_all hcat hA hF hK hw.2.1)
  | _, .semi a b _ _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    rcases h with h | h | ⟨_, _, _, _, _, _, _, _, hp⟩ | hv
    · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
    · exact .inr (.inl (sumWraps_capJoins_all hcat hA hF hK hw.2.1 h))
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (viewIssue_ne_sumWraps hv).elim
  | u, .join a b ty on, e, hw, h => by
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).HasIssueAll cat u
        (.sumWraps, e) := by
      simp only [HasIssueAll] at h ⊢
      rcases h with h | h | ⟨_, _, _, _, _, _, _, _, hp⟩ | hv
      · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
      · exact .inr (.inl (sumWraps_capJoins_all hcat hA hF hK hw.2.1 h))
      · exact (sumWraps_not_mem_issues hp).elim
      · exact (viewIssue_ne_sumWraps hv).elim
    simp only [capJoins]
    split
    · split
      · simp only [HasIssueAll]; exact hj
      · exact hj
    · exact hj
  | _, .aggregate r _ _, _, hw, h => by
    simp only [HasIssueAll, capJoins] at h ⊢
    rcases h with h | ⟨_, _, _, _, _, _, hp⟩ | ⟨i, hi, h⟩ | ⟨_, _, _, hv⟩
    · exact .inl (sumWraps_capJoins_all hcat hA hF hK hw.1 h)
    · exact (sumWraps_not_mem_issues hp).elim
    · exact .inr (.inr (.inl ⟨i, orderAllowed_capJoins hcat hA hF hK hw.1 hi, h⟩))
    · exact (viewIssue_ne_sumWraps hv).elim

end

/-! ## Rows per key on every order -/

omit [Boxes.Ambient] in
/-- A `DISTINCT`'s representatives have no more rows per key than its input:
keys compare classes (`keyOf`), and each representative stands for a class
of its own. -/
theorem RowsPer.of_reps {k : List Nat} {n : Nat} {rows reps : Relation} (h : RowsPer k n rows)
    (hd : IsReps Row.canon rows reps) : RowsPer k n reps := fun v => by
  have hnd : ((reps.filter fun row => decide (keyOf k row = v)).map Row.canon).Nodup :=
    List.pairwise_map.2 ((hd.1.sublist List.filter_sublist).imp id)
  have hsub : ((reps.filter fun row => decide (keyOf k row = v)).map Row.canon) ⊆
      ((rows.filter fun row => decide (keyOf k row = v)).map Row.canon) := fun z hz => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    obtain ⟨hx, hv⟩ := List.mem_filter.1 hx
    obtain ⟨y, hy, ex⟩ := hd.class_mem hx
    rw [ex]
    refine List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, ?_⟩, rfl⟩
    rwa [← keyOf_eq_of_canon ex]
  have := hnd.length_le_of_subset hsub
  simp only [List.length_map] at this
  exact Nat.le_trans this (h v)

section
variable {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
  {K : TableCond} {P : String → List (List Nat × Nat)}

/-- **The bounds on rows per key hold on every order.** -/
theorem Rel.perKey_sound_all (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : K.Hold cat)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → ∀ kn ∈ r.perKey cat A F K P, ∀ {out : Relation},
      r.OrderAllowed cat out → RowsPer kn.1 kn.2 out
  | .read t, _, kn, h, _, ho => (hP t kn h).perm ho
  | .values _ _, _, _, h, _, _ | .cross _ _, _, _, h, _, _ | .window _ _ _ _, _, _, h, _, _
  | .aggregate _ _ _, _, _, h, _, _ | .unnest _ _, _, _, h, _, _ => by simp [perKey] at h
  | .filter r _, hw, kn, h, _, ⟨i, hi, ho⟩ => by
    simp only [perKey] at h; subst ho
    exact (perKey_sound_all hcat hA hF hK hP hw.1 kn h hi).sublist List.filter_sublist
  | .semi r _ _ _, hw, kn, h, _, ⟨x, _, hx, _, ho⟩ => by
    simp only [perKey] at h
    exact ((perKey_sound_all hcat hA hF hK hP hw.1 kn h hx).sublist List.filter_sublist).perm ho
  | .fetch r _ c, hw, kn, h, _, ⟨i, hi, ho⟩ => by
    simp only [perKey] at h; subst ho
    have hr := perKey_sound_all hcat hA hF hK hP (r := r) hw kn h hi
    cases c with
    | none => exact hr.sublist (List.drop_sublist _ _)
    | some n => exact hr.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  | .orderBy r _, hw, kn, h, _, ⟨i, hi, ho, _⟩ => by
    simp only [perKey] at h
    exact (perKey_sound_all hcat hA hF hK hP hw.1 kn h hi).perm ho
  | .distinct r, hw, kn, h, _, ⟨i, hi, d, hd, ho⟩ => by
    simp only [perKey] at h
    exact ((perKey_sound_all hcat hA hF hK hP (r := r) hw kn h hi).of_reps hd).perm ho
  | .project r es, hw, kn, h, _, ⟨i, hi, ho⟩ => by
    simp only [perKey, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at h
    subst ho
    exact (perKey_sound_all hcat hA hF hK hP hw.1 kn h.1 hi).map fun x hx =>
      keyOf_append_left fun c hc => (orderAllowed_arity hcat hw.1 hi x hx) ▸ h.2 c hc
  | .emit r m, hw, kn, h, _, ⟨i, hi, ho⟩ => by
    simp only [perKey, List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨k, n⟩, hkn, k', hk', rfl⟩ := h
    subst ho
    exact (perKey_sound_all hcat hA hF hK hP hw.1 _ hkn hi).map fun x _ => emitKey_keyOf hk'
  | .unionAll a b, hw, kn, h, _, ⟨x, y, hx, hy, ho⟩ => by
    simp only [perKey, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨⟨k, m⟩, hk, ⟨k', n⟩, hk', hkn⟩ := h
    split at hkn
    · rename_i heq
      subst heq
      simp only [Option.some.injEq] at hkn; subst hkn
      exact ((perKey_sound_all hcat hA hF hK hP hw.1 _ hk hx).append
        (perKey_sound_all hcat hA hF hK hP hw.2.1 _ hk' hy)).perm ho
    · cases hkn
  | .join a b ty on, hw, kn, h, out, ho => by
    simp only [perKey] at h
    split at h
    · rename_i hkey
      simp only [List.mem_filter, List.mem_append, List.mem_map, List.all_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨hmem, hlt⟩ := h
      have side : ∀ {x y : Relation}, a.OrderAllowed cat x → b.OrderAllowed cat y →
          RowsPer kn.1 kn.2 x ∧ ∀ r ∈ x,
            (((y.map (r ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ 1 ∧
              ∀ row ∈ (y.map (r ++ ·)).filter (fun row => (on.eval row).isTrue), ∃ z, row = r ++ z) :=
        fun hx hy => by
          refine ⟨?_, fun r hr => ⟨?_, fun row hrow => ?_⟩⟩
          · rcases hmem with hm | ⟨k, hk, rfl⟩
            · exact perKey_sound_all hcat hA hF hK hP hw.1 kn hm hx
            · exact RowsPer.of_keyOn (Rel.keys_sound_all hcat hA hF hK hw.1 k hk hx)
          · exact Rel.keyedJoin_partners_all hcat hA hF hK hw.2.1 hkey hy
              (orderAllowed_arity hcat hw.1 hx r hr)
          · obtain ⟨z, _, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hrow).1
            exact ⟨z, rfl⟩
      cases ty with
      | inner =>
        obtain ⟨x, y, hx, hy, hp⟩ := ho
        obtain ⟨ha, hg⟩ := side hx hy
        refine RowsPer.perm ?_ hp
        simp only [crossRows, List.filter_flatMap]
        exact ha.flatMap_prefix hlt (fun r hr => orderAllowed_arity hcat hw.1 hx r hr) hg
      | left =>
        obtain ⟨x, y, hx, hy, hp⟩ := ho
        obtain ⟨ha, hg⟩ := side hx hy
        refine RowsPer.perm ?_ hp
        refine ha.flatMap_prefix hlt (fun r hr => orderAllowed_arity hcat hw.1 hx r hr) fun r hr => ?_
        unfold leftJoinRow
        simp only []
        split
        · exact ⟨by simp, fun row hrow => ⟨_, by simpa using hrow⟩⟩
        · exact hg r hr
    · simp at h

/-- `Rel.groupRows` bounds the groups of every order of the input. -/
theorem Rel.groupRows_sound_all (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : K.Hold cat)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) {r : Rel} (hw : r.WF cat)
    {i : Relation} (hi : r.OrderAllowed cat i)
    {gs : List Expr} {grp : Relation} (hg : grp ∈ aggGroups gs i) :
    ∀ n, r.groupRows cat A F K P gs = some n → grp.length ≤ n := fun n hn => by
  refine le_leastOf (fun m hm => ?_) hn
  simp only [List.mem_map, List.mem_filter, List.mem_append] at hm
  obtain ⟨⟨k, m'⟩, ⟨hmem, hc⟩, rfl⟩ := hm
  have hrp : RowsPer k m' i := by
    rcases hmem with h | h
    · exact perKey_sound_all hcat hA hF hK hP hw _ h hi
    · obtain ⟨k', hk', heq⟩ := h
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      exact RowsPer.of_keyOn (Rel.keys_sound_all hcat hA hF hK hw k' hk' hi)
  exact length_le_of_rowsPer hrp (sublist_of_mem_aggGroups hg) (keyOf_eq_of_mem_aggGroups hc hg)

/-- **An integer `SUM` that `Rel.sumsPer` leaves out fits, on every order.** -/
theorem Rel.sumsPer_sound_all (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    (hK : K.Hold cat)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) :
    ∀ {u : Bool} {r : Rel} {e : Expr}, r.WF cat → r.SmallAll cat →
      r.HasIssueAll cat u (.sumWraps, e) → e ∈ r.sumsPer cat A F T K P
  | _, .read _, _, _, _, h | _, .values _ _, _, _, _, h => h.elim
  | _, .filter r _, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer]
    rcases h with h | ⟨_, _, _, _, hp⟩ | hv
    · exact sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs h
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (Rel.viewIssue_ne_sumWraps hv).elim
  | _, .project r _, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer]
    rcases h with h | ⟨_, _, _, _, _, _, hp⟩ | ⟨_, _, _, hv⟩
    · exact sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs h
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (Rel.viewIssue_ne_sumWraps hv).elim
  | _, .emit r _, _, hw, hs, h | _, .orderBy r _, _, hw, hs, h | _, .unnest r _, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer]
    exact sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs h
  | _, .fetch r _ _, _, hw, hs, h | _, .distinct r, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer]
    exact sumsPer_sound_all hcat hA hF hT hK hP (r := r) hw hs h
  | _, .window r _ _ _, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨_, _, ⟨m, hm, hf, heq, _⟩ | ⟨_, _, heq, _⟩ | ⟨_, _, heq, _⟩⟩
    · exact .inl (sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs.2 h)
    · simp only [Prod.mk.injEq] at heq
      exact .inr ⟨m, hm, by simp [hf, heq.2]⟩
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim
  | _, .cross a b, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer, List.mem_append]
    exact h.imp (sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs.1)
      (sumsPer_sound_all hcat hA hF hT hK hP hw.2 hs.2)
  | _, .unionAll a b, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer, List.mem_append]
    exact h.imp (sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs.1)
      (sumsPer_sound_all hcat hA hF hT hK hP hw.2.1 hs.2)
  | _, .semi a b _ _, _, hw, hs, h | _, .join a b _ _, _, hw, hs, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer, List.mem_append]
    rcases h with h | h | ⟨_, _, _, _, _, _, _, _, hp⟩ | hv
    · exact .inl (sumsPer_sound_all hcat hA hF hT hK hP hw.1 hs.1 h)
    · exact .inr (sumsPer_sound_all hcat hA hF hT hK hP hw.2.1 hs.2 h)
    · exact (sumWraps_not_mem_issues hp).elim
    · exact (Rel.viewIssue_ne_sumWraps hv).elim
  | _, .aggregate r gs ms, _, hw, ⟨_, hsm⟩, h => by
    simp only [HasIssueAll] at h; simp only [sumsPer, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨_, _, _, _, _, _, hp⟩ |
      ⟨i, hi, ⟨m, hm, hf, heq, grp, hgrp, hov⟩ | ⟨_, _, heq, _⟩ | ⟨_, _, heq, _⟩⟩ | ⟨_, _, _, hv⟩
    · exact .inl (sumsPer_sound_all hcat hA hF hT hK hP hw.1 hsm h)
    · exact (sumWraps_not_mem_issues hp).elim
    · simp only [Prod.mk.injEq] at heq
      have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T))
          (r.groupRows cat A F K P gs) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T))
            (r.groupRows cat A F K P gs)
        · rfl
        · have := Measure.sumFits_sound (grp := grp) (fun y hy => by
              have hyr := mem_of_mem_aggGroups hgrp hy
              exact Expr.absD_sound
                (aeval_sound_allSz hcat hA hF hT (sz := true) hw.1 (fun _ => hsm) hi y hyr)
                (facts_sound_all hcat hF hT hw.1 hi y hyr) (KsHold.nil y) m.arg)
            (Rel.groupRows_sound_all hcat hA hF hK hP hw.1 hi hgrp) hfit
          rw [hov] at this; cases this
      exact .inr ⟨m, hm, by simp [hf, hfits, heq.2]⟩
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim
    · exact (Rel.viewIssue_ne_sumWraps hv).elim

end

/-- **Soundness with row caps, on every order**: every issue that can happen
on any order of a well-formed plan, on tables within their caps and bounds
per key, is among `Rel.issuesCapped`, the views of join inputs included. -/
theorem Rel.issuesCapped_sound_all {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {K : TableCond} (hK : K.Hold cat)
    {caps : String → Option Nat} (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    {P : String → List (List Nat × Nat)} (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows)
    {r : Rel} (hwf : r.WF cat) (hsm : r.SmallAll cat) (p : Issue × Expr)
    (h : r.HasIssueAll cat false p) : p ∈ r.issuesCapped cat A F T K caps P := by
  simp only [issuesCapped, List.mem_append, List.mem_filter]
  obtain ⟨i, e⟩ := p
  have hrw : (r.capReads caps).WF cat := Rel.capReads_wf hwf
  have hrs := Rel.capReads_smallAll hcap hsm
  by_cases hi : i = .sumWraps
  · subst hi
    have h' := Rel.sumWraps_capJoins_all hcat hA hF hK (K := K) hrw (Rel.hasIssueAll_capReads hcap h)
    have hwf' := Rel.capJoins_wf (A := A) (F := F) (K := K) hrw
    have hsm' := Rel.capJoins_smallAll (A := A) (F := F) (K := K) hcat hA hF hK hrw hrs
    exact .inr ⟨mayIssues_sound_all hcat hA hF hT hwf' hsm' _ h',
      by
        have := Rel.sumsPer_sound_all hcat hA hF hT hK hP hwf' hsm' h'
        simp only [capped] at this ⊢
        simp [this]⟩
  · exact .inl ⟨mayIssues_sound_all hcat hA hF hT hrw hrs _ (Rel.hasIssueAll_capReads hcap h),
      by simp [hi]⟩

end Substrait

namespace Substrait.ContractCheck

open Lean (Json)
open Parse

variable [Boxes.Ambient]

/-- **Every issue that can happen on any order is reported**
(`Rel.issuesCapped_sound_all`): on data that meets the request and its bounds
per key (`rows_per`), and whose windows and aggregates read fewer rows than
the size hypothesis allows on every order (`Rel.SmallAll`), each issue of the
transformation on any order the reference allows, on the views of its join
inputs included (`Rel.HasIssueAll`), is in the report, but an overflow to
`±∞` of a scalar operation under a profile other than the reference, where it is the engine's
value. -/
theorem check_issues_sound_all {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data) {T : Plan} (hT : R.transform = some T)
    (hP : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows)
    (hsm : T.root.SmallAll data) :
    ∀ p, T.root.HasIssueAll data false p →
      p ∈ rep.issues ∨ (p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs) := by
  intro p hp
  have hok := Request.check_ok (check_parse hR hc)
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys hD.ranges
  have hwf := check_transform_wf hR hc hD hT
  have hin := Rel.issuesCapped_sound_all hD.wf hK.cols hK.facts (hK.windows hD.wf) hK.keys hD.caps
    hP hwf hsm p hp
  rw [Rel.issuesCapped_congr hD.arity] at hin
  have htw := hok.transformWF
  simp only [hT, Option.all_some] at htw
  rw [hok.issues]
  simp only [Request.issuesIn, hT, htw, ↓reduceIte, List.mem_filter, List.mem_eraseDups,
    List.mem_append, KnowledgeEnv.windows, ← Rel.keyedWindows_congr hD.arity]
  by_cases hinf : p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs
  · exact .inr hinf
  · refine .inl ⟨.inl (by simpa [KnowledgeEnv.windows] using hin), ?_⟩
    obtain ⟨i, e⟩ := p
    simp only at hinf ⊢
    cases hr : R.underReference
    · by_cases hi : i = .infinite
      · subst hi
        by_cases he : e ∈ T.root.aggArgs
        · simp [he]
        · exact absurd ⟨rfl, hr, he⟩ hinf
      · simp [hi]
    · simp

end Substrait.ContractCheck
