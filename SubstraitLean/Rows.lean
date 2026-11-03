import SubstraitLean.Safety
import SubstraitLean.Guards
import SubstraitLean.Keys

/-!
# Row caps that rule out `SUM` overflow (#219)

`Rel.maxRows` (`SubstraitLean/Contracts.lean`) bounds the rows of a plan from
its shape: a `VALUES` list, a `FETCH` count, a product of joins. `sverify`
caps each read of a table with a `max_rows` precondition with a `FETCH`
(`Rel.capReads`). This file adds the other cap and puts both to use:

* A join whose condition determines a key of its right side gives each left
  row at most one partner (`Rel.join_length_le_of_keyed`), so it has at most
  the left side's rows. `Rel.capJoins` wraps such a join in a `FETCH` of
  that many, which changes no rows (`Rel.capJoins_eval`): `Rel.maxRows` then
  bounds it by the left side alone, where the product would be far too large.
* Capped reads change neither the rows nor the loose rows of a plan, so
  every issue of the plan is one of the plan with capped reads
  (`Rel.hasIssue_capReads`). There a double `SUM` or `AVG` has its error
  bound (#85), and a cast of it to an integer or a decimal can be proved to
  fit.
* An integer `SUM` overflows only on a group or window frame of the plan's
  rows, which the plan with capped joins has too (`Rel.sumWraps_capJoins`).
  So its `SUM`s are decided on the plan with capped reads and joins, where
  `Rel.mayIssues` drops a `SUM` whose rows and values keep it within 64 bits
  (`Measure.sumFits`). Every other issue is decided on the plan with capped
  reads only: capping a join changes the loose rows a filter condition is
  evaluated on. `Rel.issuesCapped_sound` puts the two together.
-/

namespace Substrait

/-- Each join that determines a key of its right side, wrapped in a `FETCH`
of as many rows as `Rel.maxRows` bounds its left side by. -/
def Rel.capJoins (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (r.capJoins cat A F K) c
  | .project r es => .project (r.capJoins cat A F K) es
  | .emit r m => .emit (r.capJoins cat A F K) m
  | .cross a b => .cross (a.capJoins cat A F K) (b.capJoins cat A F K)
  | .join a b ty on =>
    if Rel.keyedJoin cat A F K (a.capJoins cat A F K) (b.capJoins cat A F K) on then
      match (a.capJoins cat A F K).maxRows with
      | some n => .fetch (.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on) 0 (some n)
      | none => .join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on
    else .join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on
  | .fetch r o c => .fetch (r.capJoins cat A F K) o c
  | .unionAll a b => .unionAll (a.capJoins cat A F K) (b.capJoins cat A F K)
  | .window r p s fns => .window (r.capJoins cat A F K) p s fns
  | .semi a b anti on => .semi (a.capJoins cat A F K) (b.capJoins cat A F K) anti on
  | .orderBy r k => .orderBy (r.capJoins cat A F K) k
  | .distinct r => .distinct (r.capJoins cat A F K)
  | .aggregate r gs ms => .aggregate (r.capJoins cat A F K) gs ms
  | .unnest r c => .unnest (r.capJoins cat A F K) c

section
variable {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
  {K : String → List (List Nat)}

theorem Rel.capJoins_arity : ∀ r : Rel, (r.capJoins cat A F K).arity cat = r.arity cat
  | .read _ | .values _ _ | .emit _ _ | .aggregate _ _ _ => rfl
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ => by
    simp only [capJoins, arity]; exact capJoins_arity r
  | .project r _ | .window r _ _ _ => by simp only [capJoins, arity, capJoins_arity r]
  | .cross a b => by simp only [capJoins, arity, capJoins_arity a, capJoins_arity b]
  | .unionAll a _ | .semi a _ _ _ => by simp only [capJoins, arity, capJoins_arity a]
  | .join a b _ _ => by
    simp only [capJoins]
    split
    · split <;> simp only [arity, capJoins_arity a, capJoins_arity b]
    · simp only [arity, capJoins_arity a, capJoins_arity b]

theorem Rel.capJoins_wf : ∀ {r : Rel}, r.WF cat → (r.capJoins cat A F K).WF cat
  | .read _, h | .values _ _, h => h
  | .filter r _, h | .project r _, h | .emit r _, h | .window r _ _ _, h | .orderBy r _, h
  | .aggregate r _ _, h | .unnest r _, h => by
    simp only [capJoins, WF, capJoins_arity] at h ⊢
    exact ⟨capJoins_wf h.1, h.2⟩
  | .fetch r _ _, h | .distinct r, h => by
    simp only [capJoins, WF] at h ⊢
    exact capJoins_wf (r := r) h
  | .cross a b, h => ⟨capJoins_wf h.1, capJoins_wf h.2⟩
  | .unionAll a b, h => by
    simp only [capJoins, WF, capJoins_arity] at h ⊢
    exact ⟨capJoins_wf h.1, capJoins_wf h.2.1, h.2.2⟩
  | .semi a b _ _, h => by
    simp only [capJoins, WF, capJoins_arity] at h ⊢
    exact ⟨capJoins_wf h.1, capJoins_wf h.2.1, h.2.2⟩
  | .join a b ty on, h => by
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).WF cat := by
      simp only [WF, capJoins_arity] at h ⊢
      exact ⟨capJoins_wf h.1, capJoins_wf h.2.1, h.2.2⟩
    simp only [capJoins]
    split
    · split
      · exact hj
      · exact hj
    · exact hj

/-- **Capping joins changes nothing.** -/
theorem Rel.capJoins_eval (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → (r.capJoins cat A F K).eval cat = r.eval cat
  | .read _, _ | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .window r _ _ _, h | .orderBy r _, h
  | .aggregate r _ _, h | .unnest r _, h => by
    simp only [capJoins, eval, capJoins_eval hcat hA hF hK h.1]
  | .fetch r _ _, h | .distinct r, h => by
    simp only [capJoins, eval, capJoins_eval hcat hA hF hK (r := r) h]
  | .cross a b, h => by
    simp only [capJoins, eval, capJoins_eval hcat hA hF hK h.1, capJoins_eval hcat hA hF hK h.2]
  | .unionAll a b, h | .semi a b _ _, h => by
    simp only [capJoins, eval, capJoins_eval hcat hA hF hK h.1, capJoins_eval hcat hA hF hK h.2.1]
  | .join a b ty on, h => by
    have ea := capJoins_eval hcat hA hF hK h.1
    have eb := capJoins_eval hcat hA hF hK h.2.1
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).eval cat =
        (Rel.join a b ty on).eval cat := by
      cases ty <;> simp only [eval, ea, eb, capJoins_arity]
    have hjwf : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).WF cat := by
      simp only [WF, capJoins_arity] at h ⊢
      exact ⟨capJoins_wf h.1, capJoins_wf h.2.1, h.2.2⟩
    simp only [capJoins]
    split
    · rename_i hkey
      split
      · rename_i n hn
        simp only [eval, List.drop_zero]
        rw [List.take_of_length_le, hj]
        exact Nat.le_trans (Rel.join_length_le_of_keyed hcat hA hF hK hjwf hkey)
          (Rel.maxRows_sound hn)
      · exact hj
    · exact hj

theorem Rel.capJoins_small (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → r.Small cat → (r.capJoins cat A F K).Small cat
  | .read _, _, h | .values _ _, _, h => h
  | .filter r _, hw, h | .project r _, hw, h | .emit r _, hw, h | .orderBy r _, hw, h
  | .aggregate r _ _, hw, h | .unnest r _, hw, h => capJoins_small hcat hA hF hK (r := r) hw.1 h
  | .fetch r _ _, hw, h | .distinct r, hw, h => capJoins_small hcat hA hF hK (r := r) hw h
  | .window r _ _ _, hw, h => by
    simp only [capJoins, Small, capJoins_eval hcat hA hF hK hw.1] at h ⊢
    exact ⟨h.1, capJoins_small hcat hA hF hK hw.1 h.2⟩
  | .cross a b, hw, h => ⟨capJoins_small hcat hA hF hK hw.1 h.1, capJoins_small hcat hA hF hK hw.2 h.2⟩
  | .unionAll a b, hw, h | .semi a b _ _, hw, h =>
    ⟨capJoins_small hcat hA hF hK hw.1 h.1, capJoins_small hcat hA hF hK hw.2.1 h.2⟩
  | .join a b ty on, hw, h => by
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).Small cat :=
      ⟨capJoins_small hcat hA hF hK hw.1 h.1, capJoins_small hcat hA hF hK hw.2.1 h.2⟩
    simp only [capJoins]
    split
    · split
      · exact hj
      · exact hj
    · exact hj

end

section
variable {cat : Catalog} {caps : String → Option Nat}

theorem Rel.capReads_wf : ∀ {r : Rel}, r.WF cat → (r.capReads caps).WF cat
  | .read t, h => by unfold capReads; split <;> trivial
  | .values _ _, h => h
  | .filter r _, h | .project r _, h | .emit r _, h | .window r _ _ _, h | .orderBy r _, h
  | .aggregate r _ _, h | .unnest r _, h => by
    simp only [capReads, WF, capReads_arity] at h ⊢
    exact ⟨capReads_wf h.1, h.2⟩
  | .fetch r _ _, h | .distinct r, h => by
    simp only [capReads, WF] at h ⊢
    exact capReads_wf (r := r) h
  | .cross a b, h => ⟨capReads_wf h.1, capReads_wf h.2⟩
  | .unionAll a b, h | .semi a b _ _, h | .join a b _ _, h => by
    simp only [capReads, WF, capReads_arity] at h ⊢
    exact ⟨capReads_wf h.1, capReads_wf h.2.1, h.2.2⟩

theorem Rel.capReads_small (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {r : Rel}, r.Small cat → (r.capReads caps).Small cat
  | .read t, h => by unfold capReads; split <;> trivial
  | .values _ _, h => h
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h | .aggregate r _ _, h
  | .unnest r _, h | .fetch r _ _, h | .distinct r, h => capReads_small hcap (r := r) h
  | .window r _ _ _, h => by
    simp only [capReads, Small, capReads_eval hcap] at h ⊢
    exact ⟨h.1, capReads_small hcap h.2⟩
  | .cross a b, h | .unionAll a b, h | .semi a b _ _, h | .join a b _ _, h =>
    ⟨capReads_small hcap h.1, capReads_small hcap h.2⟩

end

/-! ## `SUM`s of the plan are `SUM`s of the capped plan -/

theorem sumWraps_ne_domain {e e' : Expr} (h : ((Issue.sumWraps, e) : Issue × Expr) = (.domain, e')) :
    False := by simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

/-- Capping reads commutes with loosening: `FETCH` stops `Rel.loose`. -/
theorem Rel.capReads_loose (caps : String → Option Nat) :
    ∀ r : Rel, (r.capReads caps).loose = r.loose.capReads caps
  | .read t => by simp only [capReads, loose]; split <;> rfl
  | .values _ _ | .fetch _ _ _ | .window _ _ _ _ | .aggregate _ _ _ => rfl
  | .filter r _ | .semi r _ _ _ | .orderBy r _ | .distinct r => by
    simp only [capReads, loose]; exact capReads_loose caps r
  | .project r _ | .emit r _ => by simp only [capReads, loose, capReads_loose caps r]
  | .cross a b | .unionAll a b | .join a b .inner _ | .join a b .left _ => by
    simp only [capReads, loose, capReads_loose caps a, capReads_loose caps b]
  | .unnest r _ => by simp only [capReads, loose, capReads_loose caps r]

theorem Rel.capReads_eval_ite (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    (u : Bool) (r : Rel) :
    (if u then (r.capReads caps).loose else r.capReads caps).eval cat =
      (if u then r.loose else r).eval cat := by
  cases u <;> simp only [Bool.false_eq_true, ↓reduceIte, capReads_loose, capReads_eval hcap]

/-- An issue of the plan is an issue of the plan with capped reads, on tables
within their caps: both have the same rows and the same loose rows. -/
theorem Rel.hasIssue_capReads {cat : Catalog} {caps : String → Option Nat}
    (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n) :
    ∀ {u : Bool} {r : Rel} {p : Issue × Expr}, r.HasIssue cat u p →
      (r.capReads caps).HasIssue cat u p
  | _, .read _, _, h | _, .values _ _, _, h => h.elim
  | _, .filter r _, _, h => by
    simp only [HasIssue, capReads, capReads_loose, capReads_eval hcap] at h ⊢
    exact h.imp (hasIssue_capReads hcap) id
  | _, .project r _, _, h => by
    simp only [HasIssue, capReads, capReads_eval_ite hcap] at h ⊢
    exact h.imp (hasIssue_capReads hcap) id
  | _, .emit r _, _, h | _, .fetch r _ _, _, h | _, .orderBy r _, _, h | _, .distinct r, _, h
  | _, .unnest r _, _, h => by
    simp only [HasIssue, capReads] at h ⊢
    exact hasIssue_capReads hcap (r := r) h
  | _, .window r _ _ _, _, h => by
    simp only [HasIssue, capReads, capReads_eval hcap] at h ⊢
    exact h.imp (hasIssue_capReads hcap) id
  | _, .cross a b, _, h | _, .unionAll a b, _, h => by
    simp only [HasIssue, capReads] at h ⊢
    exact h.imp (hasIssue_capReads hcap) (hasIssue_capReads hcap)
  | _, .join a b _ _, _, h | _, .semi a b _ _, _, h => by
    simp only [HasIssue, capReads, capReads_loose, capReads_eval hcap] at h ⊢
    exact h.imp (hasIssue_capReads hcap) (Or.imp (hasIssue_capReads hcap) id)
  | _, .aggregate r _ _, _, h => by
    simp only [HasIssue, capReads, capReads_eval hcap, capReads_eval_ite hcap] at h ⊢
    exact h.imp (hasIssue_capReads hcap) id

/-- A `SUM` that overflows on the plan overflows on the plan with capped
joins. -/
theorem Rel.sumWraps_capJoins {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) :
    ∀ {u : Bool} {r : Rel} {e : Expr}, r.WF cat → r.HasIssue cat u (.sumWraps, e) →
      (r.capJoins cat A F K).HasIssue cat u (.sumWraps, e)
  | _, .read _, _, _, h | _, .values _ _, _, _, h => h.elim
  | _, .filter r _, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    rcases h with h | ⟨_, _, hp⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .project r _, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    rcases h with h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .emit r _, _, hw, h | _, .orderBy r _, _, hw, h | _, .unnest r _, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    exact sumWraps_capJoins hcat hA hF hK hw.1 h
  | _, .fetch r _ _, _, hw, h | _, .distinct r, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    exact sumWraps_capJoins hcat hA hF hK (r := r) hw h
  | _, .window r _ _ _, _, hw, h => by
    simp only [HasIssue, capJoins, capJoins_eval hcat hA hF hK hw.1] at h ⊢
    rcases h with h | h | ⟨_, _, heq, _⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact .inr (.inl h)
    · exact (sumWraps_ne_domain heq).elim
  | _, .cross a b, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    exact h.imp (sumWraps_capJoins hcat hA hF hK hw.1) (sumWraps_capJoins hcat hA hF hK hw.2)
  | _, .unionAll a b, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    exact h.imp (sumWraps_capJoins hcat hA hF hK hw.1) (sumWraps_capJoins hcat hA hF hK hw.2.1)
  | _, .semi a b _ _, _, hw, h => by
    simp only [HasIssue, capJoins] at h ⊢
    rcases h with h | h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact .inr (.inl (sumWraps_capJoins hcat hA hF hK hw.2.1 h))
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | u, .join a b ty on, e, hw, h => by
    have hj : (Rel.join (a.capJoins cat A F K) (b.capJoins cat A F K) ty on).HasIssue cat u
        (.sumWraps, e) := by
      simp only [HasIssue] at h ⊢
      rcases h with h | h | ⟨_, _, _, _, hp⟩
      · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
      · exact .inr (.inl (sumWraps_capJoins hcat hA hF hK hw.2.1 h))
      · exact absurd rfl (Expr.issues_ne_sumWraps hp)
    simp only [capJoins]
    split
    · split
      · simp only [HasIssue]; exact hj
      · exact hj
    · exact hj
  | _, .aggregate r _ _, _, hw, h => by
    simp only [HasIssue, capJoins, capJoins_eval hcat hA hF hK hw.1] at h ⊢
    rcases h with h | ⟨_, _, _, _, hp⟩ | h | ⟨_, _, heq, _⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
    · exact .inr (.inr (.inl h))
    · exact (sumWraps_ne_domain heq).elim

/-! ## Issues with row caps -/

/-- The plan with capped reads and joins. -/
def Rel.capped (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (caps : String → Option Nat) (r : Rel) : Rel :=
  (r.capReads caps).capJoins cat A F K

/-- `Rel.mayIssues`, decided on the plan with capped reads, and its integer
`SUM`s on the plan with capped reads and joins. -/
def Rel.issuesCapped (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (caps : String → Option Nat) (r : Rel) :
    List (Issue × Expr) :=
  ((r.capReads caps).mayIssues cat A F T false).filter (·.1 != .sumWraps) ++
    ((r.capped cat A F K caps).mayIssues cat A F T false).filter (·.1 == .sumWraps)

/-- **Soundness with row caps**: every issue that can happen when running a
well-formed plan on tables within their caps is among `Rel.issuesCapped`.
An integer `SUM` it leaves out cannot overflow. -/
theorem Rel.issuesCapped_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {caps : String → Option Nat} (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    {r : Rel} (hwf : r.WF cat) (hsm : r.Small cat) (p : Issue × Expr)
    (h : r.HasIssue cat false p) : p ∈ r.issuesCapped cat A F T K caps := by
  simp only [issuesCapped, List.mem_append, List.mem_filter]
  obtain ⟨i, e⟩ := p
  by_cases hi : i = .sumWraps
  · subst hi
    have hrw : (r.capReads caps).WF cat := Rel.capReads_wf hwf
    have h' := Rel.sumWraps_capJoins hcat hA hF hK (K := K) hrw (Rel.hasIssue_capReads hcap h)
    have hwf' := Rel.capJoins_wf (A := A) (F := F) (K := K) hrw
    have hsm' := Rel.capJoins_small (A := A) (F := F) (K := K) hcat hA hF hK hrw
      (Rel.capReads_small hcap hsm)
    exact .inr ⟨mayIssues_sound hcat hA hF hT hwf' hsm' _ h', by simp⟩
  · exact .inl ⟨mayIssues_sound hcat hA hF hT (Rel.capReads_wf hwf) (Rel.capReads_small hcap hsm) _
      (Rel.hasIssue_capReads hcap h), by simp [hi]⟩

end Substrait
