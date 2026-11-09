import Sverify.Analysis.Safety
import Sverify.Analysis.Guards
import Sverify.Analysis.Keys

/-!
# Row caps that rule out `SUM` overflow (#219)

`Rel.maxRows` (`analysis/Sverify/Analysis/Contracts.lean`) bounds the rows of a plan from
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
  | .unnest r _, hw, h => capJoins_small hcat hA hF hK (r := r) hw.1 h
  | .aggregate r _ _, hw, h => by
    simp only [capJoins, Small, capJoins_eval hcat hA hF hK hw.1] at h ⊢
    exact ⟨h.1, capJoins_small hcat hA hF hK hw.1 h.2⟩
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
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h
  | .unnest r _, h | .fetch r _ _, h | .distinct r, h => capReads_small hcap (r := r) h
  | .aggregate r _ _, h => by
    simp only [capReads, Small, capReads_eval hcap] at h ⊢
    exact ⟨h.1, capReads_small hcap h.2⟩
  | .window r _ _ _, h => by
    simp only [capReads, Small, capReads_eval hcap] at h ⊢
    exact ⟨h.1, capReads_small hcap h.2⟩
  | .cross a b, h | .unionAll a b, h | .semi a b _ _, h | .join a b _ _, h =>
    ⟨capReads_small hcap h.1, capReads_small hcap h.2⟩

end

/-! ## `SUM`s of the plan are `SUM`s of the capped plan -/

theorem sumWraps_ne_domain {e e' : Expr} (h : ((Issue.sumWraps, e) : Issue × Expr) = (.domain, e')) :
    False := by simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

theorem sumWraps_ne_infinite {e e' : Expr}
    (h : ((Issue.sumWraps, e) : Issue × Expr) = (.infinite, e')) :
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
    rcases h with h | h | ⟨_, _, heq, _⟩ | ⟨_, _, heq, _⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact .inr (.inl h)
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim
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
    rcases h with h | ⟨_, _, _, _, hp⟩ | h | ⟨_, _, heq, _⟩ | ⟨_, _, heq, _⟩
    · exact .inl (sumWraps_capJoins hcat hA hF hK hw.1 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
    · exact .inr (.inr (.inl h))
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim

/-! ## Rows per key (`sv.rows_per`)

`sv.rows_per(k, at_most=n)` bounds the rows of a table that agree on the
columns `k` (`RowsPer`); a key is the bound 1 (`RowsPer.of_keyOn`). The bounds
carry through the operators that keep a subset of their input's rows
(`Rel.perKey`): filters, `FETCH`, sorts, `DISTINCT`, semi-joins, projections
and emits that keep the columns, unions, and joins on a key of their right
side, which give each left row at most one partner. An aggregate grouping by
all of a bound's columns has groups of at most that many rows
(`Rel.groupRows`), so a `SUM` of values in `[-m, m]` over at most `n` rows
fits when `n · m` does (`Rel.sumsPer`). -/

/-- At most `n` of `rows` agree on the columns `k`. -/
def RowsPer (k : List Nat) (n : Nat) (rows : Relation) : Prop :=
  ∀ v : List Value, (rows.filter fun row => decide (keyOf k row = v)).length ≤ n

theorem RowsPer.sublist {k : List Nat} {n : Nat} {rows rows' : Relation} (h : RowsPer k n rows)
    (hs : rows'.Sublist rows) : RowsPer k n rows' := fun v =>
  Nat.le_trans (hs.filter _).length_le (h v)

/-- Distinct rows drawn from `rows` have no more rows per key. -/
theorem RowsPer.of_nodup_subset {k : List Nat} {n : Nat} {rows rows' : Relation} (h : RowsPer k n rows)
    (hn : rows'.Nodup) (hs : ∀ x ∈ rows', x ∈ rows) : RowsPer k n rows' := fun v =>
  Nat.le_trans (List.Nodup.length_le_of_subset (hn.filter _) fun x hx =>
    List.mem_filter.mpr ⟨hs x (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩) (h v)

theorem RowsPer.perm {k : List Nat} {n : Nat} {rows rows' : Relation} (h : RowsPer k n rows)
    (hp : rows'.Perm rows) : RowsPer k n rows' := fun v => by
  rw [(hp.filter _).length_eq]; exact h v

/-- A key bounds the rows per key by 1. -/
theorem RowsPer.of_keyOn {k : List Nat} : ∀ {rows : Relation}, KeyOn k rows → RowsPer k 1 rows
  | [], _, v => by simp
  | x :: rows, h, v => by
    have hp := List.pairwise_cons.1 h
    have ih := RowsPer.of_keyOn (k := k) hp.2 v
    simp only [List.filter_cons]
    split
    · rename_i hx
      have hz : (rows.filter fun row => decide (keyOf k row = v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hv
        simp only [decide_eq_true_eq] at hx hv
        exact hp.1 y hy (hx.trans hv.symm)
      simp [hz]
    · exact ih

/-- Rows that map to rows with the same key: as many per key. -/
theorem RowsPer.map {k k' : List Nat} {n : Nat} {rows : Relation} {f : Row → Row}
    (h : RowsPer k n rows) (hf : ∀ x ∈ rows, keyOf k' (f x) = keyOf k x) :
    RowsPer k' n (rows.map f) := fun v => by
  rw [List.filter_map, List.length_map]
  have : (rows.filter ((fun row => decide (keyOf k' row = v)) ∘ f)) =
      rows.filter fun row => decide (keyOf k row = v) :=
    List.filter_congr fun x hx => by simp only [Function.comp, hf x hx]
  rw [this]; exact h v

theorem RowsPer.append {k : List Nat} {m n : Nat} {xs ys : Relation} (hx : RowsPer k m xs)
    (hy : RowsPer k n ys) : RowsPer k (m + n) (xs ++ ys) := fun v => by
  rw [List.filter_append, List.length_append]; exact Nat.add_le_add (hx v) (hy v)

/-- A `flatMap` that gives each row at most one row, and none to the rows
`q` rejects, has at most as many rows as `q` accepts. -/
theorem length_flatMap_le_filter {g : Row → Relation} {q : Row → Bool} :
    ∀ {xs : Relation}, (∀ x ∈ xs, (g x).length ≤ 1 ∧ (q x = false → g x = [])) →
      (xs.flatMap g).length ≤ (xs.filter q).length
  | [], _ => by simp
  | x :: xs, h => by
    have ih := length_flatMap_le_filter (g := g) (q := q) (xs := xs)
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.length_append, List.filter_cons]
    cases hq : q x
    · simp only [hx.2 hq, List.length_nil, Nat.zero_add, Bool.false_eq_true, ↓reduceIte]; exact ih
    · simp only [↓reduceIte, List.length_cons]; omega

/-- Rows each with at most one partner (a join on a key of its right side)
keep the left side's bounds on its columns. -/
theorem RowsPer.flatMap_prefix {k : List Nat} {n a : Nat} {xs : Relation} {g : Row → Relation}
    (h : RowsPer k n xs) (hk : ∀ c ∈ k, c < a) (hlen : ∀ x ∈ xs, x.length = a)
    (hg : ∀ x ∈ xs, (g x).length ≤ 1 ∧ ∀ row ∈ g x, ∃ y, row = x ++ y) :
    RowsPer k n (xs.flatMap g) := fun v => by
  rw [List.filter_flatMap]
  refine Nat.le_trans (length_flatMap_le_filter (q := fun row => decide (keyOf k row = v))
    fun x hx => ⟨Nat.le_trans (List.length_filter_le _ _) (hg x hx).1, fun hq => ?_⟩) (h v)
  rw [List.filter_eq_nil_iff]
  intro row hrow hv
  obtain ⟨y, rfl⟩ := (hg x hx).2 row hrow
  rw [keyOf_append_left fun c hc => (hlen x hx) ▸ hk c hc] at hv
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hv hq
  exact hq hv

/-- Is every column of `k` a grouping expression? -/
def coveredBy (gs : List Expr) (k : List Nat) : Bool :=
  k.all fun i => gs.any fun e => match e with
    | .field j => j == i
    | _ => false

/-- The least of the bounds. -/
def leastOf : List Nat → Option Nat
  | [] => none
  | n :: ns => some (match leastOf ns with
    | some m => min n m
    | none => n)

theorem le_leastOf {L : Nat} : ∀ {ns : List Nat} {n : Nat}, (∀ m ∈ ns, L ≤ m) →
    leastOf ns = some n → L ≤ n
  | [], _, _, h => by simp [leastOf] at h
  | m :: ns, n, hall, h => by
    simp only [leastOf, Option.some.injEq] at h
    have hm := hall m (List.mem_cons_self ..)
    cases hl : leastOf ns with
    | none => simp only [hl] at h; omega
    | some k =>
      have := le_leastOf (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm')) hl
      simp only [hl] at h; omega

section
variable {cat : Catalog} {A : String → List AVal} {F : String → List Fact}
  {K : String → List (List Nat)} {P : String → List (List Nat × Nat)}

/-- Bounds on the rows per key of a plan's result, from the tables' bounds
`P` and keys `K`: `(k, n)` says at most `n` rows agree on the columns `k`. -/
def Rel.perKey (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (P : String → List (List Nat × Nat)) :
    Rel → List (List Nat × Nat)
  | .read t => P t
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ =>
    r.perKey cat A F K P
  -- A projection keeps its input's columns in front.
  | .project r _ => (r.perKey cat A F K P).filter (·.1.all (· < r.arity cat))
  | .emit r m => (r.perKey cat A F K P).filterMap fun (k, n) => (emitKey m k).map (·, n)
  | .unionAll a b => (a.perKey cat A F K P).flatMap fun (k, m) =>
      (b.perKey cat A F K P).filterMap fun (k', n) => if k = k' then some (k, m + n) else none
  -- A join on a key of its right side gives each left row at most one partner.
  | .join a b _ on =>
    if Rel.keyedJoin cat A F K a b on then
      (a.perKey cat A F K P ++ (a.keys cat A F K).map (·, 1)).filter (·.1.all (· < a.arity cat))
    else []
  | _ => []

theorem Rel.perKey_sound (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) :
    ∀ {r : Rel}, r.WF cat → ∀ kn ∈ r.perKey cat A F K P, RowsPer kn.1 kn.2 (r.eval cat)
  | .read t, _, kn, h => hP t kn h
  | .values _ _, _, _, h | .cross _ _, _, _, h | .window _ _ _ _, _, _, h
  | .aggregate _ _ _, _, _, h | .unnest _ _, _, _, h => by simp [perKey] at h
  | .filter r _, hw, kn, h => by
    simp only [perKey] at h; simp only [eval]
    exact (perKey_sound hcat hA hF hK hP hw.1 kn h).sublist List.filter_sublist
  | .semi r _ _ _, hw, kn, h => by
    simp only [perKey] at h; simp only [eval]
    exact (perKey_sound hcat hA hF hK hP hw.1 kn h).sublist List.filter_sublist
  | .fetch r _ c, hw, kn, h => by
    simp only [perKey] at h; simp only [eval]
    have hr := perKey_sound hcat hA hF hK hP (r := r) hw kn h
    cases c with
    | none => exact hr.sublist (List.drop_sublist _ _)
    | some n => exact hr.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  | .orderBy r _, hw, kn, h => by
    simp only [perKey] at h; simp only [eval]
    exact (perKey_sound hcat hA hF hK hP hw.1 kn h).perm (List.mergeSort_perm _ _)
  | .distinct r, hw, kn, h => by
    simp only [perKey] at h; simp only [eval]
    exact (perKey_sound hcat hA hF hK hP (r := r) hw kn h).of_nodup_subset (canonReps_nodup _)
      fun _ hx => canonReps_sub hx
  | .project r es, hw, kn, h => by
    simp only [perKey, List.mem_filter, List.all_eq_true, decide_eq_true_eq] at h
    simp only [eval]
    exact (perKey_sound hcat hA hF hK hP hw.1 kn h.1).map fun x hx =>
      keyOf_append_left fun c hc => (eval_arity hcat hw.1 x hx) ▸ h.2 c hc
  | .emit r m, hw, kn, h => by
    simp only [perKey, List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨⟨k, n⟩, hkn, k', hk', rfl⟩ := h
    simp only [eval]
    exact (perKey_sound hcat hA hF hK hP hw.1 _ hkn).map fun x _ => emitKey_keyOf hk'
  | .unionAll a b, hw, kn, h => by
    simp only [perKey, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨⟨k, m⟩, hk, ⟨k', n⟩, hk', hkn⟩ := h
    split at hkn
    · rename_i heq
      subst heq
      simp only [Option.some.injEq] at hkn; subst hkn
      simp only [eval]
      exact (perKey_sound hcat hA hF hK hP hw.1 _ hk).append (perKey_sound hcat hA hF hK hP hw.2.1 _ hk')
    · cases hkn
  | .join a b ty on, hw, kn, h => by
    simp only [perKey] at h
    split at h
    · rename_i hkey
      simp only [List.mem_filter, List.mem_append, List.mem_map, List.all_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨hmem, hlt⟩ := h
      have ha : RowsPer kn.1 kn.2 (a.eval cat) := by
        rcases hmem with hm | ⟨k, hk, rfl⟩
        · exact perKey_sound hcat hA hF hK hP hw.1 kn hm
        · exact RowsPer.of_keyOn (Rel.keys_sound hcat hA hF hK hw.1 k hk)
      obtain ⟨kb, hkb, hd⟩ := List.any_eq_true.1 hkey
      have hkB := Rel.keys_sound hcat hA hF hK hw.2.1 kb hkb
      have hp : ∀ x ∈ a.eval cat,
          (((b.eval cat).map (x ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ 1 :=
        fun x hx => partners_le_one (Rel.eval_arity hcat hw.1 x hx) hkB hd
      have hpre : ∀ x, ∀ row ∈ ((b.eval cat).map (x ++ ·)).filter (fun row => (on.eval row).isTrue),
          ∃ y, row = x ++ y := fun x row hrow => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hrow).1
        exact ⟨y, rfl⟩
      cases ty with
      | inner =>
        simp only [eval, crossRows, List.filter_flatMap]
        exact ha.flatMap_prefix hlt (fun x hx => Rel.eval_arity hcat hw.1 x hx)
          fun x hx => ⟨hp x hx, hpre x⟩
      | left =>
        simp only [eval]
        refine ha.flatMap_prefix hlt (fun x hx => Rel.eval_arity hcat hw.1 x hx) fun x hx => ?_
        unfold leftJoinRow
        simp only []
        split
        · exact ⟨by simp, fun row hrow => ⟨_, by simpa using hrow⟩⟩
        · exact ⟨hp x hx, hpre x⟩
    · simp at h

/-- The most rows a group of `aggregate r gs _` has, from the bounds on the
rows per key of `r` whose columns are all grouping expressions; none if
nothing bounds them. -/
def Rel.groupRows (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (P : String → List (List Nat × Nat)) (r : Rel)
    (gs : List Expr) : Option Nat :=
  leastOf (((r.perKey cat A F K P ++ (r.keys cat A F K).map (·, 1)).filter
    fun kn : List Nat × Nat => coveredBy gs kn.1).map fun kn : List Nat × Nat => kn.2)

theorem keyOf_eq_of_mem_aggGroups {gs : List Expr} {k : List Nat} {rows grp : Relation}
    (hc : coveredBy gs k = true) (hg : grp ∈ aggGroups gs rows) :
    ∀ y ∈ grp, ∀ z ∈ grp, keyOf k y = keyOf k z := by
  intro y hy z hz
  unfold aggGroups at hg
  split at hg
  · rename_i hemp
    have hk : k = [] := by
      cases k with
      | nil => rfl
      | cons i _ =>
        simp only [coveredBy, List.all_cons, Bool.and_eq_true, List.any_eq_true] at hc
        obtain ⟨⟨e, he, _⟩, _⟩ := hc
        simp only [List.isEmpty_iff] at hemp; subst hemp; simp at he
    subst hk; rfl
  · obtain ⟨kk, _, rfl⟩ := List.mem_map.1 hg
    simp only [groupRows, List.mem_filter, beq_iff_eq] at hy hz
    have hyz : (groupKey gs y).canon = (groupKey gs z).canon := hy.2.trans hz.2.symm
    simp only [Row.canon, groupKey, List.map_map, List.map_inj_left] at hyz
    simp only [keyOf, List.map_inj_left]
    intro i hi
    simp only [coveredBy, List.all_eq_true, List.any_eq_true] at hc
    obtain ⟨e, he, hfe⟩ := hc i hi
    cases e with
    | field j =>
      simp only [beq_iff_eq] at hfe; subst hfe
      simpa [Expr.eval] using hyz _ he
    | _ => simp at hfe

theorem sublist_of_mem_aggGroups {gs : List Expr} {rows grp : Relation}
    (hg : grp ∈ aggGroups gs rows) : grp.Sublist rows := by
  unfold aggGroups at hg
  split at hg
  · simp only [List.mem_singleton] at hg; exact hg ▸ List.Sublist.refl _
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
    exact List.filter_sublist

theorem length_le_of_rowsPer {k : List Nat} {n : Nat} {rows grp : Relation}
    (h : RowsPer k n rows) (hs : grp.Sublist rows) (heq : ∀ y ∈ grp, ∀ z ∈ grp, keyOf k y = keyOf k z) :
    grp.length ≤ n := by
  cases grp with
  | nil => simp
  | cons y0 rest =>
    have hf := (hs.filter fun row => decide (keyOf k row = keyOf k y0)).length_le
    rw [List.filter_eq_self.2 fun z hz => by
      simpa using heq z hz y0 (List.mem_cons_self ..)] at hf
    exact Nat.le_trans hf (h _)

theorem Rel.groupRows_sound (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row)
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) {r : Rel} (hw : r.WF cat)
    {gs : List Expr} {grp : Relation} (hg : grp ∈ aggGroups gs (r.eval cat)) :
    ∀ n, r.groupRows cat A F K P gs = some n → grp.length ≤ n := fun n hn => by
  refine le_leastOf (fun m hm => ?_) hn
  simp only [List.mem_map, List.mem_filter, List.mem_append] at hm
  obtain ⟨⟨k, m'⟩, ⟨hmem, hc⟩, rfl⟩ := hm
  have hrp : RowsPer k m' (r.eval cat) := by
    rcases hmem with h | h
    · exact perKey_sound hcat hA hF hK hP hw _ h
    · obtain ⟨k', hk', heq⟩ := h
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
      exact RowsPer.of_keyOn (Rel.keys_sound hcat hA hF hK hw k' hk')
  exact length_le_of_rowsPer hrp (sublist_of_mem_aggGroups hg) (keyOf_eq_of_mem_aggGroups hc hg)

/-- The `SUM`s that may leave their type with groups bounded by
`Rel.groupRows`: those of windows, and those of aggregates whose groups and
values do not keep them within it (`Measure.sumFits`). -/
def Rel.sumsPer (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys)
    (K : String → List (List Nat)) (P : String → List (List Nat × Nat)) : Rel → List Expr
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.sumsPer cat A F T K P
  | .window r _ _ fns => r.sumsPer cat A F T K P ++
      (WinFn.aggs fns).filterMap fun m => if m.fn = .sum then some m.arg else none
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ =>
    a.sumsPer cat A F T K P ++ b.sumsPer cat A F T K P
  | .aggregate r gs ms => r.sumsPer cat A F T K P ++ ms.filterMap fun m =>
      if m.fn = .sum ∧ m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T))
          (r.groupRows cat A F K P gs) = false
      then some m.arg else none

theorem Rel.sumsPer_sound (hcat : cat.WF)
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows) :
    ∀ {u : Bool} {r : Rel} {e : Expr}, r.WF cat → r.Small cat → r.HasIssue cat u (.sumWraps, e) →
      e ∈ r.sumsPer cat A F T K P
  | _, .read _, _, _, _, h | _, .values _ _, _, _, _, h => h.elim
  | _, .filter r _, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer]
    rcases h with h | ⟨_, _, hp⟩
    · exact sumsPer_sound hcat hA hF hT hK hP hw.1 hs h
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .project r _, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer]
    rcases h with h | ⟨_, _, _, _, hp⟩
    · exact sumsPer_sound hcat hA hF hT hK hP hw.1 hs h
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .emit r _, _, hw, hs, h | _, .orderBy r _, _, hw, hs, h | _, .unnest r _, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer]
    exact sumsPer_sound hcat hA hF hT hK hP hw.1 hs h
  | _, .fetch r _ _, _, hw, hs, h | _, .distinct r, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer]
    exact sumsPer_sound hcat hA hF hT hK hP (r := r) hw hs h
  | _, .window r _ _ _, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨m, hm, hf, heq, _⟩ | ⟨_, _, heq, _⟩ | ⟨_, _, heq, _⟩
    · exact .inl (sumsPer_sound hcat hA hF hT hK hP hw.1 hs.2 h)
    · simp only [Prod.mk.injEq] at heq
      exact .inr ⟨m, hm, by simp [hf, heq.2]⟩
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim
  | _, .cross a b, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append]
    exact h.imp (sumsPer_sound hcat hA hF hT hK hP hw.1 hs.1)
      (sumsPer_sound hcat hA hF hT hK hP hw.2 hs.2)
  | _, .unionAll a b, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append]
    exact h.imp (sumsPer_sound hcat hA hF hT hK hP hw.1 hs.1)
      (sumsPer_sound hcat hA hF hT hK hP hw.2.1 hs.2)
  | _, .semi a b _ _, _, hw, hs, h => by
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append]
    rcases h with h | h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumsPer_sound hcat hA hF hT hK hP hw.1 hs.1 h)
    · exact .inr (sumsPer_sound hcat hA hF hT hK hP hw.2.1 hs.2 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .join a b ty _, _, hw, hs, h => by
    have ha : a.WF cat := by cases ty <;> exact hw.1
    have hb : b.WF cat := by cases ty <;> exact hw.2.1
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append]
    rcases h with h | h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumsPer_sound hcat hA hF hT hK hP ha hs.1 h)
    · exact .inr (sumsPer_sound hcat hA hF hT hK hP hb hs.2 h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .aggregate r gs ms, _, hw, ⟨_, hsm⟩, h => by
    simp only [HasIssue] at h; simp only [sumsPer, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨_, _, _, _, hp⟩ | ⟨m, hm, hf, heq, grp, hgrp, hov⟩ | ⟨_, _, heq, _⟩ |
      ⟨_, _, heq, _⟩
    · exact .inl (sumsPer_sound hcat hA hF hT hK hP hw.1 hsm h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
    · simp only [Prod.mk.injEq] at heq
      have hfits : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T))
          (r.groupRows cat A F K P gs) = false := by
        cases hfit : m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T))
            (r.groupRows cat A F K P gs)
        · rfl
        · have := Measure.sumFits_sound (grp := grp) (fun y hy => by
              have hyr := mem_of_mem_aggGroups hgrp hy
              exact Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hw.1 (fun _ => hsm) y hyr)
                (facts_sound hcat hF hT hw.1 y hyr) (KsHold.nil y) m.arg)
            (Rel.groupRows_sound hcat hA hF hK hP hw.1 hgrp) hfit
          rw [hov] at this; cases this
      exact .inr ⟨m, hm, by simp [hf, hfits, heq.2]⟩
    · exact (sumWraps_ne_domain heq).elim
    · exact (sumWraps_ne_infinite heq).elim

end

/-! ## Issues with row caps -/

/-- The plan with capped reads and joins. -/
def Rel.capped (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (caps : String → Option Nat) (r : Rel) : Rel :=
  (r.capReads caps).capJoins cat A F K

/-- `Rel.mayIssues`, decided on the plan with capped reads, and its integer
`SUM`s on the plan with capped reads and joins, where both the plan's row
counts and the bounds on its rows per key (`Rel.sumsPer`) leave them
possible. -/
def Rel.issuesCapped (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (caps : String → Option Nat)
    (P : String → List (List Nat × Nat)) (r : Rel) : List (Issue × Expr) :=
  ((r.capReads caps).mayIssues cat A F T false).filter (·.1 != .sumWraps) ++
    ((r.capped cat A F K caps).mayIssues cat A F T false).filter fun p =>
      p.1 == .sumWraps && decide (p.2 ∈ (r.capped cat A F K caps).sumsPer cat A F T K P)

/-- **Soundness with row caps**: every issue that can happen when running a
well-formed plan on tables within their caps and bounds per key is among
`Rel.issuesCapped`.
An integer `SUM` it leaves out cannot overflow. -/
theorem Rel.issuesCapped_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {caps : String → Option Nat} (hcap : ∀ t n, caps t = some n → (cat t).rows.length ≤ n)
    {P : String → List (List Nat × Nat)} (hP : ∀ t, ∀ kn ∈ P t, RowsPer kn.1 kn.2 (cat t).rows)
    {r : Rel} (hwf : r.WF cat) (hsm : r.Small cat) (p : Issue × Expr)
    (h : r.HasIssue cat false p) : p ∈ r.issuesCapped cat A F T K caps P := by
  simp only [issuesCapped, List.mem_append, List.mem_filter]
  obtain ⟨i, e⟩ := p
  by_cases hi : i = .sumWraps
  · subst hi
    have hrw : (r.capReads caps).WF cat := Rel.capReads_wf hwf
    have h' := Rel.sumWraps_capJoins hcat hA hF hK (K := K) hrw (Rel.hasIssue_capReads hcap h)
    have hwf' := Rel.capJoins_wf (A := A) (F := F) (K := K) hrw
    have hsm' := Rel.capJoins_small (A := A) (F := F) (K := K) hcat hA hF hK hrw
      (Rel.capReads_small hcap hsm)
    exact .inr ⟨mayIssues_sound hcat hA hF hT hwf' hsm' _ h',
      by
        have := Rel.sumsPer_sound hcat hA hF hT hK hP hwf' hsm' h'
        simp only [capped] at this ⊢
        simp [this]⟩
  · exact .inl ⟨mayIssues_sound hcat hA hF hT (Rel.capReads_wf hwf) (Rel.capReads_small hcap hsm) _
      (Rel.hasIssue_capReads hcap h), by simp [hi]⟩

end Substrait
