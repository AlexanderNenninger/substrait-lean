import SubstraitLean.Safety
import SubstraitLean.Guards
import SubstraitLean.Keys

/-!
# Row-count bounds (#219)

`Rel.rowBound` bounds how many rows a plan returns, from bounds on its base
tables (a precondition `rows(at_most=N)`, or a table format's metadata):

* filters, semi-joins, `DISTINCT`: at most their input;
* projections, emits, sorts, windows: as many as their input;
* `FETCH`: at most its count, and at most the input after the offset;
* `UNION ALL`: the sum;
* cross products and joins: the product, or at most the left side's rows when
  the join condition determines a key of the right side (`Rel.keys`), so each
  left row has at most one partner; a left join keeps a row without partners;
* aggregates: one row without `GROUP BY`, otherwise at most one per input row;
* literal tables: their rows; `UNNEST` is unbounded.

`Rel.rowBound_sound` proves the bound against `Rel.eval`. It extends
`Rel.maxRows` (`SubstraitLean/Safety.lean`), which bounds rows from the plan's
shape alone, to base tables, joins and unions.

With it, an integer `SUM` over a group or window frame of at most `n` rows
whose values all satisfy `|x| ≤ m` stays within `n · m`
(`Measure.sumFits`). When that fits in 64 bits, the `SUM` cannot overflow,
and `Rel.issuesR` leaves it out of the issues `Rel.mayIssues` reports
(`Rel.issuesR_sound`).
-/

namespace Substrait

open FloatCode (minI64 maxI64)

/-- Upper bounds on the number of rows of the base tables. -/
abbrev RowBounds := String → Option Nat

def RowBounds.Sound (R : RowBounds) (cat : Catalog) : Prop :=
  ∀ t n, R t = some n → (cat t).rows.length ≤ n

def RowBounds.none : RowBounds := fun _ => Option.none

def optMul : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a * b)
  | _, _ => Option.none

def optAdd : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => Option.none

/-- Does the join condition tie each left row to at most one right row? -/
def Rel.keyedJoin (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (a b : Rel) (on : Expr) : Bool :=
  (b.keys cat A F K).any (determines on (a.arity cat))

/-- An upper bound on the number of rows (`none`: unbounded). -/
def Rel.rowBound (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : RowBounds) : Rel → Option Nat
  | .read t => R t
  | .values _ rows => some rows.length
  | .filter r _ | .project r _ | .emit r _ | .window r _ _ _ | .orderBy r _ | .distinct r =>
      r.rowBound cat A F K R
  | .semi a _ _ _ => a.rowBound cat A F K R
  | .cross a b => optMul (a.rowBound cat A F K R) (b.rowBound cat A F K R)
  | .join a b ty on =>
      if Rel.keyedJoin cat A F K a b on then a.rowBound cat A F K R
      else match ty with
        | .inner => optMul (a.rowBound cat A F K R) (b.rowBound cat A F K R)
        | .left => optMul (a.rowBound cat A F K R) ((b.rowBound cat A F K R).map (max 1))
  | .fetch r off cnt =>
      match cnt, r.rowBound cat A F K R with
      | some c, some n => some (min c (n - off))
      | some c, Option.none => some c
      | Option.none, n => n.map (· - off)
  | .unionAll a b => optAdd (a.rowBound cat A F K R) (b.rowBound cat A F K R)
  | .aggregate r gs _ => if gs.isEmpty then some 1 else r.rowBound cat A F K R
  | .unnest _ _ => Option.none

/-! ## Soundness of the row bound -/

theorem crossRows_length (xs ys : Relation) :
    (crossRows xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [crossRows]
  | cons x xs ih =>
    simp only [crossRows, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul]
    omega

theorem length_flatMap_le {α β : Type} {f : α → List β} {k : Nat} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).length ≤ k) → (l.flatMap f).length ≤ l.length * k
  | [], _ => by simp
  | x :: l, h => by
    have := length_flatMap_le (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem length_le_one_of_pairwise_false {α : Type} :
    ∀ {l : List α}, l.Pairwise (fun _ _ => False) → l.length ≤ 1
  | [], _ | [_], _ => by simp
  | _ :: b :: _, h => ((List.pairwise_cons.1 h).1 b (List.mem_cons_self ..)).elim

/-- On a key of the right side that the condition determines, a left row has
at most one partner. -/
theorem partners_le_one {B : Relation} {n : Nat} {on : Expr} {kb : List Nat} {x : Row}
    (hx : x.length = n) (hkB : KeyOn kb B) (hd : determines on n kb = true) :
    ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ 1 := by
  apply length_le_one_of_pairwise_false
  rw [List.pairwise_filter, List.pairwise_map]
  exact hkB.imp fun hne ht ht' => hne (determines_sound hd hx ht ht')

theorem leftJoinRow_length_le {on : Expr} {m : Nat} {B : Relation} {x : Row} {k : Nat}
    (h : ((B.map (x ++ ·)).filter fun row => (on.eval row).isTrue).length ≤ k) :
    (leftJoinRow on m B x).length ≤ max 1 k := by
  unfold leftJoinRow
  simp only []
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans h (Nat.le_max_right _ _)

theorem aggregateEval_length_le (gs : List Expr) (ms : List Measure) (rows : Relation) :
    (aggregateEval gs ms rows).length ≤ (if gs.isEmpty then 1 else rows.length) := by
  unfold aggregateEval
  split
  · simp
  · simp only [List.length_map]
    exact (Nat.le_trans (dedup_length_le _) (by simp))

theorem optMul_le {a b : Option Nat} {x y n : Nat}
    (ha : ∀ k, a = some k → x ≤ k) (hb : ∀ k, b = some k → y ≤ k)
    (h : optMul a b = some n) : x * y ≤ n := by
  cases a <;> cases b <;> simp only [optMul, Option.some.injEq, reduceCtorEq] at h
  subst h
  exact Nat.mul_le_mul (ha _ rfl) (hb _ rfl)

/-- **Soundness of `Rel.rowBound`**: a well-formed plan returns at most the
bound's rows, on base tables within their bounds. -/
theorem Rel.rowBound_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {R : RowBounds} (hR : R.Sound cat) :
    ∀ {r : Rel}, r.WF cat → ∀ n, r.rowBound cat A F K R = some n → (r.eval cat).length ≤ n
  | .read t, _, n, h => hR t n h
  | .values _ _, _, n, h => by
    simp only [rowBound, Option.some.injEq] at h
    subst h; simp [eval]
  | .filter r _, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (List.length_filter_le _ _) (rowBound_sound hcat hA hF hK hR hwf.1 n h))
  | .project r _, hwf, n, h => by
    simp only [eval, List.length_map]
    exact rowBound_sound hcat hA hF hK hR hwf.1 n h
  | .emit r _, hwf, n, h => by
    simp only [eval, List.length_map]
    exact rowBound_sound hcat hA hF hK hR hwf.1 n h
  | .window r _ _ _, hwf, n, h => by
    simp only [eval, windowEval, windowRows_length, List.length_mergeSort]
    exact rowBound_sound hcat hA hF hK hR hwf.1 n h
  | .orderBy r _, hwf, n, h => by
    simp only [eval, List.length_mergeSort]
    exact rowBound_sound hcat hA hF hK hR hwf.1 n h
  | .distinct r, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (dedup_length_le _) (rowBound_sound hcat hA hF hK hR (r := r) hwf n h))
  | .semi a _ _ _, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (List.length_filter_le _ _) (rowBound_sound hcat hA hF hK hR hwf.1 n h))
  | .cross a b, hwf, n, h => by
    simp only [eval, crossRows_length]
    exact optMul_le (rowBound_sound hcat hA hF hK hR hwf.1) (rowBound_sound hcat hA hF hK hR hwf.2) h
  | .join a b ty on, hwf, n, h => by
    have ha := rowBound_sound hcat hA hF hK hR hwf.1
    have hb := rowBound_sound hcat hA hF hK hR hwf.2.1
    have hlen := Rel.eval_arity hcat hwf.1
    simp only [rowBound] at h
    split at h
    · -- Each left row has at most one partner.
      rename_i hkey
      obtain ⟨kb, hkb, hd⟩ := List.any_eq_true.1 hkey
      have hkB := Rel.keys_sound hcat hA hF hK hwf.2.1 kb hkb
      have hp : ∀ x ∈ a.eval cat,
          ((((b.eval cat).map (x ++ ·)).filter fun row => (on.eval row).isTrue)).length ≤ 1 :=
        fun x hx => partners_le_one (hlen x hx) hkB hd
      refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_of_eq (Nat.mul_one _)) (ha n h))
      cases ty with
      | inner =>
        simp only [eval, crossRows, List.filter_flatMap]
        exact length_flatMap_le hp
      | left =>
        simp only [eval]
        exact length_flatMap_le fun x hx => (Nat.le_trans (leftJoinRow_length_le (hp x hx)) (by simp))
    · cases ty with
      | inner =>
        simp only [eval]
        refine (Nat.le_trans (List.length_filter_le _ _) ?_)
        rw [crossRows_length]
        exact optMul_le ha hb h
      | left =>
        simp only [eval]
        refine Nat.le_trans (length_flatMap_le (k := max 1 (b.eval cat).length) fun x _ =>
          leftJoinRow_length_le ((Nat.le_trans (List.length_filter_le _ _) (by simp)))) ?_
        refine optMul_le ha (fun k hk => ?_) h
        cases hbr : b.rowBound cat A F K R with
        | none => simp [hbr] at hk
        | some j =>
          simp only [hbr, Option.map_some, Option.some.injEq] at hk
          subst hk
          have := hb j hbr
          omega
  | .fetch r off cnt, hwf, n, h => by
    have hr := rowBound_sound hcat hA hF hK hR (r := r) hwf
    simp only [rowBound] at h
    simp only [eval]
    cases cnt with
    | none =>
      cases hm : r.rowBound cat A F K R with
      | none => simp [hm] at h
      | some j =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        have := hr j hm
        simp only [List.length_drop]
        omega
    | some c =>
      cases hm : r.rowBound cat A F K R with
      | none =>
        simp only [hm, Option.some.injEq] at h
        simp only [List.length_take]
        omega
      | some j =>
        simp only [hm, Option.some.injEq] at h
        have := hr j hm
        simp only [List.length_take, List.length_drop]
        omega
  | .unionAll a b, hwf, n, h => by
    have ha := rowBound_sound hcat hA hF hK hR hwf.1
    have hb := rowBound_sound hcat hA hF hK hR hwf.2.1
    simp only [eval, List.length_append]
    simp only [rowBound] at h
    cases hma : a.rowBound cat A F K R <;> cases hmb : b.rowBound cat A F K R <;>
      simp only [hma, hmb, optAdd, Option.some.injEq, reduceCtorEq] at h
    have := ha _ hma
    have := hb _ hmb
    omega
  | .aggregate r gs ms, hwf, n, h => by
    simp only [eval]
    refine (Nat.le_trans (aggregateEval_length_le gs ms _) ?_)
    simp only [rowBound] at h
    split at h
    · simp only [Option.some.injEq] at h
      simp [*]
    · simp only [*, Bool.false_eq_true, ite_false]
      exact rowBound_sound hcat hA hF hK hR hwf.1 n h
  | .unnest _ _, _, n, h => by simp [rowBound] at h

/-! ## Integer sums over few rows -/

/-- Does an integer `SUM` of `m` over any group or window frame of `r`'s rows
fit in 64 bits, by `r`'s row bound? -/
def Rel.sumFitsR (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (R : RowBounds) (r : Rel) (m : Measure) : Bool :=
  m.sumFits (·.absD (r.aeval cat A F T true) (r.facts cat F T)) (r.rowBound cat A F K R)

/-- A sum over at most `r`'s rows, all of them `r`'s, fits when `Rel.sumFitsR`
says so. -/
theorem Rel.sumFitsR_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {R : RowBounds} (hR : R.Sound cat) {r : Rel} {m : Measure} {grp : Relation}
    (hwf : r.WF cat) (hsm : r.Small cat) (hin : ∀ y ∈ grp, y ∈ r.eval cat)
    (hlen : grp.length ≤ (r.eval cat).length)
    (hfit : r.sumFitsR cat A F T K R m = true) : inI64 (intSum (m.inputs grp)) = true :=
  Measure.sumFits_sound
    (fun y hy => Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf (fun _ => hsm) y (hin y hy))
      (facts_sound hcat hF hT hwf y (hin y hy)) (KsHold.nil y) m.arg)
    (fun k hk => Nat.le_trans hlen (rowBound_sound hcat hA hF hK hR hwf k hk)) hfit

/-! ## Issues with row bounds -/

/-- The integer `SUM`s that may leave 64 bits: those over groups or window
frames the row bound and the values' range do not keep within them. -/
def Rel.sumRisks (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (R : RowBounds) : Rel → List (Issue × Expr)
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.sumRisks cat A F T K R
  | .window r _ _ fns => r.sumRisks cat A F T K R ++ (WinFn.aggs fns).filterMap fun m =>
      if m.fn = .sum ∧ m.arg.isDecimal = false ∧ r.sumFitsR cat A F T K R m = false
      then some (.sumWraps, m.arg) else Option.none
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ =>
      a.sumRisks cat A F T K R ++ b.sumRisks cat A F T K R
  | .aggregate r _ ms => r.sumRisks cat A F T K R ++ ms.filterMap fun m =>
      if m.fn = .sum ∧ m.arg.isDecimal = false ∧ r.sumFitsR cat A F T K R m = false
      then some (.sumWraps, m.arg) else Option.none

/-- `Rel.mayIssues`, with only the integer `SUM`s of `Rel.sumRisks`. -/
def Rel.issuesR (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (R : RowBounds) (u : Bool) (r : Rel) :
    List (Issue × Expr) :=
  (r.mayIssues cat A F T u).filter (·.1 != .sumWraps) ++ r.sumRisks cat A F T K R

theorem Rel.sumRisks_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {R : RowBounds} (hR : R.Sound cat) :
    ∀ {u : Bool} {r : Rel}, r.WF cat → r.Small cat → ∀ e, r.HasIssue cat u (.sumWraps, e) →
      (.sumWraps, e) ∈ r.sumRisks cat A F T K R
  | _, .read _, _, _, _, h | _, .values _ _, _, _, _, h => h.elim
  | _, .filter r _, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    rcases h with h | ⟨_, _, hp⟩
    · exact sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm e h
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .project r _, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    rcases h with h | ⟨_, _, _, _, hp⟩
    · exact sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm e h
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .emit r _, hwf, hsm, e, h => sumRisks_sound hcat hA hF hT hK hR (r := r) hwf.1 hsm e h
  | _, .fetch r _ _, hwf, hsm, e, h => sumRisks_sound hcat hA hF hT hK hR (r := r) hwf hsm e h
  | _, .orderBy r _, hwf, hsm, e, h => sumRisks_sound hcat hA hF hT hK hR (r := r) hwf.1 hsm e h
  | _, .distinct r, hwf, hsm, e, h => sumRisks_sound hcat hA hF hT hK hR (r := r) hwf hsm e h
  | _, .unnest r _, hwf, hsm, e, h => sumRisks_sound hcat hA hF hT hK hR (r := r) hwf.1 hsm e h
  | _, .window r _ _ _, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨m, hm, hf, hd, heq, frame, hframe, hlen, hov⟩ | ⟨_, _, heq, _⟩
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm.2 e h)
    · refine .inr ⟨m, hm, ?_⟩
      have hfit : r.sumFitsR cat A F T K R m = false := by
        cases hc : r.sumFitsR cat A F T K R m
        · rfl
        · rw [Rel.sumFitsR_sound hcat hA hF hT hK hR hwf.1 hsm.2 hframe hlen hc] at hov
          exact absurd hov (by simp)
      simp only [Prod.mk.injEq] at heq
      simp [hf, hd, hfit, heq.2]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at heq
  | _, .cross a b, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append]
    rcases h with h | h
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm.1 e h)
    · exact .inr (sumRisks_sound hcat hA hF hT hK hR hwf.2 hsm.2 e h)
  | _, .unionAll a b, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append]
    rcases h with h | h
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm.1 e h)
    · exact .inr (sumRisks_sound hcat hA hF hT hK hR hwf.2.1 hsm.2 e h)
  | _, .join a b ty _, hwf, hsm, e, h => by
    have ha : a.WF cat := by cases ty <;> exact hwf.1
    have hb : b.WF cat := by cases ty <;> exact hwf.2.1
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append]
    rcases h with h | h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR ha hsm.1 e h)
    · exact .inr (sumRisks_sound hcat hA hF hT hK hR hb hsm.2 e h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .semi a b _ _, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append]
    rcases h with h | h | ⟨_, _, _, _, hp⟩
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm.1 e h)
    · exact .inr (sumRisks_sound hcat hA hF hT hK hR hwf.2.1 hsm.2 e h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
  | _, .aggregate r gs ms, hwf, hsm, e, h => by
    simp only [HasIssue] at h
    simp only [sumRisks, List.mem_append, List.mem_filterMap]
    rcases h with h | ⟨_, _, _, _, hp⟩ | ⟨m, hm, hf, hd, heq, grp, hgrp, hov⟩ | ⟨_, _, heq, _⟩
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm e h)
    · exact absurd rfl (Expr.issues_ne_sumWraps hp)
    · refine .inr ⟨m, hm, ?_⟩
      have hfit : r.sumFitsR cat A F T K R m = false := by
        cases hc : r.sumFitsR cat A F T K R m
        · rfl
        · rw [Rel.sumFitsR_sound hcat hA hF hT hK hR hwf.1 hsm
            (fun y hy => mem_of_mem_aggGroups hgrp hy) (length_le_of_mem_aggGroups hgrp) hc] at hov
          exact absurd hov (by simp)
      simp only [Prod.mk.injEq] at heq
      simp [hf, hd, hfit, heq.2]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at heq

/-- **Soundness with row bounds**: every issue that can happen when running a
well-formed plan is among `Rel.issuesR`, on base tables within their row
bounds. An integer `SUM` it leaves out cannot overflow. -/
theorem Rel.issuesR_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {R : RowBounds} (hR : R.Sound cat) {u : Bool} {r : Rel} (hwf : r.WF cat) (hsm : r.Small cat)
    (p : Issue × Expr) (h : r.HasIssue cat u p) : p ∈ Rel.issuesR cat A F T K R u r := by
  simp only [issuesR, List.mem_append, List.mem_filter]
  obtain ⟨i, e⟩ := p
  by_cases hi : i = .sumWraps
  · subst hi
    exact .inr (sumRisks_sound hcat hA hF hT hK hR hwf hsm e h)
  · exact .inl ⟨mayIssues_sound hcat hA hF hT hwf hsm _ h, by simp [hi]⟩

end Substrait
