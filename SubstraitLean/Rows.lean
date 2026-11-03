import SubstraitLean.Safety
import SubstraitLean.Guards
import SubstraitLean.Keys

/-!
# Row-count bounds (#219)

`Rel.maxRows` bounds how many rows a plan returns, from bounds on its base
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

`Rel.maxRows_sound` proves the bound against `Rel.eval`.

With it, an integer `SUM` over a group of at most `n` rows whose values all
satisfy `|x| ≤ m` stays within `n · m`. When that fits in 64 bits, the `SUM`
cannot overflow, and `Rel.issuesR` leaves it out of the issues
`Rel.mayIssues` reports (`Rel.issuesR_sound`). Window `SUM`s stay reported.
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
def Rel.maxRows (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (R : RowBounds) : Rel → Option Nat
  | .read t => R t
  | .values _ rows => some rows.length
  | .filter r _ | .project r _ | .emit r _ | .window r _ _ _ | .orderBy r _ | .distinct r =>
      r.maxRows cat A F K R
  | .semi a _ _ _ => a.maxRows cat A F K R
  | .cross a b => optMul (a.maxRows cat A F K R) (b.maxRows cat A F K R)
  | .join a b ty on =>
      if Rel.keyedJoin cat A F K a b on then a.maxRows cat A F K R
      else match ty with
        | .inner => optMul (a.maxRows cat A F K R) (b.maxRows cat A F K R)
        | .left => optMul (a.maxRows cat A F K R) ((b.maxRows cat A F K R).map (max 1))
  | .fetch r off cnt =>
      match cnt, r.maxRows cat A F K R with
      | some c, some n => some (min c (n - off))
      | some c, Option.none => some c
      | Option.none, n => n.map (· - off)
  | .unionAll a b => optAdd (a.maxRows cat A F K R) (b.maxRows cat A F K R)
  | .aggregate r gs _ => if gs.isEmpty then some 1 else r.maxRows cat A F K R
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

/-- **Soundness of `Rel.maxRows`**: a well-formed plan returns at most the
bound's rows, on base tables within their bounds. -/
theorem Rel.maxRows_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {R : RowBounds} (hR : R.Sound cat) :
    ∀ {r : Rel}, r.WF cat → ∀ n, r.maxRows cat A F K R = some n → (r.eval cat).length ≤ n
  | .read t, _, n, h => hR t n h
  | .values _ _, _, n, h => by
    simp only [maxRows, Option.some.injEq] at h
    subst h; simp [eval]
  | .filter r _, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (List.length_filter_le _ _) (maxRows_sound hcat hA hF hK hR hwf.1 n h))
  | .project r _, hwf, n, h => by
    simp only [eval, List.length_map]
    exact maxRows_sound hcat hA hF hK hR hwf.1 n h
  | .emit r _, hwf, n, h => by
    simp only [eval, List.length_map]
    exact maxRows_sound hcat hA hF hK hR hwf.1 n h
  | .window r _ _ _, hwf, n, h => by
    simp only [eval, windowEval, windowRows_length, List.length_mergeSort]
    exact maxRows_sound hcat hA hF hK hR hwf.1 n h
  | .orderBy r _, hwf, n, h => by
    simp only [eval, List.length_mergeSort]
    exact maxRows_sound hcat hA hF hK hR hwf.1 n h
  | .distinct r, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (dedup_length_le _) (maxRows_sound hcat hA hF hK hR (r := r) hwf n h))
  | .semi a _ _ _, hwf, n, h => by
    simp only [eval]
    exact (Nat.le_trans (List.length_filter_le _ _) (maxRows_sound hcat hA hF hK hR hwf.1 n h))
  | .cross a b, hwf, n, h => by
    simp only [eval, crossRows_length]
    exact optMul_le (maxRows_sound hcat hA hF hK hR hwf.1) (maxRows_sound hcat hA hF hK hR hwf.2) h
  | .join a b ty on, hwf, n, h => by
    have ha := maxRows_sound hcat hA hF hK hR hwf.1
    have hb := maxRows_sound hcat hA hF hK hR hwf.2.1
    have hlen := Rel.eval_arity hcat hwf.1
    simp only [maxRows] at h
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
        cases hbr : b.maxRows cat A F K R with
        | none => simp [hbr] at hk
        | some j =>
          simp only [hbr, Option.map_some, Option.some.injEq] at hk
          subst hk
          have := hb j hbr
          omega
  | .fetch r off cnt, hwf, n, h => by
    have hr := maxRows_sound hcat hA hF hK hR (r := r) hwf
    simp only [maxRows] at h
    simp only [eval]
    cases cnt with
    | none =>
      cases hm : r.maxRows cat A F K R with
      | none => simp [hm] at h
      | some j =>
        simp only [hm, Option.map_some, Option.some.injEq] at h
        have := hr j hm
        simp only [List.length_drop]
        omega
    | some c =>
      cases hm : r.maxRows cat A F K R with
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
    have ha := maxRows_sound hcat hA hF hK hR hwf.1
    have hb := maxRows_sound hcat hA hF hK hR hwf.2.1
    simp only [eval, List.length_append]
    simp only [maxRows] at h
    cases hma : a.maxRows cat A F K R <;> cases hmb : b.maxRows cat A F K R <;>
      simp only [hma, hmb, optAdd, Option.some.injEq, reduceCtorEq] at h
    have := ha _ hma
    have := hb _ hmb
    omega
  | .aggregate r gs ms, hwf, n, h => by
    simp only [eval]
    refine (Nat.le_trans (aggregateEval_length_le gs ms _) ?_)
    simp only [maxRows] at h
    split at h
    · simp only [Option.some.injEq] at h
      simp [*]
    · simp only [*, Bool.false_eq_true, ite_false]
      exact maxRows_sound hcat hA hF hK hR hwf.1 n h
  | .unnest _ _, _, n, h => by simp [maxRows] at h

/-! ## Integer sums over few rows -/

/-- The largest absolute value of an integer the abstract value allows
(`0` when it allows none). -/
def AVal.absMax (a : AVal) : Option Nat :=
  match a.int with
  | Option.none => some 0
  | some b => match b.lo, b.hi with
    | some l, some h => some (max l.natAbs h.natAbs)
    | _, _ => Option.none

theorem AVal.absMax_mem {a : AVal} {m : Nat} {i : Int} (h : a.absMax = some m)
    (hm : a.Mem (.int i)) : i.natAbs ≤ m := by
  obtain ⟨b, hb, hlo, hhi⟩ := hm
  simp only [absMax, hb] at h
  cases hl : b.lo <;> cases hh : b.hi <;> simp only [hl, hh, reduceCtorEq, Option.some.injEq] at h
  rename_i l u
  have := hlo l hl
  have := hhi u hh
  omega

/-- A `SUM` of at most `n` values allowed by `a` fits in 64 bits. -/
def sumFits (n : Nat) (a : AVal) : Bool :=
  match a.absMax with
  | some m => decide ((n * m : Nat) ≤ maxI64)
  | Option.none => false

theorem intSum_natAbs_le {m : Nat} :
    ∀ (vs : List Value), (∀ i, Value.int i ∈ vs → i.natAbs ≤ m) →
      (intSum vs).natAbs ≤ vs.length * m
  | [], _ => by simp [intSum]
  | v :: vs, h => by
    have ih := intSum_natAbs_le vs fun i hi => h i (List.mem_cons_of_mem _ hi)
    rw [List.length_cons, Nat.succ_mul]
    match v with
    | .int i =>
      have := h i (List.mem_cons_self ..)
      have := Int.natAbs_add_le i (intSum vs)
      simp only [intSum]
      omega
    | .null | .bool _ | .str _ | .list _ =>
      simp only [intSum]
      omega

theorem inI64_of_natAbs_le {s : Int} (h : (s.natAbs : Int) ≤ maxI64) : inI64 s = true := by
  have h1 : s ≤ (s.natAbs : Int) := Int.le_natAbs
  have h2 : -s ≤ (s.natAbs : Int) := by rw [← Int.natAbs_neg]; exact Int.le_natAbs
  have hm : maxI64 = 9223372036854775807 := rfl
  have hn : minI64 = -9223372036854775808 := rfl
  rw [hm] at h
  simp only [inI64, hn, hm, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem Measure.inputs_length_le (m : Measure) (rows : Relation) :
    (m.inputs rows).length ≤ rows.length := by
  have hk : (m.kept rows).length ≤ rows.length := by
    unfold Measure.kept
    split
    · exact Nat.le_refl _
    · exact List.length_filter_le _ _
  have hv : (((m.kept rows).map m.arg.eval).filter (· != .null)).length ≤ rows.length :=
    (Nat.le_trans (List.length_filter_le _ _) (by simpa using hk))
  simp only [Measure.inputs]
  split
  · exact (Nat.le_trans (dedup_length_le _) hv)
  · exact hv

theorem length_le_of_mem_aggGroups {gs : List Expr} {rows grp : Relation}
    (hg : grp ∈ aggGroups gs rows) : grp.length ≤ rows.length := by
  unfold aggGroups at hg
  split at hg
  · simp only [List.mem_singleton] at hg
    exact hg ▸ Nat.le_refl _
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
    exact List.length_filter_le _ _

/-- Does an integer `SUM` of `arg` over any group of `r`'s rows fit in 64
bits? -/
def Rel.sumFits (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (R : RowBounds) (r : Rel) (arg : Expr) : Bool :=
  match r.maxRows cat A F K R with
  | some n => Substrait.sumFits n (arg.absD (r.aeval cat A F T true) (r.facts cat F T))
  | Option.none => false

theorem Rel.sumFits_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {K : String → List (List Nat)} (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows)
    {R : RowBounds} (hR : R.Sound cat) {r : Rel} {gs : List Expr} {m : Measure} {grp : Relation}
    (hwf : r.WF cat) (hsm : r.Small cat) (hgrp : grp ∈ aggGroups gs (r.eval cat))
    (hfit : r.sumFits cat A F T K R m.arg = true) : inI64 (intSum (m.inputs grp)) = true := by
  unfold Rel.sumFits at hfit
  split at hfit
  · rename_i n hn
    have hrows := maxRows_sound hcat hA hF hK hR hwf n hn
    have hlen : (m.inputs grp).length ≤ n :=
      (Nat.le_trans (Measure.inputs_length_le m grp) ((Nat.le_trans (length_le_of_mem_aggGroups hgrp) hrows)))
    unfold Substrait.sumFits at hfit
    split at hfit
    · rename_i M hM
      have hle : (n * M : Nat) ≤ maxI64 := of_decide_eq_true hfit
      have hint : ∀ i, Value.int i ∈ m.inputs grp → i.natAbs ≤ M := fun i hi => by
        obtain ⟨_, y, hy, hev⟩ := Measure.mem_inputs hi
        have hyr := mem_of_mem_aggGroups hgrp hy
        have := Expr.absD_sound (aeval_sound hcat hA hF hT (sz := true) hwf (fun _ => hsm) y hyr)
          (facts_sound hcat hF hT hwf y hyr) (KsHold.nil y) m.arg
        rw [hev] at this
        exact AVal.absMax_mem hM this
      have hs := intSum_natAbs_le _ hint
      have : (m.inputs grp).length * M ≤ n * M := Nat.mul_le_mul_right M hlen
      exact inI64_of_natAbs_le (by omega)
    · simp at hfit
  · simp at hfit

/-! ## Issues with row bounds -/

/-- The integer `SUM`s that may leave 64 bits: those over groups the row
bound and the values' range do not keep within them, and every window `SUM`. -/
def Rel.sumRisks (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (K : String → List (List Nat)) (R : RowBounds) : Rel → List (Issue × Expr)
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.sumRisks cat A F T K R
  | .window r _ _ fns => r.sumRisks cat A F T K R ++ (WinFn.sumArg? fns).map (.sumWraps, ·)
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ =>
      a.sumRisks cat A F T K R ++ b.sumRisks cat A F T K R
  | .aggregate r _ ms => r.sumRisks cat A F T K R ++ ms.filterMap fun m =>
      if m.fn = .sum ∧ m.arg.isDecimal = false ∧ r.sumFits cat A F T K R m.arg = false
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
    simp only [sumRisks, List.mem_append]
    rcases h with h | h
    · exact .inl (sumRisks_sound hcat hA hF hT hK hR hwf.1 hsm.2 e h)
    · exact .inr h
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
      have hfit : r.sumFits cat A F T K R m.arg = false := by
        cases hc : r.sumFits cat A F T K R m.arg
        · rfl
        · rw [Rel.sumFits_sound hcat hA hF hT hK hR hwf.1 hsm hgrp hc] at hov
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
