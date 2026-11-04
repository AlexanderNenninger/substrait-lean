import SubstraitLean.Partition

/-!
# Guard elimination

Engines compute integers in 64 bits, and DataFusion wraps around where Lean's
integers do not, so the SQL that `sverify.sql` writes checks every
operation: a sum or product outside 64 bits raises, so does a division by
zero (Lean: NULL), and so on. These **guards** cost a `CASE` per operation.

When `Rel.mayIssues` reports nothing for a plan, nothing can go wrong on any
row the plan evaluates, and the guards never fire. This module proves that
running the plan *without* them gives the same result.

* `Impl` is an engine's own implementation of the functions, without
  checks. `Impl.Faithful` is what is assumed of it, function by function:
  it agrees with Lean wherever `UnFn.issue` and `BinFn.issue` report
  nothing. Wrapping 64-bit addition is faithful (it is exact in range);
  so is a division that does whatever it likes when dividing by zero. This
  is the trusted part, the same per-function semantics each dialect's hooks
  already implement, minus the checks.
* `Rel.evalI` runs a plan with those functions. Integer `SUM` keeps its check
  (`Issue.sumWraps` comes from a group's rows, so contracts on rows rarely
  rule it out).
* `Rel.evalI_eq`: if every issue a plan can run into is assumed, a `SUM`
  that may wrap or an overflow to `±∞` (#575, whose check the written SQL
  keeps), the unchecked plan computes `Rel.eval`. `Rel.guardFree_sound`
  derives this from an empty `Rel.mayIssues` (up to assumed issues), which is
  what `substrait-check --contract` reports as `guard_free`.
* `Rel.evalG_marks`: the same per expression. `Rel.marks` lists the
  expressions without abstract issues, `Rel.evalG` runs only those
  unchecked, and the result is `Rel.eval` whatever the other expressions
  may run into; `substrait-check --contract` reports the list as
  `unchecked`.

`Rel.HasIssue` looks at the rows of `Rel.loose`, the plan with the filters an
engine may reorder removed, which has all the plan's rows only when no left
join has a right side that `loose` changes (`Rel.looseSub`); otherwise
the theorem does not apply and the guards stay.
-/

namespace Substrait

/-! ## Expressions -/

/-- An engine's functions, without run-time checks. -/
structure Impl where
  un : UnFn → Value → Value
  bin : BinFn → Value → Value → Value

/-- Agrees with Lean wherever Lean reports no issue. -/
def Impl.Faithful (I : Impl) : Prop :=
  (∀ f v, f.issue v = none → I.un f v = f.apply v) ∧
    ∀ f v w, f.issue v w = none → I.bin f v w = f.apply v w

/-- Lean's own functions are faithful. -/
theorem Impl.lean_faithful : Impl.Faithful ⟨UnFn.apply, BinFn.apply⟩ :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def Expr.evalI (I : Impl) (row : Row) : Expr → Value
  | .lit v => v
  | .field i => row.getD i .null
  | .un f a => I.un f (a.evalI I row)
  | .bin f a b => I.bin f (a.evalI I row) (b.evalI I row)
  | .ifThen c t e => if (c.evalI I row).isTrue then t.evalI I row else e.evalI I row
  | .hof f l b => f.apply (l.evalI I row) fun x => b.evalI I [x]

/-- **Unchecked evaluation is exact** where no issue happens. -/
theorem Expr.evalI_eq {I : Impl} (hI : I.Faithful) {row : Row} :
    ∀ {e : Expr}, e.issues row = [] → e.evalI I row = e.eval row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, h => by
    simp only [issues, List.append_eq_nil_iff, Option.toList_eq_nil_iff, Option.map_eq_none_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1]
    exact hI.1 f _ (Option.or_eq_none_iff.mp h.2).1
  | .bin f a b, h => by
    simp only [issues, List.append_eq_nil_iff, Option.toList_eq_nil_iff, Option.map_eq_none_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1.1, evalI_eq hI h.1.2]
    exact hI.2 f _ _ (Option.or_eq_none_iff.mp h.2).1
  | .ifThen c t e, h => by
    simp only [issues, List.append_eq_nil_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1]
    split
    · rename_i hc; simp only [hc, ↓reduceIte] at h; exact evalI_eq hI h.2
    · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact evalI_eq hI h.2
  | .hof f l b, h => by
    simp only [issues, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1]
    exact HoFn.apply_congr f _ fun x hx => evalI_eq hI (h.2 x hx)

theorem UnFn.issue_ne_sumWraps (f : UnFn) (v : Value) : f.issue v ≠ some .sumWraps := by
  unfold UnFn.issue wrapIf rangeIssue domainIssue
  split <;> (try split) <;> (try split) <;> simp

theorem BinFn.issue_ne_sumWraps (f : BinFn) (v w : Value) : f.issue v w ≠ some .sumWraps := by
  unfold BinFn.issue wrapIf rangeIssue domainIssue nanIssue
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem UnFn.issueAll_ne_sumWraps (f : UnFn) (v : Value) : f.issueAll v ≠ some .sumWraps := by
  intro h
  unfold UnFn.issueAll at h
  cases hi : f.issue v with
  | some k => rw [hi] at h; exact f.issue_ne_sumWraps v (hi.trans h)
  | none => rw [hi, Option.none_or] at h; cases UnFn.infIssue_eq h

theorem BinFn.issueAll_ne_sumWraps (f : BinFn) (v w : Value) : f.issueAll v w ≠ some .sumWraps := by
  intro h
  unfold BinFn.issueAll at h
  cases hi : f.issue v w with
  | some k => rw [hi] at h; exact f.issue_ne_sumWraps v w (hi.trans h)
  | none => rw [hi, Option.none_or] at h; cases BinFn.infIssue_eq h

/-- Row-level issues are never `SUM`s. -/
theorem Expr.issues_ne_sumWraps {row : Row} :
    ∀ {e : Expr} {p : Issue × Expr}, p ∈ e.issues row → p.1 ≠ .sumWraps
  | .lit _, _, h | .field _, _, h => by simp [issues] at h
  | .un f a, p, h => by
    simp only [issues, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at h
    rcases h with h | ⟨i, hi, rfl⟩
    · exact issues_ne_sumWraps h
    · rintro rfl; exact f.issueAll_ne_sumWraps _ hi
  | .bin f a b, p, h => by
    simp only [issues, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at h
    rcases h with (h | h) | ⟨i, hi, rfl⟩
    · exact issues_ne_sumWraps h
    · exact issues_ne_sumWraps h
    · rintro rfl; exact f.issueAll_ne_sumWraps _ _ hi
  | .ifThen c t e, p, h => by
    simp only [issues, List.mem_append] at h
    rcases h with h | h
    · exact issues_ne_sumWraps h
    · split at h
      · exact issues_ne_sumWraps h
      · exact issues_ne_sumWraps h
  | .hof _ l b, p, h => by
    simp only [issues, List.mem_append, List.mem_flatMap] at h
    rcases h with h | ⟨_, _, h⟩
    · exact issues_ne_sumWraps h
    · exact issues_ne_sumWraps h

theorem UnFn.issue_ne_infinite (f : UnFn) (v : Value) : f.issue v ≠ some .infinite := by
  unfold UnFn.issue wrapIf rangeIssue domainIssue
  split <;> (try split) <;> (try split) <;> simp

theorem BinFn.issue_ne_infinite (f : BinFn) (v w : Value) : f.issue v w ≠ some .infinite := by
  unfold BinFn.issue wrapIf rangeIssue domainIssue nanIssue
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

/-- A call whose only issue is assumed (`Issue.assumed`: an overflow to `±∞`)
has no error issue: the engine's function agrees with Lean's there. -/
theorem issue_none_of_assumed {o i : Option Issue} {k : Issue} (h : o.or i = some k)
    (hk : k.assumed = true) (h1 : o ≠ some .sumWraps) (h2 : o ≠ some .infinite) : o = none := by
  cases o with
  | none => rfl
  | some k' =>
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    cases k' <;> simp_all [Issue.assumed]

/-- **Unchecked evaluation is exact** where every issue is assumed: a
`SUM` (which keeps its check) or an overflow to `±∞` (#575), where Lean keeps
the IEEE value an engine gives. -/
theorem Expr.evalI_eq_assumed {I : Impl} (hI : I.Faithful) {row : Row} :
    ∀ {e : Expr}, (∀ p ∈ e.issues row, p.1.assumed = true) → e.evalI I row = e.eval row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, h => by
    have ha : ∀ p ∈ a.issues row, p.1.assumed = true := fun p hp => h p (by simp [issues, hp])
    simp only [evalI, eval, evalI_eq_assumed hI ha]
    apply hI.1 f _
    cases hk : f.issueAll (a.eval row) with
    | none => exact (Option.or_eq_none_iff.mp hk).1
    | some k =>
      have := h (k, .un f a) (by simp [issues, hk])
      exact issue_none_of_assumed hk this (f.issue_ne_sumWraps _) (f.issue_ne_infinite _)
  | .bin f a b, h => by
    have ha : ∀ p ∈ a.issues row, p.1.assumed = true := fun p hp => h p (by simp [issues, hp])
    have hb : ∀ p ∈ b.issues row, p.1.assumed = true := fun p hp => h p (by simp [issues, hp])
    simp only [evalI, eval, evalI_eq_assumed hI ha, evalI_eq_assumed hI hb]
    apply hI.2 f _ _
    cases hk : f.issueAll (a.eval row) (b.eval row) with
    | none => exact (Option.or_eq_none_iff.mp hk).1
    | some k =>
      have := h (k, .bin f a b) (by simp [issues, hk])
      exact issue_none_of_assumed hk this (f.issue_ne_sumWraps _ _) (f.issue_ne_infinite _ _)
  | .ifThen c t e, h => by
    have hc : ∀ p ∈ c.issues row, p.1.assumed = true := fun p hp => h p (by simp [issues, hp])
    simp only [evalI, eval, evalI_eq_assumed hI hc]
    split
    · rename_i hct
      exact evalI_eq_assumed hI fun p hp => h p (by simp [issues, hct, hp])
    · rename_i hct
      exact evalI_eq_assumed hI fun p hp => h p (by simp [issues, hct, hp])
  | .hof f l b, h => by
    have hl : ∀ p ∈ l.issues row, p.1.assumed = true := fun p hp => h p (by simp [issues, hp])
    simp only [evalI, eval, evalI_eq_assumed hI hl]
    exact HoFn.apply_congr f _ fun x hx => evalI_eq_assumed hI fun p hp =>
      h p (by simp only [issues, List.mem_append, List.mem_flatMap]; exact .inr ⟨x, hx, hp⟩)

theorem Expr.evalI_eq_of {I : Impl} (hI : I.Faithful) {row : Row} {e : Expr}
    (h : ∀ p ∈ e.issues row, p.1.assumed = true) : e.evalI I row = e.eval row :=
  evalI_eq_assumed hI h

/-! ## Relations -/

def leftJoinRowI (I : Impl) (on : Expr) (rightArity : Nat) (ys : Relation) (x : Row) : Relation :=
  let ms := (ys.map (x ++ ·)).filter fun row => (on.evalI I row).isTrue
  if ms.isEmpty then [x ++ List.replicate rightArity .null] else ms

def hasMatchI (I : Impl) (on : Expr) (ys : Relation) (x : Row) : Bool :=
  ys.any fun y => (on.evalI I (x ++ y)).isTrue

def Measure.keptI (I : Impl) (m : Measure) (rows : Relation) : Relation :=
  match m.filter with
  | none => rows
  | some c => rows.filter fun row => (c.evalI I row).isTrue

def Measure.inputsI (I : Impl) (m : Measure) (rows : Relation) : List Value :=
  let vs := ((m.keptI I rows).map (m.arg.evalI I)).filter (· != .null)
  if m.distinct then dedup vs else vs

def Measure.evalI (I : Impl) (rows : Relation) (m : Measure) : Value :=
  match m.fn with
  | .collect => AggFn.collect.apply (m.inputsI I (rows.mergeSort (sortLe m.sort)))
  | .pick last => (AggFn.pick last).apply (m.inputsI I (rows.mergeSort (sortLe m.sort)))
  | .concat sep => (AggFn.concat sep).apply (m.inputsI I (rows.mergeSort (sortLe m.sort)))
  | .mode => AggFn.mode.apply (m.inputsI I (rows.mergeSort (sortLe m.sort)))
  | f => f.apply (m.inputsI I rows)

def groupKeyI (I : Impl) (gs : List Expr) (row : Row) : Row := gs.map (·.evalI I row)

def aggregateEvalI (I : Impl) (gs : List Expr) (ms : List Measure) (rows : Relation) : Relation :=
  if gs.isEmpty then [ms.map (·.evalI I rows)]
  else (dedup (rows.map (groupKeyI I gs))).map fun k =>
    k ++ ms.map (·.evalI I (rows.filter fun row => groupKeyI I gs row == k))

/-- `Rel.eval` with the engine's functions. -/
def Rel.evalI (I : Impl) (cat : Catalog) : Rel → Relation
  | .read t => (cat t).rows
  | .values _ rows => rows
  | .filter r c => (r.evalI I cat).filter fun row => (c.evalI I row).isTrue
  | .project r es => (r.evalI I cat).map fun row => row ++ es.map (·.evalI I row)
  | .emit r m => (r.evalI I cat).map fun row => m.map (row.getD · .null)
  | .cross a b => crossRows (a.evalI I cat) (b.evalI I cat)
  | .join a b .inner on =>
      (crossRows (a.evalI I cat) (b.evalI I cat)).filter fun row => (on.evalI I row).isTrue
  | .join a b .left on =>
      (a.evalI I cat).flatMap (leftJoinRowI I on (b.arity cat) (b.evalI I cat))
  | .fetch r off cnt =>
      let rest := (r.evalI I cat).drop off
      match cnt with
      | none => rest
      | some n => rest.take n
  | .unionAll a b => a.evalI I cat ++ b.evalI I cat
  | .window r part sort fns => windowEval part sort fns (r.evalI I cat)
  | .semi a b anti on => (a.evalI I cat).filter fun x => hasMatchI I on (b.evalI I cat) x != anti
  | .orderBy r keys => (r.evalI I cat).mergeSort (sortLe keys)
  | .distinct r => dedup (r.evalI I cat)
  | .unnest r c => (r.evalI I cat).flatMap (unnestRow c)
  | .aggregate r gs ms => aggregateEvalI I gs ms (r.evalI I cat)

/-! ## Congruence -/

theorem aggregateEvalI_eq {I : Impl} {gs : List Expr} {ms : List Measure} {rows : Relation}
    (h : ∀ row ∈ rows, ∀ e ∈ gs ++ ms.flatMap Measure.exprs, e.evalI I row = e.eval row) :
    aggregateEvalI I gs ms rows = aggregateEval gs ms rows := by
  have hk : ∀ row ∈ rows, groupKeyI I gs row = groupKey gs row := fun row hr =>
    List.map_congr_left fun g hg => h row hr g (List.mem_append_left _ hg)
  -- A measure on rows of `rows`.
  have hin : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) →
      m.inputsI I sub = m.inputs sub := by
    intro m hm sub hsub
    have he : ∀ row ∈ sub, ∀ e ∈ m.exprs, e.evalI I row = e.eval row := fun row hr e he =>
      h row (hsub row hr) e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, he⟩))
    have hkept : m.keptI I sub = m.kept sub := by
      cases hc : m.filter with
      | none => simp only [Measure.keptI, Measure.kept, hc]
      | some c =>
        simp only [Measure.keptI, Measure.kept, hc]
        exact List.filter_congr fun row hr => by
          rw [he row hr c (by simp [Measure.exprs, hc])]
    have hsub' : ∀ row ∈ m.kept sub, row ∈ sub := fun row hr => by
      unfold Measure.kept at hr; split at hr
      · exact hr
      · exact (List.mem_filter.mp hr).1
    simp only [Measure.inputsI, Measure.inputs, hkept]
    rw [List.map_congr_left fun row hr => he row (hsub' row hr) m.arg (by simp [Measure.exprs])]
  have hm : ∀ m ∈ ms, ∀ sub : Relation, (∀ row ∈ sub, row ∈ rows) → m.evalI I sub = m.eval sub := by
    intro m hm sub hsub
    cases hf : m.fn
    all_goals simp only [Measure.evalI, Measure.eval, hf]
    case collect => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case pick => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case concat => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    case mode => rw [hin m hm _ fun row hr => hsub row (List.mem_mergeSort.mp hr)]
    all_goals rw [hin m hm sub hsub]
  unfold aggregateEvalI aggregateEval
  split
  · exact congrArg (fun x => [x]) (List.map_congr_left fun m hmm => hm m hmm rows fun _ h => h)
  · rw [List.map_congr_left hk]
    refine List.map_congr_left fun k _ => ?_
    have hf : (rows.filter fun row => groupKeyI I gs row == k) = groupRows gs rows k :=
      List.filter_congr fun row hr => by rw [hk row hr]
    rw [hf]
    exact congrArg (k ++ ·) (List.map_congr_left fun m hmm =>
      hm m hmm _ fun _ hr => (List.mem_filter.mp hr).1)

theorem leftJoinRowI_eq {I : Impl} {on : Expr} {n : Nat} {ys : Relation} {x : Row}
    (h : ∀ y ∈ ys, on.evalI I (x ++ y) = on.eval (x ++ y)) :
    leftJoinRowI I on n ys x = leftJoinRow on n ys x := by
  have : ((ys.map (x ++ ·)).filter fun row => (on.evalI I row).isTrue) =
      (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue :=
    List.filter_congr fun row hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      rw [h y hy]
  simp only [leftJoinRowI, leftJoinRow, this]

theorem hasMatchI_eq {I : Impl} {on : Expr} {x : Row} :
    ∀ {ys : Relation}, (∀ y ∈ ys, on.evalI I (x ++ y) = on.eval (x ++ y)) →
      hasMatchI I on ys x = hasMatch on ys x
  | [], _ => rfl
  | y :: ys, h => by
    have ih := hasMatchI_eq (ys := ys) fun z hz => h z (by simp [hz])
    simp only [hasMatchI, hasMatch, List.any_cons] at ih ⊢
    rw [h y (by simp), ih]

/-! ## The loose plan has all the rows -/

theorem mem_leftJoinRow {on : Expr} {n : Nat} {ys : Relation} {x row : Row} :
    row ∈ leftJoinRow on n ys x ↔
      (∃ y ∈ ys, (on.eval (x ++ y)).isTrue = true ∧ row = x ++ y) ∨
        ((∀ y ∈ ys, (on.eval (x ++ y)).isTrue = false) ∧ row = x ++ List.replicate n .null) := by
  unfold leftJoinRow
  simp only []
  split
  · rename_i he
    have hn : ∀ y ∈ ys, (on.eval (x ++ y)).isTrue = false := fun y hy => by
      cases hc : (on.eval (x ++ y)).isTrue
      · rfl
      · have : x ++ y ∈ (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue :=
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨y, hy, rfl⟩, hc⟩
        simp [List.isEmpty_iff.mp he] at this
    simp only [List.mem_singleton]
    constructor
    · exact fun h => .inr ⟨hn, h⟩
    · rintro (⟨y, hy, ht, _⟩ | ⟨_, h⟩)
      · simp [hn y hy] at ht
      · exact h
  · rename_i he
    simp only [List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, ht⟩; exact .inl ⟨y, hy, ht, rfl⟩
    · rintro (⟨y, hy, ht, rfl⟩ | ⟨hn, _⟩)
      · exact ⟨⟨y, hy, rfl⟩, ht⟩
      · refine absurd ?_ he
        rw [List.isEmpty_iff, List.filter_eq_nil_iff]
        intro a ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        simp [hn y hy]

mutual
/-- `loose` keeps all the rows: no left join's right side loses a filter. -/
def Rel.looseSub : Rel → Bool
  | .read _ | .values _ _ => true
  | .fetch r _ _ | .window r _ _ _ | .aggregate r _ _ | .filter r _ | .project r _ | .emit r _
  | .orderBy r _ | .distinct r => r.looseSub
  | .cross a b | .unionAll a b | .join a b .inner _ | .semi a b _ _ => a.looseSub && b.looseSub
  | .join a b .left _ => a.looseSub && b.looseExact
  -- Guards are not eliminated through an `UNNEST`.
  | .unnest _ _ => false

/-- `loose` gives the same rows (as a set), and keeps all the rows below. -/
def Rel.looseExact : Rel → Bool
  | .read _ | .values _ _ => true
  -- `loose` leaves these alone; their inputs must allow guard elimination too.
  | .fetch r _ _ | .window r _ _ _ | .aggregate r _ _ => r.looseSub
  | .project r _ | .emit r _ | .orderBy r _ | .distinct r => r.looseExact
  | .cross a b | .unionAll a b | .join a b .left _ => a.looseExact && b.looseExact
  | .filter _ _ | .join _ _ .inner _ | .semi _ _ _ _ | .unnest _ _ => false
end

theorem Rel.looseExact_mem {cat : Catalog} :
    ∀ {r : Rel}, r.looseExact = true → ∀ row, row ∈ r.loose.eval cat ↔ row ∈ r.eval cat
  | .read _, _, _ | .values _ _, _, _ | .fetch _ _ _, _, _ | .window _ _ _ _, _, _
  | .aggregate _ _ _, _, _ => .rfl
  | .filter _ _, h, _ | .join _ _ .inner _, h, _ | .semi _ _ _ _, h, _ | .unnest _ _, h, _ => by
    simp [looseExact] at h
  | .project r es, h, row => by
    simp only [loose, eval, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, (looseExact_mem (r := r) h x).mp hx, e⟩,
      fun ⟨x, hx, e⟩ => ⟨x, (looseExact_mem (r := r) h x).mpr hx, e⟩⟩
  | .emit r m, h, row => by
    simp only [loose, eval, List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, (looseExact_mem (r := r) h x).mp hx, e⟩,
      fun ⟨x, hx, e⟩ => ⟨x, (looseExact_mem (r := r) h x).mpr hx, e⟩⟩
  | .orderBy r _, h, row => by
    simp only [loose, eval, List.mem_mergeSort]; exact looseExact_mem (r := r) h row
  | .distinct r, h, row => by
    simp only [loose, eval, mem_dedup]; exact looseExact_mem (r := r) h row
  | .cross a b, h, row => by
    simp only [looseExact, Bool.and_eq_true] at h
    simp only [loose, eval, mem_crossRows, looseExact_mem h.1, looseExact_mem h.2]
  | .unionAll a b, h, row => by
    simp only [looseExact, Bool.and_eq_true] at h
    simp only [loose, eval, List.mem_append, looseExact_mem h.1, looseExact_mem h.2]
  | .join a b .left on, h, row => by
    simp only [looseExact, Bool.and_eq_true] at h
    simp only [loose, eval, List.mem_flatMap, mem_leftJoinRow, loose_arity, looseExact_mem h.1,
      looseExact_mem h.2]

theorem Rel.mem_loose {cat : Catalog} :
    ∀ {r : Rel}, r.looseSub = true → ∀ row ∈ r.eval cat, row ∈ r.loose.eval cat
  | .read _, _, _, h | .values _ _, _, _, h | .fetch _ _ _, _, _, h | .window _ _ _ _, _, _, h
  | .aggregate _ _ _, _, _, h => h
  | .filter r _, hs, row, h => by
    simp only [eval, List.mem_filter] at h; exact mem_loose (r := r) hs row h.1
  | .semi r _ _ _, hs, row, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [eval, List.mem_filter] at h; exact mem_loose (r := r) hs.1 row h.1
  | .project r es, hs, row, h => by
    simp only [eval, List.mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp only [loose, eval, List.mem_map]; exact ⟨x, mem_loose (r := r) hs x hx, rfl⟩
  | .emit r m, hs, row, h => by
    simp only [eval, List.mem_map] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp only [loose, eval, List.mem_map]; exact ⟨x, mem_loose (r := r) hs x hx, rfl⟩
  | .orderBy r _, hs, row, h => by
    simp only [eval, List.mem_mergeSort] at h; exact mem_loose (r := r) hs row h
  | .distinct r, hs, row, h => by
    simp only [eval, mem_dedup] at h; exact mem_loose (r := r) hs row h
  | .cross a b, hs, row, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [eval, mem_crossRows] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    simp only [loose, eval, mem_crossRows]
    exact ⟨x, mem_loose hs.1 x hx, y, mem_loose hs.2 y hy, rfl⟩
  | .join a b .inner _, hs, row, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [eval, List.mem_filter, mem_crossRows] at h
    obtain ⟨⟨x, hx, y, hy, rfl⟩, _⟩ := h
    simp only [loose, eval, mem_crossRows]
    exact ⟨x, mem_loose hs.1 x hx, y, mem_loose hs.2 y hy, rfl⟩
  | .unionAll a b, hs, row, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [eval, List.mem_append] at h
    simp only [loose, eval, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_loose hs.1 row h)
    · exact .inr (mem_loose hs.2 row h)
  | .join a b .left on, hs, row, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [eval, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [loose, eval, List.mem_flatMap, loose_arity, mem_leftJoinRow,
      looseExact_mem hs.2]
    exact ⟨x, mem_loose hs.1 x hx, mem_leftJoinRow.mp h⟩

theorem Rel.looseExact_sub : ∀ {r : Rel}, r.looseExact = true → r.looseSub = true
  | .read _, _ | .values _ _, _ => rfl
  | .fetch _ _ _, h | .window _ _ _ _, h | .aggregate _ _ _, h => h
  | .filter _ _, h | .join _ _ .inner _, h | .semi _ _ _ _, h => by simp [looseExact] at h
  | .project r _, h | .emit r _, h | .orderBy r _, h | .distinct r, h => looseExact_sub (r := r) h
  | .cross a b, h | .unionAll a b, h => by
    simp only [looseExact, Bool.and_eq_true] at h
    simp only [looseSub, looseExact_sub h.1, looseExact_sub h.2, Bool.and_self]
  | .join a b .left _, h => by
    simp only [looseExact, Bool.and_eq_true] at h
    simp only [looseSub, looseExact_sub h.1, h.2, Bool.and_self]

theorem Rel.mem_loose_if {cat : Catalog} {r : Rel} (hs : r.looseSub = true) (u : Bool) {row : Row}
    (h : row ∈ r.eval cat) : row ∈ (if u then r.loose else r).eval cat := by
  cases u
  · exact h
  · exact mem_loose hs row h

/-! ## Plans -/

/-- **Guard elimination**: if the only issues a plan can run into are assumed
(`Issue.assumed`): an integer `SUM` that may wrap (which keeps its check) or
an overflow to `±∞` (whose check the written SQL keeps, #575), running it
with unchecked functions gives `Rel.eval`. -/
theorem Rel.evalI_eq {I : Impl} (hI : I.Faithful) {cat : Catalog} :
    ∀ {u : Bool} {r : Rel}, r.looseSub = true → (∀ p, r.HasIssue cat u p → p.1.assumed = true) →
      r.evalI I cat = r.eval cat
  | _, .read _, _, _ | _, .values _ _, _, _ => rfl
  | _, .filter r c, hs, h => by
    have ih := evalI_eq hI (u := true) (r := r) hs fun p hp => h p (.inl hp)
    simp only [evalI, eval, ih]
    exact List.filter_congr fun row hr => by
      rw [Expr.evalI_eq_of hI fun p hp => h p (.inr ⟨row, mem_loose (r := r) hs row hr, hp⟩)]
  | u, .project r es, hs, h => by
    have ih := evalI_eq hI (u := u) (r := r) hs fun p hp => h p (.inl hp)
    simp only [evalI, eval, ih]
    exact List.map_congr_left fun row hr => congrArg (row ++ ·) (List.map_congr_left fun e he =>
      Expr.evalI_eq_of hI fun p hp => h p (.inr ⟨row, mem_loose_if (r := r) hs u hr, e, he, hp⟩))
  | u, .emit r _, hs, h => by
    simp only [evalI, eval, evalI_eq hI (u := u) (r := r) hs h]
  | u, .fetch r _ cnt, hs, h => by
    simp only [looseSub] at hs
    have ih := evalI_eq hI (u := u) (r := r) hs h
    cases cnt <;> simp only [evalI, eval, ih]
  | u, .window r _ _ _, hs, h => by
    simp only [looseSub] at hs
    simp only [evalI, eval, evalI_eq hI (u := u) (r := r) hs fun p hp => h p (.inl hp)]
  | u, .orderBy r _, hs, h => by
    simp only [evalI, eval, evalI_eq hI (u := u) (r := r) hs h]
  | u, .distinct r, hs, h => by
    simp only [evalI, eval, evalI_eq hI (u := u) (r := r) hs h]
  | u, .cross a b, hs, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalI, eval, evalI_eq hI (u := u) (r := a) hs.1 fun p hp => h p (.inl hp),
      evalI_eq hI (u := u) (r := b) hs.2 fun p hp => h p (.inr hp)]
  | u, .unionAll a b, hs, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalI, eval, evalI_eq hI (u := u) (r := a) hs.1 fun p hp => h p (.inl hp),
      evalI_eq hI (u := u) (r := b) hs.2 fun p hp => h p (.inr hp)]
  | _, .join a b .inner on, hs, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalI, eval, evalI_eq hI (u := true) (r := a) hs.1 fun p hp => h p (.inl hp),
      evalI_eq hI (u := true) (r := b) hs.2 fun p hp => h p (.inr (.inl hp))]
    exact List.filter_congr fun row hr => by
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp hr
      rw [Expr.evalI_eq_of hI fun p hp =>
        h p (.inr (.inr ⟨x, mem_loose hs.1 x hx, y, mem_loose hs.2 y hy, hp⟩))]
  | _, .join a b .left on, hs, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalI, eval, evalI_eq hI (u := true) (r := a) hs.1 fun p hp => h p (.inl hp)]
    have hbi : b.evalI I cat = b.eval cat := by
      refine evalI_eq hI (u := true) (r := b) ?_ fun p hp => h p (.inr (.inl hp))
      exact looseExact_sub hs.2
    rw [hbi]
    exact flatMap_congr fun x hx => leftJoinRowI_eq fun y hy =>
      Expr.evalI_eq_of hI fun p hp => h p (.inr (.inr ⟨x, mem_loose hs.1 x hx, y,
        (looseExact_mem hs.2 y).mpr hy, hp⟩))
  | _, .semi a b _ on, hs, h => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalI, eval, evalI_eq hI (u := true) (r := a) hs.1 fun p hp => h p (.inl hp),
      evalI_eq hI (u := true) (r := b) hs.2 fun p hp => h p (.inr (.inl hp))]
    exact List.filter_congr fun x hx => by
      rw [hasMatchI_eq fun y hy => Expr.evalI_eq_of hI fun p hp =>
        h p (.inr (.inr ⟨x, mem_loose hs.1 x hx, y, mem_loose hs.2 y hy, hp⟩))]
  | u, .aggregate r gs ms, hs, h => by
    simp only [looseSub] at hs
    have ih := evalI_eq hI (u := u) (r := r) hs fun p hp => h p (.inl hp)
    simp only [evalI, eval, ih]
    exact aggregateEvalI_eq fun row hr e he =>
      Expr.evalI_eq_of hI fun p hp => h p (.inr (.inl ⟨row, mem_loose_if (r := r) hs u hr, e, he, hp⟩))

/-- **Guard elimination from contracts**: when `Rel.mayIssues` reports
nothing but assumed issues (integer `SUM`s, overflows to `±∞`), on every catalog that satisfies the
preconditions and the size hypothesis (`Rel.Small`: windows read fewer than
`2⁶²` rows, aggregates fewer than `2⁶³`), the plan runs correctly with unchecked functions. -/
theorem Rel.guardFree_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true)
    {I : Impl} (hI : I.Faithful) : r.evalI I cat = r.eval cat :=
  evalI_eq hI (u := false) hs fun p hp => by
    have := List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf hsmall p hp)
    simpa using this

/-! ## Per-expression guards

`Rel.guardFree_sound` drops every check of a plan or none. Here each
expression decides for itself: `Rel.marks` lists, per node, the expressions
whose abstract issues (`Expr.mayIssues`, on the same inputs `Rel.mayIssues`
analyses) are none, and `Rel.evalG` runs exactly those with the engine's
unchecked functions and the rest with Lean's. `Rel.evalG_marks`: the result is
`Rel.eval`. So the SQL keeps the checks of the other expressions only. -/

/-- Evaluate `e` unchecked (`u`) or with Lean's functions. -/
def Expr.evalIf (I : Impl) (u : Bool) (row : Row) (e : Expr) : Value :=
  if u then e.evalI I row else e.eval row

/-- Which expressions of a plan run unchecked, as a tree parallel to the plan:
a node's slots, then the marks of its inputs, in order. The slots of a
filter, a join and a semi-join are `[0]` (the condition) or `[]`; of a
projection, the indices of its expressions; of an aggregate, `[0]` when all
its grouping expressions and measures' arguments, filters and sort keys
(`Measure.exprs`) run unchecked. -/
inductive Marks where
  | mk (slots : List Nat) (inputs : List Marks)

/-- Every check stays. -/
def Marks.checked : Marks := .mk [] []

def Marks.slots : Marks → List Nat
  | .mk s _ => s

def Marks.input (m : Marks) (i : Nat) : Marks :=
  match m with
  | .mk _ ks => ks.getD i .checked

/-- `Rel.eval` with each expression unchecked where `Marks` says so. -/
def Rel.evalG (I : Impl) (cat : Catalog) : Marks → Rel → Relation
  | _, .read t => (cat t).rows
  | _, .values _ rows => rows
  | m, .filter r c =>
      (r.evalG I cat (m.input 0)).filter fun row => (c.evalIf I (m.slots.contains 0) row).isTrue
  | m, .project r es =>
      (r.evalG I cat (m.input 0)).map fun row =>
        row ++ es.mapIdx fun i e => e.evalIf I (m.slots.contains i) row
  | m, .emit r mp => (r.evalG I cat (m.input 0)).map fun row => mp.map (row.getD · .null)
  | m, .cross a b => crossRows (a.evalG I cat (m.input 0)) (b.evalG I cat (m.input 1))
  | m, .join a b .inner on =>
      (crossRows (a.evalG I cat (m.input 0)) (b.evalG I cat (m.input 1))).filter fun row =>
        (on.evalIf I (m.slots.contains 0) row).isTrue
  | m, .join a b .left on =>
      (a.evalG I cat (m.input 0)).flatMap fun x =>
        if m.slots.contains 0 then leftJoinRowI I on (b.arity cat) (b.evalG I cat (m.input 1)) x
        else leftJoinRow on (b.arity cat) (b.evalG I cat (m.input 1)) x
  | m, .fetch r off cnt =>
      let rest := (r.evalG I cat (m.input 0)).drop off
      match cnt with
      | none => rest
      | some n => rest.take n
  | m, .unionAll a b => a.evalG I cat (m.input 0) ++ b.evalG I cat (m.input 1)
  | m, .window r part sort fns => windowEval part sort fns (r.evalG I cat (m.input 0))
  | m, .semi a b anti on =>
      (a.evalG I cat (m.input 0)).filter fun x =>
        (if m.slots.contains 0 then hasMatchI I on (b.evalG I cat (m.input 1)) x
         else hasMatch on (b.evalG I cat (m.input 1)) x) != anti
  | m, .orderBy r keys => (r.evalG I cat (m.input 0)).mergeSort (sortLe keys)
  | m, .distinct r => dedup (r.evalG I cat (m.input 0))
  | m, .unnest r c => (r.evalG I cat (m.input 0)).flatMap (unnestRow c)
  | m, .aggregate r gs ms =>
      if m.slots.contains 0 then aggregateEvalI I gs ms (r.evalG I cat (m.input 0))
      else aggregateEval gs ms (r.evalG I cat (m.input 0))

/-- The indices of the expressions `ok` accepts. -/
def okSlots (es : List Expr) (ok : Expr → Bool) : List Nat :=
  (List.range es.length).filter fun i => match es[i]? with
    | some e => ok e
    | none => false

/-- The expressions without abstract issues, on the inputs `Rel.mayIssues`
analyses them on. -/
def Rel.marks (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (T : WindowKeys) :
    Bool → Rel → Marks
  | _, .read _ | _, .values _ _ => .checked
  | _, .filter r c =>
    .mk (if (c.mayIssues (r.loose.aeval cat A F T true) (r.loose.facts cat F T)).isEmpty
      then [0] else []) [r.marks cat A F T true]
  | u, .project r es =>
    let s := if u then r.loose else r
    .mk (okSlots es fun e => (e.mayIssues (s.aeval cat A F T true) (s.facts cat F T)).isEmpty)
      [r.marks cat A F T u]
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r
  | u, .unnest r _ | u, .window r _ _ _ => .mk [] [r.marks cat A F T u]
  | u, .cross a b | u, .unionAll a b => .mk [] [a.marks cat A F T u, b.marks cat A F T u]
  | _, .join a b _ on | _, .semi a b _ on =>
    let ab := Rel.cross a.loose b.loose
    .mk (if (on.mayIssues (ab.aeval cat A F T true) (ab.facts cat F T)).isEmpty then [0] else [])
      [a.marks cat A F T true, b.marks cat A F T true]
  | u, .aggregate r gs ms =>
    let s := if u then r.loose else r
    .mk (if (gs ++ ms.flatMap Measure.exprs).all
        (fun e => (e.mayIssues (s.aeval cat A F T true) (s.facts cat F T)).isEmpty)
      then [0] else []) [r.marks cat A F T u]

theorem contains_zero_ite {c : Bool} (h : (if c = true then [0] else ([] : List Nat)).contains 0 = true) :
    c = true := by
  cases c <;> simp_all

theorem ite_eq_right_of {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c → a = b) :
    (if c then a else b) = b := by
  split
  · exact h ‹_›
  · rfl

theorem Expr.evalIf_eq {I : Impl} {u : Bool} {row : Row} {e : Expr}
    (h : u = true → e.evalI I row = e.eval row) : e.evalIf I u row = e.eval row := by
  cases u with
  | false => rfl
  | true => exact h rfl

theorem mapIdx_eq_map {α β : Type} {l : List α} {f : Nat → α → β} {g : α → β}
    (h : ∀ i (hi : i < l.length), f i l[i] = g l[i]) : l.mapIdx f = l.map g := by
  apply List.ext_getElem (by simp)
  intro i h1 _
  simp only [List.getElem_mapIdx, List.getElem_map]
  exact h i (by simpa using h1)

theorem okSlots_mem {es : List Expr} {ok : Expr → Bool} {i : Nat} (hi : i < es.length)
    (h : i ∈ okSlots es ok) : ok es[i] = true := by
  simp only [okSlots, List.mem_filter, List.getElem?_eq_getElem hi] at h
  exact h.2

section
variable {cat : Catalog} (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
  (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
  (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
  {I : Impl} (hI : I.Faithful)

include hcat hA hF hT hI in
/-- An expression without abstract issues on `s` runs unchecked on `s`'s rows. -/
theorem Expr.evalI_of_safe {s : Rel} (hwf : s.WF cat) (hsm : s.Small cat) {e : Expr}
    (he : (e.mayIssues (s.aeval cat A F T true) (s.facts cat F T)).isEmpty = true) {row : Row}
    (hrow : row ∈ s.eval cat) : e.evalI I row = e.eval row :=
  Expr.evalI_eq hI (List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
    have := Expr.mayIssues_sound (Rel.aeval_sound hcat hA hF hT (sz := true) hwf (fun _ => hsm) row hrow)
      (Rel.facts_sound hcat hF hT hwf row hrow) (KsHold.nil row) e p hp
    simp [List.isEmpty_iff.mp he] at this)

include hcat hA hF hT hI in
/-- A join condition without abstract issues runs unchecked on the pairs of
loose rows. -/
theorem Expr.evalI_of_safe_cond {a b : Rel} (ha : a.WF cat) (hb : b.WF cat) (hsa : a.Small cat)
    (hsb : b.Small cat) {on : Expr}
    (he : (on.mayIssues ((Rel.cross a.loose b.loose).aeval cat A F T true)
      ((Rel.cross a.loose b.loose).facts cat F T)).isEmpty = true) {x y : Row}
    (hx : x ∈ a.loose.eval cat) (hy : y ∈ b.loose.eval cat) :
    on.evalI I (x ++ y) = on.eval (x ++ y) :=
  Expr.evalI_eq hI (List.eq_nil_iff_forall_not_mem.mpr fun _ hp => by
    have := condIssue_sound hcat hA hF hT ha hb hsa hsb hx hy hp
    simp [List.isEmpty_iff.mp he] at this)

theorem Rel.loose_if_wf {u : Bool} {r : Rel} (h : r.WF cat) :
    (if u then r.loose else r).WF cat := by
  cases u
  · exact h
  · exact loose_wf h

theorem Rel.loose_if_small {u : Bool} {r : Rel} (h : r.Small cat) :
    (if u then r.loose else r).Small cat := by
  cases u
  · exact h
  · exact Rel.Small.loose (r := r) h

include hcat hA hF hT hI in
/-- **Per-expression guard elimination**: on every catalog that satisfies the
preconditions and the size hypothesis, the plan with the expressions
`Rel.marks` lists unchecked gives `Rel.eval`. -/
theorem Rel.evalG_marks :
    ∀ {u : Bool} {r : Rel}, r.WF cat → r.Small cat → r.looseSub = true →
      r.evalG I cat (r.marks cat A F T u) = r.eval cat
  | _, .read _, _, _, _ | _, .values _ _, _, _, _ => rfl
  | _, .filter r c, hwf, hsm, hs => by
    have ih := evalG_marks (u := true) (r := r) hwf.1 hsm hs
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, eval, ih]
    refine List.filter_congr fun row hr => ?_
    rw [Expr.evalIf_eq fun hc => Expr.evalI_of_safe hcat hA hF hT hI (loose_wf hwf.1)
      (Rel.Small.loose (r := r) hsm) (contains_zero_ite hc) (mem_loose (r := r) hs row hr)]
  | u, .project r es, hwf, hsm, hs => by
    have ih := evalG_marks (u := u) (r := r) hwf.1 hsm hs
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, eval, ih]
    refine List.map_congr_left fun row hr => congrArg (row ++ ·) (mapIdx_eq_map fun i hi => ?_)
    refine Expr.evalIf_eq fun hc => Expr.evalI_of_safe hcat hA hF hT hI (loose_if_wf hwf.1)
      (loose_if_small hsm) ?_ (mem_loose_if (r := r) hs u hr)
    exact okSlots_mem hi (by simpa using hc)
  | u, .emit r _, hwf, hsm, hs => by
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, eval,
      evalG_marks (u := u) (r := r) hwf.1 hsm hs]
  | u, .fetch r _ cnt, hwf, hsm, hs => by
    simp only [looseSub] at hs
    have ih := evalG_marks (u := u) (r := r) hwf hsm hs
    cases cnt <;> simp only [evalG, marks, Marks.input, List.getD_cons_zero, eval, ih]
  | u, .window r _ _ _, hwf, hsm, hs => by
    simp only [looseSub] at hs
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, eval,
      evalG_marks (u := u) (r := r) hwf.1 hsm.2 hs]
  | u, .orderBy r _, hwf, hsm, hs => by
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, eval,
      evalG_marks (u := u) (r := r) hwf.1 hsm hs]
  | u, .distinct r, hwf, hsm, hs => by
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, eval,
      evalG_marks (u := u) (r := r) hwf hsm hs]
  | _, .unnest _ _, _, _, hs => by simp [looseSub] at hs
  | u, .cross a b, hwf, hsm, hs => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, List.getD_cons_succ, eval,
      evalG_marks (u := u) (r := a) hwf.1 hsm.1 hs.1,
      evalG_marks (u := u) (r := b) hwf.2 hsm.2 hs.2]
  | u, .unionAll a b, hwf, hsm, hs => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalG, marks, Marks.input, List.getD_cons_zero, List.getD_cons_succ, eval,
      evalG_marks (u := u) (r := a) hwf.1 hsm.1 hs.1,
      evalG_marks (u := u) (r := b) hwf.2.1 hsm.2 hs.2]
  | _, .join a b .inner on, hwf, hsm, hs => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, List.getD_cons_succ,
      eval, evalG_marks (u := true) (r := a) hwf.1 hsm.1 hs.1,
      evalG_marks (u := true) (r := b) hwf.2.1 hsm.2 hs.2]
    refine List.filter_congr fun row hr => ?_
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_crossRows.mp hr
    rw [Expr.evalIf_eq fun hc => Expr.evalI_of_safe_cond hcat hA hF hT hI hwf.1 hwf.2.1 hsm.1
      hsm.2 (contains_zero_ite hc) (mem_loose hs.1 x hx) (mem_loose hs.2 y hy)]
  | _, .join a b .left on, hwf, hsm, hs => by
    simp only [looseSub, Bool.and_eq_true] at hs
    have hbs := looseExact_sub hs.2
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, List.getD_cons_succ,
      eval, evalG_marks (u := true) (r := a) hwf.1 hsm.1 hs.1,
      evalG_marks (u := true) (r := b) hwf.2.1 hsm.2 hbs]
    refine flatMap_congr fun x hx => ?_
    split
    · rename_i hc
      exact leftJoinRowI_eq fun y hy => Expr.evalI_of_safe_cond hcat hA hF hT hI hwf.1 hwf.2.1
        hsm.1 hsm.2 hc (mem_loose hs.1 x hx)
        ((looseExact_mem hs.2 y).mpr hy)
    · rfl
  | _, .semi a b _ on, hwf, hsm, hs => by
    simp only [looseSub, Bool.and_eq_true] at hs
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, List.getD_cons_succ,
      eval, evalG_marks (u := true) (r := a) hwf.1 hsm.1 hs.1,
      evalG_marks (u := true) (r := b) hwf.2.1 hsm.2 hs.2]
    refine List.filter_congr fun x hx => ?_
    split
    · rename_i hc
      rw [hasMatchI_eq fun y hy => Expr.evalI_of_safe_cond hcat hA hF hT hI hwf.1 hwf.2.1
        hsm.1 hsm.2 hc (mem_loose hs.1 x hx) (mem_loose hs.2 y hy)]
      simp
    · rfl
  | u, .aggregate r gs ms, hwf, hsm, hs => by
    simp only [looseSub] at hs
    have ih := evalG_marks (u := u) (r := r) hwf.1 hsm.2 hs
    simp only [evalG, marks, Marks.input, Marks.slots, List.getD_cons_zero, eval, ih]
    refine ite_eq_right_of fun hc => ?_
    have hall := contains_zero_ite hc
    exact aggregateEvalI_eq fun row hr e he =>
      Expr.evalI_of_safe hcat hA hF hT hI (loose_if_wf hwf.1) (loose_if_small hsm.2)
        (List.all_eq_true.mp hall e he) (mem_loose_if (r := r) hs u hr)

end

end Substrait
