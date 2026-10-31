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
* `Rel.evalI_eq`: if every issue a plan can run into is a `SUM` that may
  wrap, the unchecked plan computes `Rel.eval`. `Rel.guardFree_sound`
  derives this from an empty `Rel.mayIssues` (up to `sumWraps`), which is
  what `substrait-check --contract` reports as `guard_free`.

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

/-- **Unchecked evaluation is exact** where no issue happens. -/
theorem Expr.evalI_eq {I : Impl} (hI : I.Faithful) {row : Row} :
    ∀ {e : Expr}, e.issues row = [] → e.evalI I row = e.eval row
  | .lit _, _ | .field _, _ => rfl
  | .un f a, h => by
    simp only [issues, List.append_eq_nil_iff, Option.toList_eq_nil_iff, Option.map_eq_none_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1]
    exact hI.1 f _ h.2
  | .bin f a b, h => by
    simp only [issues, List.append_eq_nil_iff, Option.toList_eq_nil_iff, Option.map_eq_none_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1.1, evalI_eq hI h.1.2]
    exact hI.2 f _ _ h.2
  | .ifThen c t e, h => by
    simp only [issues, List.append_eq_nil_iff] at h
    simp only [evalI, eval, evalI_eq hI h.1]
    split
    · rename_i hc; simp only [hc, ↓reduceIte] at h; exact evalI_eq hI h.2
    · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact evalI_eq hI h.2

theorem UnFn.issue_ne_sumWraps (f : UnFn) (v : Value) : f.issue v ≠ some .sumWraps := by
  unfold UnFn.issue wrapIf rangeIssue
  split <;> (try split) <;> (try split) <;> simp

theorem BinFn.issue_ne_sumWraps (f : BinFn) (v w : Value) : f.issue v w ≠ some .sumWraps := by
  unfold BinFn.issue wrapIf rangeIssue
  split <;> (try split) <;> (try split) <;> (try split) <;> simp

/-- Row-level issues are never `SUM`s. -/
theorem Expr.issues_ne_sumWraps {row : Row} :
    ∀ {e : Expr} {p : Issue × Expr}, p ∈ e.issues row → p.1 ≠ .sumWraps
  | .lit _, _, h | .field _, _, h => by simp [issues] at h
  | .un f a, p, h => by
    simp only [issues, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at h
    rcases h with h | ⟨i, hi, rfl⟩
    · exact issues_ne_sumWraps h
    · rintro rfl; exact f.issue_ne_sumWraps _ hi
  | .bin f a b, p, h => by
    simp only [issues, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at h
    rcases h with (h | h) | ⟨i, hi, rfl⟩
    · exact issues_ne_sumWraps h
    · exact issues_ne_sumWraps h
    · rintro rfl; exact f.issue_ne_sumWraps _ _ hi
  | .ifThen c t e, p, h => by
    simp only [issues, List.mem_append] at h
    rcases h with h | h
    · exact issues_ne_sumWraps h
    · split at h
      · exact issues_ne_sumWraps h
      · exact issues_ne_sumWraps h

theorem Expr.evalI_eq_of {I : Impl} (hI : I.Faithful) {row : Row} {e : Expr}
    (h : ∀ p ∈ e.issues row, p.1 = .sumWraps) : e.evalI I row = e.eval row :=
  evalI_eq hI (List.eq_nil_iff_forall_not_mem.mpr fun p hp => issues_ne_sumWraps hp (h p hp))

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

/-- **Guard elimination**: if the only issue a plan can run into is an
integer `SUM` that may wrap (which keeps its check), running it with
unchecked functions gives `Rel.eval`. -/
theorem Rel.evalI_eq {I : Impl} (hI : I.Faithful) {cat : Catalog} :
    ∀ {u : Bool} {r : Rel}, r.looseSub = true → (∀ p, r.HasIssue cat u p → p.1 = .sumWraps) →
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
    simp only [evalI, eval, evalI_eq hI (u := u) (r := r) hs h]
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
nothing but integer `SUM`s, on every catalog that satisfies the
preconditions, the plan runs correctly with unchecked functions. -/
theorem Rel.guardFree_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1 == .sumWraps) = true)
    {I : Impl} (hI : I.Faithful) : r.evalI I cat = r.eval cat :=
  evalI_eq hI (u := false) hs fun p hp => by
    have := List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf p hp)
    simpa using this

end Substrait
