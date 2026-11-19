import Sverify.Core.Ties
import Sverify.Core.Robust
import Sverify.Core.AllowedP

/-!
# Postconditions on every allowed result (#899)

`contract_sound_all` (`Ties.lean`) proves a postcondition on every result of
every order the reference allows (`Rel.OrderAllowed`): rows in any order the
plan leaves open, each double `SUM` and `AVG` with `Rel.eval`'s value.
`Rel.Allowed` allows more where a measure's value is a choice of the
reference: `QUANTILE_CONT`, whose value lies between two neighbours
(`contAllowed`). Before D25 a double `SUM` or `AVG` added in any order and
grouping (`FloatSums`), and before D30 a statistical aggregate was any value
with `StatProps`; both are one value now. A postcondition proved of
`Rel.eval`'s values must allow for the others.

`contract_sound_allowed` (`AllowedAnalysis.lean`) does that, from this
module's closeness. A postcondition narrowed by each
column's tolerance (`Expr.narrow`, `Robust.lean`) and proved under
`contract_sound_all` holds on every result `Rel.Allowed` admits, for a plan
whose allowed results are, up to the observation `q`, results of its orders:
`Rel.FloatOpenSafe`, the side condition.

`Rel.FloatOpenSafe` fails for a plan that reads an open sum where a last bit
changes which rows come out: a filter, a join condition, a group, sort or
window key, a `DISTINCT` on it (#929's discontinuity rows, #568).
`Rel.floatOpenSafe_of_closed` proves it for a plan with no open measure
(`Rel.closedB`): every allowed result is one of an order.

D25 (#915) takes `FloatSums` out of `Rel.Allowed`: a double `SUM` or `AVG`
is order-free (`AggFn.orderFree`), so `Measure.closedB` holds of it. D30 (#918) does the same for
`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`. `QUANTILE_CONT` (`contAllowed`)
is the one choice left, so `Rel.FloatOpenSafe` is not yet true of every plan,
and `contract_sound_allowed` keeps its side condition. -/

namespace Substrait
variable [Boxes.Ambient]

/-! ## Measures whose allowed values are an order's -/

/-- A measure whose every allowed value is one of an order's: it sorts its
rows, or is a function of their multiset (`Measure.orderFree`). -/
def Measure.closedB (m : Measure) : Bool := m.fn.sorts || m.orderFree

theorem Measure.Allowed.orderAllowed {m : Measure} (hm : m.closedB = true) {rows : Relation}
    {v : Value} (h : m.Allowed rows v) : m.OrderAllowed rows v := by
  unfold Measure.closedB at hm
  by_cases hs : m.fn.sorts = true
  · obtain ⟨s, hp, hsort, hv⟩ := h
    have key : ∀ f : AggFn, f.sorts = true → ∀ vs v, f.Allowed vs v → v = f.apply vs := by
      intro f hf vs v h; cases f <;> simp_all [AggFn.sorts, AggFn.Allowed, AggFn.Picks, AggFn.classPick]
    refine ⟨s, hp, hsort hs, ?_⟩
    simp only [hs, ↓reduceIte]
    rw [Measure.eval_sorts hs, mergeSort_eq_of_sorted (hsort hs)]
    exact key _ hs _ _ hv
  · simp only [hs, Bool.false_or] at hm
    refine ⟨rows.mergeSort (sortLe m.sort), List.mergeSort_perm _ _, mergeSort_sorted _ _, ?_⟩
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact Measure.allowed_picks hm h

theorem forall2_closed_orderAllowed {grp : Relation} :
    ∀ {ms : List Measure} {vs : List Value}, (∀ m ∈ ms, m.closedB = true) →
      Forall2 (fun m v => m.Allowed grp v) ms vs → Forall2 (fun m v => m.OrderAllowed grp v) ms vs
  | _, _, _, .nil => .nil
  | _, _, hms, .cons h t =>
    .cons (h.orderAllowed (hms _ (List.mem_cons_self ..)))
      (forall2_closed_orderAllowed (fun m hm => hms m (List.mem_cons_of_mem _ hm)) t)

theorem aggAllowed_orderAllowed {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (hms : ∀ m ∈ ms, m.closedB = true) (h : aggAllowed gs ms rows out) :
    aggOrderAllowed gs ms rows out := by
  unfold aggAllowed at h; unfold aggOrderAllowed
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    simp only [hg, ite_true]
    exact ⟨vs, rfl, forall2_closed_orderAllowed hms hv⟩
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    obtain ⟨ks, hks, h⟩ := h
    exact ⟨ks, hks, Forall2.weaken (fun _ _ ⟨vs, he, hv⟩ => ⟨vs, he, forall2_closed_orderAllowed hms hv⟩) h⟩

/-! ## Plans without open measures -/

/-- No measure of the plan leaves its value open. -/
def Rel.closedB : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .unnest r _ => r.closedB
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => a.closedB && b.closedB
  | .aggregate r _ ms => r.closedB && ms.all (·.closedB)

/-- **Without open measures, every allowed result is one of an order.** -/
theorem Rel.allowed_orderAllowed {cat : Catalog} :
    ∀ {r : Rel}, r.closedB = true → ∀ {out : Relation}, r.Allowed cat out → r.OrderAllowed cat out
  | .read _, _, _, h | .values _ _, _, _, h => h
  | .filter r _, hc, _, ⟨i, hi, h⟩ | .project r _, hc, _, ⟨i, hi, h⟩
  | .emit r _, hc, _, ⟨i, hi, h⟩ =>
    ⟨i, allowed_orderAllowed (r := r) hc hi, h⟩
  | .fetch r _ _, hc, _, ⟨i, hi, h⟩ => ⟨i, allowed_orderAllowed (r := r) hc hi, h⟩
  | .cross a b, hc, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, hc, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, hc, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [Rel.closedB, Bool.and_eq_true] at hc
    exact ⟨x, y, allowed_orderAllowed (r := a) hc.1 hx, allowed_orderAllowed (r := b) hc.2 hy, h⟩
  | .join a b .inner _, hc, _, ⟨x, y, hx, hy, h⟩ | .join a b .left _, hc, _, ⟨x, y, hx, hy, h⟩ => by
    simp only [Rel.closedB, Bool.and_eq_true] at hc
    exact ⟨x, y, allowed_orderAllowed (r := a) hc.1 hx, allowed_orderAllowed (r := b) hc.2 hy, h⟩
  | .window r _ _ _, hc, _, ⟨i, hi, h⟩ => ⟨i, allowed_orderAllowed (r := r) hc hi, h⟩
  | .orderBy r _, hc, _, ⟨i, hi, h⟩ => ⟨i, allowed_orderAllowed (r := r) hc hi, h⟩
  | .distinct r, hc, _, ⟨i, hi, h⟩ | .unnest r _, hc, _, ⟨i, hi, h⟩ =>
    ⟨i, allowed_orderAllowed (r := r) hc hi, h⟩
  | .aggregate r _ ms, hc, _, ⟨i, hi, o, h, ho⟩ => by
    simp only [Rel.closedB, Bool.and_eq_true, List.all_eq_true] at hc
    exact ⟨i, allowed_orderAllowed (r := r) hc.1 hi, o, h, aggAllowed_orderAllowed hc.2 ho⟩

/-! ## The side condition -/

/-- **The side condition**: every result the reference allows for `r` is,
up to `q`, the result of one of its orders. The double `SUM`s and `AVG`s
left open reach the output only where `q` tolerates them, and nothing reads
them to choose rows. After D25 (#916) and D30 (#918) it holds of every plan
without `QUANTILE_CONT`. -/
def Rel.FloatOpenSafe (q : Obs) (ctx : ObsCtx) (cat : Catalog) (r : Rel) : Prop :=
  ∀ out, r.Allowed cat out → ∃ out', r.OrderAllowed cat out' ∧ Relation.Equiv q ctx out' out

theorem Rel.floatOpenSafe_of_closed {q : Obs} {ctx : ObsCtx} (hc : ctx.ReflAt q) {cat : Catalog}
    {r : Rel} (h : r.closedB = true) : r.FloatOpenSafe q ctx cat :=
  fun out ho => ⟨out, Rel.allowed_orderAllowed h ho, .refl' hc out⟩

/-! ## The observation of a plan's double sums -/

/-- The observation of a plan's double sums: rows as a multiset, doubles
within the plan's bound. -/
def Obs.plan : Obs := { rows := .multiset, floats := .within "plan" }

end Substrait
