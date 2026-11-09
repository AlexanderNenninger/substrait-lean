import Sverify.Core.Allowed

/-!
# Every order the reference allows (#679, D24)

The reference leaves the order of rows open, and with it how ties are broken
(`tie_order`, `tie_pick`): the rows that tie in an `ORDER BY` or in a
window's order come in any order, a `FETCH` takes the first rows of any
order the plan allows, and `FIRST`, `LAST`, `ARG_MIN`/`ARG_MAX`,
`STRING_AGG`, `collect` and `MODE` take their rows in any order their own
`ORDER BY` allows. `Rel.eval` picks one of these orders (a stable
`List.mergeSort`, rows in list order): it is the evaluator of the
deterministic profile, which fixes them.

`Rel.OrderAllowed` (`OrderAllowed.lean`) holds the results of every such
order. It is `Rel.Allowed` with every other choice taken as `Rel.eval` takes
it: a statistical aggregate keeps `Rel.eval`'s value, so `stat_algo` stays
with `Rel.Allowed` and #85's bounds. A double `SUM` or `AVG` is no choice
(D25): the exact sum rounded once, whatever the order of the rows.

* `Rel.orderAllowed_allowed`: each order's result is one `Rel.Allowed`
  allows; `Rel.eval_orderAllowed` (`OrderAllowed.lean`): `Rel.eval`'s is one
  of them.
* The analyses are proved over every order where they are stated:
  `Rel.facts_sound_all`, `Rel.maxRows_sound_all`, `Rel.aeval_sound_all` and
  `contract_sound_all` in `Contracts.lean`, `Rel.keys_sound_all` in
  `Keys.lean` (#904). Their `Rel.eval` forms are corollaries by
  `Rel.eval_orderAllowed`.
* `Rel.orderAllowed_capReads` (`AllowedAnalysis.lean`): a row cap keeps every order.
-/

namespace Substrait

/-! ## Measures -/

theorem Measure.OrderAllowed.allowed {m : Measure} {rows : Relation} {v : Value}
    (h : m.OrderAllowed rows v) : m.Allowed rows v := by
  obtain ⟨s, hp, hs, h⟩ := h
  split at h
  · next hsorts =>
    subst h
    refine ⟨s, hp, fun _ => hs, ?_⟩
    rw [Measure.eval_sorts hsorts, mergeSort_eq_of_sorted hs]
    exact AggFn.apply_allowed _ _
  · exact ⟨rows, .refl _, fun h' => absurd h' ‹_›, AggFn.allowed_of_picks h⟩

theorem aggOrderAllowed_allowed {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (h : aggOrderAllowed gs ms rows out) : aggAllowed gs ms rows out := by
  have hm : ∀ {grp : Relation} {vs : List Value},
      Forall2 (fun m v => m.OrderAllowed grp v) ms vs → Forall2 (fun m v => m.Allowed grp v) ms vs :=
    Forall2.weaken fun _ _ h => h.allowed
  unfold aggOrderAllowed at h; unfold aggAllowed
  split at h
  · next hg => obtain ⟨vs, rfl, hv⟩ := h; simp only [hg, ite_true]; exact ⟨vs, rfl, hm hv⟩
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    obtain ⟨ks, hks, h⟩ := h
    exact ⟨ks, hks, Forall2.weaken (fun _ _ ⟨vs, he, hv⟩ => ⟨vs, he, hm hv⟩) h⟩

/-! ## Plans -/

/-- **Every order is one the reference allows.** -/
theorem Rel.orderAllowed_allowed {cat : Catalog} :
    ∀ {r : Rel} {out : Relation}, r.OrderAllowed cat out → r.Allowed cat out
  | .read _, _, h | .values _ _, _, h => h
  | .filter r _, _, ⟨i, hi, h⟩ | .project r _, _, ⟨i, hi, h⟩ | .emit r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .fetch r _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .cross a b, _, ⟨x, y, hx, hy, h⟩ | .unionAll a b, _, ⟨x, y, hx, hy, h⟩
  | .semi a b _ _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_allowed (r := a) hx, orderAllowed_allowed (r := b) hy, h⟩
  | .join a b .inner _, _, ⟨x, y, hx, hy, h⟩ | .join a b .left _, _, ⟨x, y, hx, hy, h⟩ =>
    ⟨x, y, orderAllowed_allowed (r := a) hx, orderAllowed_allowed (r := b) hy, h⟩
  | .window r _ _ _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .orderBy r _, _, ⟨i, hi, h⟩ => ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .distinct r, _, ⟨i, hi, h⟩ | .unnest r _, _, ⟨i, hi, h⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, h⟩
  | .aggregate r _ _, _, ⟨i, hi, o, h, ho⟩ =>
    ⟨i, orderAllowed_allowed (r := r) hi, o, h, aggOrderAllowed_allowed ho⟩

end Substrait
