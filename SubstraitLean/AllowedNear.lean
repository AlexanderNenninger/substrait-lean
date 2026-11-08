import SubstraitLean.Ties
import SubstraitLean.Robust
import SubstraitLean.AllowedP

/-!
# Postconditions on every allowed result (#899)

`contract_sound_all` (`Ties.lean`) proves a postcondition on every result of
every order the reference allows (`Rel.OrderAllowed`): rows in any order the
plan leaves open, each double `SUM` and `AVG` with `Rel.eval`'s value.
`Rel.Allowed` allows more where a measure's value is a choice of the
reference: before D25 a double `SUM` or `AVG` added in any order and grouping
(`FloatSums`), and still a statistical aggregate (`StatProps`). A
postcondition proved of `Rel.eval`'s values must allow for the others.

`contract_sound_allowed` (`AllowedAnalysis.lean`) does that, from this
module's closeness. A postcondition narrowed by each
column's tolerance (`Expr.narrow`, `Robust.lean`) and proved under
`contract_sound_all` holds on every result `Rel.Allowed` admits, for a plan
whose allowed results are, up to the observation `q`, results of its orders:
`Rel.FloatOpenSafe`, the side condition.

`Rel.FloatOpenSafe` fails for a plan that reads an open sum where a last bit
changes which rows come out: a filter, a join condition, a group, sort or
window key, a `DISTINCT` on it (#929's discontinuity rows, #568). Two
sufficient conditions are proved:

* `Rel.floatOpenSafe_of_closed`: a plan with no open measure
  (`Rel.closedB`): every allowed result is one of an order.
* `Rel.floatOpenSafe_aggregate`: an aggregate over such a plan, whose open
  measures are double `SUM`s and `AVG`s (`aggCtx`: equal up to the order of
  their additions).

D25 (#915) takes `FloatSums` out of `Rel.Allowed`: a double `SUM` or `AVG`
is order-free (`AggFn.orderFree`), so `Measure.closedB` holds of it, and
`Measure.Allowed.near_eval` by reflexivity. `Rel.FloatOpenSafe` is not yet
true of every plan: `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` stay choices of
the reference (`StatProps`) until their exact moments (#918), and
`QUANTILE_CONT` (`contAllowed`) is a choice too. Once those go,
`contract_sound_allowed` needs no side condition. -/

namespace Substrait

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
      intro f hf vs v h; cases f <;> simp_all [AggFn.sorts, AggFn.Allowed]
    refine ⟨s, hp, hsort hs, ?_⟩
    simp only [hs, ↓reduceIte]
    rw [Measure.eval_sorts hs, mergeSort_eq_of_sorted (hsort hs)]
    exact key _ hs _ _ hv
  · simp only [hs, Bool.false_or] at hm
    refine ⟨rows.mergeSort (sortLe m.sort), List.mergeSort_perm _ _, mergeSort_sorted _ _, ?_⟩
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact Measure.allowed_eq hm h

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
    exact Forall2.weaken (fun _ _ ⟨vs, he, hv⟩ => ⟨vs, he, forall2_closed_orderAllowed hms hv⟩) h

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
them to choose rows. After D25 (#916) it holds for every plan. -/
def Rel.FloatOpenSafe (q : Obs) (ctx : ObsCtx) (cat : Catalog) (r : Rel) : Prop :=
  ∀ out, r.Allowed cat out → ∃ out', r.OrderAllowed cat out' ∧ Relation.Equiv q ctx out' out

theorem Rel.floatOpenSafe_of_closed {q : Obs} {ctx : ObsCtx} (hc : ctx.ReflAt q) {cat : Catalog}
    {r : Rel} (h : r.closedB = true) : r.FloatOpenSafe q ctx cat :=
  fun out ho => ⟨out, Rel.allowed_orderAllowed h ho, .refl' hc out⟩

/-! ## An aggregate with open double sums -/

/-- The observation of a plan's double sums: rows as a multiset, doubles
within the plan's bound. -/
def Obs.plan : Obs := { rows := .multiset, floats := .within "plan" }

/-- A double `SUM` or `AVG`: its value depends on the order of its additions. -/
def Measure.openB (m : Measure) : Bool := m.fn == .fsum || m.fn == .avg

/-- Two values of an open measure over the same values: sums of them in two
orders (`FloatSums`), or two averages of such sums. -/
def Measure.Open (m : Measure) (a b : Int) : Prop :=
  match m.fn with
  | .fsum => ∃ vs, FloatSums vs a ∧ FloatSums vs b
  | .avg => ∃ vs c₁ c₂, FloatSums vs c₁ ∧ FloatSums vs c₂ ∧
      a = FloatCode.fdiv c₁ (FloatCode.ofInt vs.length) ∧
      b = FloatCode.fdiv c₂ (FloatCode.ofInt vs.length)
  | _ => a = b

/-- The context of an aggregate's output with `g` group columns and the
measures `ms`: an open measure's column is a double, whose values are equal
up to the order of the additions (`Measure.Open`); every other column is
exact. -/
def aggCtx (g : Nat) (ms : List Measure) : ObsCtx where
  kind col := if g ≤ col ∧ (ms[col - g]?.any (·.openB)) = true then .double else .other
  near _ col x y := x = y ∨
    ∃ m a b, ms[col - g]? = some m ∧ x = fp64.canon a ∧ y = fp64.canon b ∧ m.Open a b

theorem aggCtx_reflAt (g : Nat) (ms : List Measure) : (aggCtx g ms).ReflAt Obs.plan :=
  ⟨fun _ _ _ _ => .inl rfl, fun _ h hne => absurd (h.symm.trans rfl) hne⟩

/-- An open measure's allowed value is equal, up to the order of its
additions, to `Measure.eval`'s, in its column `g + j`. -/
theorem Measure.Allowed.near_eval {m : Measure} (ho : m.openB = true) {g j : Nat}
    {ms : List Measure} (_hj : ms[j]? = some m) {grp : Relation} {v : Value}
    (h : m.Allowed grp v) : Value.Equiv Obs.plan (aggCtx g ms) (g + j) (m.eval grp) v := by
  -- D25: a double `SUM` or `AVG` is order-free, so its allowed value is
  -- `Measure.eval`'s.
  have hof : m.orderFree = true := by
    simp only [Measure.openB, Bool.or_eq_true, beq_iff_eq] at ho
    simp only [Measure.orderFree, AggFn.orderFree]
    rcases ho with h | h <;> simp [h]
  rw [← Measure.allowed_eq hof h]
  exact Value.Equiv.refl (aggCtx_reflAt g ms) _

/-- The measures of a group: their allowed values are, column by column,
equal up to `aggCtx` to the values of an order. -/
theorem measures_near {g : Nat} {ms₀ : List Measure} {grp : Relation}
    (hms : ∀ m ∈ ms₀, m.closedB = true ∨ m.openB = true) :
    ∀ (ms : List Measure) (i : Nat) (vs : List Value), (∀ j m, ms[j]? = some m → ms₀[i + j]? = some m) →
      Forall2 (fun m v => m.Allowed grp v) ms vs →
      ∃ vs', Forall2 (fun m v => m.OrderAllowed grp v) ms vs' ∧
        Row.EquivFrom Obs.plan (aggCtx g ms₀) (g + i) vs' vs
  | [], _, [], _, _ => ⟨[], .nil, trivial⟩
  | m :: ms, i, v :: vs, hidx, .cons hv t => by
    have h0 : ms₀[i]? = some m := by simpa using hidx 0 m rfl
    have hidx' : ∀ j m', ms[j]? = some m' → ms₀[i + 1 + j]? = some m' := by
      intro j m' h
      have := hidx (j + 1) m' (by simpa using h)
      rwa [Nat.add_assoc, Nat.add_comm 1 j]
    obtain ⟨vs', t', e'⟩ := measures_near hms ms (i + 1) vs hidx' t
    have hrest : Row.EquivFrom Obs.plan (aggCtx g ms₀) (g + i + 1) vs' vs := by
      simpa [Nat.add_assoc] using e'
    rcases hms m (List.mem_of_getElem? h0) with hc | ho
    · exact ⟨v :: vs', .cons (hv.orderAllowed hc) t',
        ⟨Value.Equiv.refl (aggCtx_reflAt g ms₀) v, hrest⟩⟩
    · exact ⟨m.eval grp :: vs', .cons (Measure.eval_orderAllowed m grp) t',
        ⟨hv.near_eval ho h0, hrest⟩⟩
  | [], _, _ :: _, _, h | _ :: _, _, [], _, h => by cases h

theorem Row.EquivFrom.append_left {q : Obs} {ctx : ObsCtx} (hc : ctx.ReflAt q) :
    ∀ (k : Row) {i : Nat} {a b : Row}, Row.EquivFrom q ctx (i + k.length) a b →
      Row.EquivFrom q ctx i (k ++ a) (k ++ b)
  | [], i, a, b, h => by simpa using h
  | x :: k, i, a, b, h =>
    ⟨Value.Equiv.refl hc x, Row.EquivFrom.append_left hc k (i := i + 1)
      (by simpa [Nat.add_assoc, Nat.add_comm 1 k.length] using h)⟩

/-- `Forall2` through an intermediate list. -/
theorem Forall2.lift {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} {R : γ → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a ∈ as, ∀ b, P a b → ∃ c, Q a c ∧ R c b) →
      Forall2 P as bs → ∃ cs, Forall2 Q as cs ∧ Forall2 R cs bs
  | _, _, _, .nil => ⟨[], .nil, .nil⟩
  | a :: as, _, h, .cons p t => by
    obtain ⟨c, hq, hr⟩ := h a (List.mem_cons_self ..) _ p
    obtain ⟨cs, hq', hr'⟩ := Forall2.lift (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) t
    exact ⟨c :: cs, .cons hq hq', .cons hr hr'⟩

/-- An aggregate's allowed output, over rows in some order, is equal up to
`aggCtx` to the output of an order of each group's rows. -/
theorem aggAllowed_near {gs : List Expr} {ms : List Measure} {rows out : Relation}
    (hms : ∀ m ∈ ms, m.closedB = true ∨ m.openB = true) (h : aggAllowed gs ms rows out) :
    ∃ out', aggOrderAllowed gs ms rows out' ∧
      Forall2 (Row.Equiv Obs.plan (aggCtx gs.length ms)) out' out := by
  have hc := aggCtx_reflAt gs.length ms
  have hidx : ∀ j m, ms[j]? = some m → ms[0 + j]? = some m := fun j m h => by simpa using h
  unfold aggAllowed at h; unfold aggOrderAllowed
  split at h
  · next hg =>
    obtain ⟨vs, rfl, hv⟩ := h
    have hg0 : gs.length = 0 := by simpa using List.isEmpty_iff.mp hg
    obtain ⟨vs', hv', e⟩ := measures_near (g := gs.length) (grp := rows) hms ms 0 vs hidx hv
    refine ⟨[vs'], ?_, .cons ?_ .nil⟩
    · simp only [hg, ite_true]; exact ⟨vs', rfl, hv'⟩
    · show Row.EquivFrom _ _ 0 vs' vs; simpa [hg0] using e
  · next hg =>
    simp only [hg, Bool.false_eq_true, ite_false]
    refine Forall2.lift (fun k hk row ⟨vs, he, hv⟩ => ?_) h
    obtain ⟨vs', hv', e⟩ := measures_near (g := gs.length) (grp := groupRows gs rows k) hms ms 0 vs
      hidx hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
    refine ⟨groupKey gs x ++ vs', ⟨vs', rfl, hv'⟩, ?_⟩
    rw [he]
    exact Row.EquivFrom.append_left hc _ (i := 0) (by simpa [groupKey] using e)

/-- **An aggregate over a plan without open measures is safe**: its double
`SUM`s and `AVG`s are equal to its orders' up to the order of their
additions, and nothing above reads them. -/
theorem Rel.floatOpenSafe_aggregate {cat : Catalog} {r : Rel} {gs : List Expr}
    {ms : List Measure} (hr : r.closedB = true)
    (hms : ∀ m ∈ ms, m.closedB = true ∨ m.openB = true) :
    (Rel.aggregate r gs ms).FloatOpenSafe Obs.plan (aggCtx gs.length ms) cat := by
  rintro out ⟨i, hi, o, hp, ho⟩
  obtain ⟨o', ho', e⟩ := aggAllowed_near hms ho
  exact ⟨o', ⟨i, Rel.allowed_orderAllowed hr hi, o', .refl _, ho'⟩, ⟨o, e, hp.symm⟩⟩

end Substrait
