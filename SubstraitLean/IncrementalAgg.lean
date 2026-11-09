import SubstraitLean.TouchedGroups
import SubstraitLean.TableFormat
import Sverify.Core.Kinds

/-!
# Delta rules for `COUNT`, `SUM` and `DISTINCT` (#248, stage 1)

`COUNT` and integer `SUM` per group are linear over Z-sets: each is a sum of
`g(row) · weight` over the input (`ZSet.lin`). So a view can keep, per group,

* the number of input rows (`rowsIn`),
* for each measure, the number of values it adds up (rows that pass its
  `FILTER` and whose argument is not NULL, `valuesIn`), and their exact sum
  (`sumIn`),

and add a batch's change to them: the state of `old + Δ` is the state of
`old` plus the state of `Δ` (`ZSet.lin_append`). A group is in the output
while it has rows, so groups appear when their count leaves 0 and disappear
when it returns to 0. `DISTINCT` is the same with no measures: a count per
row, and a row is in the output while its count is positive.

* `LinState`: a measure's state in general, linear features of its values
  summed per group (`featIn`) and a finish; `LinState.Sound` says the finish
  gives the aggregate. `COUNT` and `SUM` keep the number of values and their
  sum (`sumState`, `sumState_sound`); `SUM` and `AVG` of doubles keep their
  exact moments (`IncrementalFloat.lean`).
* `outRow_eq`: on a Z-set with the weights of a bag, the state's output row
  of a group is the aggregate's row (`Measure.eval`) for every measure with
  a sound state.
* `aggregate_state`: the aggregate is the output rows of the groups with a
  positive count, in any order.
* `aggregate_maintained`: after a batch, the aggregate is the old rows of
  the groups the batch does not touch, and the rows of the touched groups
  from the old state plus the state of the change. This is what
  `sverify._linear` computes.
* `distinct_state`, `distinct_maintained`: the same for `DISTINCT`.

The change `Δ` only has to have the right weights (`ChangeFeed`): a change
feed may delete and re-insert a row.

`SUM` is exact here. An engine adds up 64-bit integers, so a `SUM` whose
result leaves 64 bits is an error, which the contract checker assumes away
and the job checks on the data (`Report.assumed`). The maintained sum is the
exact sum of the group's values, so checking that it fits is the same check.
-/

namespace Substrait
namespace LinearAgg

/-- A measure with a delta rule: `COUNT` or integer `SUM`, without
`DISTINCT`. (`FILTER` is allowed, and `ORDER BY` changes nothing.) -/
def Linear (m : Measure) : Prop := (m.fn = .count ∨ m.fn = .sum) ∧ m.distinct = false

variable [Boxes.Ambient]
/-- The row passes the measure's `FILTER`. -/
def keeps (m : Measure) (row : Row) : Bool :=
  match m.filter with
  | none => true
  | some c => (c.eval row).isTrue

/-- The row adds a value to the measure: it passes the filter, and the
argument is not NULL. -/
def counts (m : Measure) (row : Row) : Bool := keeps m row && m.arg.eval row != .null

def intOf : Value → Int
  | .int i | .dec _ i => i
  | _ => 0

def ind (b : Bool) (x : Int) : Int := if b then x else 0

/-- The weight of group `k`'s rows. -/
def rowsIn (gs : List Expr) (k : Row) (z : ZSet) : Int :=
  ZSet.lin (fun r => ind (groupKey gs r == k) 1) z

/-- The weighted sum of a feature `f` of the values measure `m` adds up in
group `k`. -/
def featIn (gs : List Expr) (m : Measure) (f : Value → Int) (k : Row) (z : ZSet) : Int :=
  ZSet.lin (fun r => ind (groupKey gs r == k && counts m r) (f (m.arg.eval r))) z

/-- The weight of the values measure `m` adds up in group `k`. -/
def valuesIn (gs : List Expr) (m : Measure) (k : Row) (z : ZSet) : Int :=
  featIn gs m (fun _ => 1) k z

/-- The weighted sum of the values measure `m` adds up in group `k`. -/
def sumIn (gs : List Expr) (m : Measure) (k : Row) (z : ZSet) : Int := featIn gs m intOf k z

/-- A measure's value from the group's state: the count of values for
`COUNT`; for `SUM`, NULL without values, else the sum: a decimal of scale `s`
where the plan's kinds give the argument that scale (`sc = some s`, #923). -/
def finish (m : Measure) (sc : Option Nat) (n s : Int) : Value :=
  match m.fn with
  | .count => .int n
  | _ => if n = 0 then .null else match sc with
    | some d => .dec d s
    | none => .int s

/-- The scale of a `SUM` of an argument of kind `k`: a decimal's, none for an
integer. -/
def sumScale : Kind → Option Nat
  | .dec _ s => some s
  | _ => none

/-- The kind a `SUM`'s argument has where its scale is `sc`. -/
def scaleKind : Option Nat → Kind
  | some s => .dec 38 s
  | none => .int

/-- **The premise of `finish_eval`** (D29): on the rows, a `SUM`'s argument
has the kind the plan gives it, a decimal of scale `s` where `sc = some s` and
an integer otherwise. A kind-checked plan has it (`ArgScale.of_kindT`). -/
def ArgScale (sc : Option Nat) (m : Measure) (rows : Relation) : Prop :=
  m.fn = .sum → ∀ row ∈ rows, (m.arg.eval row).hasKind (scaleKind sc) = true

omit [Boxes.Ambient] in
theorem hasKind_dec_scale {p s : Nat} {v : Value} (h : v.hasKind (.dec p s) = true) :
    v.hasKind (.dec 38 s) = true := by
  cases v <;> simp_all [Value.hasKind]

/-- A `SUM` whose argument the kind checker types as an integer or a decimal
(`Expr.kindT`) on rows of the kinds `env` has the premise, at the scale of the
argument's kind. -/
theorem ArgScale.of_kindT {env : List Kind} {m : Measure} {rows : Relation} {t : KT}
    (hr : ∀ row ∈ rows, Row.HasKinds env row) (hk : m.arg.kindT env = some t)
    (ht : t.toKind = .int ∨ ∃ p s, t.toKind = .dec p s) :
    ArgScale (sumScale t.toKind) m rows := fun _ row hrow => by
  have h := Expr.kindT_sound (hr row hrow) hk
  simp only [KT.has] at h
  rcases ht with ht | ⟨p, s, ht⟩ <;> rw [ht] at h ⊢
  · exact h
  · exact hasKind_dec_scale h

theorem ArgScale.mono {sc : Option Nat} {m : Measure} {rows rows' : Relation}
    (h : ArgScale sc m rows) (hs : ∀ r ∈ rows', r ∈ rows) : ArgScale sc m rows' :=
  fun hf r hr => h hf r (hs r hr)

/-! ## A measure's linear state -/

/-- A measure's state: features of each value it adds up, each summed with
the rows' weights over the group (`featIn`), and the finish that gives the
measure from those sums. `good` is what the finish needs of each value. -/
structure LinState where
  feats : List (Value → Int)
  fin : List Int → Value
  good : Value → Prop := fun _ => True

/-- `L` finishes `m`: on every list of non-`NULL` values `L` accepts, the
sums of its features finish to the aggregate. -/
def LinState.Sound (L : LinState) (m : Measure) : Prop :=
  m.distinct = false ∧ m.fn.sorts = false ∧
    ∀ vs : List Value, (∀ v ∈ vs, v ≠ .null ∧ L.good v) →
      L.fin (L.feats.map fun f => (vs.map f).sum) = m.fn.apply vs

/-- `L`'s premise holds of the values `m` adds up on `rows`. -/
def LinState.Good (L : LinState) (m : Measure) (rows : Relation) : Prop :=
  ∀ r ∈ rows, counts m r = true → L.good (m.arg.eval r)

theorem LinState.Good.mono {L : LinState} {m : Measure} {rows rows' : Relation}
    (h : L.Good m rows) (hs : ∀ r ∈ rows', r ∈ rows) : L.Good m rows' :=
  fun r hr => h r (hs r hr)

/-- `COUNT`'s and `SUM`'s state: the number of values and their sum, a
`SUM`'s a decimal of scale `s` where `sc = some s` (`ArgScale`). -/
def sumState (m : Measure) (sc : Option Nat) : LinState where
  feats := [fun _ => 1, intOf]
  fin l := finish m sc (l.getD 0 0) (l.getD 1 0)
  good v := m.fn = .sum → v.hasKind (scaleKind sc) = true

theorem ArgScale.good {sc : Option Nat} {m : Measure} {rows : Relation} (h : ArgScale sc m rows) :
    (sumState m sc).Good m rows := fun r hr _ hs => h hs r hr

/-- Group `k`'s output row, from the state of `z`; `st` gives each measure
its state. -/
def outRow (gs : List Expr) (ms : List Measure) (st : Measure → LinState) (z : ZSet) (k : Row) :
    Row :=
  k ++ ms.map fun m => (st m).fin ((st m).feats.map fun f => featIn gs m f k z)

/-! ## The state adds up -/

theorem rowsIn_append (gs : List Expr) (k : Row) (a b : ZSet) :
    rowsIn gs k (a ++ b) = rowsIn gs k a + rowsIn gs k b := ZSet.lin_append _ _ _

theorem featIn_append (gs : List Expr) (m : Measure) (f : Value → Int) (k : Row) (a b : ZSet) :
    featIn gs m f k (a ++ b) = featIn gs m f k a + featIn gs m f k b := ZSet.lin_append _ _ _

theorem valuesIn_append (gs : List Expr) (m : Measure) (k : Row) (a b : ZSet) :
    valuesIn gs m k (a ++ b) = valuesIn gs m k a + valuesIn gs m k b := featIn_append _ _ _ _ _ _

theorem sumIn_append (gs : List Expr) (m : Measure) (k : Row) (a b : ZSet) :
    sumIn gs m k (a ++ b) = sumIn gs m k a + sumIn gs m k b := featIn_append _ _ _ _ _ _

/-- A feature's sum over a sequence of batches is its sum over them all. -/
theorem featIn_flatten (gs : List Expr) (m : Measure) (f : Value → Int) (k : Row) :
    ∀ Δs : List ZSet, (Δs.map (featIn gs m f k)).sum = featIn gs m f k Δs.flatten
  | [] => rfl
  | Δ :: Δs => by
    rw [List.map_cons, List.sum_cons, featIn_flatten gs m f k Δs, List.flatten_cons, featIn_append]

theorem featIn_congr {gs : List Expr} {m : Measure} {f : Value → Int} {k : Row} {z z' : ZSet}
    (h : ∀ r, z.weight r = z'.weight r) : featIn gs m f k z = featIn gs m f k z' :=
  ZSet.lin_congr _ h

/-- The state only depends on the weights. -/
theorem outRow_congr {gs : List Expr} {ms : List Measure} {st : Measure → LinState} {z z' : ZSet}
    (h : ∀ r, z.weight r = z'.weight r) (k : Row) : outRow gs ms st z k = outRow gs ms st z' k := by
  simp only [outRow, featIn_congr h]

theorem rowsIn_congr {gs : List Expr} {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r)
    (k : Row) : rowsIn gs k z = rowsIn gs k z' := ZSet.lin_congr _ h

omit [Boxes.Ambient] in
/-- A functional that vanishes on every row of `z` is 0 on it. -/
theorem lin_zero {g : Row → Int} {z : ZSet} (h : ∀ x ∈ z, g x.1 = 0) : ZSet.lin g z = 0 := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      rw [ZSet.lin_cons, h x List.mem_cons_self,
        ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
      simp

/-! ## On bags -/

omit [Boxes.Ambient] in
theorem lin_lift (g : Row → Int) (rows : Relation) :
    ZSet.lin g (ZSet.lift rows) = (rows.map g).sum := by
  induction rows with
  | nil => rfl
  | cons a rows ih => simp only [ZSet.lift, List.map_cons] at ih ⊢; rw [ZSet.lin_cons, ih]; simp

omit [Boxes.Ambient] in
theorem sum_ind_one (p : Row → Bool) (rows : Relation) :
    (rows.map fun r => ind (p r) 1).sum = (rows.filter p).length := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      simp only [ind] at ih
      simp only [List.map_cons, List.sum_cons, ih, List.filter_cons, ind]
      split <;> simp <;> omega

omit [Boxes.Ambient] in
theorem sum_ind (p : Row → Bool) (f : Row → Int) (rows : Relation) :
    (rows.map fun r => ind (p r) (f r)).sum = ((rows.filter p).map f).sum := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      simp only [ind] at ih
      simp only [List.map_cons, List.sum_cons, ih, List.filter_cons, ind]
      split <;> simp

omit [Boxes.Ambient] in
theorem intSum_eq (vs : List Value) : intSum vs = (vs.map intOf).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases v <;> simp [intSum, intOf, ih]

omit [Boxes.Ambient] in
/-- A `SUM` of non-NULL values of one kind, an integer or a decimal of scale
`sc`: that kind's number of their sum. -/
theorem sumOf_of_scale {sc : Option Nat} {v : Value} {vs : List Value}
    (h : ∀ w ∈ v :: vs, w.hasKind (scaleKind sc) = true ∧ w ≠ .null) :
    sumOf (v :: vs) = match sc with
      | some d => .dec d (intSum (v :: vs))
      | none => .int (intSum (v :: vs)) := by
  cases sc with
  | some d =>
    have ha : allDecOf d (v :: vs) = true := by
      simp only [allDecOf, List.isEmpty_cons, Bool.not_false, Bool.true_and]
      exact List.all_eq_true.mpr fun w hw => by
        obtain ⟨h1, h2⟩ := h w hw
        cases w <;> simp_all [Value.hasKind, scaleKind, Value.isDecOf]
    rcases sumOf_cases (v :: vs) with ⟨s, hs, e⟩ | ⟨hn, _⟩
    · rw [e, allDecOf_scale hs ha]
    · rw [hn d] at ha; cases ha
  | none =>
    rcases sumOf_cases (v :: vs) with ⟨s, hs, _⟩ | ⟨_, e⟩
    · exfalso
      simp only [allDecOf, List.isEmpty_cons, Bool.not_false, Bool.true_and] at hs
      have := List.all_eq_true.mp hs v (by simp)
      obtain ⟨h1, h2⟩ := h v (by simp)
      cases v <;> simp_all [Value.hasKind, scaleKind, Value.isDecOf]
    · exact e

/-- The values a measure without `DISTINCT` adds up are its argument on the
rows that count. -/
theorem inputs_eq {m : Measure} (hd : m.distinct = false) (rows : Relation) :
    m.inputs rows = (rows.filter (counts m)).map m.arg.eval := by
  have hk : m.kept rows = rows.filter (keeps m) := by
    unfold Measure.kept keeps; cases m.filter <;> simp <;> exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
  simp only [Measure.inputs, hd, Bool.false_eq_true, ↓reduceIte, hk, List.filter_map,
    List.filter_filter]
  congr 1
  exact List.filter_congr fun x _ => by simp [counts, Bool.and_comm]

theorem groupRows_filter (gs : List Expr) (rows : Relation) (k : Row) (p : Row → Bool) :
    (groupRows gs rows k).filter p = rows.filter fun r => groupKey gs r == k && p r := by
  simp [groupRows, List.filter_filter, Bool.and_comm]

theorem rowsIn_lift (gs : List Expr) (rows : Relation) (k : Row) :
    rowsIn gs k (ZSet.lift rows) = (groupRows gs rows k).length := by
  rw [rowsIn, lin_lift, sum_ind_one]; rfl

omit [Boxes.Ambient] in
theorem sum_one : ∀ vs : List Value, (vs.map fun _ => (1 : Int)).sum = vs.length
  | [] => rfl
  | _ :: vs => by rw [List.map_cons, List.sum_cons, sum_one vs, List.length_cons]; omega

/-- **A sound state gives the aggregate**: on a bag, the sums of a sound
state's features over a group finish to the measure of the group's rows. -/
theorem fin_eval {gs : List Expr} {m : Measure} {L : LinState} (hL : L.Sound m) {rows : Relation}
    (hg : L.Good m rows) (k : Row) :
    L.fin (L.feats.map fun f => featIn gs m f k (ZSet.lift rows)) = m.eval (groupRows gs rows k) := by
  rw [Measure.eval_eq hL.2.1, inputs_eq hL.1, groupRows_filter]
  have hf : ∀ f : Value → Int, featIn gs m f k (ZSet.lift rows) =
      (((rows.filter fun r => groupKey gs r == k && counts m r).map m.arg.eval).map f).sum := by
    intro f; rw [featIn, lin_lift, sum_ind, List.map_map]; rfl
  simp only [hf]
  refine hL.2.2 _ fun v hv => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hr
  have hc : counts m r = true := by simp only [Bool.and_eq_true] at h2; exact h2.2
  refine ⟨?_, hg r h1 hc⟩
  simp only [counts, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  exact hc.2

/-- `COUNT` and `SUM` finish from the number of their values and their sum. -/
theorem sumState_sound {m : Measure} (hm : Linear m) (sc : Option Nat) : (sumState m sc).Sound m := by
  refine ⟨hm.2, by rcases hm.1 with h | h <;> simp [h, AggFn.sorts], fun vs hvs => ?_⟩
  simp only [sumState, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [sum_one]
  rcases hm.1 with h | h
  · simp [finish, h, AggFn.apply]
  · rw [h]
    cases vs with
    | nil => simp [finish, h, AggFn.apply]
    | cons a l =>
      have hk : ∀ w ∈ a :: l, w.hasKind (scaleKind sc) = true ∧ w ≠ .null :=
        fun w hw => ⟨(hvs w hw).2 h, (hvs w hw).1⟩
      change _ = sumOf (a :: l)
      rw [sumOf_of_scale hk, ← intSum_eq]
      cases sc <;> simp [finish, h] <;> omega

/-- **The state gives the aggregate's row**, for `COUNT` and `SUM`, where a
`SUM`'s argument has the scale the plan's kinds give it (`ArgScale`, D29). -/
theorem finish_eval {gs : List Expr} {m : Measure} (hm : Linear m) {sc : Option Nat}
    {rows : Relation} (hsc : ArgScale sc m rows) (k : Row) :
    finish m sc (valuesIn gs m k (ZSet.lift rows)) (sumIn gs m k (ZSet.lift rows)) =
      m.eval (groupRows gs rows k) :=
  fin_eval (sumState_sound hm sc) hsc.good k

/-- On a Z-set with the weights of a bag, a group's output row from the
state is the aggregate's row. -/
theorem outRow_eq {gs : List Expr} {ms : List Measure} {st : Measure → LinState}
    (hst : ∀ m ∈ ms, (st m).Sound m) {rows : Relation} (hg : ∀ m ∈ ms, (st m).Good m rows)
    {z : ZSet} (hz : ∀ r, z.weight r = (ZSet.lift rows).weight r) (k : Row) :
    outRow gs ms st z k = k ++ ms.map (·.eval (groupRows gs rows k)) := by
  rw [outRow_congr hz, outRow]
  exact congrArg (k ++ ·) (List.map_congr_left fun m hm => fin_eval (hst m hm) (hg m hm) k)

theorem mem_keys_iff {gs : List Expr} {rows : Relation} {k : Row} :
    k ∈ dedup (rows.map (groupKey gs)) ↔ 0 < rowsIn gs k (ZSet.lift rows) := by
  rw [mem_dedup, rowsIn_lift, groupRows, Int.natCast_pos, List.length_pos_iff_exists_mem]
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]

/-! ## Aggregates -/

variable {gs : List Expr} {ms : List Measure}

/-- **The aggregate from the state**: on a Z-set `z` with the weights of the
bag `rows`, the aggregate of `rows` is the output rows of the groups whose
count is positive, listed once each in any order. -/
theorem aggregate_state (hg : gs ≠ []) {st : Measure → LinState}
    (hst : ∀ m ∈ ms, (st m).Sound m) {rows : Relation} (hgood : ∀ m ∈ ms, (st m).Good m rows)
    {z : ZSet} (hz : ∀ r, z.weight r = (ZSet.lift rows).weight r) {ks : List Row} (hnd : ks.Nodup)
    (hks : ∀ k, k ∈ ks ↔ 0 < rowsIn gs k z) :
    (aggregateEval gs ms rows).Perm (ks.map (outRow gs ms st z)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte]
  rw [show (fun k => k ++ ms.map (·.eval (groupRows gs rows k))) = outRow gs ms st z from
    funext fun k => (outRow_eq hst hgood hz k).symm]
  refine List.Perm.map _ ((List.perm_ext_iff_of_nodup (nodup_dedup _) hnd).mpr fun k => ?_)
  rw [mem_keys_iff, hks, rowsIn_congr hz]

/-- **Maintaining `COUNT` and `SUM` per group.** A batch changes the input
bag from `rows` to `rows'` by a change `Δ` (with the right weights), and
every row of `Δ` has a group key in `K`. Then the aggregate of `rows'` is
the old aggregate's rows of the groups outside `K`, and for the groups in
`K` that still have rows (`ks`), the output row of the old state plus the
state of `Δ`. -/
theorem aggregate_maintained (hg : gs ≠ []) {st : Measure → LinState}
    (hst : ∀ m ∈ ms, (st m).Sound m) {rows rows' : Relation}
    (hgood : ∀ m ∈ ms, (st m).Good m rows) (hgood' : ∀ m ∈ ms, (st m).Good m rows') {Δ : ZSet}
    (hΔ : ∀ r, (ZSet.lift rows ++ Δ).weight r = (ZSet.lift rows').weight r)
    {K : Row → Bool} (hK : ∀ x ∈ Δ, K (groupKey gs x.1) = true)
    {ks : List Row} (hnd : ks.Nodup)
    (hks : ∀ k, k ∈ ks ↔ K k = true ∧ 0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k Δ) :
    (aggregateEval gs ms rows').Perm
      ((aggregateEval gs ms rows).filter (fun o => !K (o.take gs.length)) ++
        ks.map fun k => k ++ ms.map fun m =>
          (st m).fin ((st m).feats.map fun f =>
            featIn gs m f k (ZSet.lift rows) + featIn gs m f k Δ)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  let ku := (dedup (rows.map (groupKey gs))).filter fun k => !K k
  -- Outside `K`, the change adds nothing to a group's state.
  have hzero : ∀ k, K k = false → ∀ g : Row → Int, (∀ r, groupKey gs r ≠ k → g r = 0) →
      ZSet.lin g Δ = 0 := fun k hk g hg' => lin_zero fun x hx => hg' x.1 fun he => by
    have := hK x hx; rw [he, hk] at this; exact Bool.false_ne_true this
  have hout : ∀ k, K k = false →
      outRow gs ms st (ZSet.lift rows ++ Δ) k = outRow gs ms st (ZSet.lift rows) k := by
    intro k hk
    simp only [outRow, featIn_append]
    refine congrArg (k ++ ·) (List.map_congr_left fun m _ => congrArg _
      (List.map_congr_left fun f _ => ?_))
    have h0 := hzero k hk (fun r => ind (groupKey gs r == k && counts m r) (f (m.arg.eval r)))
      (fun r hr => by simp [ind, hr])
    simp only [featIn] at h0 ⊢
    rw [h0, Int.add_zero]
  have hrows : ∀ k, K k = false → rowsIn gs k Δ = 0 := fun k hk =>
    hzero k hk _ fun r hr => by simp [ind, hr]
  -- The new aggregate, from the state of `old ++ Δ`, over the keys `ku ++ ks`.
  have hdisj : ∀ a ∈ ku, ∀ b ∈ ks, a ≠ b := fun a ha b hb he => by
    have h1 := (List.mem_filter.mp ha).2
    have h2 := ((hks b).mp hb).1
    rw [he, h2] at h1; simp at h1
  have hnd' : (ku ++ ks).Nodup :=
    List.nodup_append.mpr ⟨(nodup_dedup _).filter _, hnd, hdisj⟩
  have hmem : ∀ k, k ∈ ku ++ ks ↔ 0 < rowsIn gs k (ZSet.lift rows ++ Δ) := by
    intro k
    rw [List.mem_append, List.mem_filter, mem_keys_iff, hks, rowsIn_append]
    cases hk : K k
    · simp [hrows k hk]
    · simp
  have hnew := aggregate_state hg hst hgood' hΔ hnd' hmem
  refine hnew.trans (.of_eq ?_)
  rw [List.map_append]
  congr 1
  · -- The untouched groups keep their old rows.
    simp only [aggregateEval, hge, Bool.false_eq_true, ↓reduceIte, ku]
    rw [List.filter_map]
    have hf : (dedup (rows.map (groupKey gs))).filter
        ((fun o : Row => !K (o.take gs.length)) ∘
          fun k => k ++ ms.map (·.eval (groupRows gs rows k))) =
        (dedup (rows.map (groupKey gs))).filter fun k => !K k :=
      List.filter_congr fun k hk => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
        simp only [Function.comp_apply, List.take_left' (groupKey_length' gs r)]
    rw [hf]
    refine List.map_congr_left fun k hk => ?_
    have hk' := (List.mem_filter.mp hk).2
    rw [hout k (by simpa using hk'), outRow_eq hst hgood (fun _ => rfl)]
  · refine List.map_congr_left fun k _ => ?_
    simp only [outRow, featIn_append]
where
  groupKey_length' (gs : List Expr) (r : Row) : (groupKey gs r).length = gs.length := by
    simp [groupKey]

/-! ## `DISTINCT` -/

omit [Boxes.Ambient] in
theorem weight_lift_nonneg : ∀ (rows : Relation) (k : Row), 0 ≤ (ZSet.lift rows).weight k
  | [], _ => by simp [ZSet.lift, WSet.weight_nil]
  | a :: rows, k => by
      have := weight_lift_nonneg rows k
      simp only [ZSet.lift, List.map_cons] at this ⊢
      rw [WSet.weight_cons]
      split <;> omega

omit [Boxes.Ambient] in
theorem weight_lift_pos {rows : Relation} {k : Row} :
    0 < (ZSet.lift rows).weight k ↔ k ∈ rows := by
  induction rows with
  | nil => simp [ZSet.lift, WSet.weight_nil]
  | cons a rows ih =>
      have hn := weight_lift_nonneg rows k
      simp only [ZSet.lift, List.map_cons] at ih hn ⊢
      rw [WSet.weight_cons, List.mem_cons]
      by_cases h : a = k
      · subst h; simp only [↓reduceIte, true_or, iff_true]; omega
      · simp only [h, ↓reduceIte]
        constructor
        · intro h'; exact Or.inr (ih.mp (by omega))
        · intro h'; have := ih.mpr (h'.resolve_left (Ne.symm h)); omega

omit [Boxes.Ambient] in
/-- **`DISTINCT` from a count per row**: on a Z-set `z` with the weights of
the bag `rows`, `DISTINCT` of `rows` is the rows whose count is positive. -/
theorem distinct_state {rows : Relation} {z : ZSet}
    (hz : ∀ r, z.weight r = (ZSet.lift rows).weight r) {ks : List Row} (hnd : ks.Nodup)
    (hks : ∀ k, k ∈ ks ↔ 0 < z.weight k) : (dedup rows).Perm ks :=
  (List.perm_ext_iff_of_nodup (nodup_dedup _) hnd).mpr fun k => by
    rw [mem_dedup, hks, hz, weight_lift_pos]

omit [Boxes.Ambient] in
/-- **Maintaining `DISTINCT`.** A batch changes the input bag from `rows`
to `rows'` by `Δ` (with the right weights), and every row of `Δ` is in `K`.
Then `DISTINCT` of `rows'` is the old output's rows outside `K` and the rows
in `K` whose old count plus the change's is positive: a row is emitted when
its count leaves 0 and retracted when it returns to 0. -/
theorem distinct_maintained {rows rows' : Relation} {Δ : ZSet}
    (hΔ : ∀ r, (ZSet.lift rows ++ Δ).weight r = (ZSet.lift rows').weight r)
    {K : Row → Bool} (hK : ∀ x ∈ Δ, K x.1 = true) {ks : List Row} (hnd : ks.Nodup)
    (hks : ∀ k, k ∈ ks ↔ K k = true ∧ 0 < (ZSet.lift rows).weight k + Δ.weight k) :
    (dedup rows').Perm ((dedup rows).filter (fun r => !K r) ++ ks) := by
  have hzero : ∀ k, K k = false → Δ.weight k = 0 := fun k hk => by
    rw [ZSet.weight_eq_lin]
    exact lin_zero fun x hx => by
      have := hK x hx
      by_cases he : x.1 = k
      · rw [he, hk] at this; exact absurd this Bool.false_ne_true
      · simp [he]
  have hdisj : ∀ a ∈ (dedup rows).filter (fun r => !K r), ∀ b ∈ ks, a ≠ b := fun a ha b hb he => by
    have h1 := (List.mem_filter.mp ha).2
    rw [he, ((hks b).mp hb).1] at h1; simp at h1
  refine (List.perm_ext_iff_of_nodup (nodup_dedup _)
    (List.nodup_append.mpr ⟨(nodup_dedup _).filter _, hnd, hdisj⟩)).mpr fun k => ?_
  rw [mem_dedup, ← weight_lift_pos, ← hΔ, WSet.weight_append, List.mem_append, List.mem_filter,
    mem_dedup, ← weight_lift_pos, hks]
  cases hk : K k
  · simp [hzero k hk]
  · simp

end LinearAgg
end Substrait
