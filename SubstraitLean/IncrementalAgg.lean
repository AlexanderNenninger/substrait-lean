import SubstraitLean.TouchedGroups
import SubstraitLean.TableFormat
import Sverify.Core.Kinds
import Sverify.Core.Allowed

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
* `aggregate_state`: the output rows of the groups with a positive count,
  the canonical key of each class of keys, are an aggregate the reference
  allows (`aggAllowed`).
* `aggregate_maintained`: after a batch, the old rows of the groups the
  batch does not touch, and the rows of the touched groups from the old
  state plus the state of the change, are an aggregate the reference
  allows. This is what `sverify._linear` computes.
* `distinct_state`, `distinct_maintained`: the same for `DISTINCT`.

Groups are classes of keys equal up to canonical codes (`-0.0` and `0.0`,
D31), as `groupRows` makes them, and a group's row carries the class's
canonical key, as Spark's and DuckDB's `GROUP BY` do: so the theorems
conclude membership in what the reference allows.

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

/-- The weight of group `k`'s rows: the rows whose key is `k` up to
canonical codes (`-0.0` is `0.0`, D31), as `groupRows` groups them. -/
def rowsIn (gs : List Expr) (k : Row) (z : ZSet) : Int :=
  ZSet.lin (fun r => ind ((groupKey gs r).canon == k.canon) 1) z

/-- The weighted sum of a feature `f` of the values measure `m` adds up in
group `k`. -/
def featIn (gs : List Expr) (m : Measure) (f : Value → Int) (k : Row) (z : ZSet) : Int :=
  ZSet.lin (fun r => ind ((groupKey gs r).canon == k.canon && counts m r) (f (m.arg.eval r))) z

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
    (groupRows gs rows k).filter p = rows.filter fun r => (groupKey gs r).canon == k.canon && p r := by
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
      (((rows.filter fun r => (groupKey gs r).canon == k.canon && counts m r).map m.arg.eval).map f).sum := by
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

/-- A group has rows exactly when a row's key is in its class. -/
theorem rowsIn_lift_pos {gs : List Expr} {rows : Relation} {k : Row} :
    0 < rowsIn gs k (ZSet.lift rows) ↔ ∃ r ∈ rows, (groupKey gs r).canon = k.canon := by
  rw [rowsIn_lift, groupRows, Int.natCast_pos, List.length_pos_iff_exists_mem]
  simp only [List.mem_filter, beq_iff_eq]

/-- A bag's weight of a row is the row's count. -/
theorem weight_lift_count (r : Row) : ∀ rows : Relation, (ZSet.lift rows).weight r = rows.count r
  | [] => by simp [ZSet.lift, WSet.weight_nil]
  | a :: rows => by
    have ih := weight_lift_count r rows
    simp only [ZSet.lift, List.map_cons] at ih ⊢
    rw [WSet.weight_cons, ih, List.count_cons]
    by_cases h : a = r
    · subst h; simp; omega
    · simp [h]

/-- A measure allows the same values on a permutation of its rows. -/
theorem Measure.Allowed.perm {m : Measure} {rows rows' : Relation} {v : Value}
    (h : m.Allowed rows v) (hp : rows.Perm rows') : m.Allowed rows' v :=
  let ⟨s, hs, ho, hv⟩ := h; ⟨s, hs.trans hp, ho, hv⟩

/-! ## Aggregates

The state keeps one row per class of keys, and a group's output row carries
the class's canonical key, as Spark's and DuckDB's `GROUP BY` do: an output
`aggAllowed` allows (D31). So the theorems conclude that the maintained rows
are an output the reference allows. -/

variable {gs : List Expr} {ms : List Measure}

/-- **The aggregate from the state**: on a Z-set `z` with the weights of the
bag `rows`, the output rows of keys `ks`, one key for each class of keys
whose count is positive, are an aggregate of `rows` the reference allows. -/
theorem aggregate_state (hg : gs ≠ []) {st : Measure → LinState}
    (hst : ∀ m ∈ ms, (st m).Sound m) {rows : Relation} (hgood : ∀ m ∈ ms, (st m).Good m rows)
    {z : ZSet} (hz : ∀ r, z.weight r = (ZSet.lift rows).weight r) {ks : List Row}
    (hks : ks.Pairwise fun a b => a.canon ≠ b.canon) (hkc : ∀ k ∈ ks, k.canon = k) (hpos : ∀ k ∈ ks, 0 < rowsIn gs k z)
    (hcov : ∀ k, 0 < rowsIn gs k z → ∃ k' ∈ ks, k'.canon = k.canon) :
    aggAllowed gs ms rows (ks.map (outRow gs ms st z)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  unfold aggAllowed
  simp only [hge, Bool.false_eq_true, ↓reduceIte]
  refine ⟨ks, ⟨hks, fun k hk => ?_, fun x hx => ?_⟩, forall₂_map_self ks fun k _ =>
    ⟨_, outRow_eq hst hgood hz k, forall₂_map_self ms fun m _ => Measure.eval_allowed m _⟩⟩
  · have := hpos k hk
    rw [rowsIn_congr hz] at this
    obtain ⟨r, hr, he⟩ := rowsIn_lift_pos.mp this
    exact ⟨_, List.mem_map_of_mem hr, he.symm, .inr ((hkc k hk).symm.trans he.symm)⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    refine hcov _ ?_
    rw [rowsIn_congr hz]
    exact rowsIn_lift_pos.mpr ⟨r, hr, rfl⟩

/-- A group's rows on rows filtered by a predicate of the key that holds on
the group's class are the group's rows. -/
theorem groupRows_filter_key {p : Row → Bool} (hp : RespectsCanon p) {k : Row} (hk : p k = true)
    (rows : Relation) : groupRows gs (rows.filter fun r => p (groupKey gs r)) k = groupRows gs rows k := by
  simp only [groupRows, List.filter_filter]
  exact List.filter_congr fun r _ => by
    by_cases he : ((groupKey gs r).canon == k.canon) = true
    · rw [hp _ _ (by simpa using he), hk]; simp [he]
    · simp [he]

/-- The keys of an output the reference allows have the keys' length. -/
theorem aggAllowed_key_length {ks : List Row} {rows : Relation}
    (h : IsReps Row.canon (rows.map (groupKey gs)) ks) {k : Row} (hk : k ∈ ks) :
    k.length = gs.length := by
  obtain ⟨_, hy, he⟩ := h.class_mem hk
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy
  rw [Row.length_of_canon he]; simp [groupKey]

/-- **An allowed aggregate restricted to some classes of keys** is an allowed
aggregate of those classes' rows. -/
theorem aggAllowed_filter_key (hg : gs ≠ []) {p : Row → Bool} (hp : RespectsCanon p)
    {rows out : Relation} (h : aggAllowed gs ms rows out) :
    aggAllowed gs ms (rows.filter fun r => p (groupKey gs r))
      (out.filter fun o => p (o.take gs.length)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  unfold aggAllowed at h ⊢
  simp only [hge, Bool.false_eq_true, ↓reduceIte] at h ⊢
  obtain ⟨ks, hr, hf⟩ := h
  have hpk : ∀ k ∈ ks.filter p, p k = true := fun k hk => (List.mem_filter.mp hk).2
  refine ⟨ks.filter p, ⟨hr.1.sublist List.filter_sublist, fun k hk => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨_, hy, he, ho⟩ := hr.2.1 _ (List.mem_filter.mp hk).1
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hy
    have : p (groupKey gs r) = true := by rw [← hp _ _ he]; exact hpk k hk
    exact ⟨_, List.mem_map_of_mem (List.mem_filter.mpr ⟨hr', this⟩), he, ho⟩
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hx
    have hpr := (List.mem_filter.mp hr').2
    obtain ⟨y, hy, he⟩ := hr.2.2 _ (List.mem_map_of_mem (List.mem_filter.mp hr').1)
    have : p y = true := by rw [hp _ _ he]; exact hpr
    exact ⟨y, List.mem_filter.mpr ⟨hy, this⟩, he⟩
  · have hf1 := hf.imp_mem fun k hk o h => And.intro h (aggAllowed_key_length hr hk)
    have hf2 := hf1.filter (p := p) (p' := fun o => p (o.take gs.length))
      fun k o ⟨⟨vs, ho, _⟩, hl⟩ => by rw [ho, ← hl, List.take_left]
    exact hf2.imp_mem fun k hk o ⟨⟨vs, ho, hv⟩, _⟩ =>
      ⟨vs, ho, by rwa [groupRows_filter_key hp (hpk k hk)]⟩

/-- **Allowed aggregates of two sets of classes of keys** make an allowed
aggregate of their union. -/
theorem aggAllowed_append (hg : gs ≠ []) {p : Row → Bool} (hp : RespectsCanon p)
    {rows A B : Relation} (hA : aggAllowed gs ms (rows.filter fun r => p (groupKey gs r)) A)
    (hB : aggAllowed gs ms (rows.filter fun r => !p (groupKey gs r)) B) :
    aggAllowed gs ms rows (A ++ B) := by
  have hge : gs.isEmpty = false := by simpa using hg
  have hnp : RespectsCanon fun k => !p k := fun k k' he => by simp only [hp k k' he]
  unfold aggAllowed at hA hB ⊢
  simp only [hge, Bool.false_eq_true, ↓reduceIte] at hA hB ⊢
  obtain ⟨ka, hra, hfa⟩ := hA
  obtain ⟨kb, hrb, hfb⟩ := hB
  -- A key's class decides the predicate.
  have side : ∀ {q : Row → Bool}, RespectsCanon q → ∀ {ks : List Row},
      IsReps Row.canon ((rows.filter fun r => q (groupKey gs r)).map (groupKey gs)) ks →
        ∀ k ∈ ks, q k = true ∧
          ∃ y ∈ rows.map (groupKey gs), k.canon = y.canon ∧ (k = y ∨ k = y.canon) := by
    intro q hq ks h k hk
    obtain ⟨_, hy, he, ho⟩ := h.2.1 k hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    exact ⟨by rw [hq _ _ he]; exact (List.mem_filter.mp hr).2,
      _, List.mem_map_of_mem (List.mem_filter.mp hr).1, he, ho⟩
  refine ⟨ka ++ kb, ⟨?_, fun x hx => ?_, fun x hx => ?_⟩, Forall2.append ?_ ?_⟩
  · refine List.pairwise_append.mpr ⟨hra.1, hrb.1, fun a ha b hb he => ?_⟩
    have h1 := (side hp hra a ha).1
    have h2 := (side hnp hrb b hb).1
    rw [hp a b he] at h1; rw [h1] at h2; exact Bool.false_ne_true h2
  · rcases List.mem_append.mp hx with hx | hx
    · exact (side hp hra x hx).2
    · exact (side hnp hrb x hx).2
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    cases hpr : p (groupKey gs r)
    · obtain ⟨y, hy, he⟩ := hrb.2.2 _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by simp [hpr]⟩))
      exact ⟨y, List.mem_append_right _ hy, he⟩
    · obtain ⟨y, hy, he⟩ := hra.2.2 _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, hpr⟩))
      exact ⟨y, List.mem_append_left _ hy, he⟩
  · exact hfa.imp_mem fun k hk o ⟨vs, ho, hv⟩ =>
      ⟨vs, ho, by rwa [groupRows_filter_key hp (side hp hra k hk).1] at hv⟩
  · exact hfb.imp_mem fun k hk o ⟨vs, ho, hv⟩ =>
      ⟨vs, ho, by rwa [groupRows_filter_key hnp (side hnp hrb k hk).1] at hv⟩

/-- **Maintaining `COUNT` and `SUM` per group.** A batch changes the input
bag from `rows` to `rows'` by a change `Δ` (with the right weights), and
every row of `Δ` has a group key in `K`, a set of classes of keys. Then the
rows of an old output `old` the reference allows whose groups are outside
`K`, and for one key of each class in `K` that still has rows (`ks`), the
output row of the old state plus the state of `Δ`, are an output the
reference allows on `rows'`. -/
theorem aggregate_maintained (hg : gs ≠ []) {st : Measure → LinState}
    (hst : ∀ m ∈ ms, (st m).Sound m) {rows rows' : Relation}
    (hgood' : ∀ m ∈ ms, (st m).Good m rows') {Δ : ZSet}
    (hΔ : ∀ r, (ZSet.lift rows ++ Δ).weight r = (ZSet.lift rows').weight r)
    {K : Row → Bool} (hKc : RespectsCanon K)
    (hK : ∀ x ∈ Δ, K (groupKey gs x.1) = true) {old : Relation} (hold : aggAllowed gs ms rows old)
    {ks : List Row} (hks : ks.Pairwise fun a b => a.canon ≠ b.canon) (hkc : ∀ k ∈ ks, k.canon = k)
    (hpos : ∀ k ∈ ks, K k = true ∧ 0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k Δ)
    (hcov : ∀ k, K k = true → 0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k Δ →
      ∃ k' ∈ ks, k'.canon = k.canon) :
    aggAllowed gs ms rows'
      (old.filter (fun o => !K (o.take gs.length)) ++
        ks.map fun k => k ++ ms.map fun m =>
          (st m).fin ((st m).feats.map fun f =>
            featIn gs m f k (ZSet.lift rows) + featIn gs m f k Δ)) := by
  have hge : gs.isEmpty = false := by simpa using hg
  unfold aggAllowed at hold ⊢
  simp only [hge, Bool.false_eq_true, ↓reduceIte] at hold ⊢
  obtain ⟨ks0, hr0, hf0⟩ := hold
  -- `Δ` holds no row of a class outside `K`, so those rows keep their counts.
  have hw : ∀ r, K (groupKey gs r) = false → (ZSet.lift rows').weight r = (ZSet.lift rows).weight r := by
    intro r hr
    have h0 : Δ.weight r = 0 := by
      rw [ZSet.weight_eq_lin]
      exact lin_zero fun x hx => by
        have := hK x hx
        by_cases he : x.1 = r
        · rw [he, hr] at this; exact absurd this Bool.false_ne_true
        · simp [he]
    rw [← hΔ, WSet.weight_append, h0, Int.add_zero]
  have hmem : ∀ r, K (groupKey gs r) = false → (r ∈ rows' ↔ r ∈ rows) := fun r hr => by
    have := hw r hr
    rw [weight_lift_count, weight_lift_count] at this
    rw [← List.count_pos_iff, ← List.count_pos_iff]; omega
  have hperm : ∀ k, K k = false → (groupRows gs rows k).Perm (groupRows gs rows' k) := by
    intro k hk
    rw [List.perm_iff_count]; intro r
    unfold groupRows
    by_cases hp : ((groupKey gs r).canon == k.canon) = true
    · have hKr : K (groupKey gs r) = false := by rw [hKc _ k (by simpa using hp)]; exact hk
      rw [List.count_filter (p := fun row => (groupKey gs row).canon == k.canon) hp,
        List.count_filter (p := fun row => (groupKey gs row).canon == k.canon) hp]
      have := hw r hKr
      rw [weight_lift_count, weight_lift_count] at this
      exact_mod_cast this.symm
    · have h0 : ∀ l : Relation, (l.filter fun row => (groupKey gs row).canon == k.canon).count r = 0 :=
        fun l => List.count_eq_zero.mpr fun h => hp (List.mem_filter.mp h).2
      rw [h0, h0]
  have hnew : ∀ k, 0 < rowsIn gs k (ZSet.lift rows) + rowsIn gs k Δ ↔
      ∃ r ∈ rows', (groupKey gs r).canon = k.canon := fun k => by
    rw [← rowsIn_append, rowsIn_congr hΔ, rowsIn_lift_pos]
  let ku := ks0.filter fun k => !K k
  have hku : ∀ k ∈ ku, K k = false := fun k hk => by simpa using (List.mem_filter.mp hk).2
  refine ⟨ku ++ ks, ⟨?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · -- One key per class: a class outside `K` and one in it differ.
    refine List.pairwise_append.mpr ⟨hr0.1.sublist List.filter_sublist, hks, fun a ha b hb he => ?_⟩
    have := hKc a b he
    rw [hku a ha, (hpos b hb).1] at this; exact Bool.false_ne_true this
  · -- Each key's class has rows in `rows'`.
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨_, hy, he, ho⟩ := hr0.2.1 _ (List.mem_filter.mp hx).1
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
      have hKr : K (groupKey gs r) = false := by rw [← hKc _ _ he]; exact hku x hx
      exact ⟨_, List.mem_map_of_mem ((hmem r hKr).mpr hr), he, ho⟩
    · obtain ⟨r, hr, he⟩ := (hnew x).mp (hpos x hx).2
      exact ⟨_, List.mem_map_of_mem hr, he.symm, .inr ((hkc x hx).symm.trans he.symm)⟩
  · -- Each class of `rows'` has a key.
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    cases hKr : K (groupKey gs r)
    · obtain ⟨y, hy, he⟩ := hr0.2.2 _ (List.mem_map_of_mem ((hmem r hKr).mp hr))
      have hKy : K y = false := by rw [hKc _ _ he]; exact hKr
      exact ⟨y, List.mem_append_left _ (List.mem_filter.mpr ⟨hy, by simp [hKy]⟩), he⟩
    · obtain ⟨k', hk', he⟩ := hcov _ hKr ((hnew _).mpr ⟨r, hr, rfl⟩)
      exact ⟨k', List.mem_append_right _ hk', he⟩
  · refine Forall2.append ?_ (forall₂_map_self ks fun k _ => ⟨_, rfl, ?_⟩)
    · -- The untouched groups keep their old rows, allowed on `rows'` too.
      have hlen : ∀ k ∈ ks0, k.length = gs.length := fun k hk => by
        obtain ⟨_, hy, he⟩ := hr0.class_mem hk
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp hy
        rw [Row.length_of_canon he]; simp [groupKey]
      have hf1 := hf0.imp_mem fun k hk o h => And.intro h (hlen k hk)
      have hf2 := hf1.filter (p := fun k => !K k) (p' := fun o => !K (o.take gs.length))
        fun k o ⟨⟨vs, ho, _⟩, hl⟩ => by rw [ho, ← hl, List.take_left]
      refine hf2.imp_mem fun k hk o ⟨⟨vs, ho, hv⟩, _⟩ => ⟨vs, ho, hv.imp fun m v h => Measure.Allowed.perm h (hperm k ?_)⟩
      exact hku k hk
    · -- The touched groups' rows, from the new state.
      have e : (ms.map fun m => (st m).fin ((st m).feats.map fun f =>
          featIn gs m f k (ZSet.lift rows) + featIn gs m f k Δ)) =
          ms.map (·.eval (groupRows gs rows' k)) := by
        have := outRow_eq (gs := gs) hst hgood' (z := ZSet.lift rows ++ Δ) hΔ k
        simpa only [outRow, featIn_append, List.append_cancel_left_eq] using this
      rw [e]
      exact forall₂_map_self ms fun m _ => Measure.eval_allowed m _

/-! ## `DISTINCT`

The state keeps a count per class of rows equal up to canonical codes, and
the output the canonical row of each class with a positive count: what
`Rel.Allowed` allows for `DISTINCT` (`IsReps`, D31). -/

/-- The weight of the rows in `k`'s class. -/
def classIn (k : Row) (z : ZSet) : Int := ZSet.lin (fun r => ind (r.canon == k.canon) 1) z

theorem classIn_append (k : Row) (a b : ZSet) : classIn k (a ++ b) = classIn k a + classIn k b :=
  ZSet.lin_append _ _ _

theorem classIn_congr {z z' : ZSet} (h : ∀ r, z.weight r = z'.weight r) (k : Row) :
    classIn k z = classIn k z' := ZSet.lin_congr _ h

/-- A class has rows exactly when one of the bag's rows is in it. -/
theorem classIn_lift_pos {rows : Relation} {k : Row} :
    0 < classIn k (ZSet.lift rows) ↔ ∃ r ∈ rows, r.canon = k.canon := by
  rw [classIn, lin_lift, sum_ind_one, Int.natCast_pos, List.length_pos_iff_exists_mem]
  simp only [List.mem_filter, beq_iff_eq]

/-- **`DISTINCT` from a count per class**: on a Z-set `z` with the weights of
the bag `rows`, one row of each class whose count is positive is a
`DISTINCT` of `rows` the reference allows. -/
theorem distinct_state {rows : Relation} {z : ZSet}
    (hz : ∀ r, z.weight r = (ZSet.lift rows).weight r) {ks : List Row}
    (hks : ks.Pairwise fun a b => a.canon ≠ b.canon) (hkc : ∀ k ∈ ks, k.canon = k) (hpos : ∀ k ∈ ks, 0 < classIn k z)
    (hcov : ∀ k, 0 < classIn k z → ∃ k' ∈ ks, k'.canon = k.canon) : IsReps Row.canon rows ks := by
  refine ⟨hks, fun k hk => ?_, fun x hx => hcov x ?_⟩
  · have := hpos k hk
    rw [classIn_congr hz] at this
    obtain ⟨r, hr, he⟩ := classIn_lift_pos.mp this
    exact ⟨r, hr, he.symm, .inr ((hkc k hk).symm.trans he.symm)⟩
  · rw [classIn_congr hz]; exact classIn_lift_pos.mpr ⟨x, hx, rfl⟩

omit [Boxes.Ambient] in
/-- **Maintaining `DISTINCT`.** A batch changes the input bag from `rows`
to `rows'` by `Δ` (with the right weights), and every row of `Δ` is in `K`,
a set of classes. Then the rows outside `K` of an old output `old` the
reference allows, and one row of each class in `K` whose old count plus the
change's is positive, are a `DISTINCT` of `rows'` the reference allows: a
class is emitted when its count leaves 0 and retracted when it returns to 0. -/
theorem distinct_maintained {rows rows' : Relation} {Δ : ZSet}
    (hΔ : ∀ r, (ZSet.lift rows ++ Δ).weight r = (ZSet.lift rows').weight r)
    {K : Row → Bool} (hKc : RespectsCanon K)
    (hK : ∀ x ∈ Δ, K x.1 = true) {old : Relation} (hold : IsReps Row.canon rows old)
    {ks : List Row} (hks : ks.Pairwise fun a b => a.canon ≠ b.canon) (hkc : ∀ k ∈ ks, k.canon = k)
    (hpos : ∀ k ∈ ks, K k = true ∧ 0 < classIn k (ZSet.lift rows) + classIn k Δ)
    (hcov : ∀ k, K k = true → 0 < classIn k (ZSet.lift rows) + classIn k Δ →
      ∃ k' ∈ ks, k'.canon = k.canon) :
    IsReps Row.canon rows' (old.filter (fun r => !K r) ++ ks) := by
  have hzero : ∀ r, K r = false → Δ.weight r = 0 := fun r hr => by
    rw [ZSet.weight_eq_lin]
    exact lin_zero fun x hx => by
      have := hK x hx
      by_cases he : x.1 = r
      · rw [he, hr] at this; exact absurd this Bool.false_ne_true
      · simp [he]
  have hmem : ∀ r, K r = false → (r ∈ rows' ↔ r ∈ rows) := fun r hr => by
    have := hΔ r
    rw [WSet.weight_append, hzero r hr, Int.add_zero, weight_lift_count, weight_lift_count] at this
    rw [← List.count_pos_iff, ← List.count_pos_iff]; omega
  have hnew : ∀ k, 0 < classIn k (ZSet.lift rows) + classIn k Δ ↔ ∃ r ∈ rows', r.canon = k.canon :=
    fun k => by rw [← classIn_append, classIn_congr hΔ, classIn_lift_pos]
  have hku : ∀ k ∈ old.filter (fun r => !K r), K k = false := fun k hk => by
    simpa using (List.mem_filter.mp hk).2
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · refine List.pairwise_append.mpr ⟨hold.1.sublist List.filter_sublist, hks, fun a ha b hb he => ?_⟩
    have := hKc a b he
    rw [hku a ha, (hpos b hb).1] at this; exact Bool.false_ne_true this
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, he, ho⟩ := hold.2.1 x (List.mem_filter.mp hx).1
      have hKy : K y = false := by rw [← hKc _ _ he]; exact hku x hx
      exact ⟨y, (hmem y hKy).mpr hy, he, ho⟩
    · obtain ⟨r, hr, he⟩ := (hnew x).mp (hpos x hx).2
      exact ⟨r, hr, he.symm, .inr ((hkc x hx).symm.trans he.symm)⟩
  · cases hKx : K x
    · obtain ⟨y, hy, he⟩ := hold.2.2 x ((hmem x hKx).mp hx)
      have hKy : K y = false := by rw [hKc _ _ he]; exact hKx
      exact ⟨y, List.mem_append_left _ (List.mem_filter.mpr ⟨hy, by simp [hKy]⟩), he⟩
    · obtain ⟨k', hk', he⟩ := hcov x hKx ((hnew x).mpr ⟨x, hx, rfl⟩)
      exact ⟨k', List.mem_append_right _ hk', he⟩

end LinearAgg
end Substrait
