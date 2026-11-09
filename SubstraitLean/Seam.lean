import Sverify.Core.Ties
import Sverify.Analysis.AllowedAnalysis

/-!
# The ordered seam (#928)

The reference's core is unordered: a relation is a multiset of rows. Order
is an effect on top of it. `Lin keys R` is the set of sorted enumerations of
`R` (every list of `R`'s rows sorted by `keys`, ties in any order), and an
order-sensitive operator `op` reads one of them, so its meaning is
`Sem op keys R`, the set of `op L` over `L ∈ Lin keys R`. `LinBy` and `SemBy`
are the same over a comparison of rows, the form a measure's or a window's
own order takes.

* `Rel.orderAllowed_orderBy`, `Rel.orderAllowed_fetch_orderBy`,
  `Rel.orderAllowed_window`, `Measure.orderAllowed_iff_semBy`:
  `Rel.OrderAllowed`'s order-sensitive cases are `Lin` and `Sem`.
* `Sem.eq_iff_of_permInv`, `SemBy.eq_iff_of_permInv`: **the lifting
  lemma**. An operator that factors through the multiset has one meaning,
  its value on the multiset, so every theorem about the unordered core holds
  for it unchanged. `Measure.orderAllowed_eq` is the case of an order-free
  measure, `Measure.allowed_eq` for `Measure.OrderAllowed`.
* `Rel.Bags`: the multisets a plan may give, `fromList` (forgetting the
  order) of each result. An ordered result below an unordered operator (a
  `FETCH` without a total `ORDER BY` under a join) makes this a set of
  multisets, with more than one member (`Rel.bags_fetch_two`). The unordered
  operators act on it pointwise (`Rel.bags_filter`, `Rel.bags_unionAll`,
  …), an `ORDER BY` leaves it as it is (`Rel.bags_orderBy`), and a plan
  without choices has one member, `Rel.eval`'s rows (`Rel.bags_iff_perm_eval`).
  So `refresh`, which commits a result once, refuses a plan whose bags are
  not determined.

On today's carrier a multiset is a `List Row` up to `List.Perm`; EPIC2 (#905)
makes it `KRel ℕ`.
-/

namespace Substrait

/-! ## Enumerations and order-sensitive operators -/

/-- The enumerations of `R` sorted by `le`: lists of `R`'s rows, each as
often as in `R`, with each row `le` every later one. -/
def LinBy (le : Row → Row → Bool) (R L : Relation) : Prop :=
  L.Perm R ∧ L.Pairwise (le · · = true)

/-- **The sorted enumerations of `R` under `keys`**: lists of `R`'s rows in
an order `ORDER BY keys` allows, ties and a clustered key's groups in any
order (`SortAllowed`). -/
def Lin (keys : List SortKey) (R L : Relation) : Prop :=
  L.Perm R ∧ SortAllowed keys L

/-- What an operator reading one enumeration of `R` under `le` may give. -/
def SemBy {α : Type} (op : Relation → α) (le : Row → Row → Bool) (R : Relation) (v : α) :
    Prop :=
  ∃ L, LinBy le R L ∧ v = op L

/-- **What an order-sensitive operator may give**: `op` of any enumeration
of `R` that `keys` allows. -/
def Sem {α : Type} (op : Relation → α) (keys : List SortKey) (R : Relation) (v : α) : Prop :=
  ∃ L, Lin keys R L ∧ v = op L

theorem LinBy.mergeSort {le : Row → Row → Bool} (h : TotalPre le) (R : Relation) :
    LinBy le R (R.mergeSort le) :=
  ⟨List.mergeSort_perm _ _, List.pairwise_mergeSort h.trans h.total R⟩

theorem LinBy.lin {keys : List SortKey} {R L : Relation} (h : LinBy (sortLe keys) R L) :
    Lin keys R L :=
  ⟨h.1, .of_sorted h.2⟩

/-- `Rel.eval`'s stable sort is one enumeration. -/
theorem Lin.mergeSort (keys : List SortKey) (R : Relation) :
    Lin keys R (R.mergeSort (sortLe keys)) :=
  (LinBy.mergeSort (sortLe_totalPre keys) R).lin

/-- Without keys, every enumeration: `R` in any order. -/
theorem lin_nil {R L : Relation} : Lin [] R L ↔ L.Perm R :=
  ⟨And.left, fun h => ⟨h, Value.le, Value.le_validCmp, List.pairwise_of_forall fun _ _ => rfl⟩⟩

theorem SemBy.mergeSort {α : Type} (op : Relation → α) {le : Row → Row → Bool} (h : TotalPre le)
    (R : Relation) : SemBy op le R (op (R.mergeSort le)) :=
  ⟨_, LinBy.mergeSort h R, rfl⟩

theorem Sem.mergeSort {α : Type} (op : Relation → α) (keys : List SortKey) (R : Relation) :
    Sem op keys R (op (R.mergeSort (sortLe keys))) :=
  ⟨_, Lin.mergeSort keys R, rfl⟩

/-! ## The lifting lemma -/

/-- An operator that factors through the multiset: it gives the same value
for any order of the same rows. -/
def PermInv {α : Type} (op : Relation → α) : Prop :=
  ∀ {L L' : Relation}, L.Perm L' → op L = op L'

/-- **The lifting lemma**: an operator that factors through the multiset has
one meaning over every enumeration, its value on `R`. -/
theorem Sem.eq_iff_of_permInv {α : Type} {op : Relation → α} (hop : PermInv op)
    {keys : List SortKey} {R : Relation} {v : α} : Sem op keys R v ↔ v = op R :=
  ⟨fun ⟨_, ⟨hp, _⟩, hv⟩ => hv.trans (hop hp),
    fun h => ⟨_, Lin.mergeSort keys R, h.trans (hop (List.mergeSort_perm _ _)).symm⟩⟩

theorem SemBy.eq_iff_of_permInv {α : Type} {op : Relation → α} (hop : PermInv op)
    {le : Row → Row → Bool} (hle : TotalPre le) {R : Relation} {v : α} :
    SemBy op le R v ↔ v = op R :=
  ⟨fun ⟨_, ⟨hp, _⟩, hv⟩ => hv.trans (hop hp),
    fun h => ⟨_, LinBy.mergeSort hle R, h.trans (hop (List.mergeSort_perm _ _)).symm⟩⟩

/-! ## Measures -/

/-- The value a measure gives over one enumeration of its group's rows: its
aggregate of the enumeration where it sorts, of the rows as they come
otherwise. -/
def Measure.op (m : Measure) (rows : Relation) (s : Relation) : Value :=
  if m.fn.sorts then m.eval s else m.eval rows

/-- **`Measure.OrderAllowed` is `SemBy`** over the measure's own order, for a
measure other than `MIN` and `MAX` (whose member of a class is open, D31). -/
theorem Measure.orderAllowed_iff_semBy (m : Measure) (hmin : m.fn ≠ .min) (hmax : m.fn ≠ .max)
    (rows : Relation) (v : Value) :
    m.OrderAllowed rows v ↔ SemBy (m.op rows) (sortLe m.sort) rows v := by
  have key : ∀ s, (if m.fn.sorts then v = m.eval s else m.fn.Picks (m.inputs rows) v) ↔
      v = m.op rows s := fun s => by
    unfold Measure.op
    split
    · exact Iff.rfl
    · next hs =>
      rw [Measure.eval_eq (by simpa using hs)]
      exact ⟨fun h => by rcases h with h | ⟨hf, -⟩; · exact h
                         rcases hf with hf | hf <;> contradiction, Or.inl⟩
  exact ⟨fun ⟨s, hp, hs, hv⟩ => ⟨s, ⟨hp, hs⟩, (key s).mp hv⟩,
    fun ⟨s, ⟨hp, hs⟩, hv⟩ => ⟨s, hp, hs, (key s).mpr hv⟩⟩

theorem Measure.op_permInv {m : Measure} (hm : m.orderFree = true) (rows : Relation) :
    PermInv (m.op rows) := fun h => by
  unfold Measure.op; split
  · exact Measure.eval_perm hm h
  · rfl

/-- An order-free measure has one value over every order of its rows: the
lifting lemma for measures, `Measure.allowed_eq` for `Measure.OrderAllowed`. -/
theorem Measure.orderAllowed_eq {m : Measure} (hm : m.orderFree = true) (hmin : m.fn ≠ .min)
    (hmax : m.fn ≠ .max) {rows : Relation} {v : Value} :
    m.OrderAllowed rows v ↔ v = m.eval rows := by
  rw [Measure.orderAllowed_iff_semBy m hmin hmax,
    SemBy.eq_iff_of_permInv (Measure.op_permInv hm rows) (sortLe_totalPre _)]
  unfold Measure.op; rw [ite_self]

/-! ## Plans: `Rel.OrderAllowed`'s order-sensitive cases -/

/-- The rows a `FETCH` takes from a list. -/
def fetchRows (off : Nat) : Option Nat → Relation → Relation
  | none, l => l.drop off
  | some n, l => (l.drop off).take n

/-- **An `ORDER BY` gives the enumerations of its input**: `Lin`. -/
theorem Rel.orderAllowed_orderBy {cat : Catalog} {r : Rel} {keys : List SortKey}
    {out : Relation} :
    (Rel.orderBy r keys).OrderAllowed cat out ↔ ∃ i, r.OrderAllowed cat i ∧ Lin keys i out :=
  Iff.rfl

/-- A `FETCH` takes its rows from whichever list its input gives. -/
theorem Rel.orderAllowed_fetch {cat : Catalog} {r : Rel} {off : Nat} {cnt : Option Nat}
    {out : Relation} :
    (Rel.fetch r off cnt).OrderAllowed cat out ↔
      ∃ i, r.OrderAllowed cat i ∧ out = fetchRows off cnt i := by
  cases cnt <;> exact Iff.rfl

/-- **A `FETCH` over an `ORDER BY` is `Sem`** of the rows it takes. -/
theorem Rel.orderAllowed_fetch_orderBy {cat : Catalog} {r : Rel} {keys : List SortKey}
    {off : Nat} {cnt : Option Nat} {out : Relation} :
    (Rel.fetch (.orderBy r keys) off cnt).OrderAllowed cat out ↔
      ∃ i, r.OrderAllowed cat i ∧ Sem (fetchRows off cnt) keys i out := by
  rw [Rel.orderAllowed_fetch]
  exact ⟨fun ⟨_, ⟨i, hi, hl⟩, he⟩ => ⟨i, hi, _, hl, he⟩,
    fun ⟨i, hi, L, hl, he⟩ => ⟨L, ⟨i, hi, hl⟩, he⟩⟩

/-- **A window is `SemBy`** of its rows over its own order. -/
theorem Rel.orderAllowed_window {cat : Catalog} {r : Rel} {part : List Nat}
    {sort : List SortKey} {fns : List WinFn} {out : Relation} :
    (Rel.window r part sort fns).OrderAllowed cat out ↔
      ∃ i, r.OrderAllowed cat i ∧ ∃ w, SemBy (windowRows part fns []) (sortLe sort) i w ∧
        out.Perm w :=
  ⟨fun ⟨i, hi, s, hp, hs, ho⟩ => ⟨i, hi, _, ⟨s, ⟨hp, hs⟩, rfl⟩, ho⟩,
    fun ⟨i, hi, _, ⟨s, ⟨hp, hs⟩, hw⟩, ho⟩ => ⟨i, hi, s, hp, hs, hw ▸ ho⟩⟩

/-! ## Forgetting the order: a set of multisets -/

/-- **The multisets `r` may give**: each result of every order the
reference allows, its order forgotten (`fromList`). On today's carrier a
multiset is a list up to `Perm`. -/
def Rel.Bags (cat : Catalog) (r : Rel) (B : Relation) : Prop :=
  ∃ out, r.OrderAllowed cat out ∧ out.Perm B

theorem Rel.Bags.perm {cat : Catalog} {r : Rel} {B B' : Relation} (h : r.Bags cat B)
    (hp : B.Perm B') : r.Bags cat B' :=
  let ⟨out, ho, hb⟩ := h; ⟨out, ho, hb.trans hp⟩

theorem Rel.bags_eval (cat : Catalog) (r : Rel) : r.Bags cat (r.eval cat) :=
  ⟨_, r.eval_orderAllowed cat, .refl _⟩

/-- An `ORDER BY` changes no multiset: it is the identity below the ordered
layer, as `evalK` (#905) takes it. -/
theorem Rel.bags_orderBy {cat : Catalog} {r : Rel} {keys : List SortKey} {B : Relation} :
    (Rel.orderBy r keys).Bags cat B ↔ r.Bags cat B :=
  ⟨fun ⟨_, ⟨i, hi, hp, _⟩, hb⟩ => ⟨i, hi, hp.symm.trans hb⟩,
    fun ⟨i, hi, hb⟩ =>
      ⟨_, ⟨i, hi, Lin.mergeSort keys i⟩, (List.mergeSort_perm _ _).trans hb⟩⟩

/-- A filter acts on each multiset. -/
theorem Rel.bags_filter {cat : Catalog} {r : Rel} {c : Expr} {B : Relation} :
    (Rel.filter r c).Bags cat B ↔
      ∃ B₀, r.Bags cat B₀ ∧ (B₀.filter fun row => (c.eval row).isTrue).Perm B :=
  ⟨fun ⟨_, ⟨i, hi, he⟩, hb⟩ => ⟨i, ⟨i, hi, .refl _⟩, he ▸ hb⟩,
    fun ⟨_, ⟨i, hi, hp⟩, hb⟩ => ⟨_, ⟨i, hi, rfl⟩, (hp.filter _).trans hb⟩⟩

/-- A projection acts on each multiset. -/
theorem Rel.bags_project {cat : Catalog} {r : Rel} {es : List Expr} {B : Relation} :
    (Rel.project r es).Bags cat B ↔
      ∃ B₀, r.Bags cat B₀ ∧ (B₀.map fun row => row ++ es.map (·.eval row)).Perm B :=
  ⟨fun ⟨_, ⟨i, hi, he⟩, hb⟩ => ⟨i, ⟨i, hi, .refl _⟩, he ▸ hb⟩,
    fun ⟨_, ⟨i, hi, hp⟩, hb⟩ => ⟨_, ⟨i, hi, rfl⟩, (hp.map _).trans hb⟩⟩

/-- `UNION ALL` acts on each pair of multisets. -/
theorem Rel.bags_unionAll {cat : Catalog} {a b : Rel} {B : Relation} :
    (Rel.unionAll a b).Bags cat B ↔
      ∃ X Y, a.Bags cat X ∧ b.Bags cat Y ∧ (X ++ Y).Perm B :=
  ⟨fun ⟨_, ⟨x, y, hx, hy, he⟩, hb⟩ => ⟨x, y, ⟨x, hx, .refl _⟩, ⟨y, hy, .refl _⟩, he.symm.trans hb⟩,
    fun ⟨_, _, ⟨x, hx, px⟩, ⟨y, hy, py⟩, hb⟩ =>
      ⟨_, ⟨x, y, hx, hy, .refl _⟩, (px.append py).trans hb⟩⟩

/-- A cross product acts on each pair of multisets. -/
theorem Rel.bags_cross {cat : Catalog} {a b : Rel} {B : Relation} :
    (Rel.cross a b).Bags cat B ↔
      ∃ X Y, a.Bags cat X ∧ b.Bags cat Y ∧ (crossRows X Y).Perm B :=
  ⟨fun ⟨_, ⟨x, y, hx, hy, he⟩, hb⟩ => ⟨x, y, ⟨x, hx, .refl _⟩, ⟨y, hy, .refl _⟩, he.symm.trans hb⟩,
    fun ⟨_, _, ⟨x, hx, px⟩, ⟨y, hy, py⟩, hb⟩ =>
      ⟨_, ⟨x, y, hx, hy, .refl _⟩, (crossRows_perm px py).trans hb⟩⟩

/-- A `FETCH` reads a list, not a multiset: its multisets are those of the
rows it takes from each result of its input. -/
theorem Rel.bags_fetch {cat : Catalog} {r : Rel} {off : Nat} {cnt : Option Nat} {B : Relation} :
    (Rel.fetch r off cnt).Bags cat B ↔
      ∃ i, r.OrderAllowed cat i ∧ (fetchRows off cnt i).Perm B := by
  unfold Rel.Bags; simp only [Rel.orderAllowed_fetch]
  exact ⟨fun ⟨_, ⟨i, hi, he⟩, hb⟩ => ⟨i, hi, he ▸ hb⟩, fun ⟨i, hi, hb⟩ => ⟨_, ⟨i, hi, rfl⟩, hb⟩⟩

/-- **A plan without choices has one multiset**, `Rel.eval`'s (D24's
deterministic profile). -/
theorem Rel.bags_iff_perm_eval {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : String → List (List Nat)}
    (hK : ∀ t, ∀ k ∈ K t, KeyOn k (cat t).rows) {r : Rel} (hwf : r.WF cat)
    (hd : r.detPlan cat A F K = true) {B : Relation} :
    r.Bags cat B ↔ B.Perm (r.eval cat) :=
  ⟨fun ⟨_, ho, hb⟩ =>
      hb.symm.trans (Rel.allowed_perm_eval hcat hA hF hK hwf hd (Rel.orderAllowed_allowed ho)),
    fun h => (r.bags_eval cat).perm h.symm⟩

/-- **An unordered `FETCH` has more than one multiset**: the first row of
two distinct rows is either of them. So its result is not determined, and
`refresh` refuses it unless the plan fixes the order. -/
theorem Rel.bags_fetch_two (cat : Catalog) :
    let r := Rel.fetch (.values 1 [[.int 0], [.int 1]]) 0 (some 1)
    r.Bags cat [[.int 0]] ∧ r.Bags cat [[.int 1]] ∧
      ¬ ([[Value.int 0]] : Relation).Perm [[.int 1]] := by
  refine ⟨Rel.bags_fetch.mpr ⟨_, List.Perm.refl _, .refl _⟩,
    Rel.bags_fetch.mpr ⟨[[.int 1], [.int 0]], List.Perm.swap _ _ _, .refl _⟩, ?_⟩
  simp

end Substrait
