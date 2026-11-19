import Sverify.Analysis.AllowedAnalysis

/-!
# Refinement through the operators (#1787)

A rewrite replaces a subplan `r` by `q`, and the plan around it stays. Where
`q` refines `r` (`Rel.Refines`, `Rel.RefinesBag`), the plan with `q` refines
the plan with `r`: the lemmas here carry a refinement up through each
operator, so a rule proved at one node holds of the whole plan.

How far a refinement up to the order of rows (`Rel.RefinesBag`) climbs
depends on the operator. Each constructor of `Rel`, with the form its lemma
takes:

| Constructor | Below | Above | Lemma |
|---|---|---|---|
| `read`, `values` | none | | no input to rewrite: no lemma |
| `filter`, `project`, `emit` | bag | bag | `Rel.RefinesBag.filter`, `.project`, `.emit` |
| `filter`, `project`, `emit` | exact | exact | `Rel.Refines.filter`, `.project`, `.emit` |
| `fetch` | exact | exact | `Rel.Refines.fetch` |
| `orderBy`, `window`, `distinct`, `aggregate`, `unnest` | bag | exact | `Rel.RefinesBag.orderBy`, `.window`, `.distinct`, `.aggregate`, `.unnest` |
| `cross`, `join`, `unionAll`, `semi` | bag, both inputs | exact | `Rel.RefinesBag.cross`, `.join`, `.unionAll`, `.semi` |

`FILTER`, `PROJECT` and `EMIT` keep their input's order, so a refinement up to
the order of rows stays one and no more. The operators of the bag-to-exact
rows read their input in any order or allow their output in any order, so an
`ORDER BY` over a rewritten input refines the original exactly. `FETCH` takes
the first rows of its input's order and has no bag lemma: it would be false,
as `Rel.unsorted_refinesBag_not_refines` shows for `ORDER BY`. A left join
pads with as many NULLs as its right input has columns, so `.join` asks the
right inputs' arities to agree for a left join only (`values 1 []` and
`values 2 []` refine each other).

An exact refinement climbs through every operator: through the exact rows by
their lemmas, through the rest by `Rel.Refines.bag` and the bag lemmas.
-/

namespace Substrait
variable [Boxes.Ambient]

variable {cat : Catalog}

/-! ## Up to the order of rows, kept -/

theorem Rel.RefinesBag.filter {q r : Rel} (h : q.RefinesBag cat r) (c : Expr) :
    (Rel.filter q c).RefinesBag cat (.filter r c) :=
  Rel.refinesBag_iff.2 fun _ ⟨i, hi, he⟩ => by
    obtain ⟨i', hi', hp⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨_, ⟨i', hi', rfl⟩, he ▸ hp.filter _⟩

theorem Rel.RefinesBag.project {q r : Rel} (h : q.RefinesBag cat r) (es : List Expr) :
    (Rel.project q es).RefinesBag cat (.project r es) :=
  Rel.refinesBag_iff.2 fun _ ⟨i, hi, he⟩ => by
    obtain ⟨i', hi', hp⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨_, ⟨i', hi', rfl⟩, he ▸ hp.map _⟩

theorem Rel.RefinesBag.emit {q r : Rel} (h : q.RefinesBag cat r) (m : List Nat) :
    (Rel.emit q m).RefinesBag cat (.emit r m) :=
  Rel.refinesBag_iff.2 fun _ ⟨i, hi, he⟩ => by
    obtain ⟨i', hi', hp⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨_, ⟨i', hi', rfl⟩, he ▸ hp.map _⟩

/-! ## Up to the order of rows below, exact above -/

theorem Rel.RefinesBag.orderBy {q r : Rel} (h : q.RefinesBag cat r) (keys : List SortKey) :
    (Rel.orderBy q keys).Refines cat (.orderBy r keys) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, hp, hs⟩ => by
    obtain ⟨i', hi', hp'⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨i', hi', hp.trans hp', hs⟩

theorem Rel.RefinesBag.window {q r : Rel} (h : q.RefinesBag cat r) (part : List Nat)
    (sort : List SortKey) (fns : List WinFn) :
    (Rel.window q part sort fns).Refines cat (.window r part sort fns) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, s, hs, hrest⟩ => by
    obtain ⟨i', hi', hp⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨i', hi', s, hs.trans hp, hrest⟩

theorem Rel.RefinesBag.distinct {q r : Rel} (h : q.RefinesBag cat r) :
    (Rel.distinct q).Refines cat (.distinct r) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, d, hd, hp⟩ => by
    obtain ⟨i', hi', hp'⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨i', hi', d, hd.congr fun _ => hp'.mem_iff, hp⟩

theorem Rel.RefinesBag.unnest {q r : Rel} (h : q.RefinesBag cat r) (c : Nat) :
    (Rel.unnest q c).Refines cat (.unnest r c) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, hp⟩ => by
    obtain ⟨i', hi', hp'⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨i', hi', hp.trans (hp'.flatMap_right _)⟩

/-- What an aggregate allows depends on its input up to its order. -/
theorem aggAllowed_perm {gs : List Expr} {ms : List Measure} {rows rows' out : Relation}
    (h : aggAllowed gs ms rows out) (hp : rows.Perm rows') : aggAllowed gs ms rows' out := by
  by_cases hg : gs.isEmpty = true
  · simp only [aggAllowed, hg, ite_true] at h ⊢
    obtain ⟨vs, rfl, hv⟩ := h
    exact ⟨vs, rfl, hv.imp fun _ _ hm => hm.perm hp⟩
  · simp only [aggAllowed, hg, ite_false, Bool.false_eq_true] at h ⊢
    obtain ⟨ks, hks, hf⟩ := h
    exact ⟨ks, hks.congr fun _ => (hp.map _).mem_iff, hf.imp fun k _ ⟨vs, he, hv⟩ =>
      ⟨vs, he, hv.imp fun _ _ hm => hm.perm (groupRows_perm hp k)⟩⟩

theorem Rel.RefinesBag.aggregate {q r : Rel} (h : q.RefinesBag cat r) (gs : List Expr)
    (ms : List Measure) :
    (Rel.aggregate q gs ms).Refines cat (.aggregate r gs ms) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, o, hp, ho⟩ => by
    obtain ⟨i', hi', hp'⟩ := Rel.refinesBag_iff.1 h i hi
    exact ⟨i', hi', o, hp, aggAllowed_perm ho hp'⟩

theorem Rel.RefinesBag.cross {qa ra qb rb : Rel} (ha : qa.RefinesBag cat ra)
    (hb : qb.RefinesBag cat rb) : (Rel.cross qa qb).Refines cat (.cross ra rb) :=
  Rel.refines_iff.2 fun _ ⟨x, y, hx, hy, hp⟩ => by
    obtain ⟨x', hx', px⟩ := Rel.refinesBag_iff.1 ha x hx
    obtain ⟨y', hy', py⟩ := Rel.refinesBag_iff.1 hb y hy
    exact ⟨x', y', hx', hy', hp.trans (crossRows_perm px py)⟩

/-- A left join pads with as many NULLs as its right input has columns, so
for a left join the two right inputs have one arity. -/
theorem Rel.RefinesBag.join {qa ra qb rb : Rel} (ha : qa.RefinesBag cat ra)
    (hb : qb.RefinesBag cat rb) {ty : JoinType} (har : ty = .left → qb.arity cat = rb.arity cat)
    (on : Expr) :
    (Rel.join qa qb ty on).Refines cat (.join ra rb ty on) := by
  refine Rel.refines_iff.2 fun out hq => ?_
  cases ty with
  | inner =>
    obtain ⟨x, y, hx, hy, hp⟩ := hq
    obtain ⟨x', hx', px⟩ := Rel.refinesBag_iff.1 ha x hx
    obtain ⟨y', hy', py⟩ := Rel.refinesBag_iff.1 hb y hy
    exact ⟨x', y', hx', hy', hp.trans ((crossRows_perm px py).filter _)⟩
  | left =>
    obtain ⟨x, y, hx, hy, hp⟩ := hq
    obtain ⟨x', hx', px⟩ := Rel.refinesBag_iff.1 ha x hx
    obtain ⟨y', hy', py⟩ := Rel.refinesBag_iff.1 hb y hy
    refine ⟨x', y', hx', hy', hp.trans ?_⟩
    rw [har rfl]
    exact (flatMap_perm_congr fun z _ => leftJoinRow_perm z py).trans (px.flatMap_right _)

theorem Rel.RefinesBag.unionAll {qa ra qb rb : Rel} (ha : qa.RefinesBag cat ra)
    (hb : qb.RefinesBag cat rb) : (Rel.unionAll qa qb).Refines cat (.unionAll ra rb) :=
  Rel.refines_iff.2 fun _ ⟨x, y, hx, hy, hp⟩ => by
    obtain ⟨x', hx', px⟩ := Rel.refinesBag_iff.1 ha x hx
    obtain ⟨y', hy', py⟩ := Rel.refinesBag_iff.1 hb y hy
    exact ⟨x', y', hx', hy', hp.trans (px.append py)⟩

theorem Rel.RefinesBag.semi {qa ra qb rb : Rel} (ha : qa.RefinesBag cat ra)
    (hb : qb.RefinesBag cat rb) (anti : Bool) (on : Expr) :
    (Rel.semi qa qb anti on).Refines cat (.semi ra rb anti on) :=
  Rel.refines_iff.2 fun _ ⟨x, y, hx, hy, hp⟩ => by
    obtain ⟨x', hx', px⟩ := Rel.refinesBag_iff.1 ha x hx
    obtain ⟨y', hy', py⟩ := Rel.refinesBag_iff.1 hb y hy
    refine ⟨x', y', hx', hy', hp.trans ?_⟩
    have : (fun row => hasMatch on y row != anti) = fun row => hasMatch on y' row != anti := by
      funext row; simp only [hasMatch, py.any_eq]
    rw [this]; exact px.filter _

/-! ## Exact -/

theorem Rel.Refines.filter {q r : Rel} (h : q.Refines cat r) (c : Expr) :
    (Rel.filter q c).Refines cat (.filter r c) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, he⟩ => ⟨i, Rel.refines_iff.1 h i hi, he⟩

theorem Rel.Refines.project {q r : Rel} (h : q.Refines cat r) (es : List Expr) :
    (Rel.project q es).Refines cat (.project r es) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, he⟩ => ⟨i, Rel.refines_iff.1 h i hi, he⟩

theorem Rel.Refines.emit {q r : Rel} (h : q.Refines cat r) (m : List Nat) :
    (Rel.emit q m).Refines cat (.emit r m) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, he⟩ => ⟨i, Rel.refines_iff.1 h i hi, he⟩

theorem Rel.Refines.fetch {q r : Rel} (h : q.Refines cat r) (off : Nat) (cnt : Option Nat) :
    (Rel.fetch q off cnt).Refines cat (.fetch r off cnt) :=
  Rel.refines_iff.2 fun _ ⟨i, hi, he⟩ => ⟨i, Rel.refines_iff.1 h i hi, he⟩

end Substrait
