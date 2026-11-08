import Sverify.Core.Rel

/-!
# Weighted relations and their evaluator (#905)

A relation over a weight type `K` is a list of rows with weights,
`WSet K := List (Row × K)` (K-relations: Green, Karvounarakis, Tannen,
"Provenance semirings", PODS 2007). The weights pick the semantics: `Nat`
gives bags, `Int` gives Z-sets (`SubstraitLean/Incremental.lean`, where a
deletion is a negative weight), and a provenance semiring gives lineage.

`Rel.evalK I cat` evaluates the incremental fragment (`Rel.Incremental`:
read, values, filter, project, emit, cross, inner join, union and sort) over
any `K` with a multiplication and a one. Union appends, cross and join
multiply weights. The other operators give `[]`; every theorem excludes them.
`ORDER BY` sorts by the rows and leaves the weights alone.

Main results:

* `Rel.incrementalK_sound`: `Q(D + ΔD) ~ Q(D) + ΔQ` for any `[Mul K]`, with
  `ΔQ` computed by the delta plan `Rel.delta`, an ordinary plan an engine
  runs. The delta rule uses no law of `K`: `WSet.cross_add` is append and
  permutation only.
* `Rel.evalK_lift`: over a semiring, on rows of weight `1`, `evalK` is
  `Rel.eval`.
* `Rel.evalK_mapW`: changing the weights by a map that keeps `*` and `1`
  commutes with evaluation (the K-relation homomorphism theorem).

Equivalence is `List.Perm`, finer than equality of weight functions (it never
adds two weights of one row), so each `Perm` result also holds for those.
-/

namespace Substrait

/-- Rows with weights in `K`. -/
abbrev WSet (K : Type) := List (Row × K)

namespace WSet

variable {K : Type}

/-- Every row with weight `1`. -/
def lift [One K] (r : Relation) : WSet K := r.map (·, 1)

def filter (p : Row → Bool) (z : WSet K) : WSet K := List.filter (fun x => p x.1) z

def map (f : Row → Row) (z : WSet K) : WSet K := List.map (fun x => (f x.1, x.2)) z

/-- Weights multiply. This makes the cross product bilinear. -/
def cross [Mul K] (a b : WSet K) : WSet K :=
  List.flatMap (fun x => List.map (fun y => (x.1 ++ y.1, x.2 * y.2)) b) a

/-- The same rows with their weights sent through `h`. -/
def mapW {L : Type} (h : K → L) (z : WSet K) : WSet L := List.map (fun x => (x.1, h x.2)) z

section Cross

variable [Mul K]

theorem cross_append_left (a a' b : WSet K) : cross (a ++ a') b = cross a b ++ cross a' b := by
  simp [cross, List.flatMap_append]

theorem cross_append_right (a b b' : WSet K) :
    (cross a (b ++ b')).Perm (cross a b ++ cross a b') := by
  induction a with
  | nil => simp [cross]
  | cons x a ih =>
    simp only [cross, List.flatMap_cons, List.map_append] at *
    refine (ih.append_left _).trans ?_
    simp only [List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

theorem cross_perm {a a' b b' : WSet K} (ha : a.Perm a') (hb : b.Perm b') :
    (cross a b).Perm (cross a' b') := by
  refine (List.Perm.flatMap_right _ ha).trans ?_
  clear ha
  induction a' with
  | nil => simp [cross]
  | cons x a' ih => simp only [cross, List.flatMap_cons] at *; exact (hb.map _).append ih

/-- The bilinear delta rule: `(A + ΔA) × (B + ΔB) ~ A × B + (ΔA × (B + ΔB) + A × ΔB)`. -/
theorem cross_add (A ΔA B ΔB : WSet K) :
    (cross (A ++ ΔA) (B ++ ΔB)).Perm (cross A B ++ (cross ΔA (B ++ ΔB) ++ cross A ΔB)) := by
  rw [cross_append_left]
  refine ((cross_append_right A B ΔB).append_right _).trans ?_
  simp only [List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

end Cross

/-! ### Weights

Read through `weight`, the total weight of each row, a `WSet K` is a
finitely supported function `Row → K`, an element of the free
`K`-semimodule on rows: the support lies in the listed rows
(`weight_of_not_mem`), append is pointwise addition (`weight_append`), and a
permutation keeps every weight (`weight_perm`), so each `Perm` theorem is also
an equality of weight functions. -/

/-- The total weight of `row` in `z`. -/
def weight [Add K] [Zero K] (z : WSet K) (row : Row) : K :=
  z.foldr (fun x acc => if x.1 == row then x.2 + acc else acc) 0

section Weight

variable [Lean.Grind.Semiring K]

theorem weight_nil (row : Row) : weight ([] : WSet K) row = 0 := rfl

theorem weight_cons (x : Row × K) (z : WSet K) (row : Row) :
    weight (x :: z) row = (if x.1 = row then x.2 else 0) + z.weight row := by
  simp only [weight, List.foldr_cons, beq_iff_eq]
  split
  · rfl
  · rw [Lean.Grind.Semiring.add_comm, Lean.Grind.Semiring.add_zero]

theorem weight_of_not_mem {z : WSet K} {row : Row} (h : row ∉ List.map (·.1) z) :
    z.weight row = 0 := by
  induction z with
  | nil => rfl
  | cons x z ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [weight, List.foldr_cons] at ih ⊢
    split
    · exact absurd (beq_iff_eq.mp ‹_›).symm h.1
    · exact ih h.2

theorem weight_append (a b : WSet K) (row : Row) :
    (a ++ b).weight row = a.weight row + b.weight row := by
  induction a with
  | nil =>
    show b.weight row = 0 + b.weight row
    rw [Lean.Grind.Semiring.add_comm, Lean.Grind.Semiring.add_zero]
  | cons x a ih =>
    simp only [weight, List.cons_append, List.foldr_cons] at ih ⊢
    split
    · rw [ih, Lean.Grind.Semiring.add_assoc]
    · exact ih

theorem weight_perm {a b : WSet K} (h : a.Perm b) (row : Row) : a.weight row = b.weight row := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [weight, List.foldr_cons] at ih ⊢; rw [ih]
  | swap x y l =>
    simp only [weight, List.foldr_cons]
    split <;> split <;> try rfl
    rw [← Lean.Grind.Semiring.add_assoc, ← Lean.Grind.Semiring.add_assoc,
      Lean.Grind.Semiring.add_comm y.2]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem weight_mergeSort (le : Row × K → Row × K → Bool) (z : WSet K) (row : Row) :
    weight (z.mergeSort le) row = z.weight row :=
  weight_perm (List.mergeSort_perm z le) row

end Weight

end WSet

/-- A catalog of weighted tables. -/
abbrev WCatalog (K : Type) := String → WSet K

/-- Apply a change set: each table gains the rows (and weights) in `Δ`. -/
instance {K : Type} : Add (WCatalog K) := ⟨fun cat Δ t => cat t ++ Δ t⟩

theorem WCatalog.add_apply {K : Type} (cat Δ : WCatalog K) (t : String) :
    (cat + Δ) t = cat t ++ Δ t := rfl

/-- Operators whose result changes linearly (or bilinearly) with their
inputs. A left join can retract its null-padded rows, a semi or anti join
depends on whether *any* right row matches, `DISTINCT` on whether a row was
there before, and a fetch or a window on the other rows' positions, so none
has a delta rule of this shape. A sort is just a bag in some order.
`DISTINCT` and `COUNT` and `SUM` per group do have delta rules, over a state
kept beside the view: a count per row or per group, and each measure's
count and sum (`LinearAgg` in `SubstraitLean/IncrementalAgg.lean`); so do
`MIN` and `MAX`, which recompute the groups a batch deletes from
(`ExtremeAgg` in `SubstraitLean/IncrementalMinMax.lean`), and semi and anti
joins, from a count of matches per left row (`SemiDelta` in
`SubstraitLean/IncrementalSemi.lean`). -/
def Rel.Incremental : Rel → Prop
  | .read _ | .values _ _ => True
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => r.Incremental
  | .cross a b | .unionAll a b | .join a b .inner _ => a.Incremental ∧ b.Incremental
  | .join _ _ .left _ | .fetch _ _ _ | .window _ _ _ _ | .semi _ _ _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => False

def Rel.tables : Rel → List String
  | .read t => [t]
  | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .aggregate r _ _ | .unnest r _ => r.tables
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => a.tables ++ b.tables

/-! ## Delta plans

`Rel.delta δ r` is a plan that reads the old tables `t` and the change
tables `δ t` and outputs `ΔQ`. Since it is an ordinary `Rel`, it can be
serialized back to Substrait and run by an engine. -/

def Rel.delta (δ : String → String) : Rel → Rel
  | .read t => .read (δ t)
  | .values n _ => .values n []
  | .filter r c => .filter (r.delta δ) c
  | .project r es => .project (r.delta δ) es
  | .emit r m => .emit (r.delta δ) m
  | .cross a b => .unionAll (.cross (a.delta δ) (.unionAll b (b.delta δ))) (.cross a (b.delta δ))
  | .join a b ty on =>
      .unionAll (.join (a.delta δ) (.unionAll b (b.delta δ)) ty on) (.join a (b.delta δ) ty on)
  | .unionAll a b => .unionAll (a.delta δ) (b.delta δ)
  | .fetch r o c => .fetch (r.delta δ) o c
  | .window r p s f => .window (r.delta δ) p s f
  | .orderBy r keys => .orderBy (r.delta δ) keys
  | .semi a b anti on => .semi (a.delta δ) (b.delta δ) anti on
  | .distinct r => .distinct (r.delta δ)
  | .unnest r c => .unnest (r.delta δ) c
  | .aggregate r gs ms => .aggregate (r.delta δ) gs ms

/-! ## The evaluator -/

/-- Whether a weighted set has positive total weight: DBSP's `[w > 0]`,
which `DISTINCT`, semi and anti joins and a left join's padding read. -/
def WSet.positive {K : Type} [Add K] [Zero K] [LT K] [DecidableLT K] (z : WSet K) : Bool :=
  decide (0 < (List.map (·.2) z).sum)

/-- What `Rel.evalK` reads where it does not recurse: the rows of the ordered
and aggregate nodes (`fetch`, windows, aggregates), the presence test of
`DISTINCT`, semi joins and left joins, and the arity a left join pads to.
The default reads nothing: no rows, nothing present, no padding. -/
structure Seam (K : Type) where
  ord : Rel → WSet K := fun _ => []
  pos : WSet K → Bool := fun _ => false
  arity : Rel → Nat := fun _ => 0

theorem List.filter_const_false' {α : Type} (l : List α) : l.filter (fun _ => false) = [] := by simp

section EvalK

variable {K : Type} [Mul K] [One K]

/-- Weighted semantics, with the scalar functions of `I`. Union appends,
cross and join multiply weights, `DISTINCT` keeps each present row once,
semi and anti joins keep the left rows whose matches are (not) present, and
a left join pads the left rows whose matches are not. `fetch`, windows and
aggregates read the seam `S`. -/
def Rel.evalK (I : Impl) (cat : WCatalog K) (S : Seam K := {}) : Rel → WSet K
  | .read t => cat t
  | .values _ rows => WSet.lift rows
  | .filter r c => WSet.filter (fun row => (c.eval row I).isTrue) (r.evalK I cat S)
  | .project r es => WSet.map (fun row => row ++ es.map (·.eval row I)) (r.evalK I cat S)
  | .emit r m => WSet.map (fun row => m.map (row.getD · .null)) (r.evalK I cat S)
  | .cross a b => WSet.cross (a.evalK I cat S) (b.evalK I cat S)
  | .join a b .inner on =>
      WSet.filter (fun row => (on.eval row I).isTrue)
        (WSet.cross (a.evalK I cat S) (b.evalK I cat S))
  | .join a b .left on => (a.evalK I cat S).flatMap fun x =>
      let ms := WSet.filter (fun row => (on.eval row I).isTrue) (WSet.cross [x] (b.evalK I cat S))
      if S.pos ms then ms else [(x.1 ++ List.replicate (S.arity b) .null, x.2)]
  | .unionAll a b => a.evalK I cat S ++ b.evalK I cat S
  | .orderBy r keys => (r.evalK I cat S).mergeSort fun x y => sortLe keys x.1 y.1
  | .distinct r =>
      let z := r.evalK I cat S
      ((dedup (List.map (·.1) z)).filter fun row => S.pos (WSet.filter (· == row) z)).map (·, 1)
  | .semi a b anti on => WSet.filter (fun x => S.pos (WSet.filter
      (fun y => (on.eval (x ++ y) I).isTrue) (b.evalK I cat S)) != anti) (a.evalK I cat S)
  | .unnest r c => (r.evalK I cat S).flatMap fun x => (unnestRow c x.1).map (·, x.2)
  | r@(.fetch _ _ _) | r@(.window _ _ _ _) | r@(.aggregate _ _ _) => S.ord r

variable {I : Impl}

/-- A plan only depends on the tables it reads. -/
theorem Rel.evalK_congr {C cat : WCatalog K} {S : Seam K} :
    ∀ {r : Rel}, (∀ t ∈ r.tables, C t = cat t) → r.evalK I C S = r.evalK I cat S
  | .read t, h => h t (by simp [tables])
  | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h | .distinct r, h
  | .unnest r _, h => by
      simp only [evalK, evalK_congr (r := r) h]
  | .fetch _ _ _, _ | .window _ _ _ _, _ | .aggregate _ _ _, _ => rfl
  | .cross a b, h | .unionAll a b, h | .join a b .inner _, h | .join a b .left _, h
  | .semi a b _ _, h => by
      simp only [tables, List.mem_append] at h
      simp only [evalK, evalK_congr (r := a) (fun t ht => h t (.inl ht)),
        evalK_congr (r := b) (fun t ht => h t (.inr ht))]

/-- On the incremental fragment the seam is never read. -/
theorem Rel.evalK_seam {cat : WCatalog K} {S S' : Seam K} :
    ∀ {r : Rel}, r.Incremental → r.evalK I cat S = r.evalK I cat S'
  | .read _, _ | .values _ _, _ => rfl
  | .filter r _, h | .project r _, h | .emit r _, h | .orderBy r _, h => by
      simp only [evalK, evalK_seam (r := r) (S := S) (S' := S') h]
  | .cross a b, h | .unionAll a b, h | .join a b .inner _, h => by
      simp only [evalK, evalK_seam (r := a) (S := S) (S' := S') h.1,
        evalK_seam (r := b) (S := S) (S' := S') h.2]
  | .join _ _ .left _, h => h.elim
  | .fetch _ _ _, h | .window _ _ _ _, h | .semi _ _ _ _, h | .distinct _, h
  | .aggregate _ _ _, h | .unnest _ _, h => h.elim

/-- **Incremental maintenance is sound**, for any weights: the new result is
the old result plus the output of the delta plan `Rel.delta δ r`, run on the
engine's catalog `C` (old tables under their own names, change tables under
`δ t`). The step at a cross product or an inner join is bilinearity,
`(A + ΔA) × (B + ΔB) ~ A × B + (ΔA × (B + ΔB) + A × ΔB)` (`WSet.cross_add`);
filter, project, emit, union and sort are linear. No law of `K` is used. -/
theorem Rel.incrementalK_sound {C cat Δ : WCatalog K} {δ : String → String} :
    ∀ {r : Rel}, r.Incremental →
      (∀ t ∈ r.tables, C t = cat t) → (∀ t ∈ r.tables, C (δ t) = Δ t) →
      (r.evalK I (cat + Δ)).Perm (r.evalK I cat ++ (r.delta δ).evalK I C)
  | .read t, _, _, hδ => by simp [evalK, delta, WCatalog.add_apply, hδ t (by simp [tables])]
  | .values _ _, _, _, _ => by simp [evalK, delta, WSet.lift]
  | .filter r _, h, hold, hδ => by
      simp only [evalK, delta, WSet.filter, ← List.filter_append]
      exact (incrementalK_sound (r := r) h hold hδ).filter _
  | .project r _, h, hold, hδ | .emit r _, h, hold, hδ => by
      simp only [evalK, delta, WSet.map, ← List.map_append]
      exact (incrementalK_sound (r := r) h hold hδ).map _
  | .orderBy r _, h, hold, hδ => by
      simp only [evalK, delta]
      exact (List.mergeSort_perm _ _).trans ((incrementalK_sound (r := r) h hold hδ).trans
        (List.Perm.append (List.mergeSort_perm _ _).symm (List.mergeSort_perm _ _).symm))
  | .cross a b, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [evalK, delta, evalK_congr (r := a) (fun t ht => hold t (.inl ht)),
        evalK_congr (r := b) (fun t ht => hold t (.inr ht))]
      exact (WSet.cross_perm
        (incrementalK_sound (r := a) h.1 (fun t ht => hold t (.inl ht)) (fun t ht => hδ t (.inl ht)))
        (incrementalK_sound (r := b) h.2 (fun t ht => hold t (.inr ht))
          (fun t ht => hδ t (.inr ht)))).trans (WSet.cross_add _ _ _ _)
  | .join a b .inner _, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [evalK, delta, evalK_congr (r := a) (fun t ht => hold t (.inl ht)),
        evalK_congr (r := b) (fun t ht => hold t (.inr ht)), WSet.filter, ← List.filter_append]
      exact ((WSet.cross_perm
        (incrementalK_sound (r := a) h.1 (fun t ht => hold t (.inl ht)) (fun t ht => hδ t (.inl ht)))
        (incrementalK_sound (r := b) h.2 (fun t ht => hold t (.inr ht))
          (fun t ht => hδ t (.inr ht)))).trans (WSet.cross_add _ _ _ _)).filter _
  | .unionAll a b, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [evalK, delta]
      refine ((incrementalK_sound (r := a) h.1 (fun t ht => hold t (.inl ht))
        (fun t ht => hδ t (.inl ht))).append (incrementalK_sound (r := b) h.2
          (fun t ht => hold t (.inr ht)) (fun t ht => hδ t (.inr ht)))).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)
  | .join _ _ .left _, h, _, _ => h.elim
  | .fetch _ _ _, h, _, _ | .window _ _ _ _, h, _, _ | .semi _ _ _ _, h, _, _
  | .distinct _, h, _, _ | .aggregate _ _ _, h, _, _ | .unnest _ _, h, _, _ => h.elim

/-- **The delta plan's output only depends on the old tables and the
changes**: two engine catalogs that hold them, under any names for the change
tables, give the same rows. -/
theorem Rel.delta_evalK_eq {C C' cat Δ : WCatalog K} {δ δ' : String → String} :
    ∀ {r : Rel}, (∀ t ∈ r.tables, C t = cat t) → (∀ t ∈ r.tables, C (δ t) = Δ t) →
      (∀ t ∈ r.tables, C' t = cat t) → (∀ t ∈ r.tables, C' (δ' t) = Δ t) →
      (r.delta δ).evalK I C = (r.delta δ').evalK I C'
  | .read t, _, hδ, _, hδ' => (hδ t (by simp [tables])).trans (hδ' t (by simp [tables])).symm
  | .values _ _, _, _, _, _ => rfl
  | .filter r _, h1, h2, h3, h4 | .project r _, h1, h2, h3, h4 | .emit r _, h1, h2, h3, h4
  | .orderBy r _, h1, h2, h3, h4 => by
      simp only [delta, evalK, delta_evalK_eq (r := r) h1 h2 h3 h4]
  | .cross a b, h1, h2, h3, h4 | .join a b .inner _, h1, h2, h3, h4 => by
      simp only [tables, List.mem_append] at h1 h2 h3 h4
      simp only [delta, evalK,
        delta_evalK_eq (r := a) (fun t ht => h1 t (.inl ht)) (fun t ht => h2 t (.inl ht))
          (fun t ht => h3 t (.inl ht)) (fun t ht => h4 t (.inl ht)),
        delta_evalK_eq (r := b) (fun t ht => h1 t (.inr ht)) (fun t ht => h2 t (.inr ht))
          (fun t ht => h3 t (.inr ht)) (fun t ht => h4 t (.inr ht)),
        evalK_congr (r := a) (fun t ht => h1 t (.inl ht)),
        evalK_congr (r := a) (fun t ht => h3 t (.inl ht)),
        evalK_congr (r := b) (fun t ht => h1 t (.inr ht)),
        evalK_congr (r := b) (fun t ht => h3 t (.inr ht))]
  | .unionAll a b, h1, h2, h3, h4 => by
      simp only [tables, List.mem_append] at h1 h2 h3 h4
      simp only [delta, evalK,
        delta_evalK_eq (r := a) (fun t ht => h1 t (.inl ht)) (fun t ht => h2 t (.inl ht))
          (fun t ht => h3 t (.inl ht)) (fun t ht => h4 t (.inl ht)),
        delta_evalK_eq (r := b) (fun t ht => h1 t (.inr ht)) (fun t ht => h2 t (.inr ht))
          (fun t ht => h3 t (.inr ht)) (fun t ht => h4 t (.inr ht))]
  | .join a b .left _, h1, h2, h3, h4 => by
      simp only [tables, List.mem_append] at h1 h2 h3 h4
      simp [delta, evalK,
        delta_evalK_eq (r := a) (fun t ht => h1 t (.inl ht)) (fun t ht => h2 t (.inl ht))
          (fun t ht => h3 t (.inl ht)) (fun t ht => h4 t (.inl ht)),
        evalK_congr (r := a) (fun t ht => h1 t (.inl ht)),
        evalK_congr (r := a) (fun t ht => h3 t (.inl ht))]
  | .semi a b _ _, h1, h2, h3, h4 => by
      simp only [tables, List.mem_append] at h1 h2 h3 h4
      simp [delta, evalK,
        delta_evalK_eq (r := a) (fun t ht => h1 t (.inl ht)) (fun t ht => h2 t (.inl ht))
          (fun t ht => h3 t (.inl ht)) (fun t ht => h4 t (.inl ht))]
  | .unnest r _, h1, h2, h3, h4 => by
      simp only [delta, evalK, delta_evalK_eq (r := r) h1 h2 h3 h4]
  | .distinct _, _, _, _, _ => by simp [delta, evalK, List.filter_const_false']
  | .fetch _ _ _, _, _, _, _ | .window _ _ _ _, _, _, _, _ | .aggregate _ _ _, _, _, _, _ => rfl

/-- **Changing the weights commutes with evaluation**: a map `h` that keeps
`*` and `1` sends the evaluation over `K` to the evaluation over `L` of the
mapped tables, on every plan, with the default seam. -/
theorem Rel.evalK_mapW {L : Type} [Mul L] [One L] {h : K → L}
    (hmul : ∀ a b, h (a * b) = h a * h b) (hone : h 1 = 1) {cat : WCatalog K} :
    ∀ r : Rel, (r.evalK I cat).mapW h = r.evalK I (fun t => (cat t).mapW h)
  | .read _ => rfl
  | .values _ _ => by simp [evalK, WSet.mapW, WSet.lift, hone]
  | .filter r _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone r]
      simp [WSet.mapW, WSet.filter, List.filter_map, Function.comp_def]
  | .project r _ | .emit r _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone r]
      simp [WSet.mapW, WSet.map]
  | .cross a b => by
      simp only [evalK]; rw [← evalK_mapW hmul hone a, ← evalK_mapW hmul hone b]
      simp [WSet.mapW, WSet.cross, List.map_flatMap, List.flatMap_map, hmul, Function.comp_def]
  | .join a b .inner _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone a, ← evalK_mapW hmul hone b]
      simp [WSet.mapW, WSet.cross, WSet.filter, List.map_flatMap, List.flatMap_map,
        List.filter_map, List.filter_flatMap, hmul, Function.comp_def]
  | .unionAll a b => by
      simp only [evalK]; rw [← evalK_mapW hmul hone a, ← evalK_mapW hmul hone b]
      simp [WSet.mapW]
  | .orderBy r _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone r]
      exact List.map_mergeSort (f := fun (x : Row × K) => (x.1, h x.2)) fun _ _ _ _ => rfl
  | .join a b .left _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone a]
      simp [WSet.mapW, List.flatMap_map, ← List.map_eq_flatMap]
  | .semi a b _ _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone a]
      simp [WSet.mapW, WSet.filter, List.filter_map, Function.comp_def]
  | .unnest r _ => by
      simp only [evalK]; rw [← evalK_mapW hmul hone r]
      simp [WSet.mapW, List.map_flatMap, List.flatMap_map, Function.comp_def]
  | .distinct _ => by simp [evalK, WSet.mapW, List.filter_const_false']
  | .fetch _ _ _ | .window _ _ _ _ | .aggregate _ _ _ => rfl

end EvalK

/-! ## Agreement with bag semantics -/

theorem WSet.lift_filter {K : Type} [One K] (p : Row → Bool) (rows : Relation) :
    (WSet.lift (rows.filter p) : WSet K) = WSet.filter p (WSet.lift rows) := by
  simp [WSet.lift, WSet.filter, List.filter_map, Function.comp_def]

theorem WSet.positive_lift (rows : Relation) : (WSet.lift rows : WSet Nat).positive = !rows.isEmpty := by
  cases rows <;> simp [positive, lift] <;> omega

/-- The seam of bags: ordered and aggregate nodes give their rows under
`Rel.eval`, at weight `1`. -/
def Seam.bags (cat : Catalog) (I : Impl) : Seam Nat where
  ord r := WSet.lift (r.eval cat I)
  pos := WSet.positive
  arity r := r.arity cat

theorem any_eq_not_isEmpty_filter (p : Row → Bool) (rows : Relation) :
    rows.any p = !(rows.filter p).isEmpty := by
  induction rows with
  | nil => rfl
  | cons x rows ih => by_cases h : p x <;> simp [h, ih]

/-- **`Rel.eval` is `Rel.evalK` over `Nat`.** On bags, every plan's rows at
weight `1` are its weighted evaluation, with the seam of bags at the ordered
and aggregate nodes. Every unordered arm of `Rel.eval` (filter, project,
emit, cross, joins, union, sort, `DISTINCT`, semi and anti joins, unnest)
is the weighted one, stated once. -/
theorem Rel.eval_eq_evalK {cat : Catalog} {I : Impl} :
    ∀ r : Rel, r.evalK I (fun t => WSet.lift (cat t).rows) (Seam.bags cat I) = WSet.lift (r.eval cat I)
  | .read _ | .values _ _ | .fetch _ _ _ | .window _ _ _ _ | .aggregate _ _ _ => rfl
  | .filter r _ => by
      simp only [evalK, eval, eval_eq_evalK r, ← WSet.lift_filter]
  | .project r _ | .emit r _ => by
      simp only [evalK, eval, eval_eq_evalK r]; simp [WSet.map, WSet.lift]
  | .cross a b => by
      simp only [evalK, eval, eval_eq_evalK a, eval_eq_evalK b]
      simp [WSet.cross, WSet.lift, crossRows, List.flatMap_map, List.map_flatMap,
        Function.comp_def]
  | .join a b .inner _ => by
      simp only [evalK, eval, eval_eq_evalK a, eval_eq_evalK b]
      simp [WSet.cross, WSet.filter, WSet.lift, crossRows, List.flatMap_map, List.map_flatMap,
        List.filter_map, List.filter_flatMap, Function.comp_def]
  | .join a b .left on => by
      simp only [evalK, eval, eval_eq_evalK a, eval_eq_evalK b]
      simp only [WSet.lift, List.flatMap_map, List.map_flatMap]
      congr 1; funext x
      have hms : WSet.filter (fun row => (on.eval row I).isTrue)
          (WSet.cross [(x, 1)] (List.map (·, 1) (b.eval cat I))) =
          WSet.lift (((b.eval cat I).map (x ++ ·)).filter fun row => (on.eval row I).isTrue) := by
        simp [WSet.cross, WSet.filter, WSet.lift, List.filter_map, Function.comp_def]
      simp only [hms, Seam.bags, WSet.positive_lift, leftJoinRow]
      cases hE : (((b.eval cat I).map (x ++ ·)).filter fun row => (on.eval row I).isTrue).isEmpty <;>
        simp [WSet.lift]
  | .unionAll a b => by simp only [evalK, eval, eval_eq_evalK a, eval_eq_evalK b]; simp [WSet.lift]
  | .orderBy r _ => by
      simp only [evalK, eval, eval_eq_evalK r]
      exact (List.map_mergeSort (f := fun row => (row, (1 : Nat))) fun _ _ _ _ => rfl).symm
  | .distinct r => by
      simp only [evalK, eval, eval_eq_evalK r]
      have hm : List.map (·.1) (WSet.lift (r.eval cat I) : WSet Nat) = r.eval cat I := by
        simp [WSet.lift, Function.comp_def]
      rw [hm, List.filter_eq_self.mpr fun row hrow => ?_]
      · rfl
      · simp only [Seam.bags, ← WSet.lift_filter, WSet.positive_lift, Bool.not_eq_true',
          List.isEmpty_eq_false_iff, ne_eq, List.filter_eq_nil_iff, beq_iff_eq]
        exact fun h => h row (mem_dedup.mp hrow) rfl
  | .semi a b anti _ => by
      simp only [evalK, eval, eval_eq_evalK a, eval_eq_evalK b, ← WSet.lift_filter]
      congr 1
      refine List.filter_congr fun x _ => ?_
      simp [Seam.bags, WSet.positive_lift, hasMatch,
        any_eq_not_isEmpty_filter]
  | .unnest r _ => by
      simp only [evalK, eval, eval_eq_evalK r]
      simp [WSet.lift, List.flatMap_map, List.map_flatMap]

attribute [local instance] Lean.Grind.Semiring.natCast in
/-- On ordinary bags (every weight `1`), weighted evaluation over a semiring
is `Rel.eval` with the same functions: `Rel.eval_eq_evalK` with its weights
cast from `Nat` to `K`. -/
theorem Rel.evalK_lift {K : Type} [Lean.Grind.Semiring K] {I : Impl} {cat : Catalog}
    {r : Rel} (h : r.Incremental) :
    r.evalK I (fun t => (WSet.lift (cat t).rows : WSet K)) = WSet.lift (r.eval cat I) := by
  have hl : ∀ rows : Relation, (WSet.lift rows : WSet K) = (WSet.lift rows : WSet Nat).mapW Nat.cast :=
    fun rows => by
      simp only [WSet.lift, WSet.mapW, List.map_map]
      exact List.map_congr_left fun _ _ => by rw [Function.comp_apply, Lean.Grind.Semiring.natCast_one]
  have hcat : (fun t => (WSet.lift (cat t).rows : WSet K)) =
      fun t => (WSet.lift (cat t).rows : WSet Nat).mapW Nat.cast := funext fun t => hl _
  rw [hcat, ← evalK_mapW (fun a b => Lean.Grind.Semiring.natCast_mul a b)
    Lean.Grind.Semiring.natCast_one, evalK_seam (S' := Seam.bags cat I) h, eval_eq_evalK, ← hl]

end Substrait
