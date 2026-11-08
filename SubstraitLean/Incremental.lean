import SubstraitLean.WSet

/-!
# Incremental view maintenance over Z-sets

Bags cannot express deletions, so updates are modelled as **Z-sets**: rows
with signed multiplicities (DBSP, Budiu et al., VLDB 2023). A Z-set is a
weighted relation over `Int` (`WSet Int`, `SubstraitLean/WSet.lean`); adding
Z-sets is list append, and a deletion is a row with negative weight.

Equivalence is `List.Perm`. It is finer than Z-set equality (it never
cancels `+1` against `-1`), so every `Perm` result below also holds for Z-sets.

`Rel.zeval` is `Rel.evalK` over `Int` with Lean's functions
(`Rel.zeval_eq_evalK`), so `incremental_sound` and `zeval_lift` are the
`WSet` theorems at `Int`. For the incremental fragment (`Rel.Incremental`: every operator except left
join and fetch):

* `Rel.zeval_add`: evaluating on an updated database equals the old result
  plus a delta, `Q(D + ΔD) ~ Q(D) + ΔQ`.
* `Rel.delta_correct`: `Rel.delta` turns a plan into an ordinary plan that
  computes `ΔQ` from the old tables and the change tables. It can be run by
  any engine.
* `Rel.zeval_lift`: on ordinary bags (all weights 1) Z-set evaluation agrees
  with `Rel.eval`.
-/

namespace Substrait

abbrev ZSet := WSet Int

namespace ZSet

def lift (r : Relation) : ZSet := r.map (·, 1)

def filter (p : Row → Bool) (z : ZSet) : ZSet := List.filter (fun x => p x.1) z

def map (f : Row → Row) (z : ZSet) : ZSet := List.map (fun x => (f x.1, x.2)) z

/-- Weights multiply. This makes the cross product bilinear. -/
def cross (a b : ZSet) : ZSet :=
  List.flatMap (fun x => List.map (fun y => (x.1 ++ y.1, x.2 * y.2)) b) a

/-- Normal form: one entry per row with its total weight, zero weights
dropped. Only used to display and compare results. -/
def consolidate (z : ZSet) : ZSet :=
  let rows := (List.map (·.1) z).eraseDups
  List.filter (·.2 != 0)
    (List.map (fun r => (r, (List.map (·.2) (List.filter (·.1 == r) z)).sum)) rows)

theorem cross_append_left (a a' b : ZSet) : cross (a ++ a') b = cross a b ++ cross a' b :=
  WSet.cross_append_left a a' b

theorem cross_append_right (a b b' : ZSet) :
    (cross a (b ++ b')).Perm (cross a b ++ cross a b') :=
  WSet.cross_append_right a b b'

theorem cross_perm {a a' b b' : ZSet} (ha : a.Perm a') (hb : b.Perm b') :
    (cross a b).Perm (cross a' b') :=
  WSet.cross_perm ha hb

/-- The bilinear delta rule: `(A + ΔA) × (B + ΔB) ~ A × B + (ΔA × (B + ΔB) + A × ΔB)`. -/
theorem cross_add (A ΔA B ΔB : ZSet) :
    (cross (A ++ ΔA) (B ++ ΔB)).Perm (cross A B ++ (cross ΔA (B ++ ΔB) ++ cross A ΔB)) :=
  WSet.cross_add A ΔA B ΔB

end ZSet

/-- A catalog of Z-sets; `cat + Δ` applies a change set (`WCatalog`'s `+`). -/
abbrev ZCatalog := String → ZSet

theorem ZCatalog.add_apply (cat Δ : ZCatalog) (t : String) : (cat + Δ) t = cat t ++ Δ t := rfl

/-- Z-set semantics. Mirrors `Rel.eval` on the incremental fragment. -/
def Rel.zeval (cat : ZCatalog) : Rel → ZSet
  | .read t => cat t
  | .values _ rows => ZSet.lift rows
  | .filter r c => ZSet.filter (fun row => (c.eval row).isTrue) (r.zeval cat)
  | .project r es => ZSet.map (fun row => row ++ es.map (·.eval row)) (r.zeval cat)
  | .emit r m => ZSet.map (fun row => m.map (row.getD · .null)) (r.zeval cat)
  | .cross a b => ZSet.cross (a.zeval cat) (b.zeval cat)
  | .join a b .inner on =>
      ZSet.filter (fun row => (on.eval row).isTrue) (ZSet.cross (a.zeval cat) (b.zeval cat))
  | .unionAll a b => a.zeval cat ++ b.zeval cat
  | .orderBy r keys => (r.zeval cat).mergeSort fun x y => sortLe keys x.1 y.1
  -- Outside the incremental fragment; every theorem excludes these.
  | .join _ _ .left _ | .fetch _ _ _ | .window _ _ _ _ | .semi _ _ _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => []

/-- The change in a plan's output caused by the change set `Δ`. -/
def Rel.zdelta (cat Δ : ZCatalog) : Rel → ZSet
  | .read t => Δ t
  | .values _ _ => []
  | .filter r c => ZSet.filter (fun row => (c.eval row).isTrue) (r.zdelta cat Δ)
  | .project r es => ZSet.map (fun row => row ++ es.map (·.eval row)) (r.zdelta cat Δ)
  | .emit r m => ZSet.map (fun row => m.map (row.getD · .null)) (r.zdelta cat Δ)
  | .cross a b =>
      ZSet.cross (a.zdelta cat Δ) (b.zeval cat ++ b.zdelta cat Δ) ++
        ZSet.cross (a.zeval cat) (b.zdelta cat Δ)
  | .join a b .inner on =>
      ZSet.filter (fun row => (on.eval row).isTrue)
        (ZSet.cross (a.zdelta cat Δ) (b.zeval cat ++ b.zdelta cat Δ) ++
          ZSet.cross (a.zeval cat) (b.zdelta cat Δ))
  | .unionAll a b => a.zdelta cat Δ ++ b.zdelta cat Δ
  | .orderBy r keys => (r.zdelta cat Δ).mergeSort fun x y => sortLe keys x.1 y.1
  | .join _ _ .left _ | .fetch _ _ _ | .window _ _ _ _ | .semi _ _ _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => []

theorem Rel.zeval_eq_evalK {cat : ZCatalog} : ∀ r : Rel, r.zeval cat = r.evalK Impl.lean cat
  | .read _ | .values _ _ => rfl
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => by
      simp only [zeval, evalK, zeval_eq_evalK r, ZSet.filter, WSet.filter, ZSet.map, WSet.map]
  | .cross a b | .unionAll a b | .join a b .inner _ => by
      simp only [zeval, evalK, zeval_eq_evalK a, zeval_eq_evalK b, ZSet.filter, WSet.filter,
        ZSet.cross, WSet.cross]
  | .join _ _ .left _ | .fetch _ _ _ | .window _ _ _ _ | .semi _ _ _ _ | .distinct _
  | .aggregate _ _ _ | .unnest _ _ => rfl

/-- A plan only depends on the tables it reads. -/
theorem Rel.zeval_congr {C cat : ZCatalog} {r : Rel} (h : ∀ t ∈ r.tables, C t = cat t) :
    r.zeval C = r.zeval cat := by
  simpa only [zeval_eq_evalK] using evalK_congr h

/-- **Delta rule**: `Q(D + ΔD) ~ Q(D) + ΔQ`. -/
theorem Rel.zeval_add {cat Δ : ZCatalog} :
    ∀ {r : Rel}, r.Incremental → (r.zeval (cat + Δ)).Perm (r.zeval cat ++ r.zdelta cat Δ)
  | .read t, _ => by simp [zeval, zdelta, ZCatalog.add_apply]
  | .values _ _, _ => by simp [zeval, zdelta]
  | .filter r c, h => by
      simp only [zeval, zdelta, ZSet.filter, ← List.filter_append]
      exact (zeval_add (r := r) h).filter _
  | .project r es, h => by
      simp only [zeval, zdelta, ZSet.map, ← List.map_append]
      exact (zeval_add (r := r) h).map _
  | .emit r m, h => by
      simp only [zeval, zdelta, ZSet.map, ← List.map_append]
      exact (zeval_add (r := r) h).map _
  | .cross a b, h => by
      simp only [zeval, zdelta]
      exact (ZSet.cross_perm (zeval_add (r := a) h.1) (zeval_add (r := b) h.2)).trans
        (ZSet.cross_add _ _ _ _)
  | .join a b .inner on, h => by
      simp only [zeval, zdelta, ZSet.filter, ← List.filter_append]
      exact ((ZSet.cross_perm (zeval_add (r := a) h.1) (zeval_add (r := b) h.2)).trans
        (ZSet.cross_add _ _ _ _)).filter _
  | .unionAll a b, h => by
      simp only [zeval, zdelta]
      refine ((zeval_add (r := a) h.1).append (zeval_add (r := b) h.2)).trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)
  | .orderBy r _, h => by
      simp only [zeval, zdelta]
      exact (List.mergeSort_perm _ _).trans ((zeval_add (r := r) h).trans
        (List.Perm.append (List.mergeSort_perm _ _).symm (List.mergeSort_perm _ _).symm))
  | .join _ _ .left _, h => h.elim
  | .fetch _ _ _, h | .window _ _ _ _, h | .semi _ _ _ _, h | .distinct _, h
  | .aggregate _ _ _, h | .unnest _ _, h => h.elim

/-- **The delta plan computes the delta.** `C` is the engine's catalog: old
tables under their own names and change tables under `δ t`. -/
theorem Rel.delta_correct {C cat Δ : ZCatalog} {δ : String → String} :
    ∀ {r : Rel}, r.Incremental →
      (∀ t ∈ r.tables, C t = cat t) → (∀ t ∈ r.tables, C (δ t) = Δ t) →
      (r.delta δ).zeval C = r.zdelta cat Δ
  | .read t, _, _, hδ => hδ t (by simp [tables])
  | .values _ _, _, _, _ => rfl
  | .filter r _, h, hold, hδ | .project r _, h, hold, hδ | .emit r _, h, hold, hδ
  | .orderBy r _, h, hold, hδ => by
      simp only [delta, zeval, zdelta, delta_correct (r := r) h hold hδ]
  | .cross a b, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [delta, zeval, zdelta,
        delta_correct (r := a) h.1 (fun t ht => hold t (.inl ht)) (fun t ht => hδ t (.inl ht)),
        delta_correct (r := b) h.2 (fun t ht => hold t (.inr ht)) (fun t ht => hδ t (.inr ht)),
        zeval_congr (r := a) (fun t ht => hold t (.inl ht)),
        zeval_congr (r := b) (fun t ht => hold t (.inr ht))]
  | .join a b .inner _, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [delta, zeval, zdelta, ZSet.filter, List.filter_append,
        delta_correct (r := a) h.1 (fun t ht => hold t (.inl ht)) (fun t ht => hδ t (.inl ht)),
        delta_correct (r := b) h.2 (fun t ht => hold t (.inr ht)) (fun t ht => hδ t (.inr ht)),
        zeval_congr (r := a) (fun t ht => hold t (.inl ht)),
        zeval_congr (r := b) (fun t ht => hold t (.inr ht))]
  | .unionAll a b, h, hold, hδ => by
      simp only [tables, List.mem_append] at hold hδ
      simp only [delta, zeval, zdelta,
        delta_correct (r := a) h.1 (fun t ht => hold t (.inl ht)) (fun t ht => hδ t (.inl ht)),
        delta_correct (r := b) h.2 (fun t ht => hold t (.inr ht)) (fun t ht => hδ t (.inr ht))]
  | .join _ _ .left _, h, _, _ => h.elim
  | .fetch _ _ _, h, _, _ | .window _ _ _ _, h, _, _ | .semi _ _ _ _, h, _, _
  | .distinct _, h, _, _ | .aggregate _ _ _, h, _, _ | .unnest _ _, h, _, _ => h.elim

/-- **Incremental maintenance is sound**: the new result is the old result
plus the output of the delta plan. -/
theorem Rel.incremental_sound {C cat Δ : ZCatalog} {δ : String → String} {r : Rel}
    (h : r.Incremental)
    (hold : ∀ t ∈ r.tables, C t = cat t) (hδ : ∀ t ∈ r.tables, C (δ t) = Δ t) :
    (r.zeval (cat + Δ)).Perm (r.zeval cat ++ (r.delta δ).zeval C) := by
  simpa only [zeval_eq_evalK] using incrementalK_sound (I := Impl.lean) h hold hδ

/-! ## Agreement with bag semantics -/

/-- On ordinary bags (every weight `1`), Z-set evaluation is `Rel.eval`. -/
theorem Rel.zeval_lift {cat : Catalog} {r : Rel} (h : r.Incremental) :
    r.zeval (fun t => ZSet.lift (cat t).rows) = ZSet.lift (r.eval cat) := by
  rw [zeval_eq_evalK]
  exact evalK_lift h

end Substrait
