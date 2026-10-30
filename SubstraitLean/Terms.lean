import SubstraitLean.Incremental

/-!
# Splitting a plan into union-free terms

Every operator in the incremental fragment distributes over `UNION ALL`, so
a plan is equivalent to the concatenation of union-free plans (`Rel.terms`).
Engines can then run each term separately, which works around DuckDB 1.2's
Substrait consumer executing `SET_OP_UNION_ALL` as `UNION DISTINCT`.
-/

namespace Substrait

def Rel.terms : Rel → List Rel
  | .unionAll a b => a.terms ++ b.terms
  | .filter r c => r.terms.map (.filter · c)
  | .project r es => r.terms.map (.project · es)
  | .emit r m => r.terms.map (.emit · m)
  | .cross a b => a.terms.flatMap fun x => b.terms.map fun y => .cross x y
  | .join a b ty on => a.terms.flatMap fun x => b.terms.map fun y => .join x y ty on
  | r => [r]

def Rel.hasUnion : Rel → Bool
  | .unionAll _ _ => true
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ => r.hasUnion
  | .cross a b | .join a b _ _ => a.hasUnion || b.hasUnion

theorem perm_flatMap_congr {α β : Type} {L : List α} {f g : α → List β}
    (h : ∀ x ∈ L, (f x).Perm (g x)) : (L.flatMap f).Perm (L.flatMap g) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih fun y hy => h y (by simp [hy]))

theorem ZSet.cross_flatMap_left {α : Type} (L : List α) (f : α → ZSet) (B : ZSet) :
    ZSet.cross (L.flatMap f) B = L.flatMap fun x => ZSet.cross (f x) B := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, ZSet.cross_append_left, ih]

theorem ZSet.cross_flatMap_right {α : Type} (A : ZSet) (L : List α) (g : α → ZSet) :
    (ZSet.cross A (L.flatMap g)).Perm (L.flatMap fun y => ZSet.cross A (g y)) := by
  induction L with
  | nil => simp [ZSet.cross]
  | cons y L ih =>
    simp only [List.flatMap_cons]
    exact (ZSet.cross_append_right _ _ _).trans (List.Perm.append_left _ ih)

/-- Cross product of two concatenations, term by term. -/
theorem ZSet.cross_flatMap {α : Type} (L M : List α) (f : α → ZSet) :
    (ZSet.cross (L.flatMap f) (M.flatMap f)).Perm
      (L.flatMap fun x => M.flatMap fun y => ZSet.cross (f x) (f y)) := by
  rw [ZSet.cross_flatMap_left]
  exact perm_flatMap_congr fun x _ => ZSet.cross_flatMap_right _ _ _

/-- **A plan is the sum of its terms.** -/
theorem Rel.zeval_terms {Z : ZCatalog} :
    ∀ {r : Rel}, r.Incremental → (r.zeval Z).Perm (r.terms.flatMap (·.zeval Z))
  | .read _, _ | .values _ _, _ => by simp [terms]
  | .unionAll a b, h => by
      simp only [zeval, terms, List.flatMap_append]
      exact (zeval_terms (r := a) h.1).append (zeval_terms (r := b) h.2)
  | .filter r c, h => by
      simp only [zeval, terms, ZSet.filter, List.flatMap_map]
      refine ((zeval_terms (r := r) h).filter _).trans ?_
      rw [List.filter_flatMap]
  | .project r es, h => by
      simp only [zeval, terms, ZSet.map, List.flatMap_map]
      refine ((zeval_terms (r := r) h).map _).trans ?_
      rw [List.map_flatMap]
  | .emit r m, h => by
      simp only [zeval, terms, ZSet.map, List.flatMap_map]
      refine ((zeval_terms (r := r) h).map _).trans ?_
      rw [List.map_flatMap]
  | .cross a b, h => by
      simp only [zeval, terms, List.flatMap_assoc, List.flatMap_map]
      exact (ZSet.cross_perm (zeval_terms (r := a) h.1) (zeval_terms (r := b) h.2)).trans
        (ZSet.cross_flatMap _ _ _)
  | .join a b .inner on, h => by
      simp only [zeval, terms, List.flatMap_assoc, List.flatMap_map]
      refine (((ZSet.cross_perm (zeval_terms (r := a) h.1) (zeval_terms (r := b) h.2)).trans
        (ZSet.cross_flatMap _ _ _)).filter _).trans ?_
      simp only [ZSet.filter, List.filter_flatMap]
      exact List.Perm.refl _
  | .join _ _ .left _, h => h.elim
  | .fetch _ _ _, h => h.elim

end Substrait
