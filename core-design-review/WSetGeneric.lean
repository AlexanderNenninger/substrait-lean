import SubstraitLean.Value

/-!
Prototype for #905: how much of `ZSet.cross_add` (the bilinear delta rule
behind `Rel.delta_correct`) needs the weight semiring's laws?

Answer tested here: none. The list-level statement is a `Perm` of weighted
lists whose weights are formed by `*` pointwise, so it holds for any weight
type with a `Mul`. The semiring laws (`CSemiring` in #905) are needed only
once lists are read as K-relations (weights summed per row: `consolidate`,
`weight`), i.e. for `evalK_lift`, `distinct`, aggregates and difference,
never for the positive fragment's delta plan.

Consequence: `Rel.lineage` over ℤ[X] (provenance polynomials with integer
coefficients) gets `delta_correct` for free, so provenance of *deltas*
(which source rows added or removed an output row) is a corollary, not new
proof work. -/

namespace Substrait

abbrev WSet (K : Type) := List (Row × K)

namespace WSet
variable {K : Type} [Mul K]

def lift [One K] (r : Relation) : WSet K := r.map (·, 1)

def filter (p : Row → Bool) (z : WSet K) : WSet K := List.filter (fun x => p x.1) z

def map (f : Row → Row) (z : WSet K) : WSet K := List.map (fun x => (f x.1, x.2)) z

/-- Weights multiply: the cross product is bilinear in list append. -/
def cross (a b : WSet K) : WSet K :=
  List.flatMap (fun x => List.map (fun y => (x.1 ++ y.1, x.2 * y.2)) b) a

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

/-- The bilinear delta rule, for any weight type with a `Mul`:
`(A + ΔA) × (B + ΔB) ~ A × B + (ΔA × (B + ΔB) + A × ΔB)`. -/
theorem cross_add (A ΔA B ΔB : WSet K) :
    (cross (A ++ ΔA) (B ++ ΔB)).Perm (cross A B ++ (cross ΔA (B ++ ΔB) ++ cross A ΔB)) := by
  rw [cross_append_left]
  refine ((cross_append_right A B ΔB).append_right _).trans ?_
  simp only [List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

end WSet

/-! ## ℤ[X] as a weight type: provenance polynomials with integer coefficients

A monomial is a multiset of source-row ids (table, position); a polynomial
a list of (coefficient, monomial). Product is pairwise; this is the free
commutative ring on the ids, read up to `Perm` at both levels and
consolidation. Only `Mul` is needed for `cross_add`; the ring laws enter
with `consolidate`. -/

abbrev RowId := String × Nat
abbrev Monomial := List RowId
abbrev ZPoly := List (Int × Monomial)

instance : Mul ZPoly := ⟨fun p q => p.flatMap fun (c, m) => q.map fun (d, n) => (c * d, m ++ n)⟩
instance : One ZPoly := ⟨[(1, [])]⟩
instance : Add ZPoly := ⟨(· ++ ·)⟩
instance : Zero ZPoly := ⟨[]⟩

/-- A source table's rows annotated with their own ids: the catalog of a
provenance evaluation. A change table's rows carry `-x` for a delete. -/
def ZPoly.ofTable (t : String) (rows : Relation) : WSet ZPoly :=
  rows.zipIdx.map fun (row, i) => (row, [(1, [(t, i)])])

def ZPoly.ofDelta (t : String) (inserts deletes : Relation) : WSet ZPoly :=
  (inserts.zipIdx.map fun (row, i) => (row, [((1 : Int), [(t ++ "+", i)])])) ++
  (deletes.zipIdx.map fun (row, i) => (row, [((-1 : Int), [(t ++ "-", i)])]))

/-- The delta rule specialised to provenance polynomials: typechecks with
no ring law. -/
example (A ΔA B ΔB : WSet ZPoly) :
    (WSet.cross (A ++ ΔA) (B ++ ΔB)).Perm
      (WSet.cross A B ++ (WSet.cross ΔA (B ++ ΔB) ++ WSet.cross A ΔB)) :=
  WSet.cross_add A ΔA B ΔB

/-- And to `Int` (today's `ZSet`) and `Nat` (bags). -/
example (A ΔA B ΔB : WSet Int) :
    (WSet.cross (A ++ ΔA) (B ++ ΔB)).Perm
      (WSet.cross A B ++ (WSet.cross ΔA (B ++ ΔB) ++ WSet.cross A ΔB)) :=
  WSet.cross_add A ΔA B ΔB

example (A ΔA B ΔB : WSet Nat) :
    (WSet.cross (A ++ ΔA) (B ++ ΔB)).Perm
      (WSet.cross A B ++ (WSet.cross ΔA (B ++ ΔB) ++ WSet.cross A ΔB)) :=
  WSet.cross_add A ΔA B ΔB

/-- A worked example: one inserted left row joins two right rows; the
delta's provenance names the inserted row and each right partner, with
coefficient +1; a deleted right row gives coefficient −1. -/
def exL : WSet ZPoly := ZPoly.ofTable "L" [[.int 1]]
def exR : WSet ZPoly := ZPoly.ofTable "R" [[.int 1, .str "a"], [.int 1, .str "b"]]
def exΔL : WSet ZPoly := ZPoly.ofDelta "L" [[.int 1]] []
def exΔR : WSet ZPoly := ZPoly.ofDelta "R" [] [[.int 1, .str "b"]]

#eval WSet.cross exΔL (exR ++ exΔR) ++ WSet.cross exL exΔR

end Substrait
