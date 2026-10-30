import SubstraitLean.Expr

/-!
# Relational operators

Models a fragment of Substrait's `Rel` message:

| Substrait                         | Here                     |
|-----------------------------------|--------------------------|
| `ReadRel` (named table)           | `Rel.read`               |
| `ReadRel` (`virtual_table`)       | `Rel.values`             |
| `FilterRel`                       | `Rel.filter`             |
| `ProjectRel`                      | `Rel.project`            |
| `RelCommon.emit.output_mapping`   | `Rel.emit`               |
| `CrossRel`                        | `Rel.cross`              |
| `JoinRel` (`INNER`, `LEFT`)       | `Rel.join`               |
| `FetchRel`                        | `Rel.fetch`              |
| `SetRel` (`UNION_ALL`)            | `Rel.unionAll`           |

Two Substrait-specific details are kept on purpose:

* `ProjectRel` *appends* its expressions to the input columns; narrowing
  happens through `emit`. We model `emit` as its own node rather than as a
  field on every relation.
* Field references are positional, so schemas are just arities.
-/

namespace Substrait

structure Table where
  arity : Nat
  rows : Relation

/-- Named tables. Unknown names resolve to an empty, zero-column table. -/
abbrev Catalog := String → Table

def Catalog.WF (cat : Catalog) : Prop :=
  ∀ t, ∀ row ∈ (cat t).rows, row.length = (cat t).arity

inductive JoinType where
  | inner | left
  deriving Repr, DecidableEq

inductive Rel where
  | read (table : String)
  | values (arity : Nat) (rows : Relation)
  | filter (input : Rel) (cond : Expr)
  | project (input : Rel) (exprs : List Expr)
  | emit (input : Rel) (mapping : List Nat)
  | cross (left right : Rel)
  | join (left right : Rel) (type : JoinType) (on : Expr)
  | fetch (input : Rel) (offset : Nat) (count : Option Nat)
  | unionAll (a b : Rel)
  deriving Repr, BEq

/-- Output arity (the length of the output schema). -/
def Rel.arity (cat : Catalog) : Rel → Nat
  | .read t => (cat t).arity
  | .values n _ => n
  | .filter r _ => r.arity cat
  | .project r es => r.arity cat + es.length
  | .emit _ m => m.length
  | .cross a b => a.arity cat + b.arity cat
  | .join a b _ _ => a.arity cat + b.arity cat
  | .fetch r _ _ => r.arity cat
  | .unionAll a _ => a.arity cat

/-- Static well-formedness: every field reference is in range, literal
tables are rectangular, and union inputs agree on arity. -/
def Rel.WF (cat : Catalog) : Rel → Prop
  | .read _ => True
  | .values n rows => ∀ row ∈ rows, row.length = n
  | .filter r c => r.WF cat ∧ c.refsLt (r.arity cat)
  | .project r es => r.WF cat ∧ ∀ e ∈ es, e.refsLt (r.arity cat)
  | .emit r m => r.WF cat ∧ ∀ i ∈ m, i < r.arity cat
  | .cross a b => a.WF cat ∧ b.WF cat
  | .join a b _ on => a.WF cat ∧ b.WF cat ∧ on.refsLt (a.arity cat + b.arity cat)
  | .fetch r _ _ => r.WF cat
  | .unionAll a b => a.WF cat ∧ b.WF cat ∧ a.arity cat = b.arity cat

def crossRows (xs ys : Relation) : Relation :=
  xs.flatMap fun x => ys.map (x ++ ·)

/-- Left outer join, one left row at a time: matching rows, or the left row
padded with nulls when nothing matches. -/
def leftJoinRow (on : Expr) (rightArity : Nat) (ys : Relation) (x : Row) : Relation :=
  let ms := (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue
  if ms.isEmpty then [x ++ List.replicate rightArity .null] else ms

/-- Denotational semantics. `FetchRel` takes rows in list order; real engines
only promise this after a `SortRel`, so theorems about `fetch` hold for one
particular (deterministic) choice. -/
def Rel.eval (cat : Catalog) : Rel → Relation
  | .read t => (cat t).rows
  | .values _ rows => rows
  | .filter r c => (r.eval cat).filter fun row => (c.eval row).isTrue
  | .project r es => (r.eval cat).map fun row => row ++ es.map (·.eval row)
  | .emit r m => (r.eval cat).map fun row => m.map (row.getD · .null)
  | .cross a b => crossRows (a.eval cat) (b.eval cat)
  | .join a b .inner on =>
      (crossRows (a.eval cat) (b.eval cat)).filter fun row => (on.eval row).isTrue
  | .join a b .left on =>
      (a.eval cat).flatMap (leftJoinRow on (b.arity cat) (b.eval cat))
  | .fetch r off cnt =>
      let rest := (r.eval cat).drop off
      match cnt with
      | none => rest
      | some n => rest.take n
  | .unionAll a b => a.eval cat ++ b.eval cat

/-- Bag equivalence of plans: same rows with the same multiplicities, on
every catalog. -/
def Rel.Equiv (r₁ r₂ : Rel) : Prop :=
  ∀ cat, (r₁.eval cat).Perm (r₂.eval cat)

@[inherit_doc] infix:50 " ≈ᵣ " => Rel.Equiv

/-! ## Type soundness -/

theorem mem_crossRows {xs ys : Relation} {row : Row} :
    row ∈ crossRows xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, row = x ++ y := by
  simp [crossRows, eq_comm]

/-- **Soundness of `Rel.arity`**: on a well-formed catalog, every row a
well-formed plan produces has exactly the predicted number of columns. -/
theorem Rel.eval_arity {cat : Catalog} (hcat : cat.WF) :
    ∀ {r : Rel}, r.WF cat → ∀ row ∈ r.eval cat, row.length = r.arity cat
  | .read t, _, row, h => hcat t row h
  | .values _ _, hwf, row, h => hwf row h
  | .filter r _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact eval_arity hcat hwf.1 row h.1
  | .project r es, hwf, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp [arity, eval_arity hcat hwf.1 x hx]
  | .emit _ _, _, row, h => by
      simp only [eval, List.mem_map] at h
      obtain ⟨x, _, rfl⟩ := h
      simp [arity]
  | .cross a b, hwf, row, h => by
      simp only [eval, mem_crossRows] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      simp [arity, eval_arity hcat hwf.1 x hx, eval_arity hcat hwf.2 y hy]
  | .join a b .inner _, hwf, row, h => by
      simp only [eval, List.mem_filter, mem_crossRows] at h
      obtain ⟨⟨x, hx, y, hy, rfl⟩, _⟩ := h
      simp [arity, eval_arity hcat hwf.1 x hx, eval_arity hcat hwf.2.1 y hy]
  | .join a b .left on, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      have hxl := eval_arity hcat hwf.1 x hx
      unfold leftJoinRow at h
      simp only [] at h
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        simp [arity, hxl]
      · simp only [List.mem_filter, List.mem_map] at h
        obtain ⟨⟨y, hy, rfl⟩, _⟩ := h
        simp [arity, hxl, eval_arity hcat hwf.2.1 y hy]
  | .fetch r off cnt, hwf, row, h => by
      simp only [eval] at h
      have := eval_arity hcat (r := r) hwf
      split at h
      · exact this row (List.mem_of_mem_drop h)
      · exact this row (List.mem_of_mem_drop (List.mem_of_mem_take h))
  | .unionAll a b, hwf, row, h => by
      simp only [eval, List.mem_append] at h
      rcases h with h | h
      · exact eval_arity hcat hwf.1 row h
      · simp only [arity, hwf.2.2]; exact eval_arity hcat hwf.2.1 row h

end Substrait
