import SubstraitLean.Aggregate

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
| `JoinRel` (`LEFT_SEMI`, `LEFT_ANTI`) | `Rel.semi`            |
| `SortRel`                         | `Rel.orderBy`            |
| `AggregateRel` without measures   | `Rel.distinct`           |
| `AggregateRel` (one grouping set) | `Rel.aggregate`          |
| `FetchRel`                        | `Rel.fetch`              |
| `SetRel` (`UNION_ALL`)            | `Rel.unionAll`           |
| `windowFunction` in a `ProjectRel`| `Rel.window`             |
| `ExtensionSingleRel` (`sverify.Unnest`) | `Rel.unnest`       |

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
  /-- Window functions over one `PARTITION BY … ORDER BY …`, appended as columns. -/
  | window (input : Rel) (part : List Nat) (sort : List SortKey) (fns : List WinFn)
  /-- The left rows with some (`anti`: no) right row satisfying `on`. -/
  | semi (left right : Rel) (anti : Bool) (on : Expr)
  /-- `ORDER BY`: a stable sort. -/
  | orderBy (input : Rel) (keys : List SortKey)
  /-- `DISTINCT`: the first occurrence of every row. -/
  | distinct (input : Rel)
  /-- `GROUP BY groups`, appending one column per measure (see
  `SubstraitLean/Aggregate.lean`). -/
  | aggregate (input : Rel) (groups : List Expr) (measures : List Measure)
  /-- `UNNEST` of the list in column `col`: one row per element, in its place
  (no standard Substrait relation; see `docs/nested-values.md`). -/
  | unnest (input : Rel) (col : Nat)
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
  | .window r _ _ fns => r.arity cat + fns.length
  | .semi a _ _ _ => a.arity cat
  | .orderBy r _ | .distinct r | .unnest r _ => r.arity cat
  | .aggregate _ gs ms => gs.length + ms.length

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
  | .window r part sort fns => r.WF cat ∧ (∀ i ∈ part, i < r.arity cat) ∧
      (∀ k ∈ sort, k.col < r.arity cat) ∧ ∀ f ∈ fns, f.refsLt (r.arity cat) = true
  | .semi a b _ on => a.WF cat ∧ b.WF cat ∧ on.refsLt (a.arity cat + b.arity cat)
  | .orderBy r keys => r.WF cat ∧ ∀ k ∈ keys, k.col < r.arity cat
  | .distinct r => r.WF cat
  | .aggregate r gs ms => r.WF cat ∧ (∀ g ∈ gs, g.refsLt (r.arity cat)) ∧
      ∀ m ∈ ms, m.refsLt (r.arity cat)
  | .unnest r c => r.WF cat ∧ c < r.arity cat

def crossRows (xs ys : Relation) : Relation :=
  xs.flatMap fun x => ys.map (x ++ ·)

/-- Left outer join, one left row at a time: matching rows, or the left row
padded with nulls when nothing matches. -/
def leftJoinRow (on : Expr) (rightArity : Nat) (ys : Relation) (x : Row) : Relation :=
  let ms := (ys.map (x ++ ·)).filter fun row => (on.eval row).isTrue
  if ms.isEmpty then [x ++ List.replicate rightArity .null] else ms

/-- `UNNEST` on one row: a row per element of the list in column `c`, with
the element in its place; none for an empty list or NULL (as DataFusion and
DuckDB do; Polars' `explode` gives a row of NULL instead). -/
def unnestRow (c : Nat) (x : Row) : Relation :=
  match x.getD c .null with
  | .list vs => vs.map (x.set c ·)
  | _ => []

theorem mem_unnestRow {c : Nat} {x row : Row} :
    row ∈ unnestRow c x → ∃ vs v, x.getD c .null = .list vs ∧ v ∈ vs ∧ row = x.set c v := by
  unfold unnestRow
  split
  · rename_i vs h
    simp only [List.mem_map]
    rintro ⟨v, hv, rfl⟩
    exact ⟨vs, v, h, hv, rfl⟩
  · simp

/-- Does some row of `ys` satisfy `on` next to `x`? -/
def hasMatch (on : Expr) (ys : Relation) (x : Row) : Bool :=
  ys.any fun y => (on.eval (x ++ y)).isTrue

/-- Denotational semantics. `FetchRel` takes rows in list order; real engines
only promise this after a `SortRel`, so theorems about `fetch` hold for one
particular (deterministic) choice. Likewise `SortRel` is stable here, while
engines may order ties either way. -/
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
  | .window r part sort fns => windowEval part sort fns (r.eval cat)
  | .semi a b anti on => (a.eval cat).filter fun x => hasMatch on (b.eval cat) x != anti
  | .orderBy r keys => (r.eval cat).mergeSort (sortLe keys)
  | .distinct r => dedup (r.eval cat)
  | .aggregate r gs ms => aggregateEval gs ms (r.eval cat)
  | .unnest r c => (r.eval cat).flatMap (unnestRow c)

/-- Bag equivalence of plans: same rows with the same multiplicities, on
every catalog. -/
def Rel.Equiv (r₁ r₂ : Rel) : Prop :=
  ∀ cat, (r₁.eval cat).Perm (r₂.eval cat)

@[inherit_doc] infix:50 " ≈ᵣ " => Rel.Equiv

/-! ## Keys -/

def keyOf (k : List Nat) (row : Row) : List Value := k.map (row.getD · .null)

/-- No two rows (at different positions) agree on the columns `k`. -/
def KeyOn (k : List Nat) (rows : Relation) : Prop :=
  rows.Pairwise fun r s => keyOf k r ≠ keyOf k s

/-- Which windows `Rel.window r part sort _` have a key of `r` among their
partition and sort columns. The fact analysis takes this as an oracle (it is
computed from `Rel.keys`, which itself uses the fact analysis). -/
abbrev WindowKeys := Rel → List Nat → List SortKey → Bool

def WindowKeys.Sound (T : WindowKeys) (cat : Catalog) : Prop :=
  ∀ r part sort, T r part sort = true → r.WF cat → KeyOn (part ++ sort.map (·.col)) (r.eval cat)

def WindowKeys.none : WindowKeys := fun _ _ _ => false

theorem WindowKeys.none_sound (cat : Catalog) : WindowKeys.none.Sound cat :=
  fun _ _ _ h => by simp [WindowKeys.none] at h

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
  | .window r _ _ _, hwf, row, h => by
      obtain ⟨_, x, _, _, hx, rfl⟩ := mem_windowEval h
      simp [arity, eval_arity hcat hwf.1 x hx]
  | .semi a _ _ _, hwf, row, h => by
      simp only [eval, List.mem_filter] at h
      exact eval_arity hcat hwf.1 row h.1
  | .orderBy r _, hwf, row, h => by
      simp only [eval, List.mem_mergeSort] at h
      exact eval_arity hcat hwf.1 row h
  | .distinct r, hwf, row, h => by
      simp only [eval, mem_dedup] at h
      exact eval_arity hcat (r := r) hwf row h
  | .aggregate _ _ _, _, _, h => aggregateEval_length h
  | .unnest r _, hwf, row, h => by
      simp only [eval, List.mem_flatMap] at h
      obtain ⟨x, hx, h⟩ := h
      obtain ⟨_, _, _, _, rfl⟩ := mem_unnestRow h
      simp [arity, eval_arity hcat hwf.1 x hx]

end Substrait
