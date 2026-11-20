import Sverify.Analysis.Contracts.Facts

/-!
# As-of join sites (#1447, ruling 162 A2 and A7)

An as-of join is no node of its own: the core states it as a range join, a
ranking and a filter (`sverify.asof.asof_join` builds that plan, and the SQL
lift reads DuckDB's `ASOF JOIN` as one). Its range join compares each left
row with every right row of its key group, so its cost is quadratic in the
rows. `Rel.asofSite` recognises the shape; it names no engine.

* The site keeps the nodes above the join (`AsofSite.layers`) and the join's
  parts as they are, and reads the keys and the `on` columns off the join's
  condition. `Rel.asofSite_sound`: the site rebuilds the plan it came from.
* `AsofSite.pairs` is the count of the pairs the range join compares, a plan
  of one row: per key group, the left rows times the right rows, summed. A
  run evaluates it first and refuses the join above the cap `asof_join`
  states (`max_pairs`), whatever the rows come from. It is `asof.pairs` as a
  plan (`python/src/sverify/asof.py`).

The recognition is a test of the shape, not a statement about engines. An
engine that runs a site natively (DuckDB's `ASOF JOIN`, ruling 162 A) builds
on it with a fact of its own.
-/

namespace Substrait

/-- A node above a join, without its input. -/
inductive AsofLayer where
  | emit (mapping : List Nat)
  | project (exprs : List Expr)
  | window (part : List Nat) (sort : List SortKey) (fns : List WinFn)
  | filter (cond : Expr)
  deriving Repr

/-- `layers`, outermost first, over `r`. -/
def AsofLayer.apply : List AsofLayer → Rel → Rel
  | [], r => r
  | .emit m :: ls, r => .emit (apply ls r) m
  | .project es :: ls, r => .project (apply ls r) es
  | .window p s f :: ls, r => .window (apply ls r) p s f
  | .filter c :: ls, r => .filter (apply ls r) c

/-- The emits, projections, windows and filters at the top of a plan,
outermost first, and the node below them. -/
def Rel.peel : Rel → List AsofLayer × Rel
  | .emit r m => (.emit m :: r.peel.1, r.peel.2)
  | .project r es => (.project es :: r.peel.1, r.peel.2)
  | .window r p s f => (.window p s f :: r.peel.1, r.peel.2)
  | .filter r c => (.filter c :: r.peel.1, r.peel.2)
  | r => ([], r)

/-- Peeling a plan and putting the layers back gives the plan. -/
theorem Rel.peel_apply (r : Rel) : AsofLayer.apply r.peel.1 r.peel.2 = r := by
  induction r <;> simp_all [Rel.peel, AsofLayer.apply]

/-- An as-of join: the nodes above its range join, the join's two inputs,
type and condition as they are, and what the condition says. -/
structure AsofSite where
  /-- The emits, projections, windows and filters above the join, outermost
  first: the ranking of each left row's matches and the filter on it. -/
  layers : List AsofLayer
  /-- The join's left input: the left rows, numbered. -/
  numbered : Rel
  right : Rel
  type : JoinType
  /-- The join's condition, as written. -/
  on : Expr
  /-- The equalities of the condition: a column of `numbered`, one of
  `right` (in its own numbering). -/
  keys : List (Nat × Nat)
  /-- `right.ron ≤ numbered.lon`, written `NOT (lon < n + ron)`. -/
  lon : Nat
  ron : Nat
  /-- The other conjuncts, such as a tolerance (`on - tolerance <= right.on`). -/
  rest : List Expr
  deriving Repr

/-- The plan the site stands for. -/
def AsofSite.toRel (s : AsofSite) : Rel :=
  AsofLayer.apply s.layers (.join s.numbered s.right s.type s.on)

/-- A key conjunct: `left col = right col`, either way round, `n` the left
side's arity. -/
def Expr.asofKey (n : Nat) : Expr → Option (Nat × Nat)
  | .bin .eq (.field a) (.field b) =>
    if a < n && n ≤ b then some (a, b - n)
    else if b < n && n ≤ a then some (b, a - n) else none
  | _ => none

/-- The `on` conjunct: `NOT (left on < right on)`. -/
def Expr.asofOn (n : Nat) : Expr → Option (Nat × Nat)
  | .un .not (.bin .lt (.field a) (.field b)) => if a < n && n ≤ b then some (a, b - n) else none
  | _ => none

/-- A `ROW_NUMBER` window whose input rows are its only function's. -/
def AsofLayer.isRowNumber : AsofLayer → Bool
  | .window _ _ [.rowNumber] => true
  | _ => false

/-- The ranking of a left row's matches: `ROW_NUMBER` with one sort key,
latest first. -/
def AsofLayer.isLatestFirst : AsofLayer → Bool
  | .window _ [k] [.rowNumber] => k.desc
  | _ => false

def AsofLayer.isFilter : AsofLayer → Bool
  | .filter _ => true
  | _ => false

/-- What an as-of join's parts say, or none where they are no as-of join:
the left input numbers its rows (`ROW_NUMBER` under emits and
projections), the condition is equalities of a left and a right column and
exactly one `NOT (left on < right on)`, and above the join a `ROW_NUMBER`
ranks the matches latest first and a filter keeps the first. -/
def asofParts (cat : Catalog) (layers : List AsofLayer) (l : Rel) (on : Expr) :
    Option (List (Nat × Nat) × Nat × Nat × List Expr) := do
  let n := l.arity cat
  guard (l.peel.1.any (·.isRowNumber))
  guard (layers.any (·.isLatestFirst) && layers.any (·.isFilter))
  let cs := on.conjuncts
  let (lon, ron) ← match cs.filterMap (Expr.asofOn n) with
    | [p] => some p
    | _ => none
  let keys := cs.filterMap (Expr.asofKey n)
  let rest := cs.filter fun c => (c.asofKey n).isNone && (c.asofOn n).isNone
  some (keys, lon, ron, rest)

/-- **The as-of join at the top of a plan**, under its ranking and filter;
none where the plan is no as-of join. -/
def Rel.asofSite (cat : Catalog) (r : Rel) : Option AsofSite :=
  match r.peel with
  | (layers, .join l rt ty on) =>
    (asofParts cat layers l on).map fun (keys, lon, ron, rest) =>
      { layers, numbered := l, right := rt, type := ty, on, keys, lon, ron, rest }
  | _ => none

/-- A site rebuilds the plan it was read from. -/
theorem Rel.asofSite_sound {cat : Catalog} {r : Rel} {s : AsofSite}
    (h : r.asofSite cat = some s) : s.toRel = r := by
  unfold Rel.asofSite at h
  split at h
  · rename_i layers l rt ty on hp
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
    have := Rel.peel_apply r
    rw [hp] at this
    exact this
  · simp at h

/-- Which builder's shape a site has, read off how its left input numbers
its rows: `asof.py`'s numbers all rows in one order (`builder`), the
lift's numbers each row among its duplicates (`lift`); `other` for any
other numbering. A writer that states a site's output per shape reads it. -/
inductive AsofForm where
  | builder | lift | other
  deriving Repr, BEq

def AsofForm.name : AsofForm → String
  | .builder => "builder"
  | .lift => "lift"
  | .other => "other"

/-- The site's shape (`AsofForm`). -/
def AsofSite.form (s : AsofSite) : AsofForm :=
  match s.numbered.peel.1.find? (·.isRowNumber) with
  | some (.window [] (_ :: _) _) => .builder
  | some (.window (_ :: _) [] _) => .lift
  | _ => .other

/-- The as-of sites at every node of a plan, outermost first, each with the
path to its node from the plan's root (0 for a node's input or a join's
left side, 1 for the right side). A site is read again at each layer above
its join, so `Rel.asofSites` keeps one per join. -/
def Rel.asofSitesAt (cat : Catalog) (path : List Nat) : Rel → List (List Nat × AsofSite)
  | r@(.project i _) | r@(.emit i _) | r@(.window i ..) | r@(.filter i _) =>
    ((r.asofSite cat).toList.map (path, ·)) ++ i.asofSitesAt cat (path ++ [0])
  | .fetch i _ _ | .orderBy i _ | .distinct i | .aggregate i _ _ | .unnest i _ =>
    i.asofSitesAt cat (path ++ [0])
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
    a.asofSitesAt cat (path ++ [0]) ++ b.asofSitesAt cat (path ++ [1])
  | .read _ | .values _ _ => []

/-- The as-of joins of a plan, outermost first, one per join, at the path of
its outermost layer: the node whose plan the site rebuilds. -/
def Rel.asofSites (cat : Catalog) (r : Rel) : List (List Nat × AsofSite) :=
  (r.asofSitesAt cat []).foldl (fun acc (p, s) =>
    if acc.any fun (_, t) => t.numbered == s.numbered && t.right == s.right && t.on == s.on
    then acc else acc ++ [(p, s)]) []

/-- The rows of `r` per value of its columns `cols`: those columns, then the
count. -/
def countBy (r : Rel) (cols : List Nat) : Rel :=
  .aggregate r (cols.map .field) [{ fn := .count, arg := .lit (.int 1) }]

/-- `a₀ = b₀ AND … AND TRUE`. -/
def eqAll : List (Nat × Nat) → Expr
  | [] => .lit (.bool true)
  | (a, b) :: ps => .bin .and (.bin .eq (.field a) (.field b)) (eqAll ps)

/-- **The pairs the range join compares**: per key group, the left rows times
the right rows, summed; one row of one integer (NULL where no group has rows
on both sides, which is none). A NULL key matches nothing, as in the join. -/
def AsofSite.pairs (s : AsofSite) : Rel :=
  let k := s.keys.length
  let l := countBy s.numbered (s.keys.map (·.1))
  let r := countBy s.right (s.keys.map (·.2))
  let on := eqAll ((List.range k).map fun i => (i, k + 1 + i))
  .aggregate (.join l r .inner on) [] [{ fn := .sum, arg := .bin .mul (.field k) (.field (2 * k + 1)) }]

end Substrait
