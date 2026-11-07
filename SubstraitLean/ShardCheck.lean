import SubstraitLean.Partition
import SubstraitLean.Write
import SubstraitLean.Check
import SubstraitLean.ContractCheck

/-!
# Splitting a plan for sharded evaluation

Input (JSON):

```json
{ "plan": <plan>, "sharded": ["<table>", ...],
  "keys": {"<table>": [<col>, ...]},   -- optional split keys, by column position
  "unique": {"<table>": [[<col>, ...], ...]},   -- optional keys of the whole tables
  "float_order": "exact" | "any" }    -- optional; "any" splits SUM/AVG of doubles
```

The sharded tables are split over the shards; every other table is broadcast
(each shard has all of it). A split key promises that rows with equal values
on those columns, in any keyed table, are on the same shard
(`Sharding.keyDisj`); the caller checks it on the data. `unique` lists
columns with no two equal rows in the whole table (checked by the caller,
like a contract's `unique`); a window splits when they show it has no ties
(`Rel.keyedWindows`, sound by `Rel.keyedWindows_sound` for rows of the
declared types). An integer `AVG` splits into a `SUM` and a `COUNT` when the
declared types make its argument an integer (`IntArgs.ofTypes`, sound by
`IntArgs.ofTypes_sound` for the same rows).

Output: `{"mode": "linear" | "two_phase", "proved": <bool>, "partial": <plan>,
"combine": <plan>}`. Run `partial` on every shard, put the concatenated
results in the table `__partials`, and `combine` gives the plan's result
(`Rel.shardSplit_sound`). For a linear plan, `combine` just reads
`__partials`. `proved` is false when `float_order: "any"` was needed: the
double `SUM`s and `AVG`s then round as the split makes them, and
`"float_bounds"` says where to read their bound (#428):

```json
{ "keys": <k>,                       -- the grouping keys, the partial rows' first columns
  "measures": [{"kind": "sum" | "avg", "abs": <col>, "count": <col>, "max": <col>}, ...],
  "columns": [{"key": <i>} | {"exact": true} | {"bounded": <j>} | {"unbounded": true}, ...],
  "filters_read_doubles": <bool> }
```

Each split double measure `j` adds `SUM(|x|)`, `COUNT(x)` and `MAX(|x|)` to the
partial rows at those columns (`floatBoundParts`); from them, per group, the
output columns `{"bounded": j}` are within `shardTolCR` (`"sum"`) or
`shardAvgTolCR` (`"avg"`) of Lean's value when Lean computes the split
(`floatSplit_sum`, `floatSplit_avg`, D25), and within `shardTolScaled` or
`shardAvgTolScaled` when an engine adds the shards in its own order
(`float-bounds/FloatBounds/Shard.lean`, whose `γ n` term covers the
reference's one rounding); `sverify.partition` reports the larger. `{"key": i}` copies grouping key `i`, `{"exact": true}`
is Lean's value, and `{"unbounded": true}` is computed from a split double
by an expression the bound does not carry over to. With
`filters_read_doubles`, a filter above the aggregate (`HAVING`) reads a split
double, so a group near its threshold may be kept on one side only.

The JSON handling, the refusal messages and the schema of `__partials` are
trusted.
-/

namespace Substrait.ShardCheck

open Lean (Json toJson)
open Parse Write

def partials : String := "__partials"

def colNames (n : Nat) : List String := (List.range n).map (s!"c{·}")

def schemaOf (ks : List Kind) : Json :=
  obj [("names", toJson (colNames ks.length)),
       ("struct", obj [("types", Json.arr (ks.map kindType).toArray),
                       ("nullability", "NULLABILITY_REQUIRED")])]

/-- Why `r` cannot be split (for the message only). -/
def why (S : String → Bool) (K : String → Option (List Nat)) (T : WindowKeys) (cat : Catalog)
    (I : IntArgs) : Rel → String
  | .read _ => "the plan reads no sharded table, so every shard would compute all of it"
  | .values _ _ => "a literal table (VALUES) would be repeated on every shard"
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => why S K T cat I r
  | .fetch _ _ _ => "FETCH (LIMIT/OFFSET) depends on the rows of all shards"
  | .unnest _ _ => "UNNEST is not split into shards yet"
  | .window r _ _ _ =>
    if !r.linear S K T cat then why S K T cat I r
    else "a window looks at rows of other shards; it splits when its PARTITION BY contains the split key (keys) and its PARTITION BY and ORDER BY columns are unique (unique), so that ties cannot fall differently"
  | .distinct r =>
    if !r.linear S K T cat then why S K T cat I r
    else "DISTINCT compares rows of different shards; it splits when its columns include the split key (keys)"
  | .aggregate r _ ms =>
    if !r.linear S K T cat then
      if (r.tables.any S) then why S K T cat I r else "the aggregate reads no sharded table"
    else match ms.find? (!·.algebraic I r (r.keyCols S K T cat)) with
      | some m =>
        if m.distinct then
          "an aggregate over DISTINCT values: a value in two shards counts once in the whole and twice in the parts, unless its argument is the split key"
        else if m.fn = .iavg then
          "an integer AVG splits into SUM and COUNT only when its argument is an integer, by the plan's column types"
        else "SUM or AVG of doubles: floating-point addition is not associative, so the rounding depends on how the rows are split (float_order=\"any\" splits them anyway, unproved)"
      | none => "only one aggregate can be split in two phases, at the top of the plan; one below other operators needs the split key in its GROUP BY"
  | .unionAll a b =>
    if !a.tables.any S || !b.tables.any S then
      "a UNION ALL branch reads no sharded table and would be repeated on every shard"
    else if a.linear S K T cat then why S K T cat I b else why S K T cat I a
  | .cross a b | .join a b _ _ =>
    if a.tables.any S && b.tables.any S then
      "a join of two sharded tables needs both split on keys its condition equates (co-partitioning: keys, and ON a.k = b.k)"
    else if a.tables.any S then why S K T cat I a else why S K T cat I b
  | .semi a b _ _ =>
    if b.tables.any S then "the right side of a semi or anti join reads a sharded table"
    else why S K T cat I a

/-- Where an output column above the split aggregate comes from. -/
inductive ColSrc where
  | key (i : Nat)
  | exact
  | bounded (j : Nat)
  /-- Computed from a split double. -/
  | unbounded

def ColSrc.double : ColSrc → Bool
  | .bounded _ | .unbounded => true
  | _ => false

def ColSrc.toJson : ColSrc → Json
  | .key i => obj [("key", Lean.toJson i)]
  | .exact => obj [("exact", Lean.toJson true)]
  | .bounded j => obj [("bounded", Lean.toJson j)]
  | .unbounded => obj [("unbounded", Lean.toJson true)]

/-- The columns an expression reads (a lambda's body reads its parameter). -/
def reads : Expr → List Nat
  | .lit _ => []
  | .field i => [i]
  | .un _ a => reads a
  | .bin _ a b => reads a ++ reads b
  | .ifThen c t e => reads c ++ reads t ++ reads e
  | .hof _ l _ => reads l

/-- An expression's source: a copy of a column keeps it; anything else is
exact unless it reads a split double. -/
def exprSrc (srcs : List ColSrc) : Expr → ColSrc
  | .field i => srcs.getD i .exact
  | e => if (reads e).any fun i => (srcs.getD i .exact).double then .unbounded else .exact

/-- The split double measures' indices among `ms`, in order. -/
def doubleIdx (ms : List Measure) : List Nat :=
  ms.zipIdx.filterMap fun (m, i) => if m.fn = .fsum ∨ m.fn = .avg then some i else none

/-- The output columns' sources above the aggregate `splitAgg` splits, and
whether a filter there reads a split double. -/
def colSrcs : Rel → Option (List ColSrc × Bool)
  | .aggregate _ gs ms =>
    let ds := doubleIdx ms
    some ((List.range gs.length).map .key ++ (List.range ms.length).map fun i =>
      match ds.idxOf? i with
      | some j => .bounded j
      | none => .exact, false)
  | .filter r c => (colSrcs r).map fun (srcs, f) =>
      (srcs, f || (reads c).any fun i => (srcs.getD i .exact).double)
  | .project r es => (colSrcs r).map fun (srcs, f) => (srcs ++ es.map (exprSrc srcs), f)
  | .emit r m => (colSrcs r).map fun (srcs, f) => (m.map (srcs.getD · .exact), f)
  | .orderBy r _ => colSrcs r
  | _ => none

/-- The split aggregate's grouping keys and measures. -/
def splitAggregate : Rel → Option (Nat × List Measure)
  | .aggregate _ gs ms => some (gs.length, ms)
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => splitAggregate r
  | _ => none

/-- Where the bound of each split double measure is read (`floatBoundParts`):
after the keys and `floatPartial`'s columns, three columns per measure. -/
def floatBounds (root : Rel) : Option Json := do
  let (k, ms) ← splitAggregate root
  let (srcs, f) ← colSrcs root
  let base := k + (ms.flatMap floatPartial).length
  let doubles := ms.filter fun m => m.fn = .fsum ∨ m.fn = .avg
  let measures := doubles.zipIdx.map fun (m, j) =>
    obj [("kind", Lean.toJson (if m.fn = .avg then "avg" else "sum")),
      ("abs", Lean.toJson (base + 3 * j)), ("count", Lean.toJson (base + 3 * j + 1)),
      ("max", Lean.toJson (base + 3 * j + 2))]
  return obj [("keys", Lean.toJson k), ("measures", Json.arr measures.toArray),
    ("columns", Json.arr (srcs.map ColSrc.toJson).toArray),
    ("filters_read_doubles", Lean.toJson f)]

def check (input : Json) : Except String Json := do
  let plan ← parsePlan ((input.getObjVal? "plan").toOption.getD .null).compress
  let sharded := ((input.getObjValAs? (Array String) "sharded").toOption.getD #[]).toList
  let S : String → Bool := (sharded.contains ·)
  let keyJson := (input.getObjVal? "keys").toOption.getD (Json.mkObj [])
  let K : String → Option (List Nat) := fun t =>
    (keyJson.getObjVal? t).toOption.bind fun j => (j.getArr?).toOption.map fun cs =>
      cs.toList.filterMap fun c => (c.getNat?).toOption
  let floats := (input.getObjValAs? String "float_order").toOption == some "any"
  let cat := plan.catalog
  let uniqueJson := (input.getObjVal? "unique").toOption.getD (Json.mkObj [])
  let U : String → List (List Nat) := fun t => ContractCheck.natLists
    ((uniqueJson.getObjVal? t).toOption.getD (.arr #[]))
  let A : String → List AVal := fun t => match plan.tables.lookup t with
    | some (_, schema) => ContractCheck.schemaEnv schema
    | none => []
  let T := Rel.keyedWindows cat A (fun _ => []) U
  let I := IntArgs.ofTypes cat A
  -- `Rel.shardSplit_sound` is stated for well-formed plans' semantics; the
  -- combining plan must read only `__partials`.
  if !plan.root.checkWF cat then throw "the plan is not well-formed"
  if plan.tables.any (·.1 == partials) then throw s!"the plan reads a table named {partials}"
  for t in sharded do
    if let some kt := K t then
      if kt.isEmpty || kt.any (· ≥ (cat t).arity) then
        throw s!"the split key of {t} must name columns of it"
  match plan.root.shardSplit S K T cat I partials floats with
  | none => throw (why S K T cat I plan.root)
  | some (p, q) =>
    let schemas := planSchemas plan
    let pk := (relKinds schemas cat p).map WKind.toKind
    let cat' : Catalog := fun t => if t == partials then ⟨pk.length, []⟩ else cat t
    let schemas' : Schemas := fun t n => if t == partials then schemaOf pk else schemas t n
    let linear := plan.root.linear S K T cat
    let proved := (plan.root.shardSplit S K T cat I partials false).isSome
    let bounds := if proved then [] else match floatBounds plan.root with
      | some j => [("float_bounds", j)]
      | none => []
    return Json.mkObj ([
      ("mode", toJson (if linear then "linear" else "two_phase")),
      ("proved", toJson proved),
      ("partial", writePlan schemas cat p (if linear then plan.names else colNames pk.length)),
      ("combine", writePlan schemas' cat' q plan.names)] ++ bounds)

end Substrait.ShardCheck
