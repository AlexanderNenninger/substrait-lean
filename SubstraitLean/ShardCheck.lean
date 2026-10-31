import SubstraitLean.Partition
import SubstraitLean.Write
import SubstraitLean.Check

/-!
# Splitting a plan for sharded evaluation

Input (JSON):

```json
{ "plan": <plan>, "sharded": ["<table>", ...],
  "keys": {"<table>": [<col>, ...]},   -- optional split keys, by column position
  "float_order": "exact" | "any" }    -- optional; "any" splits SUM/AVG of doubles
```

The sharded tables are split over the shards; every other table is broadcast
(each shard has all of it). A split key promises that rows with equal values
on those columns, in any keyed table, are on the same shard
(`Sharding.keyDisj`); the caller checks it on the data.

Output: `{"mode": "linear" | "two_phase", "proved": <bool>, "partial": <plan>,
"combine": <plan>}`. Run `partial` on every shard, put the concatenated
results in the table `__partials`, and `combine` gives the plan's result
(`Rel.shardSplit_sound`). For a linear plan, `combine` just reads
`__partials`. `proved` is false when `float_order: "any"` was needed: the
result then rounds as the split makes it.

The JSON handling, the refusal messages and the schema of `__partials` are
trusted.
-/

namespace Substrait.ShardCheck

open Lean (Json toJson)
open Parse Write

def partials : String := "__partials"

def kindType (k : Kind) : Json :=
  let n := obj [("nullability", "NULLABILITY_NULLABLE")]
  match k with
  | .float => fp64Type
  | .time => obj [("precisionTimestamp", obj [("precision", toJson 6),
      ("nullability", "NULLABILITY_NULLABLE")])]
  | .date => obj [("date", n)]
  | .str => obj [("string", n)]
  | .bool => obj [("bool", n)]
  | .int | .other => i64Type

def colNames (n : Nat) : List String := (List.range n).map (s!"c{·}")

def schemaOf (ks : List Kind) : Json :=
  obj [("names", toJson (colNames ks.length)),
       ("struct", obj [("types", Json.arr (ks.map kindType).toArray),
                       ("nullability", "NULLABILITY_REQUIRED")])]

/-- Why `r` cannot be split (for the message only). -/
def why (S : String → Bool) (K : String → Option (List Nat)) (cat : Catalog) : Rel → String
  | .read _ => "the plan reads no sharded table, so every shard would compute all of it"
  | .values _ _ => "a literal table (VALUES) would be repeated on every shard"
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => why S K cat r
  | .fetch _ _ _ => "FETCH (LIMIT/OFFSET) depends on the rows of all shards"
  | .window _ _ _ _ => "a window looks at rows of other shards (splitting on its PARTITION BY keys is not supported yet)"
  | .distinct r =>
    if !r.linear S K cat then why S K cat r
    else "DISTINCT compares rows of different shards; it splits when its columns include the split key (keys)"
  | .aggregate r _ ms =>
    if !r.linear S K cat then
      if (r.tables.any S) then why S K cat r else "the aggregate reads no sharded table"
    else match ms.find? (!·.twoPhase (r.keyCols S K cat)) with
      | some m =>
        if m.distinct then
          "an aggregate over DISTINCT values: a value in two shards counts once in the whole and twice in the parts, unless its argument is the split key"
        else "SUM or AVG of doubles: floating-point addition is not associative, so the rounding depends on how the rows are split (float_order=\"any\" splits them anyway, unproved)"
      | none => "only one aggregate can be split in two phases, at the top of the plan; one below other operators needs the split key in its GROUP BY"
  | .unionAll a b =>
    if !a.tables.any S || !b.tables.any S then
      "a UNION ALL branch reads no sharded table and would be repeated on every shard"
    else if a.linear S K cat then why S K cat b else why S K cat a
  | .cross a b | .join a b _ _ =>
    if a.tables.any S && b.tables.any S then
      "a join of two sharded tables needs both split on the join key (co-partitioning, not supported yet)"
    else if a.tables.any S then why S K cat a else why S K cat b
  | .semi a b _ _ =>
    if b.tables.any S then "the right side of a semi or anti join reads a sharded table"
    else why S K cat a

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
  -- `Rel.shardSplit_sound` is stated for well-formed plans' semantics; the
  -- combining plan must read only `__partials`.
  if !plan.root.checkWF cat then throw "the plan is not well-formed"
  if plan.tables.any (·.1 == partials) then throw s!"the plan reads a table named {partials}"
  for t in sharded do
    if let some kt := K t then
      if kt.isEmpty || kt.any (· ≥ (cat t).arity) then
        throw s!"the split key of {t} must name columns of it"
  match plan.root.shardSplit S K cat partials floats with
  | none => throw (why S K cat plan.root)
  | some (p, q) =>
    let schemas := planSchemas plan
    let pk := relKinds schemas cat p
    let cat' : Catalog := fun t => if t == partials then ⟨pk.length, []⟩ else cat t
    let schemas' : Schemas := fun t n => if t == partials then schemaOf pk else schemas t n
    let linear := plan.root.linear S K cat
    return Json.mkObj [
      ("mode", toJson (if linear then "linear" else "two_phase")),
      ("proved", toJson (plan.root.shardSplit S K cat partials false).isSome),
      ("partial", writePlan schemas cat p (if linear then plan.names else colNames pk.length)),
      ("combine", writePlan schemas' cat' q plan.names)]

end Substrait.ShardCheck
