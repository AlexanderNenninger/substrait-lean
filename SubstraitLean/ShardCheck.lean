import SubstraitLean.Partition
import SubstraitLean.Write
import SubstraitLean.Check

/-!
# Splitting a plan for sharded evaluation

Input (JSON): `{"plan": <plan>, "sharded": ["<table>", ...]}`. The sharded
tables are split over the shards; every other table is broadcast (each shard
has all of it).

Output: `{"mode": "linear" | "two_phase", "partial": <plan>, "combine": <plan>}`.
Run `partial` on every shard, put the concatenated results in the table
`__partials`, and `combine` gives the plan's result (`Rel.shardSplit_sound`).
For a linear plan, `combine` just reads `__partials`.

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
def why (S : String → Bool) : Rel → String
  | .read _ => "the plan reads no sharded table, so every shard would compute all of it"
  | .values _ _ => "a literal table (VALUES) would be repeated on every shard"
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => why S r
  | .fetch _ _ _ => "FETCH (LIMIT/OFFSET) depends on the rows of all shards"
  | .window _ _ _ _ => "a window looks at rows of other shards (splitting on its PARTITION BY keys is not supported yet)"
  | .distinct _ => "DISTINCT compares rows of different shards"
  | .aggregate r _ ms =>
    if !r.linear S then
      if (r.tables.any S) then why S r else "the aggregate reads no sharded table"
    else match ms.find? (!·.decomposable) with
      | some m =>
        if m.distinct then
          "an aggregate over DISTINCT values: a value in two shards counts once in the whole and twice in the parts"
        else "SUM or AVG of doubles: floating-point addition is not associative, so the rounding depends on how the rows are split"
      | none => "only one aggregate, at the top of the plan, can be split"
  | .unionAll a b =>
    if !a.tables.any S || !b.tables.any S then
      "a UNION ALL branch reads no sharded table and would be repeated on every shard"
    else if a.linear S then why S b else why S a
  | .cross a b | .join a b _ _ =>
    if a.tables.any S && b.tables.any S then
      "a join of two sharded tables needs both split on the join key (co-partitioning)"
    else if a.tables.any S then why S a else why S b
  | .semi a b _ _ =>
    if b.tables.any S then "the right side of a semi or anti join reads a sharded table"
    else why S a

def check (input : Json) : Except String Json := do
  let plan ← parsePlan ((input.getObjVal? "plan").toOption.getD .null).compress
  let sharded := ((input.getObjValAs? (Array String) "sharded").toOption.getD #[]).toList
  let S : String → Bool := (sharded.contains ·)
  let cat := plan.catalog
  -- `Rel.shardSplit_sound` is stated for well-formed plans' semantics; the
  -- combining plan must read only `__partials`.
  if !plan.root.checkWF cat then throw "the plan is not well-formed"
  if plan.tables.any (·.1 == partials) then throw s!"the plan reads a table named {partials}"
  match plan.root.shardSplit S partials with
  | none => throw (why S plan.root)
  | some (p, q) =>
    let schemas := planSchemas plan
    let pk := relKinds schemas cat p
    let cat' : Catalog := fun t => if t == partials then ⟨pk.length, []⟩ else cat t
    let schemas' : Schemas := fun t n => if t == partials then schemaOf pk else schemas t n
    let linear := plan.root.linear S
    return Json.mkObj [
      ("mode", toJson (if linear then "linear" else "two_phase")),
      ("partial", writePlan schemas cat p (if linear then plan.names else colNames pk.length)),
      ("combine", writePlan schemas' cat' q plan.names)]

end Substrait.ShardCheck
