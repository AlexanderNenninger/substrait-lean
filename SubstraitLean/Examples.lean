import SubstraitLean.Kinds
import SubstraitLean.Rewrites
import SubstraitLean.Incremental
import SubstraitLean.Weighted
import SubstraitLean.Terms
import SubstraitLean.Contracts
import SubstraitLean.Retention
import SubstraitLean.TouchedGroups
import SubstraitLean.TouchedFrames
import SubstraitLean.IncrementalAgg
import SubstraitLean.IncrementalMinMax
import SubstraitLean.IncrementalSemi
import SubstraitLean.Safety
import SubstraitLean.Keys
import SubstraitLean.Rows
import SubstraitLean.Completeness
import SubstraitLean.Compose
import SubstraitLean.TableFormat
import SubstraitLean.Pruning
import SubstraitLean.Implied
import SubstraitLean.Partition
import SubstraitLean.Allowed
import SubstraitLean.Ties
import SubstraitLean.Guards
import SubstraitLean.LoweringDuckDB
import SubstraitLean.LiftDuckDB
import SubstraitLean.Semantic
import SubstraitLean.Obligations
import SubstraitLean.FloatExact

/-!
# Examples

The semantics is executable, so concrete plans can be run with `#eval` and
checked with `#guard` at build time.
-/

namespace Substrait.Examples

open Rel

/-- `orders(id, customer, amount)` -/
def orders : Table :=
  { arity := 3
    rows := [[.int 1, .str "ada", .int 30],
             [.int 2, .str "bob", .int 5],
             [.int 3, .str "ada", .null]] }

def cat : Catalog := fun
  | "orders" => orders
  | _ => ⟨0, []⟩

/-- `SELECT id, amount * 2 FROM orders WHERE amount > 10`, written the way a
Substrait producer emits it: Project appends column 3, Emit narrows to (0, 3). -/
def plan : Rel :=
  emit
    (project
      (filter (read "orders") (.bin .lt (.lit (.int 10)) (.field 2)))
      [.bin .mul (.field 2) (.lit (.int 2))])
    [0, 3]

#guard plan.eval cat == [[.int 1, .int 60]]

-- The null amount is filtered out: `10 < NULL` is NULL, not true.
#guard ((filter (read "orders") (.bin .lt (.lit (.int 10)) (.field 2))).eval cat).length == 1

-- A left join pads unmatched rows with nulls on the right.
#guard (join (read "orders") (values 1 [[.str "ada"]]) .left
          (.bin .eq (.field 1) (.field 3))).eval cat
       == [[.int 1, .str "ada", .int 30, .str "ada"],
           [.int 2, .str "bob", .int 5, .null],
           [.int 3, .str "ada", .null, .str "ada"]]

/-! ## Incremental maintenance

A change set on `orders`: delete order 1, insert order 4, and update order 2's
amount from 5 to 20 (a delete plus an insert). Change tables are named
`<table>$delta`. -/

def zcat : ZCatalog := fun t => ZSet.lift (cat t).rows

def customers : ZSet := ZSet.lift [[.str "ada"], [.str "bob"]]

def zcat₂ : ZCatalog := fun
  | "customers" => customers
  | t => zcat t

def Δ : ZCatalog := fun
  | "orders" => [([.int 1, .str "ada", .int 30], -1),
                 ([.int 4, .str "cy", .int 50], 1),
                 ([.int 2, .str "bob", .int 5], -1),
                 ([.int 2, .str "bob", .int 20], 1)]
  | "customers" => [([.str "cy"], 1)]
  | _ => []

def δ (t : String) : String := t ++ "$delta"

/-- What the engine sees: old tables plus change tables. -/
def engineCat (old : ZCatalog) : ZCatalog := fun t =>
  if t.endsWith "$delta" then Δ (t.dropEnd 6).toString else old t

-- The delta plan reads `orders$delta` and is itself an ordinary plan.
#guard (plan.delta δ).tables == ["orders$delta"]

-- ΔQ: order 1 leaves the result, orders 2 and 4 enter it.
#guard ZSet.consolidate ((plan.delta δ).zeval (engineCat zcat))
       == [([.int 1, .int 60], -1), ([.int 4, .int 100], 1), ([.int 2, .int 40], 1)]

-- Old result + ΔQ = recomputing from scratch (`Rel.incremental_sound`).
#guard (ZSet.consolidate (plan.zeval zcat ++ (plan.delta δ).zeval (engineCat zcat))).isPerm
       (ZSet.consolidate (plan.zeval (zcat + Δ)))

/-- `orders ⋈ customers ON orders.customer = customers.name`, with both
sides changing at once (the bilinear case). -/
def joinPlan : Rel := join (read "orders") (read "customers") .inner (.bin .eq (.field 1) (.field 3))

#guard (ZSet.consolidate (joinPlan.zeval zcat₂ ++ (joinPlan.delta δ).zeval (engineCat zcat₂))).isPerm
       (ZSet.consolidate (joinPlan.zeval (zcat₂ + Δ)))

-- The new `cy` customer joins with the newly inserted order 4.
#guard (ZSet.consolidate (joinPlan.zeval (zcat₂ + Δ))).contains
       ([.int 4, .str "cy", .int 50, .str "cy"], 1)

/-! ## Windows -/

/-- Readings `(sensor, ts, value)`, out of order. -/
def readings : Rel :=
  .values 3 [[.int 1, .int 20, .int 7], [.int 2, .int 10, .int 5], [.int 1, .int 10, .int 3]]

/-- `LAG(value)` and `ROW_NUMBER()` per sensor, by timestamp. -/
def withPrev : Rel := .window readings [0] [{ col := 1 }] [.lag 2 1 .null, .rowNumber]

#guard withPrev.eval (fun _ => ⟨0, []⟩) ==
  [[.int 2, .int 10, .int 5, .null, .int 1],
   [.int 1, .int 10, .int 3, .null, .int 1],
   [.int 1, .int 20, .int 7, .int 3, .int 2]]

/-! ## Aggregates -/

/-- `SELECT customer, COUNT(*), SUM(amount), MAX(amount) FROM orders GROUP BY customer`:
`ada`'s NULL amount counts as a row but not as a value. -/
def totals : Rel :=
  .aggregate (read "orders") [.field 1]
    [{ fn := .count, arg := .lit (.int 1) }, { fn := .sum, arg := .field 2 },
     { fn := .max, arg := .field 2 }]

#guard totals.eval cat ==
  [[.str "ada", .int 2, .int 30, .int 30],
   [.str "bob", .int 1, .int 5, .int 5]]

-- Without grouping there is one row, even for no input.
#guard (Rel.aggregate (.values 1 []) [] [{ fn := .count, arg := .field 0 },
    { fn := .sum, arg := .field 0 }]).eval cat == [[.int 0, .null]]

-- Two-phase aggregation: `totals` on two shards of `orders`, then combined.
#guard
  let shards := [(cat "orders").rows.take 1, (cat "orders").rows.drop 1]
  let ms := [{ fn := .count, arg := .lit (.int 1) }, { fn := .sum, arg := .field 2 },
    { fn := .max, arg := .field 2 : Measure }]
  aggregateEval (keyFields 1) (combineMeasures 1 ms) (shards.flatMap (aggregateEval [.field 1] ms))
    == totals.eval cat

end Substrait.Examples

-- Proofs rely only on Lean's standard axioms (no `sorry`).
#print axioms Substrait.Rel.eval_arity
#print axioms Substrait.Rel.kinds_sound
#print axioms Substrait.filter_project_pushdown
#print axioms Substrait.filter_cross_pushdown_left
#print axioms Substrait.emit_project_identity
#print axioms Substrait.Rel.incremental_sound
#print axioms Substrait.Rel.zeval_lift
#print axioms Substrait.Rel.weighted_eval
#print axioms Substrait.Rel.zeval_terms
#print axioms Substrait.contract_sound
#print axioms Substrait.Rel.mayIssues_sound
#print axioms Substrait.Rel.noIssue_of_sumsFit
#print axioms Substrait.floatSumCR_mem
#print axioms Substrait.floatAvgCR_mem
#print axioms Substrait.floatSumCR_sign
#print axioms Substrait.floatSumCR_perm
#print axioms Substrait.Rel.eval_allowed
#print axioms Substrait.Rel.allowed_perm_eval
#print axioms Substrait.Rel.refines_of_perm
#print axioms Substrait.Rel.guardFree_allowed
#print axioms Substrait.Rel.duckdb_shim_allowed
#print axioms Substrait.Rel.eval_orderAllowed
#print axioms Substrait.Rel.orderAllowed_allowed
#print axioms Substrait.contract_sound_all
#print axioms Substrait.Rel.keys_sound_all
#print axioms Substrait.Rel.keyedWindows_soundAll
#print axioms Substrait.Rel.orderAllowed_capReads
#print axioms Substrait.Rel.duckdb_refines
#print axioms Substrait.Lowering.lowerRel_raises
#print axioms Substrait.FloatCode.round_mono
#print axioms Substrait.Time.monthIndex_spec
#print axioms Substrait.Time.trunc_mono
#print axioms Substrait.Rel.keys_sound
#print axioms Substrait.Rel.join_length_le_of_keyed
#print axioms Substrait.IoT.window_complete
#print axioms Substrait.window_tiebreak
#print axioms Substrait.Rel.window_deterministic
#print axioms Substrait.Rel.window_allColumns
#print axioms Substrait.window_orderFree
#print axioms Substrait.window_tieFree
#print axioms Substrait.KeyOn.eqVariants
#print axioms Substrait.Measure.abs_sound
#print axioms Substrait.Rel.capReads_eval
#print axioms Substrait.Rel.maxRows_sound
#print axioms Substrait.StatProps.apply
#print axioms Substrait.Rel.capJoins_eval
#print axioms Substrait.Rel.issuesCapped_sound
#print axioms Substrait.FloatCode.ofInt_mono
#print axioms Substrait.FloatCode.ofInt_exact
#print axioms Substrait.FloatCode.ofInt_rel
#print axioms Substrait.FloatCode.toInt?_ofInt
#print axioms Substrait.FloatCode.ofDecimal_rel
#print axioms Substrait.FloatCode.ofDecimal_mono
#print axioms Substrait.FloatCode.toDecimal?_between
#print axioms Substrait.FloatCode.roundRat_rel
#print axioms Substrait.pairFacts_sound
#print axioms Substrait.Rel.ratioPart_sound
#print axioms Substrait.ratioSharpen_sound
#print axioms Substrait.aggregateEval_key
#print axioms Substrait.Triple.compose
#print axioms Substrait.Triple.compose_spec
#print axioms Substrait.Triple.of_contract
#print axioms Substrait.Triple.of_keys
#print axioms Substrait.Triple.of_aeval
#print axioms Substrait.RowsSat.update
#print axioms Substrait.KeyOn.update
#print axioms Substrait.Spec.update
#print axioms Substrait.Triple.maintained
#print axioms Substrait.Rel.stack_sound
#print axioms Substrait.Rel.chain_sound
#print axioms Substrait.ZSet.diff_correct
#print axioms Substrait.Rel.zeval_weight_congr
#print axioms Substrait.ChangeFeed.of_diff
#print axioms Substrait.Rel.cdf_sound
#print axioms Substrait.ChangeFeed.of_changed_files
#print axioms Substrait.stats_table
#print axioms Substrait.stats_append
#print axioms Substrait.stats_bounds
#print axioms Substrait.stats_fact
#print axioms Substrait.stats_all_null
#print axioms Substrait.prune_sound
#print axioms Substrait.Rel.eval_pruned
#print axioms Substrait.stats_prune
#print axioms Substrait.DoubleStats.colStats_correct
#print axioms Substrait.strPrune_sound
#print axioms Substrait.strStats_prune
#print axioms Substrait.Rel.need_sound
#print axioms Substrait.Rel.need_eval
#print axioms Substrait.Rel.eval_sharded
#print axioms Substrait.Rel.keyRows
#print axioms Substrait.Sharding.coDisjoint
#print axioms Substrait.windowEval_sharded
#print axioms Substrait.aggregateEval_flatten_disjoint
#print axioms Substrait.Measure.combine_eval
#print axioms Substrait.twoPhase_correct
#print axioms Substrait.Rel.eval_algebraic
#print axioms Substrait.IntArgs.ofTypes_sound
#print axioms Substrait.Rel.shardSplit_sound
#print axioms Substrait.inI64_partial
#print axioms Substrait.floatSplit_sum
#print axioms Substrait.floatSplit_avg
#print axioms Substrait.absPart_eval
#print axioms Substrait.Rel.evalI_eq
#print axioms Substrait.Rel.guardFree_sound
#print axioms Substrait.Rel.optimize_sound
#print axioms Substrait.Expr.evalP_reference
#print axioms Substrait.Rel.duckdb_sound
#print axioms Substrait.Rel.duckdb_shim_sound
#print axioms Substrait.Lowering.lowerRel_sound
#print axioms Substrait.Lowering.lower_correct
#print axioms Substrait.Lowering.duckdb_exact
#print axioms Substrait.liftDuckDB.total
#print axioms Substrait.liftReference.total
#print axioms Substrait.Retention.final_unchanged
#print axioms Substrait.Retention.retention_sound
#print axioms Substrait.Retention.final_stable
#print axioms Substrait.Retention.expiry_sound
#print axioms Substrait.Retention.open_buckets_le
#print axioms Substrait.Retention.trunc_eq_bucket
#print axioms Substrait.TouchedGroups.touched_sound
#print axioms Substrait.TouchedGroups.touched_eval
#print axioms Substrait.TouchedGroups.touched_window_sound
#print axioms Substrait.TouchedFrames.outRow_local
#print axioms Substrait.TouchedFrames.framed_sound
#print axioms Substrait.TouchedFrames.framed_batch
#print axioms Substrait.LinearAgg.aggregate_state
#print axioms Substrait.LinearAgg.aggregate_maintained
#print axioms Substrait.LinearAgg.distinct_state
#print axioms Substrait.LinearAgg.distinct_maintained
#print axioms Substrait.ExtremeAgg.done_merge
#print axioms Substrait.ExtremeAgg.extreme_maintained
#print axioms Substrait.ExtremeAgg.map_maintained
#print axioms Substrait.ExtremeAgg.finish_iavg
#print axioms Substrait.SemiDelta.semi_maintained
#print axioms Substrait.SemiDelta.matchCount_by_key
#print axioms Substrait.Relation.Equiv_mono
#print axioms Substrait.Relation.Equiv_exact
#print axioms Substrait.Relation.Near_add
#print axioms Substrait.Rel.refines_of_same
#print axioms Substrait.Rel.unsorted_refinesBag_not_refines
