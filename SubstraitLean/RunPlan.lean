import SubstraitLean.ContractCheck
import Sverify.Analysis.Refines
import Sverify.Engines.NoDouble
import Sverify.Engines.Transfer
import SubstraitLean.Engine

/-!
# The plan to run (#1787, item 2)

`Rel.optimize` rewrites the transformation `r` the user wrote into `s`
(`check_optimized_sound`: `Same`). This module decides whether an engine runs
`s` in place of `r`, and proves that the decision keeps the report's
guarantee. The checker decides; Python only reads the answer (ruling 129).

The rules are those the gate turns on (`Rule.onByDefault`, or the request's
`"rules"`) that keep the size hypothesis (`Rule.keepsSmall`, `Rel.optimize_small`),
so `Rel.Small` of `s` follows from `Rel.Small` of `r`, which the engine
statements assume: no new hypothesis. `s` runs only when every gate below passes; the first that fails
is named in the report (`run_gate`) and `r` runs:

* `profile`: the request is under the reference (`underReference`). `Same`
  speaks of the reference's `Rel.eval`.
* `no_rewrite`: no rule that is on fired.
* `rows`: the observation's rows level is `multiset`, and `s` leaves no choice
  but its row order (`Rel.detPlan`), so `s` refines `r` up to the order of
  rows (`Rel.refines_of_same`). Otherwise `r` is an `ORDER BY` under filters,
  projections, emits and fetches, and only its input is rewritten
  (`Rel.belowOrder`): an exact refinement (`Rel.RefinesBag.orderBy` and
  `Rel.Refines.filter` and the others, `Rel.belowOrder_refines`).
* `issues`: neither `r` nor `s` has an issue. An issue names an
  expression, not the rows it sees: a rule that evaluates it on more rows can
  raise where `r` returns, and a rule that drops it (a join no column of which
  is used) returns where `r` raises. `Same` equates the reference's `Rel.eval`,
  which says nothing of where a plan raises (#2006).
* `guard_free`: where `r` runs without its row checks (`guardFreeIn`), so does
  `s`.
* `near`: `r`'s verdict does not rest on doubles within a bound: an
  observation that coarsens `floats` (the plan's bound or a stated tolerance,
  #2105) or an `approx` postcondition, unless `r` and `s`
  have no double and transfer to the reference at each built-in engine
  (`Request.nearRoute`, `Rel.floatOpenSafeP_of_noDouble`). A
  refinement at the reference says nothing at an engine's table (ruling 127).
* `closed`: `s` is closed where `r` is (`closedIn`): no measure decomposed.
* `reads`, `functions`: `s` reads no option and calls no function `r` does
  not, so the transfer check and each engine's verdict for `r` hold for `s`
  (`transferB_of_reads_sub`).

The bounds, margins, preconditions and assumptions stay `r`'s: the report
computes them from `r`, and the contract theorems take every hypothesis on `r`
(`Engine.contract_sound_rewrite`).
-/

namespace Substrait

variable [Boxes.Ambient]

/-! ## Below the root `ORDER BY` -/

/-- The input of the root `ORDER BY`, under filters, projections, emits and
fetches. -/
def Rel.orderInput : Rel → Option Rel
  | .orderBy r _ => some r
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ => r.orderInput
  | _ => none

/-- `r` with `f` applied to the input of its root `ORDER BY`
(`Rel.orderInput`). -/
def Rel.belowOrder (f : Rel → Rel) : Rel → Option Rel
  | .orderBy r k => some (.orderBy (f r) k)
  | .filter r c => (r.belowOrder f).map (.filter · c)
  | .project r es => (r.belowOrder f).map (.project · es)
  | .emit r m => (r.belowOrder f).map (.emit · m)
  | .fetch r o n => (r.belowOrder f).map (.fetch · o n)
  | _ => none

omit [Boxes.Ambient] in
theorem Rel.orderInput_wf {cat : Catalog} :
    ∀ {r r0 : Rel}, r.WF cat → r.orderInput = some r0 → r0.WF cat
  | .orderBy _ _, _, hw, h => by simp only [orderInput, Option.some.injEq] at h; exact h ▸ hw.1
  | .filter r _, _, hw, h | .project r _, _, hw, h | .emit r _, _, hw, h =>
    Rel.orderInput_wf (r := r) hw.1 h
  | .fetch r _ _, _, hw, h => Rel.orderInput_wf (r := r) hw h
  | .read _, _, _, h | .values _ _, _, _, h | .cross _ _, _, _, h | .join _ _ _ _, _, _, h
  | .unionAll _ _, _, _, h | .window _ _ _ _, _, _, h | .semi _ _ _ _, _, _, h
  | .distinct _, _, _, h | .aggregate _ _ _, _, _, h | .unnest _ _, _, _, h => by
    simp [orderInput] at h

/-- **Rewriting the input of the root `ORDER BY` refines the plan exactly**,
where the rewrite of that input refines it up to the order of rows. -/
theorem Rel.belowOrder_refines {cat : Catalog} {f : Rel → Rel} :
    ∀ {r s : Rel}, (∀ r0, r.orderInput = some r0 → (f r0).RefinesBag cat r0) →
      r.belowOrder f = some s → s.Refines cat r
  | .orderBy r k, s, hf, h => by
    simp only [belowOrder, Option.some.injEq] at h
    subst h; exact (hf r rfl).orderBy k
  | .filter r c, s, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact (Rel.belowOrder_refines (r := r) hf hq).filter c
  | .project r es, s, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact (Rel.belowOrder_refines (r := r) hf hq).project es
  | .emit r m, s, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact (Rel.belowOrder_refines (r := r) hf hq).emit m
  | .fetch r o n, s, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact (Rel.belowOrder_refines (r := r) hf hq).fetch o n
  | .read _, _, _, h | .values _ _, _, _, h | .cross _ _, _, _, h | .join _ _ _ _, _, _, h
  | .unionAll _ _, _, _, h | .window _ _ _ _, _, _, h | .semi _ _ _ _, _, _, h
  | .distinct _, _, _, h | .aggregate _ _ _, _, _, h | .unnest _ _, _, _, h => by
    simp [belowOrder] at h

/-- `Rel.Small` of the plan with its `ORDER BY`'s input rewritten, where the
rewrite keeps it. -/
theorem Rel.belowOrder_small {cat : Catalog} {f : Rel → Rel} :
    ∀ {r s : Rel}, r.Small cat → (∀ r0, r.orderInput = some r0 → r0.Small cat →
      (f r0).Small cat) → r.belowOrder f = some s → s.Small cat
  | .orderBy r k, s, hs, hf, h => by
    simp only [belowOrder, Option.some.injEq] at h; subst h; exact hf r rfl hs
  | .filter r _, s, hs, hf, h | .project r _, s, hs, hf, h | .emit r _, s, hs, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact Rel.belowOrder_small (r := r) (s := q) hs hf hq
  | .fetch r _ _, s, hs, hf, h => by
    simp only [belowOrder, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact Rel.belowOrder_small (r := r) (s := q) hs hf hq
  | .read _, _, _, _, h | .values _ _, _, _, _, h | .cross _ _, _, _, _, h
  | .join _ _ _ _, _, _, _, h | .unionAll _ _, _, _, _, h | .window _ _ _ _, _, _, _, h
  | .semi _ _ _ _, _, _, _, h | .distinct _, _, _, _, h | .aggregate _ _ _, _, _, _, h
  | .unnest _ _, _, _, _, h => by simp [belowOrder] at h

/-! ## The transfer check -/

omit [Boxes.Ambient] in
/-- **A plan that reads no option another plan does not passes its transfer
check**: `transferB` checks each option read. -/
theorem transferB_of_reads_sub {r s : Rel} {t u : ProfileTable}
    (hsub : ∀ p ∈ s.reads, p ∈ r.reads) (h : transferB r t u = true) : transferB s t u = true :=
  List.all_eq_true.mpr fun p hp => List.all_eq_true.mp h p (hsub p hp)

/-! ## Where a double may occur

`Rel.mayDouble` (`core/Sverify/Core/NoDouble.lean`, ruling 154) is the
syntactic test the `near` gate reads; `Rel.floatOpenSafeP_of_noDouble`
(`engines/Sverify/Engines/NoDouble.lean`) proves what the gate needs of a plan
it passes. The examples below pin its inputs. -/

/-- A table `t` of one 64-bit integer column, in a request's schema form. -/
private def intTable : Parse.Tables := [("t", 1, Lean.Json.mkObj [("struct", Lean.Json.mkObj
  [("types", Lean.Json.arr #[Lean.Json.mkObj [("i64", Lean.Json.mkObj [])]])])])]

private def intCat : Catalog := ContractCheck.tablesCatalog intTable

private def intKinds (t : String) : List Kind := match intTable.lookup t with
  | some (_, sch) => Parse.schemaKinds sch
  | none => []

/-- Does `r` transfer to the reference at every built-in engine, past the
options only doubles read? -/
private def nearAll (r : Rel) : Bool :=
  builtinEngines.all fun e => transferB r Profile.reference.table (e.table.refAt floatOnlyOptions)

-- Ruling 136's counterexample: every column an integer, and a double in the
-- filter (`atan2(-(CAST(a AS DOUBLE)), -1.0) < 0`), where the sign of `-0.0`
-- decides whether the row stays.
#guard (Rel.filter (.read "t")
    (.bin .lt (.bin .fatan2 (.un .fneg (.un .itof (.field 0))) (.lit (.float (FloatCode.ofFloat (-1.0))))) (.lit (.int 0)))
    ).mayDouble intCat intKinds &&
  !(Rel.read "t").mayDouble intCat intKinds

-- Ruling 154, condition 1: a `GROUP BY` on an integer key and an integer
-- comparison transfer at every built-in engine.
#guard nearAll (.aggregate (.read "t") [.field 0] [{ fn := .count, arg := .field 0 }])
#guard nearAll (.filter (.read "t") (.bin .lt (.field 0) (.lit (.int 1))))
-- An integer `MAX` transfers at DuckDB only: `MIN` and `MAX` read `list_null_order`, whose
-- scope is every call (`optionScope`, until it narrows to list arguments, ruling 171), and
-- Polars's and Spark's tables leave the reference's `GREATEST` there.
#guard (builtinEngines.filter fun e =>
    !transferB (.aggregate (.read "t") [] [{ fn := .max, arg := .field 0 }])
      Profile.reference.table (e.table.refAt floatOnlyOptions)).map (·.name) == ["polars", "spark"]
-- Ruling 169: an integer `BIT_AND` has no double but is not `closedB`
-- (`AggFn.orderFree` leaves `.bit _` out), so the `near` gate keeps it as written.
#guard
  let r := Rel.aggregate (.read "t") [] [{ fn := .bit .and, arg := .field 0 }]
  !r.mayDouble intCat intKinds && !r.closedB
-- Nor does an integer `AVG`: each engine's table leaves the reference at
-- `avg_int_result` (`FP64` at Polars and Spark), which changes its integer
-- result, outside `floatOnlyOptions` by design.
#guard (builtinEngines.filter fun e =>
    !transferB (.aggregate (.read "t") [] [{ fn := .iavg, arg := .field 0 }])
      Profile.reference.table (e.table.refAt floatOnlyOptions)).map (·.name) == ["duckdb", "polars", "spark"]

/-! ## The size hypothesis through the rewrites

`Rel.Small` bounds the rows an aggregate or a window reads. Every rule but
eager aggregation keeps it: the rewritten aggregate reads the same rows, or as
many (a join on a key keeps one row per left row, `Rel.joinElim_sound`).
Eager aggregation aggregates the join's left input, whose rows the join's do
not bound (ruling 129, C). -/

section
variable {cat : Catalog} (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
  (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
  (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {K : TableCond}
  (hK : K.Hold cat) {R : ForeignKeys} (hR : R.Hold cat)

omit [Boxes.Ambient] in
theorem Rule.keepsSmall_aggregateBelowJoin : Rule.aggregateBelowJoin.keepsSmall = false := rfl

theorem Rel.eagerAgg_name {r s : Rel} {gs : List Expr} {ms : List Measure} {name : Rule}
    (h : r.eagerAgg cat A F K gs ms = some (name, s)) : name = .aggregateBelowJoin := by
  unfold eagerAgg at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
    · cases h
  · cases h

theorem Rel.fdAgg_small {r s : Rel} {gs : List Expr} {ms : List Measure} {name : Rule}
    (h : r.fdAgg cat A F K gs ms = some (name, s)) (hs : (Rel.aggregate r gs ms).Small cat) :
    s.Small cat := by
  unfold fdAgg at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
  · cases h

theorem Rel.joinElim_small {r a : Rel} {name : Rule} {k : Nat}
    (h : r.joinElim cat A F K R = some (name, a, k)) (hs : r.Small cat) : a.Small cat := by
  cases r with
  | join a' b ty on =>
    simp only [joinElim] at h
    split at h
    · cases ty with
      | left => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact hs.1
      | inner =>
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact hs.1
        · cases h
    · cases h
  | _ => simp [joinElim] at h

include hcat hA hF hK hR

/-- **A rule that keeps `Rel.Small` keeps it.** -/
theorem Rel.rule_small {r s : Rel} {name : Rule} (hwf : r.WF cat)
    (h : r.rule cat A F K R = some (name, s)) (hn : name.keepsSmall = true) (hs : r.Small cat) :
    s.Small cat := by
  match r, hwf, h with
  | .filter r c, _, h =>
    simp only [rule] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; trivial
      · split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
          · cases h
        · cases h
  | .join a b .left on, _, h =>
    simp only [rule] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
    · cases h
  | .distinct r, _, h =>
    simp only [rule] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
  | .aggregate r gs ms, hwf, h =>
    simp only [rule] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs.2
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact hs
      · split at h
        · rename_i name' a k hj
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
            obtain ⟨-, -, g, he, -⟩ := Rel.joinElim_sound hcat hA hF hK hR hwf.1 hj
            refine ⟨?_, Rel.joinElim_small hj hs.2⟩
            have := hs.1
            rwa [he, List.length_map] at this
          · cases h
        · split at h
          · rename_i x hx
            rw [h] at hx
            exact Rel.fdAgg_small hx hs
          · rw [Rel.eagerAgg_name h] at hn
            exact absurd hn (by rw [Rule.keepsSmall_aggregateBelowJoin]; decide)
  | .emit r m, _, h =>
    simp only [rule] at h
    split at h
    · rename_i name' a k hj
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        exact (Rel.joinElim_small hj (hs : r.Small cat) : a.Small cat)
      · cases h
    · split at h
      · split at h
        · rename_i name' a k hj
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
            exact (Rel.joinElim_small hj (hs : Rel.Small cat _) : a.Small cat)
          · cases h
        · cases h
      · cases h
  | .read _, _, h | .values _ _, _, h | .project _ _, _, h | .cross _ _, _, h
  | .join _ _ .inner _, _, h | .fetch _ _ _, _, h | .unionAll _ _, _, h
  | .window _ _ _ _, _, h | .semi _ _ _ _, _, h | .orderBy _ _, _, h | .unnest _ _, _, h =>
    simp [rule] at h

theorem Rel.stepN_small {use : Rule → Bool} (huse : ∀ n, use n = true → n.keepsSmall = true) :
    ∀ (fuel : Nat) {r : Rel} {log : List Rule}, r.WF cat → r.Small cat →
      (r.stepN cat A F K R use fuel log).1.Small cat
  | 0, _, _, _, hs => hs
  | fuel + 1, r, log, hwf, hs => by
    unfold stepN
    split
    · rename_i name s hr
      split
      · rename_i hu
        exact Rel.stepN_small huse fuel (Rel.rule_sound hcat hA hF hK hR hwf hr).wf
          (Rel.rule_small hcat hA hF hK hR hwf hr (huse _ hu) hs)
      · exact hs
    · exact hs

/-- **`optimize` keeps `Rel.Small`** where every rule it may apply keeps it:
a rewritten input has the rows of the original (`Rel.optimize_sound`). -/
theorem Rel.optimize_small {use : Rule → Bool} (huse : ∀ n, use n = true → n.keepsSmall = true) :
    ∀ {r : Rel}, r.WF cat → r.Small cat → (r.optimize cat A F K R use).1.Small cat
  | .read _, _, hs | .values _ _, _, hs | .unnest _ _, _, hs => hs
  | .filter r c, hwf, hs | .project r c, hwf, hs | .emit r c, hwf, hs | .orderBy r c, hwf, hs => by
    have ih := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4 ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
      (Rel.optimize_small huse hwf.1 hs)
  | .fetch r o n, hwf, hs | .distinct r, hwf, hs => by
    have ih := Rel.optimize_sound hcat hA hF hK hR (use := use) (r := r) hwf
    exact Rel.stepN_small hcat hA hF hK hR huse 4 ih.wf (Rel.optimize_small huse (r := r) hwf hs)
  | .aggregate r gs ms, hwf, hs => by
    have ih := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4 ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
      ⟨by rw [ih.eval]; exact hs.1, Rel.optimize_small huse hwf.1 hs.2⟩
  | .window r part sort fns, hwf, hs => by
    have ih := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4 ⟨ih.wf, by rw [ih.arity]; exact hwf.2⟩
      ⟨by rw [ih.eval]; exact hs.1, Rel.optimize_small huse hwf.1 hs.2⟩
  | .cross a b, hwf, hs => by
    have iha := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    have ihb := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.2
    exact Rel.stepN_small hcat hA hF hK hR huse 4 ⟨iha.wf, ihb.wf⟩
      ⟨Rel.optimize_small huse hwf.1 hs.1, Rel.optimize_small huse hwf.2 hs.2⟩
  | .join a b ty on, hwf, hs => by
    have iha := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    have ihb := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.2.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
      ⟨Rel.optimize_small huse hwf.1 hs.1, Rel.optimize_small huse hwf.2.1 hs.2⟩
  | .unionAll a b, hwf, hs => by
    have iha := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    have ihb := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.2.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
      ⟨Rel.optimize_small huse hwf.1 hs.1, Rel.optimize_small huse hwf.2.1 hs.2⟩
  | .semi a b anti on, hwf, hs => by
    have iha := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.1
    have ihb := Rel.optimize_sound hcat hA hF hK hR (use := use) hwf.2.1
    exact Rel.stepN_small hcat hA hF hK hR huse 4
      ⟨iha.wf, ihb.wf, by rw [iha.arity, ihb.arity]; exact hwf.2.2⟩
      ⟨Rel.optimize_small huse hwf.1 hs.1, Rel.optimize_small huse hwf.2.1 hs.2⟩

end

namespace ContractCheck
open Lean (Json)
open Parse

/-- Why the plan as written runs (`run_gate`). -/
inductive RunGate where
  | profile | noRewrite | rows | issues | guardFree | near | closed | reads | functions
  deriving DecidableEq, Repr

def RunGate.name : RunGate → String
  | .profile => "profile"
  | .noRewrite => "no_rewrite"
  | .rows => "rows"
  | .issues => "issues"
  | .guardFree => "guard_free"
  | .near => "near"
  | .closed => "closed"
  | .reads => "reads"
  | .functions => "functions"

namespace Request

variable (R : Request)

/-- The rules on for this request: those `"rules"` names, or the gate's. -/
def rulesOn : Rule → Bool :=
  match (R.input.getObjValAs? (Array String) "rules").toOption with
  | some ns => fun r => ns.contains r.name
  | none => Rule.onByDefault

/-- The rules the plan to run may apply: those on that keep `Rel.Small`. -/
def runRules (n : Rule) : Bool := R.rulesOn n && n.keepsSmall

omit [Boxes.Ambient] in
theorem runRules_keepsSmall (n : Rule) (h : R.runRules n = true) : n.keepsSmall = true := by
  simp only [runRules, Bool.and_eq_true] at h; exact h.2

/-- The request with `s` as the transformation's root. -/
def withRoot (s : Rel) : Request :=
  { R with transform := R.transform.map fun p => { p with root := s } }

/-- Is the observation's rows level `multiset`, by name? -/
def rowsMultiset : Bool :=
  ((R.input.getObjVal? "observation").toOption.bind
    (·.getObjValAs? String "rows" |>.toOption)) == some "multiset"

/-- The kinds of a table's columns, from the request's schema. -/
def tableKinds (t : String) : List Kind := match R.tables.lookup t with
  | some (_, sch) => Parse.schemaKinds sch
  | none => []

/-- Is `x` a plan `Rel.floatOpenSafeP_of_noDouble` covers at every built-in
engine: no double, no open measure, and the transfer to the reference past
the options only doubles read? The data is taken to have `tableKinds`. -/
def nearProved (x : Rel) : Bool :=
  !x.mayDouble R.cat R.tableKinds && x.closedB &&
    builtinEngines.all fun e => transferB x Profile.reference.table (e.table.refAt floatOnlyOptions)

/-- Does the verdict on `r` rest on doubles within a bound: the observation
coarsens `floats` (`floats="plan"` or a stated tolerance, `sv.within`, #2105)
or a postcondition is `approx`, and `r` or its rewrite `s` is not a plan `nearProved` covers?

The gate passes `r` and `s` where `Rel.floatOpenSafeP_of_noDouble` discharges
the obligation (`hsafeE` of `Engine.contract_sound_runs_near`) at every
built-in engine's table: neither has a double or an open measure, and each
transfers to the reference past `floatOnlyOptions` (ruling 154). What stays
open: plans with a double, and plans without one that read an option where an
engine's table leaves the reference outside `floatOnlyOptions` (an integer
`MIN`, `MAX` or `AVG` at every built-in engine), which the gate keeps as written. -/
def nearRoute (r s : Rel) : Bool :=
  let obs := (R.input.getObjVal? "observation").toOption
  (((obs.bind (·.getObjValAs? (Array String) "coarsens" |>.toOption)).getD #[]).contains "floats" ||
    ((obs.bind (·.getObjValAs? (Array Bool) "approx" |>.toOption)).getD #[]).any id) &&
    !(R.nearProved r && R.nearProved s)

/-- The rewrite of the plan `r` the gate looks at, and the rules applied:
the whole plan under a `multiset` observation, the input of the root
`ORDER BY` otherwise. `none` where neither shape applies. -/
def rewriteOf (K : KnowledgeEnv) (r : Rel) : Option (Rel × Rel × List Rule) :=
  let opt := fun x : Rel => x.optimize R.cat K.cols K.facts K.keys R.foreignKeysOf R.runRules
  if R.rowsMultiset then
    let (s, log) := opt r
    some (s, s, log)
  else match r.orderInput, r.belowOrder fun x => (opt x).1 with
    | some r0, some s => some (s, (opt r0).1, (opt r0).2)
    | _, _ => none

/-- The gates on the rewrite `s` of `r`, `part` the rewritten subplan and
`log` the rules applied, past the shape (`Request.rewriteOf`). -/
def gateOf (K : KnowledgeEnv) (r s part : Rel) (log : List Rule) : Option RunGate :=
  let R' := R.withRoot s
  let is := R'.issuesIn K
  ([(log.isEmpty, RunGate.noRewrite),
    (!part.detPlan R.cat K.cols K.facts K.keys, .rows),
    (!((R.issuesIn K).isEmpty && is.isEmpty), .issues),
    (R.guardFreeIn K && !R'.guardFreeIn K, .guardFree),
    (R.nearRoute r s, .near),
    (R'.closedIn != R.closedIn, .closed),
    (!s.reads.all r.reads.contains, .reads),
    (!s.functions.all r.functions.contains, .functions)].find? (·.1)).map (·.2)

/-- **The plan to run**, or the gate that keeps the plan as written. -/
def runPlanIn (K : KnowledgeEnv) : Except RunGate Rel :=
  if !R.underReference then .error .profile
  else match R.transform with
    | none => .error .noRewrite
    | some T =>
      -- No rule on: nothing to rewrite, and no analysis to run (the default).
      if !Rule.all.any R.runRules then .error .noRewrite
      else if !T.root.checkWF R.cat then .error .noRewrite
      else if (T.root.optimize R.cat K.cols K.facts K.keys R.foreignKeysOf R.runRules).2.isEmpty then
        .error .noRewrite
      else match R.rewriteOf K T.root with
        | none => .error .rows
        | some (s, part, log) => match R.gateOf K T.root s part log with
          | some g => .error g
          | none => .ok s

/-- The report's `run_plan` (the plan in the writer's JSON, or null),
`run_gate` (the gate that kept the plan as written, or null) and
`run_unchecked` (the plan's per-expression marks, as `unchecked`). -/
def runPlanJson : List (String × Json) :=
  let K := R.kenv
  match R.transform, R.runPlanIn K with
  | some p, .ok s =>
    let A := K.cols
    let F := K.facts
    let W := K.windows R.cat
    [("run_plan", Write.writePlan (Write.planSchemas p) R.cat s p.names),
      ("run_gate", .null),
      ("run_unchecked", if s.looseSub then s.marksJson (s.marks R.cat A F W false) else .null)]
  | _, .error g => [("run_plan", .null), ("run_gate", g.name), ("run_unchecked", .null)]
  | none, .ok _ => [("run_plan", .null), ("run_gate", RunGate.noRewrite.name),
      ("run_unchecked", .null)]

end Request

/-- The gate's table, for `substrait-check --rules`: each rule's name, whether
it is on by default, and whether it keeps `Rel.Small`. -/
def rulesJson : Json :=
  Json.arr (Rule.all.map fun r => Json.mkObj [("name", r.name),
    ("on", Lean.toJson r.onByDefault), ("keeps_small", Lean.toJson r.keepsSmall)]).toArray

/-! ## Soundness -/

/-- **The plan to run refines the plan as written** (#1787, ruling 129): on
data that meets the request and its foreign keys (`references`), the plan
`runPlanIn` gives refines the transformation up to the order of rows, and
exactly where the observation's rows level is not `multiset`; it is as small
as the transformation (`Rel.Small`, the engine statements' size hypothesis); it
reads no option
and calls no function the transformation does not, it has no issue the
transformation lacks, and it runs guard-free where the transformation does.
With `Engine.Sound.runPlan` (`engines/Sverify/Engines/Rewrite.lean`) an
engine's run of it is a result the reference allows for the transformation. -/
theorem check_run_plan_sound {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data) {T : Plan} (hT : R.transform = some T)
    (hFK : R.foreignKeysOf.Hold data) {s : Rel} (hs : R.runPlanIn R.kenv = .ok s) :
    s.RefinesBag data T.root ∧ (R.rowsMultiset = false → s.Refines data T.root) ∧
      (T.root.Small data → s.Small data) ∧
      (s.reads.all T.root.reads.contains = true) ∧
      (s.functions.all T.root.functions.contains = true) ∧
      (R.issuesIn R.kenv = [] ∧ (R.withRoot s).issuesIn R.kenv = []) ∧
      (R.guardFreeIn R.kenv = true → (R.withRoot s).guardFreeIn R.kenv = true) := by
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys hD.ranges
  have hwf := check_transform_wf hR hc hD hT
  unfold Request.runPlanIn at hs
  rw [hT] at hs
  split at hs
  · simp at hs
  dsimp only at hs
  split at hs
  · simp at hs
  split at hs
  · simp at hs
  split at hs
  · simp at hs
  split at hs
  · simp at hs
  rename_i x s' part log hrw
  split at hs
  · simp at hs
  rename_i hg
  simp only [Except.ok.injEq] at hs
  subst hs
  simp only [Request.gateOf, Option.map_eq_none_iff, List.find?_eq_none, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hg
  obtain ⟨-, hdet, his, hgf, -, -, hreads, hfns⟩ := hg
  have hdet' : part.detPlan data R.kenv.cols R.kenv.facts R.kenv.keys = true := by
    rw [Rel.detPlan_congr hD.arity]; simpa using hdet
  have same : ∀ {x : Rel}, x.WF data →
      Same data x (x.optimize R.cat R.kenv.cols R.kenv.facts R.kenv.keys R.foreignKeysOf
        R.runRules).1 := fun hx => by
    rw [← Rel.optimize_congr hD.arity]
    exact Rel.optimize_sound hD.wf hK.cols hK.facts hK.keys hFK hx
  have small : ∀ {x : Rel}, x.WF data → x.Small data →
      (x.optimize R.cat R.kenv.cols R.kenv.facts R.kenv.keys R.foreignKeysOf
        R.runRules).1.Small data := fun hx hs => by
    rw [← Rel.optimize_congr hD.arity]
    exact Rel.optimize_small hD.wf hK.cols hK.facts hK.keys hFK R.runRules_keepsSmall hx hs
  have hsmall : T.root.Small data → s'.Small data := fun hs => by
    unfold Request.rewriteOf at hrw
    split at hrw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hrw
      obtain ⟨rfl, rfl, -⟩ := hrw
      exact small hwf hs
    · dsimp only at hrw
      split at hrw
      · rename_i r0 q h0 hq
        simp only [Option.some.injEq, Prod.mk.injEq] at hrw
        obtain ⟨rfl, rfl, -⟩ := hrw
        exact Rel.belowOrder_small hs (fun r0' h0' hs0 => by
          rw [h0] at h0'; cases h0'
          exact small (Rel.orderInput_wf hwf h0) hs0) hq
      · simp at hrw
  have href : s'.RefinesBag data T.root ∧ (R.rowsMultiset = false → s'.Refines data T.root) := by
    unfold Request.rewriteOf at hrw
    split at hrw
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hrw
      obtain ⟨rfl, rfl, -⟩ := hrw
      exact ⟨Rel.refines_of_same hD.wf hK.cols hK.facts hK.keys (same hwf) hdet',
        fun h => by simp [hm] at h⟩
    · dsimp only at hrw
      split at hrw
      · rename_i r0 q h0 hq
        simp only [Option.some.injEq, Prod.mk.injEq] at hrw
        obtain ⟨rfl, rfl, -⟩ := hrw
        have hr := Rel.belowOrder_refines (cat := data) (fun r0' h0' => by
          rw [h0] at h0'; cases h0'
          exact Rel.refines_of_same hD.wf hK.cols hK.facts hK.keys
            (same (Rel.orderInput_wf hwf h0)) hdet') hq
        exact ⟨hr.bag, fun _ => hr⟩
      · simp at hrw
  refine ⟨href.1, href.2, hsmall, ?_, ?_, ?_, fun h => ?_⟩
  · simpa [List.all_eq_true] using hreads
  · simpa [List.all_eq_true] using hfns
  · simpa [List.isEmpty_iff] using his
  · revert hgf; cases (R.withRoot s').guardFreeIn R.kenv <;> simp [h]


/-! ## DuckDB's side condition for the plan to run -/

/-- **Every issue a request's transformation can run into is listed** by
`Request.issuesIn`, for any request whose transformation is well-formed (the
part of `check_issues_sound` that needs no parse). -/
theorem Request.issuesIn_sound (R : Request) {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) (hw : T.root.checkWF R.cat = true)
    (hP : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows)
    (hsm : T.root.Small data) :
    ∀ p, T.root.HasIssue data false p →
      p ∈ R.issuesIn R.kenv ∨ (p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs) := by
  intro p hp
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys hD.ranges
  have hwf : T.root.WF data := Rel.wf_congr hD.arity (Rel.checkWF_iff.mp hw)
  have hin := Rel.issuesCapped_sound hD.wf hK.cols hK.facts (hK.windows hD.wf) hK.keys hD.caps hP
    hwf hsm p hp
  rw [Rel.issuesCapped_congr hD.arity] at hin
  simp only [Request.issuesIn, hT, hw, ↓reduceIte, List.mem_filter, List.mem_eraseDups,
    List.mem_append, KnowledgeEnv.windows, ← Rel.keyedWindows_congr hD.arity]
  by_cases hinf : p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs
  · exact .inr hinf
  · refine .inl ⟨.inl (by simpa [KnowledgeEnv.windows] using hin), ?_⟩
    obtain ⟨i, e⟩ := p
    simp only at hinf ⊢
    cases hr : R.underReference
    · by_cases hi : i = .infinite
      · subst hi
        by_cases he : e ∈ T.root.aggArgs
        · simp [he]
        · exact absurd ⟨rfl, hr, he⟩ hinf
      · simp [hi]
    · simp

/-- The data meets the request with another root: the root is no part of
what `DataMeets` asks. -/
theorem DataMeets.withRoot {R : Request} {data : Catalog} (hD : DataMeets R data) (s : Rel) :
    DataMeets (R.withRoot s) data :=
  ⟨hD.wf, hD.arity, hD.schemas, hD.pre, hD.keys, hD.ranges, hD.caps⟩

/-- **DuckDB's side condition for the plan to run, from the report**: under
the reference, where the transformation is guard-free, DuckDB's lowered plan
to run raises on nothing, on data that meets the request, its foreign keys,
its bounds per key and the size hypothesis. The gate gives the plan to run no
issues (`issues`, which also asks the transformation to have none),
guard-freedom (`guard_free`) and the size hypothesis (`Rel.optimize_small`). -/
theorem run_plan_noRaise_duckdb {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data) {T : Plan} (hT : R.transform = some T)
    (hFK : R.foreignKeysOf.Hold data) {s : Rel} (hs : R.runPlanIn R.kenv = .ok s)
    (hP : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows)
    (hsm : T.root.Small data) (href : R.underReference = true)
    (hg : rep.guardFree = true) : (Engine.duckdb {} rfl).NoRaiseSide data s := by
  obtain ⟨-, -, hss, -, -, his, hgf⟩ := check_run_plan_sound hR hc hD hT hFK hs
  have hok := Request.check_ok (check_parse hR hc)
  rw [hok.guardFree] at hg
  have hg' := hgf hg
  have hT' : (R.withRoot s).transform = some { T with root := s } := by
    simp [Request.withRoot, hT]
  simp only [Request.guardFreeIn, hT', Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨hw, hloose⟩, -⟩, -⟩ := hg'
  intro r' hl hr
  cases hl
  obtain ⟨p, hp⟩ := Rel.hasIssue_of_raises false hloose
    (Lowering.lowerRel_raises Lowering.duckdb_total hr)
  rcases (R.withRoot s).issuesIn_sound (hD.withRoot s) hT' hw hP (hss hsm) p hp with h | ⟨-, h, -⟩
  · exact absurd (show p ∈ (R.withRoot s).issuesIn R.kenv from h) (by rw [his.2]; simp)
  · exact absurd href (by rw [show (R.withRoot s).underReference = R.underReference from rfl] at h
                          simp [h])

end ContractCheck

end Substrait
