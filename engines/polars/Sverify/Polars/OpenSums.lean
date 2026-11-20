import Sverify.Engines.OpenSums
import Sverify.Polars.Engine

/-!
# An example: a double `SUM` on Polars (#1484, #929)

One table of one double, `1.0`, and `SUM(x)` over it, with the postcondition
`SUM(x) IS NULL OR NOT (SUM(x) < 0.0)`. Under Polars's table every
hypothesis of `Engine.contract_sound_runs_near` is discharged here, the side
condition by `Rel.floatOpenSafeP_aggregate`, and only D16's trusted claim
(`Engine.Runs`) stays open: Polars's `sum_order` is not the reference's, and
the sum it allows is the correctly rounded one up to its zero's sign
(`SumOrder.int_exact`). -/


namespace Substrait

section Example
attribute [local instance] Engine.exampleBoxes

def Engine.sumCat : Catalog := fun
  | "t" => ⟨1, [[.float FloatCode.one]]⟩
  | _ => ⟨0, []⟩

def Engine.sumPlan : Rel := .aggregate (.read "t") [] [{ fn := .fsum, arg := .field 0 }]

def Engine.sumA : String → List AVal := fun
  | "t" => [{ int := some ⟨some FloatCode.one, some FloatCode.one⟩, nk := some .float }]
  | _ => []

/-- `SUM(x) IS NULL OR NOT (SUM(x) < 0.0)`. -/
def Engine.sumPost : List Expr :=
  [.bin .or (.un .isNull (.field 0)) (.un .not (.bin .lt (.field 0) (.lit (.float 0))))]

/-- Rows as a multiset, values exactly. -/
def Engine.sumObs : Obs := { rows := .multiset }

def Engine.sumCtx : ObsCtx := {}

theorem Engine.sumCat_wf : Engine.sumCat.WF := by
  intro t row h
  unfold Engine.sumCat at h ⊢
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; rfl
  · simp at h

theorem Engine.sumA_mem :
    ∀ t, ∀ row ∈ (Engine.sumCat t).rows, EnvMem (Engine.sumA t) row := by
  intro t row h i
  unfold Engine.sumCat at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    unfold Engine.sumA
    subst h; cases i <;>
      simp [AVal.Mem, AVal.MemR, AVal.MemNum, Bound.Mem, AVal.top] <;> decide +kernel
  · simp at h

theorem Engine.sumPlan_wf : Engine.sumPlan.WF Engine.sumCat := by
  simp [Engine.sumPlan, Rel.WF, Expr.refsLt, Rel.arity, Engine.sumCat, Measure.refsLt]

theorem Engine.sumCtx_reflAt : Engine.sumCtx.ReflAt Engine.sumObs :=
  ⟨fun n h => by simp [Engine.sumObs] at h, fun s h hne => absurd h.symm hne⟩

/-- Polars allows no other behaviour at the options of `SUM` of `1.0`: it
creates no NaN, does not overflow and the group is not empty. -/
theorem Engine.polars_sum_noExtra : ¬AggExtra Engine.polars.table .fsum [.float FloatCode.one] := by
  rintro ⟨r, hr, os, hos, o, ho, hi, ⟨b, hb, hn⟩, hs⟩
  have hg : (Functions.rowOf (.agg .fsum)).map (·.group) = some "agg.fsum" := by decide +kernel
  rw [hr] at hg
  simp only [Option.map_some, Option.some.injEq] at hg
  rw [hg] at hos hb hn
  have hos' : Functions.groups.lookup "agg.fsum" =
      some ["sum_order", "rounding", "nan_creation", "empty_group_aggregates", "float_overflow"] := by
    decide +kernel
  rw [hos'] at hos
  simp only [Option.some.injEq] at hos
  subst hos
  revert hs hn hb b hi
  revert o
  decide +kernel

/-- `SUM(x)` of `Engine.sumPlan` reads `[1.0]` under any table. -/
theorem Engine.sum_groupInputs {t : ProfileTable} {vs : List Value}
    (h : (Rel.read "t").GroupInputs t Engine.sumCat [] { fn := .fsum, arg := .field 0 } vs) :
    vs = [.float FloatCode.one] := by
  obtain ⟨I, -, i, hi, grp, hg, s, hs, rfl⟩ := h
  have hi' : i = [[.float FloatCode.one]] := List.perm_singleton.mp hi
  subst hi'
  have hg' : grp = [[.float FloatCode.one]] := by
    rcases hg with ⟨-, rfl⟩ | ⟨x, -, rfl⟩
    · rfl
    · simp [groupRows, groupKey]
  subst hg'
  have hs' : s = [[.float FloatCode.one]] := List.perm_singleton.mp hs
  subst hs'
  simp [Measure.inputs, Measure.kept, Expr.eval]

theorem Engine.polars_sumsNear :
    (Rel.read "t").SumsNear Engine.sumObs Engine.sumCtx Engine.polars.table Engine.sumCat []
      [{ fn := .fsum, arg := .field 0 }] := by
  intro j m hj
  cases j with
  | succ j => simp at hj
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  intro vs hgi _
  rw [Engine.sum_groupInputs hgi]
  refine ⟨Engine.polars_sum_noExtra, fun _ b _ c => ⟨fun _ h => ?_, fun h => by cases h⟩⟩
  have hsi : SmallInts [.float FloatCode.one] := by
    refine ⟨fun v hv => ?_, by decide +kernel⟩
    simp only [List.mem_singleton] at hv
    exact ⟨_, hv, by unfold FloatCode.IsFin; decide +kernel, 1, by decide +kernel⟩
  have he := SumOrder.int_exact h hsi
  have hcr : floatSumCR [.float FloatCode.one] = FloatCode.one := by decide +kernel
  rw [hcr, show FloatCode.canon FloatCode.one = FloatCode.one by decide +kernel] at he
  have hc : c = FloatCode.one := by
    revert he; unfold FloatCode.canon FloatFormat.canon
    split
    · intro h; exact absurd h (by decide +kernel)
    · split
      · intro h; exact absurd h (by decide +kernel)
      · exact id
  show IntEquiv Engine.sumObs Engine.sumCtx 0 _ _
  simp only [IntEquiv, Engine.sumCtx, hcr, hc]

/-- The checker's tolerance for `Engine.sumPlan`'s `SUM`: one value of at
most `1.0` (`2¹⁰⁷⁴` scaled), as `Epsilon.measureEps` computes it. -/
def Engine.sumTol : Nat :=
  FloatCode.sumTolScaled 1 (2 ^ 1074) + FloatCode.ceilDiv (1 * 2 ^ 1074) (2 ^ 53)

/-- Rows as a multiset, doubles within `Engine.sumTol`. -/
def Engine.sumObsTol : Obs := { rows := .multiset, floats := .within "sum" }

def Engine.sumCtxTol : ObsCtx :=
  { kind := fun _ => .double,
    near := fun _ _ a b => (FloatCode.scaled a - FloatCode.scaled b).natAbs ≤ Engine.sumTol }

set_option exponentiation.threshold 2100 in
/-- **The corollary on the example** (ruling 135): under the checker's own
tolerance, `SumsNear` holds of Polars's `SUM` from the request's range (one
value, at most `1.0`) by `Measure.sumNear_of_tol`, `SumTolCovers 1 2¹⁰⁷⁴`
decided by evaluation. -/
theorem Engine.polars_sumsNear_tol :
    (Rel.read "t").SumsNear Engine.sumObsTol Engine.sumCtxTol Engine.polars.table Engine.sumCat []
      [{ fn := .fsum, arg := .field 0 }] := by
  intro j m hj
  cases j with
  | succ j => simp at hj
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  refine Measure.sumNear_of_tol (nm := "sum") (N := 1) (bs := 2 ^ 1074) rfl rfl
    (fun a b _ _ h => h) rfl
    (fun vs hg => by rw [Engine.sum_groupInputs hg]; exact Engine.polars_sum_noExtra)
    (fun vs hg => by
      rw [Engine.sum_groupInputs hg]
      refine ⟨by simp, fun x hx => ?_⟩
      simp only [List.mem_singleton] at hx
      exact ⟨_, hx, by unfold FloatCode.IsFin; decide +kernel, by decide +kernel⟩)
    (by decide) (by rw [FloatCode.maxMag_def]; decide +kernel) (by decide +kernel)

/-- And so `Rel.FloatOpenSafeP` under that tolerance, for Polars's table. -/
theorem Engine.polars_sum_openSafe_tol :
    Engine.sumPlan.FloatOpenSafeP Engine.sumObsTol Engine.sumCtxTol Engine.polars.table
      Engine.sumCat :=
  Rel.floatOpenSafeP_aggregate rfl ⟨fun _ _ _ _ => by simp [Engine.sumCtxTol], fun s h hne =>
    absurd h.symm (by simpa [Engine.sumObsTol] using hne)⟩
    (by decide +kernel) (by decide +kernel) (by decide) Engine.polars_sumsNear_tol

/-- **`Engine.contract_sound_runs_near` applies to a double `SUM`** (#1484):
on Polars's table, for `Engine.sumPlan`, every hypothesis is shown here but
D16's trusted claim (`Engine.Runs`), so the postcondition holds on the rows
Polars returns, whichever of its sums it computes. -/
theorem Engine.polars_sum_example {out : Relation}
    (hrun : Engine.polars.Runs Engine.sumCat Engine.sumPlan out) :
    ∀ row ∈ postRows Engine.sumPost [1] out, ∀ v ∈ row, v = .bool true :=
  Engine.contract_sound_runs_near Engine.sumCat_wf (S := Engine.sumA) (pre := fun _ => [])
    Engine.sumA_mem (by intro t row _ e he; simp at he) Engine.sumPlan_wf
    (q := Engine.sumObs) (ctx := Engine.sumCtx) rfl
    (Rel.floatOpenSafeP_aggregate rfl Engine.sumCtx_reflAt (by decide +kernel) (by decide +kernel)
      (by decide) Engine.polars_sumsNear)
    (sh := fun _ => none) (by simp) (by decide +kernel)
    (by simp [Rel.WF, Expr.refsLt, Rel.arity, Engine.sumCat, Engine.sumPlan, Engine.sumPost,
      Expr.narrow, Expr.narrowCmp, Expr.cmp?, Measure.refsLt])
    (WindowKeys.none_soundAll _) (by rw [Rel.aeval_csimp]; decide +kernel) hrun

end Example

end Substrait
