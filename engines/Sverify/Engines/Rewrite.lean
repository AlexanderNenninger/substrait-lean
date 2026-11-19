import Sverify.Engines.Sound

/-!
# Running a rewritten plan (#1787)

An optimization rewrites the plan the user wrote, `r`, to `s` on the
reference plan (seam A), and the engine runs `E.lower s`. The guarantee the
report states is about `r`. The lemmas here carry it over:

* `Engine.Sound.of_refines`: where `s` refines `r` (`Rel.Refines`) and `E`'s
  side condition holds of `s`, the rows `E`'s model computes for the lowered
  `s` are a result the reference allows for `r`. `Engine.Sound.of_refinesBag`
  is the form up to the order of rows (`Rel.RefinesBag`).
* `Engine.contract_sound_rewrite`: a contract verified on `r` holds on the
  rows the engine computes for the lowered `s`. Every hypothesis of the
  verification is about `r`: the preconditions, the analysis, robustness and
  the float side condition (`Rel.FloatOpenSafe`). So the bounds and checks
  come from the plan the user wrote, and a rewrite that hides a margin site
  changes none of them. A refinement up to the order of rows is enough: the
  contract observes its rows as a multiset.
* `Engine.runPlan`: the plan to run. The rewrite where `E` translates it and
  the decidable check of `E`'s side condition passes on it, otherwise the plan
  as written (`Engine.Sound.runPlan`). A rewrite that would evaluate an
  expression on rows the original skipped, and so could raise, fails the
  check and falls back to `r`.

The refinement itself is proved rule by rule at one node and carried up
through the plan by `analysis/Sverify/Analysis/Refines.lean`.
-/

namespace Substrait

variable [Boxes.Ambient]

variable {E : Engine} {side : Catalog → Rel → Prop} {cat : Catalog}

/-- **The engine's run of a rewrite is a result the reference allows for the
plan as written**, where the rewrite `s` refines it. -/
theorem Engine.Sound.of_refines (hE : E.Sound side) {r s s' : Rel} (hl : E.lower s = some s')
    (hs : side cat s) (h : s.Refines cat r) : r.Allowed cat (s'.eval cat E.impl) :=
  Rel.refines_iff.1 h _ (hE hl hs)

/-- `Engine.Sound.of_refines` up to the order of rows. -/
theorem Engine.Sound.of_refinesBag (hE : E.Sound side) {r s s' : Rel} (hl : E.lower s = some s')
    (hs : side cat s) (h : s.RefinesBag cat r) :
    ∃ out, r.Allowed cat out ∧ (s'.eval cat E.impl).Perm out :=
  Rel.refinesBag_iff.1 h _ (hE hl hs)

/-- **A contract verified on the plan as written holds on the engine's run of
a rewrite**, where the rewrite refines the plan up to the order of rows and
`E`'s side condition holds of the rewrite. The hypotheses of
`Engine.contract_sound` are all about `T`, the plan the user wrote. -/
theorem Engine.contract_sound_rewrite (hE : E.Sound side) (hcat : cat.WF)
    {S : String → List AVal} {pre : String → List Expr} {T : Rel} {es : List Expr}
    {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafe : T.FloatOpenSafe q ctx cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true)
    {R R' : Rel} (hR : R.RefinesBag cat T) (hl : E.lower R = some R') (hside : side cat R) :
    ∀ row ∈ postRows es mp (R'.eval cat E.impl), ∀ v ∈ row, v = .bool true := by
  obtain ⟨out, hout, hp⟩ := hE.of_refinesBag hl hside hR
  intro row hrow
  have hm : row ∈ postRows es mp out := ((hp.map _).map _).mem_iff.mp hrow
  exact contract_sound_allowed hcat hS hpre hT hq hsafe hsh hrob hQ hW hproved
    hout.postRows row hm

/-! ## The plan to run -/

/-- **The plan to run**: the rewrite `s` where `E` translates it and `check`,
the decidable part of `E`'s side condition, passes on it; otherwise the plan
as written, `r`. -/
def Engine.runPlan (E : Engine) (check : Rel → Bool) (r s : Rel) : Rel :=
  if (E.lower s).isSome && check s then s else r

/-- The plan to run is the rewrite or the plan as written. -/
theorem Engine.runPlan_cases (E : Engine) (check : Rel → Bool) (r s : Rel) :
    (E.runPlan check r s = s ∧ check s = true) ∨ E.runPlan check r s = r := by
  unfold Engine.runPlan
  split
  · rename_i h; simp only [Bool.and_eq_true] at h; exact .inl ⟨rfl, h.2⟩
  · exact .inr rfl

/-- **The plan to run is sound for the plan as written**: where `check`
implies `E`'s side condition, the side condition holds of `r`, and the rewrite
`s` refines `r`, the engine's run of whichever plan `Engine.runPlan` picks is a
result the reference allows for `r`. -/
theorem Engine.Sound.runPlan (hE : E.Sound side) {check : Rel → Bool}
    (hc : ∀ q, check q = true → side cat q) {r s p' : Rel} (hr : side cat r)
    (h : s.Refines cat r) (hl : E.lower (E.runPlan check r s) = some p') :
    r.Allowed cat (p'.eval cat E.impl) := by
  rcases E.runPlan_cases check r s with ⟨he, hcs⟩ | he <;> rw [he] at hl
  · exact hE.of_refines hl (hc s hcs) h
  · exact hE hl hr

/-- `Engine.Sound.runPlan` up to the order of rows. -/
theorem Engine.Sound.runPlanBag (hE : E.Sound side) {check : Rel → Bool}
    (hc : ∀ q, check q = true → side cat q) {r s p' : Rel} (hr : side cat r)
    (h : s.RefinesBag cat r) (hl : E.lower (E.runPlan check r s) = some p') :
    ∃ out, r.Allowed cat out ∧ (p'.eval cat E.impl).Perm out := by
  rcases E.runPlan_cases check r s with ⟨he, hcs⟩ | he <;> rw [he] at hl
  · exact hE.of_refinesBag hl (hc s hcs) h
  · exact ⟨_, hE hl hr, .refl _⟩

/-! ### The three paths

The reference translates every plan; an engine that refuses a plan
(`Engine.refusing`) translates none. One example per path of `Engine.runPlan`. -/

section Paths

/-- An engine that translates no plan. -/
def Engine.refusing : Engine := { Engine.reference with lower := fun _ => none }

private def Engine.pathR : Rel := .values 1 [[.int 1]]
private def Engine.pathS : Rel := .values 1 [[.int 2]]

/-- The engine does not translate the rewrite: the plan as written runs. -/
example : Engine.refusing.runPlan (fun _ => true) Engine.pathR Engine.pathS = Engine.pathR := rfl

/-- The check fails on the rewrite: the plan as written runs. -/
example : Engine.reference.runPlan (fun _ => false) Engine.pathR Engine.pathS = Engine.pathR := rfl

/-- The engine translates the rewrite and the check passes: the rewrite runs. -/
example : Engine.reference.runPlan (fun _ => true) Engine.pathR Engine.pathS = Engine.pathS := rfl

end Paths

end Substrait
