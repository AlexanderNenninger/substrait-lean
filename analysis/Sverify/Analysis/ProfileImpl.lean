import Sverify.Core.Profile
import Sverify.Analysis.Guards

/-!
# Plans that cannot raise

For a plan `verify` proves error-free from its contract, no shim is needed:
an engine whose profile agrees with the reference wherever the reference
does not raise (`Impl.Faithful`, `analysis/Sverify/Analysis/Guards.lean`) gives
`Rel.eval`'s rows, by guard elimination (`Rel.guardFree_sound`). The
reference's own values are such an implementation
(`Profile.reference_faithful`); DuckDB's profile is another
(`Profile.duckdbWritten_faithful`), and the benchmark queries of #229 take
this route. Engine-neutral: the engines' profiles and lowerings import it,
the core (`Profile`, `Allowed`) does not.

A reference raise is an issue that is not assumed (`Rel.hasIssue_of_raises`),
so a report with only assumed issues rules out a reference raise
(`Rel.not_raises_of_assumed`): an engine's no-raise side condition from the
checker's report.
-/

namespace Substrait

variable [Boxes.Ambient]
theorem Profile.reference_faithful : Profile.reference.impl.Faithful :=
  ⟨fun f v h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val],
   fun f v w h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val]⟩

/-! ## The reference's functions where it does not raise -/

omit [Boxes.Ambient] in
theorem Measure.mapExpr_id (m : Measure) : m.mapExpr id = m := by
  cases m; simp [Measure.mapExpr]

omit [Boxes.Ambient] in
theorem Rel.mapExprs_id : ∀ r : Rel, r.mapExprs id = r
  | .read _ | .values _ _ => rfl
  | .filter r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => by simp [mapExprs, Rel.mapExprs_id r]
  | .project r _ => by simp [mapExprs, Rel.mapExprs_id r]
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => by
    simp [mapExprs, Rel.mapExprs_id a, Rel.mapExprs_id b]
  | .aggregate r _ ms => by
    simp only [mapExprs, Rel.mapExprs_id r, List.map_id_fun, id_eq]
    congr 1
    exact (List.map_congr_left fun m _ => Measure.mapExpr_id m).trans (List.map_id ms)

/-- Where the reference does not raise, its functions give `Rel.eval`'s rows. -/
theorem Rel.evalI_reference {cat : Catalog} {r : Rel} (h : ¬r.Raises Profile.reference cat) :
    r.eval cat Profile.reference.impl = r.eval cat := by
  have := Rel.evalI_mapExprs (f := id) Expr.reference_exact (fun _ => rfl) (cat := cat) (r := r)
  rw [Rel.mapExprs_id] at this
  exact this h


/-! ## A reference raise is an issue (FM round 9)

`Rel.mayIssues_sound` covers `Rel.HasIssue`; these link it to `Rel.Raises`, so
a report with only assumed issues discharges an engine's no-raise side
condition. -/

/-- An expression that raises under the reference has an issue on that row
that is not assumed: the reference raises the first error `Expr.issues`
reports, an error is no overflow to `±∞`, and a row's issue is no `SUM`'s
(`Expr.issues_ne_sumWraps`). -/
theorem Expr.issue_of_raises {e : Expr} {row : Row} (h : e.RaisesOn Profile.reference row) :
    ∃ p ∈ e.issues row, p.1.assumed = false := by
  simp only [Expr.RaisesOn, Expr.evalP_reference, Expr.refOutcome_err] at h
  obtain ⟨k, hk⟩ : ∃ k, firstError (e.issues row) = some k := by
    cases hf : firstError (e.issues row) with
    | none => simp [hf] at h
    | some k => exact ⟨k, rfl⟩
  simp only [firstError, Option.map_eq_some_iff] at hk
  obtain ⟨p, hp, -⟩ := hk
  have hmem := List.mem_of_find?_eq_some hp
  have herr := List.find?_some hp
  refine ⟨p, hmem, ?_⟩
  have hs := Expr.issues_ne_sumWraps hmem
  obtain ⟨i, x⟩ := p
  revert herr hs
  cases i <;> simp [Issue.isError, Issue.assumed]

/-- **A reference raise is an issue.** Where the reference raises in `r`, some
issue of `r` that is not assumed happens (`Rel.HasIssue`), read at either level `u`.

`Rel.HasIssue` reads filter and join conditions over the loose input
(`Rel.loose`), and `Rel.Raises` over the strict one, so the statement needs
the strict rows among the loose rows: `Rel.looseSub` (`Rel.mem_loose`). Without
it the statement is false. Take `a = {(1)}`, `b = {(1, -1)}` and

  `filter (join a (filter b (v > 0)) .left (a.k = b.k)) (1 / coalesce(b.v, 0) > 0)`.

The strict join pads `(1)` with NULLs, and the condition divides by zero on
`(1, NULL, NULL)`. The loose join drops `b`'s filter and gives `(1, 1, -1)`
alone, where nothing raises. The report still lists that zero divisor:
`Rel.mayIssues` reads the left join's right columns as nullable. -/
theorem Rel.hasIssue_of_raises {cat : Catalog} :
    ∀ {r : Rel} (u : Bool), r.looseSub = true → r.Raises Profile.reference cat →
      ∃ p, r.HasIssue cat u p ∧ p.1.assumed = false
  | .read _, _, _, h | .values _ _, _, _, h => h.elim
  | .filter r c, _, hs, h => by
    simp only [Rel.looseSub] at hs
    by_cases hr : r.Raises Profile.reference cat
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises true hs hr; exact ⟨p, .inl hp, hn⟩
    rcases h with h | ⟨row, hrow, hc⟩
    · exact absurd h hr
    rw [Rel.evalI_reference hr] at hrow
    obtain ⟨p, hp, hn⟩ := Expr.issue_of_raises hc
    exact ⟨p, .inr ⟨row, Rel.mem_loose hs row hrow, hp⟩, hn⟩
  | .project r es, u, hs, h => by
    simp only [Rel.looseSub] at hs
    by_cases hr : r.Raises Profile.reference cat
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises u hs hr; exact ⟨p, .inl hp, hn⟩
    rcases h with h | ⟨row, hrow, e, he, hc⟩
    · exact absurd h hr
    rw [Rel.evalI_reference hr] at hrow
    obtain ⟨p, hp, hn⟩ := Expr.issue_of_raises hc
    refine ⟨p, .inr ⟨row, ?_, e, he, hp⟩, hn⟩
    cases u
    · exact hrow
    · exact Rel.mem_loose hs row hrow
  | .emit r _, u, hs, h | .fetch r _ _, u, hs, h | .orderBy r _, u, hs, h
  | .distinct r, u, hs, h => by
    simp only [Rel.looseSub] at hs
    exact hasIssue_of_raises (r := r) u hs h
  | .window r _ _ _, u, hs, h => by
    simp only [Rel.looseSub] at hs
    obtain ⟨p, hp, hn⟩ := hasIssue_of_raises (r := r) u hs h
    exact ⟨p, .inl hp, hn⟩
  | .unnest _ _, _, hs, _ => by simp [Rel.looseSub] at hs
  | .cross a b, u, hs, h | .unionAll a b, u, hs, h => by
    simp only [Rel.looseSub, Bool.and_eq_true] at hs
    rcases h with h | h
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises u hs.1 h; exact ⟨p, .inl hp, hn⟩
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises u hs.2 h; exact ⟨p, .inr hp, hn⟩
  | .join a b ty on, _, hs, h | .semi a b _ on, _, hs, h => by
    have hab : a.looseSub = true ∧ b.looseSub = true := by
      first
        | (cases ty <;> simp only [Rel.looseSub, Bool.and_eq_true] at hs <;>
            exact ⟨hs.1, by first | exact hs.2 | exact Rel.looseExact_sub hs.2⟩)
        | (simp only [Rel.looseSub, Bool.and_eq_true] at hs; exact hs)
    by_cases ha : a.Raises Profile.reference cat
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises true hab.1 ha; exact ⟨p, .inl hp, hn⟩
    by_cases hb : b.Raises Profile.reference cat
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises true hab.2 hb; exact ⟨p, .inr (.inl hp), hn⟩
    rcases h with h | h | ⟨x, hx, y, hy, hc⟩
    · exact absurd h ha
    · exact absurd h hb
    rw [Rel.evalI_reference ha] at hx
    rw [Rel.evalI_reference hb] at hy
    obtain ⟨p, hp, hn⟩ := Expr.issue_of_raises hc
    exact ⟨p, .inr (.inr ⟨x, Rel.mem_loose hab.1 x hx, y, Rel.mem_loose hab.2 y hy, hp⟩), hn⟩
  | .aggregate r gs ms, u, hs, h => by
    simp only [Rel.looseSub] at hs
    by_cases hr : r.Raises Profile.reference cat
    · obtain ⟨p, hp, hn⟩ := hasIssue_of_raises u hs hr; exact ⟨p, .inl hp, hn⟩
    rcases h with h | ⟨row, hrow, e, he, hc⟩
    · exact absurd h hr
    rw [Rel.evalI_reference hr] at hrow
    obtain ⟨p, hp, hn⟩ := Expr.issue_of_raises hc
    refine ⟨p, .inr (.inl ⟨row, ?_, e, he, hp⟩), hn⟩
    cases u
    · exact hrow
    · exact Rel.mem_loose hs row hrow

/-- **A report with only assumed issues rules out a reference raise**: on a
catalog that satisfies the preconditions, a plan whose `Rel.mayIssues` are all
assumed does not raise under the reference. -/
theorem Rel.not_raises_of_assumed {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    ¬r.Raises Profile.reference cat := fun h => by
  obtain ⟨p, hp, ha⟩ := Rel.hasIssue_of_raises false hs h
  have := List.all_eq_true.mp hm p (mayIssues_sound hcat hA hF hT hwf hsmall p hp)
  rw [ha] at this; cases this


end Substrait
