import SubstraitLean.DuckDBFunctions
import SubstraitLean.ProfileImpl
import Sverify.Analysis.Knowledge

/-!
# DuckDB's profile (#185)

The soundness of running a verified plan on DuckDB (`Rel.duckdb_sound`):
DuckDB's functions, as the SQL printer writes them, agree with the reference
wherever it does not raise (`Profile.duckdbWritten_faithful`). The profile
itself, `Profile.duckdb` and `Profile.duckdbWritten`, is in
`DuckDBFunctions.lean`, on the core alone. Polars's
and Spark's profiles have their own modules (`PolarsProfile.lean`,
`SparkProfile.lean`); the core (`Profile.lean`, `Allowed`, `AllowedNear`)
does not import this one.
-/

namespace Substrait

/-- **DuckDB, as the SQL printer writes it, agrees with the reference
wherever the reference does not raise**, with IEEE operations on (DuckDB's
default). Elsewhere it differs only where the reference raises: `∞ - ∞` is
NaN, `x / 0.0` is `±∞`, `sqrt(-1)` NaN. (Without IEEE operations, `0 ^ -1`
raises in DuckDB and is `∞` in the reference.) -/
theorem Profile.duckdbWritten_faithful (s : DuckDBSettings) (hs : s.ieeeOps = true) :
    (Profile.duckdbWritten s).impl.Faithful := by
  refine ⟨fun f v h => ?_, fun f v w h => ?_⟩
  · have hr := Profile.reference_faithful.1 f v h
    simp only [Profile.impl, Profile.duckdbWritten, Profile.duckdb] at hr ⊢
    split
    · exact hr
    · rename_i hw
      simp only []
      split
      · rename_i x
        cases f <;> simp only [duckUn, UnFn.duckdbWritten] at hw ⊢ <;> (try split) <;>
          simp_all [UnFn.issue, domainIssue]
      · exact hr
  · have hr := Profile.reference_faithful.2 f v w h
    simp only [Profile.impl, Profile.duckdbWritten] at hr ⊢
    split
    · exact hr
    · rename_i hw
      simp only [Profile.duckdb]
      split
      case h_3 => exact hr
      all_goals
        cases f <;> simp only [duckBin, BinFn.duckdbWritten, BinFn.onFloats, Bool.false_eq_true,
          ite_true, ite_false] at hw ⊢ <;>
          (try split) <;> (try split) <;> (try split) <;>
          simp_all [BinFn.issue, nanIssue, domainIssue, BitOp.apply, atan2?, FloatCode.canon_zero] <;>
          first | omega | (split at h <;> simp at h)

/-- **A verified plan runs correctly on DuckDB.** When `Rel.mayIssues` reports
nothing but integer `SUM`s that may wrap (which keep their check), on every
catalog that satisfies the preconditions `A`, `F`, evaluating the plan with
DuckDB's functions gives `Rel.eval`'s rows, under DuckDB's IEEE operations
(the default), provided the plan's windows read fewer than `2⁶²` rows (the
size hypothesis, `Rel.Small`). Trusted: that `Profile.duckdb` is DuckDB's
(probed: `characterization/duckdb/probes.json`), that the SQL printer is
faithful, writing out `MIN % -1` and `<<` (`Profile.duckdbWritten`), and that
DuckDB's aggregates are Lean's (`AggFn.apply`): a profile gives only the
scalar functions. For a double `SUM` or `AVG` that last part does not hold in
general: DuckDB merges partial sums in finishing order and adds a constant
vector as one `fl(k · x)` (#633), so on those the conclusion holds of the
model, and what DuckDB gives is within #85's bound of it (`Profile.duckdb.table`'s
`sum_order` row, `approx`, proved in `float-bounds` as `StdModel.epsilon_sum_cr`
against the reference's correctly rounded sum, D25). -/
theorem Rel.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat (Profile.duckdbWritten s).impl = r.eval cat :=
  Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm (Profile.duckdbWritten_faithful s hieee)

/-- `Rel.duckdb_sound` on one hypothesis. -/
theorem Knowledge.duckdb_sound (s : DuckDBSettings) (hieee : s.ieeeOps = true) {cat : Catalog}
    (hcat : cat.WF) {K : KnowledgeEnv} (hK : K.Sound cat) {r : Rel} (hwf : r.WF cat)
    (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat K.cols K.facts (K.windows cat) false).all (·.1.assumed) = true) :
    r.eval cat (Profile.duckdbWritten s).impl = r.eval cat :=
  Rel.duckdb_sound s hieee hcat hK.cols hK.facts (hK.windows hcat) hwf hsmall hs hm

end Substrait
