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
-/

namespace Substrait

theorem Profile.reference_faithful : Profile.reference.impl.Faithful :=
  ⟨fun f v h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val],
   fun f v w h => by simp [Profile.impl, Profile.reference, raiseIf, h, Outcome.val]⟩

end Substrait
