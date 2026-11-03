import SubstraitLean.Aggregate

/-!
# What a statistical aggregate may give (#85)

`VARIANCE`, `STDDEV`, `COVAR_SAMP`/`COVAR_POP` and `CORR` are computed by each
engine's own algorithm (decided on #54). The reference allows any value with
their generic properties (`StatProps`), the set `AggFn.Allowed` uses
(`SubstraitLean/Allowed.lean`). The float-bounds work (#85) states those
properties: `NULL` where the reference says, a variance or deviation `≥ 0`, and
an error bound on the co-moment.

For now `StatProps` is the reference's own formula, the one value
`AggFn.apply` gives; #85 widens it to the properties. `StatProps.apply` is the
witness every version keeps.
-/

namespace Substrait

/-- The values a statistical aggregate `f` of `vs` may give. -/
def StatProps (f : AggFn) (vs : List Value) (v : Value) : Prop := v = f.apply vs

/-- The reference's own value is allowed. -/
theorem StatProps.apply (f : AggFn) (vs : List Value) : StatProps f vs (f.apply vs) := rfl

end Substrait
