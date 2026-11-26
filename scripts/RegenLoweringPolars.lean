import Sverify.Engines.LoweringSearch
import Sverify.Polars.LoweringSchemas

/-!
# Regenerating the Polars lowering (`poe regen-lowering`)

Runs the lowering generator's search (`engines/Sverify/Engines/LoweringSearch.lean`)
for Polars's profile and writes what it finds, entries and proofs, to
`engines/polars/Sverify/Polars/LoweringOn`. A build checks those modules and
never searches; run this when `Profile.polars`, the generator or the model's
functions change. Not part of the library: `lake build` does not elaborate it.
-/

namespace Substrait

attribute [local instance] Boxes.Ambient.none in
generate_lowering polarsOn : Profile.polars
  unfolding [Profile.polars, UnFn.polarsTmpl, BinFn.polarsTmpl]
  using []
  -- Polars has no shift (polars-int-shift): `&`, `|`, `^` are schemas of the native call.
  excluding [BinFn.bit]
  hand_written LoweringSearch.polarsSchemas
  writing "engines/polars/Sverify/Polars/LoweringOn"
  refusing [BinFn.fmod, UnFn.ftod]

end Substrait
