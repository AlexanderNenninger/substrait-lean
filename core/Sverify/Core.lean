import Sverify.Core.BlackBox
import Sverify.Core.Conversions
import Sverify.Core.Dedup
import Sverify.Core.Digest
import Sverify.Core.Float
import Sverify.Core.FloatArith
import Sverify.Core.FloatExact
import Sverify.Core.FloatFormat
import Sverify.Core.FloatMoments
import Sverify.Core.Forall2
import Sverify.Core.Numeric
import Sverify.Core.Reflect
import Sverify.Core.Regex
import Sverify.Core.Rounding
import Sverify.Core.Text
import Sverify.Core.Time
import Sverify.Core.Value
import Sverify.Core.VarcharCasts

/-! The core (#1189): the reference's semantics. It imports nothing but
Lean, which the standalone build of this package checks. -/
