import Sverify.Frontend.Bind
import Sverify.Frontend.Guard
import Sverify.Frontend.GuardedColumns
import Sverify.Frontend.Parse
import Sverify.Frontend.SubstraitJson
import Sverify.Frontend.Write

/-! The frontend (#1189): what reads a plan into the model, the Substrait JSON
parser first, and what writes it back: the writer (`Write`) and the pass that
binds shared arguments to columns before a plan is written (`Bind`). It
imports only the core and the analysis, which the standalone build of this
package checks. -/
