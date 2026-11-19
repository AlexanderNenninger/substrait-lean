import Sverify.Analysis.AllowedAnalysis
import Sverify.Analysis.Choices
import Sverify.Analysis.ChoicesSound
import Sverify.Analysis.Contracts
import Sverify.Analysis.Contracts.Facts
import Sverify.Analysis.Contracts.Lattice
import Sverify.Analysis.Contracts.Plan
import Sverify.Analysis.Contracts.Refine
import Sverify.Analysis.Contracts.Sound
import Sverify.Analysis.Contracts.Transfer
import Sverify.Analysis.Contracts.TransferSound
import Sverify.Analysis.Guards
import Sverify.Analysis.Incremental
import Sverify.Analysis.Infer
import Sverify.Analysis.Keys
import Sverify.Analysis.Knowledge
import Sverify.Analysis.MarginSound
import Sverify.Analysis.Partition
import Sverify.Analysis.ProfileImpl
import Sverify.Analysis.Quarantine
import Sverify.Analysis.Refines
import Sverify.Analysis.Refresh
import Sverify.Analysis.Retention
import Sverify.Analysis.Rows
import Sverify.Analysis.Safety
import Sverify.Analysis.Seam
import Sverify.Analysis.Terms
import Sverify.Analysis.TouchedFrames
import Sverify.Analysis.TouchedGroups
import Sverify.Analysis.WSet
import Sverify.Analysis.Weighted

/-! The analysis (#1189, step 3b): what `verify` proves of a plan under the
core, engine-free. It imports only the core, which the standalone build of
this package checks. -/
