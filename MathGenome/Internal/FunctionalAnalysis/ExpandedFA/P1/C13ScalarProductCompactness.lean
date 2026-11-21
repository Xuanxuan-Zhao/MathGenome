import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13ScalarProductCompactness
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Compact products of scalar disks

Each scalar disk is a closed ball in a finite-dimensional real normed space,
and is therefore compact. Tychonoff's theorem gives compactness of their
arbitrary product in the product topology.
-/

namespace ExpandedFA.P1

/-- The manuscript's compactness lemma for products of scalar disks. -/
theorem compact_scalar_disk_products :
    C13ScalarProductCompactnessSpec.CompactScalarDiskProducts := by
  intro 𝕜 _ I r _hr
  let : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  apply isCompact_pi_infinite (s := fun i => {z : 𝕜 | ‖z‖ ≤ r i})
  intro i
  simpa only [Metric.closedBall, dist_zero_right] using
    (isCompact_closedBall (0 : 𝕜) (r i))

end ExpandedFA.P1
