import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CompactHullFrechet
import Mathlib.Analysis.Convex.TotallyBounded

/-! Compactness of closed convex hulls in real and complex Fréchet spaces. -/

namespace ExpandedFA.P1

/-- Compactness gives total boundedness. Local convexity preserves total
boundedness under real convex hulls, and closure also preserves it. Completeness
for the given topology's translation uniformity then gives compactness. -/
theorem compact_closed_convexHull_frechet : CompactHullFrechetSpec.CompactHull := by
  intro 𝕜 E _ _ _ _ _ _ hE K hK
  obtain ⟨⟨hadd, hsmul, _hmetric, hcomplete⟩, hconvex⟩ := hE
  let : IsTopologicalAddGroup E := hadd
  let : ContinuousSMul 𝕜 E := hsmul
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : LocallyConvexSpace ℝ E := hconvex
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  exact hK.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure

end ExpandedFA.P1
