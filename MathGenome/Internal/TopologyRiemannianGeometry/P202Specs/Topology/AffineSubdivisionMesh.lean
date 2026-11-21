import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularSubdivision
import Mathlib.Analysis.Convex.MetricSpace

noncomputable section
namespace P202Specs.AffineSubdivisionMesh
open Convexity P202Specs.SingularSubdivision
universe u v

/-- Quantitative vertex diameter estimate for iterates of the concrete affine
subdivision. No distinctness or nontriviality assumption is imposed. -/
def shrinkingVertexDiameter : Prop :=
  ∀ (R : Type u) [CommRing R] (Y : Type v) [ConvexSpace ℝ Y]
    [MetricSpace Y] [IsConvexDist Y] (n m : ℕ) (t : Fin (n+1) → Y)
    (r : ℝ), 0 ≤ r → (∀ i j, dist (t i) (t j) ≤ r) →
    ∀ q ∈ (((affineSubdivision R Y (n+1)) ^ m) (Finsupp.single t 1)).support,
      ∀ i j, dist (q i) (q j) ≤ (1 - 1 / ((n+1 : ℕ) : ℝ)) ^ m * r

end P202Specs.AffineSubdivisionMesh
