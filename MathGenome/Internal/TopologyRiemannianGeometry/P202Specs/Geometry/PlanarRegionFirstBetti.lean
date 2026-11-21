import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The first rational Betti number in paper.tex 4811–4820.
The group here is the ordinary homology of the canonical finite singular
chains of the original closed planar region. No finite-type premise is added. -/
noncomputable section

namespace P202Specs.PlanarRegionFirstBetti.Expected

/-- Both finite dimensionality and the dimension of actual ordinary H₁. -/
def firstBettiNumber : Prop := ∀ R : P202Specs.PlanarRegionTopology.PlanarRegion,
  FiniteDimensional ℚ (P202Specs.SingularChains.homology ℚ ℚ
    (TopCat.of R.carrier) (1 : ℤ)) ∧
  Module.finrank ℚ (P202Specs.SingularChains.homology ℚ ℚ
    (TopCat.of R.carrier) (1 : ℤ)) = R.boundaryCount - 1

end P202Specs.PlanarRegionFirstBetti.Expected
