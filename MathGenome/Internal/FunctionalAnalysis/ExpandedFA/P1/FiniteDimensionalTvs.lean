import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteDimensionalTvs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite-dimensional and locally compact Hausdorff TVSs over ℝ or ℂ.
The library results used here are for general TVSs, with the given topology;
in particular they do not assume a norm or local convexity on the space.
-/

namespace ExpandedFA.P1

/-- The coordinate homeomorphism gives equality of the topologies, for every
finite basis, rather than merely an abstract homeomorphism of the spaces. -/
theorem finite_dimensional_tvs_euclidean_topology :
    FiniteDimensionalTvsSpec.EuclideanTopology := by
  intro 𝕜 E _ _ _ _ _ _ _ ι _ b
  exact b.equivFunL.toHomeomorph.isInducing.eq_induced

theorem finite_dimensional_subspace_closed :
    FiniteDimensionalTvsSpec.FiniteDimensionalSubspacesClosed := by
  intro 𝕜 E _ _ _ _ _ _ _ M hM
  let : FiniteDimensional 𝕜 M := hM
  exact M.closed_of_finiteDimensional

theorem locally_compact_tvs_finite_dimensional :
    FiniteDimensionalTvsSpec.LocallyCompactFiniteDimensional := by
  intro 𝕜 E _ _ _ _ _ _ _ hcompact
  let : LocallyCompactSpace E := hcompact
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

end ExpandedFA.P1
