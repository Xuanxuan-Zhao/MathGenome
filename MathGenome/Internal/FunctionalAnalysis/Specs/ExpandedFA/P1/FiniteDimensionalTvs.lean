import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for `fa2:p1:finite-dimensional-tvs`, paper.tex:1791–1796.
All spaces carry their given topology. No norm, local convexity, completeness,
or metrizability of the vector space is assumed.

The usual Euclidean topology is the topology pulled back from the ordinary
finite product of copies of the scalar field by a basis coordinate map.
The equality is required for every finite basis, including the empty basis.
For complex scalars this is the ordinary topology on complex coordinate space
(equivalently real coordinate space of twice the dimension).
-/

namespace ExpandedFA.P1.FiniteDimensionalTvsSpec

/-- Every finite basis identifies the given Hausdorff vector topology with
the usual finite-coordinate topology. -/
def EuclideanTopology : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ (ι : Type*) [Finite ι] (b : Module.Basis ι 𝕜 E),
      t = TopologicalSpace.induced b.equivFun inferInstance

/-- Finite-dimensional subspaces of an arbitrary Hausdorff TVS are closed
in the ambient topology. -/
def FiniteDimensionalSubspacesClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, FiniteDimensional 𝕜 M → IsClosed (M : Set E)

/-- Local compactness of the given Hausdorff vector topology implies finite
dimension over the original scalar field. -/
def LocallyCompactFiniteDimensional : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E],
    LocallyCompactSpace E → FiniteDimensional 𝕜 E

end ExpandedFA.P1.FiniteDimensionalTvsSpec
