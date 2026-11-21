import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ConvexBodySetup
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Independent statements for the uniqueness and continuity stage of
`fa2:p2:projection-regularity`. The topology on central planes is the usual
Euclidean Grassmann topology, represented by their orthogonal projections.
Kernel directions are represented in the same way by orthogonal projections
onto the kernel. No smoothness hypothesis is imposed on the body. -/
namespace Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness

universe u
open Set
open ConvexBodySetup

structure CentralPlane (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  subspace : Submodule ℝ E
  finrank_eq_two : Module.finrank ℝ subspace = 2

noncomputable instance {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : TopologicalSpace (CentralPlane E) :=
  TopologicalSpace.induced (fun L => L.subspace.starProjection) inferInstance

def uniquenessType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
      ∀ L : Submodule ℝ E, Module.finrank ℝ L = 2 →
        ∃! P : E →L[ℝ] E, BodyProjection K L P

/-- Operator continuity as well as continuity of the one-dimensional kernels. -/
def continuityType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
      ∃ P : CentralPlane E → (E →L[ℝ] E),
        (∀ L, BodyProjection K L.subspace (P L)) ∧ Continuous P ∧
        (∀ L, Module.finrank ℝ (LinearMap.ker (P L).toLinearMap) = 1) ∧
        Continuous (fun L => (LinearMap.ker (P L).toLinearMap).starProjection)

end Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness
