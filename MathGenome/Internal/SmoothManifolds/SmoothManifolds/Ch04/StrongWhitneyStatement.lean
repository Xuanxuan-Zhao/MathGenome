import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.StrongWhitneyStatement
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses

/-! The cited strong Whitney bounds, recorded solely as statement interfaces.

The proofs of these propositions belong to differential topology, as specified
in the paragraph following M04.03 of the manuscript. This module provides no
inhabitant of either proposition and no axiom asserting either bound.
-/
namespace SmoothManifolds.StrongWhitney
open ModelData AtlasData MapData BoundaryData MapClassData StrongWhitneyData
universe u

/-- Strong Whitney embedding bound for arbitrary boundaryless smooth manifolds.
The target atlas contains the identity chart and hence is the standard one.
This conclusion does not require the embedding to be proper. -/
def strongEmbeddingStatement : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (M : Type u) [TopologicalSpace M] (a : ModelKind)
      (S : SmoothManifold n a M),
      intrinsicBoundary S = ∅ →
      ∃ T : SmoothManifold (2 * n) .euclidean (Euclidean (2 * n)),
        standardEuclideanChart (2 * n) ∈ T.smoothStructure.val ∧
        ∃ f : M → Euclidean (2 * n), IsSmoothEmbedding S T f

/-- Strong Whitney immersion bound for arbitrary boundaryless smooth manifolds.
Both smoothness and injectivity of the full tangent differential are required. -/
def strongImmersionStatement : Prop :=
  ∀ (n : ℕ), 1 < n →
    ∀ (M : Type u) [TopologicalSpace M] (a : ModelKind)
      (S : SmoothManifold n a M),
      intrinsicBoundary S = ∅ →
      ∃ T : SmoothManifold (2 * n - 1) .euclidean (Euclidean (2 * n - 1)),
        standardEuclideanChart (2 * n - 1) ∈ T.smoothStructure.val ∧
        ∃ f : M → Euclidean (2 * n - 1), IsSmoothMap S T f ∧ IsImmersion S T f

end SmoothManifolds.StrongWhitney
