import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Homeomorph.Lemmas

/-! Independent statements of the two cited strong Whitney bounds.

These are definitions of propositions, not proofs or assumed certificates.
The manuscript (paper.tex, paragraph following M04.03) assigns their proofs
 to differential topology. No compactness or connectedness is imposed.
-/
namespace SmoothManifolds.StrongWhitneyData
open ModelData

/-- The global identity coordinate chart on the actual real vector space.
The subtype in the chart target is the shared Euclidean model, whose
underlying set is all of `Euclidean q`. -/
def standardEuclideanChart (q : ℕ) : ModelChart q .euclidean (Euclidean q) :=
  (Homeomorph.Set.univ (Euclidean q)).symm.toOpenPartialHomeomorph

end SmoothManifolds.StrongWhitneyData

namespace Specs.SmoothManifolds.Ch04.StrongWhitneyStatement
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.StrongWhitneyData
universe u

/-- The interface is itself a proposition, rather than a proof of the bound. -/
def strongEmbeddingStatementType := Prop

/-- Every boundaryless smooth n-manifold embeds in the standard R^(2n)
for n > 0. Membership of the global identity chart fixes the maximal target
atlas to be the standard Euclidean smooth structure, excluding exotic choices.
The target structure is existentially packaged with the map, so this statement
requires no additional target-structure hypothesis. Properness is not asserted. -/
def strongEmbeddingStatementValue : strongEmbeddingStatementType :=
  ∀ (n : ℕ), 0 < n →
    ∀ (M : Type u) [TopologicalSpace M] (a : ModelKind)
      (S : SmoothManifold n a M),
      intrinsicBoundary S = ∅ →
      ∃ T : SmoothManifold (2 * n) .euclidean (Euclidean (2 * n)),
        standardEuclideanChart (2 * n) ∈ T.smoothStructure.val ∧
        ∃ f : M → Euclidean (2 * n), IsSmoothEmbedding S T f

/-- As with the embedding interface, this is only the type of a statement. -/
def strongImmersionStatementType := Prop

/-- Every boundaryless smooth n-manifold admits a smooth immersion into
standard R^(2n-1) for n > 1. Smoothness is explicit: the canonical immersion
predicate alone requires only C¹ regularity. -/
def strongImmersionStatementValue : strongImmersionStatementType :=
  ∀ (n : ℕ), 1 < n →
    ∀ (M : Type u) [TopologicalSpace M] (a : ModelKind)
      (S : SmoothManifold n a M),
      intrinsicBoundary S = ∅ →
      ∃ T : SmoothManifold (2 * n - 1) .euclidean (Euclidean (2 * n - 1)),
        standardEuclideanChart (2 * n - 1) ∈ T.smoothStructure.val ∧
        ∃ f : M → Euclidean (2 * n - 1), IsSmoothMap S T f ∧ IsImmersion S T f

end Specs.SmoothManifolds.Ch04.StrongWhitneyStatement
