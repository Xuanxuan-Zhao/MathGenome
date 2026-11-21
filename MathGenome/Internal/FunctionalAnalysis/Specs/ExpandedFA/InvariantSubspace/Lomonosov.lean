import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.Complex.Basic

/-! Independent specifications for Lomonosov's theorem,
paper.tex:9697–9701, `fa2:p2:lomonosov`.

The ambient space is an arbitrary complex Banach space. Nonscalar means
unequal to every complex scalar multiple of the identity. Hyperinvariance
is invariance under every bounded complex-linear operator commuting with T.
Compactness uses the shared definition, in the original norm topology.
-/
namespace ExpandedFA.InvariantSubspace.Lomonosov.Spec

universe u

/-- The full hyperinvariant-subspace assertion. -/
def HyperinvariantSubspace : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    (∀ c : ℂ, T ≠ c • ContinuousLinearMap.id ℂ X) →
    ∀ K : X →L[ℂ] X,
      Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
      K ≠ 0 → Commute T K →
      ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
        ∀ S : X →L[ℂ] X, Commute T S → ∀ x ∈ M, S x ∈ M

/-- The stated invariant-subspace consequence, with the same hypotheses. -/
def InvariantSubspaceConsequence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    (∀ c : ℂ, T ≠ c • ContinuousLinearMap.id ℂ X) →
    ∀ K : X →L[ℂ] X,
      Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
      K ≠ 0 → Commute T K →
      ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
        ∀ x ∈ M, T x ∈ M

end ExpandedFA.InvariantSubspace.Lomonosov.Spec
