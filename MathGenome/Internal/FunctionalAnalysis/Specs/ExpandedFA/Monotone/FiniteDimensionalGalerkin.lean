import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The finite-dimensional stage of paper.tex:7647–7662.
These statements are stronger than the reflexive Banach specialization:
completeness and reflexivity of the ambient space are not needed at this stage.
The radius precedes the quantification over all finite-dimensional subspaces.
No separability, positive dimension, or norm continuity is assumed. -/
namespace ExpandedFA.Monotone.Galerkin
universe u

/-- Restriction in both the argument and the testing variable, with the inherited norm. -/
def restriction {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (E : Submodule ℝ X) (A : X → X →L[ℝ] ℝ) : E → E →L[ℝ] ℝ :=
  fun x => (A x).comp E.subtypeL

namespace Spec

def FiniteRestrictionContinuous : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ),
    ExpandedFA.Monotone.Spec.BoundedOnBoundedSetsValue X A →
    ExpandedFA.Monotone.Spec.HemicontinuousValue X A →
    ExpandedFA.Monotone.Spec.MonotoneMapValue X A →
    ∀ (E : Submodule ℝ X) [FiniteDimensional ℝ E], Continuous (restriction E A)

def CoerciveOutwardRadius : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ),
    ExpandedFA.Monotone.Spec.CoerciveValue X A →
    ∀ f : X →L[ℝ] ℝ, ∃ R > 0, ∀ x : X, R ≤ ‖x‖ → 0 < (A x - f) x

def UniformGalerkin : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : X → X →L[ℝ] ℝ),
    ExpandedFA.Monotone.Spec.BoundedOnBoundedSetsValue X A →
    ExpandedFA.Monotone.Spec.HemicontinuousValue X A →
    ExpandedFA.Monotone.Spec.MonotoneMapValue X A →
    ExpandedFA.Monotone.Spec.CoerciveValue X A →
    ∀ f : X →L[ℝ] ℝ, ∃ R > 0,
      ∀ (E : Submodule ℝ X) [FiniteDimensional ℝ E],
        ∃ x : E, ‖x‖ ≤ R ∧ ∀ v : E, (A (x : X) - f) (v : X) = 0

end Spec
end ExpandedFA.Monotone.Galerkin
