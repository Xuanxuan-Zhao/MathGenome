import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Order.WithTop

/-! Independent statement of `fa2:p1:fenchel-rockafellar`, paper.tex:5236–5247.
The functions take values in `WithTop ℝ = (-∞,+∞]`. Infima and suprema
are in the full extended real line, retaining the possible value −∞.
Continuity is at the given common finite-domain point for the original
LCS topology. Neither completeness nor lower semicontinuity is assumed. -/
namespace ExpandedFA.P1.FenchelRockafellar

open ExtendedConvexFunctions

/-- The same continuous-dual conjugate as in C06, on a general real TVS. -/
noncomputable def conjugate {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (φ : ExtendedFunction E) (f : E →L[ℝ] ℝ) : EReal :=
  ⨆ x, (f x : EReal) - C06Conjugates.Spec.ExtendedRealValueValue (φ x)

/-- The primal infimum, including the unbounded-below case. -/
noncomputable def primalValue {E : Type*} (φ ψ : ExtendedFunction E) : EReal :=
  ⨅ x, C06Conjugates.Spec.ExtendedRealValueValue (φ x) +
    C06Conjugates.Spec.ExtendedRealValueValue (ψ x)

/-- Every conjugate is > −∞ for proper inputs, so the two negated
conjugates are in [−∞,+∞), and their sum is unambiguous. -/
noncomputable def dualValue {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (φ ψ : ExtendedFunction E) (f : E →L[ℝ] ℝ) : EReal :=
  -conjugate φ f - conjugate ψ (-f)

namespace Spec

def Duality : Prop :=
  ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E],
    LCS ℝ E → ∀ (φ ψ : ExtendedFunction E),
      ExtendedConvexFunctions.Spec.ProperValue E φ →
      ExtendedConvexFunctions.Spec.ProperValue E ψ →
      ExtendedConvexFunctions.Spec.ExtendedConvexValue E φ →
      ExtendedConvexFunctions.Spec.ExtendedConvexValue E ψ →
      ∀ x₀ : E, φ x₀ ≠ ⊤ → ψ x₀ ≠ ⊤ → ContinuousAt φ x₀ →
        primalValue φ ψ = ⨆ f : E →L[ℝ] ℝ, dualValue φ ψ f ∧
        ∀ a : ℝ, primalValue φ ψ = (a : EReal) →
          ∃ f : E →L[ℝ] ℝ, dualValue φ ψ f = (a : EReal)

/-- The LCS extension agrees with the previously established conjugate
on every real normed space. -/
def NormedConjugateAgreement : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (f : E →L[ℝ] ℝ),
    conjugate φ f = C06Conjugates.Spec.ConvexConjugateValue E φ f

end Spec
end ExpandedFA.P1.FenchelRockafellar
