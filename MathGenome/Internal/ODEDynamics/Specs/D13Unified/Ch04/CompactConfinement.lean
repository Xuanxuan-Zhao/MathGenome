import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap

/-! Independent statement of paper.tex, Corollary d13:04:confinement.
The forward part of the maximal solution through `(s, ξ)` is considered on
its actual domain. For each real horizon `B > s` a different compact state
set is allowed; the full closed time-state product must lie in the original
open domain. No bound on values outside the solution interval is imposed. -/
noncomputable section
open Set
open D13Unified

namespace Specs.D13Unified.Ch04.CompactConfinement
open Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u

def compactConfinementExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ODE E), locallyLipschitzInStateValue F →
    ∀ (s : ℝ) (ξ : E), (s, ξ) ∈ F.domain →
      (∀ B : ℝ, s < B → ∃ K : Set E, IsCompact K ∧
        Icc s B ×ˢ K ⊆ F.domain ∧
        ∀ t ∈ (maximalIntervalValue F s ξ).carrier,
          t ∈ Ico s B → solutionValueValue F t s ξ ∈ K) →
      upperEndpointValue F s ξ = ⊤

end Specs.D13Unified.Ch04.CompactConfinement
