import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EquivalentBases
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12BoundedSequences

/-! The two assertions of `fa2:p1:basic-selection`, paper.tex:4163–4200.
The closed span, its inherited norm, ordered unique expansions and the real
supremum of the actual truncation norms are the accepted upstream objects.
The weak topology uses the original continuous scalar-linear dual.
Index zero denotes the manuscript's first term. -/
noncomputable section
universe u v
namespace ExpandedFA.P1.BasicSelection.Spec
open Filter Topology
open ExpandedFA.P1.EquivalentBases.Spec

/-- The first assertion includes the numerical bound for genuine coordinate
truncations, not merely the existence of some finite-prefix bound. -/
def NormalizedBasicSequence : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ¬FiniteDimensional 𝕜 E → ∀ M : ℝ, 1 < M →
    ∃ x : ℕ → E, (∀ n, ‖x n‖ = 1) ∧
      ∃ h : IsBasicSequence (𝕜 := 𝕜) x,
        ∃ T : ℕ → closedSpan (𝕜 := 𝕜) x →L[𝕜] closedSpan (𝕜 := 𝕜) x,
          (∀ N z, T N z = C15Basis.Spec.rawPartialSum h N z) ∧
          C15PartialSums.Spec.basisConstant T ≤ M

/-- Failure of norm convergence is retained; the original sequence need not
be seminormalized or have all its terms nonzero. The subsequence indices are
strictly increasing. -/
def WeaklyNullBasicSubsequence : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (s : ℕ → E),
    Tendsto s atTop
      (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) 0) →
    ¬Tendsto s atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsBasicSequence (𝕜 := 𝕜) (s ∘ φ)

end ExpandedFA.P1.BasicSelection.Spec
