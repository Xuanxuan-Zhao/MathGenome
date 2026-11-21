import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-! Independent statements for Goldstine's theorem, paper.tex 2707–2732.
The continuous dual and bidual retain their normed-space definitions. The
closure explicitly uses σ(E″, E′), transported to the original bidual carrier.
No completeness, reflexivity, or nonzero-dimension hypothesis is imposed. -/
namespace ExpandedFA.P1.C14Goldstine.Spec
universe u v
noncomputable section

/-- Simultaneous approximation on any finite set of continuous linear tests. -/
def FiniteApproximation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜), ‖ξ‖ ≤ 1 →
    ∀ (s : Finset (E →L[𝕜] 𝕜)) (ε : ℝ), 0 < ε →
      ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ f ∈ s, ‖f x - ξ f‖ < ε

/-- The family formulation includes the empty family m = 0. -/
def FiniteFamilyApproximation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (ξ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜), ‖ξ‖ ≤ 1 →
    ∀ (m : ℕ) (f : Fin m → E →L[𝕜] 𝕜) (ε : ℝ), 0 < ε →
      ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ j, ‖f j x - ξ (f j)‖ < ε

/-- Ambient weak-star closure equality gives density relative to the bidual ball,
and also records that the canonical image stays inside that ball. -/
def Density : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    @closure ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' {x : E | ‖x‖ ≤ 1}) =
      {ξ | ‖ξ‖ ≤ 1}

end
end ExpandedFA.P1.C14Goldstine.Spec
