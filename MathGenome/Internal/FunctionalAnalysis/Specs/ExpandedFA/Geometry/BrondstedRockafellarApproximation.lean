import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.EpsilonSubgradient

/-! The quantitative approximation assertion of
`fa2:p2:brondsted-rockafellar`, paper.tex:12944–12951.
The primal values, finite-domain guard, and continuous real-linear dual are
those of the shared epsilon-subgradient and exact-subgradient interfaces.
-/
namespace ExpandedFA.Geometry.BrondstedRockafellarApproximation.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

universe u

/-- Quantitative Brøndsted–Rockafellar approximation on a real Banach space. -/
def Approximation : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (φ : ExtendedFunction X),
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ExpandedFA.P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    ∀ (x₀ : X) (f₀ : X →L[ℝ] ℝ) (ε : ℝ),
      0 < ε →
      f₀ ∈ ExpandedFA.Geometry.EpsilonSubgradient.Spec.EpsilonSubdifferentialValue X φ ε x₀ →
      ∀ k : ℝ, 0 < k →
        ∃ (x₁ : X) (f₁ : X →L[ℝ] ℝ),
          f₁ ∈ ExpandedFA.BanachConvex.Spec.SubdifferentialValue X φ x₁ ∧
          ‖x₁ - x₀‖ ≤ ε / k ∧ ‖f₁ - f₀‖ ≤ k

end ExpandedFA.Geometry.BrondstedRockafellarApproximation.Spec
