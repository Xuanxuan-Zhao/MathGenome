import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.FactorFourRate

/-! Independent statement of the strictness conclusion of
`fa2:p1:asplund-rate-strictness`, paper.tex 6950–7012.
The real normed space need not be complete. The functions are finite everywhere,
and strict convexity is the full function inequality for all interior weights.
The homogeneity and factor-four conclusions are supplied by FactorFourRate. -/
namespace ExpandedFA.Asplund.StrictnessPersistence.Spec

/-- Under the original iteration and quadratic comparability hypotheses,
strict convexity of either initial function persists in the common limit. -/
def ThetaStrictConvex : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ →
    (∀ (a : ℝ) (x : E), φ₀ (a • x) = a ^ 2 * φ₀ x) →
    (∀ (a : ℝ) (x : E), ψ₀ (a • x) = a ^ 2 * ψ₀ x) →
    ∀ C : ℝ, 0 ≤ C → (∀ x, φ₀ x ≤ (1 + C) * ψ₀ x) →
    (StrictConvexOn ℝ Set.univ φ₀ ∨ StrictConvexOn ℝ Set.univ ψ₀) →
    StrictConvexOn ℝ Set.univ (OrderLimit.Spec.thetaValue E φ₀ ψ₀)

end ExpandedFA.Asplund.StrictnessPersistence.Spec
