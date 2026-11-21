import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.OrderLimit

/-! Independent statements for the quantitative part of
`fa2:p1:asplund-rate-strictness` (paper.tex 6950–6983).
The space is real normed, possibly incomplete. Quadratic homogeneity
allows degenerate seminorms; no positivity away from zero is required. -/
namespace ExpandedFA.Asplund.FactorFourRate.Spec

/-- Both iterated functions retain quadratic homogeneity for every real scalar. -/
def IteratesHomogeneous : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ →
    (∀ (a : ℝ) (x : E), φ₀ (a • x) = a ^ 2 * φ₀ x) →
    (∀ (a : ℝ) (x : E), ψ₀ (a • x) = a ^ 2 * ψ₀ x) →
    ∀ n,
      (∀ (a : ℝ) (x : E), Iteration.Spec.phiValue E φ₀ ψ₀ n (a • x) =
        a ^ 2 * Iteration.Spec.phiValue E φ₀ ψ₀ n x) ∧
      (∀ (a : ℝ) (x : E), Iteration.Spec.psiValue E φ₀ ψ₀ n (a • x) =
        a ^ 2 * Iteration.Spec.psiValue E φ₀ ψ₀ n x)

/-- The common finite pointwise limit has the same homogeneity. -/
def ThetaHomogeneous : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ →
    (∀ (a : ℝ) (x : E), φ₀ (a • x) = a ^ 2 * φ₀ x) →
    (∀ (a : ℝ) (x : E), ψ₀ (a • x) = a ^ 2 * ψ₀ x) →
    ∀ (a : ℝ) (x : E), OrderLimit.Spec.thetaValue E φ₀ ψ₀ (a • x) =
      a ^ 2 * OrderLimit.Spec.thetaValue E φ₀ ψ₀ x

/-- The geometric comparison, with `4⁻ⁿ` expressed as `1 / 4^n`. -/
def FactorFourBound : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ →
    (∀ (a : ℝ) (x : E), φ₀ (a • x) = a ^ 2 * φ₀ x) →
    (∀ (a : ℝ) (x : E), ψ₀ (a • x) = a ^ 2 * ψ₀ x) →
    ∀ C : ℝ, 0 ≤ C → (∀ x, φ₀ x ≤ (1 + C) * ψ₀ x) →
    ∀ (n : ℕ) (x : E), Iteration.Spec.phiValue E φ₀ ψ₀ n x ≤
      (1 + C / (4 : ℝ) ^ n) * Iteration.Spec.psiValue E φ₀ ψ₀ n x

end ExpandedFA.Asplund.FactorFourRate.Spec
