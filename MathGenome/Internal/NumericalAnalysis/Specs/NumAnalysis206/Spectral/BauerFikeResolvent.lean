import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W39, first inequality. The coordinate space and its norm are arbitrary;
`subordinateNorm` is the induced operator norm in the chosen basis. -/
noncomputable section

namespace Specs.NumAnalysis206.BauerFikeResolvent

/-- Resolvent form of Bauer--Fike, for every specified subordinate norm.
The spectrum here is the algebraic spectrum of the actual matrices. -/
def resolvent_bound : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [FiniteDimensional ℂ X] {n : ℕ} (b : Module.Basis (Fin n) ℂ X)
    (A V E : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ) (μ : ℂ),
    IsUnit V → A = V * Matrix.diagonal lam * V⁻¹ →
    μ ∈ spectrum ℂ (A + E) → μ ∉ spectrum ℂ A →
    1 ≤ NumAnalysis206.MatrixDefinitions.subordinateNorm b b
          ((μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam)⁻¹) *
        NumAnalysis206.MatrixDefinitions.subordinateNorm b b (V⁻¹ * E * V)

end Specs.NumAnalysis206.BauerFikeResolvent
