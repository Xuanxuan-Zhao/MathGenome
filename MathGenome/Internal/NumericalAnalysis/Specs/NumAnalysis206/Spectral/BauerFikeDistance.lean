import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W39: the distance estimate in a specified subordinate norm, and its
specialization to every finite ℓ_p norm. A minimizing index records the actual
minimum without imposing a positive dimension: an eigenvalue hypothesis itself
rules out dimension zero. -/
noncomputable section
open scoped NNReal ENNReal
namespace Specs.NumAnalysis206.BauerFikeDistance
open _root_.NumAnalysis206.MatrixDefinitions

/-- The diagonal maximum property is required for every diagonal matrix in the
same specified vector norm. No exclusion of μ from the spectrum of A is made. -/
def distance_bound : Prop :=
  ∀ {K : Type*} [RCLike K] {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [FiniteDimensional K X] {n : ℕ} (b : Module.Basis (Fin n) K X),
    (∀ d : Fin n → K, subordinateNorm b b (Matrix.diagonal d) =
      ((Finset.univ.sup fun i => ‖d i‖₊ : ℝ≥0) : ℝ)) →
    ∀ (A V E : Matrix (Fin n) (Fin n) K) (lam : Fin n → K) (μ : K),
    IsUnit V → A = V * Matrix.diagonal lam * V⁻¹ →
    μ ∈ spectrum K (A + E) →
    ∃ i : Fin n, (∀ j, ‖μ - lam i‖ ≤ ‖μ - lam j‖) ∧
      ‖μ - lam i‖ ≤ subordinateNorm b b V * subordinateNorm b b V⁻¹ *
        subordinateNorm b b E

/-- Every exponent 1 ≤ p ≤ ∞, in the actual subordinate ℓ_p matrix norm. -/
def lp_distance_bound : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p)
    (A V E : Matrix (Fin n) (Fin n) K) (lam : Fin n → K) (μ : K),
    IsUnit V → A = V * Matrix.diagonal lam * V⁻¹ →
    μ ∈ spectrum K (A + E) →
    ∃ i : Fin n, (∀ j, ‖μ - lam i‖ ≤ ‖μ - lam j‖) ∧
      ‖μ - lam i‖ ≤ lpOperatorNorm p hp V * lpOperatorNorm p hp V⁻¹ *
        lpOperatorNorm p hp E

end Specs.NumAnalysis206.BauerFikeDistance
