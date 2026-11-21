import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant

noncomputable section
universe u v w
namespace Specs.NumAnalysis206.Newton.Kantorovich
open Set Metric Filter
open _root_.NumAnalysis206.Newton.Majorant
open Specs.NumAnalysis206.Newton

/-- The complete semilocal Newton–Kantorovich theorem (W77).
`A` is the actual derivative at `x₀`, so `A.symm` is its inverse.
The canonical sequence satisfies the raw Newton recurrence and has a valid
derivative inverse at every finite iterate. All conclusions refer to the same
root `p`. The non-strict parameter hypothesis includes the critical case;
larger-ball uniqueness explicitly requires the extended domain and derivative
bound and retains the strict upper radius. No inverse at `p` is assumed. -/
def Statement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (F : X → Y) (U : Set X) (x₀ : X) (A : X ≃L[𝕜] Y) (η L : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = A.toContinuousLinearMap →
    0 < η → 0 < L → 2 * η * L ≤ 1 →
    ‖A.symm (F x₀)‖ ≤ η → closedBall x₀ (lowerRoot η L) ⊆ U →
    (∀ z ∈ closedBall x₀ (lowerRoot η L), ∀ y ∈ closedBall x₀ (lowerRoot η L),
      ‖A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F z - fderiv 𝕜 F y)‖ ≤ L * ‖z - y‖) →
    let x := operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀
    IsExactRunValue (operatorNewtonValue (𝕜 := 𝕜) F) x₀ x ∧
    (∀ n : ℕ,
      operatorStepValidValue (𝕜 := 𝕜) F U (x n) ∧
      ‖x n - x₀‖ ≤ iterate η L n ∧ iterate η L n < lowerRoot η L ∧
      ‖x (n + 1) - x n‖ ≤ iterate η L (n + 1) - iterate η L n) ∧
    ∃ p ∈ closedBall x₀ (lowerRoot η L),
      F p = 0 ∧ Tendsto x atTop (nhds p) ∧
      (∀ y ∈ closedBall x₀ (lowerRoot η L), F y = 0 → y = p) ∧
      (∀ n : ℕ, ‖p - x n‖ ≤ lowerRoot η L - iterate η L n ∧
        ‖p - x (n + 1)‖ ≤ (1 / 2 : ℝ) * ‖p - x n‖) ∧
      (2 * η * L < 1 → ∀ n : ℕ,
        ‖p - x (n + 1)‖ ≤ (L / (2 * discriminant η L)) * ‖p - x n‖ ^ 2) ∧
      (2 * η * L < 1 → ∀ ρ : ℝ,
        lowerRoot η L ≤ ρ → ρ < upperRoot η L → closedBall x₀ ρ ⊆ U →
        (∀ z ∈ closedBall x₀ ρ, ∀ y ∈ closedBall x₀ ρ,
          ‖A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F z - fderiv 𝕜 F y)‖ ≤ L * ‖z - y‖) →
        ∀ y ∈ closedBall x₀ ρ, F y = 0 → y = p)

end Specs.NumAnalysis206.Newton.Kantorovich
