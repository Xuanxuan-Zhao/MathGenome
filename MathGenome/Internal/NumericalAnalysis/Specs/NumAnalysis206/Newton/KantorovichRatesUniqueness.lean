import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant

noncomputable section
universe u v w
namespace Specs.NumAnalysis206.Newton.KantorovichRatesUniqueness
open Set Metric Filter
open _root_.NumAnalysis206.Newton.Majorant
open Specs.NumAnalysis206.Newton

/-- W77: quadratic comparison for every zero in the full closed small ball,
uniqueness there, and linear and strict-case quadratic convergence rates.
No inverse at the limiting zero is assumed. -/
def Statement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (F : X → Y) (U : Set X) (x₀ : X) (A : X ≃L[𝕜] Y) (η L : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = A.toContinuousLinearMap →
    0 < η → 0 < L → 2 * η * L ≤ 1 →
    ‖A.symm (F x₀)‖ ≤ η → closedBall x₀ (lowerRoot η L) ⊆ U →
    (∀ x ∈ closedBall x₀ (lowerRoot η L), ∀ y ∈ closedBall x₀ (lowerRoot η L),
      ‖A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖) →
    let x := operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀
    (∀ y ∈ closedBall x₀ (lowerRoot η L), F y = 0 →
      (∀ n : ℕ, ‖y - x (n + 1)‖ ≤ coefficient η L n * ‖y - x n‖ ^ 2) ∧
      (∀ n : ℕ, ‖y - x n‖ ≤ error η L n)) ∧
    ∃ p ∈ closedBall x₀ (lowerRoot η L),
      F p = 0 ∧ Tendsto x atTop (nhds p) ∧
      (∀ y ∈ closedBall x₀ (lowerRoot η L), F y = 0 → y = p) ∧
      (∀ n : ℕ, ‖p - x (n + 1)‖ ≤ (1 / 2 : ℝ) * ‖p - x n‖) ∧
      (2 * η * L < 1 → ∀ n : ℕ,
        ‖p - x (n + 1)‖ ≤ (L / (2 * discriminant η L)) * ‖p - x n‖ ^ 2)

end Specs.NumAnalysis206.Newton.KantorovichRatesUniqueness
