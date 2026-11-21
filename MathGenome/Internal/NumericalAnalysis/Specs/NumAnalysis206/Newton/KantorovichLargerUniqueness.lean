import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant

noncomputable section
universe u v w
namespace Specs.NumAnalysis206.Newton.KantorovichLargerUniqueness
open Set Metric Filter
open _root_.NumAnalysis206.Newton.Majorant
open Specs.NumAnalysis206.Newton

/-- W77, larger-radius uniqueness. All derivative bounds are restricted to the
specified larger closed ball. Its radius is strictly below the upper root. -/
def Statement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (F : X → Y) (U : Set X) (x₀ : X) (A : X ≃L[𝕜] Y) (η L ρ : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = A.toContinuousLinearMap →
    0 < η → 0 < L → 2 * η * L < 1 →
    ‖A.symm (F x₀)‖ ≤ η →
    lowerRoot η L ≤ ρ → ρ < upperRoot η L → closedBall x₀ ρ ⊆ U →
    (∀ x ∈ closedBall x₀ ρ, ∀ y ∈ closedBall x₀ ρ,
      ‖A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖) →
    (∀ y ∈ closedBall x₀ ρ, F y = 0 →
      0 ≤ majorant η L ‖y - x₀‖ ∧ ‖y - x₀‖ ≤ lowerRoot η L) ∧
    ∃ p ∈ closedBall x₀ (lowerRoot η L), F p = 0 ∧
      Tendsto (operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀) atTop (nhds p) ∧
      ∀ y ∈ closedBall x₀ ρ, F y = 0 → y = p

end Specs.NumAnalysis206.Newton.KantorovichLargerUniqueness
