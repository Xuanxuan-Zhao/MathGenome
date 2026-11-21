import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant

noncomputable section
universe u v w
namespace Specs.NumAnalysis206.Newton.KantorovichExistence
open Set Metric Filter
open _root_.NumAnalysis206.Newton.Majorant
open Specs.NumAnalysis206.Newton

/-- W77: telescoping estimate, Cauchy convergence, and a root with the
majorant error radius, under the original semilocal hypotheses. The
non-strict parameter inequality includes the double-root case. -/
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
    (∀ n j : ℕ, n ≤ j → ‖x j - x n‖ ≤ iterate η L j - iterate η L n) ∧
    CauchySeq x ∧
    ∃ p ∈ closedBall x₀ (lowerRoot η L),
      F p = 0 ∧ Tendsto x atTop (nhds p) ∧
      ∀ n : ℕ, ‖p - x n‖ ≤ lowerRoot η L - iterate η L n

end Specs.NumAnalysis206.Newton.KantorovichExistence
