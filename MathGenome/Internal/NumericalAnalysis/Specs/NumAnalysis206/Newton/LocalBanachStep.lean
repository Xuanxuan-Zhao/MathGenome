import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions

universe u v w

namespace Specs.NumAnalysis206.Newton

/-- The one-step part of W76. The inverse and Newton point are the canonical
ones belonging to the actual Fréchet derivative at the point being used.
A Lipschitz constant is nonnegative; it may be zero. No nontriviality of the
spaces or regularity outside the open domain is required. -/
def LocalBanachStepStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (F : X → Y) (U : Set X) (p : X) (A : X ≃L[𝕜] Y) (L R r : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U →
    F p = 0 → A.toContinuousLinearMap = fderiv 𝕜 F p →
    Metric.closedBall p R ⊆ U → 0 ≤ L →
    (∀ x ∈ Metric.closedBall p R, ∀ y ∈ Metric.closedBall p R,
      ‖fderiv 𝕜 F x - fderiv 𝕜 F y‖ ≤ L * ‖x - y‖) →
    0 < r → r ≤ R →
    let b := ‖A.symm.toContinuousLinearMap‖
    b * L * r < 1 → ∀ x ∈ Metric.closedBall p r,
      operatorStepValidValue (𝕜 := 𝕜) F U x ∧
      ‖(fderiv 𝕜 F x).inverse‖ ≤ b / (1 - b * L * r) ∧
      operatorNewtonValue (𝕜 := 𝕜) F x - p =
        (fderiv 𝕜 F x).inverse (F p - F x - fderiv 𝕜 F x (p - x)) ∧
      ‖operatorNewtonValue (𝕜 := 𝕜) F x - p‖ ≤
        (b * L / (2 * (1 - b * L * r))) * ‖x - p‖ ^ 2

end Specs.NumAnalysis206.Newton
