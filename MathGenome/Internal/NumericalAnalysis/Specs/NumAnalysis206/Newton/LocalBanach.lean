import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.LocalBanachStep

noncomputable section
universe u v w

namespace Specs.NumAnalysis206.Newton

/-- W76, including applicability from every point of the small closed ball.
The sequence uses the shared exact, root-absorbing Newton iteration; its
successor is also the raw Newton expression, including at a root. -/
def LocalBanachStatement : Prop :=
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
    b * L * r < 1 → b * L * r / (2 * (1 - b * L * r)) < 1 →
    ∀ x₀ ∈ Metric.closedBall p r,
    let x := operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀
    (∀ n, x n ∈ Metric.closedBall p r ∧
      operatorStepValidValue (𝕜 := 𝕜) F U (x n) ∧
      ‖(fderiv 𝕜 F (x n)).inverse‖ ≤ b / (1 - b * L * r) ∧
      ‖x (n + 1) - p‖ ≤ (b * L / (2 * (1 - b * L * r))) * ‖x n - p‖ ^ 2) ∧
    Filter.Tendsto x Filter.atTop (nhds p) ∧
    (L = 0 → ∀ n, x (n + 1) = p) ∧
    (∀ N, x N = p → ∀ k, x (N + k) = p)

/-- A positive admissible radius exists whenever the outer radius is positive,
including when either of the nonnegative constants is zero. -/
def LocalBanachRadiusStatement : Prop :=
  ∀ (b L R : ℝ), 0 ≤ b → 0 ≤ L → 0 < R →
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ b * L * r < 1 ∧
      b * L * r / (2 * (1 - b * L * r)) < 1

end Specs.NumAnalysis206.Newton
