import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Normed.Module.Convex

/-! Independent statements of the two degenerate cases of W78.
A continuous linear equivalence `e` represents the actual derivative at the initial
point, so `e.symm` is precisely its bounded inverse. No positive constants or
radius expressions involving division are used. -/

universe u v w
namespace Specs.NumAnalysis206.Newton

/-- Zero residual certifies the root in the closed ball of radius zero; the
Newton update fixes it. No derivative bound on a neighborhood is needed. -/
def ZeroResidualStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
  ∀ (F : X → Y) (U : Set X) (x₀ : X) (e : X ≃L[𝕜] Y),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = (e : X →L[𝕜] Y) → ‖e.symm (F x₀)‖ ≤ 0 →
    F x₀ = 0 ∧ Metric.closedBall x₀ 0 = {x₀} ∧
      (∃ x ∈ Metric.closedBall x₀ 0, F x = 0) ∧
      operatorNewtonValue (𝕜 := 𝕜) F x₀ = x₀

/-- With the zero preconditioned derivative bound on the radius-η ball, `BF`
is affine there. The actual Newton update is valid, is the specified endpoint,
and is the unique root in that ball. The radius η may equal zero. -/
def ConstantDerivativeStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y],
  ∀ (F : X → Y) (U : Set X) (x₀ : X) (e : X ≃L[𝕜] Y) (η : ℝ),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = (e : X →L[𝕜] Y) → 0 ≤ η → ‖e.symm (F x₀)‖ ≤ η →
    Metric.closedBall x₀ η ⊆ U →
    (∀ x ∈ Metric.closedBall x₀ η, ∀ y ∈ Metric.closedBall x₀ η,
      ‖(e.symm : Y →L[𝕜] X).comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤
        0 * ‖x - y‖) →
    (∀ d : X, ‖d‖ ≤ η → e.symm (F (x₀ + d)) = e.symm (F x₀) + d) ∧
    operatorStepValidValue (𝕜 := 𝕜) F U x₀ ∧
    operatorNewtonValue (𝕜 := 𝕜) F x₀ = x₀ - e.symm (F x₀) ∧
    x₀ - e.symm (F x₀) ∈ Metric.closedBall x₀ η ∧
    F (x₀ - e.symm (F x₀)) = 0 ∧
    (∀ y ∈ Metric.closedBall x₀ η, F y = 0 → y = x₀ - e.symm (F x₀))

end Specs.NumAnalysis206.Newton
