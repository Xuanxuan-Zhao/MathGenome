import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Definitions
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.Majorant

noncomputable section
universe u v w
namespace Specs.NumAnalysis206.Newton.KantorovichSteps
open Set Metric
open _root_.NumAnalysis206.Newton.Majorant
open Specs.NumAnalysis206.Newton

/-- Preconditioning by the actual inverse of the derivative at the starting point.
The formula for the derivative is asserted only on the open domain. -/
def PreconditioningStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) (Y : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (F : X → Y) (U : Set X) (x₀ : X) (A : X ≃L[𝕜] Y),
    IsOpen U → DifferentiableOn 𝕜 F U → x₀ ∈ U →
    fderiv 𝕜 F x₀ = A.toContinuousLinearMap →
    let G : X → X := fun x => A.symm (F x)
    DifferentiableOn 𝕜 G U ∧ fderiv 𝕜 G x₀ = ContinuousLinearMap.id 𝕜 X ∧
    ∀ x ∈ U,
      fderiv 𝕜 G x = A.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x) ∧
      ((fderiv 𝕜 G x).IsInvertible ↔ (fderiv 𝕜 F x).IsInvertible) ∧
      operatorNewtonValue (𝕜 := 𝕜) G x = operatorNewtonValue (𝕜 := 𝕜) F x

/-- The simultaneous finite-step bounds of W77. The sequence is the canonical
exact Newton sequence; no validity, invariance, or convergence is assumed.
All inverse bounds are at finite iterates, including at the critical parameter. -/
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
    let G : X → X := fun x => A.symm (F x)
    let x := operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀
    DifferentiableOn 𝕜 G U ∧ fderiv 𝕜 G x₀ = ContinuousLinearMap.id 𝕜 X ∧
    (∀ z ∈ closedBall x₀ (lowerRoot η L), ∀ y ∈ closedBall x₀ (lowerRoot η L),
      ‖fderiv 𝕜 G z - fderiv 𝕜 G y‖ ≤ L * ‖z - y‖) ∧
    (∀ z ∈ U, ((fderiv 𝕜 G z).IsInvertible ↔ (fderiv 𝕜 F z).IsInvertible) ∧
      operatorNewtonValue (𝕜 := 𝕜) G z = operatorNewtonValue (𝕜 := 𝕜) F z) ∧
    ∀ n : ℕ,
      operatorStepValidValue (𝕜 := 𝕜) F U (x n) ∧
      (fderiv 𝕜 G (x n)).IsInvertible ∧
      ‖x n - x₀‖ ≤ iterate η L n ∧ iterate η L n < lowerRoot η L ∧
      ‖G (x n)‖ ≤ majorant η L (iterate η L n) ∧
      ‖(fderiv 𝕜 G (x n)).inverse‖ ≤ 1 / (1 - L * iterate η L n) ∧
      ‖x (n + 1) - x n‖ ≤ iterate η L (n + 1) - iterate η L n

end Specs.NumAnalysis206.Newton.KantorovichSteps
