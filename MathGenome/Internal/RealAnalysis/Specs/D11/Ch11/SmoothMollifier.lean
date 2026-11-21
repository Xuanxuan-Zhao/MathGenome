import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionBound
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! The explicit mollifier and regularization prerequisites of paper.tex:3789–3797.
All integrals in the public interfaces use the previously constructed completed
Lebesgue measure. Smoothness means real smoothness, also for complex outputs. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace Specs.D11.Ch11.SmoothMollifier
open _root_.D11.Ch03 Specs.D11.Ch03.LebesgueMeasures

def rawBump_type := (d : ℕ) → [NeZero d] → Point d → ℝ

def rawBump_value : rawBump_type := fun _ _ x =>
  if ‖x‖ < 1 then Real.exp (-1 / (1 - ‖x‖ ^ 2)) else 0

def mollifier_type := rawBump_type

def mollifier_value : mollifier_type := fun d _ x =>
  (∫ y, rawBump_value d y ∂lebesgue_value d)⁻¹ * rawBump_value d x

def scaledMollifier_type := (d : ℕ) → [NeZero d] → ℝ → Point d → ℝ

def scaledMollifier_value : scaledMollifier_type := fun d _ t x =>
  (t ^ d)⁻¹ * mollifier_value d (t⁻¹ • x)

/-- Smoothness includes the unit sphere. The integral is an absolutely
convergent, strictly positive real number before normalization. -/
def rawBump_properties : Prop := ∀ (d : ℕ) [NeZero d],
  ContDiff ℝ ∞ (rawBump_value d) ∧
  (∀ x, 0 ≤ rawBump_value d x) ∧
  tsupport (rawBump_value d) ⊆ Metric.closedBall 0 1 ∧
  HasCompactSupport (rawBump_value d) ∧
  (letI := lebesgueSpace_value d; Integrable (rawBump_value d) (lebesgue_value d)) ∧
  0 < ∫ x, rawBump_value d x ∂lebesgue_value d

def mollifier_properties : Prop := ∀ (d : ℕ) [NeZero d],
  ContDiff ℝ ∞ (mollifier_value d) ∧
  (∀ x, 0 ≤ mollifier_value d x) ∧
  tsupport (mollifier_value d) ⊆ Metric.closedBall 0 1 ∧
  HasCompactSupport (mollifier_value d) ∧
  (letI := lebesgueSpace_value d; Integrable (mollifier_value d) (lebesgue_value d)) ∧
  (∫ x, mollifier_value d x ∂lebesgue_value d) = 1

def scaledMollifier_properties : Prop := ∀ (d : ℕ) [NeZero d] (t : ℝ), 0 < t →
  ContDiff ℝ ∞ (scaledMollifier_value d t) ∧
  (∀ x, 0 ≤ scaledMollifier_value d t x) ∧
  tsupport (scaledMollifier_value d t) ⊆ Metric.closedBall 0 t ∧
  HasCompactSupport (scaledMollifier_value d t)

/-- The kernel is embedded in either scalar field via the canonical real map.
The derivative formula is an equality of continuous linear maps, with a
separate absolute integrability assertion for its integral. -/
def regularization : Prop := ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
  (g : Point d → 𝕜), Continuous g → HasCompactSupport g →
  ∀ (t : ℝ), 0 < t →
  let k : Point d → 𝕜 := fun x => (scaledMollifier_value d t x : 𝕜)
  let c := Specs.D11.Ch11.ConvolutionBound.convolution_value d g k
  ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
  (∀ x, letI := lebesgueSpace_value d;
    Integrable (fun y => g y * k (x-y)) (lebesgue_value d)) ∧
  (∀ x, letI := lebesgueSpace_value d;
    Integrable (fun y => (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
      (fderiv ℝ k (x-y))) (lebesgue_value d)) ∧
  (∀ x, HasFDerivAt c
    (∫ y, (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
      (fderiv ℝ k (x-y)) ∂lebesgue_value d) x)

/-- Repeated real directional derivatives; lists of coordinate basis vectors
include every mixed partial derivative, in every order. -/
def iterDirectional {d : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    List (Point d) → (Point d → 𝕜) → Point d → 𝕜
  | [], f => f
  | v :: vs, f => fun x => fderiv ℝ (iterDirectional vs f) x v

def regularization_all_derivatives : Prop := ∀ (d : ℕ) [NeZero d]
  (𝕜 : Type) [RCLike 𝕜] (g : Point d → 𝕜), Continuous g → HasCompactSupport g →
  ∀ (t : ℝ), 0 < t →
  let k : Point d → 𝕜 := fun x => (scaledMollifier_value d t x : 𝕜)
  ∀ vs : List (Point d),
    iterDirectional vs (Specs.D11.Ch11.ConvolutionBound.convolution_value d g k) =
      Specs.D11.Ch11.ConvolutionBound.convolution_value d g (iterDirectional vs k) ∧
    (∀ x, letI := lebesgueSpace_value d;
      Integrable (fun y => g y * iterDirectional vs k (x-y)) (lebesgue_value d))

end Specs.D11.Ch11.SmoothMollifier
