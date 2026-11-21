import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Independent specifications for the value formula of paper.tex:875–905.
The contour is an actual canonical path, traversed counterclockwise on [0,2π].
Holomorphy is the shared weak differentiability predicate. -/

noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch04.DiskCauchyFormula
open _root_.D12Complex

def circlePath_type := ℂ → ℝ → PiecewiseC1Path

def circlePath_value : circlePath_type := fun a r =>
  let γ : ComplexPath := ⟨0, 2 * Real.pi, Real.two_pi_pos.le,
    circleMap a r, (continuous_circleMap a r).continuousOn⟩
  ⟨γ, ⟨C1Partition.single γ (contDiff_circleMap a r).contDiffOn⟩⟩

def circlePath_apply_type : Prop :=
  ∀ (a : ℂ) (r t : ℝ),
    circlePath_value a r t = a + (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

def circlePath_trace_type : Prop :=
  ∀ (a : ℂ) (r : ℝ), 0 ≤ r → (circlePath_value a r).trace = sphere a r

def circlePath_closed_type : Prop :=
  ∀ (a : ℂ) (r : ℝ), (circlePath_value a r).IsClosed

def integral_eq_circleIntegral_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (g : ℂ → ℂ), 0 ≤ r → ContinuousOn g (sphere a r) →
    (circlePath_value a r).integral g = circleIntegral g a r

def circle_integral_sub_inv_type : Prop :=
  ∀ (a z : ℂ) (r : ℝ), 0 < r → ‖z - a‖ < r →
    (circlePath_value a r).integral (fun w => (w - z)⁻¹) =
      (2 * Real.pi * Complex.I : ℂ)

/-- A stronger form allowing only continuity at the boundary. -/
def cauchy_formula_of_continuous_differentiable_type : Prop :=
  ∀ (a z : ℂ) (r : ℝ) (f : ℂ → ℂ), 0 < r → ‖z - a‖ < r →
    ContinuousOn f (closedBall a r) →
    (∀ w ∈ ball a r, DifferentiableAt ℂ f w) →
    f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (circlePath_value a r).integral (fun w => f w / (w - z))

/-- The paper's original open-neighborhood hypothesis, with no assumption on f'. -/
def disk_cauchy_formula_type : Prop :=
  ∀ (a z : ℂ) (r : ℝ) (U : Set ℂ) (f : ℂ → ℂ),
    0 < r → HolomorphicOn U f → closedBall a r ⊆ U → ‖z - a‖ < r →
    f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (circlePath_value a r).integral (fun w => f w / (w - z))

end Specs.D12Complex.Ch04.DiskCauchyFormula
