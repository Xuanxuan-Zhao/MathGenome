import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Convergence stages of paper.tex, Theorem d13:19:birkhoff.
The limit is an actual finite-valued integrable representative. Strong L¹
convergence is expressed by the integral of the norm of the difference.
Invariance and the invariant-set integral identity are separate obligations. -/
namespace Specs.D13Unified.Ch19.BirkhoffConvergence
noncomputable section
open MeasureTheory Filter
open scoped Topology
universe u

def real_convergenceStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℝ, Integrable f μ → ∃ g : X → ℝ, Integrable g μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - g x‖ ∂μ)
        atTop (𝓝 0)

def complex_convergenceStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → ℂ, Integrable f μ → ∃ g : X → ℂ, Integrable g μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - g x‖ ∂μ)
        atTop (𝓝 0)

end
end Specs.D13Unified.Ch19.BirkhoffConvergence
