import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! The complete conclusion of paper.tex, Theorem d13:19:birkhoff.
All conclusions use the same integrable, finite-valued representative.
The invariant-set identity includes invariance modulo null sets. -/
namespace Specs.D13Unified.Ch19.Birkhoff
noncomputable section
open MeasureTheory Filter
open scoped Topology
universe u

def birkhoffStatement (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ], MeasureDefinitions.PreservesMeasure T μ →
    ∀ f : X → 𝕜, Integrable f μ → ∃ g : X → 𝕜, Integrable g μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 (g x))) ∧
      Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - g x‖ ∂μ)
        atTop (𝓝 0) ∧
      (g ∘ T =ᵐ[μ] g) ∧
      (∀ E : Set X, MeasurableSet E → MeasureDefinitions.InvariantModNull T μ E →
        (∫ x in E, g x ∂μ) = ∫ x in E, f x ∂μ) ∧
      ((∫ x, g x ∂μ) = ∫ x, f x ∂μ) ∧
      (MeasureDefinitions.IsErgodic T μ → g =ᵐ[μ] fun _ => ∫ x, f x ∂μ)

def real_birkhoffStatement : Prop := birkhoffStatement.{u} ℝ

def complex_birkhoffStatement : Prop := birkhoffStatement.{u} ℂ

end
end Specs.D13Unified.Ch19.Birkhoff
