import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UniformIntegrability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.FixedInputConditionalUI
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! The converse of terminal closure (paper.tex W34). This proof uses only
integrability of the fixed input, the conditional-expectation UI theorem, and
the shared bridge to source norm tails; it uses no convergence theorem. -/

open MeasureTheory
open scoped MeasureTheory

universe u v

namespace P207.Martingale

variable {Ω : Type u} {I : Type v} [m : MeasurableSpace Ω]

/-- Conditional expectations of a fixed integrable input are UI for any indexed
family of sub-sigma-algebras, with no ordering or countability restriction. -/
theorem sourceUniformIntegrable_condExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : Integrable Y μ)
    (ℋ : I → MeasurableSpace Ω) (hℋ : ∀ i, ℋ i ≤ m) :
    SourceUniformIntegrable μ (fun i => μ[Y | ℋ i]) := by
  exact (sourceUniformIntegrable_iff_uniformIntegrable μ _).mpr
    (hY.uniformIntegrable_condExp hℋ)

/-- In particular the index can be the entire collection of sub-sigma-algebras. -/
theorem sourceUniformIntegrable_all_condExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : Integrable Y μ) :
    SourceUniformIntegrable μ
      (fun ℋ : {ℋ : MeasurableSpace Ω // ℋ ≤ m} => μ[Y | ℋ.val]) := by
  exact sourceUniformIntegrable_condExp μ Y hY Subtype.val Subtype.property

/-- The same assertion for arbitrary almost-everywhere representatives. -/
theorem sourceUniformIntegrable_condExp_of_ae_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : Integrable Y μ)
    (ℋ : I → MeasurableSpace Ω) (hℋ : ∀ i, ℋ i ≤ m)
    (X : I → Ω → ℝ) (hX : ∀ i, X i =ᵐ[μ] μ[Y | ℋ i]) :
    SourceUniformIntegrable μ X := by
  apply (sourceUniformIntegrable_iff_uniformIntegrable μ X).mpr
  exact (hY.uniformIntegrable_condExp hℋ).ae_eq (fun i => (hX i).symm)

/-- For any filtration the conditional-expectation process is a UI martingale,
including time zero, in the source's one-step convention. -/
theorem conditional_expectation_ui_martingale
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (Y : Ω → ℝ) (hY : Integrable Y μ) :
    P207.IsMartingale (fun n => μ[Y | ℱ n]) ℱ μ ∧
      SourceUniformIntegrable μ (fun n => μ[Y | ℱ n]) := by
  exact ⟨P207.conditional_expectation_process μ ℱ Y hY,
    sourceUniformIntegrable_condExp μ Y hY ℱ ℱ.le⟩

end P207.Martingale
