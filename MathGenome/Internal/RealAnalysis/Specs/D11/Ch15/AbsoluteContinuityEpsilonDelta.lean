import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity

/-! Independent statements of the small-set characterization, paper.tex:4815–4820.
The thresholds ε and δ are positive real numbers; comparisons of positive
measure values use their canonical embeddings in [0,∞]. Every test set is
measurable in the single original sigma-algebra. There are no hypotheses on
reference mass, sigma-finiteness, completeness, atoms or nonemptiness.
The upstream variation is the supremum over measurable finite partitions.
-/

open Set MeasureTheory

universe u

namespace Specs.D11.Ch15.AbsoluteContinuityEpsilonDelta

open Specs.D11.Ch14.TotalVariation Specs.D11.Ch15.AbsoluteContinuity

def signed_variation_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation_value ν E < ENNReal.ofReal ε

def signed_value_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          ‖ν E‖ < ε

def complex_variation_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation_value ν E < ENNReal.ofReal ε

def complex_value_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) (μ : Measure α),
    scalarAbsolutelyContinuous_value ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          ‖ν E‖ < ε

end Specs.D11.Ch15.AbsoluteContinuityEpsilonDelta
