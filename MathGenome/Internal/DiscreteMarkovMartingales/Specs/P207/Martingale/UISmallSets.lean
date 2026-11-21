import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability

/-! Independent specification of paper.tex §6.2, W31, conditions (1) and (2).
The finite-measure statement includes every probability space. No nonempty
index or separability assumption is imposed. Integrability is explicit, so
all real expectations below are expectations of integrable functions. -/

open MeasureTheory
open scoped NNReal ENNReal

universe u v w

namespace Specs.P207.Martingale.UISmallSets

def sourceUniformIntegrable_iff_smallSetsType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E),
    (∀ i, Integrable (X i) μ) →
    (UniformIntegrability.SourceUniformIntegrableValue μ X ↔
      (∃ C : ℝ≥0, ∀ i, (∫ x, ‖X i x‖ ∂μ) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (i : I) (A : Set Ω), MeasurableSet A → μ A < ENNReal.ofReal δ →
          (∫ x, A.indicator (fun x => ‖X i x‖) x ∂μ) < ε)

end Specs.P207.Martingale.UISmallSets
