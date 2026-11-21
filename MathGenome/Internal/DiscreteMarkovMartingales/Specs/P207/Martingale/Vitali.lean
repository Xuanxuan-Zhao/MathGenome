import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UISmallSets
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Independent specification of paper.tex §6.3, W32.
The finite-measure formulation includes probability spaces. The codomain may
be any Banach space, with no global separability or measurable-space instance.
No measurability or integrability of the probability limit is assumed. -/

open MeasureTheory Filter
open scoped Topology

universe u v

namespace Specs.P207.Martingale.Vitali

def vitali_forwardType : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → E) (Y : Ω → E),
    (∀ n, Integrable (X n) μ) →
    TendstoInMeasure μ X atTop Y →
    UniformIntegrability.SourceUniformIntegrableValue μ X →
    Integrable Y μ ∧
      (∃ Z : Ω → E, StronglyMeasurable Z ∧ Integrable Z μ ∧ Y =ᵐ[μ] Z) ∧
      Tendsto (fun n => ∫ x, ‖X n x - Y x‖ ∂μ) atTop (𝓝 0)

def vitali_converseType : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → E) (Y : Ω → E),
    (∀ n, Integrable (X n) μ) → Integrable Y μ →
    Tendsto (fun n => ∫ x, ‖X n x - Y x‖ ∂μ) atTop (𝓝 0) →
    TendstoInMeasure μ X atTop Y ∧
      UniformIntegrability.SourceUniformIntegrableValue μ X

end Specs.P207.Martingale.Vitali
