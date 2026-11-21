import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces

/-! Independent statements for paper.tex W34, the converse and its extension
to all sub-sigma-algebras. The UI predicate is the shared norm-tail predicate.
No monotonicity, countability, or nonemptiness is imposed on indexed families
of sub-sigma-algebras. The finite-measure versions include probability spaces. -/

open MeasureTheory
open scoped MeasureTheory

universe u v

namespace Specs.P207.Martingale.FixedInputConditionalUI

def sourceUniformIntegrable_condExpType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ), Integrable Y μ →
    ∀ (ℋ : I → MeasurableSpace Ω), (∀ i, ℋ i ≤ m) →
      UniformIntegrability.SourceUniformIntegrableValue μ (fun i => μ[Y | ℋ i])

def sourceUniformIntegrable_all_condExpType : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ), Integrable Y μ →
      UniformIntegrability.SourceUniformIntegrableValue μ
        (fun ℋ : {ℋ : MeasurableSpace Ω // ℋ ≤ m} => μ[Y | ℋ.val])

/-- Each representative can have its own exceptional null set. -/
def sourceUniformIntegrable_condExp_of_ae_eqType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → ℝ), Integrable Y μ →
    ∀ (ℋ : I → MeasurableSpace Ω), (∀ i, ℋ i ≤ m) →
    ∀ (X : I → Ω → ℝ), (∀ i, X i =ᵐ[μ] μ[Y | ℋ i]) →
      UniformIntegrability.SourceUniformIntegrableValue μ X

def conditional_expectation_ui_martingaleType : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (Y : Ω → ℝ), Integrable Y μ →
      P207.IsMartingale (fun n => μ[Y | ℱ n]) ℱ μ ∧
      UniformIntegrability.SourceUniformIntegrableValue μ (fun n => μ[Y | ℱ n])

end Specs.P207.Martingale.FixedInputConditionalUI
