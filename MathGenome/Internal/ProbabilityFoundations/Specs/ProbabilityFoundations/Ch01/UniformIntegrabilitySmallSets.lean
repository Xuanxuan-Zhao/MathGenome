import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Independent statements for conditions (1) and (2) of paper.tex,
Theorem 1.10. Suprema take values in ℝ≥0∞ so that empty and unbounded
families have the intended values. No completeness of the measure space
is assumed. Normed additive groups include both ℝ and ℂ. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace Specs.ProbabilityFoundations.Ch01.UniformIntegrabilitySmallSets
open UniformIntegrabilityInterfaces

/-- The strict-tail definition agrees with Mathlib at exponent one. -/
def sourceUniformIntegrable_iff_uniformIntegrableType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) [IsFiniteMeasure μ] (H : Set (S → E)),
    SourceUniformIntegrableValue μ H ↔
      UniformIntegrable (fun f : H => (f : S → E)) 1 μ

/-- Bounded L¹ norms and uniform absolute continuity on measurable sets
are equivalent to the source tail definition for families in L¹. -/
def sourceUniformIntegrable_iff_bounded_small_setsType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) [IsFiniteMeasure μ] (H : Set (S → E))
    (hH : ∀ f ∈ H, Integrable f μ),
    SourceUniformIntegrableValue μ H ↔
      (∃ C : ℝ, ∀ f ∈ H, l1NormValue μ f ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ A : Set S, MeasurableSet A → μ A < ENNReal.ofReal δ →
          (⨆ f ∈ H, ∫⁻ x in A, ‖f x‖ₑ ∂μ) < ENNReal.ofReal ε)

end Specs.ProbabilityFoundations.Ch01.UniformIntegrabilitySmallSets
