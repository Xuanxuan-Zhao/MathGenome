import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces

/-! Independent statement of paper.tex, Theorem 1.11 (lines 378–410).
The norm formulation includes real absolute value and complex modulus. Sequences
are indexed starting at zero. L¹ convergence includes integrability of the limit;
there is no such hypothesis on the other side of the equivalence, and the
specified measure space need not be complete. -/

open MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace Specs.ProbabilityFoundations.Ch01.VitaliFiniteMeasure
open UniformIntegrabilityInterfaces

/-- Vitali's criterion on any finite measure space, including the zero measure. -/
def vitaliFiniteMeasureType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure S) [IsFiniteMeasure μ] (F : ℕ → S → E) (f : S → E),
    (∀ n, Integrable (F n) μ) → Measurable f →
    ((Integrable f μ ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0)) ↔
    (ConvergesInMeasureValue μ F f ∧ SourceUniformIntegrableValue μ (Set.range F)))

end Specs.ProbabilityFoundations.Ch01.VitaliFiniteMeasure
