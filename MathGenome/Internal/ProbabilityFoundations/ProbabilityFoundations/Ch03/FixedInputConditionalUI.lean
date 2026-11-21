import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.FixedInputConditionalUI
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.UniformIntegrabilitySmallSets
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch03.ConditionalLpContraction

/-! Conditional expectations of a fixed integrable real input are uniformly
integrable over the entire set of sub-sigma-algebras (Proposition 3.9).
Mathlib's conditional expectation theorem allows an arbitrary index type.
We use the family itself as the index type and then apply the chapter-1
bridge to the source's strict-tail definition. No completeness is required. -/

open MeasureTheory

universe u

namespace ProbabilityFoundations.Ch03

/-- Uniform integrability simultaneously for every sub-sigma-algebra and
every a.e. representative of its conditional expectation. In particular,
no common exceptional set across the family is required. -/
theorem fixed_input_conditional_ui_all_representatives
    {Ω : Type u} [F : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    Ch01.SourceUniformIntegrable P
      {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
        U =ᵐ[P] realConditionalExpectation (F := F) G P X} := by
  classical
  let H : Set (Ω → ℝ) :=
    {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
      U =ᵐ[P] realConditionalExpectation (F := F) G P X}
  let σ : H → MeasurableSpace Ω := fun U => Classical.choose U.property
  have hσ : ∀ U : H, σ U ≤ F :=
    fun U => (Classical.choose_spec U.property).1
  have heq : ∀ U : H, condExp (σ U) P X =ᵐ[P] (U : Ω → ℝ) :=
    fun U => (Classical.choose_spec U.property).2.symm
  apply (Ch01.sourceUniformIntegrable_iff_uniformIntegrable P H).mpr
  exact (hX.uniformIntegrable_condExp hσ).ae_eq heq

/-- The source's full family, with one canonical conditional expectation
for every sub-sigma-algebra of the specified ambient sigma-algebra. -/
theorem fixed_input_conditional_ui
    {Ω : Type u} [F : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    Ch01.SourceUniformIntegrable P
      {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
        U = realConditionalExpectation (F := F) G P X} := by
  classical
  let H : Set (Ω → ℝ) :=
    {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
      U = realConditionalExpectation (F := F) G P X}
  let σ : H → MeasurableSpace Ω := fun U => Classical.choose U.property
  have hσ : ∀ U : H, σ U ≤ F :=
    fun U => (Classical.choose_spec U.property).1
  have heq : ∀ U : H, condExp (σ U) P X =ᵐ[P] (U : Ω → ℝ) :=
    fun U => Filter.EventuallyEq.of_eq (Classical.choose_spec U.property).2.symm
  apply (Ch01.sourceUniformIntegrable_iff_uniformIntegrable P H).mpr
  exact (hX.uniformIntegrable_condExp hσ).ae_eq heq

end ProbabilityFoundations.Ch03
