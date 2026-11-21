import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.GDelta.Basic

noncomputable section
open Set MeasureTheory

namespace Specs.D11.Ch09.CompositionMeasurabilityFailure

/-- The density and primitive prescribed in paper.tex:3254–3257. -/
def density (K : Set ℝ) : ℝ → ℝ := (Icc 0 1 \ K).indicator (fun _ => 1)
def primitive (K : Set ℝ) (x : ℝ) : ℝ := ∫ t in 0..x, density K t

abbrev unitLebesgueSpace : MeasurableSpace (Icc (0 : ℝ) 1) :=
  MeasurableSpace.comap Subtype.val (Ch02.Completion.completedSpace_value (volume : Measure ℝ))

/-- Full interval example, including its prescribed integral, compact null
image, nonmeasurable subset, exact inverse image, and scalar composition.
`NullMeasurableSet` is measurability in completed real Lebesgue measure.
The function on the domain uses the trace of that completion. -/
def counterexample : Prop :=
  ∃ K A : Set ℝ,
    K ⊆ Icc 0 1 ∧ IsClosed K ∧ IsNowhereDense K ∧ 0 < volume K ∧
    A ⊆ K ∧ ¬ NullMeasurableSet A (volume : Measure ℝ) ∧
    let F := primitive K
    let E := F '' A
    Ch12.absolutelyContinuousOnIntervalValue F 0 1 ∧
    Continuous F ∧ StrictMonoOn F (Icc 0 1) ∧
    IsCompact (F '' K) ∧ volume (F '' K) = 0 ∧
    E ⊆ F '' K ∧ NullMeasurableSet E (volume : Measure ℝ) ∧ volume E = 0 ∧
    Icc 0 1 ∩ F ⁻¹' E = A ∧
    ¬ NullMeasurableSet (Icc 0 1 ∩ F ⁻¹' E) (volume : Measure ℝ) ∧
    @Measurable ℝ ℝ (Ch02.Completion.completedSpace_value (volume : Measure ℝ))
      inferInstance (E.indicator (fun _ => (1 : ℝ))) ∧
    ¬ @Measurable (Icc (0 : ℝ) 1) ℝ unitLebesgueSpace inferInstance
      (fun x => E.indicator (fun _ => (1 : ℝ)) (F x))

end Specs.D11.Ch09.CompositionMeasurabilityFailure
