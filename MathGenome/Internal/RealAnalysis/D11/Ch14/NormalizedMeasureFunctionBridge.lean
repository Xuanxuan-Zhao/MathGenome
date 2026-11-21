import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.NormalizedMeasureFunctionBridge
import MathGenome.Internal.RealAnalysis.D11.Ch12.NormalizedStieltjes

/-! Chapter 14's normalized measure/function bridge, paper.tex:4749–4765.
No new normalization is introduced. The Chapter 12 construction supplies the
converse, and the partition total variation supplies scalar finiteness.
This module is downstream of both; Chapter 12 never imports this bridge.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D11.Ch14.NormalizedMeasureFunctionBridge
open D11.Ch12
open D11.Ch12.ScalarStieltjesCorrespondence
open D11.Ch14.TotalVariation

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- The positive Stieltjes generator of total variation is exactly the
classical initial variation of the normalized cumulative function. -/
lemma variation_measure_recovery (ν : VectorMeasure ℝ E)
    (hν : IsFiniteMeasure ν.variation) :
    ∃ h : PositiveStieltjes.PositiveGenerator
        (fun x => (initialVariation (cumulative ν) x).toReal),
      PositiveStieltjes.stieltjesMeasure
        (fun x => (initialVariation (cumulative ν) x).toReal) h = totalVariation ν := by
  have heq : (fun x => (initialVariation (cumulative ν) x).toReal) =
      PositiveStieltjes.cumulative ν.variation := by
    funext x
    exact congrArg ENNReal.toReal ((NormalizedStieltjes.cumulative_variation ν hν).2 x).symm
  rw [heq]
  exact ⟨PositiveStieltjes.cumulative_properties ν.variation hν,
    PositiveStieltjes.stieltjesMeasure_cumulative ν.variation hν _⟩

/-- Generic finite-variation statement; the scalar specializations below
obtain this hypothesis from automatic finite scalar variation. -/
lemma distribution_properties (ν : VectorMeasure ℝ E)
    (hν : IsFiniteMeasure ν.variation) :
    Specs.D11.Ch14.NormalizedMeasureFunctionBridge.DistributionProperties ν := by
  have hF := cumulative_properties ν hν
  have hback := measure_cumulative ν hν
  have hv := NormalizedStieltjes.cumulative_variation ν hν
  refine ⟨hF, ?_, hback, hv.1, hv.2, ?_, variation_measure_recovery ν hν⟩
  · intro a b hab
    exact (cumulative_sub ν hab.le).symm
  · have hglobal := NormalizedStieltjes.variation_global (cumulative ν) hF
    rw [hback] at hglobal
    exact hglobal

/-- Real-valued countable additivity is sufficient; finite variation is a conclusion. -/
theorem signed_distribution :
    Specs.D11.Ch14.NormalizedMeasureFunctionBridge.signed_distribution := by
  intro ν
  exact distribution_properties ν (signed_finite ν)

/-- Complex-valued countable additivity is sufficient as well. -/
theorem complex_distribution :
    Specs.D11.Ch14.NormalizedMeasureFunctionBridge.complex_distribution := by
  intro ν
  exact distribution_properties ν (complex_finite ν)

/-- The existing Chapter 12 measure represents every normalized BV function,
and interval uniqueness gives uniqueness among all scalar-valued measures. -/
lemma representation_exists_unique (F : ℝ → E) (hF : NBV F) :
    ∃! ν : VectorMeasure ℝ E,
      Specs.D11.Ch14.NormalizedMeasureFunctionBridge.RepresentationProperties F ν := by
  refine ⟨stieltjesMeasure F, ?_, ?_⟩
  · exact ⟨cumulative_measure F hF, measure_interval F hF,
      NormalizedStieltjes.variation_initial F hF,
      NormalizedStieltjes.variation_global F hF⟩
  · intro ν hν
    exact measure_unique F hF ν hν.2.1

theorem signed_converse :
    Specs.D11.Ch14.NormalizedMeasureFunctionBridge.signed_converse := by
  intro F hF
  exact representation_exists_unique F hF

theorem complex_converse :
    Specs.D11.Ch14.NormalizedMeasureFunctionBridge.complex_converse := by
  intro F hF
  exact representation_exists_unique F hF

end D11.Ch14.NormalizedMeasureFunctionBridge
