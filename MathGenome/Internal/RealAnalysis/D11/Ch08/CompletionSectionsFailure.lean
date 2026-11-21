import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.CompletionSectionsFailure
import MathGenome.Internal.RealAnalysis.D11.Ch03.Vitali
import MathGenome.Internal.RealAnalysis.D11.Ch08.Sections
import MathGenome.Internal.RealAnalysis.D11.Ch02.Completion

open Set MeasureTheory
open D11.Ch03 D11.Ch03.Vitali
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch08.EuclideanProductCompletion

namespace D11.Ch08.CompletionSectionsFailure

/-- The coordinate interval is the shared closed endpoint box. -/
private theorem interval_eq_box :
    inOneSpace (Icc (0 : ℝ) 1) =
      endpointBox (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1)
        (fun _ => true) (fun _ => true) := by
  ext p
  simp [inOneSpace, endpointBox, Fin.forall_fin_one]

theorem complete_factors_null_rectangle :
    Specs.D11.Ch08.CompletionSectionsFailure.complete_factors_null_rectangle := by
  let : MeasurableSpace (Point 1) := lebesgueSpace_value 1
  let : SigmaFinite (lebesgue_value 1) := LebesgueMeasures.lebesgue_sigmaFinite 1
  have hzero := LebesgueMeasures.countable_measurable_null 1 ({0} : Set (Point 1))
    (Set.countable_singleton _)
  have hi : MeasurableSet[lebesgueSpace_value 1] (inOneSpace (Icc (0 : ℝ) 1)) := by
    rw [interval_eq_box]
    exact LebesgueMeasures.borel_le_lebesgue 1 _
      (LebesgueMeasures.endpointBox_borel 1 _ _ _ _)
  refine ⟨LebesgueMeasures.lebesgue_complete 1, hzero.1.prod hi, ?_⟩
  change (lebesgue_value 1).prod (lebesgue_value 1)
    (({0} : Set (Point 1)) ×ˢ inOneSpace (Icc (0 : ℝ) 1)) = 0
  rw [Measure.prod_prod, hzero.2, zero_mul]

theorem vertical_obstruction :
    Specs.D11.Ch08.CompletionSectionsFailure.vertical_obstruction := by
  intro V hV hnon
  have hsub : verticalSet V ⊆ nullRectangle := by
    intro p hp
    exact ⟨hp.1, hV hp.2⟩
  have hsection : {y : Point 1 | ((0 : Point 1), y) ∈ verticalSet V} = inOneSpace V := by
    ext y
    simp [verticalSet]
  have hreal : {y : ℝ | ((0 : Point 1), WithLp.toLp 2 (fun _ : Fin 1 => y)) ∈
      verticalSet V} = V := by
    ext y
    simp [verticalSet, inOneSpace]
  have hn : ¬ MeasurableSet[factorSpace 1 1] (verticalSet V) := by
    intro h
    apply hnon
    rw [← hsection]
    exact Sections.set_section_left (lebesgueSpace_value 1) (lebesgueSpace_value 1)
      (verticalSet V) h 0
  have hR := complete_factors_null_rectangle
  have hext := D11.Ch02.Completion.extends_original
    (m := factorSpace 1 1) (factorProduct 1 1)
  have hc := D11.Ch02.Completion.completed_subset_null
    (m := factorSpace 1 1) (factorProduct 1 1) (verticalSet V) nullRectangle hsub
    (hext.1 nullRectangle hR.2.1) ((hext.2 nullRectangle hR.2.1).trans hR.2.2)
  exact ⟨hsub, hc.1, hc.2, hsection, hreal, hn⟩

theorem completion_sections_failure :
    Specs.D11.Ch08.CompletionSectionsFailure.completion_sections_failure := by
  obtain ⟨V, hV⟩ := Vitali.selector_exists
  have hn := Vitali.selector_nonmeasurable V hV
  obtain ⟨hsub, hc, _hnull, hsection, _hreal, hnot⟩ := vertical_obstruction V hV.1 hn
  refine ⟨⟨V, hV.1, hn, hc, hnot, ?_⟩, ?_⟩
  · rwa [hsection]
  · intro hcomplete
    have hz : factorProduct 1 1 (verticalSet V) = 0 :=
      measure_mono_null hsub complete_factors_null_rectangle.2.2
    exact hnot (hcomplete.out (verticalSet V) hz)

end D11.Ch08.CompletionSectionsFailure
