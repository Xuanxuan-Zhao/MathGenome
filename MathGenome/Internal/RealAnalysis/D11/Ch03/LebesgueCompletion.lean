import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelBoxApproximation
import MathGenome.Internal.RealAnalysis.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueCompletion

/-!
The Borel envelopes give a literal Borel sandwich with null difference.
This proves that every Carathéodory Lebesgue set belongs to the Borel
completion. The converse and agreement of values follow from the
minimality theorem for completion, applied to the complete Lebesgue measure.
-/

noncomputable section

open Set MeasureTheory

namespace D11.Ch03.LebesgueCompletion

open LebesgueMeasures

private theorem borel_agreement (d : ℕ) [NeZero d] (E : Set (Point d))
    (hE : MeasurableSet E) : lebesgue d E = borelMeasure d E := by
  have hEB : MeasurableSet[borel (Point d)] E := (borel_structure d).le E hE
  exact (lebesgue_apply d E (borel_le_lebesgue d E hEB)).trans
    (borel_apply d E hEB).symm

private theorem completion_minimality (d : ℕ) [NeZero d] :
    D11.Ch02.Completion.completedSpace (borelMeasure d) ≤ lebesgueSpace d ∧
      ∀ E : Set (Point d),
        MeasurableSet[D11.Ch02.Completion.completedSpace (borelMeasure d)] E →
          lebesgue d E = D11.Ch02.Completion.completedMeasure (borelMeasure d) E :=
  D11.Ch02.Completion.minimality (borelMeasure d) (lebesgueSpace d) (lebesgue d)
    (native_borel_le d) (lebesgue_complete d) (borel_agreement d)

/-- No finite-volume premise is needed for the null Borel sandwich. -/
theorem borel_sandwich (d : ℕ) [NeZero d] (E : Set (Point d))
    (hE : MeasurableSet[lebesgueSpace d] E) :
    D11.Ch02.Completion.Sandwiched (borelMeasure d) E := by
  obtain ⟨F, G, _hFs, _hGd, hF, hG, hFE, hEG, hEF, hGE⟩ :=
    (BorelBoxApproximation.borel_box_approximation d E hE).1
  have hGF : lebesgue d (G \ F) = 0 := by
    apply measure_mono_null (t := (G \ E) ∪ (E \ F))
    · intro x hx
      by_cases hxE : x ∈ E
      · exact Or.inr ⟨hxE, hx.2⟩
      · exact Or.inl ⟨hx.1, hxE⟩
    · exact measure_union_null hGE hEF
  have hFn : MeasurableSet F := (borel_structure d).ge F hF
  have hGn : MeasurableSet G := (borel_structure d).ge G hG
  refine ⟨F, G, hFn, hGn, hFE, hEG, ?_⟩
  exact (borel_agreement d (G \ F) (hGn.diff hFn)).symm.trans hGF

theorem completion_space : Specs.D11.Ch03.LebesgueCompletion.completion_space := by
  intro d _
  apply le_antisymm
  · intro E hE
    exact (D11.Ch02.Completion.completed_measurable_iff (borelMeasure d) E).mpr
      (borel_sandwich d E hE)
  · exact (completion_minimality d).1

theorem completion_value : Specs.D11.Ch03.LebesgueCompletion.completion_value := by
  intro d _ E hE
  apply (completion_minimality d).2 E
  exact (D11.Ch02.Completion.completed_measurable_iff (borelMeasure d) E).mpr
    (borel_sandwich d E hE)

theorem lebesgue_completion : Specs.D11.Ch03.LebesgueCompletion.lebesgue_completion := by
  intro d _
  exact ⟨completion_space d, completion_value d⟩

theorem borel_mod_null_iff : Specs.D11.Ch03.LebesgueCompletion.borel_mod_null_iff := by
  intro d _ E
  constructor
  · intro hE
    obtain ⟨F, G, hF, hG, hFE, hEG, hGF⟩ := borel_sandwich d E hE
    refine ⟨F, G \ F, E \ F, (borel_structure d).le F hF,
      (borel_structure d).le (G \ F) (hG.diff hF), hGF,
      sdiff_subset_sdiff_left hEG, ?_⟩
    exact (union_sdiff_cancel hFE).symm
  · rintro ⟨B, N, Z, hB, hN, hnull, hZN, rfl⟩
    have hNm := borel_le_lebesgue d N hN
    have hNzero : lebesgue d N = 0 := by
      have hNnative : MeasurableSet N := (borel_structure d).ge N hN
      exact (borel_agreement d N hNnative).trans hnull
    exact (borel_le_lebesgue d B hB).union (null_subset d N Z hNm hNzero hZN).1

end D11.Ch03.LebesgueCompletion
