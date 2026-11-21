import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.D11.Ch01.ElementaryMeasuresLimits
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.EuclideanDiscreteHaarExamples

/-!
# Euclidean and discrete two-sided Haar measures

These are the first two examples of paper.tex:5992–5997. We use the shared
Borel Lebesgue measure and native counting measure. The additive Euclidean
statement spells out the two translation conditions of the shared Haar
predicates. On discrete spaces all sets are open and Borel. The proof of
inner regularity treats infinite sets using finite subsets of arbitrarily
large cardinality, with no countability assumption on the ambient space.
-/

noncomputable section

namespace D11.Ch21.EuclideanDiscreteHaarExamples

open Set MeasureTheory MeasurableSpace
open scoped ENNReal
universe u

/-- Restricting an already Borel measure to the explicit Borel structure
preserves all outer evaluations; this only changes the type representation. -/
theorem borelTrim_apply {X : Type*} [TopologicalSpace X] [m : MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) (E : Set X) : μ.trim OpensMeasurableSpace.borel_le E = μ E := by
  borelize X
  rw [trim_eq_self]

theorem borelTrim_regular {X : Type*} [TopologicalSpace X] [m : MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [Measure.Regular μ] :
    @Measure.Regular X (borel X) _ (μ.trim OpensMeasurableSpace.borel_le) := by
  borelize X
  simpa only [trim_eq_self] using (inferInstance : Measure.Regular μ)

theorem euclidean_twoSidedHaar :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.euclidean_twoSidedHaar := by
  intro d _
  let μ := D11.Ch03.LebesgueMeasures.borelMeasure d
  change μ.trim OpensMeasurableSpace.borel_le ≠ 0 ∧ D11.Ch18.isRadon (μ.trim OpensMeasurableSpace.borel_le) ∧ _
  haveI : Measure.Regular μ := by
    change Measure.Regular (volume : Measure (D11.Ch03.Point d))
    infer_instance
  refine ⟨?_, (D11.Ch18.isRadon_iff_regular _).mpr (borelTrim_regular μ), ?_, ?_⟩
  · intro hz
    have hzero : μ = 0 := by
      ext E _
      rw [← borelTrim_apply μ E, hz]
      rfl
    exact (NeZero.ne (volume : Measure (D11.Ch03.Point d))) hzero
  · intro a E _
    simp only [borelTrim_apply]
    change volume ((fun x => a + x) '' E) = volume E
    have h := D11.Ch03.TranslationDilation.volume_affine d a 1 E
    simpa only [one_smul, abs_one, one_pow, ENNReal.ofReal_one, one_mul] using h
  · intro a E _
    simp only [borelTrim_apply]
    change volume ((fun x => x + a) '' E) = volume E
    have h := D11.Ch03.TranslationDilation.volume_affine d a 1 E
    simpa only [one_smul, abs_one, one_pow, ENNReal.ofReal_one, one_mul, add_comm] using h

theorem discrete_sets_open_borel :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.discrete_sets_open_borel.{u} := by
  intro X _ _ E
  borelize X
  exact ⟨isOpen_discrete E, (isOpen_discrete E).measurableSet⟩

theorem discrete_compact_iff_finite :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.discrete_compact_iff_finite.{u} := by
  intro X _ _ K
  exact isCompact_iff_finite

theorem count_outerRegular :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.count_outerRegular.{u} := by
  intro X _ _ E
  borelize X
  refine le_antisymm ?_ ?_
  · exact le_iInf fun U => le_iInf fun hEU => le_iInf fun _ => measure_mono hEU
  · exact iInf_le_of_le E (iInf_le_of_le Subset.rfl (iInf_le_of_le (isOpen_discrete E) le_rfl))

theorem count_compactInnerRegular :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.count_compactInnerRegular.{u} := by
  intro X _ _ E
  borelize X
  refine le_antisymm ?_ ?_
  · by_cases hE : E.Finite
    · exact le_iSup_of_le E (le_iSup_of_le Subset.rfl (le_iSup_of_le hE.isCompact le_rfl))
    · change E.Infinite at hE
      rw [Measure.count_apply_infinite hE]
      refine le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_
      obtain ⟨K, hKE, hcard⟩ := hE.exists_subset_card_eq n
      refine le_iSup_of_le (K : Set X) (le_iSup_of_le hKE (le_iSup_of_le K.finite_toSet.isCompact ?_))
      rw [Measure.count_apply_finset, hcard]
  · exact iSup_le fun K => iSup_le fun hKE => iSup_le fun _ => measure_mono hKE

theorem count_twoSidedHaar :
    Specs.D11.Ch21.EuclideanDiscreteHaarExamples.count_twoSidedHaar.{u} := by
  intro G _ _ _
  borelize G
  have hrad : D11.Ch18.isRadon (Measure.count : Measure G) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K hK
      exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete
    · intro E _
      exact count_outerRegular E
    · intro U _
      exact count_compactInnerRegular U
  have hleft : D11.Ch21.isLeftHaarMeasure (Measure.count : Measure G) := by
    refine ⟨Measure.count_ne_zero'', hrad, ?_⟩
    intro a E _
    exact Measure.count_injective_image (mul_right_injective a) E
  have hright : D11.Ch21.isRightHaarMeasure (Measure.count : Measure G) := by
    refine ⟨Measure.count_ne_zero'', hrad, ?_⟩
    intro a E _
    exact Measure.count_injective_image (mul_left_injective a) E
  exact ⟨hleft, hright⟩

end D11.Ch21.EuclideanDiscreteHaarExamples
