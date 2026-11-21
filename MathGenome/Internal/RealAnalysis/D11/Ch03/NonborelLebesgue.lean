import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.NonborelLebesgue
import MathGenome.Internal.RealAnalysis.D11.Ch03.CantorSet

noncomputable section
open Set MeasureTheory
open scoped Cardinal

namespace D11.Ch03.NonborelLebesgue
open CantorConstruction

/-- A countable topological basis generates at most continuum many Borel sets.
The cardinal estimate for a generated sigma-algebra uses Mathlib's transfinite
construction, without any separation or completeness assumption on the space. -/
theorem borel_cardinality_le : Specs.D11.Ch03.NonborelLebesgue.borel_cardinality_le := by
  intro X _ _
  obtain ⟨b, hb, _, hbase⟩ := TopologicalSpace.exists_countable_basis X
  rw [hbase.borel_eq_generateFrom]
  apply MeasurableSpace.cardinal_measurableSet_le_continuum
  exact (Cardinal.le_aleph0_iff_set_countable.mpr hb).trans Cardinal.aleph0_le_continuum

/-- Cantor's strict powerset inequality rules out Borel measurability of all
subsets of a set of cardinality continuum. -/
theorem exists_nonborel_cantor_subset :
    Specs.D11.Ch03.NonborelLebesgue.exists_nonborel_cantor_subset := by
  classical
  change ∃ N : Set ℝ, N ⊆ CantorSet.C ∧ ¬ MeasurableSet[borel ℝ] N
  by_contra! h
  let f : (𝒫 CantorSet.C) → {s : Set ℝ | MeasurableSet[borel ℝ] s} :=
    fun s => ⟨s.1, h s.1 s.2⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun z : {s : Set ℝ | MeasurableSet[borel ℝ] s} => z.1) hst
  have hcard := (Cardinal.mk_le_of_injective hf).trans (borel_cardinality_le ℝ)
  have hC : Cardinal.mk ↥CantorSet.C = 𝔠 := CantorSet.C_cardinality
  rw [Cardinal.mk_powerset, hC] at hcard
  exact (not_le_of_gt (Cardinal.cantor 𝔠)) hcard

theorem lebesgue_not_borel : Specs.D11.Ch03.NonborelLebesgue.lebesgue_not_borel := by
  obtain ⟨N, hNC, hN⟩ := exists_nonborel_cantor_subset
  have hi : Function.Injective linePoint := by
    intro x y hxy
    exact congrArg (fun p : Point 1 => p 0) hxy
  have hc : Continuous linePoint :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp
      (continuous_pi fun _ => continuous_id)
  have hNB : ¬ MeasurableSet[borel (Point 1)] (linePoint '' N) := by
    intro hm
    rw [← BorelSpace.measurable_eq (α := Point 1)] at hm
    apply hN
    have hp := hm.preimage hc.measurable
    simpa only [preimage_image_eq _ hi] using hp
  obtain ⟨hCm, hC0⟩ := CantorSet.C_lebesgue_null
  obtain ⟨hNm, hN0⟩ := LebesgueMeasures.null_subset 1
    (linePoint '' CantorSet.C) (linePoint '' N) hCm hC0 (image_mono hNC)
  exact ⟨N, hNC, hN, hNB, hNm, hN0⟩

theorem borel_incomplete : Specs.D11.Ch03.NonborelLebesgue.borel_incomplete := by
  obtain ⟨N, hNC, _, hNB, _, _⟩ := lebesgue_not_borel
  intro hcomplete
  apply hNB
  have hnull : LebesgueMeasures.borelMeasure 1 (linePoint '' CantorSet.C) = 0 := by
    change volume (linePoint '' CantorSet.C) = 0
    rw [LebesgueMeasures.native_outer_agreement 1]
    obtain ⟨hCm, hC0⟩ := CantorSet.C_lebesgue_null
    exact (LebesgueMeasures.lebesgue_apply 1 _ hCm).symm.trans hC0
  have hN0 := measure_mono_null (image_mono hNC) hnull
  rw [← BorelSpace.measurable_eq (α := Point 1)]
  exact hcomplete.out _ hN0

end D11.Ch03.NonborelLebesgue
