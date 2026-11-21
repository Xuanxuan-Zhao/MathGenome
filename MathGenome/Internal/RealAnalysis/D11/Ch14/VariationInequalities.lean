import MathGenome.Internal.RealAnalysis.D11.Ch14.TotalVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.VariationInequalities
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Tactic.NormNum

/-! Variation identities, the full real and complex norm axioms, and cancellation
on a two-point space. Variation is the upstream partition variation measure. -/

open Set MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace D11.Ch14.VariationInequalities

open D11.Ch14.TotalVariation

noncomputable def variationNorm {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) : ℝ :=
  (totalVariation ν univ).toReal

theorem variation_smul {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedField K] (c : K) (ν : VectorMeasure α K) :
    totalVariation (c • ν) = ENNReal.ofReal ‖c‖ • totalVariation ν := by
  rw [ofReal_norm, enorm_eq_nnnorm, Measure.coe_nnreal_smul]
  exact VectorMeasure.variation_smul

theorem variation_add {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν η : VectorMeasure α K)
    (E : Set α) (_hE : MeasurableSet E) :
    totalVariation (ν + η) E ≤ totalVariation ν E + totalVariation η E := by
  exact (VectorMeasure.variation_add_le (μ := ν) (ν := η) E).trans_eq
    (Measure.add_apply _ _ _)

theorem restriction_apply {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (A E : Set α) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    ν.restrict A E = ν (E ∩ A) :=
  VectorMeasure.restrict_apply ν hA hE

theorem variation_restrict {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (A E : Set α) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    totalVariation (ν.restrict A) E = totalVariation ν (E ∩ A) := by
  change (ν.restrict A).variation E = ν.variation (E ∩ A)
  rw [VectorMeasure.variation_restrict hA, Measure.restrict_apply hE]

theorem variationNorm_nonneg {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) :
    0 ≤ variationNorm ν := ENNReal.toReal_nonneg

theorem variationNorm_eq_zero_iff {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    [IsFiniteMeasure (totalVariation ν)] : variationNorm ν = 0 ↔ ν = 0 := by
  have hfin : totalVariation ν univ ≠ ⊤ := measure_ne_top _ _
  rw [variationNorm, ENNReal.toReal_eq_zero_iff, or_iff_left hfin,
    Measure.measure_univ_eq_zero]
  exact VectorMeasure.variation_eq_zero

theorem variationNorm_add_le {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν η : VectorMeasure α K)
    [IsFiniteMeasure (totalVariation ν)] [IsFiniteMeasure (totalVariation η)] :
    variationNorm (ν + η) ≤ variationNorm ν + variationNorm η := by
  unfold variationNorm
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨measure_ne_top _ _, measure_ne_top _ _⟩) (variation_add ν η univ .univ)

theorem variationNorm_smul {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedField K] (c : K) (ν : VectorMeasure α K) :
    variationNorm (c • ν) = ‖c‖ * variationNorm ν := by
  simp [variationNorm, variation_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul]

theorem signed_norm_axioms : Specs.D11.Ch14.VariationInequalities.signed_norm_axioms.{u} := by
  intro α _
  refine ⟨variationNorm_nonneg, ?_, ?_, variationNorm_smul⟩
  · intro ν
    haveI := signed_finite ν
    exact variationNorm_eq_zero_iff ν
  · intro ν η
    haveI := signed_finite ν
    haveI := signed_finite η
    exact variationNorm_add_le ν η

theorem complex_norm_axioms : Specs.D11.Ch14.VariationInequalities.complex_norm_axioms.{u} := by
  intro α _
  refine ⟨variationNorm_nonneg, ?_, ?_, variationNorm_smul⟩
  · intro ν
    haveI := complex_finite ν
    exact variationNorm_eq_zero_iff ν
  · intro ν η
    haveI := complex_finite ν
    haveI := complex_finite η
    exact variationNorm_add_le ν η

theorem cancellation_example : Specs.D11.Ch14.VariationInequalities.cancellation_example.{u} := by
  intro α a b hab hX
  letI : MeasurableSpace α := ⊤
  let ν : SignedMeasure α := VectorMeasure.dirac a 1 - VectorMeasure.dirac b 1
  have ha : ν {a} = 1 := by simp [ν, hab.symm]
  have hb : ν {b} = -1 := by simp [ν, hab]
  have hmass : totalVariation ν univ = 2 := by
    rw [hX]
    change ν.variation ({a} ∪ {b}) = 2
    rw [measure_union (Set.disjoint_singleton.mpr hab) MeasurableSet.of_discrete,
      VectorMeasure.variation_apply_singleton, VectorMeasure.variation_apply_singleton, ha, hb]
    norm_num
  change ν univ = 0 ∧ totalVariation ν univ = 2 ∧ ν {a} = 1 ∧
    ¬ (totalVariation ν univ = 0)
  exact ⟨by simp [ν], hmass, ha, by rw [hmass]; norm_num⟩

end D11.Ch14.VariationInequalities
