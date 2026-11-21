import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.ContinuousVariation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Jordan
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-! Continuity of strict-partition variation (K03.15.continuous_variation).
The library continuity theorem uses signed variation on an intersected interval.
We first identify it with the manuscript's variation at every point of [a,b].
No extension or continuity assumption outside the interval is used. -/
namespace SingleVariableAnalysis.BV
open scoped Topology
universe u

theorem totalVariation_toReal_eq_variationOnFromTo {E : Type u} [NormedAddCommGroup E]
    (f : ℝ → E) {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    (totalVariation f a x).toReal = variationOnFromTo f (Set.Icc a b) a x := by
  simp only [totalVariation]
  rw [totalVariation_eq_eVariationOn f hx.1,
    variationOnFromTo.eq_of_le _ _ hx.1,
    Set.inter_eq_right.mpr (Set.Icc_subset_Icc le_rfl hx.2)]

theorem continuousOn_totalVariation :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.continuousVariation := by
  intro E _ f a b hab hf hc x hx
  have hBV := (boundedVariation_iff f hab).mp hf
  have h := (hBV.continuousWithinAt_variationOnFromTo_iff ⟨le_rfl, hab⟩ hx).mpr (hc x hx)
  exact h.congr_of_mem (fun y hy => totalVariation_toReal_eq_variationOnFromTo f hy) hx

theorem rightContinuousAt_totalVariation :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.rightContinuousVariationAt := by
  intro E _ f a b c hab hf hc hfc
  have hBV := (boundedVariation_iff f hab).mp hf
  have h := hBV.continuousWithinAt_variationOnFromTo_inter_Ici ⟨le_rfl, hab⟩ hc hfc
  exact h.congr_of_mem (fun y hy => totalVariation_toReal_eq_variationOnFromTo f hy.1)
    ⟨hc, by simp⟩

theorem leftContinuousAt_totalVariation :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.leftContinuousVariationAt := by
  intro E _ f a b c hab hf hc hfc
  have hBV := (boundedVariation_iff f hab).mp hf
  have h := hBV.continuousWithinAt_variationOnFromTo_inter_Iic ⟨le_rfl, hab⟩ hc hfc
  exact h.congr_of_mem (fun y hy => totalVariation_toReal_eq_variationOnFromTo f hy.1)
    ⟨hc, by simp⟩

theorem continuous_jordan_canonical :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.continuousJordan := by
  intro f a b hab hf hc
  have hv : ContinuousOn (variationFunction f a) (Set.Icc a b) :=
    continuousOn_totalVariation f hab hf hc
  refine ⟨?_, ?_, jordan_canonical f hab hf⟩
  · exact ((hv.add hc).sub continuousOn_const).div_const 2
  · exact ((hv.sub hc).add continuousOn_const).div_const 2

noncomputable abbrev rightJumpStep :=
  Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue

theorem rightJumpStep_monotone : Monotone rightJumpStep := by
  intro x y hxy
  simp only [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue]
  split_ifs <;> grind

theorem rightJumpStep_variation :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepVariation := by
  intro x hx
  have h := totalVariation_of_monotoneOn rightJumpStep hx.1
    (rightJumpStep_monotone.monotoneOn (Set.Icc (-1) x))
  change (totalVariation rightJumpStep (-1) x).toReal = rightJumpStep x
  simp only [totalVariation]
  rw [h, ENNReal.toReal_ofReal (abs_nonneg _)]
  simp only [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue]
  split_ifs <;> norm_num at *

theorem rightJumpStep_rightContinuous (c : ℝ) :
    ContinuousWithinAt rightJumpStep (Set.Ici c) c := by
  by_cases hc : 0 ≤ c
  · apply (continuousWithinAt_const (b := (1 : ℝ))).congr_of_mem _ (Set.mem_Ici.mpr le_rfl)
    intro y hy
    simp [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue,
      hc.trans hy]
  · have hc' : c < 0 := lt_of_not_ge hc
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hc'] with y hy
    simp [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue,
      not_le.mpr hy]

theorem rightJumpStep_leftLimit :
    Filter.Tendsto rightJumpStep (𝓝[<] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue,
    not_le.mpr (Set.mem_Iio.mp hy)]

theorem rightJumpStep_not_continuousWithinAt :
    ¬ ContinuousWithinAt rightJumpStep (Set.Icc (-1) 1) 0 := by
  intro h
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousWithinAt_iff.mp h (1 / 2) (by norm_num)
  let t : ℝ := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have hdist : dist (-t) (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht] using htδ
  have hbad := hbound (x := -t) ⟨by linarith, by linarith⟩ hdist
  have hneg : ¬ (0 : ℝ) ≤ -t := by linarith
  norm_num [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue,
    hneg] at hbad

theorem rightContinuity_counterexample :
    Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.rightContinuityCounterexample := by
  have hbv : HasBoundedVariation rightJumpStep (-1) 1 :=
    (hasBoundedVariation_of_monotone rightJumpStep (by norm_num)
      (Or.inl (rightJumpStep_monotone.monotoneOn _))).1
  refine ⟨hbv, rightJumpStep_rightContinuous, rightJumpStep_leftLimit, ?_,
    rightJumpStep_not_continuousWithinAt, ?_, ?_⟩
  · norm_num [rightJumpStep, Specs.SingleVariableAnalysis.Ch15.ContinuousVariation.stepValue]
  · intro c hc
    exact rightContinuousAt_totalVariation rightJumpStep (by norm_num) hbv hc
      ((rightJumpStep_rightContinuous c).mono Set.inter_subset_right)
  · intro h
    apply rightJumpStep_not_continuousWithinAt
    exact h.congr_of_mem (fun y hy => (rightJumpStep_variation y hy).symm) (by norm_num)

end SingleVariableAnalysis.BV
