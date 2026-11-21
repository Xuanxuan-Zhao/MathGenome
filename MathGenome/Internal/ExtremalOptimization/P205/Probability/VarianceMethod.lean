import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.VarianceMethod
import MathGenome.Internal.ExtremalOptimization.P205.Probability.MomentIdentities
import MathGenome.Internal.ExtremalOptimization.P205.Probability.MarkovZeroDefect

open MeasureTheory Filter
open scoped Topology

namespace P205.Probability.VarianceMethod

/-- The zero event is contained in the inclusive deviation event at the mean. -/
theorem zero_probability_le_variance :
    Specs.P205.Probability.VarianceMethod.ZeroProbabilityBound := by
  intro Ω _ μ _ X hX _hNonneg hMean
  have hSubset : {ω | X ω = 0} ⊆
      {ω | (∫ x, X x ∂μ) ≤ |X ω - ∫ x, X x ∂μ|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    simp [hω, abs_of_pos hMean]
  have hCheb := ProbabilityTheory.meas_ge_le_variance_div_sq hX hMean
  have hReal := ENNReal.toReal_mono (by finiteness) hCheb
  rw [ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg X μ)
    (sq_nonneg _))] at hReal
  exact (measureReal_mono hSubset).trans hReal

/-- For an almost-surely nonnegative variable the positive and zero events
are complementary up to a null set. -/
theorem positive_probability_eq_one_sub_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    μ.real {ω | 0 < X ω} = 1 - μ.real {ω | X ω = 0} := by
  have hZero : NullMeasurableSet {ω | X ω = 0} μ :=
    hX.aestronglyMeasurable.nullMeasurableSet_eq_fun aestronglyMeasurable_const
  have hEvents : {ω | 0 < X ω} =ᵐ[μ] {ω | X ω = 0}ᶜ := by
    filter_upwards [hNonneg] with ω hω
    apply propext
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact (lt_iff_le_and_ne).trans (and_iff_right hω) |>.trans ne_comm
  rw [measureReal_congr hEvents]
  exact probReal_compl_eq_one_sub₀ hZero

/-- The zero probabilities are squeezed between zero and the relative variances;
the complementary positive probabilities therefore converge to one. -/
theorem positive_probability_tendsto_one :
    Specs.P205.Probability.VarianceMethod.PositiveProbabilityTendstoOne := by
  intro Ω _ μ _ X hX hNonneg hMean hRatio
  have hZero : Tendsto (fun n ↦ (μ n).real {ω | X n ω = 0}) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ zero_probability_le_variance (μ n) (X n) (hX n) (hNonneg n)
        (hMean n)) hRatio
  have hSub := (tendsto_const_nhds (x := (1 : ℝ))).sub hZero
  simpa only [sub_zero, ← positive_probability_eq_one_sub_zero (μ _) (X _) (hX _)
    (hNonneg _)] using hSub

end P205.Probability.VarianceMethod
