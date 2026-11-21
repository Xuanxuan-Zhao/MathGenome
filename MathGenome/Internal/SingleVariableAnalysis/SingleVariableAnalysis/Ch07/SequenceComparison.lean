import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.StandardLimits
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.ESequence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.SequenceComparison

/-!
The reciprocal increments x/(n+1) tend to zero, their bases are eventually
positive, and (n+1) * (x/(n+1)) = x at every index. The upstream
variable-power limit therefore tends to the factorial-series exponential.
On the positive tail the shared real-power bridge identifies these powers
with natural powers. No nonzero hypothesis on x is needed.
At x=1 uniqueness of limits identifies the previously constructed
supremum limit with the series value, hence with the canonical exp(1).
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology

private theorem sequence_increment_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => x / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have hrec : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      reciprocal_limit.comp (tendsto_add_atTop_nat 1)
  simpa only [mul_zero, mul_one_div] using tendsto_const_nhds.mul hrec

theorem sequence_comparison_eventually_positive :
    Specs.SingleVariableAnalysis.Ch07.SequenceComparison.eventuallyPositiveBases := by
  intro x
  have h : Tendsto (fun n : ℕ => 1 + x / (n + 1 : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (sequence_increment_tendsto x)
  exact h.eventually (lt_mem_nhds zero_lt_one)

theorem sequence_comparison_limit :
    Specs.SingleVariableAnalysis.Ch07.SequenceComparison.sequenceLimit := by
  intro x
  apply (realSequenceConverges_iff _ _).mpr
  have hpos := sequence_comparison_eventually_positive x
  have hproduct : Tendsto (fun n : ℕ => (n + 1 : ℝ) * (x / (n + 1 : ℝ)))
      atTop (𝓝 x) := by
    have heq : (fun n : ℕ => (n + 1 : ℝ) * (x / (n + 1 : ℝ))) =
        (fun _ : ℕ => x) := by
      funext n
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact tendsto_const_nhds
  have h := standard_variable_power_limit atTop
    (fun n : ℕ => x / (n + 1 : ℝ)) (fun n : ℕ => (n + 1 : ℝ)) x
    (sequence_increment_tendsto x) hpos hproduct
  apply h.congr'
  filter_upwards [hpos] with n hn
  change realPower (1 + x / (n + 1 : ℝ)) (n + 1 : ℝ) =
    (1 + x / (n + 1 : ℝ)) ^ (n + 1)
  rw [realPower_eq_rpow _ hn]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Real.rpow_natCast (1 + x / (n + 1 : ℝ)) (n + 1)

theorem sequence_comparison_zero :
    Specs.SingleVariableAnalysis.Ch07.SequenceComparison.zeroTerms := by
  intro n
  simp

theorem eSequenceLimit_eq_seriesExp :
    Specs.SingleVariableAnalysis.Ch07.SequenceComparison.classicalLimit := by
  have hseq : RealSequenceConverges eSequence (realSeriesExp 1) :=
    sequence_comparison_limit 1
  exact tendsto_nhds_unique
    ((realSequenceConverges_iff _ _).mp eSequence_converges)
    ((realSequenceConverges_iff _ _).mp hseq)

theorem eSequenceLimit_eq_exp_one :
    Specs.SingleVariableAnalysis.Ch07.SequenceComparison.classicalLimitCanonical := by
  exact eSequenceLimit_eq_seriesExp.trans (expSeries_eq_realExp 1)

end SingleVariableAnalysis
