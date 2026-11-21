import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.Stirling
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.StirlingLogError
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Stirling's normalization and the full logarithmic and relative errors.
For normalization we reuse the library's Wallis-based limit, after translating
its sqrt(2n) normalization using the already proved logarithmic bridge.
The rate comes from the upstream logarithmic error, not from equivalence alone.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch17.Stirling
open Specs.SingleVariableAnalysis.Ch17.StirlingLogError (logSequence)

def stirlingMainTerm : ℕ → ℝ := mainTerm

def stirlingRemainder : ℕ → ℝ := remainder

theorem stirling_log_limit : logarithmicLimit := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
    (show Real.sqrt Real.pi ≠ 0 by positivity)).add_const (Real.log 2 / 2)
  have he : Real.log (Real.sqrt Real.pi) + Real.log 2 / 2 =
      Real.log (Real.sqrt (2 * Real.pi)) := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_sqrt (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (stirling_log_bridge n hn).symm

theorem stirling_normalization : normalization := by
  intro c hc
  have he := tendsto_nhds_unique hc stirling_log_limit
  rw [he, Real.exp_log (by positivity)]

theorem stirling_log_remainder_bound : logarithmicError := by
  obtain ⟨c, hc, hb⟩ := stirling_log_error
  have he := tendsto_nhds_unique hc stirling_log_limit
  change Asymptotics.IsBigO atTop
    (fun n => logSequence n - Real.log (Real.sqrt (2 * Real.pi))) _
  simpa only [he] using hb

theorem stirling_mainTerm_pos : positiveMainTerm := by
  intro n hn
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold mainTerm
  positivity

private theorem log_stirling_mainTerm (n : ℕ) (hn : 1 ≤ n) :
    Real.log (mainTerm n) = Real.log (Real.sqrt (2 * Real.pi)) +
      ((n : ℝ) + 1/2) * Real.log n - n := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold mainTerm
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hp.ne',
    Real.log_pow, Real.log_div hp.ne' (Real.exp_ne_zero 1), Real.log_exp]
  ring

theorem stirling_exact_formula : exactFormula := by
  intro n hn
  have hp := stirling_mainTerm_pos n hn
  calc
    (n.factorial : ℝ) = Real.exp (Real.log (n.factorial : ℝ)) :=
      (Real.exp_log (by positivity)).symm
    _ = Real.exp (Real.log (mainTerm n) + remainder n) := by
      rw [log_stirling_mainTerm n hn]
      congr 1
      unfold remainder logSequence
      ring
    _ = mainTerm n * Real.exp (remainder n) := by
      rw [Real.exp_add, Real.exp_log hp]

private theorem stirling_remainder_tendsto_zero : Tendsto remainder atTop (𝓝 0) := by
  change Tendsto (fun n => logSequence n - Real.log (Real.sqrt (2 * Real.pi))) atTop (𝓝 0)
  simpa only [sub_self] using stirling_log_limit.sub_const
    (Real.log (Real.sqrt (2 * Real.pi)))

private theorem stirling_ratio_eventually :
    (fun n : ℕ => (n.factorial : ℝ) / mainTerm n) =ᶠ[atTop]
      (fun n => Real.exp (remainder n)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [stirling_exact_formula n hn]
  exact mul_div_cancel_left₀ _ (stirling_mainTerm_pos n hn).ne'

theorem stirling_ratio_limit : ratioLimit := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp stirling_remainder_tendsto_zero
  change Tendsto (fun n : ℕ => (n.factorial : ℝ) / mainTerm n) atTop (𝓝 1)
  simpa only [Real.exp_zero] using h.congr' stirling_ratio_eventually.symm

theorem stirling_asymptotic_equivalence : equivalence := by
  exact Asymptotics.isEquivalent_of_tendsto_one stirling_ratio_limit

theorem stirling_relative_error : relativeError := by
  have h : Asymptotics.IsBigO atTop (fun n => Real.exp (remainder n) - 1) remainder := by
    simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one, Function.comp_def] using
      (Real.exp_sub_sum_range_isBigO_pow 1).comp_tendsto stirling_remainder_tendsto_zero
  apply (h.trans stirling_log_remainder_bound).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [stirling_ratio_eventually] with n hn
  rw [hn]

end SingleVariableAnalysis
