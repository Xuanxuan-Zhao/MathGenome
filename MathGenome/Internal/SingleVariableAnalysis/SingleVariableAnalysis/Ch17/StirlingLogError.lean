import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.StirlingLogError
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The source sequence is bridged to Mathlib's normalized Stirling sequence.
Only the positive-limit and stepwise-bound results from the first part of that
library proof are used; identifying the constant via Wallis is a later goal.
A finite logarithmic Taylor estimate proves the leading increment coefficient.
The stepwise bound telescopes against 1/(12n), giving an explicit error bound
and the sum of the absolute tail. See proof-work.md for provenance. -/

noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology BigOperators
open Specs.SingleVariableAnalysis.Ch17.StirlingLogError

def stirlingLogSequence : ℕ → ℝ := logSequence

theorem stirling_log_increment : incrementIdentity := by
  intro n hn
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hq : (0 : ℝ) < n+1 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have he : (1 : ℝ) + 1/n = (n+1)/n := by field_simp
  simp only [logSequence, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Real.log_mul hq.ne' hf, he, Real.log_div hq.ne' hp.ne']
  ring

/-- Translate the library's normalized sequence, including its sqrt(2n),
into the precise logarithmic sequence used in the manuscript. -/
theorem stirling_log_bridge (n : ℕ) (hn : 1 ≤ n) :
    logSequence n = Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hp.ne',
    Real.log_div hp.ne' (Real.exp_ne_zero 1), Real.log_exp]
  unfold logSequence
  ring

theorem stirling_log_antitone : Antitone (fun n : ℕ => logSequence (n+1)) := by
  intro n m h
  dsimp only
  rw [stirling_log_bridge _ (by omega), stirling_log_bridge _ (by omega)]
  have hb := Stirling.log_stirlingSeq'_antitone h
  change Real.log (Stirling.stirlingSeq (m+1)) ≤ Real.log (Stirling.stirlingSeq (n+1)) at hb
  linarith

theorem stirling_log_step_bound (n : ℕ) (hn : 1 ≤ n) :
    logSequence n - logSequence (n+1) ≤ 1/(12*(n : ℝ)*(n+1)) := by
  rw [stirling_log_bridge n hn, stirling_log_bridge (n+1) (by omega)]
  simpa only [add_sub_add_right_eq_sub] using Stirling.log_stirlingSeq_sdiff_le n

/-- Existence here uses only the positive-limit part of the library proof;
no value for the eventual normalization constant is needed. -/
theorem stirling_log_has_limit : ∃ c : ℝ, Tendsto logSequence atTop (𝓝 c) := by
  obtain ⟨a, ha, hlim⟩ := Stirling.stirlingSeq_has_pos_limit_a
  refine ⟨Real.log a + Real.log 2 / 2, ?_⟩
  have h := (hlim.log ha.ne').add_const (Real.log 2 / 2)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (stirling_log_bridge n hn).symm

/-- A finite Taylor estimate on the positive half-neighborhood of zero. -/
theorem stirling_log_taylor_bound (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    |Real.log (1+x) - (x-x^2/2+x^3/3)| ≤ 2*x^4 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -x) (by rw [abs_neg, abs_of_nonneg hx]; linarith) 3
  norm_num [Finset.sum_range_succ, abs_neg, abs_of_nonneg hx] at h
  have he : -x + x^2/2 + -x^3/3 + Real.log (1+x) =
      Real.log (1+x) - (x-x^2/2+x^3/3) := by ring
  have hb : x^4 / (1-x) ≤ 2*x^4 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-x)).2
    nlinarith [mul_nonneg (pow_nonneg hx 4) (show 0 ≤ 1-2*x by linarith)]
  calc
    _ ≤ x^4/(1-x) := by convert h using 1; ring_nf
    _ ≤ _ := hb

theorem stirling_log_increment_bound (n : ℕ) (hn : 2 ≤ n) :
    |logSequence (n+1) - logSequence n + 1/(12*(n : ℝ)^2)| ≤
      3*((n : ℝ)⁻¹)^3 := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hp.le
  have hx' : (n : ℝ)⁻¹ ≤ 1/2 := (inv_le_comm₀ hp (by norm_num)).2 (by simpa using hn')
  have ht := stirling_log_taylor_bound (n : ℝ)⁻¹ hx hx'
  have he : 1 - ((n : ℝ)+1/2) * Real.log (1+(n : ℝ)⁻¹) + 1/(12*(n : ℝ)^2) =
      -(((n : ℝ)+1/2) * (Real.log (1+(n : ℝ)⁻¹) -
        ((n : ℝ)⁻¹-((n : ℝ)⁻¹)^2/2+((n : ℝ)⁻¹)^3/3))) -
        ((n : ℝ)⁻¹)^3/6 := by field_simp; ring
  rw [stirling_log_increment n (by omega)]
  rw [one_div (n : ℝ), he]
  calc
    _ ≤ |((n : ℝ)+1/2) * (Real.log (1+(n : ℝ)⁻¹) -
        ((n : ℝ)⁻¹-((n : ℝ)⁻¹)^2/2+((n : ℝ)⁻¹)^3/3))| +
        |((n : ℝ)⁻¹)^3/6| := by
      have htri (a b : ℝ) : |-a-b| ≤ |a|+|b| := by
        simpa only [abs_neg] using (abs_sub (-a) b)
      exact htri _ _
    _ ≤ ((n : ℝ)+1/2)*(2*((n : ℝ)⁻¹)^4) + ((n : ℝ)⁻¹)^3/6 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)+1/2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ)⁻¹)^3/6)]
      exact add_le_add (mul_le_mul_of_nonneg_left ht (by positivity)) le_rfl
    _ = (2+(n : ℝ)⁻¹+1/6)*((n : ℝ)⁻¹)^3 := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem stirling_log_increment_expansion : incrementExpansion := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (inv_nonneg.mpr (show (0 : ℝ) ≤ n from Nat.cast_nonneg n))]
    using stirling_log_increment_bound n hn

/-- The Robbins bound telescopes exactly against 1/(12n). -/
theorem stirling_log_corrected_monotone :
    Monotone (fun n : ℕ => logSequence (n+1) - 1/(12*((n+1 : ℕ):ℝ))) := by
  apply monotone_nat_of_le_succ
  intro n
  have hb := stirling_log_step_bound (n+1) (by omega)
  have he : 1/(12*(((n+1:ℕ):ℝ))*(((n+1:ℕ):ℝ)+1)) =
      1/(12*(((n+1:ℕ):ℝ))) - 1/(12*(((n+2:ℕ):ℝ))) := by
    push_cast
    field_simp
    ring
  rw [he] at hb
  convert (show logSequence (n+1) - 1/(12*(((n+1:ℕ):ℝ))) ≤
      logSequence (n+2) - 1/(12*(((n+2:ℕ):ℝ))) by linarith) using 1

theorem stirling_log_limit_bounds {c : ℝ} (hc : Tendsto logSequence atTop (𝓝 c)) (n : ℕ) :
    0 ≤ logSequence (n+1)-c ∧ logSequence (n+1)-c ≤ 1/(12*(((n+1:ℕ):ℝ))) := by
  have hs := hc.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => 1/(12*(((n+1:ℕ):ℝ)))) atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1/12 : ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    ext k
    simp only [Function.comp_apply]
    ring
  have hl := stirling_log_antitone.le_of_tendsto hs n
  have hu := stirling_log_corrected_monotone.ge_of_tendsto
    (by simpa only [Function.comp_apply, sub_zero] using hs.sub hi) n
  exact ⟨by linarith, by linarith⟩

theorem stirling_log_absolute_increments : absoluteIncrements := by
  obtain ⟨c, hc⟩ := stirling_log_has_limit
  apply summable_of_sum_range_le (c := logSequence 1-c) (fun _ => abs_nonneg _)
  intro n
  have he : ∀ i : ℕ, |logSequence (i+2) - logSequence (i+1)| =
      logSequence (i+1) - logSequence (i+2) := by
    intro i
    rw [abs_of_nonpos (by have := stirling_log_antitone (Nat.le_succ i); dsimp at this; linarith)]
    ring
  simp_rw [he]
  have ht := Finset.sum_range_sub' (fun i => logSequence (i+1)) n
  have hl := (stirling_log_limit_bounds hc n).1
  simp only [zero_add] at ht
  convert (show logSequence 1-logSequence (n+1) ≤ logSequence 1-c by linarith) using 1

theorem stirling_log_absolute_tail_bound : absoluteTailBound := by
  obtain ⟨c, hc⟩ := stirling_log_has_limit
  refine ⟨c, hc, ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one]
  refine ⟨?_, stirling_log_limit_bounds hc j⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => abs_nonneg _) _).2
  have he (i : ℕ) : |logSequence (j+1+i+1) - logSequence (j+1+i)| =
      logSequence (j+1+i) - logSequence (j+1+i+1) := by
    have hm := stirling_log_antitone (show j+i ≤ j+i+1 by omega)
    have ht : logSequence (j+1+i+1) ≤ logSequence (j+1+i) := by
      convert hm using 1 <;> congr 1 <;> omega
    rw [abs_of_nonpos (sub_nonpos.mpr ht)]
    ring
  have hl : Tendsto (fun m : ℕ => logSequence (j+1+m)) atTop (𝓝 c) := by
    convert hc.comp (tendsto_add_atTop_nat (j+1)) using 1
    funext m
    change logSequence (j+1+m) = logSequence (m+(j+1))
    congr 1
    omega
  have ht : ∀ m : ℕ, (∑ i ∈ Finset.range m,
      |logSequence (j+1+i+1) - logSequence (j+1+i)|) =
      logSequence (j+1)-logSequence (j+1+m) := by
    intro m
    simp_rw [he]
    convert Finset.sum_range_sub' (fun i => logSequence (j+1+i)) m using 1
  exact (tendsto_const_nhds.sub hl).congr' (Eventually.of_forall (fun m => (ht m).symm))

theorem stirling_log_error : logarithmicError := by
  obtain ⟨c, hc⟩ := stirling_log_has_limit
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound (1/12) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hb := stirling_log_limit_bounds hc k
  simp only [Nat.succ_eq_add_one, Real.norm_eq_abs]
  rw [abs_of_nonneg hb.1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((k+1:ℕ):ℝ))⁻¹)]
  convert hb.2 using 1
  ring

theorem stirling_factorial_log_error : factorialForm := by
  obtain ⟨c, hc, hb⟩ := stirling_log_error
  refine ⟨c, hc, hb, Real.exp_pos c, ?_⟩
  intro n hn
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.rpow_def_of_pos hp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have he : c + Real.log (n : ℝ) * ((n : ℝ)+1/2) + -(n : ℝ) + (logSequence n-c) =
      Real.log (n.factorial : ℝ) := by unfold logSequence; ring
  rw [he, Real.exp_log (by positivity)]

end SingleVariableAnalysis
