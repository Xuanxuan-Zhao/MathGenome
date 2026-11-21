import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.SingularExamples
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.Frobenius
import MathGenome.Internal.ODEDynamics.D13Unified.Ch09.Resonance
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Euler powers and the normalized Bessel solution from
paper.tex, Example d13:09:singular-examples. The Bessel coefficients satisfy
the shared Frobenius recurrence at every positive radius. Its convergence
and analytic substitution results therefore prove that the displayed series
is entire and solves the equation on every supplied logarithm branch. -/

noncomputable section
namespace D13Unified.Ch09.SingularExamples
open Specs.D13Unified.Ch09.Indicial
open Specs.D13Unified.Ch09.Frobenius
open Specs.D13Unified.Ch09.SingularExamples
open scoped BigOperators Topology

lemma euler_power (R : ℝ) (hR : 0 < R) (a b r : ℂ) (L : LogBranch R)
    (hr : r * (r - 1) + a * r + b = 0) :
    solutionValue (eulerEquation R hR a b) L (powerValue L r) := by
  have h := Frobenius.powerSolutionBridge (eulerEquation R hR a b) L r
    (fun _ => 1) (differentiableOn_const 1) (by
      intro z hz
      simpa [eulerEquation, deriv_const, mul_comm] using hr)
  change solutionValue (eulerEquation R hR a b) L (fun z => Complex.exp (r * L.log z))
  simpa only [eulerEquation, powerValue, mul_one] using h

theorem eulerDistinct : eulerDistinctType := by
  intro R hR a b L r₁ r₂ h₁ h₂ hne
  refine ⟨euler_power R hR a b r₁ L h₁, euler_power R hR a b r₂ L h₂, ?_⟩
  have h := Frobenius.independentMultipliers (eulerEquation R hR a b) L r₁ r₂ hne
    (fun _ => 1) (fun _ => 1) (differentiableOn_const 1) (differentiableOn_const 1) rfl rfl
  change independentValue L (fun z => Complex.exp (r₁ * L.log z))
    (fun z => Complex.exp (r₂ * L.log z))
  simpa only [eulerEquation, powerValue, mul_one] using h

theorem eulerRepeated : eulerRepeatedType := by
  intro R hR a b r L ha hb
  have hr : r * (r - 1) + a * r + b = 0 := by rw [ha, hb]; ring
  have hy := euler_power R hR a b r L hr
  refine ⟨hy, ?_⟩
  apply Resonance.reduction_pair (eulerEquation R hR a b) L (powerValue L r)
    (fun z => powerValue L r z ^ 2 / z) L.log hy
  · intro z hz
    exact Complex.exp_ne_zero _
  · intro z hz
    have hgeom := Indicial.setup.2.2.1 R L.angle hR
    have hz0 := hgeom.2.2.2 z hz
    have hp := Frobenius.hasDerivAt_branchPower (eulerEquation R hR a b) L r hz
    convert (hp.pow 2).div (hasDerivAt_id z) hz0 using 1
    · rfl
    · dsimp [eulerEquation]
      rw [ha]
      field_simp
      ring
  · intro z hz
    exact div_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _))
      ((Indicial.setup.2.2.1 R L.angle hR).2.2.2 z hz)
  · intro z hz
    convert Frobenius.hasDerivAt_branchLog (eulerEquation R hR a b) L hz using 1
    have hp0 : powerValue L r z ≠ 0 := Complex.exp_ne_zero _
    field_simp

/-- The ordinary coefficient sequence has zero odd coefficients. -/
def besselCoefficients (ν : ℝ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then besselCoefficient ν (n / 2) else 0

@[simp] lemma besselCoefficients_even (ν : ℝ) (j : ℕ) :
    besselCoefficients ν (2 * j) = besselCoefficient ν j := by
  simp [besselCoefficients]

@[simp] lemma besselCoefficients_odd (ν : ℝ) (j : ℕ) :
    besselCoefficients ν (2 * j + 1) = 0 := by
  simp [besselCoefficients, Nat.add_mod]

@[simp] lemma besselCoefficient_zero (ν : ℝ) : besselCoefficient ν 0 = 1 := by
  simp [besselCoefficient]

lemma bessel_product_ne_zero {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) :
    (∏ k ∈ Finset.Icc 1 j, ((ν : ℂ) + (k : ℂ))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1
  have hpos : 0 < ν + (k : ℝ) := add_pos_of_nonneg_of_pos hν hkpos
  exact_mod_cast ne_of_gt hpos

lemma besselCoefficient_step {ν : ℝ} (hν : 0 ≤ ν) (j : ℕ) :
    4 * (j + 1 : ℂ) * ((ν : ℂ) + (j + 1 : ℂ)) * besselCoefficient ν (j + 1) =
      -besselCoefficient ν j := by
  have hj : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  have hv : (ν : ℂ) + (j + 1 : ℂ) ≠ 0 := by
    have : 0 < ν + ((j : ℝ) + 1) := by positivity
    exact_mod_cast ne_of_gt this
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  unfold besselCoefficient
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ j + 1)]
  simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [bessel_product_ne_zero hν j]

lemma taylor_constant (c : ℂ) (n : ℕ) :
    taylorCoefficientValue (fun _ : ℂ => c) n = if n = 0 then c else 0 := by
  simp only [taylorCoefficientValue, iteratedDeriv_const]
  split_ifs with h
  · subst n; simp
  · simp

lemma taylor_bessel_q (ν : ℝ) (n : ℕ) :
    taylorCoefficientValue (fun z : ℂ => z ^ 2 - (ν : ℂ) ^ 2) n =
      if n = 0 then -(ν : ℂ) ^ 2 else if n = 2 then 1 else 0 := by
  rw [taylorCoefficientValue, iteratedDeriv_fun_sub
    ((contDiff_id.pow 2).contDiffAt) contDiffAt_const,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_const]
  by_cases h0 : n = 0
  · subst n; simp
  by_cases h2 : n = 2
  · subst n; norm_num
  · simp [h0, h2]

lemma bessel_indicial (R : ℝ) (hR : 0 < R) (ν : ℝ) (r : ℂ) :
    indicialValue (besselEquation R hR ν) r = r ^ 2 - (ν : ℂ) ^ 2 := by
  simp [indicialValue, pZeroValue, qZeroValue, taylorCoefficientValue,
    besselEquation, iteratedDeriv_zero]
  ring

lemma bessel_recurrence {ν : ℝ} (hν : 0 ≤ ν) (R : ℝ) (hR : 0 < R) :
    IsCoefficientSequence (besselEquation R hR ν) (ν : ℂ) (besselCoefficients ν) := by
  refine ⟨by simp [besselCoefficients], ?_⟩
  intro n hn
  have hsum : (∑ k ∈ Finset.Icc 1 n,
      (((ν : ℂ) + (n : ℂ) - (k : ℂ)) *
        taylorCoefficientValue (besselEquation R hR ν).p k +
        taylorCoefficientValue (besselEquation R hR ν).q k) * besselCoefficients ν (n - k)) =
      if 2 ≤ n then besselCoefficients ν (n - 2) else 0 := by
    simp only [besselEquation, taylor_constant, taylor_bessel_q]
    trans ∑ k ∈ Finset.Icc 1 n, if k = 2 then besselCoefficients ν (n - 2) else 0
    · apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      by_cases hk2 : k = 2
      · subst k; simp
      · simp [hk0, hk2]
    · simp
  rw [hsum, bessel_indicial]
  obtain ⟨j, hj⟩ | ⟨j, hj⟩ := Nat.even_or_odd n
  · have heq : n = 2 * j := by omega
    clear hj
    subst n
    have hj1 : 1 ≤ j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [ite_eq_left (by omega)]
    have heq : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [heq, besselCoefficients_even, besselCoefficients_even]
    have hs := besselCoefficient_step hν k
    push_cast
    linear_combination hs
  · have heq : n = 2 * j + 1 := by omega
    clear hj
    subst n
    rw [besselCoefficients_odd, mul_zero]
    split_ifs with hh
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      rw [show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega, besselCoefficients_odd]
      simp
    · simp

/-- Applying the convergence theorem at an arbitrary radius gives the entire factor. -/
lemma bessel_analytic {ν : ℝ} (hν : 0 ≤ ν) (R : ℝ) (hR : 0 < R) :
    AnalyticSeries (besselEquation R hR ν) (besselCoefficients ν) := by
  apply Frobenius.coefficientSeries_analytic (besselEquation R hR ν) (ν : ℂ)
  · rw [bessel_indicial]; ring
  · exact bessel_recurrence hν R hR

lemma bessel_coefficients_summable {ν : ℝ} (hν : 0 ≤ ν) (z : ℂ) :
    Summable (fun n : ℕ => ‖besselCoefficients ν n * z ^ n‖) := by
  have hR : 0 < ‖z‖ + 1 := by positivity
  exact (bessel_analytic hν (‖z‖ + 1) hR).2.2.2 z (by
    simpa only [besselEquation, Metric.mem_ball, dist_zero_right] using (lt_add_one ‖z‖)) |>.1

lemma bessel_even_summable {ν : ℝ} (hν : 0 ≤ ν) (z : ℂ) :
    Summable (fun j : ℕ => ‖besselCoefficient ν j * z ^ (2 * j)‖) := by
  have h := (bessel_coefficients_summable hν z).comp_injective
    (show Function.Injective (fun j : ℕ => 2 * j) by intro i j hij; dsimp at hij; omega)
  simpa only [Function.comp_def, besselCoefficients_even] using h

lemma bessel_series_eq {ν : ℝ} (hν : 0 ≤ ν) :
    series (besselCoefficients ν) = besselFactor ν := by
  funext z
  have hs : Summable (fun j : ℕ => besselCoefficient ν j * z ^ (2 * j)) :=
    (bessel_even_summable hν z).of_norm
  have ho : HasSum (fun j : ℕ => besselCoefficients ν (2 * j + 1) * z ^ (2 * j + 1)) 0 := by
    simpa only [besselCoefficients_odd, zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have he : HasSum (fun j : ℕ => besselCoefficients ν (2 * j) * z ^ (2 * j))
      (besselFactor ν z) := by
    simpa only [besselCoefficients_even, besselFactor] using hs.hasSum
  have ht := HasSum.even_add_odd (f := fun n : ℕ => besselCoefficients ν n * z ^ n) he ho
  simpa only [add_zero, series] using ht.tsum_eq

theorem besselEntire : besselEntireType := by
  intro ν hν
  refine ⟨bessel_even_summable hν, ?_, ?_⟩
  · rw [← bessel_series_eq hν]
    intro z
    have hR : 0 < ‖z‖ + 1 := by positivity
    have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
      simp [Metric.mem_ball]
    exact (bessel_analytic hν (‖z‖ + 1) hR).1.differentiableAt
      (Metric.isOpen_ball.mem_nhds hz)
  · rw [← bessel_series_eq hν]
    exact (bessel_analytic hν 1 zero_lt_one).2.2.1

theorem besselSolution : besselSolutionType := by
  intro ν hν R hR L
  have hr : indicialValue (besselEquation R hR ν) (ν : ℂ) = 0 := by
    rw [bessel_indicial]; ring
  have h := Frobenius.powerSolutionBridge (besselEquation R hR ν) L (ν : ℂ)
    (series (besselCoefficients ν)) (bessel_analytic hν R hR).1
    (Frobenius.coefficientSeries_multiplierEquation (besselEquation R hR ν) (ν : ℂ)
      hr (bessel_recurrence hν R hR))
  rw [bessel_series_eq hν] at h
  exact h

end D13Unified.Ch09.SingularExamples
