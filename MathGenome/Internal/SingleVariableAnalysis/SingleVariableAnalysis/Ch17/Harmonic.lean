import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.Harmonic
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.EulerConstant
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.EmBound
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace SingleVariableAnalysis.Harmonic
open Set Filter
open scoped Topology BigOperators
open Riemann
open Specs.SingleVariableAnalysis.Ch17.EmRecursion
open Specs.SingleVariableAnalysis.Ch17.Bernoulli
open Specs.SingleVariableAnalysis.Ch17.EmBound
open Specs.SingleVariableAnalysis.Ch17.Harmonic

/-- Explicit real derivatives of the reciprocal, including the zeroth one. -/
def reciprocalDerivative (j : ℕ) (x : ℝ) : ℝ :=
  (-1)^j * (j.factorial : ℝ) * x ^ (-1 - (j : ℤ))

lemma reciprocalDerivative_hasDerivAt (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (reciprocalDerivative j) (reciprocalDerivative (j+1) x) x := by
  have h := (hasDerivAt_zpow (-1 - (j : ℤ)) x (Or.inl hx)).const_mul
    ((-1)^j * (j.factorial : ℝ))
  convert h using 1
  · rfl
  · dsimp only [reciprocalDerivative]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    push_cast
    rw [show (-1 - (j : ℤ) - 1) = -1 - ((j : ℤ) + 1) by omega]
    ring

lemma reciprocalDerivative_zero (x : ℝ) : reciprocalDerivative 0 x = 1/x := by
  simp [reciprocalDerivative, one_div]

lemma reciprocalDerivative_closed (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    Specs.SingleVariableAnalysis.Ch04.Higher.closedDerivativeFamilyValue
      k (fun x => 1/x) a b reciprocalDerivative := by
  refine ⟨fun x _ => reciprocalDerivative_zero x, fun j _ x hx => ?_, fun j _ x hx => ?_⟩
  · exact (reciprocalDerivative_hasDerivAt j (ha.trans_le hx.1).ne').continuousAt.continuousWithinAt
  · exact (reciprocalDerivative_hasDerivAt j (ha.trans_le hx.1).ne').hasDerivWithinAt

lemma reciprocalDerivative_div (j : ℕ) (x : ℝ) :
    reciprocalDerivative j x = (-1)^j * (j.factorial : ℝ) / x^(j+1) := by
  rw [reciprocalDerivative, show (-1 - (j : ℤ)) = -((j+1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, div_eq_mul_inv]

lemma reciprocalDerivative_even (m : ℕ) (x : ℝ) :
    reciprocalDerivative (2*m) x = ((2*m).factorial : ℝ) / x^(2*m+1) := by
  rw [reciprocalDerivative_div, (even_two_mul m).neg_one_pow, one_mul]

lemma reciprocalDerivative_odd (r : ℕ) (hr : 1 ≤ r) (x : ℝ) :
    reciprocalDerivative (2*r-1) x = -((2*r-1).factorial : ℝ) / x^(2*r) := by
  rw [reciprocalDerivative_div]
  have he : 2*r-1+1 = 2*r := by omega
  rw [he]
  have ho : Odd (2*r-1) := ⟨r-1, by omega⟩
  rw [ho.neg_one_pow, neg_one_mul]



lemma reciprocal_sum_Ioc {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Ioc (n : ℤ) (N : ℤ), 1/(k : ℝ)) = harmonicSum N - harmonicSum n := by
  have he : (∑ k ∈ Finset.Ico n N, 1/((k : ℝ)+1)) =
      ∑ k ∈ Finset.Ioc (n : ℤ) (N : ℤ), 1/(k : ℝ) := by
    apply Finset.sum_bij (fun k _ => ((k+1 : ℕ) : ℤ))
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_Ioc]
      omega
    · intro k hk l hl he
      omega
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      refine ⟨k.toNat-1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro k hk
      push_cast
      rfl
  rw [← he, Finset.sum_Ico_eq_sub _ hnN]
  rfl

lemma reciprocal_trapezoid {n N : ℕ} (hnN : n < N) :
    trapezoid (fun x : ℝ => 1/x) (n : ℤ) (N : ℤ) =
      harmonicSum N - harmonicSum n + 1/(2*(n : ℝ)) - 1/(2*(N : ℝ)) := by
  have hlt : (n : ℤ) < (N : ℤ) := by exact_mod_cast hnN
  have h := Finset.sum_Ioo_add_eq_sum_Ioc (f := fun k : ℤ => 1/(k : ℝ)) hlt
  rw [reciprocal_sum_Ioc hnN.le] at h
  dsimp [trapezoid]
  simp only [Int.cast_natCast]
  have he (x : ℝ) : 1 / 2 * (1 / x) = 1/(2*x) := by ring
  rw [he, he]
  push_cast at h
  have hh : 1/(N : ℝ) = 2*(1/(2*(N : ℝ))) := by ring
  linarith

lemma correction_term (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx : x ≠ 0) :
    (bernoulliNumberValue (2*r) / ((2*r).factorial : ℝ)) *
      reciprocalDerivative (2*r-1) x =
      -(bernoulliNumberValue (2*r) / ((2*r : ℕ) * x^(2*r))) := by
  rw [reciprocalDerivative_odd r hr]
  have hf : ((2*r).factorial : ℝ) = (2*r : ℕ) * ((2*r-1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (n := 2*r) (by omega)).symm
  rw [hf]
  have hfac : (((2*r-1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma norm_reciprocalDerivative_even (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖reciprocalDerivative (2*m) x‖ = reciprocalDerivative (2*m) x := by
  rw [Real.norm_eq_abs, reciprocalDerivative_even, abs_of_nonneg (by positivity)]

/-- The norm integral is evaluated by its genuine reciprocal antiderivative. -/
lemma norm_derivative_integral (m : ℕ) (hm : 1 ≤ m) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hN : RealIntegrable (fun x => ‖reciprocalDerivative (2*m) x‖) a b) :
    realIntegral _ hN = ((2*m-1).factorial : ℝ) / a^(2*m) -
      ((2*m-1).factorial : ℝ) / b^(2*m) := by
  have h := EulerMaclaurin.realCalculus.ftc
    (reciprocalDerivative (2*m-1)) (fun x => ‖reciprocalDerivative (2*m) x‖)
    hab
    (fun x hx => (reciprocalDerivative_hasDerivAt (2*m-1)
      (ha.trans_le hx.1).ne').continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [norm_reciprocalDerivative_even m (ha.trans hx.1)]
      have he : 2*m-1+1 = 2*m := by omega
      simpa only [he] using reciprocalDerivative_hasDerivAt (2*m-1) (ha.trans hx.1).ne') hN
  change realIntegral _ hN = _ at h
  rw [reciprocalDerivative_odd m hm, reciprocalDerivative_odd m hm] at h
  exact h.trans (by ring)



/-- Harmonic values with the finite logarithmic and Bernoulli parts removed. -/
def corrected (m n : ℕ) : ℝ :=
  harmonicSum n - seriesLog n - 1/(2*(n : ℝ)) + correction m n

lemma sum_corrections (m : ℕ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (n N : ℕ) (hea : a = n) (heb : b = N) :
    (∑ r ∈ Finset.range m,
      (bernoulliNumberValue (2*(r+1)) / ((2*(r+1)).factorial : ℝ)) *
        (reciprocalDerivative (2*(r+1)-1) b - reciprocalDerivative (2*(r+1)-1) a)) =
      correction m n - correction m N := by
  subst a b
  unfold correction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_sub, correction_term (r+1) (by omega) hb,
    correction_term (r+1) (by omega) ha]
  ring

/-- The finite EM bound, simplified before taking the endpoint to infinity. -/
lemma corrected_difference_bound (m : ℕ) (hm : 1 ≤ m) {n N : ℕ}
    (hn : 1 ≤ n) (hnN : n < N) :
    |corrected m N - corrected m n| ≤
      bernoulliMaximumValue (2*m) / ((2*m : ℕ) * (n : ℝ)^(2*m)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlt : (n : ℤ) < (N : ℤ) := by exact_mod_cast hnN
  have hle : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN.le
  have hD := reciprocalDerivative_closed (2*m) (b := (N : ℝ)) hn0
  obtain ⟨hf, hR, he⟩ := euler_maclaurin_real (n : ℤ) (N : ℤ) hlt m hm
    (fun x => 1/x) reciprocalDerivative hD
  obtain ⟨hR', hN, hb⟩ := em_real_remainder_bound (n : ℤ) (N : ℤ) hlt m hm
    (fun x => 1/x) reciprocalDerivative hD
  change trapezoid (fun x : ℝ => 1/x) (n : ℤ) (N : ℤ) =
    realIntegral _ hf + (∑ r ∈ Finset.range m,
      (bernoulliNumberValue (2*(r+1)) / ((2*(r+1)).factorial : ℝ)) *
        (reciprocalDerivative (2*(r+1)-1) (N : ℝ) -
          reciprocalDerivative (2*(r+1)-1) (n : ℝ))) -
    term (@Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue) (2*m) reciprocalDerivative hR at he
  rw [reciprocal_trapezoid hnN,
    reciprocal_integral_eq_log_sub (by exact_mod_cast hn) hle hf,
    sum_corrections m hn0.ne' hN0.ne' n N rfl rfl] at he
  have he' : corrected m N - corrected m n =
      -term (@Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue) (2*m) reciprocalDerivative hR := by
    dsimp [corrected]
    linarith
  rw [he', ← Real.norm_eq_abs]
  apply hb.trans
  have hI : realIntegral _ hN ≤ ((2*m-1).factorial : ℝ) / (n : ℝ)^(2*m) := by
    rw [norm_derivative_integral m hm hn0 hle hN]
    exact sub_le_self _ (by positivity)
  have hM : 0 ≤ bernoulliMaximumValue (2*m) := (bernoulli_maximum_attained (2*m)).1
  have hmul := mul_le_mul_of_nonneg_left hI
    (show 0 ≤ bernoulliMaximumValue (2*m) / ((2*m).factorial : ℝ) by positivity)
  refine hmul.trans_eq ?_
  have hfac : ((2*m).factorial : ℝ) = ((2*m : ℕ) : ℝ) * ((2*m-1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (n := 2*m) (by omega)).symm
  rw [hfac]
  have hfact : (((2*m-1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma inverse_power_tendsto (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => 1/(n : ℝ)^p) atTop (𝓝 0) := by
  simpa only [one_div, inv_pow, zero_pow hp.ne'] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow p

lemma correction_tendsto (m : ℕ) :
    Tendsto (fun n => correction m n) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum (Finset.range m)
    (f := fun r n : ℕ => bernoulliNumberValue (2*(r+1)) /
      ((2*(r+1) : ℕ) * (n : ℝ)^(2*(r+1))))
    (a := fun _ => (0 : ℝ)) (fun r _ => by
      simpa only [div_mul_eq_div_mul_one_div, mul_zero] using
        (inverse_power_tendsto (2*(r+1)) (by omega)).const_mul
          (bernoulliNumberValue (2*(r+1)) / ((2*(r+1) : ℕ) : ℝ)))
  simpa only [correction, Finset.sum_const_zero] using hs

lemma corrected_tendsto (m : ℕ) :
    Tendsto (corrected m) atTop (𝓝 eulerConstant) := by
  have hshift : Tendsto
      (fun n : ℕ => harmonicSum (n+1) - seriesLog ((n : ℝ)+1)) atTop (𝓝 eulerConstant) :=
    (realSequenceConverges_iff _ _).mp harmonic_log_convergence
  have hh : Tendsto (fun n : ℕ => harmonicSum n - seriesLog n) atTop (𝓝 eulerConstant) :=
    (tendsto_add_atTop_iff_nat 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hshift)
  have hi : Tendsto (fun n : ℕ => 1/(2*(n : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_mul_one_div, mul_zero] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
  change Tendsto (fun n => harmonicSum n - seriesLog n - 1/(2*(n : ℝ)) + correction m n)
    atTop (𝓝 eulerConstant)
  simpa only [sub_zero, add_zero] using (hh.sub hi).add (correction_tendsto m)

lemma error_eq_corrected (m n : ℕ) : error m n = corrected m n - eulerConstant := by
  change harmonicSum n - (seriesLog n + eulerConstant + 1/(2*(n : ℝ)) - correction m n) = _
  unfold corrected
  ring

/-- Passage to infinity in the finite EM inequality. No remainder limit is assumed. -/
theorem harmonic_expansion : Specs.SingleVariableAnalysis.Ch17.Harmonic.harmonicExpansion := by
  intro m hm n hn
  refine ⟨by dsimp [error]; ring, ?_⟩
  have hlim := ((corrected_tendsto m).sub_const (corrected m n)).abs
  have hb := le_of_tendsto hlim (show ∀ᶠ N : ℕ in atTop,
      |corrected m N - corrected m n| ≤
        bernoulliMaximumValue (2*m) / ((2*m : ℕ) * (n : ℝ)^(2*m)) from
    (eventually_gt_atTop n).mono (fun N hN => corrected_difference_bound m hm hn hN))
  rw [error_eq_corrected, abs_sub_comm]
  exact hb

lemma error_succ (m n : ℕ) :
    error m n = error (m+1) n -
      bernoulliNumberValue (2*(m+1)) / ((2*(m+1) : ℕ) * (n : ℝ)^(2*(m+1))) := by
  dsimp [error, correction]
  rw [Finset.sum_range_succ]
  ring

/-- One more Bernoulli correction gives the sharper error for each displayed count. -/
theorem harmonic_controlled_remainder :
    Specs.SingleVariableAnalysis.Ch17.Harmonic.harmonicControlledRemainder := by
  intro m
  let p := 2*(m+1)
  have hp : 0 < p := by dsimp [p]; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 0 ≤ bernoulliMaximumValue p := (bernoulli_maximum_attained p).1
  refine ⟨(bernoulliMaximumValue p + |bernoulliNumberValue p|) / (p : ℝ),
    by positivity, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := (harmonic_expansion (m+1) (by omega) n hn).2
  rw [error_succ]
  calc
    _ ≤ |error (m+1) n| +
        |bernoulliNumberValue p / ((p : ℝ) * (n : ℝ)^p)| := abs_sub _ _
    _ ≤ bernoulliMaximumValue p / ((p : ℝ) * (n : ℝ)^p) +
        |bernoulliNumberValue p / ((p : ℝ) * (n : ℝ)^p)| := add_le_add hb le_rfl
    _ = _ := by
      rw [abs_div, abs_of_pos (mul_pos hp0 (pow_pos hn0 _))]
      dsimp [p]
      ring

lemma correction_two (n : ℕ) :
    correction 2 n = 1/(12*(n : ℝ)^2) - 1/(120*(n : ℝ)^4) := by
  have h2 : bernoulliNumberValue 2 = 1/6 := bernoulli_numbers.2.2.1
  have h4 : bernoulliNumberValue 4 = -1/30 := bernoulli_numbers.2.2.2
  norm_num [correction, Finset.sum_range_succ, h2, h4]
  ring

theorem harmonic_sixth_order : Specs.SingleVariableAnalysis.Ch17.Harmonic.harmonicSixthOrder := by
  obtain ⟨C, hC, hb⟩ := harmonic_controlled_remainder 2
  refine ⟨C, hC, fun n hn => ?_⟩
  have he : harmonicSum n - (seriesLog n + eulerConstant + 1/(2*(n : ℝ)) -
      1/(12*(n : ℝ)^2) + 1/(120*(n : ℝ)^4)) = error 2 n := by
    change _ = harmonicSum n - (seriesLog n + eulerConstant + 1/(2*(n : ℝ)) - correction 2 n)
    rw [correction_two]
    ring
  change |harmonicSum n - (seriesLog n + eulerConstant + 1/(2*(n : ℝ)) -
      1/(12*(n : ℝ)^2) + 1/(120*(n : ℝ)^4))| ≤ C / (n : ℝ)^6
  rw [he]
  exact hb n hn

end SingleVariableAnalysis.Harmonic
