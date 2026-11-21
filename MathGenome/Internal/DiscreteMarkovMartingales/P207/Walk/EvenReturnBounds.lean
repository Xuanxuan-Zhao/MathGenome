import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.EvenReturnBounds
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.LatticeFourier
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.LatticeLocalBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace P207.Walk.EvenReturnBounds

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A scalar even power is dominated by Gaussians at both signs. -/
theorem even_pow_le_exp_pair (x : ℝ) (n : ℕ) :
    x ^ (2 * n) ≤ Real.exp ((2 * n : ℕ) * (x - 1)) +
      Real.exp ((2 * n : ℕ) * (-x - 1)) := by
  have hpow (y : ℝ) (hy : 0 ≤ y) :
      y ^ (2 * n) ≤ Real.exp ((2 * n : ℕ) * (y - 1)) := by
    calc
      _ ≤ (Real.exp (y - 1)) ^ (2 * n) :=
        pow_le_pow_left₀ hy (by linarith [Real.add_one_le_exp (y - 1)]) _
      _ = _ := (Real.exp_nat_mul _ _).symm
  by_cases hx : 0 ≤ x
  · exact (hpow x hx).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
  · have hh := hpow (-x) (by linarith)
    rw [Even.neg_pow (even_two_mul n)] at hh
    exact hh.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

/-- The Fourier integrand is continuous on the compact torus. -/
theorem continuous_phi (d : ℕ) : Continuous (phi (d := d)) := by
  unfold phi
  exact continuous_const.mul (continuous_finsetSum _ fun j _ =>
    Real.Angle.continuous_cos.comp (continuous_apply j))

theorem integrable_phi_pow (d n : ℕ) :
    Integrable (fun t : Torus d => phi t ^ n) (torusMeasure d) :=
  ((continuous_phi d).pow n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A one-dimensional Laplace integral for the cosine defect. -/
def cosineIntegral (k : ℝ) : ℝ :=
  ∫ t : AddCircle (2 * Real.pi), Real.exp (-k * (1 - Real.Angle.cos t))
    ∂AddCircle.haarAddCircle

/-- Global quadratic comparison on a fundamental interval gives a Gaussian
bound without a separate estimate away from the two peaks. -/
theorem cosineIntegral_le_gaussian {k : ℝ} (hk : 0 < k) :
    cosineIntegral k ≤ (2 * Real.pi)⁻¹ *
      Real.sqrt (Real.pi / (k * (2 / Real.pi ^ 2))) := by
  let f : AddCircle (2 * Real.pi) → ℝ :=
    fun t => Real.exp (-k * (1 - Real.Angle.cos t))
  let g : ℝ → ℝ := fun t => Real.exp (-(k * (2 / Real.pi ^ 2)) * t ^ 2)
  have hg : Integrable g := integrable_exp_neg_mul_sq (by positivity)
  have hc : Continuous (fun t : ℝ => f t) := by
    change Continuous (fun t : ℝ => Real.exp (-k * (1 - Real.cos t)))
    fun_prop
  have hf := hc.integrableOn_Ioc (μ := volume) (a := -Real.pi) (b := Real.pi)
  have hbound : (∫ t in Ioc (-Real.pi) Real.pi, f t) ≤
      ∫ t in Ioc (-Real.pi) Real.pi, g t := by
    apply setIntegral_mono_on hf hg.integrableOn measurableSet_Ioc
    intro t ht
    apply Real.exp_le_exp.mpr
    have habs : |t| ≤ Real.pi := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    change -k * (1 - Real.Angle.cos (t : AddCircle (2 * Real.pi))) ≤ _
    rw [LatticeLocalBounds.cos_angular_coe]
    nlinarith
  calc
    cosineIntegral k = (2 * Real.pi)⁻¹ * ∫ t in Ioc (-Real.pi) Real.pi, f t := by
      unfold cosineIntegral
      rw [AddCircle.integral_haarAddCircle,
        ← AddCircle.integral_preimage (2 * Real.pi) (-Real.pi)]
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
      rfl
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t in Ioc (-Real.pi) Real.pi, g t :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ * ∫ t, g t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hg (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
    _ = _ := by rw [show (∫ t, g t) = _ from integral_gaussian _]

/-- The scalar bound with the dependence on the scale made explicit. -/
theorem cosineIntegral_scale_bound {a N : ℝ} (ha : 0 < a) (hN : 0 < N) :
    cosineIntegral (a * N) ≤
      ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / (a * (2 / Real.pi ^ 2)))) *
        (Real.sqrt N)⁻¹ := by
  have h := cosineIntegral_le_gaussian (mul_pos ha hN)
  have heq : Real.pi / (a * N * (2 / Real.pi ^ 2)) =
      (Real.pi / (a * (2 / Real.pi ^ 2))) / N := by ring
  rw [heq, Real.sqrt_div (by positivity), div_eq_mul_inv, ← mul_assoc] at h
  exact h

/-- The translated cosine defect has exactly the same Haar integral. -/
theorem cosineIntegral_neg (k : ℝ) :
    (∫ t : AddCircle (2 * Real.pi), Real.exp (-k * (1 + Real.Angle.cos t))
      ∂AddCircle.haarAddCircle) = cosineIntegral k := by
  have h := integral_add_right_eq_self
    (μ := @AddCircle.haarAddCircle (2 * Real.pi) ⟨by positivity⟩)
    (fun t : AddCircle (2 * Real.pi) => Real.exp (-k * (1 - Real.Angle.cos t)))
    (Real.pi : AddCircle (2 * Real.pi))
  unfold cosineIntegral
  convert h using 1
  congr 1
  funext t
  have hc : Real.Angle.cos (t + (Real.pi : AddCircle (2 * Real.pi))) =
      -Real.Angle.cos t := Real.Angle.cos_add_pi t
  rw [hc, sub_neg_eq_add]

/-- Factoring the exponential of the cosine average into scalar factors. -/
theorem exp_phi_factorization {d : ℕ} [NeZero d] (k : ℝ) (t : Torus d) :
    Real.exp (k * (phi t - 1)) =
      ∏ j : Fin d, Real.exp (-(k / d) * (1 - Real.Angle.cos (t j))) := by
  rw [← Real.exp_sum]
  congr 1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  unfold phi
  field_simp
  ring

/-- The corresponding factorization at the other sign. -/
theorem exp_neg_phi_factorization {d : ℕ} [NeZero d] (k : ℝ) (t : Torus d) :
    Real.exp (k * (-phi t - 1)) =
      ∏ j : Fin d, Real.exp (-(k / d) * (1 + Real.Angle.cos (t j))) := by
  rw [← Real.exp_sum]
  congr 1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  unfold phi
  field_simp
  ring

/-- Integrating separated functions over the actual product Haar measure. -/
theorem integral_torus_prod (d : ℕ) (f : AddCircle (2 * Real.pi) → ℝ) :
    (∫ t : Torus d, ∏ j : Fin d, f (t j) ∂torusMeasure d) =
      (∫ t, f t ∂AddCircle.haarAddCircle) ^ d := by
  unfold torusMeasure
  rw [integral_fintype_prod_eq_prod]
  simp

/-- The full even return integral is bounded by two product Laplace integrals. -/
theorem return_le_cosineIntegral (d : ℕ) [NeZero d] (n : ℕ) :
    (returnProbability d (2 * n)).toReal ≤
      2 * cosineIntegral ((2 * n : ℕ) / (d : ℝ)) ^ d := by
  have hp : Continuous (fun t : Torus d => Real.exp ((2 * n : ℕ) * (phi t - 1))) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_phi d).sub continuous_const))
  have hm : Continuous (fun t : Torus d => Real.exp ((2 * n : ℕ) * (-phi t - 1))) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_phi d).neg.sub continuous_const))
  have hip := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := torusMeasure d)
  have him := hm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := torusMeasure d)
  rw [LatticeFourier.fourier_return]
  calc
    _ ≤ ∫ t : Torus d, (Real.exp ((2 * n : ℕ) * (phi t - 1)) +
        Real.exp ((2 * n : ℕ) * (-phi t - 1))) ∂torusMeasure d := by
      exact integral_mono (integrable_phi_pow d _) (hip.add him)
        (fun t => even_pow_le_exp_pair (phi t) n)
    _ = _ := by
      rw [integral_add hip him]
      simp_rw [exp_phi_factorization, exp_neg_phi_factorization]
      rw [integral_torus_prod d (fun t => Real.exp (-((2 * n : ℕ) / (d : ℝ)) *
          (1 - Real.Angle.cos t))),
        integral_torus_prod d (fun t => Real.exp (-((2 * n : ℕ) / (d : ℝ)) *
          (1 + Real.Angle.cos t)))]
      simp_rw [cosineIntegral_neg]
      change cosineIntegral _ ^ d + cosineIntegral _ ^ d = _
      ring

/-- Express the real exponent in terms of the reciprocal square root. -/
theorem rpow_dimension (N : ℝ) (hN : 0 < N) (d : ℕ) :
    N ^ (-(d : ℝ) / 2) = (Real.sqrt N)⁻¹ ^ d := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hN.le]
  congr 1
  ring

/-- The upper estimate, with a finite constant depending only on `d`. -/
theorem upper_bound (d : ℕ) [NeZero d] : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → (returnProbability d (2 * n)).toReal ≤
      C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
  let a : ℝ := 2 / d
  let A : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / (a * (2 / Real.pi ^ 2)))
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * A ^ d, by positivity, ?_⟩
  intro n hn
  have hN : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hb := cosineIntegral_scale_bound ha hN
  have heq : (2 * n : ℕ) / (d : ℝ) = a * (n : ℝ) := by
    dsimp [a]
    push_cast
    ring
  calc
    _ ≤ 2 * cosineIntegral ((2 * n : ℕ) / (d : ℝ)) ^ d := return_le_cosineIntegral d n
    _ ≤ 2 * (A * (Real.sqrt (n : ℝ))⁻¹) ^ d := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (integral_nonneg fun _ => Real.exp_nonneg _) hb _
    _ = _ := by rw [mul_pow, rpow_dimension _ hN]; ring

/-- The norm of an angle is the absolute value of its principal representative. -/
theorem angle_norm_eq_toReal (t : Real.Angle) : ‖t‖ = |t.toReal| := by
  conv_lhs => rw [← Real.Angle.coe_toReal t]
  apply (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr
  simpa only [abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_div_cancel_left₀
    Real.pi (by norm_num : (2 : ℝ) ≠ 0)] using Real.Angle.abs_toReal_le_pi t

/-- Scalar quadratic lower estimate on a circle ball. -/
theorem cos_lower_on_ball {r : ℝ} (_hr : 0 ≤ r)
    (t : AddCircle (2 * Real.pi)) (ht : t ∈ Metric.closedBall 0 r) :
    1 - r ^ 2 / 2 ≤ Real.Angle.cos t := by
  have hn0 : ‖t‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  have hn : |Real.Angle.toReal t| ≤ r := (angle_norm_eq_toReal t).symm.le.trans hn0
  have hs : (Real.Angle.toReal t) ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hn 2
  rw [← Real.Angle.cos_toReal t]
  linarith [Real.one_sub_sq_div_two_le_cos (x := Real.Angle.toReal t)]

/-- Averaging the coordinate estimates preserves their common lower bound. -/
theorem phi_lower_on_box {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 ≤ r)
    (t : Torus d) (ht : ∀ j, t j ∈ Metric.closedBall 0 r) :
    1 - r ^ 2 / 2 ≤ phi t := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  calc
    _ = (d : ℝ)⁻¹ * ∑ _j : Fin d, (1 - r ^ 2 / 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => cos_lower_on_ball hr (t j) (ht j))) (by positivity)

/-- Indicator of a small circle ball, used to measure the coordinate box. -/
def window (r : ℝ) : AddCircle (2 * Real.pi) → ℝ :=
  (Metric.closedBall 0 r).indicator (fun _ => 1)

theorem integrable_window (r : ℝ) :
    Integrable (window r) AddCircle.haarAddCircle :=
  (integrable_const 1).indicator measurableSet_closedBall

/-- The scalar ball has its actual normalized Haar length. -/
theorem integral_window {r : ℝ} (hr : 0 ≤ r) (hrpi : r ≤ Real.pi) :
    (∫ t, window r t ∂AddCircle.haarAddCircle) =
      (2 * Real.pi)⁻¹ * (2 * r) := by
  unfold window
  rw [AddCircle.integral_haarAddCircle, integral_indicator_const 1 measurableSet_closedBall,
    measureReal_def, AddCircle.volume_closedBall,
    min_eq_right (by linarith : 2 * r ≤ 2 * Real.pi),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, mul_one]

/-- Bernoulli's inequality at the scale needed for all positive times. -/
theorem bernoulli_half (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ≤ (1 - (4 * (n : ℝ))⁻¹) ^ (2 * n) := by
  have hN : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hi : (4 * (n : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hb := one_add_mul_le_pow (a := -(4 * (n : ℝ))⁻¹) (by linarith :
    -2 ≤ -(4 * (n : ℝ))⁻¹) (2 * n)
  have heq : (1 : ℝ) + (2 * n : ℕ) * -(4 * (n : ℝ))⁻¹ = 1 / 2 := by
    push_cast
    field_simp
    ring
  rw [heq] at hb
  simpa only [sub_eq_add_neg] using hb

/-- Pointwise lower bound on the box at the inverse-square-root scale. -/
theorem window_product_lower (d : ℕ) [NeZero d] (n : ℕ) (hn : 1 ≤ n)
    (t : Torus d) :
    (1 / 2 : ℝ) * ∏ j : Fin d, window ((2 * Real.sqrt (n : ℝ))⁻¹) (t j) ≤
      phi t ^ (2 * n) := by
  let r : ℝ := (2 * Real.sqrt (n : ℝ))⁻¹
  have hN : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = (4 * (n : ℝ))⁻¹ := by
    dsimp [r]
    rw [inv_pow, mul_pow, Real.sq_sqrt hN.le]
    norm_num
  by_cases ht : ∀ j, t j ∈ Metric.closedBall 0 r
  · have hp : (∏ j : Fin d, window r (t j)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      exact indicator_of_mem (ht j) _
    change 1 / 2 * ∏ j : Fin d, window r (t j) ≤ _
    rw [hp, mul_one]
    have hphi := phi_lower_on_box hr.le t ht
    have hbase : 0 ≤ 1 - (4 * (n : ℝ))⁻¹ := by
      have hh : 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have := inv_le_one_of_one_le₀ (show 1 ≤ 4 * (n : ℝ) by linarith)
      linarith
    calc
      _ ≤ (1 - (4 * (n : ℝ))⁻¹) ^ (2 * n) := bernoulli_half n hn
      _ ≤ _ := pow_le_pow_left₀ hbase (by rw [← hrsq]; nlinarith [sq_nonneg r]) _
  · push Not at ht
    obtain ⟨j, hj⟩ := ht
    have hp : (∏ j : Fin d, window r (t j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _)
    change 1 / 2 * ∏ j : Fin d, window r (t j) ≤ _
    rw [hp, mul_zero]
    exact Even.pow_nonneg (even_two_mul n) _

/-- The lower estimate, including every `n ≥ 1`. -/
theorem lower_bound (d : ℕ) [NeZero d] : ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (-(d : ℝ) / 2) ≤
      (returnProbability d (2 * n)).toReal := by
  refine ⟨(1 / 2 : ℝ) * ((2 * Real.pi)⁻¹) ^ d, by positivity, ?_⟩
  intro n hn
  let r : ℝ := (2 * Real.sqrt (n : ℝ))⁻¹
  have hN : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hN1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hN1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrpi : r ≤ Real.pi := by
    have hh : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith [Real.one_le_pi_div_two]
  have hi : Integrable (fun t : Torus d => (1 / 2 : ℝ) * ∏ j, window r (t j))
      (torusMeasure d) :=
    (Integrable.fintype_prod (μ := fun _ : Fin d => AddCircle.haarAddCircle)
      (fun _ => integrable_window r)).const_mul (1 / 2)
  have hbound : (∫ t : Torus d, (1 / 2 : ℝ) * ∏ j, window r (t j) ∂torusMeasure d) ≤
      (returnProbability d (2 * n)).toReal := by
    rw [LatticeFourier.fourier_return]
    exact integral_mono hi (integrable_phi_pow d _)
      (fun t => window_product_lower d n hn t)
  calc
    _ = ∫ t : Torus d, (1 / 2 : ℝ) * ∏ j, window r (t j) ∂torusMeasure d := by
      rw [integral_const_mul]
      unfold torusMeasure
      rw [integral_fintype_prod_eq_prod]
      simp_rw [integral_window hr.le hrpi]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [rpow_dimension _ hN]
      have heq : (2 * Real.pi)⁻¹ * (2 * r) =
          (2 * Real.pi)⁻¹ * (Real.sqrt (n : ℝ))⁻¹ := by
        dsimp [r]
        field_simp
      rw [heq, mul_pow]
      ring
    _ ≤ _ := hbound

/-- The two estimates for the original transition powers. -/
theorem even_return_bounds : EvenReturnBoundsSpec.even_return_bounds := by
  intro d _
  obtain ⟨c, hc, hlo⟩ := lower_bound d
  obtain ⟨C, _hC, hhi⟩ := upper_bound d
  refine ⟨c, max c C, hc, le_max_left _ _, ?_⟩
  intro n hn
  refine ⟨hlo n hn, (hhi n hn).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

end
end P207.Walk.EvenReturnBounds
