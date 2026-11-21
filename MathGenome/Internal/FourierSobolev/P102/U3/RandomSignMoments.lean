import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RandomSignMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace P102.U3.RandomSigns
open scoped BigOperators
open Finset

noncomputable section
open Classical

lemma expect_product {J : Type*} [Fintype J] (g : J → Bool → ℝ) :
    (𝔼 ω : Cube J, ∏ j, g j (ω j)) = ∏ j, (g j false + g j true) / 2 := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  have hs := Finset.sum_prod_piFinset (Finset.univ : Finset Bool) g
  simp only [Fintype.piFinset_univ] at hs
  rw [hs]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    Fintype.sum_bool, prod_div_distrib, prod_const, card_univ]
  congr 1
  exact Finset.prod_congr rfl fun i _ => add_comm _ _

lemma exp_sum_bound {J : Type*} [Fintype J] (a : J → ℝ) (t : ℝ) :
    (𝔼 ω : Cube J, Real.exp (t * ∑ j, sign (ω j) * a j)) ≤
      Real.exp (t ^ 2 * (∑ j, a j ^ 2) / 2) := by
  classical
  calc
    _ = 𝔼 ω : Cube J, ∏ j, Real.exp (t * (sign (ω j) * a j)) := by
      apply expect_congr rfl
      intro ω _
      rw [mul_sum, Real.exp_sum]
    _ = ∏ j, Real.cosh (t * a j) := by
      rw [expect_product (fun j b => Real.exp (t * (sign b * a j)))]
      apply prod_congr rfl
      intro j _
      simp [sign, Real.cosh_eq, add_comm]
    _ ≤ ∏ j, Real.exp ((t * a j) ^ 2 / 2) := by
      exact Finset.prod_le_prod₀ (fun _ _ => (Real.cosh_pos _).le)
        (fun _ _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp_rw [mul_pow, div_eq_mul_inv]
      rw [← sum_mul, ← mul_sum]

lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

lemma expect_sign_mul {J : Type*} [Fintype J] (i j : J) :
    (𝔼 ω : Cube J, sign (ω i) * sign (ω j)) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    simp_rw [← pow_two, sign_sq]
    exact Fintype.expect_const _
  · rw [ite_eq_right hij]
    let g : J → Bool → ℝ := fun k b =>
      (if k = i then sign b else 1) * (if k = j then sign b else 1)
    have h (ω : Cube J) : (∏ k, g k (ω k)) = sign (ω i) * sign (ω j) := by
      simp only [g, prod_mul_distrib, Fintype.prod_ite_eq']
    rw [← show (fun ω : Cube J => ∏ k, g k (ω k)) =
      (fun ω => sign (ω i) * sign (ω j)) from funext h, expect_product]
    apply prod_eq_zero (mem_univ i)
    simp [g, hij, sign]

lemma real_second_moment {J : Type*} [Fintype J] (a : J → ℝ) :
    (𝔼 ω : Cube J, (∑ j, sign (ω j) * a j) ^ 2) = ∑ j, a j ^ 2 := by
  classical
  simp_rw [sq, sum_mul_sum, expect_sum_comm]
  calc
    _ = ∑ i, ∑ j, (𝔼 ω : Cube J, sign (ω i) * sign (ω j)) * (a i * a j) := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      rw [expect_mul]
      apply expect_congr rfl
      intro ω _
      ring
    _ = _ := by simp [expect_sign_mul]

lemma complex_second_moment {J : Type*} [Fintype J] (a : J → ℂ) :
    (𝔼 ω : Cube J, ‖signedSum a ω‖ ^ 2) = energy a := by
  classical
  have hn (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm z)
  simp only [energy, hn, signedSum, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  rw [expect_add_distrib, real_second_moment, real_second_moment, sum_add_distrib]

lemma rpow_le_exp_bound (q : ℝ) (hq : 0 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 ≤ x → x ^ q ≤ A * Real.exp x := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  refine ⟨1 + n.factorial, by positivity, ?_⟩
  intro x hx
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hp : x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx n
    exact (div_le_iff₀ hfac).mp this |>.trans_eq (mul_comm _ _)
  by_cases h : x ≤ 1
  · have := Real.rpow_le_rpow hx h hq.le
    simp only [Real.one_rpow] at this
    nlinarith [Real.exp_pos x]
  · have hx1 : 1 ≤ x := le_of_not_ge h
    have := Real.rpow_le_rpow_of_exponent_le hx1 hn.le
    rw [Real.rpow_natCast] at this
    nlinarith

lemma real_moment_bound (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : J → ℝ),
      (∑ j, a j ^ 2) ≤ 1 →
      (𝔼 ω : Cube J, |∑ j, sign (ω j) * a j| ^ q) ≤ C := by
  obtain ⟨A, hA, hbound⟩ := rpow_le_exp_bound q hq
  refine ⟨A * (2 * Real.exp (1 / 2)), by positivity, ?_⟩
  intro J _ a ha
  have hpos := exp_sum_bound a 1
  have hneg := exp_sum_bound a (-1)
  have he : Real.exp ((∑ j, a j ^ 2) / 2) ≤ Real.exp (1 / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  simp only [one_pow, one_mul, neg_one_sq, neg_one_mul] at hpos hneg
  calc
    _ ≤ 𝔼 ω : Cube J,
        A * (Real.exp (∑ j, sign (ω j) * a j) +
          Real.exp (-(∑ j, sign (ω j) * a j))) := by
      apply expect_le_expect
      intro ω _
      apply (hbound _ (abs_nonneg _)).trans
      gcongr
      rcases le_total 0 (∑ j, sign (ω j) * a j) with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(∑ j, sign (ω j) * a j))]
      · rw [abs_of_nonpos h]; linarith [Real.exp_pos (∑ j, sign (ω j) * a j)]
    _ = A * ((𝔼 ω : Cube J, Real.exp (∑ j, sign (ω j) * a j)) +
        (𝔼 ω : Cube J, Real.exp (-(∑ j, sign (ω j) * a j)))) := by
      rw [← mul_expect, expect_add_distrib]
    _ ≤ _ := by nlinarith [hpos.trans he, hneg.trans he]

lemma signedSum_re {J : Type*} [Fintype J] (a : J → ℂ) (ω : Cube J) :
    (signedSum a ω).re = ∑ j, sign (ω j) * (a j).re := by
  simp [signedSum, Complex.re_sum, Complex.mul_re]

lemma signedSum_im {J : Type*} [Fintype J] (a : J → ℂ) (ω : Cube J) :
    (signedSum a ω).im = ∑ j, sign (ω j) * (a j).im := by
  simp [signedSum, Complex.im_sum, Complex.mul_im]

lemma complex_rpow_le (z : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ‖z‖ ^ q ≤ (2 : ℝ) ^ q * (|z.re| ^ q + |z.im| ^ q) := by
  have hn := Complex.norm_le_abs_re_add_abs_im z
  have htwo : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  have hr := Real.rpow_nonneg (abs_nonneg z.re) q
  have hi := Real.rpow_nonneg (abs_nonneg z.im) q
  rcases le_total |z.re| |z.im| with h | h
  · have hz : ‖z‖ ≤ 2 * |z.im| := by linarith
    have hp := Real.rpow_le_rpow (norm_nonneg z) hz hq
    rw [Real.mul_rpow (by norm_num) (abs_nonneg z.im)] at hp
    nlinarith
  · have hz : ‖z‖ ≤ 2 * |z.re| := by linarith
    have hp := Real.rpow_le_rpow (norm_nonneg z) hz hq
    rw [Real.mul_rpow (by norm_num) (abs_nonneg z.re)] at hp
    nlinarith

lemma normalized_upper (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : J → ℂ),
      energy a ≤ 1 → moment a q ≤ C := by
  obtain ⟨C, hC, hreal⟩ := real_moment_bound q hq
  refine ⟨(2 : ℝ) ^ q * (2 * C), by positivity, ?_⟩
  intro J _ a ha
  have hre : (∑ j, (a j).re ^ 2) ≤ 1 := by
    apply le_trans (sum_le_sum fun j _ => ?_) ha
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a j).re)
      (Complex.abs_re_le_norm (a j)) 2
  have him : (∑ j, (a j).im ^ 2) ≤ 1 := by
    apply le_trans (sum_le_sum fun j _ => ?_) ha
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a j).im)
      (Complex.abs_im_le_norm (a j)) 2
  calc
    _ ≤ 𝔼 ω : Cube J, (2 : ℝ) ^ q *
        (|(signedSum a ω).re| ^ q + |(signedSum a ω).im| ^ q) := by
      exact expect_le_expect fun ω _ => complex_rpow_le _ q hq.le
    _ = (2 : ℝ) ^ q *
        ((𝔼 ω : Cube J, |∑ j, sign (ω j) * (a j).re| ^ q) +
        (𝔼 ω : Cube J, |∑ j, sign (ω j) * (a j).im| ^ q)) := by
      rw [← mul_expect, expect_add_distrib]
      simp only [signedSum_re, signedSum_im]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hreal J (fun j => (a j).re) hre, hreal J (fun j => (a j).im) him]

/-- An elementary truncation estimate. No convexity assumption on the
exponent is needed. -/
lemma truncation_inequality (q : ℝ) (hq : 0 < q) (B : ℝ) (hB : 0 < B)
    (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 ≤ 1 / 4 + (B * (2 : ℝ) ^ q) * x ^ q + x ^ 4 / B := by
  have hpow := Real.rpow_nonneg hx q
  have htwo : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
  have hlast : 0 ≤ x ^ 4 / B := by positivity
  have hterm : 0 ≤ (B * (2 : ℝ) ^ q) * x ^ q := by positivity
  by_cases hsmall : x ≤ 1 / 2
  · have : x ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith
  · have hlarge : 1 ≤ (2 * x) ^ q := by
      exact Real.one_le_rpow (by linarith) hq.le
    rw [Real.mul_rpow (by norm_num) hx] at hlarge
    by_cases hmid : x ^ 2 ≤ B
    · nlinarith
    · have htail : x ^ 2 ≤ x ^ 4 / B := by
        apply (le_div_iff₀ hB).mpr
        nlinarith [sq_nonneg (x ^ 2 - B)]
      nlinarith

lemma normalized_lower (q : ℝ) (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (J : Type) [Fintype J] (a : J → ℂ),
      energy a = 1 → c ≤ moment a q := by
  obtain ⟨K, hK, hfour⟩ := normalized_upper 4 (by norm_num)
  let B := 4 * (K + 1)
  have hB : 0 < B := by dsimp [B]; linarith
  have hcoeff : 0 < B * (2 : ℝ) ^ q := by positivity
  refine ⟨(1 / 2) / (B * (2 : ℝ) ^ q), by positivity, ?_⟩
  intro J _ a ha
  have h4 : (𝔼 ω : Cube J, ‖signedSum a ω‖ ^ 4) ≤ K := by
    simpa only [moment, Real.rpow_ofNat] using hfour J a ha.le
  have h2 := complex_second_moment a
  rw [ha] at h2
  have hpoint := expect_le_expect (s := (univ : Finset (Cube J)))
    (fun ω _ => truncation_inequality q hq B hB _ (norm_nonneg (signedSum a ω)))
  rw [h2, expect_add_distrib, expect_add_distrib, Fintype.expect_const,
    ← mul_expect, ← expect_div] at hpoint
  change 1 ≤ 1 / 4 + (B * (2 : ℝ) ^ q) * moment a q +
    (𝔼 ω : Cube J, ‖signedSum a ω‖ ^ 4) / B at hpoint
  have ht : (𝔼 ω : Cube J, ‖signedSum a ω‖ ^ 4) / B ≤ 1 / 4 := by
    apply (div_le_iff₀ hB).mpr
    dsimp [B]
    linarith
  apply (div_le_iff₀ hcoeff).mpr
  nlinarith

lemma energy_nonneg {J : Type*} [Fintype J] (a : J → ℂ) : 0 ≤ energy a :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma signedSum_scale {J : Type*} [Fintype J] (a : J → ℂ) (r : ℝ) (ω : Cube J) :
    signedSum (fun j => (r : ℂ) * a j) ω = (r : ℂ) * signedSum a ω := by
  simp only [signedSum, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

lemma energy_scale {J : Type*} [Fintype J] (a : J → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    energy (fun j => (r : ℂ) * a j) = r ^ 2 * energy a := by
  simp only [energy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_pow, mul_sum]

lemma moment_scale {J : Type*} [Fintype J] (a : J → ℂ) (r : ℝ) (hr : 0 ≤ r) (q : ℝ) :
    moment (fun j => (r : ℂ) * a j) q = r ^ q * moment a q := by
  simp only [moment, signedSum_scale, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, Real.mul_rpow hr (norm_nonneg _), mul_expect]

lemma moment_of_energy_zero {J : Type*} [Fintype J] (a : J → ℂ)
    (ha : energy a = 0) (q : ℝ) (hq : 0 < q) : moment a q = 0 := by
  have hz : ∀ j, a j = 0 := by
    have hall := (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (univ : Finset J)) =>
      sq_nonneg ‖a j‖)).mp ha
    intro j
    have := hall j (mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
  simp [moment, signedSum, hz, Real.zero_rpow hq.ne']

/-- Homogeneity transfers normalized estimates to every coefficient family,
including the zero-energy case. -/
lemma bounds_of_normalized (q : ℝ) (hq : 0 < q) (c C : ℝ)
    (hbound : ∀ (J : Type) [Fintype J] (a : J → ℂ), energy a = 1 →
      c ≤ moment a q ∧ moment a q ≤ C) :
    ∀ (J : Type) [Fintype J] (a : J → ℂ),
      c * (energy a) ^ (q / 2) ≤ moment a q ∧
      moment a q ≤ C * (energy a) ^ (q / 2) := by
  intro J _ a
  by_cases hzero : energy a = 0
  · rw [moment_of_energy_zero a hzero q hq, hzero, Real.zero_rpow (by positivity)]
    simp
  have he : 0 < energy a := (energy_nonneg a).lt_of_ne' hzero
  let r := Real.sqrt (energy a)
  have hr : 0 < r := Real.sqrt_pos.mpr he
  have hrsq : r ^ 2 = energy a := Real.sq_sqrt he.le
  let b : J → ℂ := fun j => ((r⁻¹ : ℝ) : ℂ) * a j
  have hb : energy b = 1 := by
    dsimp only [b]
    rw [energy_scale a _ (by positivity), ← hrsq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
  have hreconstruct : (fun j => (r : ℂ) * b j) = a := by
    funext j
    dsimp only [b]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
      Complex.ofReal_one, one_mul]
  have hm : moment a q = r ^ q * moment b q := by
    rw [← hreconstruct, moment_scale b r hr.le]
  have hp : (energy a) ^ (q / 2) = r ^ q := by
    rw [← hrsq, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    congr 1
    ring
  obtain ⟨hl, hu⟩ := hbound J b hb
  rw [hm, hp]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hr.le q)]
  · nlinarith [mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hr.le q)]

/-- Random-sign moment bounds for arbitrary finite complex coefficient families. -/
theorem randomSignMoments : Specs.P102.U3.RandomSignMoments := by
  intro q hq
  obtain ⟨C, hC, hu⟩ := normalized_upper q hq
  obtain ⟨c, hc, hl⟩ := normalized_lower q hq
  refine ⟨min c C, C, lt_min hc hC, min_le_right _ _, ?_⟩
  apply bounds_of_normalized q hq
  intro J _ a ha
  exact ⟨(min_le_left c C).trans (hl J a ha), hu J a ha.le⟩

end
end P102.U3.RandomSigns
