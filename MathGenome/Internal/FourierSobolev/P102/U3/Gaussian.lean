import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform ContDiff Topology

namespace P102.U3

def gaussian : (d : ℕ) → ℝ → Euclidean d → ℝ := P102.Specs.U3.gaussianValue
def gaussianComplex : (d : ℕ) → ℝ → Euclidean d → ℂ := P102.Specs.U3.gaussianComplexValue

private theorem gaussianComplex_eq (d : ℕ) (t : ℝ) :
    gaussianComplex d t = fun x => ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
      Complex.exp (-(Real.pi / t : ℝ) * (‖x‖ : ℂ) ^ 2) := by
  funext x
  simp only [gaussianComplex, P102.Specs.U3.gaussianComplexValue,
    P102.Specs.U3.gaussianValue, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow]
  congr 2 <;> ring

 theorem gaussian_integrable (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (gaussian d t) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean d) (b := (Real.pi / t : ℝ))
    (by simpa using div_pos Real.pi_pos ht) 0 0
  simp only [zero_mul, add_zero] at h
  have hc : Integrable (gaussianComplex d t) := by
    rw [gaussianComplex_eq]
    exact h.const_mul _
  simpa [gaussianComplex, gaussian, P102.Specs.U3.gaussianComplexValue] using hc.re

 theorem gaussian_mass (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : Euclidean d, gaussian d t x) = 1 := by
  unfold gaussian P102.Specs.U3.gaussianValue
  simp_rw [show ∀ x : Euclidean d, -Real.pi * ‖x‖ ^ 2 / t =
    -(Real.pi / t) * ‖x‖ ^ 2 by intro x; ring]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm
    (div_pos Real.pi_pos ht)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [div_div_cancel₀ Real.pi_pos.ne']
  rw [← Real.rpow_add ht]
  convert Real.rpow_zero t using 1 <;> ring_nf

 theorem gaussian_fourier (d : ℕ) {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    (∫ x : Euclidean d,
      Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        gaussianComplex d t x) = (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ) := by
  rw [gaussianComplex_eq]
  simp_rw [mul_left_comm (Complex.exp _) ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ)]
  rw [integral_const_mul]
  have hf := fourier_gaussian_innerProductSpace
    (by simpa using div_pos Real.pi_pos ht : 0 < ((Real.pi / t : ℝ) : ℂ).re) ξ
  simp only [Real.fourier_eq', smul_eq_mul] at hf
  rw [hf]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hr : (Real.pi : ℂ) / (Real.pi / t) = t := by field_simp
  simp only [Complex.ofReal_div]
  rw [hr]
  have he : (d : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cpow ht.le, ← mul_assoc]
  rw [← Complex.ofReal_mul, ← Real.rpow_add ht]
  have hz : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
  rw [hz, Real.rpow_zero, Complex.ofReal_one, one_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp

 theorem gaussian_check (d : ℕ) {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    (∫ x : Euclidean d,
      Complex.exp ((2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
        gaussianComplex d t x) = (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ) := by
  have h := gaussian_fourier d ht (-ξ)
  simpa only [inner_neg_right, mul_neg, neg_mul, neg_neg, norm_neg] using h

/-- Polynomial radial weights times a real Gaussian are bounded. -/
private theorem gaussian_power_bound {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, (1 + |r|) ^ m * Real.exp (-b * r ^ 2) ≤ C := by
  have hzero : Tendsto (fun r : ℝ => |r| ^ m * Real.exp (-b * r ^ 2))
      (cocompact ℝ) (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (m : ℝ)
  let F : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toContinuousMap := ⟨_, by fun_prop⟩
      zero_at_infty' := hzero }
  obtain ⟨C, hC⟩ := F.isBounded_range.subset_closedBall (0 : ℝ)
  have hbound (r : ℝ) : |r| ^ m * Real.exp (-b * r ^ 2) ≤ C := by
    have := hC ⟨r, rfl⟩
    change dist (F r) 0 ≤ C at this
    simpa [F, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |r| ^ m * Real.exp (-b * r ^ 2))] using this
  refine ⟨2 ^ (m - 1) * (1 + max C 0), by positivity, fun r => ?_⟩
  calc
    _ ≤ (2 ^ (m - 1) * (1 + |r| ^ m)) * Real.exp (-b * r ^ 2) := by
      gcongr
      simpa only [one_pow] using add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg r) m
    _ = 2 ^ (m - 1) * (Real.exp (-b * r ^ 2) + |r| ^ m * Real.exp (-b * r ^ 2)) := by ring
    _ ≤ _ := by
      gcongr
      · exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
      · exact (hbound r).trans (le_max_left _ _)

/-- The real Gaussian is Schwartz on every finite-dimensional Euclidean space.
The chain-rule bound applies directly to the smooth quadratic exponent. -/
private def realGaussianSchwartz (d : ℕ) {b : ℝ} (hb : 0 < b) :
    SchwartzMap (Euclidean d) ℝ where
  toFun := fun x => Real.exp (-b * ‖x‖ ^ 2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' := by
    intro k n
    let q : Euclidean d → ℝ := fun x => -b * ‖x‖ ^ 2
    have hq : q.HasTemperateGrowth := by dsimp [q]; fun_prop
    obtain ⟨l, C, hC, hderiv⟩ := hq.norm_iteratedFDeriv_le_uniform n
    obtain ⟨B, hB, hbound⟩ := gaussian_power_bound hb (k + l * n)
    refine ⟨(n.factorial : ℝ) * (C + 1) ^ n * B, fun x => ?_⟩
    have hexp (i : ℕ) (_hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i Real.exp (q x)‖ ≤ Real.exp (q x) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
      exact (Real.norm_of_nonneg (Real.exp_nonneg _)).le
    have hqbound (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
        ‖iteratedFDeriv ℝ i q x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ i := by
      refine (hderiv i hin x).trans ?_
      rw [mul_pow]
      have hi' : i ≠ 0 := (lt_of_lt_of_le Nat.zero_lt_one hi).ne'
      gcongr
      · exact le_trans (by simp) (le_self_pow₀ (by linarith : 1 ≤ C + 1) hi')
      · exact le_self_pow₀ (one_le_pow₀ (by simp)) hi'
    have hcomp := norm_iteratedFDeriv_comp_le Real.contDiff_exp hq.1
      (by simp : (n : ℕ∞ω) ≤ ∞) x hexp hqbound
    calc
      _ ≤ (1 + ‖x‖) ^ k * ((n.factorial : ℝ) * Real.exp (q x) *
          ((C + 1) * (1 + ‖x‖) ^ l) ^ n) := by
        apply mul_le_mul
        · gcongr; linarith [norm_nonneg x]
        · exact hcomp
        · exact norm_nonneg _
        · positivity
      _ = (n.factorial : ℝ) * (C + 1) ^ n *
          ((1 + |‖x‖|) ^ (k + l * n) * Real.exp (-b * ‖x‖ ^ 2)) := by
        rw [abs_of_nonneg (norm_nonneg x), pow_add, pow_mul, mul_pow]
        dsimp [q]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound ‖x‖) (by positivity)

 theorem gaussian_schwartz (d : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ φ : Test d, (φ : Euclidean d → ℂ) = gaussianComplex d t := by
  let f := realGaussianSchwartz d (div_pos Real.pi_pos ht)
  let g := SchwartzMap.postcompCLM (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) f
  refine ⟨(t ^ (-(d : ℝ) / 2) : ℝ) • g, ?_⟩
  funext x
  change (t ^ (-(d : ℝ) / 2) : ℝ) • (Real.exp (-(Real.pi / t) * ‖x‖ ^ 2) : ℂ) = _
  simp only [gaussianComplex, P102.Specs.U3.gaussianComplexValue, P102.Specs.U3.gaussianValue,
    Complex.ofReal_mul, Complex.real_smul]
  congr 2
  ring

 theorem gaussian_derivatives_integrable (d : ℕ) {t : ℝ} (ht : 0 < t) (k n : ℕ) :
    Integrable (fun x : Euclidean d =>
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianComplex d t) x‖) := by
  obtain ⟨φ, hφ⟩ := gaussian_schwartz d ht
  rw [← hφ]
  exact φ.integrable_pow_mul_iteratedFDeriv volume k n

 theorem gaussian_coordinate_derivatives_integrable (d : ℕ) {t : ℝ} (ht : 0 < t)
    (n : ℕ) (β : Fin n → Fin d) :
    Integrable (fun x : Euclidean d =>
      iteratedFDeriv ℝ n (gaussianComplex d t) x (coordinateVector ∘ β)) := by
  obtain ⟨φ, hφ⟩ := gaussian_schwartz d ht
  rw [← hφ]
  simpa only [← coordinatePartial_apply] using (coordinatePartial β φ).integrable

end P102.U3
