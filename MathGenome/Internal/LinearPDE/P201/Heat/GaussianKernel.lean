import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace P201.Heat

abbrev gaussianKernel : P201Specs.Heat.gaussianKernelType :=
  P201Specs.Heat.gaussianKernel

theorem gaussianNonnegative : P201Specs.Heat.gaussianNonnegativeStatement := by
  intro n _ t ht x
  unfold P201Specs.Heat.gaussianKernel
  positivity

lemma gaussian_integrable_aux (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianKernel n t) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space n) (b := ((1 / (4 * t) : ℝ) : ℂ))
    (by simpa using (by positivity : 0 < (1 : ℝ) / (4 * t))) 0 0
  have hr := h.re.const_mul ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))
  convert hr using 1
  funext x
  simp only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  congr 2
  ring

theorem gaussianIntegrable : P201Specs.Heat.gaussianIntegrableStatement := by
  intro n _ t ht
  exact gaussian_integrable_aux n ht

lemma gaussian_mass_aux (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x, gaussianKernel n t x) = 1 := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  have he : (fun x : Space n => Real.exp (-‖x‖ ^ 2 / (4 * t))) =
      (fun x => Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2)) := by
    funext x
    congr 1
    ring
  rw [integral_const_mul, he,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < (1 : ℝ) / (4 * t))]
  simp only [P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin]
  rw [show Real.pi / (1 / (4 * t)) = 4 * Real.pi * t by field_simp]
  rw [← Real.rpow_add (by positivity : 0 < 4 * Real.pi * t)]
  convert Real.rpow_zero (4 * Real.pi * t) using 1
  ring

theorem gaussianMass : P201Specs.Heat.gaussianMassStatement := by
  intro n _ t ht
  exact gaussian_mass_aux n ht

theorem gaussianSmooth : P201Specs.Heat.gaussianSmoothStatement := by
  intro n _ z hz
  change 0 < z.2 at hz
  apply ContDiffAt.contDiffWithinAt
  unfold P201Specs.Heat.gaussianKernel
  apply ContDiffAt.mul
  · apply ContDiffAt.rpow_const_of_ne
    · fun_prop
    · positivity
  · apply ContDiffAt.exp
    apply ContDiffAt.div
    · exact ((contDiff_norm_sq ℝ).comp contDiff_fst).contDiffAt.neg
    · fun_prop
    · positivity

lemma gaussian_fderiv (n : ℕ) (t : ℝ) (x v : Space n) :
    fderiv ℝ (gaussianKernel n t) x v =
      gaussianKernel n t x * (-inner ℝ x v / (2 * t)) := by
  have hd := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg.mul_const
    (4 * t)⁻¹).exp).const_mul ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))
  change HasFDerivAt (gaussianKernel n t) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply, neg_apply,
    smul_eq_mul, innerSL_apply_apply, Pi.neg_apply]
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  ring

lemma gaussian_coordinate_deriv (n : ℕ) (t : ℝ) (x : Space n) (i : Fin n) :
    fderiv ℝ (gaussianKernel n t) x (coordinate n i) =
      gaussianKernel n t x * (-x i / (2 * t)) := by
  rw [gaussian_fderiv]
  change gaussianKernel n t x *
    (-inner ℝ x (EuclideanSpace.basisFun (Fin n) ℝ i) / (2 * t)) = _
  rw [EuclideanSpace.inner_basisFun_real]

lemma gaussian_coordinate_second_deriv (n : ℕ) (t : ℝ) (x : Space n) (i : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (gaussianKernel n t) y (coordinate n i)) x
      (coordinate n i) =
      gaussianKernel n t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  simp_rw [gaussian_coordinate_deriv]
  have hg : DifferentiableAt ℝ (gaussianKernel n t) x := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    have h : ContDiff ℝ ∞ (fun y : Space n =>
        (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) :=
      contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp)
    exact h.differentiable (by simp) x
  have hc₀ : HasFDerivAt (fun y : Space n => y i)
      (PiLp.proj 2 (fun _ : Fin n => ℝ) i) x := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt
  have hc := hc₀.neg.mul_const (2 * t)⁻¹
  have hd := hg.hasFDerivAt.mul hc
  change HasFDerivAt (fun y : Space n => gaussianKernel n t y * (-y i / (2 * t))) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    neg_apply, smul_eq_mul, PiLp.proj_apply, Pi.neg_apply]
  rw [gaussian_coordinate_deriv]
  have he : (coordinate n i) i = 1 := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply]
  rw [he]
  ring

lemma gaussian_time_deriv (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    deriv (fun s => gaussianKernel n s x) t =
      gaussianKernel n t x * (-(n : ℝ) / (2 * t) + ‖x‖ ^ 2 / (4 * t ^ 2)) := by
  have hp := ((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
    (p := -(n : ℝ) / 2) (Or.inl (by positivity : 4 * Real.pi * t ≠ 0))
  have he := ((hasDerivAt_const t (-‖x‖ ^ 2)).div
    ((hasDerivAt_id t).const_mul 4) (by positivity : 4 * t ≠ 0)).exp
  have hd := hp.mul he
  change HasDerivAt (fun s => gaussianKernel n s x) _ t at hd
  rw [hd.deriv]
  dsimp only [id, Pi.div_apply]
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [Real.rpow_sub (by positivity : 0 < 4 * Real.pi * t), Real.rpow_one]
  field_simp
  ring

theorem gaussianHeatEquation : P201Specs.Heat.gaussianHeatEquationStatement := by
  intro n hn t ht x
  rw [gaussian_time_deriv n ht]
  change _ = ∑ i : Fin n, multiPartial (gaussianKernel n t) ({i, i} : MultiIndex n) x
  have hpartial (i : Fin n) :
      multiPartial (gaussianKernel n t) ({i, i} : MultiIndex n) x =
        gaussianKernel n t x * ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
    change P102.U4.partialWord (gaussianKernel n t) (({i, i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
    have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
      rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·)) (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
    rw [hs]
    exact gaussian_coordinate_second_deriv n t x i
  simp_rw [hpartial]
  rw [← Finset.mul_sum]
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Finset.sum_sub_distrib, Finset.sum_div,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

/-- The quadratic identity used to integrate the convolution. -/
lemma gaussian_complete_square {n : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x y : Space n) :
    -‖x - y‖ ^ 2 / (4 * t) + -‖y‖ ^ 2 / (4 * s) =
      -‖x‖ ^ 2 / (4 * (t + s)) +
        -‖y - (s / (t + s)) • x‖ ^ 2 / (4 * (t * s / (t + s))) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right,
    real_inner_comm y x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

lemma gaussian_product {n : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x y : Space n) :
    gaussianKernel n t (x - y) * gaussianKernel n s y =
      gaussianKernel n (t + s) x *
        gaussianKernel n (t * s / (t + s)) (y - (s / (t + s)) • x) := by
  have ht' : 0 ≤ 4 * Real.pi * t := by positivity
  have hs' : 0 ≤ 4 * Real.pi * s := by positivity
  have hts : 0 ≤ 4 * Real.pi * (t + s) := by positivity
  have hq : 0 ≤ 4 * Real.pi * (t * s / (t + s)) := by positivity
  have hp : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
      (4 * Real.pi * s) ^ (-(n : ℝ) / 2) =
      (4 * Real.pi * (t + s)) ^ (-(n : ℝ) / 2) *
      (4 * Real.pi * (t * s / (t + s))) ^ (-(n : ℝ) / 2) := by
    rw [← Real.mul_rpow ht' hs', ← Real.mul_rpow hts hq]
    congr 1
    field_simp
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  calc
    _ = ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
        (4 * Real.pi * s) ^ (-(n : ℝ) / 2)) *
        Real.exp (-‖x - y‖ ^ 2 / (4 * t) + -‖y‖ ^ 2 / (4 * s)) := by
      rw [Real.exp_add]
      ring
    _ = _ := by
      rw [hp, gaussian_complete_square ht hs, Real.exp_add]
      ring

theorem gaussianConvolution : P201Specs.Heat.gaussianConvolutionStatement := by
  intro n _ t s ht hs x
  simp_rw [gaussian_product ht hs]
  rw [integral_const_mul, integral_sub_right_eq_self]
  rw [gaussian_mass_aux n (by positivity : 0 < t * s / (t + s)), mul_one]

end P201.Heat
