import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201.Elliptic.HolderCancellation
import MathGenome.Internal.FourierSobolev.P102.U3.RieszL2Multiplier
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.HalfSpaceLift
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Convolution Pointwise FourierTransform

namespace P201.Elliptic.HalfSpaceLift
open P201Specs.Elliptic.HalfSpaceLift

lemma profile_pos (m : ℕ) (z : Space m) : 0 < poissonProfile m z := by
  unfold poissonProfile
  exact Real.rpow_pos_of_pos (by positivity) _

lemma profile_contDiff (m : ℕ) : ContDiff ℝ ⊤ (poissonProfile m) := by
  unfold poissonProfile
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    (fun z => ne_of_gt (by positivity))

lemma profile_integrable (m : ℕ) : Integrable (poissonProfile m) volume := by
  apply integrable_rpow_neg_one_add_norm_sq
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  linarith

lemma profile_integral_pos (m : ℕ) : 0 < ∫ z, poissonProfile m z := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (profile_contDiff m).continuous (profile_integrable m)
    (fun z => (profile_pos m z).le) (profile_pos m 0).ne'

lemma constant_pos (m : ℕ) : 0 < poissonConstant m := by
  exact inv_pos.mpr (profile_integral_pos m)

lemma kernel_pos (m : ℕ) {t : ℝ} (ht : 0 < t) (z : Space m) :
    0 < poissonKernel m t z := by
  unfold poissonKernel
  exact mul_pos (mul_pos (constant_pos m) ht)
    (Real.rpow_pos_of_pos (by positivity) _)

lemma kernel_one (m : ℕ) (z : Space m) :
    poissonKernel m 1 z = poissonConstant m * poissonProfile m z := by
  simp [poissonKernel, poissonProfile]

lemma kernel_even (m : ℕ) (t : ℝ) (z : Space m) :
    poissonKernel m t (-z) = poissonKernel m t z := by
  simp [poissonKernel]

lemma kernel_scale (m : ℕ) {t : ℝ} (ht : 0 < t) (z : Space m) :
    poissonKernel m t (t • z) = (t ^ m)⁻¹ * poissonKernel m 1 z := by
  have hb : t ^ 2 + ‖t • z‖ ^ 2 = t ^ 2 * (1 + ‖z‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring
  have hp : (t ^ 2 : ℝ) ^ (-((m : ℝ) + 1) / 2) = t ^ (-((m : ℝ) + 1)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have he : t * t ^ (-((m : ℝ) + 1)) = (t ^ m)⁻¹ := by
    rw [show -((m : ℝ) + 1) = -(m : ℝ) - 1 by ring,
      Real.rpow_sub ht, Real.rpow_one, mul_div_cancel₀ _ ht.ne',
      Real.rpow_neg ht.le, Real.rpow_natCast]
  simp only [poissonKernel, hb, Real.mul_rpow (sq_nonneg t) (by positivity : 0 ≤ 1 + ‖z‖ ^ 2), hp,
    one_pow, mul_one]
  calc
    poissonConstant m * t * (t ^ (-((m : ℝ) + 1)) *
        (1 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1) / 2)) =
      poissonConstant m * (t * t ^ (-((m : ℝ) + 1))) *
        (1 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1) / 2) := by ring
    _ = _ := by rw [he]; ring

lemma kernel_scaling (m : ℕ) {t : ℝ} (ht : 0 < t) (z : Space m) :
    poissonKernel m t z = (t ^ m)⁻¹ * poissonKernel m 1 (t⁻¹ • z) := by
  simpa only [smul_inv_smul₀ ht.ne'] using kernel_scale m ht (t⁻¹ • z)

lemma kernel_integrable (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (poissonKernel m t) volume := by
  have h := ((profile_integrable m).const_mul (poissonConstant m)).comp_smul (inv_ne_zero ht.ne')
  have h' := h.const_mul (t ^ m)⁻¹
  exact h'.congr (.of_forall fun z => by
    simpa only [kernel_one] using (kernel_scaling m ht z).symm)

lemma kernel_mass (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ z, poissonKernel m t z) = 1 := by
  simp_rw [kernel_scaling m ht]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg (volume : Measure (Space m))
    (hR := inv_nonneg.mpr ht.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv, smul_eq_mul]
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ ht.ne')]
  simp_rw [kernel_one]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (profile_integral_pos m).ne'

lemma profile_laplace (m : ℕ) (x : Space m) :
    (∫ t : ℝ in Ioi 0, t ^ (((m : ℝ) + 1) / 2 - 1) *
      Real.exp (-((1 + ‖x‖ ^ 2) * t))) =
      Real.Gamma (((m : ℝ) + 1) / 2) * poissonProfile m x := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity)]
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  simp only [poissonProfile, neg_div]
  ring

lemma profile_laplace_integrable (m : ℕ) (x : Space m) :
    IntegrableOn (fun t : ℝ => t ^ (((m : ℝ) + 1) / 2 - 1) *
      Real.exp (-((1 + ‖x‖ ^ 2) * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := ((m : ℝ) + 1) / 2 - 1) (b := 1 + ‖x‖ ^ 2)
    (by have := Nat.cast_nonneg (α := ℝ) m; linarith) (by norm_num) (by positivity)
  simpa only [Real.rpow_one, neg_mul] using h

lemma profile_integral (m : ℕ) :
    (∫ x, poissonProfile m x) =
      Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2) := by
  let q : ℝ := ((m : ℝ) + 1) / 2
  let F : Space m → ℝ → ℝ := fun x t => t ^ (q - 1) * Real.exp (-((1 + ‖x‖ ^ 2) * t))
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    apply (integrable_prod_iff (by dsimp [F]; fun_prop)).mpr
    constructor
    · exact Filter.Eventually.of_forall (profile_laplace_integrable m)
    · dsimp only [Function.uncurry]
      have he : (fun x => ∫ t in Ioi (0 : ℝ), ‖F x t‖) =
          fun x => Real.Gamma q * poissonProfile m x := by
        funext x
        calc
          _ = ∫ t in Ioi (0 : ℝ), F x t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
          _ = _ := profile_laplace m x
      rw [he]
      exact (P201.Elliptic.HalfSpaceLift.profile_integrable m).const_mul _
  have hs := integral_integral_swap hF
  have hleft : (∫ x, ∫ t in Ioi (0 : ℝ), F x t) =
      Real.Gamma q * ∫ x, poissonProfile m x := by
    simp_rw [show ∀ x, (∫ t in Ioi (0 : ℝ), F x t) =
      Real.Gamma q * poissonProfile m x from profile_laplace m]
    rw [integral_const_mul]
  have hinner (t : ℝ) (ht : 0 < t) :
      (∫ x, F x t) = Real.pi ^ ((m : ℝ) / 2) *
        (t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-t)) := by
    have he (x : Space m) : F x t =
        (t ^ (q - 1) * Real.exp (-t)) * Real.exp (-t * ‖x‖ ^ 2) := by
      dsimp [F]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp_rw [he]
    rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [Real.div_rpow Real.pi_pos.le ht.le, div_eq_mul_inv,
      ← Real.rpow_neg ht.le]
    calc
      _ = Real.pi ^ ((m : ℝ) / 2) *
          (t ^ (q - 1) * t ^ (-((m : ℝ) / 2))) * Real.exp (-t) := by ring
      _ = _ := by
        rw [← Real.rpow_add ht]
        have hq : q - 1 + -((m : ℝ) / 2) = (1 / 2 : ℝ) - 1 := by
          dsimp [q]
          ring
        rw [hq]
        ring
  have hright : (∫ t in Ioi (0 : ℝ), ∫ x, F x t) =
      Real.pi ^ q := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Real.pi ^ ((m : ℝ) / 2) *
          (t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-t)) := by
        exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hinner t ht)
      _ = Real.pi ^ ((m : ℝ) / 2) * Real.Gamma (1 / 2) := by
        rw [integral_const_mul]
        congr 1
        simpa using Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 2 : ℝ))
          (r := (1 : ℝ)) (by norm_num) (by norm_num)
      _ = Real.pi ^ q := by
        rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
        congr 1
        dsimp [q]
        ring
  have hG : Real.Gamma q ≠ 0 := (Real.Gamma_pos_of_pos (by dsimp [q]; positivity)).ne'
  apply (eq_div_iff hG).mpr
  calc
    _ = Real.Gamma q * ∫ x, poissonProfile m x := mul_comm _ _
    _ = _ := hleft.symm.trans (hs.trans hright)

lemma constant_eq (m : ℕ) : poissonConstant m = P102.Specs.U3.Riesz.constantValue m := by
  unfold poissonConstant P102.Specs.U3.Riesz.constantValue
  rw [profile_integral, inv_div]

theorem rieszNormalization : P201Specs.Elliptic.HalfSpaceLift.rieszNormalizationStatement := by
  intro m hm
  refine ⟨constant_eq m, ?_⟩
  intro i z
  rw [constant_eq]
  rfl

theorem kernelBasic : P201Specs.Elliptic.HalfSpaceLift.kernelBasicStatement := by
  intro m hm
  refine ⟨constant_pos m, fun t ht => ?_⟩
  exact ⟨kernel_integrable m ht, kernel_mass m ht, kernel_pos m ht, kernel_scaling m ht⟩

@[simp] lemma horizontal_point {m : ℕ} (x : Space m) (t : ℝ) :
    horizontal (point x t) = x := by
  ext i
  simp [horizontal, point]

@[simp] lemma height_point {m : ℕ} (x : Space m) (t : ℝ) :
    height (point x t) = t := by
  simp [height, point]

lemma lift_positive {m : ℕ} (g : Space m → ℝ) (x : Space m) {t : ℝ} (ht : 0 < t) :
    harmonicLift g (point x t) = poissonIntegral g t x := by
  simp [harmonicLift, ht]

lemma lift_boundary {m : ℕ} (g : Space m → ℝ) (x : Space m) :
    harmonicLift g (point x 0) = g x := by
  simp [harmonicLift]

/-- Integrability of the fractional moment at height one. It is dominated
by a Japanese-bracket profile of exponent m+1-α, strictly above m. -/
lemma kernel_one_moment_integrable (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Integrable (fun z => ‖z‖ ^ α * poissonKernel m 1 z) volume := by
  have hJ : Integrable (fun z : Space m =>
      (1 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1 - α) / 2)) volume := by
    apply integrable_rpow_neg_one_add_norm_sq
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  apply (hJ.const_mul (poissonConstant m)).mono' (by unfold poissonKernel; fun_prop)
  filter_upwards [] with z
  have hb : ‖z‖ ^ α ≤ (1 + ‖z‖ ^ 2) ^ (α / 2) := by
    calc
      ‖z‖ ^ α = (‖z‖ ^ (2 : ℕ)) ^ (α / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (kernel_pos m zero_lt_one z).le), kernel_one]
  calc
    _ ≤ (1 + ‖z‖ ^ 2) ^ (α / 2) *
        (poissonConstant m * poissonProfile m z) :=
      mul_le_mul_of_nonneg_right hb (by positivity [constant_pos m, profile_pos m z])
    _ = _ := by
      unfold poissonProfile
      rw [mul_left_comm, ← Real.rpow_add (by positivity : 0 < 1 + ‖z‖ ^ 2)]
      congr 2
      ring

lemma kernel_moment_scaling (m : ℕ) (α : ℝ) {t : ℝ} (ht : 0 < t) (z : Space m) :
    ‖z‖ ^ α * poissonKernel m t z =
      (t ^ α * (t ^ m)⁻¹) *
        (‖t⁻¹ • z‖ ^ α * poissonKernel m 1 (t⁻¹ • z)) := by
  rw [kernel_scaling m ht, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht,
    Real.mul_rpow (inv_nonneg.mpr ht.le) (norm_nonneg _), Real.inv_rpow ht.le]
  have he : t ^ α * (t ^ α)⁻¹ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos ht α).ne'
  calc
    _ = (t ^ m)⁻¹ * (‖z‖ ^ α * poissonKernel m 1 (t⁻¹ • z)) := by ring
    _ = (t ^ α * (t ^ α)⁻¹) *
      ((t ^ m)⁻¹ * (‖z‖ ^ α * poissonKernel m 1 (t⁻¹ • z))) := by rw [he, one_mul]
    _ = _ := by ring

lemma kernel_moment_integrable (m : ℕ) {α t : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (ht : 0 < t) : Integrable (fun z => ‖z‖ ^ α * poissonKernel m t z) volume := by
  have h := (kernel_one_moment_integrable m hα hα1).comp_smul (inv_ne_zero ht.ne')
  exact (h.const_mul (t ^ α * (t ^ m)⁻¹)).congr
    (.of_forall fun z => (kernel_moment_scaling m α ht z).symm)

lemma kernel_moment (m : ℕ) (α : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ z, ‖z‖ ^ α * poissonKernel m t z) =
      (∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * t ^ α := by
  simp_rw [kernel_moment_scaling m α ht]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Space m)) (fun z : Space m => ‖z‖ ^ α * poissonKernel m 1 z)
    (t⁻¹) (hR := inv_nonneg.mpr ht.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv, smul_eq_mul]
  have hn : t ^ m ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp

theorem kernelMoment : P201Specs.Elliptic.HalfSpaceLift.kernelMomentStatement := by
  intro m hm α hα hα1
  refine ⟨∫ z, ‖z‖ ^ α * poissonKernel m 1 z, ?_, fun t ht => ?_⟩
  · exact integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (kernel_pos m zero_lt_one z).le)
  · exact ⟨kernel_moment_integrable m hα hα1 ht, kernel_moment m α ht⟩

lemma poisson_integrand_integrable {m : ℕ} {b : Space m → ℝ}
    (hb : Continuous b) {M : ℝ} (hM : ∀ x, ‖b x‖ ≤ M) {t : ℝ} (ht : 0 < t)
    (x : Space m) : Integrable (fun z => poissonKernel m t z * b (x - z)) volume := by
  apply ((kernel_integrable m ht).const_mul M).mono'
    ((kernel_integrable m ht).aestronglyMeasurable.mul
      (hb.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖poissonKernel m t z * b (x - z)‖ ≤ M * poissonKernel m t z
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (kernel_pos m ht z)]
  calc
    _ ≤ poissonKernel m t z * M := mul_le_mul_of_nonneg_left (hM _) (kernel_pos m ht z).le
    _ = _ := mul_comm _ _

lemma poisson_sup_bound {m : ℕ} (b : Space m → ℝ) {M : ℝ}
    (hM : ∀ x, ‖b x‖ ≤ M) {t : ℝ} (ht : 0 < t) (x : Space m) :
    ‖poissonIntegral b t x‖ ≤ M := by
  calc
    _ ≤ ∫ z, M * poissonKernel m t z := by
      apply norm_integral_le_of_norm_le ((kernel_integrable m ht).const_mul M)
      filter_upwards [] with z
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (kernel_pos m ht z)]
      simpa only [mul_comm M] using
        mul_le_mul_of_nonneg_left (hM (x - z)) (kernel_pos m ht z).le
    _ = M := by rw [integral_const_mul, kernel_mass m ht, mul_one]

lemma poisson_spatial_holder {m : ℕ} {α : ℝ} {b : Space m → ℝ} {M H : ℝ}
    (hb : Continuous b) (hM : ∀ x, ‖b x‖ ≤ M)
    (hH : ∀ x y, ‖b x - b y‖ ≤ H * dist x y ^ α)
    {t : ℝ} (ht : 0 < t) (x y : Space m) :
    ‖poissonIntegral b t x - poissonIntegral b t y‖ ≤ H * dist x y ^ α := by
  have hi := poisson_integrand_integrable hb hM ht
  have he : poissonIntegral b t x - poissonIntegral b t y =
      ∫ z, poissonKernel m t z * (b (x - z) - b (y - z)) := by
    unfold poissonIntegral
    rw [← integral_sub (hi x) (hi y)]
    congr 1
    funext z
    ring
  rw [he]
  calc
    _ ≤ ∫ z, (H * dist x y ^ α) * poissonKernel m t z := by
      apply norm_integral_le_of_norm_le ((kernel_integrable m ht).const_mul _)
      filter_upwards [] with z
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (kernel_pos m ht z)]
      have hh : ‖b (x - z) - b (y - z)‖ ≤ H * dist x y ^ α := by
        simpa only [dist_sub_right] using hH (x - z) (y - z)
      simpa only [mul_comm (H * dist x y ^ α)] using
        mul_le_mul_of_nonneg_left hh (kernel_pos m ht z).le
    _ = _ := by rw [integral_const_mul, kernel_mass m ht, mul_one]

lemma poisson_approximation_bound {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hb : Continuous b) (hM : ∀ x, ‖b x‖ ≤ M)
    (hH : ∀ x y, ‖b x - b y‖ ≤ H * dist x y ^ α)
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    ‖poissonIntegral b t x - b x‖ ≤
      (∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * t ^ α := by
  have hi := poisson_integrand_integrable hb hM ht x
  have hc := (kernel_integrable m ht).mul_const (b x)
  have he : poissonIntegral b t x - b x =
      ∫ z, poissonKernel m t z * (b (x - z) - b x) := by
    calc
      _ = poissonIntegral b t x - ∫ z, poissonKernel m t z * b x := by
        rw [integral_mul_const, kernel_mass m ht, one_mul]
      _ = _ := by
        unfold poissonIntegral
        rw [← integral_sub hi hc]
        congr 1
        funext z
        ring
  rw [he]
  calc
    _ ≤ ∫ z, H * (‖z‖ ^ α * poissonKernel m t z) := by
      apply norm_integral_le_of_norm_le ((kernel_moment_integrable m hα hα1 ht).const_mul H)
      filter_upwards [] with z
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (kernel_pos m ht z)]
      have hh : ‖b (x - z) - b x‖ ≤ H * ‖z‖ ^ α := by
        simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg] using hH (x - z) x
      calc
        _ ≤ poissonKernel m t z * (H * ‖z‖ ^ α) :=
          mul_le_mul_of_nonneg_left hh (kernel_pos m ht z).le
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul, kernel_moment m α ht]; ring

theorem poissonHolder : P201Specs.Elliptic.HalfSpaceLift.poissonHolderStatement := by
  intro m hm α hα hα1
  refine ⟨∫ z, ‖z‖ ^ α * poissonKernel m 1 z, ?_, ?_⟩
  · exact integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (kernel_pos m zero_lt_one z).le)
  · intro b M H hB t ht
    obtain ⟨hM, hH, hsup, hhol⟩ := hB
    have hc := P201.Elliptic.HolderCancellation.holder_continuous hα
      (show P201Specs.Elliptic.HolderCancellation.IsHolder α b from
        ⟨M, H, hM, hH, hsup, hhol⟩)
    exact ⟨poisson_integrand_integrable hc hsup ht,
      poisson_sup_bound b hsup ht,
      poisson_spatial_holder hc hsup hhol ht,
      poisson_approximation_bound hα hα1 hc hsup hhol ht⟩

/-- The pinned Riesz kernels meet the exact hypotheses of the accepted
Hölder cancellation theorem, with the shared surface normalization in m=1 too. -/
lemma riesz_hypotheses {m : ℕ} (hm : 1 ≤ m) (i : Fin m) :
    P201Specs.Elliptic.HolderCancellation.KernelHypotheses (rieszKernel m i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    exact ((contDiffAt_const.mul
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).contDiff.contDiffAt).div
      ((contDiffAt_norm ℝ hz').pow (m + 1))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hz'))).contDiffWithinAt
  · intro r hr z hz
    have h := P102.U3.Riesz.kernel_homogeneous m hm i r hr z
    simpa only [rieszKernel, zpow_neg, zpow_natCast, smul_eq_mul] using h
  · change (∫ z, rieszKernel m i z ∂P201.unitSurface m) = 0
    rw [P201.Elliptic.HolderCancellation.unitSurface_eq_polar]
    have hmeas : Measurable (rieszKernel m i) :=
      measurable_of_continuousOn_compl_singleton 0
        (P102.U3.Riesz.kernel_smooth m hm i).continuousOn
    rw [integral_map (by fun_prop) hmeas.aestronglyMeasurable]
    exact (P102.U3.Riesz.kernel_sphere_mean m hm i).2

lemma riesz_holder {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (i : Fin m) {b : Space m → ℝ} (hb : HasCompactSupport b)
    (hB : P201Specs.Elliptic.HolderCancellation.IsHolder α b) :
    P201Specs.Elliptic.HolderCancellation.IsHolder α
      (P201Specs.Elliptic.HolderCancellation.principalValue (rieszKernel m i) b) := by
  exact P201.Elliptic.HolderCancellation.globalHolder hm α hα hα1 _ _
    (riesz_hypotheses hm i) hb hB

lemma holder_finite_sum {ι : Type*} [Fintype ι] {m : ℕ} {α : ℝ}
    (f : ι → Space m → ℝ)
    (hf : ∀ i, P201Specs.Elliptic.HolderCancellation.IsHolder α (f i)) :
    P201Specs.Elliptic.HolderCancellation.IsHolder α (fun x => ∑ i, f i x) := by
  choose M H hM hH hsup hhol using hf
  refine ⟨∑ i, M i, ∑ i, H i, Finset.sum_nonneg (fun i _ => hM i),
    Finset.sum_nonneg (fun i _ => hH i), ?_, ?_⟩
  · intro x
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hsup i x)
  · intro x y
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (f i x - f i y)‖ ≤ ∑ i, ‖f i x - f i y‖ := norm_sum_le _ _
      _ ≤ ∑ i, H i * dist x y ^ α := Finset.sum_le_sum (fun i _ => hhol i x y)
      _ = _ := (Finset.sum_mul _ _ _).symm

lemma normalGenerator_holder {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (b : Space m → ℝ)
    (hs : ∀ i, HasCompactSupport (tangent b i))
    (hb : ∀ i, P201Specs.Elliptic.HolderCancellation.IsHolder α (tangent b i)) :
    P201Specs.Elliptic.HolderCancellation.IsHolder α (normalGenerator b) := by
  apply holder_finite_sum
  intro i
  exact riesz_holder hm hα hα1 i (hs i) (hb i)

/-- Differentiating a compactly supported datum does not enlarge its support. -/
lemma tangent_support {m : ℕ} (b : Space m → ℝ) (i : Fin m) :
    tsupport (tangent b i) ⊆ tsupport b :=
  tsupport_fderiv_apply_subset ℝ (coordinate m i)

lemma tangent_compactSupport {m : ℕ} {b : Space m → ℝ}
    (hb : HasCompactSupport b) (i : Fin m) : HasCompactSupport (tangent b i) :=
  hb.fderiv_apply ℝ (coordinate m i)

private lemma coordinate_norm {m : ℕ} (i : Fin m) : ‖coordinate m i‖ = 1 := by
  simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single]

/-- Finite ordinary jet and Hessian suprema control each constituent. -/
lemma c2Holder_bounds_by_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {g : E → ℝ} {S : Set E} (hg : C2HolderOn α g S)
    (hS : ∃ x ∈ S, ∃ y ∈ S, x ≠ y) :
    0 ≤ c2HolderNormOn α g S ∧
    (∀ k ≤ 2, ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k g S x‖ ≤ c2HolderNormOn α g S) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDerivWithin ℝ 2 g S x - iteratedFDerivWithin ℝ 2 g S y‖ ≤
        c2HolderNormOn α g S * dist x y ^ α) := by
  obtain ⟨hc, M, H, hM, hH, hjet, hhol⟩ := hg
  obtain ⟨a, ha, b, hb, hab⟩ := hS
  let J (k : ℕ) : Set ℝ := {q | ∃ x ∈ S, q = ‖iteratedFDerivWithin ℝ k g S x‖}
  let Q : Set ℝ := {q | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
    q = ‖iteratedFDerivWithin ℝ 2 g S x - iteratedFDerivWithin ℝ 2 g S y‖ / dist x y ^ α}
  have hJ (k : ℕ) (hk : k ≤ 2) : BddAbove (J k) := by
    refine ⟨M, ?_⟩
    rintro q ⟨x, hx, rfl⟩
    exact hjet k hk x hx
  have hJ0 (k : ℕ) (hk : k ≤ 2) : 0 ≤ sSup (J k) :=
    (norm_nonneg _).trans (le_csSup (hJ k hk) ⟨a, ha, rfl⟩)
  have hQ : BddAbove Q := by
    refine ⟨H, ?_⟩
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hhol x hx y hy)
  have hQ0 : 0 ≤ sSup Q :=
    (div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)).trans
      (le_csSup hQ ⟨a, ha, b, hb, hab, rfl⟩)
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range 3, sSup (J k) :=
    Finset.sum_nonneg (fun k hk => hJ0 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  have hN : c2HolderNormOn α g S = (∑ k ∈ Finset.range 3, sSup (J k)) + sSup Q := rfl
  have hN0 : 0 ≤ c2HolderNormOn α g S := by rw [hN]; exact add_nonneg hsum0 hQ0
  refine ⟨hN0, ?_, ?_⟩
  · intro k hk x hx
    have hks : k ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hle : sSup (J k) ≤ ∑ j ∈ Finset.range 3, sSup (J j) :=
      Finset.single_le_sum (fun j hj => hJ0 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hks
    rw [hN]
    exact (le_csSup (hJ k hk) ⟨x, hx, rfl⟩).trans (hle.trans (le_add_of_nonneg_right hQ0))
  · intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, dist_self] using
        mul_nonneg hN0 (Real.rpow_nonneg (by norm_num : 0 ≤ (0 : ℝ)) α)
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mp
      rw [hN]
      exact (le_csSup hQ ⟨x, hx, y, hy, hxy, rfl⟩).trans (le_add_of_nonneg_left hsum0)
/-- A bounded Lipschitz function is globally Hölder for exponents below one.
The supremum bound controls pairs separated by more than one. -/
lemma holderBounds_of_bounded_lipschitz {m : ℕ} {α M L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {b : Space m → ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖b x‖ ≤ M)
    (hlip : ∀ x y, ‖b x - b y‖ ≤ L * dist x y) :
    P201Specs.Elliptic.HolderCancellation.HolderBounds α b M (L + 2 * M) := by
  refine ⟨hM, by positivity, hb, ?_⟩
  intro x y
  by_cases hd : dist x y ≤ 1
  · have hp : dist x y ≤ dist x y ^ α := by
      by_cases hxy : x = y
      · simp [hxy, Real.zero_rpow hα.ne']
      · simpa using Real.rpow_le_rpow_of_exponent_ge (dist_pos.mpr hxy) hd hα1
    exact (hlip x y).trans ((mul_le_mul_of_nonneg_left hp hL).trans
      (mul_le_mul_of_nonneg_right (by linarith : L ≤ L + 2 * M)
        (Real.rpow_nonneg (dist_nonneg) α)))
  · have hp : 1 ≤ dist x y ^ α := Real.one_le_rpow (le_of_not_ge hd) hα.le
    calc
      ‖b x - b y‖ ≤ ‖b x‖ + ‖b y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hb x, hb y]
      _ ≤ (L + 2 * M) * dist x y ^ α := by nlinarith

lemma holder_of_bounded_lipschitz {m : ℕ} {α M L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {b : Space m → ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ x, ‖b x‖ ≤ M)
    (hlip : ∀ x y, ‖b x - b y‖ ≤ L * dist x y) :
    P201Specs.Elliptic.HolderCancellation.IsHolder α b :=
  ⟨M, L + 2 * M, holderBounds_of_bounded_lipschitz hα hα1 hM hL hb hlip⟩

lemma tangent_tangent_eq {m : ℕ} {g : Space m → ℝ} (hg : ContDiff ℝ 2 g)
    (i j : Fin m) (x : Space m) :
    tangent (tangent g j) i x =
      iteratedFDeriv ℝ 2 g x ![coordinate m i, coordinate m j] := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold tangent
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp [iteratedFDeriv_two_apply]

/-- The datum's actual first and second tangential derivatives belong to the
bounded Hölder class required by the cancellation theorem. -/
lemma c2Holder_tangent_bounds {m : ℕ} {α M H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {g : Space m → ℝ} (hc' : ContDiff ℝ 2 g) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hjet : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ M)
    (hhol : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤
      H * dist x y ^ α) :
    (∀ j, P201Specs.Elliptic.HolderCancellation.HolderBounds α (tangent g j) M (3 * M)) ∧
    (∀ i j, P201Specs.Elliptic.HolderCancellation.HolderBounds α
      (tangent (tangent g j) i) M H) := by
  have hD : ∀ x, ‖fderiv ℝ g x‖ ≤ M := by
    intro x
    simpa only [norm_iteratedFDeriv_one] using
      hjet 1 (by norm_num) x
  have hDD : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
    intro x
    simpa only [← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using hjet 2 (by norm_num) x
  have hLip : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ M * dist x y := by
    intro x y
    have hd := (hc'.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    simpa only [dist_eq_norm] using (convex_univ : Convex ℝ (univ : Set (Space m))).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hd x) (fun x _ => hDD x) (mem_univ y) (mem_univ x)
  have heval : ∀ (A : Space m →L[ℝ] ℝ) j, ‖A (coordinate m j)‖ ≤ ‖A‖ := by
    intro A j
    simpa only [coordinate_norm, mul_one] using A.le_opNorm (coordinate m j)
  have heval2 : ∀ (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space m) ℝ) i j,
      ‖A ![coordinate m i, coordinate m j]‖ ≤ ‖A‖ := by
    intro A i j
    simpa [Fin.prod_univ_two, coordinate_norm] using A.le_opNorm ![coordinate m i, coordinate m j]
  constructor
  · intro j
    have hb := holderBounds_of_bounded_lipschitz hα hα1.le hM hM
      (fun x => (heval _ j).trans (hD x))
      (fun x y => (heval (fderiv ℝ g x - fderiv ℝ g y) j).trans (hLip x y))
    change P201Specs.Elliptic.HolderCancellation.HolderBounds α
      (fun x => fderiv ℝ g x (coordinate m j)) M (3 * M)
    rw [show 3 * M = M + 2 * M by ring]
    exact hb
  · intro i j
    refine ⟨hM, hH, ?_, ?_⟩
    · intro x
      rw [tangent_tangent_eq hc']
      exact (heval2 _ i j).trans (by
        exact hjet 2 (by norm_num) x)
    · intro x y
      simp only [tangent_tangent_eq hc']
      have hh := hhol x y
      exact (heval2 (iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y) i j).trans hh

lemma c2Holder_tangents {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {g : Space m → ℝ} (hg : C2HolderOn α g univ) :
    (∀ j, P201Specs.Elliptic.HolderCancellation.IsHolder α (tangent g j)) ∧
    (∀ i j, P201Specs.Elliptic.HolderCancellation.IsHolder α (tangent (tangent g j) i)) := by
  obtain ⟨hc, M, H, hM, hH, hjet, hhol⟩ := hg
  have hjet' : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ M := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hjet
  have hhol' : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤
      H * dist x y ^ α := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hhol
  obtain ⟨hfirst, hsecond⟩ := c2Holder_tangent_bounds hα hα1 (contDiffOn_univ.mp hc)
    hM hH hjet' hhol'
  exact ⟨fun j => ⟨M, 3 * M, hfirst j⟩, fun i j => ⟨M, H, hsecond i j⟩⟩

/-- Qualitative cancellation bounds for both normal traces follow from the
original datum assumptions, without an extra assumption on its derivatives. -/
lemma normalTraces_holder {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {g : Space m → ℝ}
    (hs : HasCompactSupport g) (hg : C2HolderOn α g univ) :
    P201Specs.Elliptic.HolderCancellation.IsHolder α (normalGenerator g) ∧
    ∀ j, P201Specs.Elliptic.HolderCancellation.IsHolder α (normalGenerator (tangent g j)) := by
  obtain ⟨hfirst, hsecond⟩ := c2Holder_tangents hα hα1 hg
  refine ⟨normalGenerator_holder hm hα hα1 g (tangent_compactSupport hs) hfirst, ?_⟩
  intro j
  exact normalGenerator_holder hm hα hα1 (tangent g j)
    (tangent_compactSupport (tangent_compactSupport hs j)) (fun i => hsecond i j)

open P201Specs.Elliptic.HolderCancellation

lemma holderBounds_mono {m : ℕ} {α M H A B : ℝ} {b : Space m → ℝ}
    (hb : HolderBounds α b M H) (hMA : M ≤ A) (hHB : H ≤ B) :
    HolderBounds α b A B := by
  refine ⟨hb.1.trans hMA, hb.2.1.trans hHB, fun x => (hb.2.2.1 x).trans hMA, ?_⟩
  intro x y
  exact (hb.2.2.2 x y).trans
    (mul_le_mul_of_nonneg_right hHB (Real.rpow_nonneg dist_nonneg _))

lemma holderBounds_sum {ι : Type*} [Fintype ι] {m : ℕ} {α : ℝ}
    (f : ι → Space m → ℝ) (M H : ι → ℝ)
    (hf : ∀ i, HolderBounds α (f i) (M i) (H i)) :
    HolderBounds α (fun x => ∑ i, f i x) (∑ i, M i) (∑ i, H i) := by
  refine ⟨Finset.sum_nonneg (fun i _ => (hf i).1),
    Finset.sum_nonneg (fun i _ => (hf i).2.1), ?_, ?_⟩
  · intro x
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (hf i).2.2.1 x)
  · intro x y
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i, (f i x - f i y)‖ ≤ ∑ i, ‖f i x - f i y‖ := norm_sum_le _ _
      _ ≤ ∑ i, H i * dist x y ^ α := Finset.sum_le_sum (fun i _ => (hf i).2.2.2 x y)
      _ = _ := (Finset.sum_mul _ _ _).symm

/-- Uniform quantitative cancellation for the finite family of pinned Riesz kernels. -/
lemma riesz_holder_uniform {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin m) (b : Space m → ℝ) (B : ℝ),
      HasCompactSupport b → tsupport b ⊆ closedBall 0 R →
      HolderBounds α b B B →
      HolderBounds α (principalValue (rieszKernel m i) b) (2 * C * B) (2 * C * B) := by
  have hi (i : Fin m) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Space m → ℝ), HasCompactSupport b → tsupport b ⊆ closedBall 0 R →
        IsHolder α b → IsHolder α (principalValue (rieszKernel m i) b) ∧
          holderNorm α (principalValue (rieszKernel m i) b) ≤ C * holderNorm α b := by
    obtain ⟨A, D, hAD⟩ := P201.Elliptic.HolderCancellation.sphere_bounds_exist (riesz_hypotheses hm i)
    obtain ⟨C, hC, hest⟩ := P201.Elliptic.HolderCancellation.quantitativeHolder
      (𝕜 := ℝ) hm α hα hα1 (0 : Space m) R A D hR hAD.1 hAD.2.1
    exact ⟨C, hC, fun b hs ht hb => hest _ b (riesz_hypotheses hm i) hAD hs ht hb⟩
  choose C hC hest using hi
  let D := ∑ i, C i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hC i)
  have hCD (i : Fin m) : C i ≤ D := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i)
  refine ⟨D, hD, ?_⟩
  intro i b B hs ht hb
  obtain ⟨hholder, hnorm⟩ := hest i b hs ht ⟨B, B, hb⟩
  have hbound : holderNorm α (principalValue (rieszKernel m i) b) ≤ 2 * D * B := by
    calc
      _ ≤ C i * holderNorm α b := hnorm
      _ ≤ C i * (B + B) := mul_le_mul_of_nonneg_left
        (P201.Elliptic.HolderCancellation.holderNorm_le hm hb) (hC i)
      _ ≤ D * (B + B) := mul_le_mul_of_nonneg_right (hCD i) (add_nonneg hb.1 hb.1)
      _ = _ := by ring
  exact holderBounds_mono (P201.Elliptic.HolderCancellation.bounds_by_holderNorm hm hholder)
    hbound hbound

lemma normalGenerator_holder_quantitative {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Space m → ℝ) (B : ℝ),
      (∀ i, HasCompactSupport (tangent b i)) →
      (∀ i, tsupport (tangent b i) ⊆ closedBall 0 R) →
      (∀ i, HolderBounds α (tangent b i) B B) →
      holderNorm α (normalGenerator b) ≤ C * B := by
  obtain ⟨C, hC, hest⟩ := riesz_holder_uniform hm hα hα1 hR
  refine ⟨4 * (m : ℝ) * C, by positivity, ?_⟩
  intro b B hs ht hb
  have hout := holderBounds_sum
    (fun i x => principalValue (rieszKernel m i) (tangent b i) x)
    (fun _ => 2 * C * B) (fun _ => 2 * C * B)
    (fun i => hest i (tangent b i) B (hs i) (ht i) (hb i))
  have hnorm := P201.Elliptic.HolderCancellation.holderNorm_le hm hout
  change holderNorm α (fun x => ∑ i, principalValue (rieszKernel m i) (tangent b i) x) ≤ _
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (m : ℝ) * (2 * C * B) + (m : ℝ) * (2 * C * B) = (4 * (m : ℝ) * C) * B by ring]
    using hnorm

lemma normalTraces_quantitative {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Space m → ℝ, HasCompactSupport g →
      tsupport g ⊆ closedBall 0 R → C2HolderOn α g univ →
      holderNorm α (normalGenerator g) ≤ C * c2HolderNormOn α g univ ∧
      ∀ j, holderNorm α (normalGenerator (tangent g j)) ≤ C * c2HolderNormOn α g univ := by
  obtain ⟨C, hC, hest⟩ := normalGenerator_holder_quantitative hm hα hα1 hR
  refine ⟨3 * C, by positivity, ?_⟩
  intro g hs ht hg
  let : NeZero m := ⟨by omega⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Space m)
  have hnon : ∃ x ∈ (univ : Set (Space m)), ∃ y ∈ univ, x ≠ y :=
    ⟨0, mem_univ _, y, mem_univ _, hy.symm⟩
  obtain ⟨hN, hjet, hhol⟩ := c2Holder_bounds_by_norm hg hnon
  have hjet' : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ c2HolderNormOn α g univ := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hjet
  have hhol' : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤
      c2HolderNormOn α g univ * dist x y ^ α := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hhol
  obtain ⟨hfirst, hsecond⟩ := c2Holder_tangent_bounds hα hα1
    (contDiffOn_univ.mp hg.1) hN hN hjet' hhol'
  have hN3 : c2HolderNormOn α g univ ≤ 3 * c2HolderNormOn α g univ := by linarith
  constructor
  · have hh := hest g (3 * c2HolderNormOn α g univ)
      (tangent_compactSupport hs) (fun i => (tangent_support g i).trans ht)
      (fun i => holderBounds_mono (hfirst i) hN3 le_rfl)
    convert hh using 1; ring
  · intro j
    have hh := hest (tangent g j) (3 * c2HolderNormOn α g univ)
      (tangent_compactSupport (tangent_compactSupport hs j))
      (fun i => (tangent_support (tangent g j) i).trans ((tangent_support g j).trans ht))
      (fun i => holderBounds_mono (hsecond i j) hN3 hN3)
    convert hh using 1; ring

lemma poissonIntegral_tangent {m : ℕ} {g : Space m → ℝ}
    (hs : HasCompactSupport g) (hg : ContDiff ℝ 1 g) {t : ℝ} (ht : 0 < t)
    (x : Space m) (i : Fin m) :
    fderiv ℝ (poissonIntegral g t) x (coordinate m i) = poissonIntegral (tangent g i) t x := by
  have hk := (kernel_integrable m ht).locallyIntegrable
  have hd := hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hg x
  change fderiv ℝ (poissonKernel m t ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x _ = _
  rw [hd.fderiv, convolution_precompR_apply _ hk (hs.fderiv ℝ) (hg.continuous_fderiv one_ne_zero)]
  rfl

lemma poissonIntegral_contDiff {m : ℕ} {g : Space m → ℝ} {k : ℕ∞}
    (hs : HasCompactSupport g) (hg : ContDiff ℝ k g) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ k (poissonIntegral g t) := by
  exact hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (kernel_integrable m ht).locallyIntegrable hg

lemma poissonIntegral_tangent_tangent {m : ℕ} {g : Space m → ℝ}
    (hs : HasCompactSupport g) (hg : ContDiff ℝ 2 g) {t : ℝ} (ht : 0 < t)
    (x : Space m) (i j : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ (poissonIntegral g t) y (coordinate m j)) x (coordinate m i) =
      poissonIntegral (tangent (tangent g j) i) t x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have he : (fun y => fderiv ℝ (poissonIntegral g t) y (coordinate m j)) =
      poissonIntegral (tangent g j) t := funext fun y => poissonIntegral_tangent hs hg1 ht y j
  rw [he]
  apply poissonIntegral_tangent (tangent_compactSupport hs j) _ ht
  exact ((hg.fderiv_right (by norm_num)).clm_apply contDiff_const)

lemma horizontal_contDiff (m : ℕ) : ContDiff ℝ ⊤ (@horizontal m) := by
  apply contDiff_piLp' 2
  intro i
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) i.castSucc).contDiff

lemma height_contDiff (m : ℕ) : ContDiff ℝ ⊤ (@height m) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).contDiff

lemma point_horizontal_height {m : ℕ} (p : Space (m + 1)) :
    point (horizontal p) (height p) = p := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [point, height]
  · simp [point, horizontal]

lemma heightCLM_surjective (m : ℕ) :
    Function.Surjective (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)) := by
  intro t
  exact ⟨point (0 : Space m) t, height_point _ _⟩

lemma height_isOpenMap (m : ℕ) : IsOpenMap (@height m) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).isOpenMap
    (heightCLM_surjective m)

lemma isOpen_openHalfSpace (m : ℕ) : IsOpen (openHalfSpace m) :=
  isOpen_lt continuous_const (height_contDiff m).continuous

lemma isClosed_closedHalfSpace (m : ℕ) : IsClosed (closedHalfSpace m) :=
  isClosed_le continuous_const (height_contDiff m).continuous

lemma convex_closedHalfSpace (m : ℕ) : Convex ℝ (closedHalfSpace m) := by
  exact (convex_Ici (0 : ℝ)).linear_preimage
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).toLinearMap

lemma convex_openHalfSpace (m : ℕ) : Convex ℝ (openHalfSpace m) := by
  exact (convex_Ioi (0 : ℝ)).linear_preimage
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).toLinearMap

lemma interior_closedHalfSpace (m : ℕ) : interior (closedHalfSpace m) = openHalfSpace m := by
  change interior ((@height m) ⁻¹' Ici 0) = (@height m) ⁻¹' Ioi 0
  rw [← (height_isOpenMap m).preimage_interior_eq_interior_preimage (height_contDiff m).continuous,
    interior_Ici]

lemma closure_openHalfSpace (m : ℕ) : closure (openHalfSpace m) = closedHalfSpace m := by
  change closure ((@height m) ⁻¹' Ioi 0) = (@height m) ⁻¹' Ici 0
  rw [← (height_isOpenMap m).preimage_closure_eq_closure_preimage (height_contDiff m).continuous,
    closure_Ioi]

lemma uniqueDiffOn_closedHalfSpace (m : ℕ) : UniqueDiffOn ℝ (closedHalfSpace m) := by
  apply uniqueDiffOn_convex (convex_closedHalfSpace m)
  rw [interior_closedHalfSpace]
  refine ⟨point (0 : Space m) 1, ?_⟩
  change 0 < height (point (0 : Space m) 1)
  simp

lemma fderivWithin_closedHalfSpace_eq {m : ℕ} (f : Space (m + 1) → ℝ)
    {p : Space (m + 1)} (hp : p ∈ openHalfSpace m) :
    fderivWithin ℝ f (closedHalfSpace m) p = fderiv ℝ f p := by
  apply fderivWithin_of_mem_nhds
  rw [← mem_interior_iff_mem_nhds, interior_closedHalfSpace]
  exact hp

def horizontalCLM (m : ℕ) : Space (m + 1) →L[ℝ] Space m where
  toFun := horizontal
  map_add' p q := by ext i; simp [horizontal]
  map_smul' a p := by ext i; simp [horizontal]
  cont := (horizontal_contDiff m).continuous

@[simp] lemma horizontalCLM_apply {m : ℕ} (p : Space (m + 1)) :
    horizontalCLM m p = horizontal p := rfl

lemma fderiv_horizontal {m : ℕ} (p : Space (m + 1)) :
    fderiv ℝ (@horizontal m) p = horizontalCLM m :=
  (horizontalCLM m).hasFDerivAt.fderiv

lemma fderiv_height {m : ℕ} (p : Space (m + 1)) :
    fderiv ℝ (@height m) p =
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m) := by
  change fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)) p = _
  exact ContinuousLinearMap.fderiv _

@[simp] lemma horizontal_coordinate_castSucc {m : ℕ} (i : Fin m) :
    horizontal (coordinate (m + 1) i.castSucc) = coordinate m i := by
  ext j
  simp [horizontal, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]

@[simp] lemma horizontal_coordinate_last (m : ℕ) :
    horizontal (coordinate (m + 1) (Fin.last m)) = 0 := by
  ext j
  simp [horizontal, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]

@[simp] lemma height_coordinate_castSucc {m : ℕ} (i : Fin m) :
    height (coordinate (m + 1) i.castSucc) = 0 := by
  simp [height, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]

@[simp] lemma height_coordinate_last (m : ℕ) :
    height (coordinate (m + 1) (Fin.last m)) = 1 := by
  simp [height, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]

lemma point_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : Space m × ℝ => point p.1 p.2) := by
  apply contDiff_piLp' 2
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [point] using (contDiff_snd : ContDiff ℝ ⊤ (fun p : Space m × ℝ => p.2))
  · simpa [point, Function.comp_def] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j).contDiff.comp contDiff_fst

lemma horizontal_norm_le {m : ℕ} (p : Space (m + 1)) : ‖horizontal p‖ ≤ ‖p‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc]
  simp only [horizontal, WithLp.ofLp_toLp]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma hasFDerivWithinAt_closedHalfSpace_of_extension {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space (m + 1) → F} {D : Space (m + 1) → Space (m + 1) →L[ℝ] F}
    (hf : DifferentiableOn ℝ f (openHalfSpace m))
    (hc : ContinuousOn f (closedHalfSpace m))
    (hD : ContinuousOn D (closedHalfSpace m))
    (he : ∀ p ∈ openHalfSpace m, fderiv ℝ f p = D p)
    {p : Space (m + 1)} (hp : p ∈ closedHalfSpace m) :
    HasFDerivWithinAt f (D p) (closedHalfSpace m) p := by
  have hUS : openHalfSpace m ⊆ closedHalfSpace m := fun q hq => (show 0 < height q from hq).le
  have hlim : Tendsto (fun q => fderiv ℝ f q) (𝓝[openHalfSpace m] p) (𝓝 (D p)) := by
    apply ((hD p hp).mono hUS).congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (he q hq).symm
  rw [← closure_openHalfSpace m]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv hf (convex_openHalfSpace m)
    (isOpen_openHalfSpace m) _ hlim
  intro q hq
  rw [closure_openHalfSpace m] at hq
  exact (hc q hq).mono hUS

lemma fderivWithin_closedHalfSpace_of_extension {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space (m + 1) → F} {D : Space (m + 1) → Space (m + 1) →L[ℝ] F}
    (hf : DifferentiableOn ℝ f (openHalfSpace m))
    (hc : ContinuousOn f (closedHalfSpace m))
    (hD : ContinuousOn D (closedHalfSpace m))
    (he : ∀ p ∈ openHalfSpace m, fderiv ℝ f p = D p)
    {p : Space (m + 1)} (hp : p ∈ closedHalfSpace m) :
    fderivWithin ℝ f (closedHalfSpace m) p = D p :=
  (hasFDerivWithinAt_closedHalfSpace_of_extension hf hc hD he hp).fderivWithin
    (uniqueDiffOn_closedHalfSpace m p hp)

/-- Continuous actual interior jets give genuine C² regularity on the closed half-space. -/
lemma contDiffOn_two_closedHalfSpace_of_extension {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space (m + 1) → F}
    {D : Space (m + 1) → Space (m + 1) →L[ℝ] F}
    {A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1) →L[ℝ] F}
    (hf : DifferentiableOn ℝ f (openHalfSpace m))
    (hDf : DifferentiableOn ℝ D (openHalfSpace m))
    (hc : ContinuousOn f (closedHalfSpace m))
    (hD : ContinuousOn D (closedHalfSpace m))
    (hA : ContinuousOn A (closedHalfSpace m))
    (heD : ∀ p ∈ openHalfSpace m, fderiv ℝ f p = D p)
    (heA : ∀ p ∈ openHalfSpace m, fderiv ℝ D p = A p) :
    ContDiffOn ℝ 2 f (closedHalfSpace m) ∧
      (∀ p ∈ closedHalfSpace m, fderivWithin ℝ f (closedHalfSpace m) p = D p) ∧
      (∀ p ∈ closedHalfSpace m, fderivWithin ℝ D (closedHalfSpace m) p = A p) := by
  have hUD := uniqueDiffOn_closedHalfSpace m
  have hdD : ∀ p ∈ closedHalfSpace m, HasFDerivWithinAt f (D p) (closedHalfSpace m) p :=
    fun p hp => hasFDerivWithinAt_closedHalfSpace_of_extension hf hc hD heD hp
  have hdA : ∀ p ∈ closedHalfSpace m, HasFDerivWithinAt D (A p) (closedHalfSpace m) p :=
    fun p hp => hasFDerivWithinAt_closedHalfSpace_of_extension hDf hD hA heA hp
  have hCD : ContDiffOn ℝ 1 D (closedHalfSpace m) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUD]
    exact ⟨by simp, A, contDiffOn_zero.mpr hA, hdA⟩
  have hCf : ContDiffOn ℝ 2 f (closedHalfSpace m) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUD]
    exact ⟨by simp, D, hCD, hdD⟩
  exact ⟨hCf, fun p hp => (hdD p hp).fderivWithin (hUD p hp),
    fun p hp => (hdA p hp).fderivWithin (hUD p hp)⟩

lemma c2HolderNormOn_le_of_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {g : E → ℝ} {S : Set E} {M H : ℝ}
    (hS : ∃ x ∈ S, ∃ y ∈ S, x ≠ y)
    (hjet : ∀ k ≤ 2, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ k g S x‖ ≤ M)
    (hhol : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDerivWithin ℝ 2 g S x - iteratedFDerivWithin ℝ 2 g S y‖ ≤
        H * dist x y ^ α) :
    c2HolderNormOn α g S ≤ 3 * M + H := by
  obtain ⟨a, ha, b, hb, hab⟩ := hS
  have hj (k : ℕ) (hk : k ≤ 2) :
      sSup {q : ℝ | ∃ x ∈ S, q = ‖iteratedFDerivWithin ℝ k g S x‖} ≤ M := by
    refine csSup_le ⟨_, a, ha, rfl⟩ ?_
    rintro q ⟨x, hx, rfl⟩
    exact hjet k hk x hx
  have hq : holderSeminormOn α (iteratedFDerivWithin ℝ 2 g S) S ≤ H := by
    unfold holderSeminormOn
    refine csSup_le ⟨_, a, ha, b, hb, hab, rfl⟩ ?_
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hhol x hx y hy)
  have hs : (∑ k ∈ Finset.range 3,
      sSup {q : ℝ | ∃ x ∈ S, q = ‖iteratedFDerivWithin ℝ k g S x‖}) ≤ 3 * M := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 3, M :=
        Finset.sum_le_sum (fun k hk => hj k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      _ = _ := by simp
  exact add_le_add hs hq

def coordinateExpansion {n : ℕ} (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (Fin n → F) →L[ℝ] (Space n →L[ℝ] F) :=
  ∑ i : Fin n,
    (ContinuousLinearMap.smulRightL ℝ (Space n) F
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)).comp (ContinuousLinearMap.proj i)

@[simp] lemma coordinateExpansion_apply {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : Fin n → F) (x : Space n) :
    coordinateExpansion F c x = ∑ i : Fin n, x i • c i := by
  simp [coordinateExpansion]

@[simp] lemma coordinateExpansion_coordinate {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : Fin n → F) (j : Fin n) :
    coordinateExpansion F c (coordinate n j) = c j := by
  simp [coordinateExpansion_apply, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]

lemma coordinateExpansion_eq {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : Space n →L[ℝ] F) :
    coordinateExpansion F (fun i => A (coordinate n i)) = A := by
  ext x
  have he : x = ∑ i : Fin n, x i • coordinate n i := by
    ext j
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector, Pi.single_apply]
  calc
    _ = A (∑ i : Fin n, x i • coordinate n i) := by simp
    _ = A x := congrArg A he.symm

lemma coordinateExpansion_norm_le {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : Fin n → F) :
    ‖coordinateExpansion F c‖ ≤ ∑ i : Fin n, ‖c i‖ := by
  apply (coordinateExpansion F c).opNorm_le_bound (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro x
  rw [coordinateExpansion_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)).trans_eq (mul_comm _ _)


def bilinearJetEquiv (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (E →L[ℝ] E →L[ℝ] F) ≃ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F :=
  ((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm).trans
    ((continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm)

@[simp] lemma bilinearJetEquiv_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] F) (v : Fin 2 → E) :
    bilinearJetEquiv E F A v = A (v 0) (v 1) := by
  rfl

lemma iteratedFDerivWithin_two_eq_bilinearJet {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : UniqueDiffOn ℝ S)
    {D : E → E →L[ℝ] F} {A : E → E →L[ℝ] E →L[ℝ] F}
    (hD : ∀ p ∈ S, fderivWithin ℝ f S p = D p)
    (hA : ∀ p ∈ S, fderivWithin ℝ D S p = A p)
    {p : E} (hp : p ∈ S) :
    iteratedFDerivWithin ℝ 2 f S p = bilinearJetEquiv E F (A p) := by
  ext v
  rw [iteratedFDerivWithin_two_apply _ hS hp, bilinearJetEquiv_apply]
  rw [fderivWithin_congr' hD hp, hA p hp]

lemma c2HolderOn_of_jet_extension {m : ℕ} {α M H : ℝ}
    {f : Space (m+1) → ℝ}
    {D : Space (m+1) → Space (m+1) →L[ℝ] ℝ}
    {A : Space (m+1) → Space (m+1) →L[ℝ] Space (m+1) →L[ℝ] ℝ}
    (hf : DifferentiableOn ℝ f (openHalfSpace m))
    (hDf : DifferentiableOn ℝ D (openHalfSpace m))
    (hc : ContinuousOn f (closedHalfSpace m))
    (hD : ContinuousOn D (closedHalfSpace m))
    (hA : ContinuousOn A (closedHalfSpace m))
    (heD : ∀ p ∈ openHalfSpace m, fderiv ℝ f p = D p)
    (heA : ∀ p ∈ openHalfSpace m, fderiv ℝ D p = A p)
    (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hfM : ∀ p ∈ closedHalfSpace m, ‖f p‖ ≤ M)
    (hDM : ∀ p ∈ closedHalfSpace m, ‖D p‖ ≤ M)
    (hAM : ∀ p ∈ closedHalfSpace m, ‖A p‖ ≤ M)
    (hAH : ∀ p ∈ closedHalfSpace m, ∀ q ∈ closedHalfSpace m,
      ‖A p - A q‖ ≤ H * dist p q ^ α) :
    C2HolderOn α f (closedHalfSpace m) := by
  obtain ⟨hc2, he1, he2⟩ := contDiffOn_two_closedHalfSpace_of_extension hf hDf hc hD hA heD heA
  have hU := uniqueDiffOn_closedHalfSpace m
  have htwo := fun p hp => iteratedFDerivWithin_two_eq_bilinearJet hU he1 he2 (p := p) hp
  refine ⟨hc2, M, H, hM, hH, ?_, ?_⟩
  · intro k hk p hp
    interval_cases k
    · simpa only [norm_iteratedFDerivWithin_zero] using hfM p hp
    · rw [norm_iteratedFDerivWithin_one _ (hU p hp), he1 p hp]
      exact hDM p hp
    · rw [htwo p hp, LinearIsometryEquiv.norm_map]
      exact hAM p hp
  · intro p hp q hq
    rw [htwo p hp, htwo q hq, ← (bilinearJetEquiv (Space (m+1)) ℝ).map_sub, LinearIsometryEquiv.norm_map]
    exact hAH p hp q hq


lemma coordinateExpansion_ext {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A B : Space n →L[ℝ] F} (h : ∀ i, A (coordinate n i) = B (coordinate n i)) : A = B := by
  rw [← coordinateExpansion_eq A, ← coordinateExpansion_eq B]
  congr 1
  funext i
  exact h i

lemma continuousOn_coordinateExpansion {n : ℕ} {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : Fin n → E → F} {S : Set E} (hd : ∀ i, ContinuousOn (d i) S) :
    ContinuousOn (fun p => coordinateExpansion F (fun i => d i p)) S :=
  (coordinateExpansion F).continuous.comp_continuousOn (continuousOn_pi.mpr hd)

lemma hasFDerivAt_coordinateExpansion {n k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : Fin n → Space k → F} {d' : Fin n → Space k →L[ℝ] F} {p : Space k}
    (hd : ∀ i, HasFDerivAt (d i) (d' i) p) :
    HasFDerivAt (fun q => coordinateExpansion F (fun i => d i q))
      ((coordinateExpansion F).comp (ContinuousLinearMap.pi d')) p :=
  (coordinateExpansion F).hasFDerivAt.comp p (hasFDerivAt_pi.mpr hd)

lemma fderiv_coordinateExpansion {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : Fin n → Space n → F} {a : Fin n → Fin n → F} {p : Space n}
    (hd : ∀ j, DifferentiableAt ℝ (d j) p)
    (ha : ∀ i j, fderiv ℝ (d j) p (coordinate n i) = a i j) :
    fderiv ℝ (fun q => coordinateExpansion F (fun j => d j q)) p =
      coordinateExpansion (Space n →L[ℝ] F) (fun i => coordinateExpansion F (a i)) := by
  rw [(hasFDerivAt_coordinateExpansion (fun j => (hd j).hasFDerivAt)).fderiv]
  apply coordinateExpansion_ext
  intro i
  apply coordinateExpansion_ext
  intro j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    coordinateExpansion_coordinate]
  exact ha i j

lemma coordinateExpansion_uniform_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : Fin n → F} {M : ℝ}
    (hc : ∀ i, ‖c i‖ ≤ M) : ‖coordinateExpansion F c‖ ≤ n * M := by
  apply (coordinateExpansion_norm_le c).trans
  calc
    _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hc i
    _ = n * M := by simp

lemma coordinateExpansion_holder {n : ℕ} {E F : Type*} [PseudoMetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : Fin n → E → F} {α H : ℝ} {S : Set E}
    (hd : ∀ i, ∀ p ∈ S, ∀ q ∈ S, ‖d i p - d i q‖ ≤ H * dist p q ^ α)
    {p q : E} (hp : p ∈ S) (hq : q ∈ S) :
    ‖coordinateExpansion F (fun i => d i p) - coordinateExpansion F (fun i => d i q)‖ ≤
      (n * H) * dist p q ^ α := by
  rw [← (coordinateExpansion F).map_sub]
  exact (coordinateExpansion_uniform_bound (fun i => hd i p hp q hq)).trans_eq (by ring)


lemma kernel_contDiff (m : ℕ) :
    ContDiffOn ℝ ⊤ (fun p : Space (m + 1) =>
      poissonKernel m (height p) (horizontal p)) (openHalfSpace m) := by
  have hb : ContDiff ℝ ⊤ (fun p : Space (m + 1) =>
      height p ^ 2 + ‖horizontal p‖ ^ 2) :=
    ((height_contDiff m).pow 2).add ((contDiff_norm_sq ℝ).comp (horizontal_contDiff m))
  intro p hp
  have ht : 0 < height p := hp
  exact ((contDiffWithinAt_const.mul (height_contDiff m).contDiffWithinAt).mul
    (hb.contDiffWithinAt.rpow_const_of_ne (by positivity)))

lemma inner_coordinate {n : ℕ} (p : Space n) (i : Fin n) : innerSL ℝ p (coordinate n i) = p i := by
  simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.inner_single_right]

lemma proj_coordinate {n : ℕ} (i j : Fin n) :
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j) (coordinate n i) = if i = j then 1 else 0 := by
  simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector, eq_comm]

lemma radial_linear_first {n : ℕ} (C a : ℝ) (j i : Fin n) (p : Space n) (hp : p ≠ 0) :
    fderiv ℝ (fun q : Space n => C * q j * (‖q‖ ^ 2) ^ a) p (coordinate n i) =
      C * ((if i = j then 1 else 0) * (‖p‖ ^ 2) ^ a +
        (2 * a) * (p j * p i * (‖p‖ ^ 2) ^ (a - 1))) := by
  have hr : ‖p‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
  have hR := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.rpow_const (p := a) (Or.inl hr)
  have hP := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).hasFDerivAt (x := p)
  have hD := (hP.const_mul C).mul hR
  change (fderiv ℝ (fun q : Space n => C * q j * (‖q‖ ^ 2) ^ a) p) _ = _
  simp only [Pi.mul_def, PiLp.proj_apply] at hD
  rw [hD.fderiv]
  simp only [add_apply, smul_apply,
    inner_coordinate, proj_coordinate, two_smul, smul_eq_mul]
  ring

lemma radial_linear_second {n : ℕ} (C a : ℝ) (j i : Fin n) (p : Space n) (hp : p ≠ 0) :
    fderiv ℝ (fun q : Space n =>
      fderiv ℝ (fun r : Space n => C * r j * (‖r‖ ^ 2) ^ a) q (coordinate n i))
      p (coordinate n i) =
      C * ((4 * a) * (if i = j then p i else 0) * (‖p‖ ^ 2) ^ (a - 1) +
        (2 * a) * p j * (‖p‖ ^ 2) ^ (a - 1) +
        (4 * a * (a - 1)) * p j * (p i) ^ 2 * (‖p‖ ^ 2) ^ (a - 1 - 1)) := by
  have hr : ‖p‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
  have hEq : (fun q : Space n =>
      fderiv ℝ (fun r : Space n => C * r j * (‖r‖ ^ 2) ^ a) q (coordinate n i)) =ᶠ[𝓝 p]
      (fun q : Space n => C * ((if i = j then 1 else 0) * (‖q‖ ^ 2) ^ a +
        (2 * a) * (q j * q i * (‖q‖ ^ 2) ^ (a - 1)))) := by
    filter_upwards [eventually_ne_nhds hp] with q hq
    exact radial_linear_first C a j i q hq
  rw [hEq.fderiv_eq]
  have hR := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.rpow_const (p := a) (Or.inl hr)
  have hR' := (hasStrictFDerivAt_norm_sq p).hasFDerivAt.rpow_const (p := a - 1) (Or.inl hr)
  have hPi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt (x := p)
  have hPj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).hasFDerivAt (x := p)
  have hD := ((hR.const_mul (if i = j then 1 else 0)).add
    (((hPj.mul hPi).mul hR').const_mul (2 * a))).const_mul C
  simp only [Pi.mul_def, Pi.add_def, PiLp.proj_apply] at hD
  rw [hD.fderiv]
  simp only [add_apply, smul_apply,
    inner_coordinate, proj_coordinate, ite_true, two_smul, smul_eq_mul]
  split_ifs with hij
  · subst j
    ring
  · ring
lemma radial_linear_laplacian {n : ℕ} (C a : ℝ) (j : Fin n) (p : Space n) (hp : p ≠ 0) :
    laplacian (fun q : Space n => C * q j * (‖q‖ ^ 2) ^ a) p =
      C * p j * (2 * a * ((n : ℝ) + 2 * a)) * (‖p‖ ^ 2) ^ (a - 1) := by
  have hr : 0 < ‖p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
  have hpow : (‖p‖ ^ 2) * (‖p‖ ^ 2) ^ (a - 1 - 1) = (‖p‖ ^ 2) ^ (a - 1) := by
    nth_rw 1 [← Real.rpow_one (‖p‖ ^ 2)]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hsq : ∑ i : Fin n, p i ^ 2 = ‖p‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) p).symm
  change (∑ i : Fin n, P102.U4.multiPartial
    (fun q : Space n => C * q j * (‖q‖ ^ 2) ^ a) ({i, i} : MultiIndex n) p) = _
  simp only [P102.U4.multiPartial]
  simp [Multiset.sort_cons, P102.U4.partialWord]
  simp_rw [radial_linear_second C a j _ p hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsq]
  rw [show 4 * a * (a - 1) * p j * (‖p‖ ^ 2) * (‖p‖ ^ 2) ^ (a - 1 - 1) =
      4 * a * (a - 1) * p j * (‖p‖ ^ 2) ^ (a - 1) by rw [mul_assoc, hpow]]
  ring
lemma norm_sq_horizontal_height {m : ℕ} (p : Space (m + 1)) :
    ‖p‖ ^ 2 = height p ^ 2 + ‖horizontal p‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, horizontal, height, WithLp.ofLp_toLp]
  rw [Fin.sum_univ_castSucc]
  ring

lemma kernel_radial (m : ℕ) :
    (fun p : Space (m + 1) => poissonKernel m (height p) (horizontal p)) =
      (fun p : Space (m + 1) =>
        poissonConstant m * p (Fin.last m) * (‖p‖ ^ 2) ^ (-((m : ℝ) + 1) / 2)) := by
  funext p
  change P201Specs.Elliptic.HalfSpaceLift.poissonConstant m * height p *
    (height p ^ 2 + ‖horizontal p‖ ^ 2) ^ (-((m : ℝ) + 1) / 2) = _
  rw [← norm_sq_horizontal_height]
  rfl

lemma kernel_harmonic (m : ℕ) (p : Space (m + 1)) (hp : p ∈ openHalfSpace m) :
    laplacian (fun q : Space (m + 1) => poissonKernel m (height q) (horizontal q)) p = 0 := by
  have hp0 : p ≠ 0 := by
    intro hz
    have ht : 0 < height p := hp
    simp [height, hz] at ht
  rw [kernel_radial, radial_linear_laplacian _ _ _ p hp0]
  have hz : ((m + 1 : ℕ) : ℝ) + 2 * (-((m : ℝ) + 1) / 2) = 0 := by push_cast; ring
  rw [hz]
  ring

set_option backward.isDefEq.respectTransparency.types false in
lemma shifted_gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ u : ℝ in Ioi 0, Real.exp (-(u - a / u) ^ 2)) = Real.sqrt Real.pi / 2 := by
  let g : ℝ → ℝ := fun u => u - a / u
  let g' : ℝ → ℝ := fun u => 1 + a / u ^ 2
  let F : ℝ → ℝ := fun u => Real.exp (-(g u) ^ 2)
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt g (g' u) (Ioi 0) u := by
    intro u hu
    have h := (hasDerivAt_id u).sub ((hasDerivAt_const u a).div (hasDerivAt_id u) hu.ne')
    convert! h.hasDerivWithinAt (s := Ioi 0) using 1
    dsimp [g']; ring
  have hinj : InjOn g (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro x hx y hy hxy
    dsimp [g]
    have hh : a / y < a / x := div_lt_div_of_pos_left ha hx hxy
    linarith
  have himg : g '' Ioi (0 : ℝ) = univ := by
    apply eq_univ_of_forall
    intro v
    let s := Real.sqrt (v ^ 2 + 4 * a)
    have hs : s ^ 2 = v ^ 2 + 4 * a := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsv : -v < s := by nlinarith [sq_nonneg (s + v)]
    have hu : 0 < (v + s) / 2 := by linarith
    refine ⟨(v + s) / 2, hu, ?_⟩
    dsimp [g]
    field_simp [show v + s ≠ 0 by linarith]
    nlinarith
  have hpos : ∀ u ∈ Ioi (0 : ℝ), 0 < g' u := by
    intro u hu
    dsimp [g']
    positivity
  have hjac : (∫ u in Ioi (0 : ℝ), g' u * F u) = Real.sqrt Real.pi := by
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj
      (fun v : ℝ => Real.exp (-v ^ 2))
    rw [himg, setIntegral_univ] at h
    have hgauss : (∫ v : ℝ, Real.exp (-v ^ 2)) = Real.sqrt Real.pi := by
      simpa using integral_gaussian (1 : ℝ)
    rw [hgauss] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [abs_of_pos (hpos u hu), smul_eq_mul]
  have hjaci : IntegrableOn (fun u => g' u * F u) (Ioi 0) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj
      (fun v : ℝ => Real.exp (-v ^ 2))).mp
      (by rw [himg]; simpa using (integrable_exp_neg_mul_sq Real.zero_lt_one).integrableOn (s := univ))
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul, abs_of_pos (hpos u hu)]
    rfl
  have hFi : IntegrableOn F (Ioi 0) := by
    apply hjaci.mono' (by dsimp [F, g]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [g']
    calc
      _ = 1 * F u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (show 1 ≤ 1 + a / u ^ 2 by have := div_nonneg ha.le (sq_nonneg u); linarith) (Real.exp_pos _).le
  have hWi : IntegrableOn (fun u => (a / u ^ 2) * F u) (Ioi 0) := by
    convert hjaci.sub hFi using 1
    funext u
    dsimp [g']
    ring
  have hInv : (∫ u in Ioi (0 : ℝ), (a / u ^ 2) * F u) = ∫ u in Ioi (0 : ℝ), F u := by
    have hder : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => a / u)
        (-a / u ^ 2) (Ioi 0) u := by
      intro u hu
      convert! ((hasDerivAt_const u a).div (hasDerivAt_id u) hu.ne').hasDerivWithinAt (s := Ioi 0) using 1
      dsimp; ring
    have himg' : (fun u : ℝ => a / u) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact div_pos ha hu
      · intro hv
        exact ⟨a / v, div_pos ha hv, by field_simp⟩
    have hinj' : InjOn (fun u : ℝ => a / u) (Ioi (0 : ℝ)) := by
      intro u hu v hv huv
      have hh := (div_eq_div_iff hu.ne' hv.ne').mp huv
      nlinarith
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj' F
    rw [himg'] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have he : F (a / u) = F u := by
      dsimp [F, g]
      congr 2
      field_simp [(show 0 < u from hu).ne']
      ring
    dsimp only
    rw [he]
    simp [smul_eq_mul, abs_div, abs_neg, abs_of_pos ha, abs_pow, sq_abs]
  have he : (∫ u in Ioi (0 : ℝ), g' u * F u) =
      (∫ u in Ioi (0 : ℝ), F u) + ∫ u in Ioi (0 : ℝ), (a / u ^ 2) * F u := by
    rw [← integral_add hFi hWi]
    congr 1
    funext u
    dsimp [g']
    ring
  rw [he, hInv] at hjac
  change (∫ u in Ioi (0 : ℝ), F u) = _
  linarith

lemma subordination_gaussian {a : ℝ} (ha : 0 ≤ a) :
    (∫ u : ℝ in Ioi 0, Real.exp (-u ^ 2 - a ^ 2 / u ^ 2)) =
      Real.sqrt Real.pi / 2 * Real.exp (-2 * a) := by
  rcases ha.eq_or_lt with h | ha
  · subst a
    simpa using integral_gaussian_Ioi (1 : ℝ)
  · have he : (∫ u : ℝ in Ioi 0, Real.exp (-u ^ 2 - a ^ 2 / u ^ 2)) =
        Real.exp (-2 * a) * ∫ u : ℝ in Ioi 0, Real.exp (-(u - a / u) ^ 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [← Real.exp_add]
      congr 1
      field_simp [(show 0 < u from hu).ne']
      ring
    rw [he, shifted_gaussian_integral ha]
    ring

lemma subordination_laplace {a : ℝ} (ha : 0 ≤ a) :
    (∫ v : ℝ in Ioi 0, v ^ (-(1 / 2 : ℝ)) * Real.exp (-v - a ^ 2 / v)) =
      Real.sqrt Real.pi * Real.exp (-2 * a) := by
  rw [← integral_comp_rpow_Ioi (fun v : ℝ => v ^ (-(1 / 2 : ℝ)) *
    Real.exp (-v - a ^ 2 / v)) (p := 2) (by norm_num)]
  calc
    _ = ∫ u : ℝ in Ioi 0, 2 * Real.exp (-u ^ 2 - a ^ 2 / u ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        smul_eq_mul]
      rw [← Real.rpow_mul hu.le]
      norm_num
      rw [Real.rpow_neg_one]
      field_simp [(show 0 < u from hu).ne']
    _ = _ := by rw [integral_const_mul, subordination_gaussian ha]; ring

lemma subordination_laplace_scaled {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (∫ s : ℝ in Ioi 0, s ^ (-(1 / 2 : ℝ)) * Real.exp (-t ^ 2 * s - r ^ 2 / s)) =
      Real.sqrt Real.pi / t * Real.exp (-2 * t * r) := by
  let g : ℝ → ℝ := fun v => v ^ (-(1 / 2 : ℝ)) * Real.exp (-v - (t * r) ^ 2 / v)
  have hs (s : ℝ) (hs : 0 < s) :
      s ^ (-(1 / 2 : ℝ)) * Real.exp (-t ^ 2 * s - r ^ 2 / s) = t * g (t ^ 2 * s) := by
    dsimp [g]
    rw [Real.mul_rpow (sq_nonneg t) hs.le, ← Real.rpow_natCast t 2,
      ← Real.rpow_mul ht.le]
    norm_num
    rw [Real.rpow_neg_one]
    have he : -(t ^ 2 * s) - (t * r) ^ 2 / (t ^ 2 * s) = -t ^ 2 * s - r ^ 2 / s := by
      field_simp
    rw [he]
    field_simp
  calc
    _ = ∫ s in Ioi (0 : ℝ), t * g (t ^ 2 * s) :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs' => hs s hs')
    _ = t * ((t ^ 2)⁻¹ * ∫ v in Ioi (0 : ℝ), g v) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 (sq_pos_of_pos ht)]
      simp only [mul_zero, smul_eq_mul]
    _ = _ := by
      rw [show (∫ v in Ioi (0 : ℝ), g v) = Real.sqrt Real.pi * Real.exp (-2 * (t * r))
        from subordination_laplace (mul_nonneg ht.le hr)]
      have he : -2 * (t * r) = -2 * t * r := by ring
      rw [he]
      field_simp

lemma subordination_inverse {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (∫ s : ℝ in Ioi 0, s ^ (-(3 / 2 : ℝ)) * Real.exp (-t ^ 2 / s - r ^ 2 * s)) =
      Real.sqrt Real.pi / t * Real.exp (-2 * t * r) := by
  rw [← integral_comp_rpow_Ioi (fun s : ℝ => s ^ (-(3 / 2 : ℝ)) *
    Real.exp (-t ^ 2 / s - r ^ 2 * s)) (p := -1) (by norm_num)]
  calc
    _ = ∫ v : ℝ in Ioi 0, v ^ (-(1 / 2 : ℝ)) * Real.exp (-t ^ 2 * v - r ^ 2 / v) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      norm_num only [abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -2 by norm_num,
        smul_eq_mul]
      rw [← Real.rpow_mul (show 0 ≤ v from le_of_lt hv), ← mul_assoc,
        ← Real.rpow_add hv]
      have he : (-2 : ℝ) + -1 * -(3 / 2) = -(1 / 2 : ℝ) := by norm_num
      rw [he, Real.rpow_neg_one]
      congr 2
      field_simp
    _ = _ := subordination_laplace_scaled ht hr


def subordinationWeight (t s : ℝ) : ℝ :=
  s ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * t ^ 2 / s)

lemma weight_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (subordinationWeight t) (Ioi 0) := by
  let g : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t ^ 2 * u))
  have hg : IntegrableOn g (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
      (s := -(1 / 2 : ℝ)) (b := Real.pi * t ^ 2) (by norm_num) (by norm_num) (by positivity)
    simpa only [Real.rpow_one, neg_mul] using h
  have h := (integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)).mpr hg
  apply h.congr_fun _ measurableSet_Ioi
  intro u hu
  dsimp [g, subordinationWeight]
  simp only [abs_neg, abs_one, one_mul]
  rw [← Real.rpow_mul hu.le, ← mul_assoc, ← Real.rpow_add hu]
  norm_num
  rw [Real.rpow_neg_one]
  simp [div_eq_mul_inv]

lemma poisson_mixture {m : ℕ} {t : ℝ} (ht : 0 < t) (z : Space m) :
    poissonKernel m t z = t * ∫ s : ℝ in Ioi 0,
      subordinationWeight t s * P102.U3.gaussian m s z := by
  have hb : 0 < t ^ 2 + ‖z‖ ^ 2 := by positivity
  have he : (∫ s : ℝ in Ioi 0, subordinationWeight t s * P102.U3.gaussian m s z) =
      ∫ s : ℝ in Ioi 0, s ^ (-((m : ℝ) + 3) / 2) *
        Real.exp (-(Real.pi * (t ^ 2 + ‖z‖ ^ 2)) / s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp [subordinationWeight, P102.U3.gaussian, P102.Specs.U3.gaussianValue]
    calc
      _ = (s ^ (-(3 / 2 : ℝ)) * s ^ (-(m : ℝ) / 2)) *
          (Real.exp (-Real.pi * t ^ 2 / s) * Real.exp (-Real.pi * ‖z‖ ^ 2 / s)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hs, ← Real.exp_add]
        congr 2 <;> ring
  rw [he]
  have h := P102.U3.Riesz.inverse_gamma_integral
    (q := ((m : ℝ) + 1) / 2) (A := Real.pi * (t ^ 2 + ‖z‖ ^ 2))
    (by positivity) (by positivity)
  have hexp : -(((m : ℝ) + 1) / 2) - 1 = -((m : ℝ) + 3) / 2 := by ring
  rw [hexp] at h
  rw [h]
  rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le hb.le]
  unfold poissonKernel
  rw [P201.Elliptic.HalfSpaceLift.constant_eq]
  unfold P102.Specs.U3.Riesz.constantValue
  rw [neg_div, Real.rpow_neg hb.le]
  ring

lemma phase_norm {m : ℕ} (z ξ : Space m) : ‖fourierPhase z ξ‖ = 1 := by
  unfold fourierPhase
  rw [Complex.norm_exp]
  simp

lemma gaussian_pos (m : ℕ) {s : ℝ} (hs : 0 < s) (z : Space m) :
    0 < P102.U3.gaussian m s z := by
  unfold P102.U3.gaussian P102.Specs.U3.gaussianValue
  positivity

lemma weight_pos {t s : ℝ} (hs : 0 < s) : 0 < subordinationWeight t s := by
  unfold subordinationWeight
  positivity

lemma subordination_pi {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    t * (∫ s : ℝ in Ioi 0, subordinationWeight t s *
      Real.exp (-Real.pi * s * r ^ 2)) = Real.exp (-2 * Real.pi * t * r) := by
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hp2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have he : (∫ s : ℝ in Ioi 0, subordinationWeight t s * Real.exp (-Real.pi * s * r ^ 2)) =
      ∫ s : ℝ in Ioi 0, s ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(Real.sqrt Real.pi * t) ^ 2 / s - (Real.sqrt Real.pi * r) ^ 2 * s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only [subordinationWeight]
    rw [mul_assoc, ← Real.exp_add, mul_pow, mul_pow, hp2]
    congr 2
    ring
  rw [he, subordination_inverse (mul_pos hp ht) (mul_nonneg hp.le hr)]
  have hexp : -2 * (Real.sqrt Real.pi * t) * (Real.sqrt Real.pi * r) =
      -2 * Real.pi * t * r := by
    calc
      _ = -2 * (Real.sqrt Real.pi ^ 2) * t * r := by ring
      _ = _ := by rw [hp2]
  rw [hexp]
  field_simp

lemma kernel_fourier {m : ℕ} {t : ℝ} (ht : 0 < t) (ξ : Space m) :
    fourierIntegral (fun z => (poissonKernel m t z : ℂ)) ξ =
      (Real.exp (-2 * Real.pi * t * ‖ξ‖) : ℂ) := by
  let F : ℝ → Space m → ℂ := fun s z =>
    fourierPhase z ξ * (subordinationWeight t s * P102.U3.gaussian m s z : ℝ)
  have hnorm (s : ℝ) (hs : 0 < s) (z : Space m) :
      ‖F s z‖ = subordinationWeight t s * P102.U3.gaussian m s z := by
    dsimp [F]
    rw [norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (weight_pos hs) (gaussian_pos m hs z))]
  have hF : Integrable (Function.uncurry F) ((volume.restrict (Ioi 0)).prod volume) := by
    apply (integrable_prod_iff (by
      dsimp [F, fourierPhase, subordinationWeight, P102.U3.gaussian, P102.Specs.U3.gaussianValue]
      fun_prop)).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      apply ((P102.U3.gaussian_integrable m hs).const_mul (subordinationWeight t s)).mono'
        (by dsimp [F, fourierPhase, P102.U3.gaussian, P102.Specs.U3.gaussianValue]; fun_prop)
      exact Filter.Eventually.of_forall (fun z => (hnorm s hs z).le)
    · apply (weight_integrable ht).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      dsimp only [Function.uncurry]
      simp_rw [hnorm s hs]
      rw [integral_const_mul, P102.U3.gaussian_mass m hs, mul_one]
  have hswap := integral_integral_swap hF
  have hinner (s : ℝ) (hs : 0 < s) :
      (∫ z, F s z) = (subordinationWeight t s : ℂ) *
        (Real.exp (-Real.pi * s * ‖ξ‖ ^ 2) : ℂ) := by
    have hg := P102.U3.gaussian_fourier m hs ξ
    have he (z : Space m) : F s z = (subordinationWeight t s : ℂ) *
        (Complex.exp ((-2 * Real.pi * inner ℝ z ξ : ℝ) * Complex.I) *
          P102.U3.gaussianComplex m s z) := by
      dsimp [F, fourierPhase, P201Specs.fourierPhase, P102.U3.gaussianComplex, P102.Specs.U3.gaussianComplexValue,
        P102.U3.gaussian]
      push_cast
      ring
    simp_rw [he]
    rw [integral_const_mul, hg]
  calc
    _ = (t : ℂ) * ∫ z, ∫ s : ℝ in Ioi 0, F s z := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      have he : (∫ s : ℝ in Ioi 0, F s z) = fourierPhase z ξ *
          ((∫ s : ℝ in Ioi 0, subordinationWeight t s * P102.U3.gaussian m s z) : ℝ) := by
        dsimp [F]
        rw [integral_const_mul]
        congr 1
        convert! (integral_complex_ofReal (f := fun s =>
          subordinationWeight t s * P102.U3.gaussian m s z) (μ := volume.restrict (Ioi 0))) using 1
      rw [he, poisson_mixture ht z]
      push_cast
      ring
    _ = (t : ℂ) * ∫ s : ℝ in Ioi 0, ∫ z, F s z := by rw [hswap]
    _ = (t : ℂ) * ∫ s : ℝ in Ioi 0, (subordinationWeight t s : ℂ) *
        (Real.exp (-Real.pi * s * ‖ξ‖ ^ 2) : ℂ) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact hinner s hs
    _ = _ := by
      simp_rw [← Complex.ofReal_mul]
      have hi : (∫ s : ℝ in Ioi 0, (subordinationWeight t s *
          Real.exp (-Real.pi * s * ‖ξ‖ ^ 2) : ℝ) : ℂ) =
          ((∫ s : ℝ in Ioi 0, subordinationWeight t s * Real.exp (-Real.pi * s * ‖ξ‖ ^ 2)) : ℝ) := by
        convert! (integral_complex_ofReal (f := fun s =>
          subordinationWeight t s * Real.exp (-Real.pi * s * ‖ξ‖ ^ 2))
          (μ := volume.restrict (Ioi 0))) using 1
      rw [hi, ← Complex.ofReal_mul, subordination_pi ht (norm_nonneg ξ)]


lemma kernel_spatial_contDiff {m : ℕ} {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ⊤ (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t) := by
  unfold P201Specs.Elliptic.HalfSpaceLift.poissonKernel
  exact (contDiff_const.mul contDiff_const).mul
    ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
      (fun z => ne_of_gt (by positivity)))

lemma kernel_le_origin {m : ℕ} {t : ℝ} (ht : 0 < t) (z : Space m) :
    P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z ≤ P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t 0 := by
  simp only [P201Specs.Elliptic.HalfSpaceLift.poissonKernel, P201Specs.Elliptic.HalfSpaceLift.poissonKernel,
    norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  apply mul_le_mul_of_nonneg_left _ (mul_pos (constant_pos m) ht).le
  apply Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ht)
  · nlinarith [sq_nonneg ‖z‖]
  · have := Nat.cast_nonneg (α := ℝ) m
    linarith

lemma kernel_norm_bound {m : ℕ} {t : ℝ} (ht : 0 < t) (z : Space m) :
    ‖P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z‖ ≤ P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t 0 := by
  rw [Real.norm_of_nonneg (kernel_pos m ht z).le]
  exact kernel_le_origin ht z

lemma phase_integrable {m : ℕ} {f : Space m → ℂ} (hf : Integrable f) (ξ : Space m) :
    Integrable (fun z => fourierPhase z ξ * f z) := by
  apply hf.norm.mono' (by
    apply AEStronglyMeasurable.mul
    · exact (show Continuous (fun z : Space m => fourierPhase z ξ) by
        unfold fourierPhase P201Specs.fourierPhase
        fun_prop).aestronglyMeasurable
    · exact hf.aestronglyMeasurable)
  filter_upwards [] with z
  rw [norm_mul, phase_norm, one_mul]

lemma continuous_integrable_fourier_injective {m : ℕ} {f g : Space m → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hfc : Continuous f) (hgc : Continuous g)
    (he : FourierTransform.fourier f = FourierTransform.fourier g) : f = g := by
  let d : Space m → ℂ := fun x => f x - g x
  have hdi : Integrable d := hf.sub hg
  have hdc : Continuous d := hfc.sub hgc
  have hdz : FourierTransform.fourier d = 0 := by
    funext ξ
    rw [← P201.fourierNormalization]
    change (∫ z, fourierPhase z ξ * (f z - g z)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (phase_integrable hf ξ) (phase_integrable hg ξ)]
    change P201Specs.fourierIntegral f ξ - P201Specs.fourierIntegral g ξ = 0
    rw [P201.fourierNormalization, P201.fourierNormalization, he, sub_self]
  have hFdi : Integrable (FourierTransform.fourier d) := by rw [hdz]; exact integrable_zero _ _ _
  have hinv := hdc.fourierInv_fourier_eq hdi hFdi
  rw [hdz] at hinv
  have hi : d = 0 := by
    funext x
    have hx := congrFun hinv.symm x
    simpa only [Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero] using hx
  funext x
  have h := congrFun hi x
  exact sub_eq_zero.mp h

lemma kernel_convolution {m : ℕ} {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x : Space m) :
    Integrable (fun z => P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z * P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s (x - z)) volume ∧
      poissonIntegral (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s) t x = P201Specs.Elliptic.HalfSpaceLift.poissonKernel m (t + s) x := by
  have hti : Integrable (fun z : Space m => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z : ℂ)) :=
    (kernel_integrable m ht).ofReal
  have hsi : Integrable (fun z : Space m => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s z : ℂ)) :=
    (kernel_integrable m hs).ofReal
  have htc : Continuous (fun z : Space m => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z : ℂ)) :=
    Complex.continuous_ofReal.comp (kernel_spatial_contDiff ht).continuous
  have hsc : Continuous (fun z : Space m => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s z : ℂ)) :=
    Complex.continuous_ofReal.comp (kernel_spatial_contDiff hs).continuous
  let f : Space m → ℂ := fun z => P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z
  let g : Space m → ℂ := fun z => P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s z
  let h : Space m → ℂ := fun z => P201Specs.Elliptic.HalfSpaceLift.poissonKernel m (t + s) z
  let C : Space m → ℂ := MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume
  have hCi : Integrable C := hti.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hsi
  have hB : BddAbove (range fun z => ‖g z‖) := by
    refine ⟨P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s 0, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [g, Complex.norm_real] using kernel_norm_bound hs z
  have hCc : Continuous C := hB.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hti hsc
  have hhi : Integrable h := (kernel_integrable m (add_pos ht hs)).ofReal
  have hhc : Continuous h := Complex.continuous_ofReal.comp
    (kernel_spatial_contDiff (add_pos ht hs)).continuous
  have hF : FourierTransform.fourier C = FourierTransform.fourier h := by
    funext ξ
    dsimp [C]
    rw [Real.fourier_mul_convolution_eq hti hsi]
    rw [← P201.fourierNormalization, ← P201.fourierNormalization, ← P201.fourierNormalization]
    dsimp [f, g, h]
    have htF := kernel_fourier (m := m) ht ξ
    have hsF := kernel_fourier (m := m) hs ξ
    have haF := kernel_fourier (m := m) (add_pos ht hs) ξ
    change P201Specs.fourierIntegral (fun z => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z : ℂ)) ξ = _ at htF
    change P201Specs.fourierIntegral (fun z => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s z : ℂ)) ξ = _ at hsF
    change P201Specs.fourierIntegral (fun z => (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m (t + s) z : ℂ)) ξ = _ at haF
    rw [htF, hsF, haF, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have heq : C = h := continuous_integrable_fourier_injective hCi hhi hCc hhc hF
  refine ⟨poisson_integrand_integrable (kernel_spatial_contDiff hs).continuous
    (kernel_norm_bound hs) ht x, ?_⟩
  have hx := congrFun heq x
  have hcast : C x = (poissonIntegral (P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s) t x : ℂ) := by
    dsimp [C, MeasureTheory.convolution_def, f, g]
    simp only [← Complex.ofReal_mul]
    convert! (integral_complex_ofReal (f := fun z : Space m =>
      P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z * P201Specs.Elliptic.HalfSpaceLift.poissonKernel m s (x - z))) using 1
  rw [hcast] at hx
  exact Complex.ofReal_injective hx

lemma hasFDerivAt_integral_compact_param {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {p : Space n} (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ y, G q y)
      (∫ y, (fderiv ℝ (Function.uncurry G) (p,y)).comp
        (ContinuousLinearMap.inl ℝ (Space n) (Space m))) p := by
  let D := fun (q : Space n) (y : Space m) =>
    (fderiv ℝ (Function.uncurry G) (q,y)).comp
      (ContinuousLinearMap.inl ℝ (Space n) (Space m))
  have hDF : ContinuousOn (fderiv ℝ (Function.uncurry G)) (U ×ˢ univ) :=
    hG.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl
  have hD : ContinuousOn (Function.uncurry D) (U ×ˢ univ) := by
    exact hDF.clm_comp continuousOn_const
  have hpartial : ∀ q ∈ U, ∀ y, HasFDerivAt (fun r => G r y) (D q y) q := by
    intro q hq y
    exact ((hG.differentiableOn one_ne_zero).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hq, mem_univ y⟩)).hasFDerivAt.comp q
        (hasFDerivAt_prodMk_left q y)
  have hDzero : ∀ q ∈ U, ∀ y, y ∉ K → D q y = 0 := by
    intro q hq y hy
    have he : (fun r => G r y) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hq] with r hr using hzero r hr y hy
    rw [← (hpartial q hq y).fderiv, he.fderiv_eq]
    exact (hasFDerivAt_const (0 : ℝ) q).fderiv
  have hGc : ∀ q ∈ U, Continuous (G q) := by
    intro q hq
    exact hG.continuousOn.comp_continuous (.prodMk_right q) (fun y => ⟨hq, mem_univ y⟩)
  have hDc : ∀ q ∈ U, Continuous (D q) := by
    intro q hq
    exact hD.comp_continuous (.prodMk_right q) (fun y => ⟨hq, mem_univ y⟩)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
  let ε : ℝ := r / 2
  have hε : 0 < ε := half_pos hr
  have hclosed : closedBall p ε ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hprod : closedBall p ε ×ˢ K ⊆ U ×ˢ univ :=
    Set.prod_mono hclosed (subset_univ _)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p ε).prod hK).exists_bound_of_continuousOn
    (hD.mono hprod)
  let bound : Space m → ℝ := K.indicator (fun _ => C)
  have hb : Integrable bound volume := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_ne_top
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := D) (bound := bound) (Metric.ball_mem_nhds p hε)
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (hGc q hq).aestronglyMeasurable
  · exact (hGc p hp).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (hzero p hp))
  · exact (hDc p hp).aestronglyMeasurable
  · filter_upwards [] with y q hq
    by_cases hy : y ∈ K
    · simpa only [bound, indicator_of_mem hy, Function.uncurry] using hC (q,y) ⟨ball_subset_closedBall hq,hy⟩
    · rw [hDzero q (hclosed (ball_subset_closedBall hq)) y hy]
      simp [bound, hy]
  · exact hb
  · filter_upwards [] with y q hq
    exact hpartial q (hclosed (ball_subset_closedBall hq)) y


lemma harmonicLift_differentiableAt_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    {p : Space (m+1)} (hp : p ∈ openHalfSpace m) :
    DifferentiableAt ℝ (harmonicLift g) p := by
  let U : Set (Space (m+1)) := openHalfSpace m ∩ ball p 1
  let K : Set (Space m) := (horizontal '' closedBall p 1) - tsupport g
  let G := fun (q : Space (m+1)) (z : Space m) =>
    poissonKernel m (height q) z * g (horizontal q-z)
  have hU : IsOpen U := (isOpen_openHalfSpace m).inter isOpen_ball
  have hpU : p ∈ U := ⟨hp, mem_ball_self zero_lt_one⟩
  have hK : IsCompact K := by
    change IsCompact ((horizontal '' closedBall p 1) - tsupport g)
    rw [sub_eq_add_neg]
    exact ((isCompact_closedBall p 1).image
      (P201.Elliptic.HalfSpaceLift.horizontal_contDiff m).continuous).add (show IsCompact (tsupport g) from hgs).neg
  have hzero : ∀ q ∈ U, ∀ z, z ∉ K → G q z = 0 := by
    intro q hq z hz
    have hgzero : g (horizontal q-z) = 0 := by
      by_contra hne
      apply hz
      refine ⟨horizontal q, ⟨q, ball_subset_closedBall hq.2, rfl⟩,
        horizontal q-z, subset_tsupport g hne, ?_⟩
      simp
    simp [G, hgzero]
  have hheight : ContDiff ℝ 1 (fun q : Space (m+1) × Space m => height q.1) :=
    ((P201.Elliptic.HalfSpaceLift.height_contDiff m).of_le le_top).comp contDiff_fst
  have hbase : ContDiff ℝ 1 (fun q : Space (m+1) × Space m =>
      height q.1 ^ 2 + ‖q.2‖ ^ 2) :=
    (hheight.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have harg : ContDiff ℝ 1 (fun q : Space (m+1) × Space m => horizontal q.1-q.2) :=
    (((P201.Elliptic.HalfSpaceLift.horizontal_contDiff m).of_le le_top).comp contDiff_fst).sub
      contDiff_snd
  have hG : ContDiffOn ℝ 1 (Function.uncurry G) (U ×ˢ univ) := by
    intro q hq
    have ht : 0 < height q.1 := hq.1.1
    exact (((contDiffWithinAt_const.mul hheight.contDiffWithinAt).mul
      (hbase.contDiffWithinAt.rpow_const_of_ne (by positivity))).mul
      (hg.comp harg).contDiffWithinAt)
  have hd := (hasFDerivAt_integral_compact_param hU hK hG hzero hpU).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_openHalfSpace m).mem_nhds hp] with q hq
  have hq' : 0 < height q := hq
  simp only [harmonicLift, ite_eq_left hq', poissonIntegral, G]


lemma point_add_tangent {m : ℕ} (x : Space m) (t s : ℝ) (i : Fin m) :
    point (x+s • coordinate m i) t =
      point x t+s • coordinate (m+1) i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply]
  · by_cases h : k = i
    · subst k
      simp [point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
        EuclideanSpace.basisFun_apply]
    · simp [point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
        EuclideanSpace.basisFun_apply, h]

lemma harmonicLift_tangent_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) (i : Fin m) :
    fderiv ℝ (harmonicLift g) (point x t) (coordinate (m+1) i.castSucc) =
      poissonIntegral (tangent g i) t x := by
  have hp : point x t ∈ openHalfSpace m := by
    simpa [openHalfSpace] using ht
  have hA := (harmonicLift_differentiableAt_open hgs hg hp).hasFDerivAt
  have hcurve : HasDerivAt
      (fun s : ℝ => point x t+s • coordinate (m+1) i.castSucc)
      (coordinate (m+1) i.castSucc) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinate (m+1) i.castSucc)).const_add (point x t)
  have hcurveX : HasDerivAt (fun s : ℝ => x+s • coordinate m i) (coordinate m i) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinate m i)).const_add x
  have hk := (P201.Elliptic.HalfSpaceLift.kernel_integrable m ht).locallyIntegrable
  have hP := hgs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hg x
  have hfirst : HasDerivAt
      (harmonicLift g ∘ (fun s : ℝ => point x t+s • coordinate (m+1) i.castSucc))
      (fderiv ℝ (harmonicLift g) (point x t) (coordinate (m+1) i.castSucc)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 ?_ hcurve
    simpa only [zero_smul, add_zero] using hA
  have hsecond : HasDerivAt
      ((poissonKernel m t ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ∘
        (fun s : ℝ => x+s • coordinate m i))
      (((poissonKernel m t ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (Space m), volume]
        fderiv ℝ g) x) (coordinate m i)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 ?_ hcurveX
    simpa only [zero_smul, add_zero] using hP
  have heq : (harmonicLift g ∘ (fun s : ℝ => point x t+s • coordinate (m+1) i.castSucc)) =
      ((poissonKernel m t ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) ∘
        (fun s : ℝ => x+s • coordinate m i)) := by
    funext s
    dsimp only [Function.comp_apply]
    rw [← point_add_tangent]
    rw [P201.Elliptic.HalfSpaceLift.lift_positive g _ ht]
    rfl
  rw [heq] at hfirst
  have hval := hfirst.unique hsecond
  simpa only [zero_smul, add_zero, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply', tangent, poissonIntegral] using
    hval.trans (convolution_precompR_apply _ hk (hgs.fderiv ℝ)
      (hg.continuous_fderiv one_ne_zero) x (coordinate m i))


/-- The quantitative moment estimate gives the actual one-sided trace. -/
lemma poisson_tendsto_boundary {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hb : Continuous b) (hM : ∀ x, ‖b x‖ ≤ M)
    (hH : ∀ x y, ‖b x - b y‖ ≤ H * dist x y ^ α) (x : Space m) :
    Tendsto (fun t => poissonIntegral b t x) (𝓝[>] 0) (𝓝 (b x)) := by
  have hp : Tendsto (fun t : ℝ => t ^ α) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hα.ne'] using hi.rpow_const (Or.inr hα.le)
  have he : Tendsto (fun t => poissonIntegral b t x - b x) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun t => (∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * t ^ α)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact poisson_approximation_bound hα hα1 hb hM hH ht x
    · simpa only [mul_zero] using hp.const_mul ((∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H)
  have hh := he.add_const (b x)
  simpa only [sub_add_cancel, zero_add] using hh

/-- The closed representative has a genuine boundary trace even when the
horizontal point moves with the height. It is continuous from both sides. -/
lemma lift_continuousAt_boundary {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hB :
      P201Specs.Elliptic.HolderCancellation.HolderBounds α b M H) (x : Space m) :
    ContinuousAt (harmonicLift b) (point x 0) := by
  obtain ⟨hM, hH, hsup, hhol⟩ := hB
  have hb := P201.Elliptic.HolderCancellation.holder_continuous hα
    (show P201Specs.Elliptic.HolderCancellation.IsHolder α b from
      ⟨M, H, hM, hH, hsup, hhol⟩)
  let J := ∫ z, ‖z‖ ^ α * poissonKernel m 1 z
  have hJ : 0 ≤ J := integral_nonneg (fun z =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (kernel_pos m zero_lt_one z).le)
  have hbound : ∀ p : Space (m + 1),
      ‖harmonicLift b p - b x‖ ≤
        J * H * |height p| ^ α + H * dist (horizontal p) x ^ α := by
    intro p
    by_cases hp : 0 < height p
    · rw [harmonicLift, ite_eq_left hp]
      calc
        ‖poissonIntegral b (height p) (horizontal p) - b x‖ ≤
            ‖poissonIntegral b (height p) (horizontal p) - b (horizontal p)‖ +
              ‖b (horizontal p) - b x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by
          rw [abs_of_pos hp]
          exact add_le_add (poisson_approximation_bound hα hα1 hb hsup hhol hp _) (hhol _ _)
    · rw [harmonicLift, ite_eq_right hp]
      exact (hhol _ _).trans (le_add_of_nonneg_left (by positivity))
  have ht : Tendsto (fun p : Space (m + 1) => |height p| ^ α)
      (𝓝 (point x 0)) (𝓝 0) := by
    have hh : Tendsto (fun p : Space (m + 1) => |height p|)
        (𝓝 (point x 0)) (𝓝 (0 : ℝ)) := by
      simpa only [height_point, abs_zero] using ((height_contDiff m).continuous.tendsto (point x 0)).abs
    simpa only [Real.zero_rpow hα.ne'] using hh.rpow_const (Or.inr hα.le)
  have hx : Tendsto (fun p : Space (m + 1) => dist (horizontal p) x ^ α)
      (𝓝 (point x 0)) (𝓝 0) := by
    have hh : Tendsto (fun p : Space (m + 1) => dist (horizontal p) x)
        (𝓝 (point x 0)) (𝓝 (0 : ℝ)) := by
      simpa only [horizontal_point, dist_self] using
        (((horizontal_contDiff m).continuous.tendsto (point x 0)).dist
          (tendsto_const_nhds (x := x)))
    simpa only [Real.zero_rpow hα.ne'] using hh.rpow_const (Or.inr hα.le)
  have he : Tendsto (fun p => harmonicLift b p - b x) (𝓝 (point x 0)) (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa only [mul_zero, zero_add] using
      ((ht.const_mul (J * H)).add (hx.const_mul H)))
  change Tendsto (harmonicLift b) (𝓝 (point x 0)) (𝓝 (harmonicLift b (point x 0)))
  rw [lift_boundary]
  simpa only [sub_add_cancel, zero_add] using he.add_const (b x)

/-- Continuity proves that the prescribed representative is the actual trace. -/
theorem boundaryTrace : P201Specs.Elliptic.HalfSpaceLift.boundaryTraceStatement := by
  intro m hm α hα hα1 b hb x
  obtain ⟨M, H, hB⟩ := hb
  exact ⟨lift_continuousAt_boundary hα hα1 hB x, lift_boundary b x⟩

/-- Exported part of the original conclusion, now with no extra derivative hypotheses. -/
theorem normalTracesHolder : P201Specs.Elliptic.HalfSpaceLift.normalTracesHolderStatement := by
  intro m hm α hα hα1 g hs hg
  exact normalTraces_holder hm hα hα1 hs hg

theorem kernelRegularity : P201Specs.Elliptic.HalfSpaceLift.kernelRegularityStatement := by
  intro m hm
  exact ⟨(kernel_contDiff m).of_le (by simp), kernel_harmonic m⟩

theorem kernelSemigroup : P201Specs.Elliptic.HalfSpaceLift.kernelSemigroupStatement := by
  intro m hm
  exact ⟨(kernel_contDiff m).of_le (by simp), kernel_harmonic m,
    fun t ht ξ => kernel_fourier ht ξ,
    fun t s ht hs x => kernel_convolution ht hs x⟩

theorem tangentialConvolution : P201Specs.Elliptic.HalfSpaceLift.tangentialConvolutionStatement := by
  intro m hm g hs hg t ht
  exact ⟨poissonIntegral_contDiff hs hg ht,
    fun x j => poissonIntegral_tangent hs (hg.of_le (by norm_num)) ht x j,
    fun x i j => poissonIntegral_tangent_tangent hs hg ht x i j⟩

theorem normalTracesQuantitative :
    P201Specs.Elliptic.HalfSpaceLift.normalTracesQuantitativeStatement := by
  intro m hm α hα hα1 R hR
  exact normalTraces_quantitative hm hα hα1 hR

theorem tangentialLift : P201Specs.Elliptic.HalfSpaceLift.tangentialLiftStatement := by
  intro m hm g hs hg
  exact ⟨fun p hp => harmonicLift_differentiableAt_open hs hg hp,
    fun t ht x j => harmonicLift_tangent_open hs hg ht x j⟩

abbrev poissonProfile : P201Specs.Elliptic.HalfSpaceLift.poissonProfileType := @P201Specs.Elliptic.HalfSpaceLift.poissonProfile
abbrev poissonConstant : P201Specs.Elliptic.HalfSpaceLift.poissonConstantType := @P201Specs.Elliptic.HalfSpaceLift.poissonConstant
abbrev poissonKernel : P201Specs.Elliptic.HalfSpaceLift.poissonKernelType := @P201Specs.Elliptic.HalfSpaceLift.poissonKernel
abbrev poissonIntegral : P201Specs.Elliptic.HalfSpaceLift.poissonIntegralType := @P201Specs.Elliptic.HalfSpaceLift.poissonIntegral
abbrev harmonicLift : P201Specs.Elliptic.HalfSpaceLift.harmonicLiftType := @P201Specs.Elliptic.HalfSpaceLift.harmonicLift
abbrev rieszKernel : P201Specs.Elliptic.HalfSpaceLift.rieszKernelType := @P201Specs.Elliptic.HalfSpaceLift.rieszKernel
abbrev normalGenerator : P201Specs.Elliptic.HalfSpaceLift.normalGeneratorType := @P201Specs.Elliptic.HalfSpaceLift.normalGenerator

lemma real_odd_riesz_integrable {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    (i : Fin m) {b : Space m → ℝ} (hs : HasCompactSupport b) (hb : IsHolder α b)
    (x : Space m) :
    Integrable (fun z => rieszKernel m i z * (b (x-z)-b (x+z)) / 2) volume := by
  let C := compensatedIntegrand (rieszKernel m i) b x
  have hc : Integrable C volume :=
    P201.Elliptic.HolderCancellation.compensated_integrable hm hα (riesz_hypotheses hm i) hs hb x
  have he (z : Space m) :
      rieszKernel m i z * (b (x-z)-b (x+z)) / 2 = (C z + C (-z))/2 := by
    have ho : rieszKernel m i (-z) = -rieszKernel m i z :=
      P102.U3.Riesz.kernel_odd i z
    have hz : (-z ∈ ball (0 : Space m) 1) ↔ z ∈ ball (0 : Space m) 1 := by simp
    dsimp only [C, compensatedIntegrand]
    rw [ho]
    by_cases h : z ∈ ball (0 : Space m) 1
    · simp only [indicator_of_mem h, indicator_of_mem (hz.mpr h), sub_neg_eq_add]
      ring
    · simp only [indicator_of_notMem h, indicator_of_notMem (fun hn => h (hz.mp hn)), sub_neg_eq_add]
      ring
  simp_rw [he]
  exact (hc.add hc.comp_neg).div_const 2

lemma real_odd_riesz_value {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (i : Fin m) {b : Space m → ℝ} (hs : HasCompactSupport b) (hb : IsHolder α b)
    (x : Space m) :
    principalValue (rieszKernel m i) b x =
      ∫ z, rieszKernel m i z * (b (x-z)-b (x+z)) / 2 := by
  let C := compensatedIntegrand (rieszKernel m i) b x
  have hc : Integrable C volume :=
    P201.Elliptic.HolderCancellation.compensated_integrable hm hα (riesz_hypotheses hm i) hs hb x
  have he (z : Space m) :
      rieszKernel m i z * (b (x-z)-b (x+z)) / 2 = (C z + C (-z))/2 := by
    have ho : rieszKernel m i (-z) = -rieszKernel m i z :=
      P102.U3.Riesz.kernel_odd i z
    have hz : (-z ∈ ball (0 : Space m) 1) ↔ z ∈ ball (0 : Space m) 1 := by simp
    dsimp only [C, compensatedIntegrand]
    rw [ho]
    by_cases h : z ∈ ball (0 : Space m) 1
    · simp only [indicator_of_mem h, indicator_of_mem (hz.mpr h), sub_neg_eq_add]
      ring
    · simp only [indicator_of_notMem h, indicator_of_notMem (fun hn => h (hz.mp hn)), sub_neg_eq_add]
      ring
  rw [(P201.Elliptic.HolderCancellation.principalValueExists hm α hα hα1
    (rieszKernel m i) b (riesz_hypotheses hm i) hs hb x).2.2.2]
  simp_rw [he]
  rw [integral_div, integral_add hc hc.comp_neg,
    (Measure.measurePreserving_neg (volume : Measure (Space m))).integral_comp
      (MeasurableEquiv.neg _).measurableEmbedding C]
  change (∫ z, C z) = ((∫ z, C z)+(∫ z, C z))/2
  ring

lemma complex_odd_riesz_integrable {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    (i : Fin m) {b : Space m → ℝ} (hs : HasCompactSupport b) (hb : IsHolder α b)
    (x : Space m) :
    Integrable (P102.U3.Riesz.oddIntegrand i (fun x => (b x : ℂ)) x) volume := by
  convert (real_odd_riesz_integrable hm hα i hs hb x).ofReal (𝕜 := ℂ) using 1
  funext z
  simp only [P102.U3.Riesz.oddIntegrand, P102.U3.Riesz.kernel, rieszKernel]
  push_cast
  rfl

lemma complex_odd_riesz_value {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (i : Fin m) {b : Space m → ℝ} (hs : HasCompactSupport b) (hb : IsHolder α b)
    (x : Space m) :
    P102.U3.Riesz.principalValue m i (fun x => (b x : ℂ)) x =
      ((principalValue (rieszKernel m i) b x : ℝ) : ℂ) := by
  rw [real_odd_riesz_value hm hα hα1 i hs hb x, ← integral_complex_ofReal]
  apply integral_congr_ae
  exact .of_forall fun z => by
    simp only [P102.U3.Riesz.oddIntegrand, P102.U3.Riesz.kernel, rieszKernel]
    push_cast
    rfl

lemma holder_heatOddIntegral_tendsto {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 < α)
    (i : Fin m) {b : Space m → ℝ} (hs : HasCompactSupport b) (hb : IsHolder α b)
    (x : Space m) :
    Tendsto (fun n => ∫ z, P102.U3.Riesz.heatOddIntegrand i n (fun x => (b x : ℂ)) x z)
      atTop (𝓝 (P102.U3.Riesz.principalValue m i (fun x => (b x : ℂ)) x)) := by
  let f := fun x => (b x : ℂ)
  have hf : Continuous f := Complex.continuous_ofReal.comp
    (P201.Elliptic.HolderCancellation.holder_continuous hα hb)
  have hi := complex_odd_riesz_integrable hm hα i hs hb x
  apply tendsto_integral_of_dominated_convergence
    (fun z => ‖P102.U3.Riesz.oddIntegrand i f x z‖)
  · intro n
    have hm : Measurable (P102.U3.Riesz.heatOddIntegrand i n f x) := by
      unfold P102.U3.Riesz.heatOddIntegrand
      exact ((P102.U3.Riesz.heatKernel_measurable i n).complex_ofReal.mul
        ((hf.measurable.comp (by fun_prop)).sub
          (hf.measurable.comp (by fun_prop)))).div_const 2
    exact hm.aestronglyMeasurable
  · exact hi.norm
  · exact fun n => .of_forall (P102.U3.Riesz.heatOddIntegrand_norm_le i n f x)
  · apply Eventually.of_forall
    intro z
    have hl := ((Complex.continuous_ofReal.tendsto _).comp
      (P102.U3.Riesz.heatKernel_tendsto i z)).mul_const ((f (x-z)-f (x+z))/2)
    simpa [P102.U3.Riesz.heatOddIntegrand, P102.U3.Riesz.oddIntegrand,
      div_eq_mul_inv, mul_assoc] using hl

set_option maxHeartbeats 800000 in
lemma holder_rieszL2_identification {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (i : Fin m) {b : Space m → ℝ}
    (hs : HasCompactSupport b) (hb : IsHolder α b) :
    ∃ (hf : MemLp (fun x => (b x : ℂ)) 2 volume)
      (hg : MemLp (fun x => ((principalValue (rieszKernel m i) b x : ℝ) : ℂ)) 2 volume),
      hg.toLp _ = P102.U3.Riesz.rieszL2 i (hf.toLp _) := by
  let f := fun x => (b x : ℂ)
  have hfc : HasCompactSupport f := hs.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hcont : Continuous f := Complex.continuous_ofReal.comp
    (P201.Elliptic.HolderCancellation.holder_continuous hα hb)
  have hf2 : MemLp f 2 volume := hcont.memLp_of_hasCompactSupport hfc
  have hf1 : Integrable f := hcont.integrable_of_hasCompactSupport hfc
  have hc (n : ℕ) := (P102.U3.Riesz.heatConvolution_L2 i n
    (P102.U3.Riesz.heatKernel_complex_integrable i n)
    (P102.U3.Riesz.heatKernel_fourier i n) hf2 hf1).choose
  have hceq (n : ℕ) : (hc n).toLp _ = P102.U3.Riesz.heatRieszL2 i n (hf2.toLp f) :=
    (P102.U3.Riesz.heatConvolution_L2 i n
      (P102.U3.Riesz.heatKernel_complex_integrable i n)
      (P102.U3.Riesz.heatKernel_fourier i n) hf2 hf1).choose_spec
  have hlp : Tendsto (fun n => (hc n).toLp _) atTop
      (𝓝 (P102.U3.Riesz.rieszL2 i (hf2.toLp f))) := by
    simp_rw [hceq]
    exact P102.U3.Riesz.heatRieszL2_tendsto i _
  have hpoint (x : Space m) : Tendsto (fun n => P102.U3.Riesz.heatConvolution i n f x)
      atTop (𝓝 (((principalValue (rieszKernel m i) b x : ℝ) : ℂ))) := by
    simp_rw [P102.U3.Riesz.heatConvolution_eq_odd i _
      (P102.U3.Riesz.heatKernel_complex_integrable i _) hcont hfc]
    rw [← complex_odd_riesz_value hm hα hα1 i hs hb x]
    exact holder_heatOddIntegral_tendsto hm hα i hs hb x
  obtain ⟨hg, hgeq⟩ := P102.U3.Riesz.identify_Lp_limit_of_pointwise
    (fun n => P102.U3.Riesz.heatConvolution i n f) hc
    (P102.U3.Riesz.rieszL2 i (hf2.toLp f))
    (fun x => ((principalValue (rieszKernel m i) b x : ℝ) : ℂ)) hlp hpoint
  exact ⟨hf2, hg, hgeq⟩


lemma poisson_action_semigroup {m : ℕ} {b : Space m → ℝ} (hb : Continuous b)
    {M t s : ℝ} (hM : ∀ x, ‖b x‖ ≤ M) (ht : 0 < t) (hs : 0 < s) (x : Space m) :
    poissonIntegral b (t+s) x = poissonIntegral (poissonIntegral b s) t x := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hdom : Integrable (fun p : Space m × Space m =>
      poissonKernel m t p.2 * poissonKernel m s (p.1-p.2)) (volume.prod volume) :=
    (kernel_integrable m ht).convolution_integrand L (kernel_integrable m hs)
  have hi : Integrable (Function.uncurry fun u z : Space m =>
      poissonKernel m t z * (poissonKernel m s (u-z) * b (x-u))) (volume.prod volume) := by
    apply (hdom.const_mul M).mono' ?_ ?_
    · exact (by
        have hc : Continuous (fun p : Space m × Space m =>
            poissonKernel m t p.2 * (poissonKernel m s (p.1-p.2) * b (x-p.1))) :=
          (((kernel_spatial_contDiff ht).continuous.comp continuous_snd).mul
            (((kernel_spatial_contDiff hs).continuous.comp (continuous_fst.sub continuous_snd)).mul
              (hb.comp (continuous_const.sub continuous_fst))))
        exact hc.aestronglyMeasurable)
    · filter_upwards [] with p
      change ‖poissonKernel m t p.2 * (poissonKernel m s (p.1-p.2) * b (x-p.1))‖ ≤
        M * (poissonKernel m t p.2 * poissonKernel m s (p.1-p.2))
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (kernel_pos m ht p.2).le,
        Real.norm_of_nonneg (kernel_pos m hs (p.1-p.2)).le]
      calc
        _ ≤ poissonKernel m t p.2 * (poissonKernel m s (p.1-p.2) * M) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hM _) (kernel_pos m hs _).le) (kernel_pos m ht _).le
        _ = _ := by ring
  have ha := convolution_assoc' L L L L (fun a b c => mul_assoc a b c)
    (Filter.Eventually.of_forall (fun y => (kernel_convolution ht hs y).1))
    (Filter.Eventually.of_forall (fun y => poisson_integrand_integrable hb hM hs y)) hi
  have hfg : (poissonKernel m t ⋆[L, volume] poissonKernel m s) = poissonKernel m (t+s) := by
    funext y
    exact (kernel_convolution ht hs y).2
  rw [hfg] at ha
  exact ha

lemma poisson_height_increment {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H t s : ℝ} (hB : HolderBounds α b M H)
    (ht : 0 < t) (hs : 0 < s) (x : Space m) :
    ‖poissonIntegral b (t+s) x - poissonIntegral b t x‖ ≤
      (∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * s ^ α := by
  obtain ⟨hM, hH, hsup, hhol⟩ := hB
  have hb := P201.Elliptic.HolderCancellation.holder_continuous hα
    (show IsHolder α b from ⟨M, H, hM, hH, hsup, hhol⟩)
  have hPs : HolderBounds α (poissonIntegral b s) M H :=
    ⟨hM, hH, poisson_sup_bound b hsup hs, poisson_spatial_holder hb hsup hhol hs⟩
  have hbs := P201.Elliptic.HolderCancellation.holder_continuous hα
    (show IsHolder α (poissonIntegral b s) from ⟨M, H, hPs⟩)
  rw [poisson_action_semigroup hb hsup ht hs]
  have he : poissonIntegral (poissonIntegral b s) t x - poissonIntegral b t x =
      poissonIntegral (fun y => poissonIntegral b s y - b y) t x := by
    change (∫ z, poissonKernel m t z * poissonIntegral b s (x-z)) -
      (∫ z, poissonKernel m t z * b (x-z)) =
      ∫ z, poissonKernel m t z * (poissonIntegral b s (x-z) - b (x-z))
    rw [← integral_sub (poisson_integrand_integrable hbs hPs.2.2.1 ht x)
      (poisson_integrand_integrable hb hsup ht x)]
    congr 1
    funext z
    ring
  rw [he]
  exact poisson_sup_bound _ (poisson_approximation_bound hα hα1 hb hsup hhol hs) ht x

lemma lift_height_holder {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hB : HolderBounds α b M H)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : Space m) :
    ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point x t) - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point x s)‖ ≤
      (∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * |t-s| ^ α := by
  let J := ∫ z, ‖z‖ ^ α * poissonKernel m 1 z
  have hJ : 0 ≤ J := integral_nonneg (fun z =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (kernel_pos m zero_lt_one z).le)
  have hb := P201.Elliptic.HolderCancellation.holder_continuous hα
    (show IsHolder α b from ⟨M, H, hB⟩)
  have hord : ∀ u v : ℝ, 0 ≤ v → v ≤ u →
      ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point x u) - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point x v)‖ ≤ J * H * |u-v| ^ α := by
    intro u v hv hvu
    by_cases heq : u = v
    · subst u
      simp only [sub_self, norm_zero, abs_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
    have huv : 0 < u-v := sub_pos.mpr (lt_of_le_of_ne hvu (Ne.symm heq))
    have hu : 0 < u := lt_of_le_of_lt hv (sub_pos.mp huv)
    rw [lift_positive b x hu, abs_of_pos huv]
    by_cases hv0 : v = 0
    · subst v
      rw [lift_boundary, sub_zero]
      exact poisson_approximation_bound hα hα1 hb hB.2.2.1 hB.2.2.2 hu x
    · have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
      rw [lift_positive b x hv']
      have hsum : v+(u-v) = u := by ring
      simpa only [hsum] using poisson_height_increment hα hα1 hB hv' huv x
  by_cases hst : s ≤ t
  · exact hord t s hs hst
  · simpa only [norm_sub_rev, abs_sub_comm] using hord s t ht (le_of_not_ge hst)

lemma lift_spatial_holder {m : ℕ} {α : ℝ} (hα : 0 < α)
    {b : Space m → ℝ} {M H : ℝ} (hB : HolderBounds α b M H)
    (t : ℝ) (x y : Space m) :
    ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point x t) - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point y t)‖ ≤ H * dist x y ^ α := by
  by_cases ht : 0 < t
  · rw [lift_positive b x ht, lift_positive b y ht]
    have hb := P201.Elliptic.HolderCancellation.holder_continuous hα
      (show IsHolder α b from ⟨M, H, hB⟩)
    exact poisson_spatial_holder hb hB.2.2.1 hB.2.2.2 ht x y
  · simpa [P201Specs.Elliptic.HalfSpaceLift.harmonicLift, P201Specs.Elliptic.HalfSpaceLift.harmonicLift, ht] using hB.2.2.2 x y

lemma horizontal_dist_le {m : ℕ} (p q : Space (m+1)) :
    dist (horizontal p) (horizontal q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm]
  convert horizontal_norm_le (p-q) using 1
  rfl

lemma height_dist_le {m : ℕ} (p q : Space (m+1)) :
    |height p - height q| ≤ dist p q := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs, height] using
    PiLp.norm_apply_le (p-q) (Fin.last m)

lemma lift_sup_bound {m : ℕ} {b : Space m → ℝ} {M : ℝ}
    (hb : ∀ x, ‖b x‖ ≤ M) (p : Space (m+1)) : ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p‖ ≤ M := by
  by_cases ht : 0 < height p
  · change ‖if 0 < height p then _ else _‖ ≤ M
    rw [ite_eq_left ht]
    exact poisson_sup_bound b hb ht _
  · change ‖if 0 < height p then _ else _‖ ≤ M
    rw [ite_eq_right ht]
    exact hb _

lemma lift_joint_holder {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hB : HolderBounds α b M H)
    {p q : Space (m+1)} (hp : p ∈ closedHalfSpace m) (hq : q ∈ closedHalfSpace m) :
    ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b q‖ ≤
      (1 + ∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * dist p q ^ α := by
  let J := ∫ z, ‖z‖ ^ α * poissonKernel m 1 z
  have hJ : 0 ≤ J := integral_nonneg (fun z =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (kernel_pos m zero_lt_one z).le)
  have hH : 0 ≤ H := hB.2.1
  calc
    ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b q‖ ≤
      ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point (horizontal q) (height p))‖ +
      ‖P201Specs.Elliptic.HalfSpaceLift.harmonicLift b (point (horizontal q) (height p)) - P201Specs.Elliptic.HalfSpaceLift.harmonicLift b q‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ H * dist (horizontal p) (horizontal q) ^ α + J * H * |height p-height q| ^ α := by
      apply add_le_add
      · simpa only [point_horizontal_height] using lift_spatial_holder hα hB (height p) (horizontal p) (horizontal q)
      · simpa only [point_horizontal_height] using lift_height_holder hα hα1 hB hp hq (horizontal q)
    _ ≤ H * dist p q ^ α + J * H * dist p q ^ α := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (dist_nonneg) (horizontal_dist_le p q) hα.le) hH
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (height_dist_le p q) hα.le) (mul_nonneg hJ hH)
    _ = _ := by dsimp [J]; ring

lemma lift_continuousOn_closed {m : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {b : Space m → ℝ} {M H : ℝ} (hB : HolderBounds α b M H) :
    ContinuousOn (P201Specs.Elliptic.HalfSpaceLift.harmonicLift b) (closedHalfSpace m) := by
  intro p hp
  change Tendsto (P201Specs.Elliptic.HalfSpaceLift.harmonicLift b) (𝓝[closedHalfSpace m] p)
    (𝓝 (P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p))
  have hd : Tendsto (fun q : Space (m+1) => dist q p ^ α)
      (𝓝[closedHalfSpace m] p) (𝓝 0) := by
    have hi : Tendsto (fun q : Space (m+1) => dist q p)
        (𝓝[closedHalfSpace m] p) (𝓝 0) := by
      have hi : Tendsto (fun q : Space (m+1) => q) (𝓝[closedHalfSpace m] p) (𝓝 p) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [dist_self] using hi.dist (tendsto_const_nhds (x := p))
    simpa only [Real.zero_rpow hα.ne'] using hi.rpow_const (Or.inr hα.le)
  have he : Tendsto (fun q => P201Specs.Elliptic.HalfSpaceLift.harmonicLift b q -
      P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p) (𝓝[closedHalfSpace m] p) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun q =>
      (1 + ∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H * dist q p ^ α)
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact lift_joint_holder hα hα1 hB hq hp
    · simpa only [mul_zero] using hd.const_mul ((1 + ∫ z, ‖z‖ ^ α * poissonKernel m 1 z) * H)
  simpa only [sub_add_cancel, zero_add] using
    he.add_const (P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p)


set_option maxHeartbeats 800000 in
lemma tangent_fourier {m : ℕ} {b : Space m → ℝ}
    (hs : HasCompactSupport b) (hb : ContDiff ℝ 1 b) (i : Fin m) (ξ : Space m) :
    𝓕 (fun x => (tangent b i x : ℂ)) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * 𝓕 (fun x => (b x : ℂ)) ξ := by
  let f : Space m → ℂ := fun x => (b x : ℂ)
  have hf : ContDiff ℝ 1 f := Complex.ofRealCLM.contDiff.comp hb
  have hfs : HasCompactSupport f := hs.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hf1 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfs
  have hdf : Integrable (fderiv ℝ f) :=
    (hf.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hfs.fderiv ℝ)
  have hder (x : Space m) : fderiv ℝ f x (coordinate m i) = (tangent b i x : ℂ) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x ((hb.differentiable one_ne_zero x).hasFDerivAt)
    have hh : fderiv ℝ f x = Complex.ofRealCLM.comp (fderiv ℝ b x) := h.fderiv
    rw [hh]
    rfl
  rw [← show (fun x => fderiv ℝ f x (coordinate m i)) =
    (fun x => (tangent b i x : ℂ)) from funext hder]
  rw [← Real.fourier_continuousLinearMap_apply hdf, Real.fourier_fderiv hf1
    (hf.differentiable one_ne_zero) hdf, VectorFourier.fourierSMulRight_apply]
  change -(2 * (Real.pi : ℂ) * Complex.I) • (-(innerSL ℝ ξ (coordinate m i)) • 𝓕 f ξ) = _
  rw [inner_coordinate]
  simp only [smul_eq_mul, Complex.real_smul]
  push_cast
  ring


lemma harmonicLift_tangent_tangent_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) (i j : Fin m) :
    fderiv ℝ (fun p => fderiv ℝ (harmonicLift g) p
        (coordinate (m+1) j.castSucc)) (point x t)
      (coordinate (m+1) i.castSucc) =
      poissonIntegral (tangent (tangent g j) i) t x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have htg : ContDiff ℝ 1 (tangent g j) :=
    (hg.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hp : point x t ∈ openHalfSpace m := by simpa [openHalfSpace] using ht
  have he : (fun p => fderiv ℝ (harmonicLift g) p (coordinate (m+1) j.castSucc))
      =ᶠ[𝓝 (point x t)] harmonicLift (tangent g j) := by
    filter_upwards [(isOpen_openHalfSpace m).mem_nhds hp] with q hq
    have hq' : 0 < height q := hq
    rw [← point_horizontal_height q]
    rw [harmonicLift_tangent_open hgs hg1 hq']
    exact (lift_positive (tangent g j) (horizontal q) hq').symm
  rw [he.fderiv_eq]
  exact harmonicLift_tangent_open (tangent_compactSupport hgs j) htg ht x i

lemma contDiffOn_integral_compact_param {m n : ℕ} {k : ℕ∞}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ k (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0) :
    ContDiffOn ℝ k (fun q => ∫ y, G q y) U := by
  have hc := contDiffOn_convolution_right_with_param (μ := volume)
    (ContinuousLinearMap.mul ℝ ℝ) hU hK
    (fun p y hp hy => hzero p hp y hy)
    (locallyIntegrable_const (1 : ℝ)) hG
  have hcomp : ContDiffOn ℝ k (fun q : Space n => (q, (0 : Space m))) U :=
    contDiffOn_id.prodMk contDiffOn_const
  have h := hc.comp hcomp (fun q hq => ⟨hq, mem_univ _⟩)
  change ContDiffOn ℝ k (fun q => ∫ y, (1 : ℝ) * G q (0-y)) U at h
  simpa only [one_mul, zero_sub, integral_neg_eq_self] using h
lemma harmonicLift_contDiffAt_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {p : Space (m+1)} (hp : p ∈ openHalfSpace m) :
    ContDiffAt ℝ 2 (harmonicLift g) p := by
  let U : Set (Space (m+1)) := openHalfSpace m ∩ ball p 1
  let K : Set (Space m) := (horizontal '' closedBall p 1) - tsupport g
  let G := fun (q : Space (m+1)) (z : Space m) =>
    poissonKernel m (height q) z * g (horizontal q-z)
  have hU : IsOpen U := (isOpen_openHalfSpace m).inter isOpen_ball
  have hpU : p ∈ U := ⟨hp, mem_ball_self zero_lt_one⟩
  have hK : IsCompact K := by
    change IsCompact ((horizontal '' closedBall p 1) - tsupport g)
    rw [sub_eq_add_neg]
    exact ((isCompact_closedBall p 1).image
      (P201.Elliptic.HalfSpaceLift.horizontal_contDiff m).continuous).add (show IsCompact (tsupport g) from hgs).neg
  have hzero : ∀ q ∈ U, ∀ z, z ∉ K → G q z = 0 := by
    intro q hq z hz
    have hgzero : g (horizontal q-z) = 0 := by
      by_contra hne
      apply hz
      refine ⟨horizontal q, ⟨q, ball_subset_closedBall hq.2, rfl⟩,
        horizontal q-z, subset_tsupport g hne, ?_⟩
      simp
    simp [G, hgzero]
  have hheight : ContDiff ℝ 2 (fun q : Space (m+1) × Space m => height q.1) :=
    ((P201.Elliptic.HalfSpaceLift.height_contDiff m).of_le le_top).comp contDiff_fst
  have hbase : ContDiff ℝ 2 (fun q : Space (m+1) × Space m =>
      height q.1 ^ 2 + ‖q.2‖ ^ 2) :=
    (hheight.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have harg : ContDiff ℝ 2 (fun q : Space (m+1) × Space m => horizontal q.1-q.2) :=
    (((P201.Elliptic.HalfSpaceLift.horizontal_contDiff m).of_le le_top).comp contDiff_fst).sub
      contDiff_snd
  have hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ) := by
    intro q hq
    have ht : 0 < height q.1 := hq.1.1
    exact (((contDiffWithinAt_const.mul hheight.contDiffWithinAt).mul
      (hbase.contDiffWithinAt.rpow_const_of_ne (by positivity))).mul
      (hg.comp harg).contDiffWithinAt)
  have hd := contDiffOn_integral_compact_param hU hK hG hzero
  apply (hd.contDiffAt (hU.mem_nhds hpU)).congr_of_eventuallyEq
  filter_upwards [(isOpen_openHalfSpace m).mem_nhds hp] with q hq
  have hq' : 0 < height q := hq
  simp only [P201.Elliptic.HalfSpaceLift.harmonicLift,
    P201Specs.Elliptic.HalfSpaceLift.harmonicLift, ite_eq_left hq',
    P201.Elliptic.HalfSpaceLift.poissonIntegral,
    P201Specs.Elliptic.HalfSpaceLift.poissonIntegral, G]


lemma harmonicLift_contDiffOn_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g) :
    ContDiffOn ℝ 2 (harmonicLift g) (openHalfSpace m) :=
  fun _ hp => (harmonicLift_contDiffAt_open hgs hg hp).contDiffWithinAt

lemma param_fderiv_eq_zero_off_compact {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {q : Space n} (hq : q ∈ U) {y : Space m} (hy : y ∉ K) :
    fderiv ℝ (Function.uncurry G) (q,y) = 0 := by
  have he : Function.uncurry G =ᶠ[𝓝 (q,y)] fun _ => 0 := by
    filter_upwards [(hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hq,hy⟩] with r hr
    exact hzero r.1 hr.1 r.2 hr.2
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℝ) (q,y)).fderiv

lemma fderiv_integral_apply_compact_param {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {p : Space n} (hp : p ∈ U) (v : Space n) :
    fderiv ℝ (fun q => ∫ y, G q y) p v =
      ∫ y, fderiv ℝ (Function.uncurry G) (p,y) (v,0) := by
  have hDc : Continuous (fun y => (fderiv ℝ (Function.uncurry G) (p,y)).comp
      (ContinuousLinearMap.inl ℝ (Space n) (Space m))) := by
    apply ((hG.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_comp
      continuousOn_const).comp_continuous (.prodMk_right p)
    exact fun y => ⟨hp, mem_univ y⟩
  have hDs : HasCompactSupport (fun y => (fderiv ℝ (Function.uncurry G) (p,y)).comp
      (ContinuousLinearMap.inl ℝ (Space n) (Space m))) := by
    apply HasCompactSupport.intro hK
    intro y hy
    rw [param_fderiv_eq_zero_off_compact hU hK hzero hp hy]
    simp
  rw [(hasFDerivAt_integral_compact_param hU hK hG hzero hp).fderiv,
    ContinuousLinearMap.integral_apply (hDc.integrable_of_hasCompactSupport hDs)]
  rfl

lemma contDiffOn_param_derivative {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ)) (v : Space n) :
    ContDiffOn ℝ 1 (Function.uncurry (fun q y =>
      fderiv ℝ (Function.uncurry G) (q,y) (v,0))) (U ×ˢ univ) := by
  exact (hG.fderiv_of_isOpen (hU.prod isOpen_univ) (by norm_num)).clm_apply contDiffOn_const

lemma second_integral_apply_compact_param {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {p : Space n} (hp : p ∈ U) (v w : Space n) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => ∫ y, G r y) q v) p w =
      ∫ y, fderiv ℝ (Function.uncurry (fun q y =>
        fderiv ℝ (Function.uncurry G) (q,y) (v,0))) (p,y) (w,0) := by
  have he : (fun q => fderiv ℝ (fun r => ∫ y, G r y) q v) =ᶠ[𝓝 p]
      (fun q => ∫ y, fderiv ℝ (Function.uncurry G) (q,y) (v,0)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact fderiv_integral_apply_compact_param hU hK (hG.of_le (by norm_num)) hzero hq v
  rw [he.fderiv_eq]
  apply fderiv_integral_apply_compact_param hU hK (contDiffOn_param_derivative hU hG v) _ hp w
  intro q hq y hy
  rw [param_fderiv_eq_zero_off_compact hU hK hzero hq hy]
  simp
lemma param_derivative_eq_slice {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) (U ×ˢ univ))
    {p : Space n} (hp : p ∈ U) (y : Space m) (v : Space n) :
    fderiv ℝ (Function.uncurry G) (p,y) (v,0) =
      fderiv ℝ (fun q => G q y) p v := by
  have hd : HasFDerivAt (Function.uncurry G) (fderiv ℝ (Function.uncurry G) (p,y)) (p,y) :=
    ((hG.differentiableOn one_ne_zero).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds (x := (p,y)) ⟨hp,mem_univ y⟩)).hasFDerivAt
  have h := (hd.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p y)).fderiv
  exact (congrArg (fun L : Space n →L[ℝ] ℝ => L v) h).symm

lemma integrable_param_derivative {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {p : Space n} (hp : p ∈ U) (v : Space n) :
    Integrable (fun y => fderiv ℝ (Function.uncurry G) (p,y) (v,0)) volume := by
  have hc : Continuous (fun y => fderiv ℝ (Function.uncurry G) (p,y) (v,0)) := by
    apply ((hG.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_apply
      continuousOn_const).comp_continuous (.prodMk_right p)
    exact fun y => ⟨hp,mem_univ y⟩
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hK
  intro y hy
  rw [param_fderiv_eq_zero_off_compact hU hK hzero hp hy]
  simp

lemma second_param_derivative_eq_slice {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)}
    (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ))
    {p : Space n} (hp : p ∈ U) (y : Space m) (v w : Space n) :
    fderiv ℝ (Function.uncurry (fun q y =>
      fderiv ℝ (Function.uncurry G) (q,y) (v,0))) (p,y) (w,0) =
      fderiv ℝ (fun q => fderiv ℝ (fun r => G r y) q v) p w := by
  rw [param_derivative_eq_slice hU (contDiffOn_param_derivative hU hG v) hp]
  have he : (fun q => fderiv ℝ (Function.uncurry G) (q,y) (v,0)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (fun r => G r y) q v) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact param_derivative_eq_slice hU (hG.of_le (by norm_num)) hq y v
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L w) he.fderiv_eq

lemma laplacian_eq_sum_second {n : ℕ} (f : Space n → ℝ) (p : Space n) :
    laplacian f p = ∑ i : Fin n,
      fderiv ℝ (fun q => fderiv ℝ f q (coordinate n i)) p (coordinate n i) := by
  change (∑ i : Fin n, P102.U4.multiPartial f ({i, i} : MultiIndex n) p) = _
  simp only [P102.U4.multiPartial]
  simp [Multiset.sort_cons, P102.U4.partialWord]

lemma laplacian_integral_compact_param {m n : ℕ}
    {G : Space n → Space m → ℝ} {U : Set (Space n)} {K : Set (Space m)}
    (hU : IsOpen U) (hK : IsCompact K)
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ))
    (hzero : ∀ p ∈ U, ∀ y, y ∉ K → G p y = 0)
    {p : Space n} (hp : p ∈ U) :
    laplacian (fun q => ∫ y, G q y) p = ∫ y, laplacian (fun q => G q y) p := by
  rw [laplacian_eq_sum_second]
  simp_rw [second_integral_apply_compact_param hU hK hG hzero hp]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards [] with y
    rw [laplacian_eq_sum_second]
    apply Finset.sum_congr rfl
    intro i _
    exact second_param_derivative_eq_slice hU hG hp y _ _
  · intro i _
    apply integrable_param_derivative hU hK (contDiffOn_param_derivative hU hG _) _ hp
    intro q hq y hy
    rw [param_fderiv_eq_zero_off_compact hU hK hzero hq hy]
    simp
lemma fderiv_translate_mul {n : ℕ} {f : Space n → ℝ} (c : ℝ) (a p : Space n)
    (hf : DifferentiableAt ℝ f (p-a)) (v : Space n) :
    fderiv ℝ (fun q => f (q-a)*c) p v = fderiv ℝ f (p-a) v*c := by
  have h := ((hf.hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const a)).mul_const c).fderiv
  simpa [mul_comm] using congrArg (fun L : Space n →L[ℝ] ℝ => L v) h

lemma second_translate_mul {n : ℕ} {f : Space n → ℝ} (c : ℝ) (a p : Space n)
    (hf : ContDiffAt ℝ 2 f (p-a)) (v w : Space n) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => f (r-a)*c) q v) p w =
      fderiv ℝ (fun q => fderiv ℝ f q v) (p-a) w*c := by
  have he : (fun q => fderiv ℝ (fun r => f (r-a)*c) q v) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f (q-a) v*c) := by
    have ht : Tendsto (fun q : Space n => q-a) (𝓝 p) (𝓝 (p-a)) :=
      (continuous_id.sub continuous_const).continuousAt
    filter_upwards [ht.eventually (hf.eventually (by norm_num))] with q hq
    exact fderiv_translate_mul c a q (hq.differentiableAt (by norm_num)) v
  rw [he.fderiv_eq]
  apply fderiv_translate_mul (f := fun q => fderiv ℝ f q v) c a p _ w
  exact ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num)

lemma laplacian_translate_mul {n : ℕ} {f : Space n → ℝ} (c : ℝ) (a p : Space n)
    (hf : ContDiffAt ℝ 2 f (p-a)) :
    laplacian (fun q => f (q-a)*c) p = laplacian f (p-a)*c := by
  simp only [laplacian_eq_sum_second]
  simp_rw [second_translate_mul c a p hf]
  rw [Finset.sum_mul]
lemma laplacian_congr_nhds {n : ℕ} {f h : Space n → ℝ} {p : Space n}
    (he : f =ᶠ[𝓝 p] h) : laplacian f p = laplacian h p := by
  simp only [laplacian_eq_sum_second]
  apply Finset.sum_congr rfl
  intro i _
  have he' : (fun q => fderiv ℝ f q (coordinate n i)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ h q (coordinate n i)) :=
    he.fderiv.mono (fun q hq => congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i)) hq)
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i)) he'.fderiv_eq

lemma horizontal_sub_point_zero {m : ℕ} (p : Space (m+1)) (y : Space m) :
    horizontal (p-point y 0) = horizontal p-y := by
  ext i
  simp [horizontal, point]

lemma height_sub_point_zero {m : ℕ} (p : Space (m+1)) (y : Space m) :
    height (p-point y 0) = height p := by
  simp [height, point]

lemma poissonIntegral_fixed_support {m : ℕ} (g : Space m → ℝ) (t : ℝ) (x : Space m) :
    poissonIntegral g t x = ∫ y, poissonKernel m t (x-y)*g y := by
  have he := integral_sub_left_eq_self
    (fun z => poissonKernel m t z*g (x-z)) volume x
  simpa only [poissonIntegral, P201Specs.Elliptic.HalfSpaceLift.poissonIntegral,
    sub_sub_cancel] using he.symm

lemma harmonicLift_harmonic_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {p : Space (m+1)} (hp : p ∈ openHalfSpace m) :
    laplacian (harmonicLift g) p = 0 := by
  let U : Set (Space (m+1)) := openHalfSpace m
  let G := fun (q : Space (m+1)) (y : Space m) =>
    poissonKernel m (height q) (horizontal q-y)*g y
  have hU : IsOpen U := isOpen_openHalfSpace m
  have hzero : ∀ q ∈ U, ∀ y, y ∉ tsupport g → G q y = 0 := by
    intro q hq y hy
    simp [G, image_eq_zero_of_notMem_tsupport hy]
  have hheight : ContDiff ℝ 2 (fun q : Space (m+1) × Space m => height q.1) :=
    ((P201.Elliptic.HalfSpaceLift.height_contDiff m).of_le le_top).comp contDiff_fst
  have harg : ContDiff ℝ 2 (fun q : Space (m+1) × Space m => horizontal q.1-q.2) :=
    (((P201.Elliptic.HalfSpaceLift.horizontal_contDiff m).of_le le_top).comp contDiff_fst).sub
      contDiff_snd
  have hbase : ContDiff ℝ 2 (fun q : Space (m+1) × Space m =>
      height q.1 ^ 2 + ‖horizontal q.1-q.2‖ ^ 2) :=
    (hheight.pow 2).add ((contDiff_norm_sq ℝ).comp harg)
  have hG : ContDiffOn ℝ 2 (Function.uncurry G) (U ×ˢ univ) := by
    intro q hq
    have ht : 0 < height q.1 := hq.1
    exact (((contDiffWithinAt_const.mul hheight.contDiffWithinAt).mul
      (hbase.contDiffWithinAt.rpow_const_of_ne (by positivity))).mul
      (hg.comp contDiff_snd).contDiffWithinAt)
  have he : harmonicLift g =ᶠ[𝓝 p] (fun q => ∫ y, G q y) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change (if 0 < height q then _ else _) = _
    rw [if_pos (show 0 < height q from hq)]
    exact poissonIntegral_fixed_support g (height q) (horizontal q)
  rw [laplacian_congr_nhds he, laplacian_integral_compact_param hU hgs hG hzero hp]
  have hz : ∀ y : Space m, laplacian (fun q => G q y) p = 0 := by
    intro y
    have hp' : p-point y 0 ∈ openHalfSpace m := by
      simpa only [openHalfSpace, mem_setOf_eq, height_sub_point_zero] using hp
    have hk : ContDiffAt ℝ 2 (fun q : Space (m+1) =>
        poissonKernel m (height q) (horizontal q)) (p-point y 0) :=
      ((kernel_contDiff m).of_le (by simp)).contDiffAt
        ((isOpen_openHalfSpace m).mem_nhds hp')
    have he' : (fun q => G q y) = (fun q =>
        (fun r => poissonKernel m (height r) (horizontal r)) (q-point y 0)*g y) := by
      funext q
      simp only [G, height_sub_point_zero, horizontal_sub_point_zero]
    rw [he', laplacian_translate_mul (g y) (point y 0) p hk,
      kernel_harmonic m _ hp', zero_mul]
  simp_rw [hz]
  simp
lemma poissonIntegral_laplacian {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    poissonIntegral (laplacian g) t x =
      ∑ i : Fin m, poissonIntegral (tangent (tangent g i) i) t x := by
  have hi : ∀ i : Fin m, Integrable (fun z =>
      poissonKernel m t z*tangent (tangent g i) i (x-z)) volume := by
    intro i
    apply (tangent_compactSupport (tangent_compactSupport hgs i) i).convolutionExists_right
      (L := ContinuousLinearMap.mul ℝ ℝ) (kernel_integrable m ht).locallyIntegrable _ x
    exact (((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  change (∫ z, poissonKernel m t z*laplacian g (x-z)) =
    ∑ i : Fin m, ∫ z, poissonKernel m t z*tangent (tangent g i) i (x-z)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [laplacian_eq_sum_second, Finset.mul_sum, tangent]
  rfl

lemma harmonicLift_normal_normal_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    fderiv ℝ (fun p => fderiv ℝ (harmonicLift g) p (coordinate (m+1) (Fin.last m)))
      (point x t) (coordinate (m+1) (Fin.last m)) =
      -poissonIntegral (laplacian g) t x := by
  have hp : point x t ∈ openHalfSpace m := by simpa [openHalfSpace] using ht
  have h := harmonicLift_harmonic_open hgs hg hp
  rw [laplacian_eq_sum_second, Fin.sum_univ_castSucc] at h
  simp_rw [harmonicLift_tangent_tangent_open hgs hg ht x] at h
  rw [← poissonIntegral_laplacian hgs hg ht x] at h
  linarith

open P102.Specs.U3 (Euclidean)
open P102.Specs.U3.Riesz (L2 F2)
private lemma youngL2 {d : ℕ} {k f : Euclidean d → ℂ} (hk : Integrable k)
    (hf : MemLp f 2 volume) :
    P102.U2.YoungExpected.Result volume 2 1 2 f k := by
  exact P102.U2.Young.young volume (by norm_num) (by norm_num) (by norm_num)
    (by simp [add_comm]) hf (memLp_one_iff_integrable.mpr hk)

private def convolutionL2 {d : ℕ} (k : Euclidean d → ℂ) (hk : Integrable k)
    (u : L2 d) : L2 d :=
  (youngL2 hk (Lp.memLp u)).2.1.toLp (P102.U2.Young.integralConvolution volume u k)

private lemma convolutionL2_ae {d : ℕ} (k : Euclidean d → ℂ) (hk : Integrable k)
    (u : L2 d) : (convolutionL2 k hk u : Euclidean d → ℂ) =ᵐ[volume]
      P102.U2.Young.integralConvolution volume u k :=
  (youngL2 hk (Lp.memLp u)).2.1.coeFn_toLp

private lemma convolutionL2_norm {d : ℕ} (k : Euclidean d → ℂ) (hk : Integrable k)
    (u : L2 d) : ‖convolutionL2 k hk u‖ ≤ (eLpNorm k 1 volume).toReal * ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (convolutionL2_ae k hk u), Lp.norm_def]
  have hy := (youngL2 hk (Lp.memLp u)).2.2.1
  have hk1 : MemLp k 1 volume := memLp_one_iff_integrable.mpr hk
  have hprod : eLpNorm u 2 volume * eLpNorm k 1 volume ≠ ⊤ :=
    (ENNReal.mul_lt_top (Lp.memLp u) hk1).ne
  have hh := ENNReal.toReal_mono hprod hy
  rw [ENNReal.toReal_mul] at hh
  exact hh.trans_eq (mul_comm _ _)

private lemma convolutionL2_sub {d : ℕ} (k : Euclidean d → ℂ) (hk : Integrable k)
    (u v : L2 d) : convolutionL2 k hk u - convolutionL2 k hk v = convolutionL2 k hk (u-v) := by
  have he := P102.U2.Young.integralConvolution_congr volume (Lp.coeFn_sub u v) (ae_eq_refl k)
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (convolutionL2 k hk u) (convolutionL2 k hk v),
    convolutionL2_ae k hk u, convolutionL2_ae k hk v, convolutionL2_ae k hk (u-v),
    (youngL2 hk (Lp.memLp u)).1, (youngL2 hk (Lp.memLp v)).1] with x hc hu hv huv hui hvi
  rw [hc, Pi.sub_apply, hu, hv, huv, he]
  change (∫ y, u (x-y) * k y) - (∫ y, v (x-y) * k y) =
    ∫ y, (u (x-y)-v (x-y)) * k y
  rw [← integral_sub hui hvi]
  congr 1
  funext y
  ring

private lemma convolutionL2_continuous {d : ℕ} (k : Euclidean d → ℂ) (hk : Integrable k) :
    Continuous (convolutionL2 k hk) := by
  apply LipschitzWith.continuous (K := ⟨(eLpNorm k 1 volume).toReal, ENNReal.toReal_nonneg⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm]
  rw [convolutionL2_sub]
  exact convolutionL2_norm k hk (u-v)

theorem convolution_L2_fourier_general {d : ℕ}
    (k f m : Euclidean d → ℂ) (hk : Integrable k)
    (hf : MemLp f 2 volume) (hkF : 𝓕 k = m) :
    ∃ hc : MemLp (fun x => ∫ z, k z * f (x-z)) 2 volume,
      (F2 d (hc.toLp _) : Euclidean d → ℂ) =ᵐ[volume]
        fun ξ => m ξ * (F2 d (hf.toLp f) : Euclidean d → ℂ) ξ := by
  have hmc : Continuous m := by
    rw [← hkF]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hk
  have hmtop : MemLp m (⊤ : ENNReal) volume :=
    memLp_top_of_bound hmc.aestronglyMeasurable (∫ z, ‖k z‖)
      (Eventually.of_forall fun ξ => by rw [← hkF]; exact Real.norm_fourier_le_integral_norm k ξ)
  let T : L2 d →L[ℂ] L2 d :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL volume (⊤ : ENNReal) 2 2 (hmtop.toLp m)
  have hTae : ∀ u : L2 d, (T u : Euclidean d → ℂ) =ᵐ[volume] fun ξ => m ξ * u ξ := by
    intro u
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hmtop.toLp m) u,
      hmtop.coeFn_toLp] with ξ hξ hmξ
    simpa [T, hmξ] using hξ
  have hidentity : (fun u : L2 d => F2 d (convolutionL2 k hk u)) =
      fun u => T (F2 d u) := by
    apply Continuous.ext_on (Lp.simpleFunc.dense (by norm_num))
      ((F2 d).continuous.comp (convolutionL2_continuous k hk))
      (T.continuous.comp (F2 d).continuous)
    intro u hu
    let s : Lp.simpleFunc ℂ 2 (volume : Measure (Euclidean d)) := ⟨u, hu⟩
    have hu1 : Integrable (u : Euclidean d → ℂ) :=
      ((SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mp
        (Lp.simpleFunc.memLp s)).congr (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
    obtain ⟨hc, hcf⟩ := P102.U3.Riesz.convolution_L2_fourier k u m hk (Lp.memLp u) hu1 hkF
    have hCu : convolutionL2 k hk u = hc.toLp (fun x => ∫ z, k z * u (x-z)) := by
      apply Lp.ext
      filter_upwards [convolutionL2_ae k hk u, hc.coeFn_toLp] with x hx hy
      rw [hx, hy]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
    change F2 d (convolutionL2 k hk u) = T (F2 d u)
    rw [hCu]
    apply Lp.ext
    have hu2 : (Lp.memLp u).toLp (u : Euclidean d → ℂ) = u := Lp.toLp_coeFn u _
    rw [hu2] at hcf
    exact hcf.trans (hTae (F2 d u)).symm
  have hc : MemLp (fun x => ∫ z, k z * f (x-z)) 2 volume := by
    have hc' := (youngL2 hk hf).2.1
    exact hc'.ae_eq (Eventually.of_forall fun x => by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _)
  refine ⟨hc, ?_⟩
  have hCu : convolutionL2 k hk (hf.toLp f) = hc.toLp (fun x => ∫ z, k z * f (x-z)) := by
    apply Lp.ext
    have he := P102.U2.Young.integralConvolution_congr volume hf.coeFn_toLp (ae_eq_refl k)
    filter_upwards [convolutionL2_ae k hk (hf.toLp f), hc.coeFn_toLp] with x hx hy
    rw [hx, hy, he]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => mul_comm _ _
  rw [← hCu, congrFun hidentity (hf.toLp f)]
  exact hTae _


def normalKernel (m : ℕ) (t : ℝ) (z : Space m) : ℝ :=
  poissonConstant m * (t ^ 2 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1) / 2) *
    (1 - ((m : ℝ) + 1) * t ^ 2 / (t ^ 2 + ‖z‖ ^ 2))

lemma hasDerivAt_kernel_height (m : ℕ) {t : ℝ} (ht : 0 < t) (z : Space m) :
    HasDerivAt (fun s => poissonKernel m s z) (normalKernel m t z) t := by
  have hA : 0 < t ^ 2 + ‖z‖ ^ 2 := by positivity
  have hdA : HasDerivAt (fun s : ℝ => s ^ 2 + ‖z‖ ^ 2) (2*t) t := by
    simpa using ((hasDerivAt_id t).pow 2).add_const (‖z‖ ^ 2)
  have hpow := hdA.rpow_const (p := -((m : ℝ)+1)/2) (Or.inl hA.ne')
  convert (((hasDerivAt_id t).const_mul (poissonConstant m)).mul hpow) using 1
  · rfl
  · rw [Real.rpow_sub hA, Real.rpow_one]
    dsimp only [normalKernel]
    simp only [id_eq]
    field_simp
    ring

lemma normalKernel_bound (m : ℕ) {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (z : Space m) :
    ‖normalKernel m t z‖ ≤ ((m : ℝ)+2) / δ * poissonKernel m δ z := by
  have ht0 : 0 < t := hδ.trans_le ht
  have hA : 0 < t ^ 2 + ‖z‖ ^ 2 := by positivity
  have hD : 0 < δ ^ 2 + ‖z‖ ^ 2 := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hD
    (show δ ^ 2 + ‖z‖ ^ 2 ≤ t ^ 2 + ‖z‖ ^ 2 by nlinarith)
    (show -((m : ℝ)+1)/2 ≤ 0 by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hq0 : 0 ≤ ((m : ℝ)+1)*t^2/(t^2+‖z‖^2) := by positivity
  have hq1 : ((m : ℝ)+1)*t^2/(t^2+‖z‖^2) ≤ (m : ℝ)+1 := by
    apply (div_le_iff₀ hA).mpr
    nlinarith [sq_nonneg ‖z‖, Nat.cast_nonneg (α := ℝ) m]
  have hfac : |1-((m : ℝ)+1)*t^2/(t^2+‖z‖^2)| ≤ (m : ℝ)+2 := by
    calc
      _ ≤ |(1 : ℝ)| + |((m : ℝ)+1)*t^2/(t^2+‖z‖^2)| := abs_sub _ _
      _ ≤ _ := by rw [abs_one, abs_of_nonneg hq0]; linarith
  calc
    ‖normalKernel m t z‖ = poissonConstant m *
        (t^2+‖z‖^2)^(-((m : ℝ)+1)/2) *
        |1-((m : ℝ)+1)*t^2/(t^2+‖z‖^2)| := by
      rw [normalKernel, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (mul_nonneg (constant_pos m).le (Real.rpow_nonneg hA.le _))]
    _ ≤ poissonConstant m * (t^2+‖z‖^2)^(-((m : ℝ)+1)/2) * ((m : ℝ)+2) := by
      exact mul_le_mul_of_nonneg_left hfac (mul_nonneg (constant_pos m).le (Real.rpow_nonneg hA.le _))
    _ ≤ poissonConstant m * (δ^2+‖z‖^2)^(-((m : ℝ)+1)/2) * ((m : ℝ)+2) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (constant_pos m).le) (by positivity)
    _ = _ := by dsimp only [poissonKernel, P201Specs.Elliptic.HalfSpaceLift.poissonKernel]; field_simp

lemma normalKernel_continuous (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous (normalKernel m t) := by
  unfold normalKernel
  have hA : ∀ z : Space m, t^2+‖z‖^2 ≠ 0 := fun z => ne_of_gt (by positivity)
  have hB : Continuous (fun z : Space m => t^2+‖z‖^2) := continuous_const.add (continuous_norm.pow 2)
  exact (continuous_const.mul (hB.rpow_const (fun z => Or.inl (hA z)))).mul
    (continuous_const.sub (continuous_const.div hB hA))

lemma normalKernel_integrable (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (normalKernel m t) volume := by
  apply ((kernel_integrable m ht).const_mul (((m : ℝ)+2)/t)).mono'
    (normalKernel_continuous m ht).aestronglyMeasurable
  exact .of_forall (normalKernel_bound m ht le_rfl)

lemma normalKernel_fourier {m : ℕ} {t : ℝ} (ht : 0 < t) (ξ : Space m) :
    fourierIntegral (fun z => (normalKernel m t z : ℂ)) ξ =
      ((-2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) * (Real.exp (-2*Real.pi*t*‖ξ‖) : ℂ) := by
  let δ := t/2
  have hδ : 0 < δ := half_pos ht
  let F : ℝ → Space m → ℂ := fun s z => fourierPhase z ξ * (poissonKernel m s z : ℂ)
  let F' : ℝ → Space m → ℂ := fun s z => fourierPhase z ξ * (normalKernel m s z : ℂ)
  let bound : Space m → ℝ := fun z => ((m : ℝ)+2)/δ * poissonKernel m δ z
  have hphase : Continuous (fun z : Space m => fourierPhase z ξ) := by
    unfold fourierPhase P201Specs.fourierPhase
    fun_prop
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (show δ < t from half_lt_self ht) (show t < 2*t by linarith))
    (show ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume from by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (hphase.mul (Complex.continuous_ofReal.comp
        (kernel_spatial_contDiff hs).continuous)).aestronglyMeasurable)
    (phase_integrable (kernel_integrable m ht).ofReal ξ)
    (show AEStronglyMeasurable (F' t) volume from
      (hphase.mul (Complex.continuous_ofReal.comp
        (normalKernel_continuous m ht))).aestronglyMeasurable)
    (show ∀ᵐ z : Space m ∂volume, ∀ s ∈ Ioo δ (2*t), ‖F' s z‖ ≤ bound z from by
      exact .of_forall fun z s hs => by
        dsimp only [F', bound]
        rw [norm_mul, phase_norm, one_mul, Complex.norm_real]
        exact normalKernel_bound m hδ hs.1.le z)
    ((kernel_integrable m hδ).const_mul (((m : ℝ)+2)/δ))
    (show ∀ᵐ z : Space m ∂volume, ∀ s ∈ Ioo δ (2*t),
        HasDerivAt (fun s => F s z) (F' s z) s from by
      exact .of_forall fun z s hs =>
        ((hasDerivAt_kernel_height m (hδ.trans hs.1) z).ofReal_comp).const_mul (fourierPhase z ξ))
  have he : (fun s => ∫ z, F s z) =ᶠ[𝓝 t]
      (fun s => (Real.exp (-2*Real.pi*s*‖ξ‖) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact kernel_fourier hs ξ
  have hexp : HasDerivAt (fun s : ℝ => (Real.exp (-2*Real.pi*s*‖ξ‖) : ℂ))
      ((Real.exp (-2*Real.pi*t*‖ξ‖) * (-2*Real.pi*‖ξ‖) : ℝ) : ℂ) t := by
    have hlin : HasDerivAt (fun s : ℝ => -2*Real.pi*s*‖ξ‖) (-2*Real.pi*‖ξ‖) t := by
      convert (hasDerivAt_id t).const_mul (-2*Real.pi*‖ξ‖) using 1
      · funext s; simp only [id_eq]; ring
      · simp
    exact hlin.exp.ofReal_comp
  have huniq := (hd.2.congr_of_eventuallyEq he.symm).unique hexp
  change fourierIntegral (fun z => (normalKernel m t z : ℂ)) ξ = _ at huniq
  simpa only [Complex.ofReal_mul, mul_comm] using huniq


lemma c2HolderNormOn_le_of_closed_jets {m : ℕ} {α M H : ℝ}
    {f : Space (m+1) → ℝ}
    {D : Space (m+1) → Space (m+1) →L[ℝ] ℝ}
    {A : Space (m+1) → Space (m+1) →L[ℝ] Space (m+1) →L[ℝ] ℝ}
    (he1 : ∀ p ∈ closedHalfSpace m, fderivWithin ℝ f (closedHalfSpace m) p = D p)
    (he2 : ∀ p ∈ closedHalfSpace m, fderivWithin ℝ D (closedHalfSpace m) p = A p)
    (hfM : ∀ p ∈ closedHalfSpace m, ‖f p‖ ≤ M)
    (hDM : ∀ p ∈ closedHalfSpace m, ‖D p‖ ≤ M)
    (hAM : ∀ p ∈ closedHalfSpace m, ‖A p‖ ≤ M)
    (hAH : ∀ p ∈ closedHalfSpace m, ∀ q ∈ closedHalfSpace m,
      ‖A p - A q‖ ≤ H * dist p q ^ α) :
    c2HolderNormOn α f (closedHalfSpace m) ≤ 3 * M + H := by
  have hU := uniqueDiffOn_closedHalfSpace m
  have htwo := fun p hp => iteratedFDerivWithin_two_eq_bilinearJet hU he1 he2 (p := p) hp
  have hS : ∃ x ∈ closedHalfSpace m, ∃ y ∈ closedHalfSpace m, x ≠ y := by
    refine ⟨point (0 : Space m) 0, by simp [closedHalfSpace],
      point (0 : Space m) 1, by simp [closedHalfSpace], ?_⟩
    intro h
    have hh := congrArg height h
    exact zero_ne_one (show (0 : ℝ) = 1 by simpa only [height_point] using hh)
  apply c2HolderNormOn_le_of_bounds hS
  · intro k hk p hp
    interval_cases k
    · simpa only [norm_iteratedFDerivWithin_zero] using hfM p hp
    · rw [norm_iteratedFDerivWithin_one _ (hU p hp), he1 p hp]
      exact hDM p hp
    · rw [htwo p hp, LinearIsometryEquiv.norm_map]
      exact hAM p hp
  · intro p hp q hq
    rw [htwo p hp, htwo q hq, ← (bilinearJetEquiv (Space (m+1)) ℝ).map_sub,
      LinearIsometryEquiv.norm_map]
    exact hAH p hp q hq



lemma c2HolderOn_closed_of_scalar_jets {m : ℕ} {α B K : ℝ}
    {f : Space (m+1) → ℝ} {d : Fin (m+1) → Space (m+1) → ℝ}
    {a : Fin (m+1) → Fin (m+1) → Space (m+1) → ℝ}
    (hf : DifferentiableOn ℝ f (openHalfSpace m))
    (hd : ∀ j, DifferentiableOn ℝ (d j) (openHalfSpace m))
    (hc : ContinuousOn f (closedHalfSpace m))
    (hdc : ∀ j, ContinuousOn (d j) (closedHalfSpace m))
    (hac : ∀ i j, ContinuousOn (a i j) (closedHalfSpace m))
    (he : ∀ p ∈ openHalfSpace m, ∀ j, fderiv ℝ f p (coordinate (m+1) j) = d j p)
    (he2 : ∀ p ∈ openHalfSpace m, ∀ i j,
      fderiv ℝ (d j) p (coordinate (m+1) i) = a i j p)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hfB : ∀ p ∈ closedHalfSpace m, ‖f p‖ ≤ B)
    (hdB : ∀ j, ∀ p ∈ closedHalfSpace m, ‖d j p‖ ≤ B)
    (haB : ∀ i j, ∀ p ∈ closedHalfSpace m, ‖a i j p‖ ≤ B)
    (haK : ∀ i j, ∀ p ∈ closedHalfSpace m, ∀ q ∈ closedHalfSpace m,
      ‖a i j p - a i j q‖ ≤ K * dist p q ^ α) :
    C2HolderOn α f (closedHalfSpace m) ∧
      (∀ p ∈ closedHalfSpace m, ∀ j,
        fderivWithin ℝ f (closedHalfSpace m) p (coordinate (m+1) j) = d j p) ∧
      (∀ p ∈ closedHalfSpace m, ∀ i j,
        fderivWithin ℝ (fun q => fderivWithin ℝ f (closedHalfSpace m) q
          (coordinate (m+1) j)) (closedHalfSpace m) p (coordinate (m+1) i) = a i j p) ∧
      c2HolderNormOn α f (closedHalfSpace m) ≤
        3 * ((1 + (m+1 : ℕ) + (m+1 : ℕ) * (m+1 : ℕ) : ℝ) * B) +
          (m+1 : ℕ) * ((m+1 : ℕ) * K) := by
  let D := fun p => coordinateExpansion ℝ (fun j => d j p)
  let A := fun p => coordinateExpansion (Space (m+1) →L[ℝ] ℝ)
    (fun i => coordinateExpansion ℝ (fun j => a i j p))
  have hD : ContinuousOn D (closedHalfSpace m) := continuousOn_coordinateExpansion hdc
  have hA : ContinuousOn A (closedHalfSpace m) :=
    continuousOn_coordinateExpansion (fun i => continuousOn_coordinateExpansion (hac i))
  have heD : ∀ p ∈ openHalfSpace m, fderiv ℝ f p = D p := by
    intro p hp
    apply coordinateExpansion_ext
    intro j
    simpa only [D, coordinateExpansion_coordinate] using he p hp j
  have hDd : DifferentiableOn ℝ D (openHalfSpace m) := by
    intro p hp
    exact (hasFDerivAt_coordinateExpansion (fun j =>
      ((hd j).differentiableAt ((isOpen_openHalfSpace m).mem_nhds hp)).hasFDerivAt)).differentiableAt.differentiableWithinAt
  have heA : ∀ p ∈ openHalfSpace m, fderiv ℝ D p = A p := by
    intro p hp
    exact fderiv_coordinateExpansion
      (fun j => (hd j).differentiableAt ((isOpen_openHalfSpace m).mem_nhds hp)) (he2 p hp)
  let M := (1 + (m+1 : ℕ) + (m+1 : ℕ) * (m+1 : ℕ) : ℝ) * B
  have hM : 0 ≤ M := by positivity
  have hfM : ∀ p ∈ closedHalfSpace m, ‖f p‖ ≤ M := by
    intro p hp
    exact (hfB p hp).trans (by dsimp [M]; nlinarith)
  have hDM : ∀ p ∈ closedHalfSpace m, ‖D p‖ ≤ M := by
    intro p hp
    exact (coordinateExpansion_uniform_bound (fun j => hdB j p hp)).trans (by dsimp [M]; nlinarith)
  have hAM : ∀ p ∈ closedHalfSpace m, ‖A p‖ ≤ M := by
    intro p hp
    have hi : ∀ i, ‖coordinateExpansion ℝ (fun j => a i j p)‖ ≤ (m+1 : ℕ) * B :=
      fun i => coordinateExpansion_uniform_bound (fun j => haB i j p hp)
    exact (coordinateExpansion_uniform_bound hi).trans (by dsimp [M]; nlinarith)
  have hAK : ∀ p ∈ closedHalfSpace m, ∀ q ∈ closedHalfSpace m,
      ‖A p - A q‖ ≤ ((m+1 : ℕ) * ((m+1 : ℕ) * K)) * dist p q ^ α := by
    intro p hp q hq
    exact coordinateExpansion_holder
      (fun i r hr s hs => coordinateExpansion_holder (haK i) hr hs) hp hq
  have hc2 := c2HolderOn_of_jet_extension hf hDd hc hD hA heD heA hM
    (show 0 ≤ (m+1 : ℕ) * ((m+1 : ℕ) * K) by positivity) hfM hDM hAM hAK
  have he1 := fun p hp => fderivWithin_closedHalfSpace_of_extension hf hc hD heD (p := p) hp
  refine ⟨hc2, ?_, ?_, ?_⟩
  · intro p hp j
    rw [he1 p hp]
    exact coordinateExpansion_coordinate _ _
  · intro p hp i j
    have hcj : ContinuousOn (fun q => coordinateExpansion ℝ (fun k => a k j q))
        (closedHalfSpace m) := continuousOn_coordinateExpansion (fun k => hac k j)
    have hej : ∀ q ∈ openHalfSpace m, fderiv ℝ (d j) q =
        coordinateExpansion ℝ (fun k => a k j q) := by
      intro q hq
      apply coordinateExpansion_ext
      intro k
      simpa only [coordinateExpansion_coordinate] using he2 q hq k j
    have hEq : EqOn (fun q => fderivWithin ℝ f (closedHalfSpace m) q (coordinate (m+1) j))
        (d j) (closedHalfSpace m) := by
      intro q hq
      dsimp only
      rw [he1 q hq]
      exact coordinateExpansion_coordinate _ _
    rw [fderivWithin_congr' hEq hp,
      fderivWithin_closedHalfSpace_of_extension (hd j) (hdc j) hcj hej hp]
    exact coordinateExpansion_coordinate _ _

  · exact c2HolderNormOn_le_of_closed_jets he1
      (fun p hp => fderivWithin_closedHalfSpace_of_extension hDd hD hA heA hp)
      hfM hDM hAM hAK


lemma holderBounds_neg {m : ℕ} {α M H : ℝ} {b : Space m → ℝ}
    (hb : HolderBounds α b M H) : HolderBounds α (fun x => -b x) M H := by
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · intro x
    simpa only [norm_neg] using hb.2.2.1 x
  · intro x y
    simpa only [neg_sub_neg, norm_sub_rev] using hb.2.2.2 x y

lemma laplacian_eq_sum_tangent_tangent {m : ℕ} (g : Space m → ℝ) :
    laplacian g = fun x => ∑ i : Fin m, tangent (tangent g i) i x := by
  funext x
  change (∑ i : Fin m, P102.U4.multiPartial g ({i, i} : MultiIndex m) x) =
    ∑ i : Fin m, fderiv ℝ (fun y => fderiv ℝ g y (coordinate m i)) x (coordinate m i)
  simp only [P102.U4.multiPartial]
  simp [Multiset.sort_cons, P102.U4.partialWord]

lemma c2Holder_datum_bounds {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {g : Space m → ℝ} (hg : C2HolderOn α g univ) :
    let N := c2HolderNormOn α g univ
    0 ≤ N ∧ HolderBounds α g N (3*N) ∧
      (∀ j, HolderBounds α (tangent g j) N (3*N)) ∧
      (∀ i j, HolderBounds α (tangent (tangent g j) i) N N) ∧
      HolderBounds α (laplacian g) ((m : ℝ)*N) ((m : ℝ)*N) := by
  dsimp only
  let N := c2HolderNormOn α g univ
  let : NeZero m := ⟨by omega⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Space m)
  have hnon : ∃ x ∈ (univ : Set (Space m)), ∃ y ∈ univ, x ≠ y :=
    ⟨0, mem_univ _, y, mem_univ _, hy.symm⟩
  obtain ⟨hN, hjet, hhol⟩ := c2Holder_bounds_by_norm hg hnon
  have hjet' : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ N := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hjet
  have hhol' : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤
      N * dist x y ^ α := by
    simpa only [iteratedFDerivWithin_univ, mem_univ, forall_true_left] using hhol
  have hc : ContDiff ℝ 2 g := contDiffOn_univ.mp hg.1
  obtain ⟨hfirst, hsecond⟩ := c2Holder_tangent_bounds hα hα1 hc hN hN hjet' hhol'
  refine ⟨hN, ?_, hfirst, hsecond, ?_⟩
  · have hsup : ∀ x, ‖g x‖ ≤ N := by
      intro x
      simpa only [norm_iteratedFDeriv_zero] using hjet' 0 (by norm_num) x
    have hD : ∀ x, ‖fderiv ℝ g x‖ ≤ N := by
      intro x
      simpa only [norm_iteratedFDeriv_one] using hjet' 1 (by norm_num) x
    have hlip : ∀ x y, ‖g x - g y‖ ≤ N * dist x y := by
      intro x y
      simpa only [dist_eq_norm] using
        (convex_univ : Convex ℝ (univ : Set (Space m))).norm_image_sub_le_of_norm_fderiv_le
          (fun x _ => hc.differentiable (by norm_num) x) (fun x _ => hD x)
          (mem_univ y) (mem_univ x)
    change HolderBounds α g N (3*N)
    rw [show 3*N = N+2*N by ring]
    exact holderBounds_of_bounded_lipschitz hα hα1.le hN hN hsup hlip
  · rw [laplacian_eq_sum_tangent_tangent]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      holderBounds_sum (fun i x => tangent (tangent g i) i x) (fun _ => N) (fun _ => N)
        (fun i => hsecond i i)

lemma lift_data_uniform_bounds {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Space m → ℝ, HasCompactSupport g →
      tsupport g ⊆ closedBall 0 R → C2HolderOn α g univ →
      let N := c2HolderNormOn α g univ
      0 ≤ N ∧ HolderBounds α g (C*N) (C*N) ∧
      (∀ j, HolderBounds α (tangent g j) (C*N) (C*N)) ∧
      (∀ i j, HolderBounds α (tangent (tangent g j) i) (C*N) (C*N)) ∧
      HolderBounds α (normalGenerator g) (C*N) (C*N) ∧
      (∀ j, HolderBounds α (normalGenerator (tangent g j)) (C*N) (C*N)) ∧
      HolderBounds α (laplacian g) (C*N) (C*N) := by
  obtain ⟨A, hA, hnormal⟩ := normalTraces_quantitative hm hα hα1 hR
  refine ⟨3 + A + (m : ℝ), by positivity, ?_⟩
  intro g hs ht hg
  dsimp only
  let N := c2HolderNormOn α g univ
  obtain ⟨hN, hgB, hfirst, hsecond, hlap⟩ := c2Holder_datum_bounds hm hα hα1 hg
  have h3 : 3*N ≤ (3+A+(m : ℝ))*N :=
    mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) hN
  have h1 : N ≤ (3+A+(m : ℝ))*N := by
    calc N ≤ 3*N := by linarith
         _ ≤ _ := h3
  have hA' : A*N ≤ (3+A+(m : ℝ))*N :=
    mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) hN
  have hm' : (m : ℝ)*N ≤ (3+A+(m : ℝ))*N :=
    mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) hN
  obtain ⟨hng, hngj⟩ := normalTraces_holder hm hα hα1 hs hg
  obtain ⟨hnorm, hnormj⟩ := hnormal g hs ht hg
  refine ⟨hN, holderBounds_mono hgB h1 h3,
    fun j => holderBounds_mono (hfirst j) h1 h3,
    fun i j => holderBounds_mono (hsecond i j) h1 h1, ?_, ?_,
    holderBounds_mono hlap hm' hm'⟩
  · exact holderBounds_mono (P201.Elliptic.HolderCancellation.bounds_by_holderNorm hm hng)
      (hnorm.trans hA') (hnorm.trans hA')
  · intro j
    exact holderBounds_mono (P201.Elliptic.HolderCancellation.bounds_by_holderNorm hm (hngj j))
      ((hnormj j).trans hA') ((hnormj j).trans hA')


lemma normalGenerator_symbol_sum {m : ℕ} (ξ : Space m) (a : ℂ) :
    (∑ i : Fin m, P102.U3.Riesz.symbol m i ξ *
      ((2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * a)) =
      ((2 * Real.pi * ‖ξ‖ : ℝ) : ℂ) * a := by
  have he (i : Fin m) : P102.U3.Riesz.symbol m i ξ *
      ((2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * a) =
      ((2 * Real.pi * (ξ i)^2 / ‖ξ‖ : ℝ) : ℂ) * a := by
    simp only [P102.U3.Riesz.symbol, P102.Specs.U3.Riesz.symbolValue,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    ring_nf
    simp
  simp_rw [he]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 1
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hsq : (∑ i : Fin m, (ξ i)^2) = ‖ξ‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq ξ).symm
  rw [hsq]
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    field_simp

lemma normalGenerator_L2_frequency {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {b : Space m → ℝ}
    (hs : HasCompactSupport b) (hb : ContDiff ℝ 1 b)
    (hDb : ∀ i : Fin m, P201Specs.Elliptic.HolderCancellation.IsHolder α (tangent b i)) :
    ∃ (hf : MemLp (fun x => (b x : ℂ)) 2 volume)
      (hg : MemLp (fun x => (normalGenerator b x : ℂ)) 2 volume),
      (P102.Specs.U3.Riesz.F2 m (hg.toLp _) : Space m → ℂ) =ᵐ[volume]
        fun ξ => ((2*Real.pi*‖ξ‖ : ℝ) : ℂ) *
          (P102.Specs.U3.Riesz.F2 m (hf.toLp _) : Space m → ℂ) ξ := by
  let f : Space m → ℂ := fun x => (b x : ℂ)
  have hfs : HasCompactSupport f := hs.comp_left (g := Complex.ofReal) rfl
  have hfc : Continuous f := Complex.continuous_ofReal.comp hb.continuous
  have hf2 : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  have hf1 : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  choose hDi hPi hEq using (fun i : Fin m => holder_rieszL2_identification hm hα hα1 i
    (tangent_compactSupport hs i) (hDb i))
  have hg2 : MemLp (fun x => (normalGenerator b x : ℂ)) 2 volume := by
    convert memLp_finset_sum Finset.univ (fun i _ => hPi i) using 1
    funext x
    simp only [normalGenerator, P201Specs.Elliptic.HalfSpaceLift.normalGenerator,
      Complex.ofReal_sum]
  have hsum : hg2.toLp _ = ∑ i, (hPi i).toLp _ := by
    apply Lp.ext
    filter_upwards [hg2.coeFn_toLp, Lp.coeFn_finsetSum Finset.univ (fun i => (hPi i).toLp _),
      ae_all_iff.mpr (fun i => (hPi i).coeFn_toLp)] with x hx hsum hpx
    rw [hx, hsum]
    simp only [normalGenerator, P201Specs.Elliptic.HalfSpaceLift.normalGenerator,
      Complex.ofReal_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => (hpx i).symm)
  have hfreq (i : Fin m) :
      (P102.Specs.U3.Riesz.F2 m ((hPi i).toLp _) : Space m → ℂ) =ᵐ[volume]
        fun ξ => P102.U3.Riesz.symbol m i ξ *
          ((2*(Real.pi : ℂ)*Complex.I)*(ξ i : ℂ)*
            (P102.Specs.U3.Riesz.F2 m (hf2.toLp f) : Space m → ℂ) ξ) := by
    rw [hEq i, P102.U3.Riesz.rieszL2_frequency]
    have hdc : Continuous (fun x => (tangent b i x : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have hds : HasCompactSupport (fun x => (tangent b i x : ℂ)) :=
      (tangent_compactSupport hs i).comp_left (g := Complex.ofReal) rfl
    have hdi : Integrable (fun x => (tangent b i x : ℂ)) :=
      hdc.integrable_of_hasCompactSupport hds
    filter_upwards [P102.U3.Riesz.frequencyMul_ae i
      (P102.Specs.U3.Riesz.F2 m ((hDi i).toLp _)),
      P102.U3.Plancherel.integral_compatibility _ (hDi i) hdi,
      P102.U3.Plancherel.integral_compatibility f hf2 hf1] with ξ hξ hD hF
    rw [hξ, hD, tangent_fourier hs hb i ξ, hF]
  refine ⟨hf2, hg2, ?_⟩
  rw [hsum, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => P102.Specs.U3.Riesz.F2 m ((hPi i).toLp _)),
    ae_all_iff.mpr hfreq] with ξ hsum hξ
  rw [hsum]
  simp only [Finset.sum_apply]
  simp_rw [hξ]
  exact normalGenerator_symbol_sum ξ _


lemma second_direction_symm {n : ℕ} {f : Space n → ℝ} {p : Space n}
    (hf : ContDiffAt ℝ 2 f p) (v w : Space n) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w =
      fderiv ℝ (fun q => fderiv ℝ f q w) p v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.isSymmSndFDerivAt (by norm_num) w v
lemma first_component_contDiffAt {n : ℕ} {f : Space n → ℝ} {p : Space n}
    (hf : ContDiffAt ℝ 2 f p) (v : Space n) :
    ContDiffAt ℝ 1 (fun q => fderiv ℝ f q v) p :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

lemma harmonicLift_first_component_contDiffAt {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {p : Space (m+1)} (hp : p ∈ openHalfSpace m) (v : Space (m+1)) :
    ContDiffAt ℝ 1 (fun q => fderiv ℝ (harmonicLift g) q v) p :=
  first_component_contDiffAt (harmonicLift_contDiffAt_open hgs hg hp) v

lemma harmonicLift_reverse_mixed_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) (j : Fin m) :
    fderiv ℝ (fun q => fderiv ℝ (harmonicLift g) q (coordinate (m+1) (Fin.last m)))
        (point x t) (coordinate (m+1) j.castSucc) =
      fderiv ℝ (fun q => fderiv ℝ (harmonicLift g) q (coordinate (m+1) j.castSucc))
        (point x t) (coordinate (m+1) (Fin.last m)) := by
  apply second_direction_symm (harmonicLift_contDiffAt_open hgs hg _)
  simpa [openHalfSpace] using ht

lemma harmonicLift_tangent_eventuallyEq_lift {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    {p : Space (m+1)} (hp : p ∈ openHalfSpace m) (j : Fin m) :
    (fun q => fderiv ℝ (harmonicLift g) q (coordinate (m+1) j.castSucc))
      =ᶠ[𝓝 p] harmonicLift (tangent g j) := by
  filter_upwards [(isOpen_openHalfSpace m).mem_nhds hp] with q hq
  have hq' : 0 < height q := hq
  rw [← point_horizontal_height q]
  rw [harmonicLift_tangent_open hgs hg hq']
  exact (lift_positive (tangent g j) (horizontal q) hq').symm

lemma hasDerivAt_poissonIntegral_height {m : ℕ} {b : Space m → ℝ}
    (hb : Continuous b) {M : ℝ} (hM : ∀ x, ‖b x‖ ≤ M)
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    HasDerivAt (fun s => poissonIntegral b s x)
      (∫ z, normalKernel m t z*b (x-z)) t := by
  let δ := t/2
  have hδ : 0 < δ := half_pos ht
  let F : ℝ → Space m → ℝ := fun s z => poissonKernel m s z*b (x-z)
  let F' : ℝ → Space m → ℝ := fun s z => normalKernel m s z*b (x-z)
  let bound : Space m → ℝ := fun z => (((m : ℝ)+2)/δ * poissonKernel m δ z)*M
  have hbc : Continuous (fun z => b (x-z)) := hb.comp (continuous_const.sub continuous_id)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (show δ < t from half_lt_self ht) (show t < 2*t by linarith))
    (show ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume from by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ((kernel_spatial_contDiff hs).continuous.mul hbc).aestronglyMeasurable)
    (poisson_integrand_integrable hb hM ht x)
    (show AEStronglyMeasurable (F' t) volume from
      ((normalKernel_continuous m ht).mul hbc).aestronglyMeasurable)
    (show ∀ᵐ z : Space m ∂volume, ∀ s ∈ Ioo δ (2*t), ‖F' s z‖ ≤ bound z from by
      exact .of_forall fun z s hs => by
        dsimp only [F', bound]
        rw [norm_mul]
        calc
          _ ≤ (((m : ℝ)+2)/δ * poissonKernel m δ z)*‖b (x-z)‖ :=
            mul_le_mul_of_nonneg_right (normalKernel_bound m hδ hs.1.le z) (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hM _) (by positivity [kernel_pos m hδ z]))
    (((kernel_integrable m hδ).const_mul (((m : ℝ)+2)/δ)).mul_const M)
    (show ∀ᵐ z : Space m ∂volume, ∀ s ∈ Ioo δ (2*t),
        HasDerivAt (fun s => F s z) (F' s z) s from by
      exact .of_forall fun z s hs =>
        (hasDerivAt_kernel_height m (hδ.trans hs.1) z).mul_const (b (x-z)))
  exact hd.2

lemma point_add_normal {m : ℕ} (x : Space m) (t s : ℝ) :
    point x (t+s) = point x t+s • coordinate (m+1) (Fin.last m) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply]
  · simp [point, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply]

lemma harmonicLift_normalKernel_open {m : ℕ} {g : Space m → ℝ}
    (hgs : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    fderiv ℝ (harmonicLift g) (point x t) (coordinate (m+1) (Fin.last m)) =
      ∫ z, normalKernel m t z*g (x-z) := by
  obtain ⟨M,hM⟩ := hg.continuous.bounded_above_of_compact_support hgs
  have hp : point x t ∈ openHalfSpace m := by simpa [openHalfSpace] using ht
  have hA := (harmonicLift_differentiableAt_open hgs hg hp).hasFDerivAt
  have hcurve : HasDerivAt
      (fun s : ℝ => point x t+s • coordinate (m+1) (Fin.last m))
      (coordinate (m+1) (Fin.last m)) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinate (m+1) (Fin.last m))).const_add (point x t)
  have hfirst : HasDerivAt
      (harmonicLift g ∘ (fun s : ℝ => point x t+s • coordinate (m+1) (Fin.last m)))
      (fderiv ℝ (harmonicLift g) (point x t) (coordinate (m+1) (Fin.last m))) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 ?_ hcurve
    simpa only [zero_smul, add_zero] using hA
  have htcurve : HasDerivAt (fun s : ℝ => t+s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add t
  have hsecond : HasDerivAt (fun s : ℝ => poissonIntegral g (t+s) x)
      (∫ z, normalKernel m t z*g (x-z)) 0 := by
    have hslice : HasDerivAt (fun s => poissonIntegral g s x)
        (∫ z, normalKernel m t z*g (x-z)) (t+0) := by
      simpa only [add_zero] using hasDerivAt_poissonIntegral_height hg.continuous hM ht x
    convert! hslice.comp 0 htcurve using 1 <;> simp [Function.comp_def]
  have heq : (harmonicLift g ∘ (fun s : ℝ => point x t+s • coordinate (m+1) (Fin.last m)))
      =ᶠ[𝓝 (0 : ℝ)] (fun s => poissonIntegral g (t+s) x) := by
    have hcont : Continuous (fun s : ℝ => t+s) := continuous_const.add continuous_id
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      (show Ioi (0 : ℝ) ∈ 𝓝 (t+0) by simpa only [add_zero] using Ioi_mem_nhds ht)] with s hs
    dsimp only [Function.comp_apply]
    rw [← point_add_normal]
    exact lift_positive g x hs
  exact (hfirst.congr_of_eventuallyEq heq.symm).unique hsecond


lemma normalKernel_convolution_eq {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {b : Space m → ℝ}
    (hs : HasCompactSupport b) (hb : ContDiff ℝ 1 b)
    (hDb : ∀ i : Fin m, IsHolder α (tangent b i))
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    (∫ z, normalKernel m t z * b (x-z)) =
      -poissonIntegral (normalGenerator b) t x := by
  obtain ⟨hf2, hΛ2, hΛfreq⟩ := normalGenerator_L2_frequency hm hα hα1 hs hb hDb
  let f : Space m → ℂ := fun x => (b x : ℂ)
  let l : Space m → ℂ := fun x => (normalGenerator b x : ℂ)
  let kN : Space m → ℂ := fun z => (normalKernel m t z : ℂ)
  let kP : Space m → ℂ := fun z => (poissonKernel m t z : ℂ)
  let cN : Space m → ℂ := fun x => ∫ z, kN z*f (x-z)
  let cP : Space m → ℂ := fun x => ∫ z, kP z*l (x-z)
  have hkN : Integrable kN volume := (normalKernel_integrable m ht).ofReal
  have hkP : Integrable kP volume := (kernel_integrable m ht).ofReal
  have hkNF : 𝓕 kN = fun ξ =>
      ((-2*Real.pi*‖ξ‖ : ℝ) : ℂ) * (Real.exp (-2*Real.pi*t*‖ξ‖) : ℂ) := by
    funext ξ
    rw [← P201.fourierNormalization]
    exact normalKernel_fourier ht ξ
  have hkPF : 𝓕 kP = fun ξ => (Real.exp (-2*Real.pi*t*‖ξ‖) : ℂ) := by
    funext ξ
    rw [← P201.fourierNormalization]
    exact kernel_fourier ht ξ
  obtain ⟨hN2, hNF⟩ := convolution_L2_fourier_general kN f _ hkN hf2 hkNF
  obtain ⟨hP2, hPF⟩ := convolution_L2_fourier_general kP l _ hkP hΛ2 hkPF
  have hlp : hN2.toLp cN = -(hP2.toLp cP) := by
    apply (P102.Specs.U3.Riesz.F2 m).injective
    rw [map_neg]
    apply Lp.ext
    filter_upwards [hNF, hPF, hΛfreq,
      Lp.coeFn_neg (P102.Specs.U3.Riesz.F2 m (hP2.toLp cP))] with ξ hN hP hΛ hn
    change (P102.Specs.U3.Riesz.F2 m (hN2.toLp cN) : Space m → ℂ) ξ = _ at hN
    change (P102.Specs.U3.Riesz.F2 m (hP2.toLp cP) : Space m → ℂ) ξ = _ at hP
    rw [hn, Pi.neg_apply, hN, hP, hΛ]
    push_cast
    ring
  have hae : cN =ᵐ[volume] fun x => -cP x := by
    have he := congrArg (fun u : P102.Specs.U3.Riesz.L2 m => (u : Space m → ℂ)) hlp
    filter_upwards [hN2.coeFn_toLp, hP2.coeFn_toLp,
      Lp.coeFn_neg (hP2.toLp cP)] with y hyN hyP hyneg
    change (hN2.toLp cN : Space m → ℂ) y = cN y at hyN
    change (hP2.toLp cP : Space m → ℂ) y = cP y at hyP
    calc
      cN y = (hN2.toLp cN : Space m → ℂ) y := hyN.symm
      _ = (-(hP2.toLp cP) : P102.Specs.U3.Riesz.L2 m) y := congrFun he y
      _ = -(hP2.toLp cP : Space m → ℂ) y := hyneg
      _ = -cP y := congrArg Neg.neg hyP
  have hfc : Continuous f := Complex.continuous_ofReal.comp hb.continuous
  have hfcs : HasCompactSupport f := hs.comp_left (g := Complex.ofReal) rfl
  have hBf : BddAbove (range fun z => ‖f z‖) := (hfcs.norm.isCompact_range hfc.norm).bddAbove
  have hΛB : IsHolder α (normalGenerator b) :=
    normalGenerator_holder hm hα hα1 b (tangent_compactSupport hs) hDb
  obtain ⟨M, H, hM, hH, hsup, hhol⟩ := hΛB
  have hlc : Continuous l := Complex.continuous_ofReal.comp
    (P201.Elliptic.HolderCancellation.holder_continuous hα ⟨M,H,hM,hH,hsup,hhol⟩)
  have hBl : BddAbove (range fun z => ‖l z‖) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z,rfl⟩
    exact (Complex.norm_real _).le.trans (hsup z)
  have hcNc : Continuous cN :=
    hBf.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) hkN hfc
  have hcPc : Continuous cP :=
    hBl.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) hkP hlc
  have heq := congrFun ((hcNc.ae_eq_iff_eq volume hcPc.neg).mp hae) x
  have hcNreal : cN x = ((∫ z, normalKernel m t z*b (x-z) : ℝ) : ℂ) := by
    dsimp only [cN, kN, f]
    simp_rw [← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have hcPreal : cP x = (poissonIntegral (normalGenerator b) t x : ℂ) := by
    dsimp only [cP, kP, l, poissonIntegral, P201Specs.Elliptic.HalfSpaceLift.poissonIntegral]
    simp_rw [← Complex.ofReal_mul]
    exact integral_complex_ofReal
  rw [Pi.neg_apply, hcNreal, hcPreal, ← Complex.ofReal_neg] at heq
  exact Complex.ofReal_inj.mp heq

lemma harmonicLift_normal_open {m : ℕ} (hm : 1 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {b : Space m → ℝ}
    (hs : HasCompactSupport b) (hb : ContDiff ℝ 1 b)
    (hDb : ∀ i : Fin m, IsHolder α (tangent b i))
    {t : ℝ} (ht : 0 < t) (x : Space m) :
    fderiv ℝ (harmonicLift b) (point x t) (coordinate (m+1) (Fin.last m)) =
      -poissonIntegral (normalGenerator b) t x := by
  rw [harmonicLift_normalKernel_open hs hb ht x]
  exact normalKernel_convolution_eq hm hα hα1 hs hb hDb ht x


lemma poissonIntegral_neg {m : ℕ} (b : Space m → ℝ) (t : ℝ) (x : Space m) :
    P201Specs.Elliptic.HalfSpaceLift.poissonIntegral (fun y => -b y) t x = -P201Specs.Elliptic.HalfSpaceLift.poissonIntegral b t x := by
  change (∫ z, P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z * -b (x-z)) = -(∫ z, P201Specs.Elliptic.HalfSpaceLift.poissonKernel m t z * b (x-z))
  simp_rw [mul_neg]
  exact integral_neg _

lemma lift_neg {m : ℕ} (b : Space m → ℝ) (p : Space (m+1)) :
    P201Specs.Elliptic.HalfSpaceLift.harmonicLift (fun y => -b y) p = -P201Specs.Elliptic.HalfSpaceLift.harmonicLift b p := by
  by_cases hp : 0 < height p
  · change (if 0 < height p then _ else _) = -(if 0 < height p then _ else _)
    rw [ite_eq_left hp, ite_eq_left hp]
    exact poissonIntegral_neg b _ _
  · change (if 0 < height p then _ else _) = -(if 0 < height p then _ else _)
    rw [ite_eq_right hp, ite_eq_right hp]

set_option maxHeartbeats 800000 in
lemma halfSpaceLift_of_normal_formula
    (hnormal : ∀ {m : ℕ}, 1 ≤ m → ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {b : Space m → ℝ}, HasCompactSupport b → ContDiff ℝ 1 b →
      (∀ i : Fin m, IsHolder α (tangent b i)) → ∀ {t : ℝ}, 0 < t → ∀ x : Space m,
      fderiv ℝ (P201Specs.Elliptic.HalfSpaceLift.harmonicLift b) (point x t) (coordinate (m+1) (Fin.last m)) =
        -P201Specs.Elliptic.HalfSpaceLift.poissonIntegral (P201Specs.Elliptic.HalfSpaceLift.normalGenerator b) t x) :
    P201Specs.Elliptic.HalfSpaceLift.halfSpaceLiftStatement := by
  intro m hm α hα hα1 R hR
  obtain ⟨A, hA, hdata⟩ := lift_data_uniform_bounds hm hα hα1 hR
  let J := ∫ z : Space m, ‖z‖ ^ α * P201Specs.Elliptic.HalfSpaceLift.poissonKernel m 1 z
  have hJ : 0 ≤ J := integral_nonneg (fun z =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (kernel_pos m zero_lt_one z).le)
  let n : ℝ := m+1
  refine ⟨(3*(1+n+n*n) + n*(n*(1+J)))*A, by dsimp [n]; positivity, ?_⟩
  intro g hs hsupport hg
  let N := c2HolderNormOn α g univ
  obtain ⟨hN, hgB, hgjB, hgijB, hngB, hngjB, hlgB⟩ := hdata g hs hsupport hg
  have hc : ContDiff ℝ 2 g := contDiffOn_univ.mp hg.1
  have hc1 : ContDiff ℝ 1 g := hc.of_le (by norm_num)
  have hgj1 : ∀ j, ContDiff ℝ 1 (tangent g j) := fun j =>
    (hc.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hgjH : ∀ j, IsHolder α (tangent g j) := fun j => ⟨A*N, A*N, hgjB j⟩
  have hgijH : ∀ i j, IsHolder α (tangent (tangent g j) i) :=
    fun i j => ⟨A*N, A*N, hgijB i j⟩
  let b1 : Fin (m+1) → Space m → ℝ :=
    Fin.lastCases (fun x => -P201Specs.Elliptic.HalfSpaceLift.normalGenerator g x) (fun j => tangent g j)
  let b2 : Fin (m+1) → Fin (m+1) → Space m → ℝ := fun i =>
    Fin.lastCases
      (Fin.lastCases (fun x => -laplacian g x)
        (fun i x => -P201Specs.Elliptic.HalfSpaceLift.normalGenerator (tangent g i) x) i)
      (fun j => Fin.lastCases (fun x => -P201Specs.Elliptic.HalfSpaceLift.normalGenerator (tangent g j) x)
        (fun i => tangent (tangent g j) i) i)
  let d := fun j => P201Specs.Elliptic.HalfSpaceLift.harmonicLift (b1 j)
  let a := fun i j => P201Specs.Elliptic.HalfSpaceLift.harmonicLift (b2 i j)
  have hb1 : ∀ j, HolderBounds α (b1 j) (A*N) (A*N) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [b1, Fin.lastCases_last] using holderBounds_neg hngB
    · simpa only [b1, Fin.lastCases_castSucc] using hgjB j
  have hb2 : ∀ i j, HolderBounds α (b2 i j) (A*N) (A*N) := by
    intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [b2, Fin.lastCases_last] using holderBounds_neg hlgB
      · simpa only [b2, Fin.lastCases_last, Fin.lastCases_castSucc] using holderBounds_neg (hngjB i)
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [b2, Fin.lastCases_last, Fin.lastCases_castSucc] using holderBounds_neg (hngjB j)
      · simpa only [b2, Fin.lastCases_castSucc] using hgijB i j
  have he1p : ∀ t : ℝ, 0 < t → ∀ x : Space m, ∀ j : Fin (m+1),
      fderiv ℝ (P201Specs.Elliptic.HalfSpaceLift.harmonicLift g) (point x t) (coordinate (m+1) j) = d j (point x t) := by
    intro t ht x j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hnormal hm hα hα1 hs hc1 hgjH ht x]
      simp only [d, b1, Fin.lastCases_last, lift_positive _ _ ht, poissonIntegral_neg]
    · rw [harmonicLift_tangent_open hs hc1 ht x j]
      simp only [d, b1, Fin.lastCases_castSucc, lift_positive _ _ ht]
  have he1 : ∀ p ∈ openHalfSpace m, ∀ j, fderiv ℝ (P201Specs.Elliptic.HalfSpaceLift.harmonicLift g) p
      (coordinate (m+1) j) = d j p := by
    intro p hp j
    simpa only [point_horizontal_height] using he1p (height p) hp (horizontal p) j
  have hdeq : ∀ j, ∀ p ∈ openHalfSpace m,
      (fun q => fderiv ℝ (P201Specs.Elliptic.HalfSpaceLift.harmonicLift g) q (coordinate (m+1) j)) =ᶠ[𝓝 p] d j := by
    intro j p hp
    filter_upwards [(isOpen_openHalfSpace m).mem_nhds hp] with q hq
    exact he1 q hq j
  have hd : ∀ j, DifferentiableOn ℝ (d j) (openHalfSpace m) := by
    intro j p hp
    have hf := (harmonicLift_first_component_contDiffAt hs hc hp (coordinate (m+1) j)).differentiableAt (by norm_num)
    exact (hf.congr_of_eventuallyEq (hdeq j p hp).symm).differentiableWithinAt
  have hmixed : ∀ t : ℝ, 0 < t → ∀ (x : Space m) (j : Fin m),
      fderiv ℝ (fun p => fderiv ℝ (P201Specs.Elliptic.HalfSpaceLift.harmonicLift g) p (coordinate (m+1) j.castSucc))
        (point x t) (coordinate (m+1) (Fin.last m)) =
      -P201Specs.Elliptic.HalfSpaceLift.poissonIntegral (P201Specs.Elliptic.HalfSpaceLift.normalGenerator (tangent g j)) t x := by
    intro t ht x j
    have hp : point x t ∈ openHalfSpace m := by simpa [openHalfSpace] using ht
    rw [(harmonicLift_tangent_eventuallyEq_lift hs hc1 hp j).fderiv_eq]
    exact hnormal hm hα hα1 (tangent_compactSupport hs j) (hgj1 j)
      (fun i => hgijH i j) ht x
  have he2p : ∀ t : ℝ, 0 < t → ∀ x : Space m, ∀ i j : Fin (m+1),
      fderiv ℝ (d j) (point x t) (coordinate (m+1) i) = a i j (point x t) := by
    intro t ht x i j
    have hp : point x t ∈ openHalfSpace m := by simpa [openHalfSpace] using ht
    rw [← (hdeq j (point x t) hp).fderiv_eq]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [harmonicLift_normal_normal_open hs hc ht x]
        simp only [a, b2, Fin.lastCases_last, lift_positive _ _ ht, poissonIntegral_neg]
      · rw [harmonicLift_reverse_mixed_open hs hc ht x i, hmixed t ht x i]
        simp only [a, b2, Fin.lastCases_last, Fin.lastCases_castSucc, lift_positive _ _ ht, poissonIntegral_neg]
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [hmixed t ht x j]
        simp only [a, b2, Fin.lastCases_last, Fin.lastCases_castSucc, lift_positive _ _ ht, poissonIntegral_neg]
      · rw [harmonicLift_tangent_tangent_open hs hc ht x i j]
        simp only [a, b2, Fin.lastCases_castSucc, lift_positive _ _ ht]
  have he2 : ∀ p ∈ openHalfSpace m, ∀ i j, fderiv ℝ (d j) p
      (coordinate (m+1) i) = a i j p := by
    intro p hp i j
    simpa only [point_horizontal_height] using he2p (height p) hp (horizontal p) i j
  have hlift := c2HolderOn_closed_of_scalar_jets
    (fun p hp => (harmonicLift_contDiffAt_open hs hc hp).differentiableAt (by norm_num) |>.differentiableWithinAt)
    hd (lift_continuousOn_closed hα hα1 hgB)
    (fun j => lift_continuousOn_closed hα hα1 (hb1 j))
    (fun i j => lift_continuousOn_closed hα hα1 (hb2 i j)) he1 he2
    (mul_nonneg hA hN) (mul_nonneg (by linarith : 0 ≤ 1+J) (mul_nonneg hA hN))
    (fun p _ => lift_sup_bound hgB.2.2.1 p)
    (fun j p _ => lift_sup_bound (hb1 j).2.2.1 p)
    (fun i j p _ => lift_sup_bound (hb2 i j).2.2.1 p)
    (fun i j p hp q hq => lift_joint_holder hα hα1 (hb2 i j) hp hq)
  refine ⟨hlift.1, (fun p hp => harmonicLift_harmonic_open hs hc hp), lift_boundary g, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro t ht x
      refine ⟨fun j => harmonicLift_tangent_open hs hc1 ht x j,
        fun i j => harmonicLift_tangent_tangent_open hs hc ht x i j,
        hnormal hm hα hα1 hs hc1 hgjH ht x, fun j => hmixed t ht x j,
        harmonicLift_normal_normal_open hs hc ht x⟩
    · intro x
      have hp : point x 0 ∈ closedHalfSpace m := by simp [closedHalfSpace]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro j
        simpa only [d, b1, Fin.lastCases_castSucc, lift_boundary] using
          hlift.2.1 (point x 0) hp j.castSucc
      · simpa only [d, b1, Fin.lastCases_last, lift_boundary] using
          hlift.2.1 (point x 0) hp (Fin.last m)
      · intro i j
        simpa only [a, b2, Fin.lastCases_castSucc, lift_boundary] using
          hlift.2.2.1 (point x 0) hp i.castSucc j.castSucc
      · intro j
        simpa only [a, b2, Fin.lastCases_last, Fin.lastCases_castSucc, lift_boundary] using
          hlift.2.2.1 (point x 0) hp (Fin.last m) j.castSucc
      · simpa only [a, b2, Fin.lastCases_last, lift_boundary] using
          hlift.2.2.1 (point x 0) hp (Fin.last m) (Fin.last m)
  · exact ⟨A*N, A*N, hngB⟩
  · exact fun j => ⟨A*N, A*N, hngjB j⟩
  · convert hlift.2.2.2 using 1
    dsimp [n, J, N]
    push_cast
    ring

theorem halfSpaceLift : P201Specs.Elliptic.HalfSpaceLift.halfSpaceLiftStatement :=
  halfSpaceLift_of_normal_formula @harmonicLift_normal_open


end P201.Elliptic.HalfSpaceLift
