import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.RieszKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

noncomputable section
namespace ExpandedFA.PartIV.RieszKernel
open ExpandedFA.Fourier

theorem constant_positive : Specs.ExpandedFA.PartIV.RieszKernel.constantPositiveType := by
  intro d a ha had
  unfold rieszConstant
  exact div_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

/-- The scaled Euler integral, including its absolute convergence. -/
theorem mellin_exp {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(r * t))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t ^ (s - 1) * Real.exp (-(r * t))) =
      r ^ (-s) * Real.Gamma s := by
  constructor
  · have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) 0 hr).2
        (by simpa using Real.GammaIntegral_convergent hs)
    apply (h.const_mul (r ^ (-(s - 1)))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.mul_rpow hr.le ht.le, Real.rpow_neg hr.le]
    have hne : r ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp
  · rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div,
      Real.inv_rpow hr.le, Real.rpow_neg hr.le]

theorem gaussian_superposition :
    Specs.ExpandedFA.PartIV.RieszKernel.gaussianSuperpositionType := by
  intro d a ha x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : 0 < Real.pi * ‖x‖ ^ 2 := by positivity
  obtain ⟨hi, he⟩ := mellin_exp (show 0 < a / 2 by linarith) hr
  have hexp : ∀ t : ℝ, -(Real.pi * ‖x‖ ^ 2 * t) = -Real.pi * t * ‖x‖ ^ 2 := by
    intro t; ring
  simp_rw [hexp] at hi he
  refine ⟨hi, ?_⟩
  have hc : (∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian t x) =
      ((Real.pi * ‖x‖ ^ 2) ^ (-(a / 2)) * Real.Gamma (a / 2) : ℝ) := by
    rw [← he, ← integral_complex_ofReal]
    congr 1
    funext t
    simp [gaussian]
  rw [hc]
  unfold powerKernel
  rw [← Complex.ofReal_mul]
  congr 1
  rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
    ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul hn.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-(a / 2)) = -a by ring]
  have hg := (Real.Gamma_pos_of_pos (show 0 < a / 2 by linarith)).ne'
  have hp : Real.pi ^ (a / 2) * Real.pi ^ (-(a / 2)) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]; simp
  field_simp
  nlinarith [congrArg (fun r : ℝ => r * ‖x‖ ^ (-a)) hp]

/-- Ordinary Gaussian Fourier transform in the same Euclidean model and
normalisation as the adopted scalar-linear Schwartz dual. -/
theorem gaussian_fourier {d : ℕ} {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    integralFourier (gaussian t) ξ =
      ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * gaussian t⁻¹ ξ := by
  rw [integralFourier_eq_native]
  have hg : gaussian (d := d) t =
      fun x : Euclidean d => Complex.exp (-(Real.pi * t : ℂ) * ‖x‖ ^ 2) := by
    funext x
    unfold gaussian
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hg, fourier_gaussian_innerProductSpace (by simpa using mul_pos Real.pi_pos ht)]
  rw [show Module.finrank ℝ (Euclidean d) = d by simp [Euclidean]]
  have hpow : (Real.pi : ℂ) / (Real.pi * t : ℂ) = (t⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv]
    field_simp
  rw [hpow, show (d : ℂ) / 2 = ((d : ℝ) / 2 : ℝ) by push_cast; rfl,
    ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le,
    ← Real.rpow_neg ht.le]
  congr 1
  · congr 2; ring
  · unfold gaussian
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp

@[simp] theorem norm_powerKernel {d : ℕ} (a : ℝ) (x : Euclidean d) :
    ‖powerKernel a x‖ = ‖x‖ ^ (-a) := by
  simp [powerKernel, Real.rpow_nonneg (norm_nonneg x)]

theorem powerKernel_measurable {d : ℕ} (a : ℝ) :
    Measurable (powerKernel (d := d) a) := by
  unfold powerKernel
  exact Complex.measurable_ofReal.comp (measurable_norm.pow_const _)

theorem powerKernel_ball_integrable {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d) :
    IntegrableOn (powerKernel (d := d) a) (Metric.ball 0 1) := by
  have hd : 1 ≤ d := by have : (0 : ℝ) < d := ha.trans had; exact Nat.one_le_iff_ne_zero.mpr (by intro h; simp [h] at this)
  apply integrableOn_ball_of_norm_le_rpow (by simpa [Euclidean] using hd)
    (α := a) (C := 1) (by simpa [Euclidean] using had)
  · exact Filter.Eventually.of_forall (by intro x; simp)
  · exact (powerKernel_measurable a).aestronglyMeasurable

theorem powerKernel_le_one {d : ℕ} {a : ℝ} (ha : 0 ≤ a) {x : Euclidean d}
    (hx : x ∉ Metric.ball (0 : Euclidean d) 1) : ‖powerKernel a x‖ ≤ 1 := by
  rw [norm_powerKernel]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simpa using hx) (by linarith)

theorem kernel_pairing_integrable {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d)
    (φ : Schwartz ℂ d) : Integrable (fun x => powerKernel a x * φ x) := by
  rw [← integrableOn_univ, ← Set.union_compl_self (Metric.ball (0 : Euclidean d) 1),
    integrableOn_union]
  constructor
  · exact (powerKernel_ball_integrable ha had).mul_bdd
      φ.continuous.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun x => φ.norm_le_seminorm ℂ x)
  · exact φ.integrable.integrableOn.bdd_mul
      (powerKernel_measurable a).aestronglyMeasurable.restrict
      (by filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
          exact powerKernel_le_one ha.le hx)

theorem kernel_pairing_bound {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d)
    (φ : Schwartz ℂ d) :
    ‖∫ x, powerKernel a x * φ x‖ ≤
      (∫ x in Metric.ball (0 : Euclidean d) 1, ‖powerKernel a x‖) *
        SchwartzMap.seminorm ℂ 0 0 φ + ‖φ.toLp 1 volume‖ := by
  let B := Metric.ball (0 : Euclidean d) 1
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hi : Integrable (B.indicator fun x => ‖powerKernel a x‖) :=
    (integrable_indicator_iff hB).2 (powerKernel_ball_integrable ha had).norm
  have hb : ∀ x, ‖powerKernel a x * φ x‖ ≤
      B.indicator (fun x => ‖powerKernel a x‖) x * SchwartzMap.seminorm ℂ 0 0 φ + ‖φ x‖ := by
    intro x
    rw [norm_mul]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact (mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ x) (norm_nonneg _)).trans
        (le_add_of_nonneg_right (norm_nonneg _))
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_add]
      simpa using mul_le_mul_of_nonneg_right (powerKernel_le_one ha.le hx) (norm_nonneg (φ x))
  calc
    _ ≤ ∫ x, ‖powerKernel a x * φ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B.indicator (fun x => ‖powerKernel a x‖) x *
        SchwartzMap.seminorm ℂ 0 0 φ + ‖φ x‖ :=
      integral_mono (kernel_pairing_integrable ha had φ).norm
        ((hi.mul_const _).add φ.integrable.norm) hb
    _ = _ := by
      rw [integral_add (hi.mul_const _) φ.integrable.norm,
        integral_mul_const, integral_indicator hB, SchwartzMap.norm_toLp_one]

/-- The singular function defines a continuous, scalar-linear Schwartz dual
functional. Continuity follows from a finite family of actual Schwartz seminorms. -/
def kernelDistribution {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d) : Tempered ℂ d :=
  SchwartzMap.mkCLMtoNormedSpace (fun φ : Schwartz ℂ d => ∫ x, powerKernel a x * φ x)
    (by
      intro φ ψ
      simp only [add_apply, mul_add]
      exact integral_add (kernel_pairing_integrable ha had φ) (kernel_pairing_integrable ha had ψ))
    (by
      intro c φ
      simp only [smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm (powerKernel a _) c]
      exact integral_const_mul c _)
    (by
      obtain ⟨k, C, hC, hbound⟩ := SchwartzMap.norm_toLp_le_seminorm ℂ ℂ 1
        (volume : Measure (Euclidean d))
      let I := ∫ x in Metric.ball (0 : Euclidean d) 1, ‖powerKernel a x‖
      have hI : 0 ≤ I := integral_nonneg (fun _ => norm_nonneg _)
      refine ⟨Finset.Iic (k, 0), I + C, add_nonneg hI hC, fun φ => ?_⟩
      have hzero : SchwartzMap.seminorm ℂ 0 0 φ ≤
          (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
        apply Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℂ (Euclidean d) ℂ)
          (show (0, 0) ∈ Finset.Iic (k, 0) by simp)) φ
      have h := kernel_pairing_bound ha had φ
      dsimp only [I] at hI ⊢
      nlinarith [hbound φ])

@[simp] theorem kernelDistribution_apply {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d)
    (φ : Schwartz ℂ d) : kernelDistribution ha had φ = ∫ x, powerKernel a x * φ x := rfl

theorem mellin_gaussian_integral {d : ℕ} {a : ℝ} (ha : 0 < a)
    {x : Euclidean d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (a / 2 - 1) *
      Real.exp (-Real.pi * t * ‖x‖ ^ 2)) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), t ^ (a / 2 - 1) * Real.exp (-Real.pi * t * ‖x‖ ^ 2)) =
      (Real.pi ^ (-(a / 2)) * Real.Gamma (a / 2)) * ‖x‖ ^ (-a) := by
  obtain ⟨hi, he⟩ := mellin_exp (show 0 < a / 2 by linarith)
    (show 0 < Real.pi * ‖x‖ ^ 2 by positivity)
  have hexp : ∀ t : ℝ, -(Real.pi * ‖x‖ ^ 2 * t) = -Real.pi * t * ‖x‖ ^ 2 := by
    intro t; ring
  simp_rw [hexp] at hi he
  refine ⟨hi, he.trans ?_⟩
  rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
    ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-(a / 2)) = -a by ring]
  ring

theorem ae_ne_zero {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d) :
    ∀ᵐ x : Euclidean d, x ≠ 0 := by
  have hd : 0 < d := by exact_mod_cast ha.trans had
  have : Nontrivial (Euclidean d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa [Euclidean] using hd)
  exact ae_iff.mpr (by simp)

theorem superposition_integrable :
    Specs.ExpandedFA.PartIV.RieszKernel.superpositionIntegrableType := by
  intro d a ha had φ
  let F : ℝ × Euclidean d → ℂ := fun p =>
    ((p.1 ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian p.1 p.2 * φ p.2
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Ioi 0)).prod volume) := by
    dsimp [F, gaussian]
    fun_prop
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards [ae_ne_zero ha had] with x hx
    have hi := (mellin_gaussian_integral ha hx).1.ofReal.mul_const (φ x)
    simpa [F, gaussian, Complex.ofReal_mul] using hi
  · have hinner : (fun x : Euclidean d => ∫ t in Ioi (0 : ℝ), ‖F (t, x)‖) =ᵐ[volume]
        fun x => (Real.pi ^ (-(a / 2)) * Real.Gamma (a / 2)) *
          ‖powerKernel a x * φ x‖ := by
      filter_upwards [ae_ne_zero ha had] with x hx
      have hnorm : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖F (t, x)‖ =
          (t ^ (a / 2 - 1) * Real.exp (-Real.pi * t * ‖x‖ ^ 2)) * ‖φ x‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp only [F, gaussian, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg ht.le _), abs_of_pos (Real.exp_pos _)]
      rw [integral_congr_ae hnorm, integral_mul_const, (mellin_gaussian_integral ha hx).2,
        norm_mul, norm_powerKernel]
      ring
    exact ((kernel_pairing_integrable ha had φ).norm.const_mul _).congr hinner.symm

/-- Fubini for the Gaussian superposition, on every Schwartz test. -/
theorem kernel_superposition_pairing {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d)
    (φ : Schwartz ℂ d) :
    (∫ x, powerKernel a x * φ x) =
      ((Real.pi ^ (a / 2) / Real.Gamma (a / 2) : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) *
          ∫ x, gaussian t x * φ x := by
  let c : ℂ := (Real.pi ^ (a / 2) / Real.Gamma (a / 2) : ℝ)
  calc
    _ = ∫ x, c * ((∫ t in Ioi (0 : ℝ),
        ((t ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian t x) * φ x) := by
      apply integral_congr_ae
      filter_upwards [ae_ne_zero ha had] with x hx
      rw [(gaussian_superposition d a ha x hx).2]
      exact mul_assoc _ _ _
    _ = c * ∫ x, ∫ t in Ioi (0 : ℝ),
        ((t ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian t x * φ x := by
      simp_rw [integral_mul_const]
      rw [integral_const_mul]
    _ = c * ∫ t in Ioi (0 : ℝ), ∫ x,
        ((t ^ (a / 2 - 1) : ℝ) : ℂ) * gaussian t x * φ x :=
      congrArg (c * ·) (integral_integral_swap (superposition_integrable d a ha had φ)).symm
    _ = _ := by simp_rw [mul_assoc, integral_const_mul]; rfl

theorem gaussian_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (gaussian (d := d) t) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean d) (b := (Real.pi * t : ℝ))
    (by simpa using mul_pos Real.pi_pos ht) 0 0
  convert h using 1
  funext x
  simp only [zero_mul, add_zero]
  unfold gaussian
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem gaussian_fourier_pairing {d : ℕ} {t : ℝ} (ht : 0 < t) (φ : Schwartz ℂ d) :
    (∫ x, gaussian t x * schwartzFourier φ x) =
      ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ ξ, gaussian t⁻¹ ξ * φ ξ := by
  have h : (∫ ξ, integralFourier (gaussian t) ξ * φ ξ) =
      ∫ x, gaussian t x * integralFourier φ x := by
    simp_rw [integralFourier_eq_native]
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ (Euclidean d))
      Real.continuous_fourierChar continuous_inner (gaussian_integrable ht)
        (φ.integrable (μ := volume))
  simp_rw [← schwartz_integral d φ, gaussian_fourier ht] at h
  rw [← h]
  simp_rw [mul_assoc, integral_const_mul]

/-- The reciprocal change of variable in the Mellin integral. It is valid for
arbitrary Bochner integrands; convergence in its applications was proved above. -/
theorem reciprocal_mellin (d : ℕ) (a : ℝ) (g : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) *
        ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * g t⁻¹) =
      ∫ t in Ioi (0 : ℝ), ((t ^ (((d : ℝ) - a) / 2 - 1) : ℝ) : ℂ) * g t := by
  have h := integral_comp_rpow_Ioi
    (fun t : ℝ => ((t ^ (((d : ℝ) - a) / 2 - 1) : ℝ) : ℂ) * g t)
    (p := -1) (by norm_num)
  calc
    _ = ∫ t in Ioi (0 : ℝ), (|-1| * t ^ ((-1 : ℝ) - 1)) •
        ((((t ^ (-1 : ℝ)) ^ (((d : ℝ) - a) / 2 - 1) : ℝ) : ℂ) * g (t ^ (-1 : ℝ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hc : t ^ (a / 2 - 1) * t ^ (-(d : ℝ) / 2) =
          t ^ ((-1 : ℝ) - 1) * t⁻¹ ^ (((d : ℝ) - a) / 2 - 1) := by
        rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, ← Real.rpow_add ht,
          ← Real.rpow_add ht]
        congr 1
        ring
      simp only [Real.rpow_neg_one, abs_neg, abs_one, one_mul, Complex.real_smul]
      calc
        _ = (((t ^ (a / 2 - 1) * t ^ (-(d : ℝ) / 2)) : ℝ) : ℂ) * g t⁻¹ := by
          push_cast; ring
        _ = (((t ^ ((-1 : ℝ) - 1) * t⁻¹ ^ (((d : ℝ) - a) / 2 - 1)) : ℝ) : ℂ) * g t⁻¹ := by rw [hc]
        _ = _ := by push_cast; ring
    _ = _ := h

theorem riesz_constant_normalization (d : ℕ) {a : ℝ} (ha : 0 < a) (had : a < d) :
    rieszConstant d a *
      (Real.pi ^ (((d : ℝ) - a) / 2) / Real.Gamma (((d : ℝ) - a) / 2)) =
        Real.pi ^ (a / 2) / Real.Gamma (a / 2) := by
  have hga : Real.Gamma (a / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hgb : Real.Gamma (((d : ℝ) - a) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : Real.pi ^ (a - (d : ℝ) / 2) * Real.pi ^ (((d : ℝ) - a) / 2) =
      Real.pi ^ (a / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  unfold rieszConstant
  field_simp [hga, hgb]
  convert hp using 1
  congr 2
  ring

theorem kernel_fourier {d : ℕ} {a : ℝ} (ha : 0 < a) (had : a < d) :
    temperedFourier (kernelDistribution ha had) =
      (rieszConstant d a : ℂ) •
        kernelDistribution (a := (d : ℝ) - a) (by linarith) (by linarith) := by
  have hb : 0 < (d : ℝ) - a := by linarith
  have hbd : (d : ℝ) - a < d := by linarith
  ext φ
  change (∫ x, powerKernel a x * schwartzFourier φ x) =
    (rieszConstant d a : ℂ) * (∫ x, powerKernel ((d : ℝ) - a) x * φ x)
  rw [kernel_superposition_pairing ha had, kernel_superposition_pairing hb hbd]
  have hinner :
      (∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) *
        ∫ x, gaussian t x * schwartzFourier φ x) =
      ∫ t in Ioi (0 : ℝ), ((t ^ (((d : ℝ) - a) / 2 - 1) : ℝ) : ℂ) *
        ∫ x, gaussian t x * φ x := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), ((t ^ (a / 2 - 1) : ℝ) : ℂ) *
          ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ x, gaussian t⁻¹ x * φ x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [gaussian_fourier_pairing ht φ, mul_assoc]
      _ = _ := reciprocal_mellin d a (fun t => ∫ x, gaussian t x * φ x)
  rw [hinner, ← mul_assoc, ← Complex.ofReal_mul, riesz_constant_normalization d ha had]

theorem riesz_fourier : Specs.ExpandedFA.PartIV.RieszKernel.rieszFourierType := by
  intro d a ha had
  have hb : 0 < (d : ℝ) - a := by linarith
  have hbd : (d : ℝ) - a < d := by linarith
  refine ⟨kernelDistribution ha had, kernelDistribution hb hbd, ?_, ?_, kernel_fourier ha had⟩
  · exact fun φ => ⟨kernel_pairing_integrable ha had φ, rfl⟩
  · exact fun φ => ⟨kernel_pairing_integrable hb hbd φ, rfl⟩

end ExpandedFA.PartIV.RieszKernel
