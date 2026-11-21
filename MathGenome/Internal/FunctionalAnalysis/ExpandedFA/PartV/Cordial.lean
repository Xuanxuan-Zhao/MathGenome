import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Cordial
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace ExpandedFA.PartV.Cordial
open CordialSpec

abbrev cordialOperator : OperatorType := operatorValue
abbrev cordialEigenvalue : EigenvalueType := eigenvalueValue

variable {𝕂 : Type*} [RCLike 𝕂] {T : ℝ}

/-- Evaluation at the left endpoint retains the necessary nonzero value. -/
theorem endpoint_identity : EndpointIdentity := by
  intro 𝕂 _ T hT f
  change (∫ θ in 0..Real.pi / 2, sample hT f ⟨0, le_rfl, hT.le⟩ θ) = _
  simp [sample]

theorem exact_norm : ExactNorm := by
  intro 𝕂 _ T hT
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  · let f : Space 𝕂 T := ContinuousMap.const _ 1
    have hf : ‖f‖ ≤ 1 := by
      apply (ContinuousMap.norm_le _ zero_le_one).mpr
      intro t
      simp [f]
    have hpoint := (operatorValue 𝕂 T hT f).norm_coe_le_norm ⟨0, le_rfl, hT.le⟩
    rw [endpoint_identity] at hpoint
    have hnorm : ‖(Real.pi / 2) • f ⟨0, le_rfl, hT.le⟩‖ = Real.pi / 2 := by
      simp [f, norm_smul]
    rw [hnorm] at hpoint
    exact hpoint.trans (((operatorValue 𝕂 T hT).le_opNorm f).trans
      (mul_le_of_le_one_right (norm_nonneg _) hf))

lemma sample_eq (hT : 0 < T) (f : Space 𝕂 T) (t : Interval T) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    sample hT f t θ = f ⟨t.1 * Real.sin θ,
      mul_nonneg t.2.1 (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])),
      (mul_le_of_le_one_right t.2.1 (Real.sin_le_one θ)).trans t.2.2⟩ := by
  unfold sample
  congr 1
  exact Set.projIcc_of_mem hT.le _

lemma power_ne_zero (hT : 0 < T) (r : ℝ) (hr : 0 ≤ r) : power 𝕂 T r hr ≠ 0 := by
  intro h
  have hx := congrArg (fun f : Space 𝕂 T => f ⟨T, hT.le, le_rfl⟩) h
  change ((T ^ r : ℝ) : 𝕂) = 0 at hx
  have hx' : T ^ r = 0 := RCLike.ofReal_eq_zero.mp hx
  exact (Real.rpow_pos_of_pos hT r).ne' hx'

theorem power_eigenfunctions : PowerEigenfunctions := by
  intro 𝕂 _ T hT r hr
  refine ⟨power_ne_zero hT r hr, ?_⟩
  ext t
  change (∫ θ in 0..Real.pi / 2, sample hT (power 𝕂 T r hr) t θ) =
    (eigenvalueValue r : 𝕂) * ((t.1 ^ r : ℝ) : 𝕂)
  calc
    _ = ∫ θ in 0..Real.pi / 2, (((Real.sin θ) ^ r : ℝ) : 𝕂) *
        ((t.1 ^ r : ℝ) : 𝕂) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      rw [sample_eq hT _ t hθ]
      change (((t.1 * Real.sin θ) ^ r : ℝ) : 𝕂) = _
      rw [Real.mul_rpow t.2.1
        (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])),
        RCLike.ofReal_mul, mul_comm]
    _ = _ := by rw [intervalIntegral.integral_mul_const, RCLike.intervalIntegral_ofReal]; rfl

lemma eigenvalue_zero : eigenvalueValue 0 = Real.pi / 2 := by
  simp [eigenvalueValue]

lemma continuous_sine_power (r : ℝ) (hr : 0 ≤ r) :
    Continuous (fun θ : ℝ => (Real.sin θ) ^ r) :=
  Real.continuous_sin.rpow_const (fun _ => Or.inr hr)

lemma eigenvalue_pos (r : ℝ) (hr : 0 ≤ r) : 0 < eigenvalueValue r := by
  apply intervalIntegral.integral_pos (by positivity)
    (continuous_sine_power r hr).continuousOn
  · intro θ hθ
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le
      (by linarith [hθ.2, Real.pi_pos])) _
  · refine ⟨Real.pi / 2, ⟨by positivity, le_rfl⟩, ?_⟩
    simp

lemma eigenvalue_strictAnti : StrictAntiOn eigenvalueValue (Ici 0) := by
  intro r hr s hs hrs
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity) (continuous_sine_power s hs).continuousOn
    (continuous_sine_power r hr).continuousOn
  · intro θ hθ
    exact Real.rpow_le_rpow_of_exponent_ge'
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos]))
      (Real.sin_le_one _) hr hrs.le
  · refine ⟨Real.pi / 6, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    rw [Real.sin_pi_div_six]
    exact Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hrs

lemma sine_power_bound {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    ‖(Real.sin θ) ^ r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])) _)]
  exact Real.rpow_le_one (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])) (Real.sin_le_one _) hr

lemma eigenvalue_continuous : ContinuousOn eigenvalueValue (Ici 0) := by
  intro r hr
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun r θ : ℝ => (Real.sin θ) ^ r) (bound := fun _ => 1)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (continuous_sine_power s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ae_of_all _ (fun θ hθ => sine_power_bound hs (by
      rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      exact ⟨hθ.1.le, hθ.2⟩))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun θ hθ => by
      rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      exact (Real.continuousAt_const_rpow (Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos])).ne').continuousWithinAt)

lemma eigenvalue_tendsto_zero : Tendsto eigenvalueValue atTop (𝓝 0) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := Real.pi / 2) (l := (atTop : Filter ℝ))
    (F := fun r θ : ℝ => (Real.sin θ) ^ r) (f := fun _ => (0 : ℝ)) (fun _ => 1)
  have hmeas : ∀ᶠ r : ℝ in atTop,
      AEStronglyMeasurable (fun θ => (Real.sin θ) ^ r) (volume.restrict (uIoc 0 (Real.pi / 2))) := by
    filter_upwards [eventually_ge_atTop 0] with r hr
    exact (continuous_sine_power r hr).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in atTop, ∀ᵐ θ : ℝ, θ ∈ uIoc 0 (Real.pi / 2) →
      ‖(Real.sin θ) ^ r‖ ≤ 1 := by
    filter_upwards [eventually_ge_atTop 0] with r hr
    exact ae_of_all _ (fun θ hθ => sine_power_bound hr (by
      rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      exact ⟨hθ.1.le, hθ.2⟩))
  have hlim : ∀ᵐ θ : ℝ, θ ∈ uIoc 0 (Real.pi / 2) →
      Tendsto (fun r : ℝ => (Real.sin θ) ^ r) atTop (𝓝 0) := by
    filter_upwards [volume.ae_ne (Real.pi / 2)] with θ hne hθ
    rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1],
      lt_of_le_of_ne hθ.2 hne⟩
    have hs1 : Real.sin θ < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_le_one θ]
    exact tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hs1
  change Tendsto (fun r : ℝ => ∫ θ in 0..Real.pi / 2, (Real.sin θ) ^ r) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using h hmeas hbound intervalIntegrable_const hlim

theorem eigenvalue_properties : EigenvalueProperties :=
  ⟨eigenvalue_zero, eigenvalue_pos, eigenvalue_continuous,
    eigenvalue_strictAnti, eigenvalue_tendsto_zero⟩

theorem noncompact : Noncompact := by
  intro 𝕂 _ T hT hcompact
  have hfin := ExpandedFA.Fredholm.compact_eigenvalues_finite_away_from_zero
    (operatorValue 𝕂 T hT) hcompact (eigenvalueValue 1) (eigenvalue_pos 1 (by norm_num))
  have hinj : Set.InjOn (fun r : ℝ => (eigenvalueValue r : 𝕂)) (Icc 0 1) := by
    intro r hr s hs he
    apply eigenvalue_strictAnti.injOn hr.1 hs.1
    exact RCLike.ofReal_injective he
  have hinf := (Set.Icc_infinite (zero_lt_one : (0 : ℝ) < 1)).image hinj
  apply hinf.not_finite
  apply hfin.subset
  rintro μ ⟨r, hr, rfl⟩
  refine ⟨⟨power 𝕂 T r hr.1, (power_eigenfunctions 𝕂 T hT r hr.1).1,
    (power_eigenfunctions 𝕂 T hT r hr.1).2⟩, ?_⟩
  rw [RCLike.norm_ofReal, abs_of_pos (eigenvalue_pos r hr.1)]
  exact eigenvalue_strictAnti.antitoneOn hr.1 (by norm_num) hr.2

lemma eigenvalue_mem_spectrum (hT : 0 < T) (r : ℝ) (hr : 0 ≤ r) :
    (eigenvalueValue r : 𝕂) ∈ spectrum 𝕂 (operatorValue 𝕂 T hT) := by
  change (eigenvalueValue r : 𝕂) ∈
    Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue _ _ _
  rw [ExpandedFA.BanachAlgebra.operator_spectrum_iff_no_bounded_inverse]
  rintro ⟨S, hleft, _⟩
  have he := hleft (power 𝕂 T r hr)
  rw [(power_eigenfunctions 𝕂 T hT r hr).2, sub_self, map_zero] at he
  exact (power_eigenfunctions 𝕂 T hT r hr).1 he.symm

theorem not_quasinilpotent : NotQuasinilpotent := by
  intro 𝕂 _ T hT hzero
  have hm := eigenvalue_mem_spectrum (𝕂 := 𝕂) hT 0 le_rfl
  have hle : (‖(eigenvalueValue 0 : 𝕂)‖₊ : ℝ≥0∞) ≤
      spectralRadius 𝕂 (operatorValue 𝕂 T hT) := by
    rw [_root_.spectralRadius_eq_of_unital (𝕜 := 𝕂) (operatorValue 𝕂 T hT)]
    exact le_iSup_of_le (eigenvalueValue 0 : 𝕂) (le_iSup_of_le hm le_rfl)
  rw [hzero, le_zero_iff, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hle
  have hz : eigenvalueValue 0 = 0 := RCLike.ofReal_eq_zero.mp hle
  rw [eigenvalue_zero] at hz
  exact (by positivity : (0 : ℝ) < Real.pi / 2).ne' hz

lemma kernel_cancellation {t θ : ℝ} (ht : 0 < t) (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    (t * Real.cos θ) * (t ^ 2 - (t * Real.sin θ) ^ 2) ^ (-(1 / 2 : ℝ)) = 1 := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hp : 0 < t * Real.cos θ := mul_pos ht hc
  have hid : t ^ 2 - (t * Real.sin θ) ^ 2 = (t * Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hid, Real.rpow_neg (sq_nonneg _) _, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq_eq_abs, abs_of_pos hp]
  exact mul_inv_cancel₀ hp.ne'

/-- The sine substitution is valid for the integrable singular kernel;
values at the two integration endpoints do not affect its integral. -/
theorem singular_identity : SingularIdentity := by
  intro 𝕂 _ T hT f t ht
  let g : ℝ → 𝕂 := fun s => (t.1 ^ 2 - s ^ 2) ^ (-(1 / 2 : ℝ)) •
    f (Set.projIcc 0 T hT.le s)
  have hcont : ContinuousOn (fun θ : ℝ => t.1 * Real.sin θ) (uIcc 0 (Real.pi / 2)) := by
    fun_prop
  have hder : ∀ θ ∈ Ioo (min 0 (Real.pi / 2)) (max 0 (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => t.1 * Real.sin θ) (t.1 * Real.cos θ) θ := by
    intro θ _
    exact (Real.hasDerivAt_sin θ).const_mul t.1
  have hnonneg : ∀ θ ∈ Ioo (min 0 (Real.pi / 2)) (max 0 (Real.pi / 2)),
      0 ≤ t.1 * Real.cos θ := by
    intro θ hθ
    simp only [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    exact mul_nonneg ht.le (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  have heq : EqOn (fun θ => (t.1 * Real.cos θ) • g (t.1 * Real.sin θ))
      (sample hT f t) (uIoo 0 (Real.pi / 2)) := by
    intro θ hθ
    rw [uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    change (t.1 * Real.cos θ) • ((t.1 ^ 2 - (t.1 * Real.sin θ) ^ 2) ^
      (-(1 / 2 : ℝ)) • f (Set.projIcc 0 T hT.le (t.1 * Real.sin θ))) = _
    rw [smul_smul, kernel_cancellation ht hθ, one_smul]
    rfl
  have hi : IntervalIntegrable (fun θ => (t.1 * Real.cos θ) • g (t.1 * Real.sin θ))
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_congr_uIoo heq).mpr (sample_integrable hT f t)
  have hgi := (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (g := g) hcont hder hnonneg).mp hi
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := g) hcont hder hnonneg
  simp only [Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hgi hsub
  refine ⟨hgi, ?_⟩
  change (∫ θ in 0..Real.pi / 2, sample hT f t θ) = ∫ s in 0..t.1, g s
  exact (intervalIntegral.integral_congr_uIoo heq).symm.trans hsub

lemma beta_cancellation {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ^ 2 + y ^ 2 = 1) (r : ℝ) :
    (x ^ 2) ^ ((r + 1) / 2 - 1) * (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1) *
      (2 * x * y) = 2 * x ^ r := by
  have hid : 1 - x ^ 2 = y ^ 2 := by linarith
  rw [hid, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (sq_nonneg _) _, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hy]
  have hp : (x ^ 2) ^ ((r + 1) / 2 - 1) * x = x ^ r := by
    rw [← Real.rpow_two x, ← Real.rpow_mul hx.le,
      show (2 : ℝ) * ((r + 1) / 2 - 1) = r - 1 by ring,
      ← Real.rpow_add_one hx.ne', sub_add_cancel]
  calc
    _ = 2 * ((x ^ 2) ^ ((r + 1) / 2 - 1) * x) * (y⁻¹ * y) := by ring
    _ = _ := by rw [hp, inv_mul_cancel₀ hy.ne', mul_one]

/-- Euler's beta substitution u = sin² θ, with both endpoints ignored only
inside the integral. The r = 0 case is included. -/
theorem beta_formula : BetaFormula := by
  intro r hr
  let g : ℝ → ℝ := fun u => u ^ ((r + 1) / 2 - 1) * (1 - u) ^ ((1 / 2 : ℝ) - 1)
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin θ) ^ 2) (uIcc 0 (Real.pi / 2)) := by
    fun_prop
  have hder : ∀ θ ∈ Ioo (min 0 (Real.pi / 2)) (max 0 (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => (Real.sin θ) ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    intro θ _
    convert (Real.hasDerivAt_sin θ).pow 2 using 1; simp
  have hnonneg : ∀ θ ∈ Ioo (min 0 (Real.pi / 2)) (max 0 (Real.pi / 2)),
      0 ≤ 2 * Real.sin θ * Real.cos θ := by
    intro θ hθ
    simp only [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := g) hcont hder hnonneg
  simp only [Real.sin_zero, zero_pow (by norm_num : 2 ≠ 0), Real.sin_pi_div_two, one_pow] at hsub
  have heq : (Ioo 0 (Real.pi / 2)).EqOn
      (fun θ => g ((Real.sin θ) ^ 2) * (2 * Real.sin θ * Real.cos θ))
      (fun θ => 2 * (Real.sin θ) ^ r) := by
    intro θ hθ
    exact beta_cancellation (Real.sin_pos_of_pos_of_lt_pi hθ.1
      (by linarith [hθ.2, Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      (Real.sin_sq_add_cos_sq θ) r
  have hbet : beta ((r + 1) / 2) (1 / 2) = 2 * eigenvalueValue r := by
    change (∫ u in (0 : ℝ)..1, g u) = _
    rw [← hsub]
    simp only [Function.comp_apply]
    rw [intervalIntegral.integral_congr_Ioo_of_le (by positivity) heq,
      intervalIntegral.integral_const_mul]
    rfl
  linarith

end ExpandedFA.PartV.Cordial
