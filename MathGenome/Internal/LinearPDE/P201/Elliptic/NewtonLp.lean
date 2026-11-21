import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NewtonLp
import MathGenome.Internal.LinearPDE.P201.Potential.NewtonPotential
import MathGenome.Internal.LinearPDE.P201.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201.Elliptic.WholeSpaceW2p
import MathGenome.Internal.FourierSobolev.P102.U2.Young
import Batteries.Tactic.OpenPrivate

import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import MathGenome.Internal.FourierSobolev.P102.U4.SchwartzRestriction
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal ContDiff Pointwise Topology
namespace P201.Elliptic.NewtonLp
open private oneCoord oneCoord_norm oneCoord_coordinate oneCoord_symm_measurePreserving
  from MathGenome.Internal.LinearPDE.P201.Elliptic.NewtonHessian
open private omega_one from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental


/-- The integral agrees with the library's ordinary convolution, pointwise,
including at points where the Bochner integral is totalized. -/
lemma potential_eq_functionConvolution {n : ℕ} (F : P201.Space n → ℝ) :
    P201Specs.Elliptic.NewtonHessian.holderPotential F =
      P102.U4.functionConvolution (P201.fundamentalKernel n) F :=
  P201.Elliptic.NewtonHessian.holderPotential_eq_functionConvolution F

/-- Extend the compact-distribution equation to arbitrary compactly supported
Lᵖ functions by identifying the actual locally integrable convolution. -/
theorem potentialEquation : P201Specs.Elliptic.NewtonLp.PotentialEquationStatement := by
  intro n hn p hp F hF hsupport
  have hFloc := hF.locallyIntegrable hp
  have hΦ := P201.fundamentalLocalIntegrability n hn
  obtain ⟨hexists, hloc⟩ := P102.U4.functionConvolution_locallyIntegrable
    (P201.fundamentalKernel n) F hΦ hFloc (Or.inr hsupport)
  have hS := P102.U4.regularDistribution_compactSupport_of_essential F hFloc hsupport
  have hconv := P102.U4.rightCompactConvolution_regular
    (P201.fundamentalKernel n) F hΦ hFloc (Or.inr hsupport) hS
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hexists] with x hx
    simpa only [sub_sub_cancel] using hx.comp_sub_left x
  · rwa [potential_eq_functionConvolution]
  · rw [potential_eq_functionConvolution]
    have heq : P201Specs.regularDistribution (⊤ : P201Specs.Domain n)
        (P102.U4.functionConvolution (P201.fundamentalKernel n) F) =
        P201Specs.newtonDistribution (P201Specs.regularDistribution ⊤ F) hS := hconv.symm
    rw [heq]
    exact P201.newtonDistributionEquation n hn (P201.regularDistribution ⊤ F) hS

/-- Localize the kernel to B-A and apply L¹*Lᵖ → Lᵖ Young. -/
theorem localKernelEstimate : P201Specs.Elliptic.NewtonLp.LocalKernelEstimateStatement := by
  intro n k hk p hp A B
  let D : Set (P201.Space n) := (B : Set (P201.Space n)) - (A : Set (P201.Space n))
  have hD : IsCompact D := P102.U4.compact_sub_set B.isCompact A.isCompact
  have hkD : Integrable (D.indicator k) volume :=
    (hk.integrableOn_isCompact hD).integrable_indicator hD.measurableSet
  refine ⟨(eLpNorm (D.indicator k) 1 volume).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro F hF hA
  have hY := P102.U2.Young.young volume (p := 1) (q := p) (r := p)
    le_rfl hp hp (by simp) (memLp_one_iff_integrable.mpr hkD) hF
  have heq : P102.U4.functionConvolution k F =ᵐ[volume.restrict B]
      P102.U4.functionConvolution (D.indicator k) F := by
    filter_upwards [ae_restrict_mem B.isCompact.measurableSet] with x hx
    exact integral_congr_ae (P102.U4.convolution_localization_right k F A B hA x hx)
  have hmem : MemLp (P102.U4.functionConvolution k F) p (volume.restrict B) :=
    by
      apply (memLp_congr_ae heq).mpr
      change MemLp (fun x => ∫ y, D.indicator k (x-y) * F y) p (volume.restrict (B : Set (P201.Space n)))
      exact hY.2.1.restrict (B : Set (P201.Space n))
  refine ⟨hmem, ?_⟩
  have hb : eLpNorm (P102.U4.functionConvolution k F) p (volume.restrict B) ≤
      eLpNorm (D.indicator k) 1 volume * eLpNorm F p volume := by
    rw [eLpNorm_congr_ae heq]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hY.2.2.1
  have hfinite : eLpNorm (D.indicator k) 1 volume * eLpNorm F p volume ≠ ⊤ :=
    ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hkD).eLpNorm_ne_top hF.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono hfinite hb

/-- Bounds for the potential and all first derivative convolution integrals.
Both the logarithmic kernel and the one-dimensional kernel are included. -/
theorem lowerOrderEstimate : P201Specs.Elliptic.NewtonLp.LowerOrderEstimateStatement := by
  intro n hn p hp A B
  obtain ⟨C₀, hC₀, h₀⟩ := localKernelEstimate n (P201.fundamentalKernel n)
    (P201.fundamentalLocalIntegrability n hn) p hp A B
  have hg (i : Fin n) := localKernelEstimate n
    (P201Specs.Elliptic.NewtonHessian.gradientKernel i)
    (P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable hn i) p hp A B
  choose C hC hbound using hg
  refine ⟨C₀ + ∑ i : Fin n, C i, add_nonneg hC₀ (Finset.sum_nonneg fun i _ => hC i), ?_⟩
  intro F hF hA
  obtain ⟨hm₀, hb₀⟩ := h₀ F hF hA
  have hb (i : Fin n) := hbound i F hF hA
  rw [← potential_eq_functionConvolution F] at hm₀ hb₀
  refine ⟨hm₀, fun i => (hb i).1, ?_⟩
  calc
    _ ≤ C₀ * (eLpNorm F p volume).toReal +
        ∑ i : Fin n, C i * (eLpNorm F p volume).toReal :=
      add_le_add hb₀ (Finset.sum_le_sum fun i _ => (hb i).2)
    _ = _ := by rw [add_mul, Finset.sum_mul]

/-- Integration by parts across the corner of the line fundamental solution.
The boundary contribution at zero vanishes because the kernel is continuous. -/
lemma lineFundamental_pairing {q : ℝ → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hc : HasCompactSupport q) :
    (∫ t, -|t| / 2 * deriv q t) =
      -((∫ t in Iic (0 : ℝ), q t) / 2 - (∫ t in Ioi (0 : ℝ), q t) / 2) := by
  have hqi : Integrable q volume := hq.continuous.integrable_of_hasCompactSupport hc
  have hdq : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have htd : Integrable (fun t => t * deriv q t) volume :=
    (continuous_id.mul hdq).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hp : ContDiff ℝ 1 (fun t => t * q t) := contDiff_id.mul (hq.of_le (by simp))
  have hpc : HasCompactSupport (fun t => t * q t) := hc.mul_left
  have hpd : deriv (fun t => t * q t) = fun t => q t + t * deriv q t := by
    funext t
    convert! ((hasDerivAt_id t).mul
      ((hq.differentiable (by simp) t).hasDerivAt)).deriv using 1 <;> simp
  have hleft := hpc.integral_Iic_deriv_eq hp 0
  have hright := hpc.integral_Ioi_deriv_eq hp 0
  rw [hpd, integral_add hqi.integrableOn htd.integrableOn] at hleft hright
  simp only [zero_mul, neg_zero] at hleft hright
  have hfi : Integrable (fun t => -|t| / 2 * deriv q t) volume :=
    ((continuous_abs.neg.div_const 2).mul hdq).integrable_of_hasCompactSupport hc.deriv.mul_left
  rw [← intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn]
  have heL : (∫ t in Iic (0 : ℝ), -|t| / 2 * deriv q t) =
      (∫ t in Iic (0 : ℝ), t * deriv q t) / 2 := by
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    change -|t| / 2 * deriv q t = t * deriv q t / 2
    rw [abs_of_nonpos (show t ≤ 0 from ht)]
    ring
  have heR : (∫ t in Ioi (0 : ℝ), -|t| / 2 * deriv q t) =
      -(∫ t in Ioi (0 : ℝ), t * deriv q t) / 2 := by
    rw [← integral_neg, ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -|t| / 2 * deriv q t = -(t * deriv q t) / 2
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  rw [heL, heR]
  linarith

/-- The line gradient integral is the signed half-line integral. The value at
zero is irrelevant only after using the actual non-atomic volume measure. -/
lemma lineGradient_pairing {q : ℝ → ℝ} (hq : Continuous q) (hc : HasCompactSupport q) :
    (∫ t, -t / (2 * |t|) * q t) =
      (∫ t in Iic (0 : ℝ), q t) / 2 - (∫ t in Ioi (0 : ℝ), q t) / 2 := by
  have hi := hq.integrable_of_hasCompactSupport (μ := volume) hc
  have he : (fun t => -t / (2 * |t|) * q t) =ᵐ[volume]
      fun t => (Iic (0 : ℝ)).indicator (fun t => q t / 2) t -
        (Ioi (0 : ℝ)).indicator (fun t => q t / 2) t := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    by_cases h : t ≤ 0
    · have hneg : t < 0 := lt_of_le_of_ne h ht
      simp only [Set.indicator_apply, mem_Iic, mem_Ioi, ite_eq_left h, ite_eq_right (not_lt.mpr h),
        sub_zero, abs_of_neg hneg]
      field_simp
    · have hpos : 0 < t := lt_of_not_ge h
      simp only [Set.indicator_apply, mem_Iic, mem_Ioi, ite_eq_right h, ite_eq_left hpos,
        zero_sub, abs_of_pos hpos]
      field_simp
  rw [integral_congr_ae he,
    integral_sub ((hi.div_const 2).indicator measurableSet_Iic)
      ((hi.div_const 2).indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi,
    integral_div, integral_div]

/-- The first derivative kernel is valid in dimension one as well. -/
lemma fundamental_distribution_gradient_one :
    P201.distributionDerivative ({0} : P201.MultiIndex 1)
      (P201.regularDistribution (⊤ : P201.Domain 1) (P201.fundamentalKernel 1)) =
      P201.regularDistribution (⊤ : P201.Domain 1)
        (P201Specs.Elliptic.NewtonHessian.gradientKernel 0) := by
  ext φ
  rw [P102.U4.distributionPartial_singleton_apply]
  rw [P102.U4.regular_pairing 1 ℝ ⊤ _
      ((P201.fundamentalLocalIntegrability 1 le_rfl).locallyIntegrableOn _),
    P102.U4.regular_pairing 1 ℝ ⊤ _
      ((P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable le_rfl 0).locallyIntegrableOn _)]
  simp only [Opens.coe_top, setIntegral_univ]
  let q : ℝ → ℝ := φ ∘ oneCoord.symm
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := φ.contDiff.comp oneCoord.symm.contDiff
  have hc : HasCompactSupport q :=
    φ.hasCompactSupport.comp_isClosedEmbedding oneCoord.symm.toHomeomorph.isClosedEmbedding
  have hder (t : ℝ) : P102.U4.testPartialWord ⊤ [0] φ (oneCoord.symm t) = deriv q t := by
    rw [P102.U4.testPartialWord_coe]
    change fderiv ℝ φ (oneCoord.symm t) (P201.coordinate 1 0) = deriv q t
    have hvec : oneCoord.symm 1 = P201.coordinate 1 0 := by
      apply oneCoord.injective
      rw [oneCoord.apply_symm_apply, oneCoord_coordinate]
    rw [← fderiv_apply_one_eq_deriv, fderiv_comp t
      (φ.contDiff.differentiable (by simp) _) oneCoord.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
    change _ = (fderiv ℝ φ (oneCoord.symm t)) (oneCoord.symm 1)
    rw [hvec]
  have hchange (f : P201.Space 1 → ℝ) :=
    oneCoord_symm_measurePreserving.integral_comp
      oneCoord.symm.toHomeomorph.measurableEmbedding f
  rw [← hchange (fun x => P201.fundamentalKernel 1 x * P102.U4.testPartialWord ⊤ [0] φ x),
    ← hchange (fun x => P201Specs.Elliptic.NewtonHessian.gradientKernel 0 x * φ x)]
  have hw : P201Specs.omega 1 = 2 := omega_one
  have heF (t : ℝ) : P201.fundamentalKernel 1 (oneCoord.symm t) = -|t| / 2 := by
    simp only [P201.fundamentalKernel, P201Specs.fundamentalKernel,
      P201Specs.fundamentalProfile, ite_true, oneCoord_norm, oneCoord.apply_symm_apply]
  have heG (t : ℝ) : P201Specs.Elliptic.NewtonHessian.gradientKernel 0 (oneCoord.symm t) =
      -t / (2 * |t|) := by
    rw [P201Specs.Elliptic.NewtonHessian.gradientKernel, hw, oneCoord_norm,
      oneCoord.apply_symm_apply, pow_one]
    rfl
  simp_rw [heF, heG, hder]
  change -(∫ t, -|t| / 2 * deriv q t) = ∫ t, -t / (2 * |t|) * q t
  rw [lineFundamental_pairing hq hc, lineGradient_pairing hq.continuous hc, neg_neg]

/-- A locally integrable kernel derivative transports through the compact
source convolution without assuming continuity of the source. -/
theorem weakGradient : P201Specs.Elliptic.NewtonLp.WeakGradientStatement := by
  intro n hn p hp F hF hsupport i
  have hFloc := hF.locallyIntegrable hp
  have hΦ := P201.fundamentalLocalIntegrability n (by omega)
  have hg := P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable (by omega : 1 ≤ n) i
  have hS := P102.U4.regularDistribution_compactSupport_of_essential F hFloc hsupport
  have heq : P201Specs.regularDistribution (⊤ : P201Specs.Domain n)
      (P201Specs.Elliptic.NewtonHessian.holderPotential F) =
      P102.U4.rightCompactConvolution
        (P201Specs.regularDistribution ⊤ (P201.fundamentalKernel n))
        (P201Specs.regularDistribution ⊤ F) hS := by
    rw [potential_eq_functionConvolution]
    exact (P102.U4.rightCompactConvolution_regular _ _ hΦ hFloc (Or.inr hsupport) hS).symm
  rw [heq]
  change P102.U4.distributionPartial {i}
    (P102.U4.rightCompactConvolution _ _ hS) = _
  rw [P102.U4.rightCompactConvolution_partial_left]
  have hder : P201.distributionDerivative {i}
      (P201.regularDistribution (⊤ : P201.Domain n) (P201.fundamentalKernel n)) =
      P201.regularDistribution (⊤ : P201.Domain n)
        (P201Specs.Elliptic.NewtonHessian.gradientKernel i) := by
    by_cases h2 : 2 ≤ n
    · exact P201.Elliptic.NewtonHessian.fundamental_distribution_gradient h2 i
    · have h1 : n = 1 := by omega
      subst n
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact fundamental_distribution_gradient_one
  change P102.U4.distributionPartial {i} _ = _ at hder
  rw [hder]
  exact P102.U4.rightCompactConvolution_regular _ _ hg hFloc (Or.inr hsupport) hS

/-- In dimension one there is no missing off-diagonal Hessian information. -/
theorem dimensionOneHessian : P201Specs.Elliptic.NewtonLp.DimensionOneHessianStatement := by
  intro p hp F hF hsupport
  have h := (potentialEquation 1 le_rfl p hp F hF hsupport).2.2
  simp only [P201Specs.distributionLaplacian, Fin.sum_univ_one] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Compatibility of composed Riesz actions on the entire L²∩Lᵖ
intersection. The intermediate Riesz transform is proved to be in both
spaces before applying the second agreement hypothesis. -/
lemma rieszComposition_agrees {n : ℕ} (p : P102.U2.CZLpData.Exponent)
    (R : Fin n → P102.U2.CZLpData.StrongOperator n p)
    (hR : ∀ i, P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p (R i))
    (F : P201.Space n → ℂ) (hFp : MemLp F p.val volume) (hF2 : MemLp F 2 volume)
    (i j : Fin n) :
    (R i (R j (hFp.toLp F)) : P201.Space n → ℂ) =ᵐ[volume]
      (P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (hF2.toLp F)) :
        P201.Space n → ℂ) := by
  let g : P201.Space n → ℂ := P102.U3.Riesz.rieszL2 j (hF2.toLp F)
  have hj := hR j F hFp hF2
  have hgp : MemLp g p.val volume :=
    (memLp_congr_ae hj).mp (Lp.memLp (R j (hFp.toLp F)))
  have hg2 : MemLp g 2 volume := Lp.memLp _
  have heqp : hgp.toLp g = R j (hFp.toLp F) := by
    apply Lp.ext
    exact hgp.coeFn_toLp.trans hj.symm
  have heq2 : hg2.toLp g = P102.U3.Riesz.rieszL2 j (hF2.toLp F) :=
    Lp.toLp_coeFn _ _
  have hi := hR i g hgp hg2
  rw [heqp, heq2] at hi
  exact hi


/-- Restrict a whole-space weak derivative identity to any open domain.
The test functions are extended by zero, with exactly the same derivatives. -/
lemma regular_derivative_restrict {n : ℕ} (Ω : P201.Domain n)
    (α : P201.MultiIndex n) (u v : P201.Space n → ℝ)
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (h : P201.distributionDerivative α (P201.regularDistribution ⊤ u) =
      P201.regularDistribution ⊤ v) :
    P201.distributionDerivative α (P201.regularDistribution Ω u) =
      P201.regularDistribution Ω v := by
  have hp (f : P201.Space n → ℝ) (hf : LocallyIntegrable f volume)
      (φ : P201.Test ℝ Ω) : P201.regularDistribution Ω f φ = ∫ x, f x * φ x := by
    rw [P102.U4.regular_pairing n ℝ Ω f (hf.locallyIntegrableOn Ω),
      P102.U4.setIntegral_mul_test Ω]
  ext φ
  let ψ := P102.U4.zeroExtension ℝ (show Ω ≤ ⊤ from le_top) φ
  have hψ : (ψ : P201.Space n → ℝ) = φ := by
    ext x
    exact (P102.U4.zeroExtensionProperties n ℝ Ω ⊤ le_top φ).1 x
  have hd : (P102.U4.testPartialWord ⊤ (α.sort (· ≤ ·)) ψ : P201.Space n → ℝ) =
      P102.U4.testPartialWord Ω (α.sort (· ≤ ·)) φ := by
    simp only [P102.U4.testPartialWord_coe, hψ]
  have hh := congrArg (fun T : P201.Distribution ℝ (⊤ : P201.Domain n) => T ψ) h
  simp only [P201.distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.distributionPartial, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul] at hh ⊢
  rw [hp u hu, hp v hv]
  rw [P102.U4.regular_pairing n ℝ ⊤ u (hu.locallyIntegrableOn _),
    P102.U4.regular_pairing n ℝ ⊤ v (hv.locallyIntegrableOn _)] at hh
  simpa only [Opens.coe_top, setIntegral_univ, hψ, hd] using hh

/-- Construct the shared Sobolev object from actual globally locally integrable
weak derivative representatives; its norm is the full sum of the local Lᵖ norms. -/
lemma exists_sobolev_of_global_derivatives {n m : ℕ} (Ω : P201.Domain n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (H : P102.U4.SobolevIndex n m → P201.Space n → ℝ)
    (hH : ∀ α, LocallyIntegrable (H α) volume)
    (hmem : ∀ α, MemLp (H α) p (P201.domainMeasure Ω))
    (hder : ∀ α, P201.distributionDerivative α.val
      (P201.regularDistribution ⊤ (H (P102.U4.zeroSobolevIndex n m))) =
        P201.regularDistribution ⊤ (H α)) :
    ∃ w : P201.W ℝ Ω m p,
      (P102.U4.sobolevUnderlying w : P201.Space n → ℝ) =ᵐ[P201.domainMeasure Ω]
        H (P102.U4.zeroSobolevIndex n m) ∧
      ‖w‖ = ∑ α, (eLpNorm (H α) p (P201.domainMeasure Ω)).toReal := by
  let V (α : P102.U4.SobolevIndex n m) : P201.Lp ℝ Ω p := (hmem α).toLp (H α)
  have hreg (α : P102.U4.SobolevIndex n m) :
      P201.regularDistribution Ω (V α) = P201.regularDistribution Ω (H α) :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω p (V α))
      ((hH α).locallyIntegrableOn Ω)).mpr (hmem α).coeFn_toLp
  let W : P201.W ℝ Ω m p := ⟨WithLp.toLp 1 V, by
    apply (P102.U4.mem_sobolevSubmodule_iff Ω m p _).mpr
    intro α φ
    have hd := regular_derivative_restrict Ω α.val _ _
      (hH (P102.U4.zeroSobolevIndex n m)) (hH α) (hder α)
    have he : P102.U4.distributionPartial α.val
        (P102.U4.regularDistribution Ω (V (P102.U4.zeroSobolevIndex n m))) =
        P102.U4.regularDistribution Ω (V α) := by
      exact (congrArg (P201.distributionDerivative α.val)
        (hreg (P102.U4.zeroSobolevIndex n m))).trans (hd.trans (hreg α).symm)
    exact (P102.U4.distributionPartial_eq_regularLp_iff Ω p _ _ _).mp he φ⟩
  refine ⟨W, (hmem (P102.U4.zeroSobolevIndex n m)).coeFn_toLp, ?_⟩
  rw [P102.U4.sobolev_norm Ω m p]
  apply Finset.sum_congr rfl
  intro α _
  exact Lp.norm_toLp (H α) (hmem α)

/-- The actual classical gradient of a smooth-source Newton potential is the
ordinary convolution with the locally integrable gradient kernel, also on the line. -/
lemma smoothPotential_firstPartial {n : ℕ} (hn : 1 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i : Fin n) :
    P201.multiPartial (P201.newtonPotential F) {i} =
      P102.U4.functionConvolution (P201Specs.Elliptic.NewtonHessian.gradientKernel i) F := by
  have hder : P201.distributionDerivative {i}
      (P201.regularDistribution (⊤ : P201.Domain n) (P201.fundamentalKernel n)) =
      P201.regularDistribution ⊤ (P201Specs.Elliptic.NewtonHessian.gradientKernel i) := by
    by_cases h2 : 2 ≤ n
    · exact P201.Elliptic.NewtonHessian.fundamental_distribution_gradient h2 i
    · have h1 : n = 1 := by omega
      subst n
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact fundamental_distribution_gradient_one
  rw [P201.newtonPotential_eq_localConvolution hn F]
  change P102.U4.multiPartial (P102.U4.localConvolution _ F) {i} = _
  rw [P102.U4.localConvolution_distributionPartial P102.U4.distributionConvolution]
  change P102.U4.distributionPartial {i} _ = _ at hder
  rw [hder]
  rw [P102.U4.localConvolution_regular_whole
    (P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable hn i) F]
  funext x
  change P102.U4.functionConvolution F
    (P201Specs.Elliptic.NewtonHessian.gradientKernel i) x = _
  exact P102.U4.functionConvolution_comm _ _ x

/-- The potential has a first-order Sobolev representative without any initial
weak derivative of the datum. The constant is uniform over the prescribed support. -/
theorem firstOrderPotentialEstimate :
    P201Specs.Elliptic.NewtonLp.FirstOrderPotentialEstimateStatement := by
  intro n hn p hp K Ω hΩ
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let B : Compacts (P201.Space n) := ⟨closure (Ω : Set (P201.Space n)), hΩ.isCompact_closure⟩
  obtain ⟨C, hC, hb⟩ := lowerOrderEstimate n hn p hp K B
  let d : ℝ := Fintype.card (P102.U4.SobolevIndex n 1)
  refine ⟨d * C, mul_nonneg (by positivity) hC, ?_⟩
  intro F hF hK
  have hsupport : P102.U4.HasCompactEssentialSupport F := ⟨K, hK⟩
  have hloc := (potentialEquation n hn p hp F hF hsupport).2.1
  let u := P201Specs.Elliptic.NewtonHessian.holderPotential F
  let g (i : Fin n) := P102.U4.functionConvolution
    (P201Specs.Elliptic.NewtonHessian.gradientKernel i) F
  have hg (i : Fin n) : LocallyIntegrable (g i) volume :=
    (P102.U4.functionConvolution_locallyIntegrable _ _
      (P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable hn i)
      (hF.locallyIntegrable hp) (Or.inr hsupport)).2
  obtain ⟨huB, hgB, hbound⟩ := hb F hF hK
  have hμ : P201.domainMeasure Ω ≤ volume.restrict (B : Set (P201.Space n)) :=
    Measure.restrict_mono subset_closure le_rfl
  let N := (eLpNorm F p volume).toReal
  have hnorm (f : P201.Space n → ℝ) (hf : MemLp f p (volume.restrict B)) :
      (eLpNorm f p (P201.domainMeasure Ω)).toReal ≤
        (eLpNorm f p (volume.restrict B)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  have hsum0 : 0 ≤ ∑ i : Fin n, (eLpNorm (g i) p (volume.restrict B)).toReal :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have huBound : (eLpNorm u p (P201.domainMeasure Ω)).toReal ≤ C * N :=
    (hnorm u huB).trans ((le_add_of_nonneg_right hsum0).trans hbound)
  have hgBound (i : Fin n) : (eLpNorm (g i) p (P201.domainMeasure Ω)).toReal ≤ C * N := by
    have hsum : (eLpNorm (g i) p (volume.restrict B)).toReal ≤
        ∑ j : Fin n, (eLpNorm (g j) p (volume.restrict B)).toReal :=
      Finset.single_le_sum (f := fun j : Fin n =>
        (eLpNorm (g j) p (volume.restrict B)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
    exact (hnorm (g i) (hgB i)).trans (hsum.trans
      ((le_add_of_nonneg_left ENNReal.toReal_nonneg).trans hbound))
  let H (α : P102.U4.SobolevIndex n 1) : P201.Space n → ℝ :=
    if h : α.val.card = 1 then g (Multiset.card_eq_one.mp h).choose else u
  have hHloc (α : P102.U4.SobolevIndex n 1) : LocallyIntegrable (H α) volume := by
    dsimp only [H]
    split_ifs
    · exact hg _
    · exact hloc
  have hHmem (α : P102.U4.SobolevIndex n 1) : MemLp (H α) p (P201.domainMeasure Ω) := by
    dsimp only [H]
    split_ifs
    · exact (hgB _).mono_measure hμ
    · exact huB.mono_measure hμ
  have hzero : H (P102.U4.zeroSobolevIndex n 1) = u := by simp [H, P102.U4.zeroSobolevIndex]
  have hHder (α : P102.U4.SobolevIndex n 1) :
      P201.distributionDerivative α.val
        (P201.regularDistribution ⊤ (H (P102.U4.zeroSobolevIndex n 1))) =
          P201.regularDistribution ⊤ (H α) := by
    rw [hzero]
    by_cases h1 : α.val.card = 1
    · simp only [H, dif_pos h1]
      conv_lhs => rw [(Multiset.card_eq_one.mp h1).choose_spec]
      exact weakGradient n hn p hp F hF hsupport _
    · have h0 : α.val = 0 := Multiset.card_eq_zero.mp (by have := α.property; omega)
      simp only [H, dif_neg h1]
      rw [h0]
      exact P102.U4.derivative_zero n ℝ ⊤ _
  obtain ⟨w, hw, hwn⟩ := exists_sobolev_of_global_derivatives Ω p H hHloc hHmem hHder
  refine ⟨w, by simpa only [hzero] using hw, ?_⟩
  rw [hwn]
  have hentry (α : P102.U4.SobolevIndex n 1) :
      (eLpNorm (H α) p (P201.domainMeasure Ω)).toReal ≤ C * N := by
    dsimp only [H]
    split_ifs
    · exact hgBound _
    · exact huBound
  calc
    _ ≤ ∑ α : P102.U4.SobolevIndex n 1, C * N :=
      Finset.sum_le_sum (fun α _ => hentry α)
    _ = _ := by simp [d, N, Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The complete compact-source local W²ᵖ result in dimension one,
including the full Sobolev norm and a constant selected before the datum. -/
theorem dimensionOnePotentialEstimate :
    P201Specs.Elliptic.NewtonLp.DimensionOnePotentialEstimateStatement := by
  intro p K Ω hΩ
  let B : Compacts (P201.Space 1) := ⟨closure (Ω : Set (P201.Space 1)), hΩ.isCompact_closure⟩
  obtain ⟨C, hC, hb⟩ := lowerOrderEstimate 1 le_rfl p.val p.one_lt.le K B
  let d : ℝ := Fintype.card (P102.U4.SobolevIndex 1 2)
  refine ⟨d * (C + 1), mul_nonneg (by positivity) (by positivity), ?_⟩
  intro F hF hK
  have hsupport : P102.U4.HasCompactEssentialSupport F := ⟨K, hK⟩
  obtain ⟨hex, hloc, heq⟩ := potentialEquation 1 le_rfl p.val p.one_lt.le F hF hsupport
  refine ⟨hex, hloc, heq, ?_⟩
  let u := P201Specs.Elliptic.NewtonHessian.holderPotential F
  let g := P102.U4.functionConvolution
    (P201Specs.Elliptic.NewtonHessian.gradientKernel (0 : Fin 1)) F
  have hg : LocallyIntegrable g volume :=
    (P102.U4.functionConvolution_locallyIntegrable _ _
      (P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable le_rfl 0)
      (hF.locallyIntegrable p.one_lt.le) (Or.inr hsupport)).2
  obtain ⟨huB, hgB, hbound⟩ := hb F hF hK
  simp only [Fin.sum_univ_one] at hbound
  have hμ : P201.domainMeasure Ω ≤ volume.restrict (B : Set (P201.Space 1)) :=
    Measure.restrict_mono subset_closure le_rfl
  have huΩ : MemLp u p.val (P201.domainMeasure Ω) := huB.mono_measure hμ
  have hgΩ : MemLp g p.val (P201.domainMeasure Ω) := (hgB 0).mono_measure hμ
  have hFΩ : MemLp F p.val (P201.domainMeasure Ω) := hF.mono_measure Measure.restrict_le_self
  let N := (eLpNorm F p.val volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hnorm (f : P201.Space 1 → ℝ) (hf : MemLp f p.val (volume.restrict B)) :
      (eLpNorm f p.val (P201.domainMeasure Ω)).toReal ≤
        (eLpNorm f p.val (volume.restrict B)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  have hFu : (eLpNorm F p.val (P201.domainMeasure Ω)).toReal ≤ N :=
    ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have huBound : (eLpNorm u p.val (P201.domainMeasure Ω)).toReal ≤ (C + 1) * N := by
    have h := hnorm u huB
    have hg0 : 0 ≤ (eLpNorm g p.val (volume.restrict B)).toReal := ENNReal.toReal_nonneg
    change _ ≤ C * N at hbound
    nlinarith
  have hgBound : (eLpNorm g p.val (P201.domainMeasure Ω)).toReal ≤ (C + 1) * N := by
    have h := hnorm g (hgB 0)
    have hu0 : 0 ≤ (eLpNorm u p.val (volume.restrict B)).toReal := ENNReal.toReal_nonneg
    change _ ≤ C * N at hbound
    nlinarith
  let H (α : P102.U4.SobolevIndex 1 2) : P201.Space 1 → ℝ :=
    if α.val.card = 0 then u else if α.val.card = 1 then g else -F
  have hHloc (α : P102.U4.SobolevIndex 1 2) : LocallyIntegrable (H α) volume := by
    dsimp only [H]
    split_ifs
    · exact hloc
    · exact hg
    · exact (hF.locallyIntegrable p.one_lt.le).neg
  have hHmem (α : P102.U4.SobolevIndex 1 2) : MemLp (H α) p.val (P201.domainMeasure Ω) := by
    dsimp only [H]
    split_ifs
    · exact huΩ
    · exact hgΩ
    · exact hFΩ.neg
  have hzero : H (P102.U4.zeroSobolevIndex 1 2) = u := by simp [H, P102.U4.zeroSobolevIndex]
  have hneg : P201.regularDistribution (⊤ : P201.Domain 1) (-F) =
      -(P201.regularDistribution ⊤ F) := by
    ext φ
    rw [P102.U4.regular_pairing 1 ℝ ⊤ _
      ((hF.locallyIntegrable p.one_lt.le).neg.locallyIntegrableOn _)]
    change _ = -(P201.regularDistribution ⊤ F φ)
    rw [P102.U4.regular_pairing 1 ℝ ⊤ _
      ((hF.locallyIntegrable p.one_lt.le).locallyIntegrableOn _)]
    simp only [Pi.neg_apply, neg_mul, integral_neg]
  have hHder (α : P102.U4.SobolevIndex 1 2) :
      P201.distributionDerivative α.val
        (P201.regularDistribution ⊤ (H (P102.U4.zeroSobolevIndex 1 2))) =
          P201.regularDistribution ⊤ (H α) := by
    rw [hzero]
    by_cases h0 : α.val.card = 0
    · have hα : α.val = 0 := Multiset.card_eq_zero.mp h0
      simp only [H, h0, ite_true, hα]
      exact P102.U4.derivative_zero 1 ℝ ⊤ _
    · by_cases h1 : α.val.card = 1
      · have hα : α.val = {0} := by
          have h := Multiset.eq_replicate.mpr
            ⟨h1, fun b _ => (Subsingleton.elim b (0 : Fin 1))⟩
          simpa using h
        simp only [H, h0, ite_false, h1, ite_true]
        rw [hα]
        exact weakGradient 1 le_rfl p.val p.one_lt.le F hF hsupport 0
      · have h2 : α.val.card = 2 := by have := α.property; omega
        have hα : α.val = {0,0} := by
          have h := Multiset.eq_replicate.mpr
            ⟨h2, fun b _ => (Subsingleton.elim b (0 : Fin 1))⟩
          simpa [Multiset.replicate_succ] using h
        simp only [H, h0, h1, ite_false]
        rw [hα, hneg]
        exact dimensionOneHessian p.val p.one_lt.le F hF hsupport
  obtain ⟨w, hw, hwn⟩ := exists_sobolev_of_global_derivatives Ω p.val H hHloc hHmem hHder
  refine ⟨w, by simpa only [hzero] using hw, ?_⟩
  rw [hwn]
  have hentry (α : P102.U4.SobolevIndex 1 2) :
      (eLpNorm (H α) p.val (P201.domainMeasure Ω)).toReal ≤ (C+1) * N := by
    dsimp only [H]
    split_ifs
    · exact huBound
    · exact hgBound
    · rw [eLpNorm_neg]
      exact hFu.trans (by nlinarith)
  calc
    _ ≤ ∑ α : P102.U4.SobolevIndex 1 2, (C+1) * N :=
      Finset.sum_le_sum (fun α _ => hentry α)
    _ = _ := by simp [d, N, Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The square of the pinned one-dimensional Riesz operator is minus the
identity. The frequency zero is removed only as a Lebesgue null set. -/
lemma dimensionOneRieszSquare (f : MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space 1))) :
    P102.U3.Riesz.rieszL2 0 (P102.U3.Riesz.rieszL2 0 f) = -f := by
  apply (P102.Specs.U3.Riesz.F2 1).injective
  apply MeasureTheory.Lp.ext
  have hi := P102.U3.RieszTransforms.canonical_multiplier (by rfl : 1 ≤ 1) 0 0
    (P102.U3.Riesz.rieszL2 0 f)
  have hj := P102.U3.RieszTransforms.canonical_multiplier (by rfl : 1 ≤ 1) 0 0 f
  have hz : ∀ᵐ ξ : P201.Space 1 ∂volume, ξ ≠ 0 := volume.ae_ne 0
  rw [map_neg]
  filter_upwards [hi, hj, hz, Lp.coeFn_neg (P102.Specs.U3.Riesz.F2 1 f)]
    with ξ hiξ hjξ hξ hneg
  rw [hiξ, hjξ, hneg]
  simp only [Pi.neg_apply]
  have hn : (‖ξ‖ : ℂ)^2 = (ξ 0 : ℂ)^2 := by
    exact_mod_cast (by simpa only [Fin.sum_univ_one] using EuclideanSpace.real_norm_sq_eq ξ)
  have hnorm : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  simp only [P102.Specs.U3.Riesz.symbolAtOrigin, ite_eq_right hξ,
    P102.Specs.U3.Riesz.symbolValue, Complex.ofReal_div]
  field_simp
  calc
    _ = -((ξ 0 : ℂ)^2) * (P102.Specs.U3.Riesz.F2 1 f) ξ := by
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by rw [← hn]; ring

/-- In dimension one the Poisson equation is the whole Hessian identity.
This proves the smooth-source Riesz identification without a frequency-origin
ambiguity or any assumed regularity of a Newtonian potential at infinity. -/
theorem dimensionOneSmoothHessian :
    P201Specs.Elliptic.NewtonLp.DimensionOneSmoothHessianStatement := by
  intro p R hR F i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  let Fc : P201.Space 1 → ℂ := fun x => (F x : ℂ)
  have hp : MemLp Fc p.val volume :=
    Complex.ofRealCLM.comp_memLp' (F.continuous.memLp_of_hasCompactSupport F.hasCompactSupport)
  have h2 : MemLp Fc 2 volume :=
    Complex.ofRealCLM.comp_memLp' (F.continuous.memLp_of_hasCompactSupport F.hasCompactSupport)
  have hr := rieszComposition_agrees p R hR Fc hp h2 0 0
  rw [dimensionOneRieszSquare] at hr
  have hrF : (R 0 (R 0 (hp.toLp Fc)) : P201.Space 1 → ℂ) =ᵐ[volume]
      fun x => -(F x : ℂ) :=
    hr.trans ((Lp.coeFn_neg _).trans (h2.coeFn_toLp.neg))
  have hder : P201Specs.multiPartial (P201.newtonPotential F)
      ({0,0} : P201.MultiIndex 1) = -F := by
    funext x
    have h := P201.newtonEquation 1 le_rfl F x
    simp only [P201Specs.laplacian, Fin.sum_univ_one] at h
    exact neg_eq_iff_eq_neg.mp h
  refine ⟨hp, ?_, ?_⟩
  · simpa only [hder, Pi.neg_apply, Complex.ofReal_neg] using hrF
  · have heq : (fun x => (R 0 (R 0 (hp.toLp Fc)) x).re) =ᵐ[volume] -F := by
      filter_upwards [hrF] with x hx
      simpa only [Complex.neg_re, Complex.ofReal_re, Pi.neg_apply] using congrArg Complex.re hx
    have hmem : MemLp (fun x => (R 0 (R 0 (hp.toLp Fc)) x).re) p.val volume :=
      Complex.reCLM.comp_memLp' (Lp.memLp _)
    have hreg := (P102.U4.regular_injectivity 1 ℝ ⊤ _ _
      ((F.continuous.neg).locallyIntegrable.locallyIntegrableOn _)
      ((hmem.locallyIntegrable p.one_lt.le).locallyIntegrableOn _)).mpr
        (by simpa using heq.symm)
    change P102.U4.distributionPartial {0,0}
      (P102.U4.regularDistribution ⊤ (P201.newtonPotential F)) = _
    rw [P102.U4.derivative_classicalCompatibility 1 ℝ ⊤ _ _
      ((P201.newtonSmooth 1 le_rfl F).of_le (by simp)).contDiffOn]
    change P102.U4.regularDistribution ⊤
      (P201Specs.multiPartial (P201.newtonPotential F) {0,0}) = _
    rw [hder]
    exact hreg

/-- Mollification enlarges the prescribed compact support by at most the unit
ball, uniformly along the entire approximating sequence. -/
theorem commonSupportApproximation :
    P201Specs.Elliptic.NewtonLp.CommonSupportApproximationStatement := by
  intro n p hp hptop K
  let L : Compacts (P201.Space n) :=
    ⟨(K : Set (P201.Space n)) + Metric.closedBall 0 1,
      K.isCompact.add (isCompact_closedBall 0 1)⟩
  refine ⟨L, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx, 0, by simp, by simp⟩
  intro F hF hK
  have hFloc := hF.locallyIntegrable hp
  let ρ := P102.U4.sobolevMollifierKernel n ℝ
  let ε : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  have hεpos (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hεle (m : ℕ) : ε m ≤ 1 := by
    dsimp [ε]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg m))
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hεpos⟩
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  let f (m : ℕ) : P201.Test ℝ (⊤ : P201.Domain n) :=
    ⟨P102.U4.localConvolution (P201.regularDistribution ⊤ F) (ρ (ε m)),
      P102.U4.localConvolution_contDiff _ _,
      P102.U4.localConvolution_hasCompactSupport hFloc ⟨K, hK⟩ _, subset_univ _⟩
  have hf (m : ℕ) : (f m : P201.Space n → ℝ) =
      fun x => ∫ y, ρ (ε m) (x-y) * F y :=
    P102.U4.localConvolution_regular_whole hFloc _
  refine ⟨f, ?_, ?_⟩
  · intro m
    apply closure_minimal _ L.isCompact.isClosed
    intro x hx
    by_contra hxL
    apply hx
    rw [hf]
    apply integral_eq_zero_of_ae
    filter_upwards [hK] with y hy
    by_cases hyK : y ∈ K
    · have hz : ρ (ε m) (x-y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hz
        have hball := P102.U4.sobolevMollifierKernel_support n ℝ (ε m) (hεpos m) hz
        apply hxL
        exact ⟨y, hyK, x-y,
          Metric.closedBall_subset_closedBall (hεle m) hball, by abel⟩
      simp [hz]
    · simp [hy hyK]
  · have hrec := (P102.U2.ApproximateIdentities.lp_recovery volume
        (fun t => (ρ t : P201.Space n → ℝ))
        (P102.U4.sobolevMollifierKernel_conditions n ℝ).1 p hp hptop F hF).2
    have he := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hrec.comp hεlim)
    simp_rw [hf]
    exact he

/-- Linearity holds almost everywhere on compact-source Lᵖ inputs, with
absolute existence supplied before distributing the ordinary integral. -/
lemma functionConvolution_sub_ae {n : ℕ} (k : P201.Space n → ℝ)
    (hk : LocallyIntegrable k volume) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F G : P201.Space n → ℝ) (hF : MemLp F p volume) (hG : MemLp G p volume)
    (hFc : P102.U4.HasCompactEssentialSupport F)
    (hGc : P102.U4.HasCompactEssentialSupport G) :
    P102.U4.functionConvolution k (fun x => F x - G x) =ᵐ[volume]
      fun x => P102.U4.functionConvolution k F x - P102.U4.functionConvolution k G x := by
  have hFi := (P102.U4.functionConvolution_locallyIntegrable k F hk
    (hF.locallyIntegrable hp) (Or.inr hFc)).1
  have hGi := (P102.U4.functionConvolution_locallyIntegrable k G hk
    (hG.locallyIntegrable hp) (Or.inr hGc)).1
  filter_upwards [hFi, hGi] with x hxF hxG
  change (∫ y, k (x-y) * (F y - G y)) = _
  simp_rw [mul_sub]
  exact integral_sub hxF hxG

/-- The local Young constant controls differences and hence proves strong
local convergence of the actual potentials and first-kernel integrals. -/
theorem localConvolutionConvergence :
    P201Specs.Elliptic.NewtonLp.LocalConvolutionConvergenceStatement := by
  intro n p hp A B k hk f F hf hF hfa hFa hlim
  obtain ⟨C, hC, hbound⟩ := localKernelEstimate n k hk p hp A B
  refine ⟨fun m => (hbound (f m) (hf m) (hfa m)).1,
    (hbound F hF hFa).1, ?_⟩
  have hupper : Tendsto (fun m => C *
      (eLpNorm (fun x => f m x - F x) p volume).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul C
  apply squeeze_zero (fun m => ENNReal.toReal_nonneg) (fun m => ?_) hupper
  have hs : ∀ᵐ x ∂volume, x ∉ A → f m x - F x = 0 := by
    filter_upwards [hfa m, hFa] with x hx hxF ha
    rw [hx ha, hxF ha, sub_self]
  have he := functionConvolution_sub_ae k hk p hp (f m) F (hf m) hF
    ⟨A, hfa m⟩ ⟨A, hFa⟩
  have hb := (hbound (fun x => f m x - F x) ((hf m).sub hF) hs).2
  rw [eLpNorm_congr_ae (ae_restrict_of_ae he)] at hb
  exact hb


lemma kernelConvolution_decay {n : ℕ} (k F : P201.Space n → ℝ)
    (hk : Measurable k) (hF : Integrable F volume)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 < R)
    (hsize : ∀ z : P201.Space n, z ≠ 0 → ‖k z‖ ≤ M / ‖z‖ ^ n)
    (hsupp : ∀ y, R < ‖y‖ → F y = 0)
    {x : P201.Space n} (hx : 2 * R < ‖x‖) :
    ‖P102.U4.functionConvolution k F x‖ ≤
      (M * 2 ^ n * ∫ y, ‖F y‖) / ‖x‖ ^ n := by
  have hxp : 0 < ‖x‖ := by linarith
  let D := M * 2 ^ n / ‖x‖ ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (y : P201.Space n) : ‖k (x-y) * F y‖ ≤ D * ‖F y‖ := by
    by_cases hy : ‖y‖ ≤ R
    · have hxy : ‖x‖ / 2 ≤ ‖x-y‖ := by
        have h := norm_sub_le x y
        have h' := norm_le_norm_sub_add x y
        linarith
      have hz : x-y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖x-y‖))
      have hden : (‖x‖ / 2) ^ n ≤ ‖x-y‖ ^ n := pow_le_pow_left₀ (by positivity) hxy n
      have hpow : 0 < (‖x‖ / 2) ^ n := pow_pos (by positivity) n
      have hb : ‖k (x-y)‖ ≤ D := by
        calc
          _ ≤ M / ‖x-y‖ ^ n := hsize _ hz
          _ ≤ M / (‖x‖ / 2) ^ n := div_le_div_of_nonneg_left hM hpow hden
          _ = D := by dsimp [D]; rw [div_pow]; field_simp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    · simp [hsupp y (lt_of_not_ge hy)]
  have hi : Integrable (fun y => k (x-y) * F y) volume :=
    (hF.norm.const_mul D).mono'
      ((hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        hF.aestronglyMeasurable) (Eventually.of_forall hbound)
  change ‖∫ y, k (x-y) * F y‖ ≤ _
  calc
    _ ≤ ∫ y, ‖k (x-y) * F y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, D * ‖F y‖ := integral_mono_ae hi.norm (hF.norm.const_mul D)
      (Eventually.of_forall hbound)
    _ = _ := by rw [integral_const_mul]; dsimp [D]; ring

lemma continuous_decay_memLp_two {n : ℕ} (hn : 1 ≤ n)
    (u : P201.Space n → ℝ) (hu : Continuous u) {C R : ℝ}
    (_hC : 0 ≤ C) (hR : 0 < R)
    (hdecay : ∀ x, R < ‖x‖ → ‖u x‖ ≤ C / ‖x‖ ^ n) :
    MemLp u 2 volume := by
  letI : Nontrivial (P201.Space n) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simpa using (show 0 < n by omega)
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
  have hloc : IntegrableOn (fun x => ‖u x‖ ^ 2) (Metric.closedBall 0 R) volume :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have htail : IntegrableOn (fun x : P201.Space n => ‖x‖ ^ (-(2 * n : ℝ)))
      {x | R < ‖x‖} volume :=
    P201.Elliptic.HolderCancellation.radial_exterior_integrable
      (by simp only [P201.Space, P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin];
          have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          linarith) hR
  have hext : IntegrableOn (fun x => ‖u x‖ ^ 2) {x | R < ‖x‖} volume := by
    apply (htail.const_mul (C ^ 2)).mono' (hu.norm.pow 2).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (by measurability : MeasurableSet {x : P201.Space n | R < ‖x‖})]
      with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hxp : 0 < ‖x‖ := lt_trans hR hx
    calc
      _ ≤ (C / ‖x‖ ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdecay x hx) 2
      _ = C ^ 2 * ‖x‖ ^ (-(2 * n : ℝ)) := by
        rw [div_pow, Real.rpow_neg (norm_nonneg x),
          show (2 * n : ℝ) = ((n * 2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul]
        ring
  have hcov : Metric.closedBall (0 : P201.Space n) R ∪ {x | R < ‖x‖} = univ := by
    ext x
    simp only [mem_union, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt ‖x‖ R
  rw [← integrableOn_univ, ← hcov]
  exact hloc.union hext


open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

/-- At a zero of the source, the compensated Hessian integral is the ordinary
kernel integral; the contact term is zero there. In particular this applies
outside the prescribed source support. -/
lemma smoothPotential_hessian_eq_integral_of_zero {n : ℕ} (hn : 2 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i j : Fin n)
    (x : P201.Space n) (hx : F x = 0) :
    Integrable (fun y => hessianKernel i j (x-y) * F y) volume ∧
    P201.multiPartial (P201.newtonPotential F) {i,j} x =
      ∫ y, hessianKernel i j (x-y) * F y := by
  have hh := P201.Elliptic.NewtonHessian.test_isHolder_half F
  have hO := P201.Elliptic.NewtonHessian.hessianOperatorHolder hn (1/2)
    (by norm_num) (by norm_num) F F.hasCompactSupport hh i j
  have hH := P201.Elliptic.NewtonHessian.potentialHessian hn (1/2)
    (by norm_num) (by norm_num) F F.hasCompactSupport hh
  have hc : compensatedIntegrand (hessianKernel i j) F x =
      fun z => hessianKernel i j z * F (x-z) := by
    funext z
    simp only [compensatedIntegrand, hx, indicator_zero, sub_zero]
  have hi : Integrable (fun z => hessianKernel i j z * F (x-z)) volume := by
    simpa only [hc] using (hO.2 x).2.1
  have hie : Integrable (fun y => hessianKernel i j (x-y) * F y) volume := by
    simpa only [sub_sub_cancel] using hi.comp_sub_left x
  refine ⟨hie, ?_⟩
  have he := congrFun ((hH.2.2 i j).2.1) x
  change P201.multiPartial (P201.newtonPotential F) {i,j} x = _ at he
  rw [hx, mul_zero, zero_div, sub_zero] at he
  rw [he, (hO.2 x).2.2.2, hc]
  symm
  convert integral_sub_left_eq_self
    (fun z => hessianKernel i j z * F (x-z)) volume x using 1
  simp only [sub_sub_cancel]

lemma smoothPotential_hessian_eq_integral_outside {n : ℕ} (hn : 2 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i j : Fin n)
    (R : ℝ) (hF : tsupport F ⊆ Metric.closedBall 0 R)
    (x : P201.Space n) (hx : R < ‖x‖) :
    Integrable (fun y => hessianKernel i j (x-y) * F y) volume ∧
    P201.multiPartial (P201.newtonPotential F) {i,j} x =
      ∫ y, hessianKernel i j (x-y) * F y := by
  apply smoothPotential_hessian_eq_integral_of_zero hn F i j x
  apply image_eq_zero_of_notMem_tsupport
  intro hxF
  have hball := hF hxF
  simp only [Metric.mem_closedBall, dist_zero_right] at hball
  exact (not_le_of_gt hx) hball



lemma smoothPotential_hessian_continuous {n : ℕ} (hn : 1 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i j : Fin n) :
    Continuous (P201.multiPartial (P201.newtonPotential F) {i,j}) := by
  rw [P201.newtonPotential_eq_localConvolution hn F]
  change Continuous (P102.U4.multiPartial (P102.U4.localConvolution _ F) {i,j})
  rw [P102.U4.localConvolution_distributionPartial P102.U4.distributionConvolution]
  exact (P102.U4.localConvolution_contDiff _ _).continuous

/-- Smooth compact data have a globally square-integrable Newton Hessian.
The tail is controlled by the actual homogeneous kernel, so no polynomial
ambiguity at frequency zero can be absorbed into this representative. -/
lemma smoothPotential_hessian_memLp_two {n : ℕ} (hn : 2 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i j : Fin n) :
    MemLp (P201.multiPartial (P201.newtonPotential F) {i,j}) 2 volume := by
  obtain ⟨R, hRp, hR⟩ := F.hasCompactSupport.isBounded.exists_pos_norm_lt
  have hsupport : tsupport F ⊆ Metric.closedBall (0 : P201.Space n) R := by
    intro x hx
    exact mem_closedBall_zero_iff.mpr (hR x hx).le
  let k := P201Specs.Elliptic.NewtonHessian.hessianKernel i j
  have hK := P201.Elliptic.NewtonHessian.kernelHypotheses hn i j
  obtain ⟨M, hM, hsize⟩ := P201.Elliptic.HolderCancellation.homogeneous_size hK
  apply continuous_decay_memLp_two (R := 2 * R) (by omega : 1 ≤ n) _
    (smoothPotential_hessian_continuous (by omega) F i j)
    (show 0 ≤ M * 2 ^ n * ∫ y, ‖F y‖ by positivity) (mul_pos (by norm_num : (0 : ℝ) < 2) hRp)
  intro x hx
  have heq := (smoothPotential_hessian_eq_integral_outside hn F i j R hsupport x
    (by linarith)).2
  rw [heq]
  exact kernelConvolution_decay k F
    (P201.Elliptic.HolderCancellation.kernel_measurable hK)
    (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)
    hM hRp hsize
    (fun y hy => image_eq_zero_of_notMem_tsupport (fun hyF =>
      (not_le_of_gt hy) (mem_closedBall_zero_iff.mp (hsupport hyF)))) hx



lemma distributionDerivative_neg {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : P201.Domain n} (α : P201.MultiIndex n) (T : P201.Distribution 𝕜 Ω) :
    P201.distributionDerivative α (-T) = -P201.distributionDerivative α T := by
  ext φ
  simp [P201.distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.distributionPartial, smul_eq_mul]

lemma distributionDerivative_laplacian_commute {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : P201.Domain n} (α : P201.MultiIndex n) (T : P201.Distribution 𝕜 Ω) :
    P201.distributionDerivative α (P201.distributionLaplacian T) =
      P201.distributionLaplacian (P201.distributionDerivative α T) := by
  change P102.U4.distributionPartial α (∑ k : Fin n, P102.U4.distributionPartial {k,k} T) =
    ∑ k : Fin n, P102.U4.distributionPartial {k,k} (P102.U4.distributionPartial α T)
  have hsum : P102.U4.distributionPartial α
      (∑ k : Fin n, P102.U4.distributionPartial {k,k} T) =
      ∑ k : Fin n, P102.U4.distributionPartial α (P102.U4.distributionPartial {k,k} T) := by
    ext φ
    simp [P102.U4.distributionPartial, smul_eq_mul, Finset.mul_sum]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← P102.U4.derivative_add n 𝕜 Ω, ← P102.U4.derivative_add n 𝕜 Ω, add_comm]

lemma smooth_regular_laplacian {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : P201.Space n → 𝕜) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    P201.distributionLaplacian (P201.regularDistribution (⊤ : P201.Domain n) u) =
      P201.regularDistribution ⊤ (P201.laplacian u) := by
  have hpartial (k : Fin n) :
      P201.distributionDerivative {k,k} (P201.regularDistribution ⊤ u) =
      P201.regularDistribution ⊤ (P201.multiPartial u {k,k}) :=
    P102.U4.derivative_classicalCompatibility n 𝕜 ⊤ _ u
      (hu.of_le (by simp)).contDiffOn
  have hpartloc (k : Fin n) : LocallyIntegrable (P201.multiPartial u {k,k}) volume :=
    (P102.U4.partialWord_contDiff hu _).continuous.locallyIntegrable
  have hlaploc : LocallyIntegrable (P201.laplacian u) volume := by
    simpa only [P201.laplacian, P201Specs.laplacian, Finset.sum_apply] using
      (locallyIntegrable_finsetSum Finset.univ (fun k _ => hpartloc k))
  change (∑ k : Fin n, P201.distributionDerivative {k,k}
    (P201.regularDistribution ⊤ u)) = _
  simp_rw [hpartial]
  ext φ
  simp only [sum_apply]
  rw [P102.U4.regular_pairing n 𝕜 ⊤ _ (hlaploc.locallyIntegrableOn _)]
  simp_rw [P102.U4.regular_pairing n 𝕜 ⊤ _ ((hpartloc _).locallyIntegrableOn _)]
  simp only [Opens.coe_top, setIntegral_univ, P201.laplacian, P201Specs.laplacian, Finset.sum_mul]
  symm
  apply integral_finsetSum
  intro k _
  exact φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜).flip
    ((hpartloc k).locallyIntegrableOn _)

lemma smooth_regular_negative_laplacian {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u f : P201.Space n → 𝕜) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hf : Continuous f) (heq : ∀ x, -P201.laplacian u x = f x) :
    -P201.distributionLaplacian (P201.regularDistribution (⊤ : P201.Domain n) u) =
      P201.regularDistribution ⊤ f := by
  have hlap : P201.laplacian u = -f := by funext x; exact neg_eq_iff_eq_neg.mp (heq x)
  rw [smooth_regular_laplacian u hu, hlap]
  ext φ
  change -(P201.regularDistribution ⊤ (-f) φ) = P201.regularDistribution ⊤ f φ
  rw [P102.U4.regular_pairing n 𝕜 ⊤ _
    (hf.neg.locallyIntegrable.locallyIntegrableOn _)]
  rw [P102.U4.regular_pairing n 𝕜 ⊤ _
    (hf.locallyIntegrable.locallyIntegrableOn _)]
  simp only [Opens.coe_top, setIntegral_univ, Pi.neg_apply, neg_mul, integral_neg, neg_neg]

lemma smoothPotential_derivative_equation {n : ℕ} (hn : 1 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (α : P201.MultiIndex n) :
    -P201.distributionLaplacian (P201.regularDistribution (⊤ : P201.Domain n)
      (P201.multiPartial (P201.newtonPotential F) α)) =
      P201.distributionDerivative α (P201.regularDistribution ⊤ F) := by
  have hu := P201.newtonSmooth n hn F
  have hpoisson := smooth_regular_negative_laplacian (P201.newtonPotential F) F hu
    F.continuous (P201.newtonEquation n hn F)
  have hd : P201.distributionDerivative α
      (P201.regularDistribution ⊤ (P201.newtonPotential F)) =
      P201.regularDistribution ⊤ (P201.multiPartial (P201.newtonPotential F) α) :=
    P102.U4.derivative_classicalCompatibility n ℝ ⊤ α _
      (hu.of_le (by simp)).contDiffOn
  rw [← hd, ← distributionDerivative_laplacian_commute, ← distributionDerivative_neg, hpoisson]

lemma smoothPotential_complex_derivative_equation {n : ℕ} (hn : 1 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (α : P201.MultiIndex n) :
    -P201.distributionLaplacian (P201.regularDistribution (⊤ : P201.Domain n)
      (fun x => (P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) α x : ℂ))) =
      P201.distributionDerivative α (P201.regularDistribution ⊤ (fun x => (F x : ℂ))) := by
  let u : P201.Space n → ℂ := fun x => (P201.newtonPotential F x : ℂ)
  have hus := P201.newtonSmooth n hn F
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := Complex.ofRealCLM.contDiff.comp hus
  have heq : ∀ x, -P201.laplacian u x = (F x : ℂ) := by
    intro x
    change -P201Specs.laplacian (fun y => (P201.newtonPotential F y : ℂ)) x = (F x : ℂ)
    rw [P201.Elliptic.WholeSpaceW2p.laplacian_ofReal hus x]
    exact_mod_cast P201.newtonEquation n hn F x
  have hpoisson := smooth_regular_negative_laplacian u (fun x => (F x : ℂ)) hu
    (Complex.continuous_ofReal.comp F.continuous) heq
  have hd : P201.distributionDerivative α (P201.regularDistribution ⊤ u) =
      P201.regularDistribution ⊤
        (fun x => (P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) α x : ℂ)) := by
    change P102.U4.distributionPartial α (P102.U4.regularDistribution ⊤ u) = _
    rw [P102.U4.derivative_classicalCompatibility n ℂ ⊤ α u
      (hu.of_le (by simp)).contDiffOn]
    congr 1
    funext x
    exact P201.Elliptic.WholeSpaceW2p.multiPartial_ofReal hus α x
  rw [← hd, ← distributionDerivative_laplacian_commute, ← distributionDerivative_neg, hpoisson]



lemma toLp_tendsto_of_toReal {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℕ → X → E) (F : X → E) (hf : ∀ m, MemLp (f m) p μ) (hF : MemLp F p μ)
    (hlim : Tendsto (fun m => (eLpNorm (fun x => f m x - F x) p μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (hF.toLp F)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have heq (m : ℕ) : dist ((hf m).toLp (f m)) (hF.toLp F) =
      (eLpNorm (fun x => f m x - F x) p μ).toReal := by
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hf m).coeFn_toLp.sub hF.coeFn_toLp))
  simpa only [heq] using hlim

lemma weakDerivative_closed_multi {n : ℕ} (Ω : P201.Domain n) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (α : P201.MultiIndex n)
    (u v : ℕ → P201.Lp ℝ Ω p) (U V : P201.Lp ℝ Ω p)
    (hu : Tendsto u atTop (𝓝 U)) (hv : Tendsto v atTop (𝓝 V))
    (h : ∀ m, P201.distributionDerivative α (P201.regularDistribution Ω (u m)) =
      P201.regularDistribution Ω (v m)) :
    P201.distributionDerivative α (P201.regularDistribution Ω U) =
      P201.regularDistribution Ω V := by
  apply (P102.U4.distributionPartial_eq_regularLp_iff Ω p α U V).mpr
  intro φ
  have hleft := ((P102.U4.lpTestPairing Ω p φ).continuous.tendsto V).comp hv
  have hright := (tendsto_const_nhds (x := (-1 : ℝ) ^ α.card)).mul
    (((P102.U4.lpTestPairing Ω p (P102.U4.testPartialWord Ω (α.sort (· ≤ ·)) φ)).continuous.tendsto U).comp hu)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall fun m =>
    ((P102.U4.distributionPartial_eq_regularLp_iff Ω p α (u m) (v m)).mp (h m) φ).symm)

lemma exists_sobolev_of_local_derivatives {n m : ℕ} (Ω : P201.Domain n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (H : P102.U4.SobolevIndex n m → P201.Space n → ℝ)
    (hH : ∀ α, LocallyIntegrableOn (H α) Ω volume)
    (hmem : ∀ α, MemLp (H α) p (P201.domainMeasure Ω))
    (hder : ∀ α, P201.distributionDerivative α.val
      (P201.regularDistribution Ω (H (P102.U4.zeroSobolevIndex n m))) =
        P201.regularDistribution Ω (H α)) :
    ∃ w : P201.W ℝ Ω m p,
      (P102.U4.sobolevUnderlying w : P201.Space n → ℝ) =ᵐ[P201.domainMeasure Ω]
        H (P102.U4.zeroSobolevIndex n m) ∧
      ‖w‖ = ∑ α, (eLpNorm (H α) p (P201.domainMeasure Ω)).toReal := by
  let V (α : P102.U4.SobolevIndex n m) : P201.Lp ℝ Ω p := (hmem α).toLp (H α)
  have hreg (α : P102.U4.SobolevIndex n m) :
      P201.regularDistribution Ω (V α) = P201.regularDistribution Ω (H α) :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω p (V α)) (hH α)).mpr (hmem α).coeFn_toLp
  let W : P201.W ℝ Ω m p := ⟨WithLp.toLp 1 V, by
    apply (P102.U4.mem_sobolevSubmodule_iff Ω m p _).mpr
    intro α φ
    have he : P102.U4.distributionPartial α.val
        (P102.U4.regularDistribution Ω (V (P102.U4.zeroSobolevIndex n m))) =
        P102.U4.regularDistribution Ω (V α) := by
      exact (congrArg (P201.distributionDerivative α.val)
        (hreg (P102.U4.zeroSobolevIndex n m))).trans ((hder α).trans (hreg α).symm)
    exact (P102.U4.distributionPartial_eq_regularLp_iff Ω p _ _ _).mp he φ⟩
  refine ⟨W, (hmem (P102.U4.zeroSobolevIndex n m)).coeFn_toLp, ?_⟩
  rw [P102.U4.sobolev_norm Ω m p]
  apply Finset.sum_congr rfl
  intro α _
  exact Lp.norm_toLp (H α) (hmem α)

lemma toLp_mono_measure_tendsto {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ ν : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hμ : μ ≤ ν) (f : ℕ → MeasureTheory.Lp E p ν) (F : MeasureTheory.Lp E p ν)
    (hlim : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun m => ((Lp.memLp (f m)).mono_measure hμ).toLp (f m))
      atTop (𝓝 (((Lp.memLp F).mono_measure hμ).toLp F)) := by
  apply toLp_tendsto_of_toReal
  have hg := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun m => ?_) hg
  rw [Lp.norm_def]
  have he : eLpNorm (fun x => f m x - F x) p ν = eLpNorm (f m - F) p ν :=
    eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
  rw [← he]
  exact ENNReal.toReal_mono ((Lp.memLp (f m)).sub (Lp.memLp F)).eLpNorm_ne_top
    (eLpNorm_mono_measure _ hμ)

lemma derivative_limit_functions {n : ℕ} (Ω : P201.Domain n) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (α : P201.MultiIndex n)
    (u v : ℕ → P201.Space n → ℝ) (U V : P201.Space n → ℝ)
    (hu : ∀ m, LocallyIntegrable (u m) volume)
    (hv : ∀ m, LocallyIntegrable (v m) volume)
    (hU : LocallyIntegrable U volume) (hV : LocallyIntegrable V volume)
    (humem : ∀ m, MemLp (u m) p (P201.domainMeasure Ω))
    (hvmem : ∀ m, MemLp (v m) p (P201.domainMeasure Ω))
    (hUmem : MemLp U p (P201.domainMeasure Ω))
    (hVmem : MemLp V p (P201.domainMeasure Ω))
    (hlimu : Tendsto (fun m => (humem m).toLp (u m)) atTop (𝓝 (hUmem.toLp U)))
    (hlimv : Tendsto (fun m => (hvmem m).toLp (v m)) atTop (𝓝 (hVmem.toLp V)))
    (hder : ∀ m, P201.distributionDerivative α (P201.regularDistribution ⊤ (u m)) =
      P201.regularDistribution ⊤ (v m)) :
    P201.distributionDerivative α (P201.regularDistribution Ω U) =
      P201.regularDistribution Ω V := by
  have hreg (f : P201.Space n → ℝ) (hf : LocallyIntegrable f volume)
      (hm : MemLp f p (P201.domainMeasure Ω)) :
      P201.regularDistribution Ω (hm.toLp f) = P201.regularDistribution Ω f :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω p _) (hf.locallyIntegrableOn Ω)).mpr hm.coeFn_toLp
  have hd := weakDerivative_closed_multi Ω p α
    (fun m => (humem m).toLp (u m)) (fun m => (hvmem m).toLp (v m))
    (hUmem.toLp U) (hVmem.toLp V) hlimu hlimv (fun m => by
      rw [hreg _ (hu m) (humem m), hreg _ (hv m) (hvmem m)]
      exact regular_derivative_restrict Ω α _ _ (hu m) (hv m) (hder m))
  rwa [hreg U hU hUmem, hreg V hV hVmem] at hd

/-- Smooth-source identification extends to rough compact-source data by the
closed graph of each weak derivative on every bounded open observation set. -/
lemma localHessian_of_smooth {n : ℕ} (hn : 1 ≤ n)
    (hSmooth : P201Specs.Elliptic.NewtonLp.SmoothHessianInDimension n)
    (p : P102.U2.CZLpData.Exponent)
    (R : Fin n → P102.U2.CZLpData.StrongOperator n p)
    (hR : ∀ i, P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p (R i))
    (K : Compacts (P201.Space n)) (Ω : P201.Domain n)
    (hΩ : Bornology.IsBounded (Ω : Set (P201.Space n)))
    (F : P201.Space n → ℝ) (hF : MemLp F p.val volume)
    (hK : ∀ᵐ x ∂volume, x ∉ K → F x = 0) (i j : Fin n) :
    let hFc : MemLp (fun x => (F x : ℂ)) p.val volume :=
      Complex.ofRealCLM.comp_memLp' hF
    let G : MeasureTheory.Lp ℝ p.val (volume : Measure (P201.Space n)) :=
      Complex.reCLM.compLp (R i (R j (hFc.toLp (fun x => (F x : ℂ)))))
    P201.distributionDerivative {i,j}
      (P201.regularDistribution Ω (P201Specs.Elliptic.NewtonHessian.holderPotential F)) =
      P201.regularDistribution Ω G := by
  dsimp only
  let hFc : MemLp (fun x => (F x : ℂ)) p.val volume :=
    Complex.ofRealCLM.comp_memLp' hF
  let G : MeasureTheory.Lp ℝ p.val (volume : Measure (P201.Space n)) :=
    Complex.reCLM.compLp (R i (R j (hFc.toLp (fun x => (F x : ℂ)))))
  let B : Compacts (P201.Space n) := ⟨closure (Ω : Set (P201.Space n)), hΩ.isCompact_closure⟩
  have hμ : P201.domainMeasure Ω ≤ volume.restrict (B : Set (P201.Space n)) :=
    Measure.restrict_mono subset_closure le_rfl
  obtain ⟨L, hKL, happ⟩ := commonSupportApproximation n p.val p.one_lt.le p.lt_top.ne K
  obtain ⟨f, hfSupp, hfLim⟩ := happ F hF hK
  have hf (m : ℕ) : MemLp (f m : P201.Space n → ℝ) p.val volume :=
    (f m).continuous.memLp_of_hasCompactSupport (f m).hasCompactSupport
  have hfL (m : ℕ) : ∀ᵐ x ∂volume, x ∉ L → f m x = 0 :=
    Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hfSupp m h))
  have hFL : ∀ᵐ x ∂volume, x ∉ L → F x = 0 := by
    filter_upwards [hK] with x hx hnot
    exact hx (fun h => hnot (hKL h))
  let u (m : ℕ) := P201Specs.Elliptic.NewtonHessian.holderPotential (f m)
  let U := P201Specs.Elliptic.NewtonHessian.holderPotential F
  have huc (m : ℕ) : LocallyIntegrable (u m) volume :=
    (potentialEquation n hn p.val p.one_lt.le (f m) (hf m) ⟨L,hfL m⟩).2.1
  have hUc : LocallyIntegrable U volume :=
    (potentialEquation n hn p.val p.one_lt.le F hF ⟨K,hK⟩).2.1
  obtain ⟨huB, hUB, hulimB⟩ := localConvolutionConvergence n p.val p.one_lt.le L B
    (P201.fundamentalKernel n) (P201.fundamentalLocalIntegrability n hn)
    (fun m => (f m : P201.Space n → ℝ)) F hf hF hfL hFL hfLim
  simp_rw [← potential_eq_functionConvolution] at huB hUB hulimB
  have huΩ (m : ℕ) : MemLp (u m) p.val (P201.domainMeasure Ω) := (huB m).mono_measure hμ
  have hUΩ : MemLp U p.val (P201.domainMeasure Ω) := hUB.mono_measure hμ
  have hulimΩ : Tendsto (fun m => (eLpNorm (fun x => u m x - U x) p.val
      (P201.domainMeasure Ω)).toReal) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun m => ?_) hulimB
    exact ENNReal.toReal_mono ((huB m).sub hUB).eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  let hfC (m : ℕ) : MemLp (fun x => (f m x : ℂ)) p.val volume :=
    Complex.ofRealCLM.comp_memLp' (hf m)
  have hfCLim : Tendsto (fun m => (hfC m).toLp (fun x => (f m x : ℂ)))
      atTop (𝓝 (hFc.toLp (fun x => (F x : ℂ)))) := by
    apply toLp_tendsto_of_toReal
    have he (m : ℕ) : eLpNorm (fun x => (f m x : ℂ) - (F x : ℂ)) p.val volume =
        eLpNorm (fun x => f m x - F x) p.val volume := by
      simp_rw [← Complex.ofReal_sub]
      exact P201.Elliptic.WholeSpaceW2p.eLpNorm_complexify volume p.val _
        ((hf m).sub hF).aestronglyMeasurable
    simpa only [he] using hfLim
  let v (m : ℕ) : MeasureTheory.Lp ℝ p.val (volume : Measure (P201.Space n)) :=
    Complex.reCLM.compLp (R i (R j ((hfC m).toLp (fun x => (f m x : ℂ)))))
  have hvlim : Tendsto v atTop (𝓝 G) :=
    ((Complex.reCLM.compLpL p.val volume).continuous.tendsto _).comp
      (((R i).continuous.tendsto _).comp (((R j).continuous.tendsto _).comp hfCLim))
  have hvloc (m : ℕ) : LocallyIntegrable (v m : P201.Space n → ℝ) volume :=
    (Lp.memLp (v m)).locallyIntegrable p.one_lt.le
  have hVloc : LocallyIntegrable (G : P201.Space n → ℝ) volume :=
    (Lp.memLp G).locallyIntegrable p.one_lt.le
  have hvΩ (m : ℕ) : MemLp (v m : P201.Space n → ℝ) p.val (P201.domainMeasure Ω) :=
    (Lp.memLp (v m)).mono_measure Measure.restrict_le_self
  have hVΩ : MemLp (G : P201.Space n → ℝ) p.val (P201.domainMeasure Ω) :=
    (Lp.memLp G).mono_measure Measure.restrict_le_self
  have hder (m : ℕ) : P201.distributionDerivative {i,j} (P201.regularDistribution ⊤ (u m)) =
      P201.regularDistribution ⊤ (v m) := by
    obtain ⟨hFm, _, hd⟩ := hSmooth p R hR (f m) i j
    have he : (v m : P201.Space n → ℝ) =ᵐ[volume]
        (fun x => (R i (R j ((hfC m).toLp (fun x => (f m x : ℂ))))) x |>.re) :=
      Complex.reCLM.coeFn_compLp _
    have hreal := (P102.U4.regular_injectivity n ℝ ⊤ _ _
      ((hvloc m).locallyIntegrableOn ⊤)
      (((Complex.reCLM.comp_memLp' (Lp.memLp _)).locallyIntegrable p.one_lt.le).locallyIntegrableOn ⊤)).mpr
      (by simpa only [P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ, Function.comp_def, Complex.reCLM_apply] using he)
    exact hd.trans hreal.symm
  exact derivative_limit_functions Ω p.val {i,j} u (fun m => (v m : P201.Space n → ℝ)) U G
    huc hvloc hUc hVloc huΩ hvΩ hUΩ hVΩ
    (toLp_tendsto_of_toReal u U huΩ hUΩ hulimΩ)
    (toLp_mono_measure_tendsto Measure.restrict_le_self v G hvlim) hder

/-- The proof route from the smooth Riesz Hessian identity to the full rough
compact-source Sobolev estimate, with its constant chosen before the datum. -/
lemma potentialEstimate_of_smoothHessian {n : ℕ} (hn : 1 ≤ n)
    (hSmooth : P201Specs.Elliptic.NewtonLp.SmoothHessianInDimension n) :
    P201Specs.Elliptic.NewtonLp.PotentialEstimateInDimension n := by
  intro p K Ω hΩ
  obtain ⟨R, hR⟩ := P201.Elliptic.WholeSpaceW2p.rieszLp_exists hn p
  let B : Compacts (P201.Space n) := ⟨closure (Ω : Set (P201.Space n)), hΩ.isCompact_closure⟩
  obtain ⟨C, hC, hb⟩ := lowerOrderEstimate n hn p.val p.one_lt.le K B
  let D : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖Complex.reCLM‖ * ‖R i‖ * ‖R j‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let d : ℝ := Fintype.card (P102.U4.SobolevIndex n 2)
  refine ⟨d * (C+D), mul_nonneg (by positivity) (add_nonneg hC hD), ?_⟩
  intro F hF hK
  obtain ⟨hex, hloc, heq⟩ := potentialEquation n hn p.val p.one_lt.le F hF ⟨K,hK⟩
  refine ⟨hex, hloc, heq, ?_⟩
  let u := P201Specs.Elliptic.NewtonHessian.holderPotential F
  let g (i : Fin n) := P102.U4.functionConvolution
    (P201Specs.Elliptic.NewtonHessian.gradientKernel i) F
  have hg (i : Fin n) : LocallyIntegrable (g i) volume :=
    (P102.U4.functionConvolution_locallyIntegrable _ _
      (P201.Elliptic.NewtonHessian.gradientKernel_locallyIntegrable hn i)
      (hF.locallyIntegrable p.one_lt.le) (Or.inr ⟨K,hK⟩)).2
  let hFc : MemLp (fun x => (F x : ℂ)) p.val volume :=
    Complex.ofRealCLM.comp_memLp' hF
  let G (i j : Fin n) : MeasureTheory.Lp ℝ p.val (volume : Measure (P201.Space n)) :=
    Complex.reCLM.compLp (R i (R j (hFc.toLp (fun x => (F x : ℂ)))))
  have hG (i j : Fin n) : LocallyIntegrable (G i j : P201.Space n → ℝ) volume :=
    (Lp.memLp (G i j)).locallyIntegrable p.one_lt.le
  obtain ⟨huB, hgB, hbound⟩ := hb F hF hK
  have hμ : P201.domainMeasure Ω ≤ volume.restrict (B : Set (P201.Space n)) :=
    Measure.restrict_mono subset_closure le_rfl
  have huΩ : MemLp u p.val (P201.domainMeasure Ω) := huB.mono_measure hμ
  have hgΩ (i : Fin n) : MemLp (g i) p.val (P201.domainMeasure Ω) := (hgB i).mono_measure hμ
  have hGΩ (i j : Fin n) : MemLp (G i j : P201.Space n → ℝ) p.val (P201.domainMeasure Ω) :=
    (Lp.memLp (G i j)).mono_measure Measure.restrict_le_self
  let N := (eLpNorm F p.val volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hnorm (f : P201.Space n → ℝ) (hf : MemLp f p.val (volume.restrict B)) :
      (eLpNorm f p.val (P201.domainMeasure Ω)).toReal ≤
        (eLpNorm f p.val (volume.restrict B)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  have hsum0 : 0 ≤ ∑ i : Fin n, (eLpNorm (g i) p.val (volume.restrict B)).toReal :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have huBound : (eLpNorm u p.val (P201.domainMeasure Ω)).toReal ≤ (C+D) * N := by
    have hh : (eLpNorm u p.val (P201.domainMeasure Ω)).toReal ≤ C*N :=
      (hnorm u huB).trans ((le_add_of_nonneg_right hsum0).trans hbound)
    exact hh.trans (by nlinarith)
  have hgBound (i : Fin n) : (eLpNorm (g i) p.val (P201.domainMeasure Ω)).toReal ≤ (C+D) * N := by
    have hsum : (eLpNorm (g i) p.val (volume.restrict B)).toReal ≤
        ∑ j : Fin n, (eLpNorm (g j) p.val (volume.restrict B)).toReal :=
      Finset.single_le_sum (f := fun j => (eLpNorm (g j) p.val (volume.restrict B)).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
    have hh : (eLpNorm (g i) p.val (P201.domainMeasure Ω)).toReal ≤ C*N :=
      (hnorm (g i) (hgB i)).trans (hsum.trans
        ((le_add_of_nonneg_left ENNReal.toReal_nonneg).trans hbound))
    exact hh.trans (by nlinarith)
  have hGnorm (i j : Fin n) : ‖G i j‖ ≤
      (‖Complex.reCLM‖ * ‖R i‖ * ‖R j‖) * N := by
    have hFcN : ‖hFc.toLp (fun x => (F x : ℂ))‖ = N := by
      rw [Lp.norm_toLp, P201.Elliptic.WholeSpaceW2p.eLpNorm_complexify volume p.val F hF.aestronglyMeasurable]
    calc
      ‖G i j‖ ≤ ‖Complex.reCLM‖ * ‖R i (R j (hFc.toLp (fun x => (F x : ℂ))))‖ :=
        Complex.reCLM.norm_compLp_le _
      _ ≤ ‖Complex.reCLM‖ * (‖R i‖ * (‖R j‖ * ‖hFc.toLp (fun x => (F x : ℂ))‖)) :=
        mul_le_mul_of_nonneg_left (((R i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((R j).le_opNorm _) (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by rw [hFcN]; ring
  have hcoeff (i j : Fin n) : ‖Complex.reCLM‖ * ‖R i‖ * ‖R j‖ ≤ D := by
    have hsingle : ‖Complex.reCLM‖ * ‖R i‖ * ‖R j‖ ≤
        ∑ l : Fin n, ‖Complex.reCLM‖ * ‖R i‖ * ‖R l‖ :=
      Finset.single_le_sum (f := fun l => ‖Complex.reCLM‖ * ‖R i‖ * ‖R l‖)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    exact hsingle.trans (Finset.single_le_sum
      (f := fun k => ∑ l : Fin n, ‖Complex.reCLM‖ * ‖R k‖ * ‖R l‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hGBound (i j : Fin n) :
      (eLpNorm (G i j : P201.Space n → ℝ) p.val (P201.domainMeasure Ω)).toReal ≤ (C+D)*N := by
    have hh : (eLpNorm (G i j : P201.Space n → ℝ) p.val (P201.domainMeasure Ω)).toReal ≤ ‖G i j‖ :=
      ENNReal.toReal_mono (Lp.memLp (G i j)).eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    exact hh.trans ((hGnorm i j).trans ((mul_le_mul_of_nonneg_right (hcoeff i j) hN).trans (by nlinarith)))
  let H (α : P102.U4.SobolevIndex n 2) : P201.Space n → ℝ :=
    if h1 : α.val.card = 1 then g (Multiset.card_eq_one.mp h1).choose else
    if h2 : α.val.card = 2 then G (Multiset.card_eq_two.mp h2).choose
      (Multiset.card_eq_two.mp h2).choose_spec.choose else u
  have hHloc (α : P102.U4.SobolevIndex n 2) : LocallyIntegrable (H α) volume := by
    dsimp only [H]
    split_ifs
    · exact hg _
    · exact hG _ _
    · exact hloc
  have hHmem (α : P102.U4.SobolevIndex n 2) : MemLp (H α) p.val (P201.domainMeasure Ω) := by
    dsimp only [H]
    split_ifs
    · exact hgΩ _
    · exact hGΩ _ _
    · exact huΩ
  have hzero : H (P102.U4.zeroSobolevIndex n 2) = u := by simp [H, P102.U4.zeroSobolevIndex]
  have hHder (α : P102.U4.SobolevIndex n 2) :
      P201.distributionDerivative α.val
        (P201.regularDistribution Ω (H (P102.U4.zeroSobolevIndex n 2))) =
          P201.regularDistribution Ω (H α) := by
    rw [hzero]
    by_cases h1 : α.val.card = 1
    · simp only [H, dite_eq_left h1]
      exact (congrArg (fun β => P201.distributionDerivative β (P201.regularDistribution Ω u))
        (Multiset.card_eq_one.mp h1).choose_spec).trans
        (regular_derivative_restrict Ω _ u _ hloc (hg _)
          (weakGradient n hn p.val p.one_lt.le F hF ⟨K,hK⟩ _))
    · by_cases h2 : α.val.card = 2
      · simp only [H, dite_eq_right h1, dite_eq_left h2]
        exact (congrArg (fun β => P201.distributionDerivative β (P201.regularDistribution Ω u))
          (Multiset.card_eq_two.mp h2).choose_spec.choose_spec).trans
          (localHessian_of_smooth hn hSmooth p R hR K Ω hΩ F hF hK _ _)
      · have h0 : α.val = 0 := Multiset.card_eq_zero.mp (by have := α.property; omega)
        simp only [H, dite_eq_right h1, dite_eq_right h2]
        rw [h0]
        exact P102.U4.derivative_zero n ℝ Ω _
  obtain ⟨w, hw, hwn⟩ := exists_sobolev_of_local_derivatives Ω p.val H
    (fun α => (hHloc α).locallyIntegrableOn Ω) hHmem hHder
  refine ⟨w, by simpa only [hzero] using hw, ?_⟩
  rw [hwn]
  have hentry (α : P102.U4.SobolevIndex n 2) :
      (eLpNorm (H α) p.val (P201.domainMeasure Ω)).toReal ≤ (C+D)*N := by
    dsimp only [H]
    split_ifs
    · exact hgBound _
    · exact hGBound _ _
    · exact huBound
  calc
    _ ≤ ∑ α : P102.U4.SobolevIndex n 2, (C+D)*N :=
      Finset.sum_le_sum (fun α _ => hentry α)
    _ = _ := by simp [d, N, Finset.sum_const, nsmul_eq_mul, mul_assoc]


open scoped SchwartzMap FourierTransform Laplacian LineDeriv

lemma schwartz_laplacian_apply {n : ℕ} (u : 𝓢(P201.Space n, ℂ)) (x : P201.Space n) :
    (Δ u) x = P201.laplacian (u : P201.Space n → ℂ) x := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [sum_apply]
  change (∑ i : Fin n, (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
    (∂_{EuclideanSpace.basisFun (Fin n) ℝ i} u)) x) = _
  change _ = ∑ i : Fin n, P201.multiPartial u {i,i} x
  apply Finset.sum_congr rfl
  intro i _
  change P201Specs.Elliptic.WholeSpaceW2p.schwartzHessian u i i x = _
  exact P201.Elliptic.WholeSpaceW2p.schwartzHessian_apply u i i x

lemma l2_tempered_laplacian_test {n : ℕ}
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space n)))
    (φ : P201.Test ℂ (⊤ : P201.Domain n)) :
    (Δ (Lp.toTemperedDistribution f)) (P102.U4.testToSchwartz n ℂ φ) =
      P201.distributionLaplacian (P201.regularDistribution ⊤ f) φ := by
  rw [TemperedDistribution.laplacian_apply_apply,
    Lp.toTemperedDistribution_apply]
  change (∫ x, (Δ (P102.U4.testToSchwartz n ℂ φ)) x * f x) =
    (∑ i : Fin n, P201.distributionDerivative {i,i} (P201.regularDistribution ⊤ f)) φ
  simp only [sum_apply]
  have hloc := ((Lp.memLp f).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).locallyIntegrableOn
    (⊤ : P201.Domain n)
  have haction (i : Fin n) : P201.distributionDerivative {i,i}
      (P201.regularDistribution ⊤ f) φ =
      ∫ x, P201.multiPartial φ {i,i} x * f x := by
    obtain ⟨ψ, hψ, he⟩ := P102.U4.derivative_formula n ℂ ⊤ {i,i}
      (P201.regularDistribution ⊤ f) φ
    rw [he, P102.U4.regular_pairing n ℂ ⊤ f hloc ψ]
    simp only [Multiset.card_pair, neg_one_sq, one_mul, Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae (.of_forall fun x => by
      change f x * ψ x = P201.multiPartial φ {i,i} x * f x
      rw [hψ]; exact mul_comm _ _)
  simp_rw [haction]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    rw [schwartz_laplacian_apply]
    change (∑ i : Fin n, P201.multiPartial (P102.U4.testToSchwartz n ℂ φ) {i,i} x) * f x = _
    rw [Finset.sum_mul]
    rfl
  · intro i _
    obtain ⟨ψ, hψ, _⟩ := P102.U4.derivative_formula n ℂ ⊤ {i,i}
      (P201.regularDistribution ⊤ f) φ
    have h := ψ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ) hloc
    change Integrable (fun x => ψ x * f x) volume at h
    simpa only [hψ] using h

lemma l2_eq_zero_of_tempered_laplacian_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space n)))
    (hf : Δ (Lp.toTemperedDistribution f) = 0) : f = 0 := by
  have hm : TemperedDistribution.smulLeftCLM ℂ
      (fun x : P201.Space n => Complex.ofReal (‖x‖ ^ 2))
      (Lp.toTemperedDistribution (𝓕 f)) = 0 := by
    rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM] at hf
    have hc : (-(2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by exact neg_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero two_ne_zero Real.pi_ne_zero))
    have hf' := (smul_eq_zero.mp hf).resolve_left hc
    have hf'' := congrArg (fun T : 𝓢'(P201.Space n, ℂ) => 𝓕 T) hf'
    simpa only [TemperedDistribution.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq, FourierTransform.fourier_zero,
      Lp.fourier_toTemperedDistribution_eq] using hf''
  have hloc : LocallyIntegrable
      (fun x : P201.Space n => (‖x‖ ^ 2 : ℝ) • (𝓕 f) x) volume := by
    simpa only [Complex.real_smul] using
      ((Lp.memLp (𝓕 f)).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).continuous_mul
        (show Continuous (fun x : P201.Space n => Complex.ofReal (‖x‖ ^ 2)) by fun_prop)
  have hae : ∀ᵐ x ∂(volume : Measure (P201.Space n)),
      (‖x‖ ^ 2 : ℝ) • (𝓕 f) x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro g hg hgc
    let G : 𝓢(P201.Space n, ℂ) :=
      (hgc.comp_left (map_zero (Complex.ofRealCLM))).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hg)
    have hG := congrArg (fun T : 𝓢'(P201.Space n, ℂ) => T G) hm
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply] at hG
    simp only [SchwartzMap.smulLeftCLM_apply_apply
      (show (fun x : P201.Space n => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth by fun_prop),
      smul_eq_mul] at hG
    change (∫ x, (Complex.ofReal (‖x‖ ^ 2) * Complex.ofReal (g x)) * (𝓕 f) x) = 0 at hG
    simpa only [Complex.real_smul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hG
  have : NeZero n := ⟨by omega⟩
  have hz : ∀ᵐ x ∂(volume : Measure (P201.Space n)), x ≠ 0 :=
    Measure.ae_ne volume 0
  have hfour : (𝓕 f : MeasureTheory.Lp ℂ 2 volume) = 0 := by
    apply Lp.ext
    filter_upwards [hae, hz, Lp.coeFn_zero ℂ 2 volume] with x hx hx0 hzero
    rw [hzero]
    exact (smul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0))
  exact (FourierTransform.fourierCLE ℂ (MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space n)))).injective
    (by simpa only [FourierTransform.fourierCLE_apply, FourierTransform.fourier_zero] using hfour)

lemma l2_eq_zero_of_laplacian_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space n)))
    (hf : P201.distributionLaplacian (P201.regularDistribution ⊤ f) = 0) :
    f = 0 := by
  apply l2_eq_zero_of_tempered_laplacian_eq_zero hn f
  have htest : ∀ φ : P102.U4.WholeTests n ℂ,
      (Δ (Lp.toTemperedDistribution f)) (P102.U4.testToSchwartz n ℂ φ) = 0 := by
    intro φ
    rw [l2_tempered_laplacian_test, hf]
    rfl
  have hall := (P102.U4.testToSchwartz_denseRange n ℂ).equalizer
    (Δ (Lp.toTemperedDistribution f)).continuous continuous_const (funext htest)
  ext φ
  exact congrFun hall φ

lemma rieszComposition_tempered_poisson {n : ℕ} (hn : 1 ≤ n)
    (F : 𝓢(P201.Space n, ℂ)) (i j : Fin n) :
    -(Δ (Lp.toTemperedDistribution
      (P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (F.toLp 2))))) =
    Lp.toTemperedDistribution ((P201Specs.Elliptic.WholeSpaceW2p.schwartzHessian F i j).toLp 2) := by
  let G := P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (F.toLp 2))
  change -(Δ (Lp.toTemperedDistribution G)) = _
  apply (FourierTransform.fourierCLE ℂ (𝓢'(P201.Space n, ℂ))).injective
  simp only [FourierTransform.fourierCLE_apply,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM,
    TemperedDistribution.fourierMultiplierCLM_apply,
    neg_smul, neg_neg, Lp.fourier_toTemperedDistribution_eq]
  rw [← Complex.coe_smul, FourierTransform.fourier_smul,
    FourierTransform.fourier_fourierInv_eq]
  have hi := P102.U3.RieszTransforms.canonical_multiplier hn i 0
    (P102.U3.Riesz.rieszL2 j (F.toLp 2))
  have hj := P102.U3.RieszTransforms.canonical_multiplier hn j 0 (F.toLp 2)
  have hF := P201.Elliptic.WholeSpaceW2p.fourierL2_schwartz_ae F
  have hS := P201.Elliptic.WholeSpaceW2p.fourierL2_schwartz_ae
    (P201Specs.Elliptic.WholeSpaceW2p.schwartzHessian F i j)
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (show (fun x : P201.Space n => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth by fun_prop)]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [hi, hj, hF, hS] with ξ hiξ hjξ hFξ hSξ
  change (Complex.ofReal ((2 * Real.pi) ^ 2)) • ((Complex.ofReal (‖ξ‖ ^ 2) • φ ξ) • (𝓕 G : MeasureTheory.Lp ℂ 2 volume) ξ) =
    φ ξ • (P102.Specs.U3.Riesz.F2 n
      ((P201Specs.Elliptic.WholeSpaceW2p.schwartzHessian F i j).toLp 2)) ξ
  change (𝓕 G : MeasureTheory.Lp ℂ 2 volume) ξ = _ at hiξ
  rw [hiξ, hjξ, hFξ, hSξ,
    P201.Elliptic.WholeSpaceW2p.fourier_hessian]
  by_cases hξ : ξ = 0
  · simp [P102.Specs.U3.Riesz.symbolAtOrigin, hξ]
  · have hnorm : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
    simp only [P102.Specs.U3.Riesz.symbolAtOrigin, ite_eq_right hξ,
      P102.Specs.U3.Riesz.symbolValue, Complex.ofReal_div,
      smul_eq_mul, Complex.ofReal_pow]
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]

lemma rieszComposition_distribution_poisson {n : ℕ} (hn : 1 ≤ n)
    (F : P201.Test ℂ (⊤ : P201.Domain n)) (i j : Fin n) :
    let Fsch := P102.U4.testToSchwartz n ℂ F;
    let G := P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (Fsch.toLp 2));
    -P201.distributionLaplacian (P201.regularDistribution ⊤ G) =
      P201.distributionDerivative {i,j} (P201.regularDistribution ⊤ F) := by
  let Fsch := P102.U4.testToSchwartz n ℂ F
  let G := P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (Fsch.toLp 2))
  change -P201.distributionLaplacian (P201.regularDistribution ⊤ G) = _
  have hclass : P201.distributionDerivative {i,j} (P201.regularDistribution ⊤ F) =
      P201.regularDistribution ⊤ (P201.multiPartial F {i,j}) :=
    P102.U4.derivative_classicalCompatibility n ℂ ⊤ {i,j} F
      (F.contDiff.of_le (by simp)).contDiffOn
  rw [hclass]
  let S := P201Specs.Elliptic.WholeSpaceW2p.schwartzHessian Fsch i j
  have heS : (S : P201.Space n → ℂ) = P201.multiPartial F {i,j} := by
    ext x
    exact P201.Elliptic.WholeSpaceW2p.schwartzHessian_apply Fsch i j x
  rw [← heS]
  ext φ
  have heq := congrArg (fun T : 𝓢'(P201.Space n, ℂ) =>
    T (P102.U4.testToSchwartz n ℂ φ))
    (rieszComposition_tempered_poisson hn Fsch i j)
  change -(P201.distributionLaplacian (P201.regularDistribution ⊤ G) φ) = _
  change -((Δ (Lp.toTemperedDistribution G)) (P102.U4.testToSchwartz n ℂ φ)) =
    (Lp.toTemperedDistribution (S.toLp 2)) (P102.U4.testToSchwartz n ℂ φ) at heq
  have hbridge := congrArg Neg.neg (l2_tempered_laplacian_test G φ).symm
  rw [hbridge, heq]
  rw [Lp.toTemperedDistribution_apply,
    P102.U4.regular_pairing n ℂ ⊤ S (S.continuous.locallyIntegrable.locallyIntegrableOn _)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [S.coeFn_toLp 2] with x hx
  change φ x * (S.toLp 2 : MeasureTheory.Lp ℂ 2 volume) x = S x * φ x
  rw [hx, mul_comm]



lemma l2_eq_of_laplacian_eq {n : ℕ} (hn : 1 ≤ n)
    (f g : MeasureTheory.Lp ℂ 2 (volume : Measure (P201.Space n)))
    (hfg : P201.distributionLaplacian (P201.regularDistribution ⊤ f) =
      P201.distributionLaplacian (P201.regularDistribution ⊤ g)) : f = g := by
  have htempered : Δ (Lp.toTemperedDistribution f) = Δ (Lp.toTemperedDistribution g) := by
    have htest : ∀ φ : P102.U4.WholeTests n ℂ,
        (Δ (Lp.toTemperedDistribution f)) (P102.U4.testToSchwartz n ℂ φ) =
        (Δ (Lp.toTemperedDistribution g)) (P102.U4.testToSchwartz n ℂ φ) := by
      intro φ
      rw [l2_tempered_laplacian_test, l2_tempered_laplacian_test, hfg]
    have hall := (P102.U4.testToSchwartz_denseRange n ℂ).equalizer
      (Δ (Lp.toTemperedDistribution f)).continuous
      (Δ (Lp.toTemperedDistribution g)).continuous (funext htest)
    ext φ
    exact congrFun hall φ
  have hzero : f - g = 0 := by
    apply l2_eq_zero_of_tempered_laplacian_eq_zero hn
    change Δ ((Lp.toTemperedDistributionCLM ℂ volume 2) (f - g)) = 0
    rw [map_sub, ← TemperedDistribution.laplacianCLM_apply, map_sub]
    apply sub_eq_zero.mpr
    simpa only [TemperedDistribution.laplacianCLM_apply, Lp.toTemperedDistributionCLM_apply] using htempered
  exact sub_eq_zero.mp hzero

/-- The L² Newton Hessian is the pinned Riesz composition. L² harmonic
uniqueness removes every possible zero-frequency error. -/
lemma smoothPotential_hessian_rieszL2 {n : ℕ} (hn : 2 ≤ n)
    (F : P201.Test ℝ (⊤ : P201.Domain n)) (i j : Fin n) :
    let Fc := P102.U4.complexifyTest ⊤ F;
    let Fsch := P102.U4.testToSchwartz n ℂ Fc;
    (P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (Fsch.toLp 2)) :
      P201.Space n → ℂ) =ᵐ[volume]
      fun x => (P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) {i,j} x : ℂ) := by
  let Fc := P102.U4.complexifyTest ⊤ F
  let Fsch := P102.U4.testToSchwartz n ℂ Fc
  let G := P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (Fsch.toLp 2))
  let H : P201.Space n → ℂ :=
    fun x => (P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) {i,j} x : ℂ)
  have hH : MemLp H 2 volume := Complex.ofRealCLM.comp_memLp'
    (smoothPotential_hessian_memLp_two hn F i j)
  let h := hH.toLp H
  have hHreg : P201.regularDistribution (⊤ : P201.Domain n) h =
      P201.regularDistribution ⊤ H :=
    (P102.U4.regular_injectivity n ℂ ⊤ _ _
      (((Lp.memLp h).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      ((hH.locallyIntegrable (by norm_num)).locallyIntegrableOn _)).mpr
      (by simpa using hH.coeFn_toLp)
  have hHpoisson := smoothPotential_complex_derivative_equation (by omega : 1 ≤ n) F {i,j}
  have hGpoisson := rieszComposition_distribution_poisson (by omega : 1 ≤ n) Fc i j
  have heq : h = G := by
    apply l2_eq_of_laplacian_eq (by omega : 1 ≤ n)
    rw [hHreg]
    exact neg_injective (hHpoisson.trans hGpoisson.symm)
  change (G : P201.Space n → ℂ) =ᵐ[volume] H
  rw [← heq]
  exact hH.coeFn_toLp




/-- Full smooth compact-source Hessian identification, with both the complex
Riesz realization and the real distributional derivative. -/
theorem smoothHessian : P201Specs.Elliptic.NewtonLp.SmoothHessianStatement := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    exact dimensionOneSmoothHessian
  have h2n : 2 ≤ n := by omega
  intro p R hR F i j
  let Fc : P201.Space n → ℂ := fun x => (F x : ℂ)
  have hp : MemLp Fc p.val volume :=
    Complex.ofRealCLM.comp_memLp' (F.continuous.memLp_of_hasCompactSupport F.hasCompactSupport)
  have h2 : MemLp Fc 2 volume :=
    Complex.ofRealCLM.comp_memLp' (F.continuous.memLp_of_hasCompactSupport F.hasCompactSupport)
  let Fsch := P102.U4.testToSchwartz n ℂ (P102.U4.complexifyTest ⊤ F)
  have hFsch : Fsch.toLp 2 = h2.toLp Fc := by
    apply Lp.ext
    exact (Fsch.coeFn_toLp 2).trans h2.coeFn_toLp.symm
  have hr := rieszComposition_agrees p R hR Fc hp h2 i j
  have hh := smoothPotential_hessian_rieszL2 h2n F i j
  dsimp only at hh
  rw [hFsch] at hh
  have heq := hr.trans hh
  refine ⟨hp, heq, ?_⟩
  have hre : (fun x => (R i (R j (hp.toLp Fc)) x).re) =ᵐ[volume]
      P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) {i,j} := by
    filter_upwards [heq] with x hx
    exact congrArg Complex.re hx
  have hRmem : MemLp (fun x => (R i (R j (hp.toLp Fc)) x).re) p.val volume :=
    Complex.reCLM.comp_memLp' (Lp.memLp _)
  have hu := P201.newtonSmooth n hn F
  have hHloc : LocallyIntegrable
      (P201.multiPartial (𝕜 := ℝ) (P201.newtonPotential F) {i,j}) volume :=
    (P102.U4.partialWord_contDiff hu _).continuous.locallyIntegrable
  have hreg := (P102.U4.regular_injectivity n ℝ ⊤ _ _
    (hHloc.locallyIntegrableOn _)
    ((hRmem.locallyIntegrable p.one_lt.le).locallyIntegrableOn _)).mpr
      (by simpa using hre.symm)
  change P102.U4.distributionPartial {i,j}
    (P102.U4.regularDistribution ⊤ (P201.newtonPotential F)) = _
  rw [P102.U4.derivative_classicalCompatibility n ℝ ⊤ {i,j} _
    (hu.of_le (by simp)).contDiffOn]
  exact hreg


/-- The actual Newton potential of compactly supported Lᵖ data has the full
local W²ᵖ estimate in every positive dimension, including the logarithmic and
one-dimensional cases. No regularity of the datum beyond Lᵖ is required. -/
theorem potentialEstimate : P201Specs.Elliptic.NewtonLp.PotentialEstimateStatement := by
  intro n hn
  exact potentialEstimate_of_smoothHessian hn (smoothHessian n hn)

end P201.Elliptic.NewtonLp
