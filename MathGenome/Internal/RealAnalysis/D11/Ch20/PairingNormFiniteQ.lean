import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.PairingNormFiniteQ
import MathGenome.Internal.RealAnalysis.D11.Ch20.IntegralPairing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch20.PairingNormFiniteQ

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]

/-- Conjugate phase, zero at zero, for the bilinear integral pairing. -/
def conjugatePhase (z : 𝕜) : 𝕜 := star z / (‖z‖ : 𝕜)

lemma norm_conjugatePhase_le (z : 𝕜) : ‖conjugatePhase z‖ ≤ 1 := by
  simp only [conjugatePhase, norm_div, norm_star, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self_le_one ‖z‖

lemma norm_conjugatePhase (z : 𝕜) (hz : z ≠ 0) : ‖conjugatePhase z‖ = 1 := by
  simp [conjugatePhase, norm_div, norm_ne_zero_iff.mpr hz]

lemma conjugatePhase_mul (z : 𝕜) : conjugatePhase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz, conjugatePhase]
  · have hn : (‖z‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    change (starRingEnd 𝕜) z / (‖z‖ : 𝕜) * z = (‖z‖ : 𝕜)
    rw [div_mul_eq_mul_div, RCLike.conj_mul, pow_two, mul_div_cancel_right₀ _ hn]

lemma aestronglyMeasurable_conjugatePhase {μ : Measure X} {g : X → 𝕜}
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => conjugatePhase (g x)) μ := by
  exact (continuous_star.comp_aestronglyMeasurable hg).div₀
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable hg.norm)

lemma norm_pairing_one (μ : Measure X) (g : Lp 𝕜 1 μ) :
    ‖IntegralPairing.pairing μ ∞ 1 g‖ = ‖g‖ := by
  apply le_antisymm (IntegralPairing.pairing_norm_bound μ ∞ 1 g)
  let f : X → 𝕜 := fun x => conjugatePhase (g x)
  have hf : MemLp f ∞ μ := memLp_top_of_bound
    (aestronglyMeasurable_conjugatePhase (Lp.aestronglyMeasurable g)) 1
    (Filter.Eventually.of_forall fun x => norm_conjugatePhase_le (g x))
  have hfn : ‖hf.toLp f‖ ≤ 1 := by
    rw [Lp.norm_toLp]
    apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.one_ne_top).mpr
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
    simpa using eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall fun x => norm_conjugatePhase_le (g x))
  have hval : IntegralPairing.pairing μ ∞ 1 g (hf.toLp f) = (‖g‖ : 𝕜) := by
    calc
      _ = ∫ x, (hf.toLp f) x * g x ∂μ :=
        (IntegralPairing.pairing_eq_integral μ ∞ 1 g (hf.toLp f)).2
      _ = ∫ x, (‖g x‖ : 𝕜) ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hf] with x hx
        rw [hx]
        exact conjugatePhase_mul (g x)
      _ = (‖g‖ : 𝕜) := by rw [integral_ofReal, L1.norm_eq_integral_norm]
  have h := (IntegralPairing.pairing μ ∞ 1 g).le_opNorm (hf.toLp f)
  rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg g)] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hfn)

/-- The unnormalized power test for a finite dual exponent greater than one. -/
def powerTest (r : ℝ) (z : 𝕜) : 𝕜 := conjugatePhase z * (‖z‖ ^ r : ℝ)

lemma norm_powerTest (r : ℝ) (hr : 0 < r) (z : 𝕜) :
    ‖powerTest r z‖ = ‖z‖ ^ r := by
  by_cases hz : z = 0
  · simp [powerTest, conjugatePhase, hz, Real.zero_rpow hr.ne']
  · rw [powerTest, norm_mul, norm_conjugatePhase z hz, one_mul,
      RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

lemma powerTest_mul (r : ℝ) (hr : 0 < r) (z : 𝕜) :
    powerTest r z * z = (‖z‖ ^ (r + 1) : ℝ) := by
  rw [powerTest, mul_right_comm, conjugatePhase_mul, ← RCLike.ofReal_mul]
  congr 1
  rw [Real.rpow_add_one' (norm_nonneg _) (by linarith : r + 1 ≠ 0), mul_comm]

lemma aestronglyMeasurable_powerTest {μ : Measure X} {g : X → 𝕜}
    (hg : AEStronglyMeasurable g μ) (r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (fun x => powerTest r (g x)) μ := by
  exact (aestronglyMeasurable_conjugatePhase hg).mul
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable
      ((Real.continuous_rpow_const hr.le).comp_aestronglyMeasurable hg.norm))

/-- The conjugacy identity in the form required by the power-norm formula. -/
lemma conjugate_power_exponent (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q]
    (hq : q ≠ ∞) (hq1 : q ≠ 1) :
    0 < q.toReal - 1 ∧ p * ENNReal.ofReal (q.toReal - 1) = q := by
  have hp : p ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq1
  have hp0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 := ENNReal.HolderConjugate.ne_zero q p
  have hqgt : 1 < q := lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) (Ne.symm hq1)
  have hqr : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hq).mpr hqgt
  have hpr0 : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  have hqr0 : q.toReal ≠ 0 := (ENNReal.toReal_pos hq0 hq).ne'
  have hi : p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
    have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h
    exact h
  have he : p.toReal * (q.toReal - 1) = q.toReal := by
    field_simp at hi
    nlinarith
  refine ⟨by linarith, ?_⟩
  rw [← ENNReal.ofReal_toReal (a := p) hp, ← ENNReal.ofReal_mul (ENNReal.toReal_nonneg)]
  rw [he, ENNReal.ofReal_toReal hq]

lemma integral_norm_power (μ : Measure X) (q : ℝ≥0∞) (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (g : Lp 𝕜 q μ) : ∫ x, ‖g x‖ ^ q.toReal ∂μ = ‖g‖ ^ q.toReal := by
  have hI : 0 ≤ ∫ x, ‖g x‖ ^ q.toReal ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hn : ‖g‖ = (∫ x, ‖g x‖ ^ q.toReal ∂μ) ^ q.toReal⁻¹ := by
    rw [Lp.norm_def, (Lp.memLp g).eLpNorm_eq_integral_rpow_norm hq0 hq,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  rw [hn, Real.rpow_inv_rpow hI (ENNReal.toReal_pos hq0 hq).ne']

lemma norm_pairing_gt_one (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hq : q ≠ ∞) (hq1 : q ≠ 1) (g : Lp 𝕜 q μ) :
    ‖IntegralPairing.pairing μ p q g‖ = ‖g‖ := by
  apply le_antisymm (IntegralPairing.pairing_norm_bound μ p q g)
  by_cases hg : g = 0
  · simp [hg]
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  obtain ⟨hr, hexp⟩ := conjugate_power_exponent p q hq hq1
  let r : ℝ := q.toReal - 1
  let f : X → 𝕜 := fun x => powerTest r (g x)
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_powerTest (Lp.aestronglyMeasurable g) r hr
  have hnorm : eLpNorm f p μ = eLpNorm (fun x => g x) q μ ^ r := by
    calc
      _ = eLpNorm (fun x => ‖g x‖ ^ r) p μ := by
        apply eLpNorm_congr_norm_ae hfm
          ((Real.continuous_rpow_const hr.le).comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable g).norm)
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          exact norm_powerTest r hr (g x)
      _ = eLpNorm (fun x => g x) q μ ^ r := by
        rw [eLpNorm_norm_rpow _ (Lp.aestronglyMeasurable g) hr, hexp]
  have hf : MemLp f p μ := by
    rw [memLp_iff, hnorm]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le (Lp.memLp g).eLpNorm_ne_top
  have hfn : ‖hf.toLp f‖ = ‖g‖ ^ r := by
    rw [Lp.norm_toLp, hnorm, ← ENNReal.toReal_rpow, Lp.norm_def]
  have hval : IntegralPairing.pairing μ p q g (hf.toLp f) = (‖g‖ ^ q.toReal : ℝ) := by
    calc
      _ = ∫ x, (hf.toLp f) x * g x ∂μ :=
        (IntegralPairing.pairing_eq_integral μ p q g (hf.toLp f)).2
      _ = ∫ x, ((‖g x‖ ^ q.toReal : ℝ) : 𝕜) ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hf] with x hx
        rw [hx]
        simpa only [f, r, sub_add_cancel] using powerTest_mul r hr (g x)
      _ = (‖g‖ ^ q.toReal : ℝ) := by
        rw [integral_ofReal, integral_norm_power μ q (ENNReal.HolderConjugate.ne_zero q p) hq g]
  have h := (IntegralPairing.pairing μ p q g).le_opNorm (hf.toLp f)
  rw [hval, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hfn] at h
  have hpow : ‖g‖ ^ q.toReal = ‖g‖ * ‖g‖ ^ r := by
    dsimp [r]
    rw [Real.rpow_sub_one hgn.ne', mul_div_cancel₀ _ hgn.ne']
  rw [hpow] at h
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hgn r)).mp h

/-- On an arbitrary positive measure, every finite dual exponent gives exact
operator norm, including L¹ paired with ordinary L∞. -/
theorem norm_pairing : Specs.D11.Ch20.PairingNormFiniteQ.norm_pairing := by
  intro X 𝕜 _ _ μ p q _ _ _ hq g
  change ‖IntegralPairing.pairing μ p q g‖ = ‖g‖
  by_cases hq1 : q = 1
  · subst q
    have hp : p = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).mpr rfl
    subst p
    exact norm_pairing_one μ g
  · exact norm_pairing_gt_one μ p q hq hq1 g

/-- Scalar linearity comes from the upstream pairing; norm preservation makes
that same map an isometry, hence an injection into the continuous dual. -/
theorem isometric_injection : Specs.D11.Ch20.PairingNormFiniteQ.isometric_injection := by
  intro X 𝕜 _ _ μ p q _ _ _ hq
  have h : Isometry (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q) :=
    AddMonoidHomClass.isometry_of_norm
      (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q)
      (norm_pairing μ p q hq)
  exact ⟨h, h.injective⟩

end D11.Ch20.PairingNormFiniteQ
