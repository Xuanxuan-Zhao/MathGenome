import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.CriticalGNSmooth
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RealAnalysis.D11.Ch10.ElementaryNormInterpolation

noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology ContDiff
namespace P102.Sobolev
open P102.U4
namespace CriticalGNSmooth

/-- Classical Euclidean gradient, with the same coordinates as `weakGradient`. -/
def classicalGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Space d → 𝕜) :
    Space d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i))

/-- Power form of the W¹,¹ estimate followed by Hölder with exponents d and d/(d-1).
This is the analytic iteration step in the critical case, valid for real or complex f. -/
theorem power_step_fderiv {d : ℕ} (hd : 2 ≤ d) {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f)
    (γ : ℝ≥0) (hγ : 1 < γ) :
    eLpNorm f (NNReal.conjExponent d * γ : ℝ≥0) volume ^ (γ : ℝ) ≤
      (eLpNormLESNormFDerivOneConst (volume : Measure (Space d))
        (NNReal.conjExponent d) : ℝ≥0∞) * γ *
        eLpNorm (fderiv ℝ f) (d : ℝ≥0∞) volume *
        eLpNorm f (NNReal.conjExponent d * (γ - 1) : ℝ≥0) volume ^ ((γ : ℝ) - 1) := by
  let : InnerProductSpace ℝ 𝕜 := RCLike.toInnerProductSpaceReal
  let k : ℝ≥0 := NNReal.conjExponent d
  have hd1 : (1 : ℝ≥0) < d := by exact_mod_cast hd
  have hdk : NNReal.HolderConjugate d k := NNReal.HolderConjugate.conjExponent hd1
  have hdim : NNReal.HolderConjugate (Module.finrank ℝ (Space d)) k := by
    simpa [Space] using hdk
  have hγr : 1 < (γ : ℝ) := hγ
  have hγ0 : (γ : ℝ) ≠ 0 := (zero_lt_one.trans hγr).ne'
  have hγsub : (0 : ℝ) < γ - 1 := sub_pos.mpr hγr
  let v : Space d → ℝ := fun x => ‖f x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hf.norm_rpow hγr
  have hsv : HasCompactSupport v := hs.norm.rpow_const hγ0
  have hfcont := hf.continuous
  have hdcont := hf.continuous_fderiv one_ne_zero
  have hfmeas := hf.continuous.aestronglyMeasurable (μ := volume)
  have hdmeas := (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable (μ := volume)
  have hleft : eLpNorm v k volume = eLpNorm f (k * γ : ℝ≥0) volume ^ (γ : ℝ) := by
    simpa only [v, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul] using
      (eLpNorm_norm_rpow (μ := volume) (p := (k : ℝ≥0∞)) f hfmeas (zero_lt_one.trans hγr))
  have hright :
      (∫⁻ x, ‖f x‖ₑ ^ (((γ : ℝ) - 1) * (k : ℝ))) ^ (1 / (k : ℝ)) =
      eLpNorm f (k * (γ - 1) : ℝ≥0) volume ^ ((γ : ℝ) - 1) := by
    have hpow := eLpNorm_norm_rpow (μ := volume) (p := (k : ℝ≥0∞)) f hfmeas hγsub
    have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ ((γ : ℝ) - 1)) volume := by
      fun_prop
    rw [eLpNorm_nnreal_eq_lintegral hdk.symm.pos.ne' hmeas] at hpow
    simp only [Real.enorm_rpow_of_nonneg (norm_nonneg _) hγsub.le,
      enorm_norm] at hpow
    have he : ENNReal.ofReal ((γ : ℝ) - 1) = ((γ - 1 : ℝ≥0) : ℝ≥0∞) := by
      rw [show (γ : ℝ) - 1 = ((γ - 1 : ℝ≥0) : ℝ) by simp [NNReal.coe_sub hγ.le], ENNReal.ofReal_coe_nnreal]
    simpa only [he, ENNReal.coe_mul, ENNReal.rpow_mul] using hpow
  calc
    _ = eLpNorm v k volume := hleft.symm
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure (Space d)) k : ℝ≥0∞) *
        eLpNorm (fderiv ℝ v) 1 volume :=
      eLpNorm_le_eLpNorm_fderiv_one volume hv hsv hdim
    _ = _ * ∫⁻ x, ‖fderiv ℝ v x‖ₑ := by
      rw [eLpNorm_one_eq_lintegral_enorm (hv.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure (Space d)) k : ℝ≥0∞) * γ *
        ∫⁻ x, ‖f x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ f x‖ₑ := by
      rw [mul_assoc, ← lintegral_const_mul γ]
      · gcongr
        simp_rw [← mul_assoc]
        exact enorm_fderiv_norm_rpow_le (hf.differentiable one_ne_zero) hγ
      · dsimp [enorm]
        fun_prop
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure (Space d)) k : ℝ≥0∞) * γ *
        ((∫⁻ x, ‖f x‖ₑ ^ (((γ : ℝ) - 1) * (k : ℝ))) ^ (1 / (k : ℝ)) *
          (∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ (d : ℝ)) ^ (1 / (d : ℝ))) := by
      gcongr
      convert! ENNReal.lintegral_mul_le_Lp_mul_Lq volume hdk.symm.coe ?_ ?_ using 5
      · simp only [ENNReal.rpow_mul]
      · fun_prop
      · fun_prop
    _ = _ := by
      have he := eLpNorm_nnreal_eq_lintegral hdk.pos.ne' hdmeas
      simp only [NNReal.coe_natCast, ENNReal.coe_natCast] at he
      rw [hright, ← he]
      dsimp [k]
      ring

open private norm_linear_le_gradient from MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole

/-- Convert the operator norm in the analytic power step to the source's
Euclidean gradient. The extra dimensional factor is absorbed in the constant. -/
theorem fderiv_norm_le_gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ 1 f) (p : ℝ≥0∞) :
    eLpNorm (fderiv ℝ f) p volume ≤
      (d : ℝ≥0∞) * eLpNorm (classicalGradient f) p volume := by
  simpa only [ENNReal.coe_natCast, ENNReal.smul_def, smul_eq_mul] using
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (c := (d : ℝ≥0)) (μ := volume)
      (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        exact_mod_cast norm_linear_le_gradient (fderiv ℝ f x)) p)

/-- The critical power step with the original Euclidean gradient norm. -/
theorem power_step {d : ℕ} (hd : 2 ≤ d) {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f)
    (γ : ℝ≥0) (hγ : 1 < γ) :
    eLpNorm f (NNReal.conjExponent d * γ : ℝ≥0) volume ^ (γ : ℝ) ≤
      ((eLpNormLESNormFDerivOneConst (volume : Measure (Space d))
        (NNReal.conjExponent d) * d * γ : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume *
        eLpNorm f (NNReal.conjExponent d * (γ - 1) : ℝ≥0) volume ^ ((γ : ℝ) - 1) := by
  apply (power_step_fderiv hd hf hs γ hγ).trans
  calc
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure (Space d))
        (NNReal.conjExponent d) : ℝ≥0∞) * γ *
        ((d : ℝ≥0∞) * eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume) *
        eLpNorm f (NNReal.conjExponent d * (γ - 1) : ℝ≥0) volume ^ ((γ : ℝ) - 1) := by
      gcongr
      exact fderiv_norm_le_gradient hf _
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_natCast]; ring

/-- Absorb the upper norm in a power estimate and a lower-to-upper interpolation
estimate. All constants and powers are ordinary real numbers here. -/
theorem absorb_interpolation {X Y R G A γ b : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hR : 0 < R) (hG : 0 < G) (hA : 0 < A)
    (hγ : 1 < γ) (hb : 0 < b) (hb1 : b < 1)
    (hstep : Y ^ γ ≤ A * G * X ^ (γ - 1))
    (hinterp : X ≤ R ^ (b / (γ - b * (γ - 1))) *
      Y ^ (1 - b / (γ - b * (γ - 1)))) :
    X ≤ A ^ (1 - b) * G ^ (1 - b) * R ^ b := by
  let L := γ - b * (γ - 1)
  have hL : 0 < L := by dsimp [L]; nlinarith
  have hs := Real.log_le_log (Real.rpow_pos_of_pos hY γ) hstep
  rw [Real.log_rpow hY, Real.log_mul (mul_pos hA hG).ne'
    (Real.rpow_pos_of_pos hX _).ne', Real.log_mul hA.ne' hG.ne',
    Real.log_rpow hX] at hs
  have hi := Real.log_le_log hX hinterp
  rw [Real.log_mul (Real.rpow_pos_of_pos hR _).ne'
    (Real.rpow_pos_of_pos hY _).ne', Real.log_rpow hR,
    Real.log_rpow hY] at hi
  change Real.log X ≤ (b / L) * Real.log R + (1 - b / L) * Real.log Y at hi
  have hc : L * (b / L) = b := by field_simp
  have hc' : L * (1 - b / L) = (1 - b) * γ := by
    rw [mul_sub, mul_one, hc]
    dsimp [L]
    ring
  have hi' := mul_le_mul_of_nonneg_left hi hL.le
  rw [mul_add, ← mul_assoc, hc, ← mul_assoc, hc'] at hi'
  have hs' := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hb1.le)
  have hlog : Real.log X ≤ (1 - b) * Real.log A + (1 - b) * Real.log G +
      b * Real.log R := by
    dsimp [L] at hi'
    nlinarith [hi', hs']
  apply (Real.log_le_log_iff hX (by positivity)).mp
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hG _)).ne'
    (Real.rpow_pos_of_pos hR _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hG _).ne',
    Real.log_rpow hA, Real.log_rpow hG, Real.log_rpow hR]
  exact hlog

/-- The classical gradient has a finite norm for compactly supported C¹ functions. -/
theorem classicalGradient_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f)
    (p : ℝ≥0∞) : MemLp (classicalGradient f) p volume := by
  apply ExpandedFA.Sobolev.Subcritical.euclideanTuple_memLp
  intro i
  exact ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hs.fderiv_apply ℝ (coordinateVector d i))

/-- A real reciprocal identity suffices to apply the native norm interpolation API. -/
theorem interpolate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : Continuous f) (r q Q : ℝ≥0)
    (hr : 0 < r) (hq : 0 < q) (hQ : 0 < Q)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (heq : (q : ℝ)⁻¹ = θ / (r : ℝ) + (1 - θ) / (Q : ℝ)) :
    eLpNorm f q volume ≤ eLpNorm f r volume ^ θ * eLpNorm f Q volume ^ (1 - θ) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let : BorelSpace 𝕜 := ⟨rfl⟩
  apply D11.Ch10.ElementaryNormInterpolation.eLpNorm_interpolation volume r q Q θ f hθ hθ1
  · have h := congrArg ENNReal.ofReal heq
    rw [ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < q from hq),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_div_of_pos (show (0 : ℝ) < r from hr),
      ENNReal.ofReal_div_of_pos (show (0 : ℝ) < Q from hQ)] at h
    simpa only [ENNReal.ofReal_coe_nnreal] using h
  · exact hf.measurable

/-- The full smooth critical Gagliardo--Nirenberg bound, including q=r. -/
theorem inequality : CriticalGNSmoothExpected.Inequality := by
  intro d hd r q hr hrq
  have hrpos : (0 : ℝ≥0) < r := lt_of_lt_of_le zero_lt_one hr
  have hqpos : (0 : ℝ≥0) < q := hrpos.trans_le hrq
  by_cases hequal : r = q
  · subst q
    refine ⟨1, ?_⟩
    intro 𝕜 _ f hf hs
    simp [div_self (show (r : ℝ) ≠ 0 from ne_of_gt hrpos)]
  have hrqlt : r < q := lt_of_le_of_ne hrq hequal
  let k : ℝ≥0 := NNReal.conjExponent d
  have hd1 : (1 : ℝ≥0) < d := by exact_mod_cast hd
  have hkpos : 0 < k := (NNReal.HolderConjugate.conjExponent hd1).symm.pos
  let Q : ℝ≥0 := k + q
  let γ : ℝ≥0 := Q / k
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hγ : 1 < γ := by
    dsimp [γ, Q]
    exact (one_lt_div hkpos).mpr (lt_add_of_pos_right k hqpos)
  have hγr : 1 < (γ : ℝ) := hγ
  have hleft : k * γ = Q := by dsimp [γ]; field_simp
  have hright : k * (γ - 1) = q := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_sub hγ.le, NNReal.coe_one]
    change (k : ℝ) * ((Q : ℝ) / k - 1) = q
    dsimp [Q]
    field_simp
    ring
  let b : ℝ := (r : ℝ) / q
  have hb : 0 < b := div_pos hrpos hqpos
  have hb1 : b < 1 := (div_lt_one (show (0 : ℝ) < q from hqpos)).mpr hrqlt
  let L : ℝ := (γ : ℝ) - b * ((γ : ℝ) - 1)
  have hL : 0 < L := by dsimp [L]; nlinarith
  let A : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure (Space d)) k * d * γ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ (1 - b), ?_⟩
  intro 𝕜 _ f hf hs
  change eLpNorm f q volume ≤ ((A ^ (1 - b) : ℝ≥0) : ℝ≥0∞) *
    eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume ^ (1 - b) *
    eLpNorm f r volume ^ b
  by_cases hXzero : eLpNorm f q volume = 0
  · rw [hXzero]; exact bot_le
  have hfinite (p : ℝ≥0∞) : eLpNorm f p volume ≠ ⊤ :=
    (hf.continuous.memLp_of_hasCompactSupport hs).eLpNorm_ne_top
  have hnonzero (p : ℝ≥0) (hp : 0 < p) : eLpNorm f p volume ≠ 0 := by
    intro hz
    exact hXzero (eLpNorm_eq_zero_of_ae_zero ((eLpNorm_eq_zero_iff (by exact_mod_cast hp.ne')).mp hz))
  have hGfin := (classicalGradient_memLp hf hs (d : ℝ≥0∞)).eLpNorm_ne_top
  have hstep : eLpNorm f Q volume ^ (γ : ℝ) ≤ (A : ℝ≥0∞) *
      eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume *
      eLpNorm f q volume ^ ((γ : ℝ) - 1) := by
    have h := power_step hd hf hs γ hγ
    change eLpNorm f (k * γ : ℝ≥0) volume ^ (γ : ℝ) ≤ _ at h
    rw [hleft, hright] at h
    exact h.trans (by gcongr; exact_mod_cast le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 1 from zero_le_one))
  have hGzero : eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume ≠ 0 := by
    intro hz
    rw [hz, mul_zero, zero_mul] at hstep
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr (hnonzero Q hQpos)) (hfinite Q)).ne'
      (le_zero_iff.mp hstep)
  have hθ : 0 < b / L := div_pos hb hL
  have hθ1 : b / L < 1 := by
    apply (div_lt_one hL).mpr
    dsimp [L]
    nlinarith
  have hrreal : (0 : ℝ) < r := hrpos
  have hqreal : (0 : ℝ) < q := hqpos
  have hkreal : (0 : ℝ) < k := hkpos
  have hLform : L = ((Q : ℝ) - r) / k := by
    dsimp [L, b, γ, Q]
    field_simp
    ring
  have hexp : (q : ℝ)⁻¹ = (b / L) / (r : ℝ) + (1 - b / L) / (Q : ℝ) := by
    rw [hLform]
    dsimp [b, Q]
    have hden : (k : ℝ) + q - r ≠ 0 := ne_of_gt (by linarith [show (r : ℝ) < q from hrqlt])
    field_simp [hden]
    ring
  have hi := interpolate hf.continuous r q Q hrpos hqpos hQpos (b / L) hθ hθ1 hexp
  have hsreal := ENNReal.toReal_mono (show (A : ℝ≥0∞) *
      eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume *
      eLpNorm f q volume ^ ((γ : ℝ) - 1) ≠ ⊤ by
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hGfin)
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) (hfinite q))) hstep
  have hireal := ENNReal.toReal_mono (show eLpNorm f r volume ^ (b / L) *
      eLpNorm f Q volume ^ (1 - b / L) ≠ ⊤ by
        exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hθ.le (hfinite r))
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) (hfinite Q))) hi
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] at hsreal hireal
  have hbound := absorb_interpolation
    (ENNReal.toReal_pos hXzero (hfinite q))
    (ENNReal.toReal_pos (hnonzero Q hQpos) (hfinite Q))
    (ENNReal.toReal_pos (hnonzero r hrpos) (hfinite r))
    (ENNReal.toReal_pos hGzero hGfin) hA hγr hb hb1 hsreal hireal
  apply (ENNReal.toReal_le_toReal (hfinite q) (by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hGfin))
      (ENNReal.rpow_ne_top_of_nonneg hb.le (hfinite r)))).mp
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
    NNReal.coe_rpow]
  convert hbound using 1
  rfl

end CriticalGNSmooth
end P102.Sobolev
