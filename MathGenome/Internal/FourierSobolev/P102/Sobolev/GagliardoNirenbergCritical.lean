import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.GagliardoNirenbergCritical
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole
import MathGenome.Internal.FourierSobolev.P102.Sobolev.CriticalGNSmooth
import MathGenome.Internal.FourierSobolev.P102.Sobolev.CriticalGNApproximation
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Batteries.Tactic.OpenPrivate

noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology ContDiff
namespace P102.Sobolev
open P102.U4
namespace CriticalGN

/-- Classical Euclidean gradient, with the same coordinates as `weakGradient`. -/
def classicalGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Space d → 𝕜) :
    Space d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i))

/-- The q=r endpoint has constant one and omits the gradient factor. -/
theorem equal_exponent {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    [Fact (1 ≤ (d : ℝ≥0∞))] (r : ℝ≥0) (hr : 1 ≤ r)
    (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 (d : ℝ≥0∞))
    (hu : MemLp (sobolevUnderlying u) r volume) :
    MemLp (sobolevUnderlying u) r volume ∧
      eLpNorm (sobolevUnderlying u) r volume ≤
        (1 : ℝ≥0∞) * eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^
          (1 - (r : ℝ) / r) *
          eLpNorm (sobolevUnderlying u) r volume ^ ((r : ℝ) / r) := by
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr))
  simpa [div_self hr0] using And.intro hu (le_refl (eLpNorm (sobolevUnderlying u) r volume))

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

/-- Compact smooth estimate used in the passage to Sobolev classes. -/
def SmoothEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (r q : ℝ≥0), 1 ≤ r → r ≤ q →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] (f : Space d → 𝕜),
      ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f q volume ≤ (C : ℝ≥0∞) *
        eLpNorm (classicalGradient f) (d : ℝ≥0∞) volume ^ (1 - (r : ℝ) / q) *
        eLpNorm f r volume ^ ((r : ℝ) / q)

/-- Simultaneous approximation in the two norms needed in the estimate.
Convergence of norms and a.e. convergence suffice for the final Fatou argument.
There is no compact-support assumption on the input Sobolev class. -/
def Approximation : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (r : ℝ≥0), 1 ≤ r →
    ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (d : ℝ≥0∞))]
      (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 (d : ℝ≥0∞)),
      MemLp (sobolevUnderlying u) r volume →
      ∃ f : ℕ → Space d → 𝕜,
        (∀ n, ContDiff ℝ 1 (f n) ∧ HasCompactSupport (f n)) ∧
        (∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (sobolevUnderlying u x))) ∧
        Tendsto (fun n => eLpNorm (classicalGradient (f n)) (d : ℝ≥0∞) volume)
          atTop (𝓝 (eLpNorm (weakGradient u) (d : ℝ≥0∞) volume)) ∧
        Tendsto (fun n => eLpNorm (f n) r volume)
          atTop (𝓝 (eLpNorm (sobolevUnderlying u) r volume))

/-- Complete passage from the smooth estimate and simultaneous approximation
to all Sobolev classes. -/
theorem inequality_of_smooth_of_approximation
    (smooth : SmoothEstimate) (approximation : Approximation) :
    GagliardoNirenbergCriticalExpected.Inequality := by
  intro d hd r q hr hrq
  obtain ⟨C, hC⟩ := smooth d hd r q hr hrq
  refine ⟨C, ?_⟩
  intro 𝕜 _ _ u hu
  obtain ⟨f, hf, hae, hgrad, hrnorm⟩ := approximation d hd r hr 𝕜 u hu
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr.trans hrq)
  have ha : 0 ≤ 1 - (r : ℝ) / q := sub_nonneg.mpr ((div_le_one hqpos).mpr (by exact_mod_cast hrq))
  have hb : 0 ≤ (r : ℝ) / q := div_nonneg r.coe_nonneg q.coe_nonneg
  have hg := weakGradient_memLp u
  have hgfin : eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^ (1 - (r : ℝ) / q) ≠ ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg ha hg.eLpNorm_ne_top |>.ne
  have hrfin : eLpNorm (sobolevUnderlying u) r volume ^ ((r : ℝ) / q) ≠ ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hb hu.eLpNorm_ne_top |>.ne
  have hlimit : Tendsto (fun n => (C : ℝ≥0∞) *
      eLpNorm (classicalGradient (f n)) (d : ℝ≥0∞) volume ^ (1 - (r : ℝ) / q) *
      eLpNorm (f n) r volume ^ ((r : ℝ) / q)) atTop
      (𝓝 ((C : ℝ≥0∞) * eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^
        (1 - (r : ℝ) / q) * eLpNorm (sobolevUnderlying u) r volume ^ ((r : ℝ) / q))) :=
    ENNReal.Tendsto.mul
      (ENNReal.Tendsto.const_mul (hgrad.ennrpow_const (1 - (r : ℝ) / q))
        (Or.inr ENNReal.coe_ne_top))
      (Or.inr hrfin)
      (hrnorm.ennrpow_const ((r : ℝ) / q))
      (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top hgfin))
  have hbound : eLpNorm (sobolevUnderlying u) q volume ≤
      (C : ℝ≥0∞) * eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^
        (1 - (r : ℝ) / q) *
        eLpNorm (sobolevUnderlying u) r volume ^ ((r : ℝ) / q) := by
    exact ExpandedFA.Sobolev.Subcritical.eLpNorm_le_of_ae_tendsto_bounds
      (fun n => (hf n).1.continuous.aestronglyMeasurable)
      hu.aestronglyMeasurable hae hlimit
      (fun n => hC 𝕜 (f n) (hf n).1 (hf n).2)
  refine ⟨hbound.trans_lt ?_, hbound⟩
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.mpr hgfin))
    (lt_top_iff_ne_top.mpr hrfin)

/-- The upstream compact estimate uses exactly the same classical gradient. -/
theorem smoothEstimate : SmoothEstimate :=
  CriticalGNSmooth.inequality

/-- The simultaneous approximation controls both norms and the representative
needed for Fatou, without a support assumption on the Sobolev function. -/
theorem approximation : Approximation :=
  CriticalGNApproximation.approximation

end CriticalGN

/-- Critical whole-space Gagliardo--Nirenberg inequality for every finite
1 ≤ r ≤ q, with the gradient factor omitted when q = r. -/
theorem gagliardoNirenbergCritical : GagliardoNirenbergCriticalExpected.Inequality :=
  CriticalGN.inequality_of_smooth_of_approximation
    CriticalGN.smoothEstimate CriticalGN.approximation

end P102.Sobolev
