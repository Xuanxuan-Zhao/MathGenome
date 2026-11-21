import Mathlib.Analysis.Convolution
import MathGenome.RealAnalysis.Topics.D11.Ch10
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Group.Integral
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.CarlemanNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.LaplaceL2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ExpandedFA.PartIV.CarlemanNorm
open CarlemanNormSpec LaplaceL2Spec

lemma kernel_pos (p x : ℝ) : 0 < kernel p x := by
  exact div_pos (Real.exp_pos _) (by positivity)

lemma kernel_continuous (p : ℝ) : Continuous (kernel p) := by
  unfold kernel
  exact (Real.continuous_exp.comp (continuous_id.div_const p)).div
    (continuous_const.add Real.continuous_exp) (fun x => ne_of_gt (by positivity))

lemma exp_eulerKernel (p x : ℝ) :
    Real.exp x * eulerKernel (1 / p) (Real.exp x) = kernel p x := by
  unfold eulerKernel kernel
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

lemma kernel_integral_substitution (p : ℝ) :
    (∫ x, kernel p x) = ∫ t, eulerKernel (1 / p) t ∂halfLine := by
  simpa only [smul_eq_mul, exp_eulerKernel] using
    (integral_comp_exp (eulerKernel (1 / p)))

lemma kernel_integrable_iff (p : ℝ) :
    Integrable (kernel p) ↔ Integrable (eulerKernel (1 / p)) halfLine := by
  have heq : (fun x => Real.exp x • eulerKernel (1/p) (Real.exp x)) = kernel p := by
    funext x
    exact exp_eulerKernel p x
  rw [← heq]
  exact integrable_comp_exp (eulerKernel (1/p))

lemma kernel_left_bound (p x : ℝ) : kernel p x ≤ Real.exp (x / p) := by
  exact (div_le_iff₀ (by positivity : (0:ℝ) < 1 + Real.exp x)).mpr (by
    nlinarith [Real.exp_pos (x/p), Real.exp_pos x])

lemma kernel_right_bound (p x : ℝ) : kernel p x ≤ Real.exp ((1 / p - 1) * x) := by
  calc
    kernel p x ≤ Real.exp (x / p) / Real.exp x := by
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) (by linarith)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      ring

lemma kernel_integrable {p : ℝ} (hp : 1 < p) : Integrable (kernel p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hleft : IntegrableOn (kernel p) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (a := 1/p) (by positivity) 0).mono'
      (kernel_continuous p).aestronglyMeasurable.restrict
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_pos (kernel_pos _ _), div_eq_mul_inv,
      mul_comm x, one_mul] using kernel_left_bound p x
  have hright : IntegrableOn (kernel p) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a := 1/p-1) (by
      have : 1/p < 1 := (div_lt_one hp0).mpr hp
      linarith) 0).mono' (kernel_continuous p).aestronglyMeasurable.restrict
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_pos (kernel_pos _ _)] using kernel_right_bound p x
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

lemma logarithmic_integrand {𝕜 : Type} [RCLike 𝕜]
    (p x y : ℝ) (f : ℝ → 𝕜) :
    Real.exp (x/p) • (Real.exp y •
      (f (Real.exp y) / RCLike.ofReal (Real.exp x + Real.exp y))) =
      kernel p (x-y) • logTransform p f y := by
  have hden : Real.exp x + Real.exp y ≠ 0 := by positivity
  have hden' : 1 + Real.exp (x-y) ≠ 0 := by positivity
  have hscalar : Real.exp (x/p) * Real.exp y / (Real.exp x + Real.exp y) =
      kernel p (x-y) * Real.exp (y/p) := by
    unfold kernel
    rw [Real.exp_sub, div_mul_eq_mul_div]
    rw [← Real.exp_add ( (x-y)/p) (y/p)]
    rw [show (x-y)/p + y/p = x/p by ring]
    field_simp
    ring
  simp only [logTransform, RCLike.real_smul_eq_coe_mul]
  calc
    _ = RCLike.ofReal (Real.exp (x/p) * Real.exp y /
        (Real.exp x + Real.exp y)) * f (Real.exp y) := by
      simp only [map_div₀, map_mul]
      ring
    _ = _ := by rw [hscalar, RCLike.ofReal_mul]; ring

/-- The exact integral conjugation; no regularity is needed for this identity,
since Bochner integration and the substitution theorem use the same zero
convention for nonintegrable inputs. -/
theorem logarithmic_conjugation : LogarithmicConjugation := by
  intro 𝕜 _ p f
  funext x
  unfold logTransform carlemanIntegral CarlemanNormSpec.convolution
  rw [← integral_comp_exp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact logarithmic_integrand p x y f

/-- Absolute integrability is preserved by the same logarithmic substitution. -/
lemma logarithmic_integrable_iff {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ) (f : ℝ → 𝕜) (x : ℝ) :
    Integrable (fun t => f t / RCLike.ofReal (Real.exp x + t)) halfLine ↔
      Integrable (fun y => kernel p (x-y) • logTransform p f y) := by
  have heq : (fun y => Real.exp (x/p) • (Real.exp y •
      (f (Real.exp y) / RCLike.ofReal (Real.exp x + Real.exp y)))) =
      (fun y => kernel p (x-y) • logTransform p f y) := by
    funext y
    exact logarithmic_integrand p x y f
  rw [← heq, integrable_fun_smul_iff (Real.exp_ne_zero _)]
  exact (integrable_comp_exp (fun t => f t / RCLike.ofReal (Real.exp x+t))).symm

/-- A positive double integral that evaluates Euler's integral using only
real Gamma integrals, avoiding any contour integration. -/
def gammaProductIntegrand (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.2 ^ (a-1) * Real.exp (-((1+z.2)*z.1))

lemma gammaProduct_row (a s t : ℝ) :
    gammaProductIntegrand a (s,t) =
      Real.exp (-s) * (t ^ (a-1) * Real.exp (-(s*t))) := by
  unfold gammaProductIntegrand
  rw [show -((1+t)*s) = -s + -(s*t) by ring, Real.exp_add]
  ring

lemma gammaProduct_row_integrable {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    Integrable (fun t => gammaProductIntegrand a (s,t)) halfLine := by
  simp_rw [gammaProduct_row]
  apply Integrable.const_mul
  change IntegrableOn _ (Ioi (0:ℝ))
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a-1)
      (by linarith) (by norm_num) hs)

lemma gammaProduct_row_integral {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫ t, gammaProductIntegrand a (s,t) ∂halfLine) =
      Real.Gamma a * (Real.exp (-s) * s ^ (-a)) := by
  simp_rw [gammaProduct_row]
  rw [integral_const_mul]
  change Real.exp (-s) * (∫ t in Ioi 0, t ^ (a-1) * Real.exp (-(s*t))) = _
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hs]
  rw [one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
  ring

lemma gammaProduct_column_integral {a t : ℝ} (ht : 0 < t) :
    (∫ s, gammaProductIntegrand a (s,t) ∂halfLine) = eulerKernel a t := by
  unfold gammaProductIntegrand eulerKernel
  dsimp only
  rw [integral_const_mul]
  have he := integral_exp_mul_Ioi (a := -(1+t)) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] at he
  simp_rw [neg_mul_eq_neg_mul]
  change t ^ (a-1) * (∫ s in Ioi 0, Real.exp (-(1+t)*s)) = _
  rw [he, div_eq_mul_inv]

lemma gammaProduct_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Integrable (gammaProductIntegrand a) (halfLine.prod halfLine) := by
  have hm : Measurable (gammaProductIntegrand a) := by
    unfold gammaProductIntegrand
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact gammaProduct_row_integrable ha hs
  · apply ((Real.GammaIntegral_convergent (by linarith : 0 < 1-a)).const_mul
      (Real.Gamma a)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hnorm : (∫ t, ‖gammaProductIntegrand a (s,t)‖ ∂halfLine) =
        ∫ t, gammaProductIntegrand a (s,t) ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply Real.norm_of_nonneg
      change 0 ≤ t ^ (a-1) * Real.exp (-((1+t)*s))
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _)
    rw [hnorm, gammaProduct_row_integral ha hs]
    congr 2
    congr 1
    ring

/-- Euler's integral on the entire range 0<a<1, with absolute integrability. -/
lemma euler_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Integrable (eulerKernel a) halfLine ∧
    (∫ t, eulerKernel a t ∂halfLine) = Real.pi / Real.sin (Real.pi*a) := by
  have hprod := gammaProduct_integrable ha ha1
  have hcol : (fun t => ∫ s, gammaProductIntegrand a (s,t) ∂halfLine) =ᵐ[halfLine]
      eulerKernel a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gammaProduct_column_integral ht
  refine ⟨hprod.integral_prod_right.congr hcol, ?_⟩
  calc
    _ = ∫ t, ∫ s, gammaProductIntegrand a (s,t) ∂halfLine ∂halfLine :=
      (integral_congr_ae hcol).symm
    _ = ∫ s, ∫ t, gammaProductIntegrand a (s,t) ∂halfLine ∂halfLine :=
      (integral_integral_swap (f := fun s t => gammaProductIntegrand a (s,t)) hprod).symm
    _ = ∫ s, Real.Gamma a * (Real.exp (-s) * s ^ (-a)) ∂halfLine := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact gammaProduct_row_integral ha hs
    _ = Real.Gamma a * Real.Gamma (1-a) := by
      rw [integral_const_mul, Real.Gamma_eq_integral (by linarith : 0 < 1-a)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      rw [show 1-a-1 = -a by ring]
    _ = _ := Real.Gamma_mul_Gamma_one_sub a

/-- The exact kernel mass, together with the displayed Euler substitution. -/
theorem kernel_mass : KernelMass := by
  intro p hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ha : 0 < 1/p := by positivity
  have ha1 : 1/p < 1 := (div_lt_one hp0).mpr hp
  obtain ⟨hi, he⟩ := euler_integral ha ha1
  refine ⟨kernel_integrable hp, hi, kernel_integral_substitution p, ?_⟩
  rw [kernel_integral_substitution p, he]
  unfold sharpConstant
  congr 2
  ring

lemma logTransform_inverse {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (g : ℝ → 𝕜) :
    logTransform p (inverseLogTransform p g) = g := by
  funext x
  simp only [logTransform, inverseLogTransform, Real.exp_pos, ↓reduceIte,
    Real.log_exp, smul_smul, Real.rpow_def_of_pos (Real.exp_pos x)]
  rw [← Real.exp_add]
  rw [show x/p + x*(-1/p) = 0 by ring, Real.exp_zero, one_smul]

lemma inverse_logTransform {𝕜 : Type} [RCLike 𝕜] (p : ℝ) (f : ℝ → 𝕜) :
    inverseLogTransform p (logTransform p f) =ᵐ[halfLine] f := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  simp only [inverseLogTransform, ht0, ↓reduceIte, logTransform,
    Real.exp_log ht, smul_smul, Real.rpow_def_of_pos ht]
  rw [← Real.exp_add, show Real.log t * (-1/p) + Real.log t/p = 0 by ring,
    Real.exp_zero, one_smul]

/-- The elementary norm-power identity underlying the Lp isometry. -/
lemma logTransform_norm_rpow {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : p ≠ 0)
    (f : ℝ → 𝕜) (x : ℝ) :
    ‖logTransform p f x‖ ^ p = Real.exp x * ‖f (Real.exp x)‖ ^ p := by
  simp only [logTransform, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.mul_rpow (Real.exp_nonneg _) (norm_nonneg _), ← Real.exp_mul,
    div_mul_cancel₀ _ hp]

lemma integral_logTransform_norm_rpow {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : p ≠ 0)
    (f : ℝ → 𝕜) :
    (∫ x, ‖logTransform p f x‖ ^ p) = ∫ t, ‖f t‖ ^ p ∂halfLine := by
  simp_rw [logTransform_norm_rpow hp]
  exact integral_comp_exp (fun t => ‖f t‖ ^ p)

lemma integrable_logTransform_norm_rpow_iff {𝕜 : Type} [RCLike 𝕜] {p : ℝ}
    (hp : p ≠ 0) (f : ℝ → 𝕜) :
    Integrable (fun x => ‖logTransform p f x‖ ^ p) ↔
      Integrable (fun t => ‖f t‖ ^ p) halfLine := by
  simp_rw [logTransform_norm_rpow hp]
  exact integrable_comp_exp (fun t => ‖f t‖ ^ p)

lemma map_exp_density :
    (volume.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))).map Real.exp =
      halfLine := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg Real.continuous_exp.measurable]
  rw [lintegral_withDensity_eq_lintegral_mul volume (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x)) from by fun_prop) (show Measurable (fun x => g (Real.exp x)) from hg.comp Real.continuous_exp.measurable)]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ, Pi.mul_apply, halfLine] using h.symm

lemma ae_exp_iff (P : ℝ → Prop) :
    (∀ᵐ t ∂halfLine, P t) ↔ ∀ᵐ x ∂volume, P (Real.exp x) := by
  rw [← map_exp_density, Real.isOpenEmbedding_exp.measurableEmbedding.ae_map_iff,
    ae_withDensity_iff (by fun_prop)]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Real.exp_pos, true_implies]

lemma exp_quasiMeasurePreserving : QuasiMeasurePreserving Real.exp volume halfLine := by
  refine ⟨Real.continuous_exp.measurable, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.map_apply Real.continuous_exp.measurable hs]
  have ha : ∀ᵐ t ∂halfLine, t ∉ s := by simpa only [ae_iff, not_not, ofPred_mem_eq, preimage] using hnull
  have hb := (ae_exp_iff (fun t => t ∉ s)).mp ha
  simpa only [ae_iff, not_not, ofPred_mem_eq, preimage] using hb

lemma ae_log (P : ℝ → Prop) (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ t ∂halfLine, P (Real.log t) := by
  apply (ae_exp_iff _).mpr
  simpa only [Real.log_exp] using h

lemma log_quasiMeasurePreserving : QuasiMeasurePreserving Real.log halfLine volume := by
  refine ⟨Real.measurable_log, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.map_apply Real.measurable_log hs]
  have ha : ∀ᵐ x ∂volume, x ∉ s := by simpa only [ae_iff, not_not, ofPred_mem_eq, preimage] using hnull
  have hb := ae_log (fun x => x ∉ s) ha
  simpa only [ae_iff, not_not, ofPred_mem_eq, preimage] using hb
lemma logTransform_aestronglyMeasurable {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ) {f : ℝ → 𝕜} (hf : AEStronglyMeasurable f halfLine) :
    AEStronglyMeasurable (logTransform p f) volume := by
  exact (show AEStronglyMeasurable (fun x : ℝ => Real.exp (x/p)) volume from
    (Real.continuous_exp.comp (continuous_id.div_const p)).aestronglyMeasurable).smul
      (hf.comp_quasiMeasurePreserving exp_quasiMeasurePreserving)

lemma inverseLogTransform_aestronglyMeasurable {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ) {g : ℝ → 𝕜} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (inverseLogTransform p g) halfLine := by
  have hm : AEStronglyMeasurable (fun t : ℝ => t ^ (-1/p) • g (Real.log t)) halfLine :=
    (show AEStronglyMeasurable (fun t : ℝ => t ^ (-1/p)) halfLine from
      (by fun_prop : Measurable (fun t : ℝ => t ^ (-1/p))).aestronglyMeasurable).smul
        (hg.comp_quasiMeasurePreserving log_quasiMeasurePreserving)
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [inverseLogTransform, show 0 < t from ht]

lemma logTransform_memLp {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    {f : ℝ → 𝕜} (hf : MemLp f (ENNReal.ofReal p) halfLine) :
    MemLp (logTransform p f) (ENNReal.ofReal p) volume := by
  apply (integrable_norm_rpow_iff (logTransform_aestronglyMeasurable p hf.aestronglyMeasurable)
    (by positivity) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  apply (integrable_logTransform_norm_rpow_iff hp.ne' f).mpr
  simpa only [ENNReal.toReal_ofReal hp.le] using hf.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top

lemma inverseLogTransform_memLp {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    {g : ℝ → 𝕜} (hg : MemLp g (ENNReal.ofReal p) volume) :
    MemLp (inverseLogTransform p g) (ENNReal.ofReal p) halfLine := by
  apply (integrable_norm_rpow_iff (inverseLogTransform_aestronglyMeasurable p hg.aestronglyMeasurable)
    (by positivity) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  apply (integrable_logTransform_norm_rpow_iff hp.ne' _).mp
  rw [logTransform_inverse]
  simpa only [ENNReal.toReal_ofReal hp.le] using hg.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top

lemma logTransform_lpNorm {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    {f : ℝ → 𝕜} (hf : MemLp f (ENNReal.ofReal p) halfLine) :
    lpNorm (logTransform p f) (ENNReal.ofReal p) volume =
      lpNorm f (ENNReal.ofReal p) halfLine := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (logTransform_aestronglyMeasurable p hf.aestronglyMeasurable),
    lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, integral_logTransform_norm_rpow hp.ne']

lemma logTransform_congr {𝕜 : Type} [RCLike 𝕜] (p : ℝ) {f g : ℝ → 𝕜}
    (h : f =ᵐ[halfLine] g) : logTransform p f =ᵐ[volume] logTransform p g := by
  filter_upwards [exp_quasiMeasurePreserving.ae_eq_comp h] with x hx
  exact congrArg (fun z : 𝕜 => Real.exp (x/p) • z) hx

lemma inverseLogTransform_congr {𝕜 : Type} [RCLike 𝕜] (p : ℝ) {f g : ℝ → 𝕜}
    (h : f =ᵐ[volume] g) :
    inverseLogTransform p f =ᵐ[halfLine] inverseLogTransform p g := by
  filter_upwards [log_quasiMeasurePreserving.ae_eq_comp h] with t ht
  change f (Real.log t) = g (Real.log t) at ht
  simp only [inverseLogTransform, ht]

/-- The logarithmic change of variables, as an isometry of actual Lp classes. -/
def logarithmicLinearIsometry (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] : PositiveLp 𝕜 p →ₗᵢ[𝕜] LineLp 𝕜 p where
  toFun f := (logTransform_memLp hp (Lp.memLp f)).toLp (logTransform p f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(logTransform_memLp hp (Lp.memLp (f+g))).coeFn_toLp,
      Lp.coeFn_add
        ((logTransform_memLp hp (Lp.memLp f)).toLp (logTransform p f))
        ((logTransform_memLp hp (Lp.memLp g)).toLp (logTransform p g)),
      (logTransform_memLp hp (Lp.memLp f)).coeFn_toLp,
      (logTransform_memLp hp (Lp.memLp g)).coeFn_toLp,
      logTransform_congr p (Lp.coeFn_add f g)] with x hx ha hf hg hs
    rw [hx, ha]
    change logTransform p (f+g) x = _ + _
    rw [hf, hg, hs]
    exact smul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(logTransform_memLp hp (Lp.memLp (c • f))).coeFn_toLp,
      Lp.coeFn_smul c ((logTransform_memLp hp (Lp.memLp f)).toLp (logTransform p f)),
      (logTransform_memLp hp (Lp.memLp f)).coeFn_toLp,
      logTransform_congr p (Lp.coeFn_smul c f)] with x hx hc hf hs
    change _ = (c • (logTransform_memLp hp (Lp.memLp f)).toLp _) x
    rw [hx, hc]
    change logTransform p (c • f) x = c • _
    rw [hf, hs]
    exact smul_comm (Real.exp (x/p)) c (f (Real.exp x))
  norm_map' f := by
    change ‖(logTransform_memLp hp (Lp.memLp f)).toLp (logTransform p f)‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact logTransform_lpNorm hp (Lp.memLp f)

lemma logarithmicLinearIsometry_ae (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : PositiveLp 𝕜 p) :
    (logarithmicLinearIsometry 𝕜 hp f : ℝ → 𝕜) =ᵐ[volume] logTransform p f :=
  (logTransform_memLp hp (Lp.memLp f)).coeFn_toLp

lemma logarithmicLinearIsometry_toLp (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 0 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f : ℝ → 𝕜)
    (hf : MemLp f (ENNReal.ofReal p) halfLine) :
    (logarithmicLinearIsometry 𝕜 hp (hf.toLp f) : ℝ → 𝕜) =ᵐ[volume]
      logTransform p f :=
  (logarithmicLinearIsometry_ae 𝕜 hp _).trans (logTransform_congr p hf.coeFn_toLp)

lemma logarithmicLinearIsometry_surjective (𝕜 : Type) [RCLike 𝕜] {p : ℝ}
    (hp : 0 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    Function.Surjective (logarithmicLinearIsometry 𝕜 hp) := by
  intro g
  refine ⟨(inverseLogTransform_memLp hp (Lp.memLp g)).toLp
    (inverseLogTransform p g), ?_⟩
  apply Lp.ext
  have h := logarithmicLinearIsometry_toLp 𝕜 hp _
    (inverseLogTransform_memLp hp (Lp.memLp g))
  simpa only [logTransform_inverse] using h

/-- The original exponential formula and its logarithmic inverse on all
MemLp representatives, including surjectivity. -/
theorem logarithmic_isometry : LogarithmicIsometry := by
  intro 𝕜 _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let U := LinearIsometryEquiv.ofSurjective (logarithmicLinearIsometry 𝕜 hp0)
    (logarithmicLinearIsometry_surjective 𝕜 hp0)
  refine ⟨U, ?_, ?_⟩
  · intro f hf
    exact logarithmicLinearIsometry_toLp 𝕜 hp0 f hf
  · intro g hg
    have hU : (hg.toLp g : ℝ → 𝕜) =ᵐ[volume]
        logTransform p (U.symm (hg.toLp g)) := by
      have hh := logarithmicLinearIsometry_ae 𝕜 hp0 (U.symm (hg.toLp g))
      change (U (U.symm (hg.toLp g)) : ℝ → 𝕜) =ᵐ[volume] _ at hh
      simpa only [U.apply_symm_apply] using hh
    exact (inverse_logTransform p _).symm.trans
      ((inverseLogTransform_congr p hU.symm).trans
        (inverseLogTransform_congr p hg.coeFn_toLp))


lemma carlemanAtExponent_of_convolution (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] (C : ℝ)
    (T : LineLp 𝕜 p →L[𝕜] LineLp 𝕜 p) (hTnorm : ‖T‖ = C)
    (hT : ∀ (g : ℝ → 𝕜) (hg : MemLp g (ENNReal.ofReal p) volume),
      (∀ᵐ x ∂volume, Integrable (fun y => kernel p (x-y) • g y)) ∧
      (T (hg.toLp g) : ℝ → 𝕜) =ᵐ[volume] CarlemanNormSpec.convolution p g) :
    CarlemanAtExponent 𝕜 (ENNReal.ofReal p) C := by
  obtain ⟨U, hU, hUinv⟩ := logarithmic_isometry 𝕜 p hp
  let H : PositiveLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p :=
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp U.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨H, ?_, ?_⟩
  · dsimp only [H]
    change ‖(U.symm : LineLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p).comp
      (T.comp (U : PositiveLp 𝕜 p →L[𝕜] LineLp 𝕜 p))‖ = C
    simpa only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] using hTnorm
  · intro f hf
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    let hg := logTransform_memLp hp0 hf
    have hfU : U (hf.toLp f) = hg.toLp (logTransform p f) := by
      apply Lp.ext
      exact (hU f hf).trans hg.coeFn_toLp.symm
    obtain ⟨hi, hTae⟩ := hT (logTransform p f) hg
    constructor
    · apply (ae_exp_iff _).mpr
      filter_upwards [hi] with x hx
      exact (logarithmic_integrable_iff p f x).mpr hx
    · have hTU : (T (U (hf.toLp f)) : ℝ → 𝕜) =ᵐ[volume]
          logTransform p (carlemanIntegral f) := by
        rw [hfU]
        rw [logarithmic_conjugation p f]
        exact hTae
      have hiU := hUinv (T (U (hf.toLp f))) (Lp.memLp (T (U (hf.toLp f))))
      simp only [Lp.toLp_coeFn] at hiU
      exact hiU.trans ((inverseLogTransform_congr p hTU).trans (inverse_logTransform p _))

lemma convolution_congr_ae {𝕜 : Type} [RCLike 𝕜] (p : ℝ) {f g : ℝ → 𝕜}
    (hfg : f =ᵐ[volume] g) :
    CarlemanNormSpec.convolution p f = CarlemanNormSpec.convolution p g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  exact congrArg (fun z : 𝕜 => kernel p (x-y) • z) hy

lemma reverse_bound_of_convolution
    (hlower : ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ) (hp : 1 < p),
      letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hp.le⟩
      ∀ T : LineLp 𝕜 p →L[𝕜] LineLp 𝕜 p,
        (∀ g : LineLp 𝕜 p, (T g : ℝ → 𝕜) =ᵐ[volume]
          CarlemanNormSpec.convolution p g) → (∫ x, kernel p x) ≤ ‖T‖) :
    ReverseBound := by
  intro 𝕜 _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le⟩
  intro H hH
  obtain ⟨U, hU, hUinv⟩ := logarithmic_isometry 𝕜 p hp
  let T : LineLp 𝕜 p →L[𝕜] LineLp 𝕜 p :=
    U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (H.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hT : ∀ g : LineLp 𝕜 p, (T g : ℝ → 𝕜) =ᵐ[volume]
      CarlemanNormSpec.convolution p g := by
    intro g
    have hHU := hU (H (U.symm g)) (Lp.memLp (H (U.symm g)))
    simp only [Lp.toLp_coeFn] at hHU
    have hHg := logTransform_congr p (hH (U.symm g))
    have hUg := hU (U.symm g) (Lp.memLp (U.symm g))
    simp only [Lp.toLp_coeFn, U.apply_symm_apply] at hUg
    change (U (H (U.symm g)) : ℝ → 𝕜) =ᵐ[volume] _
    refine (hHU.trans hHg).trans ?_
    rw [logarithmic_conjugation p (U.symm g), convolution_congr_ae p hUg.symm]
  have hnorm : ‖T‖ = ‖H‖ := by
    dsimp only [T]
    change ‖(U : PositiveLp 𝕜 p →L[𝕜] LineLp 𝕜 p).comp
      (H.comp (U.symm : LineLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p))‖ = ‖H‖
    simp only [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  rw [← hnorm]
  exact hlower 𝕜 p hp T hT


namespace LineConvolution
set_option maxHeartbeats 0

/-- Real scalar convolution, in the usual order suitable for Minkowski. -/
def lineConvolution {𝕜 : Type} [RCLike 𝕜] (h : ℝ → ℝ) (g : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ y, h y • g (x-y)

lemma young_measurable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {p : ℝ} (hp : 1 ≤ p) {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h)
    {g : ℝ → 𝕜} (gm : Measurable g) (hg : MemLp g (ENNReal.ofReal p) volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => h y • g (x-y))) ∧
      eLpNorm (lineConvolution h g) (ENNReal.ofReal p) volume ≤
        eLpNorm h 1 volume * eLpNorm g (ENNReal.ofReal p) volume := by
  let F : ℝ × ℝ → 𝕜 := fun z => h z.2 • g (z.1-z.2)
  have hF : Measurable F := (hm.comp measurable_snd).smul
    (gm.comp (measurable_fst.sub measurable_snd))
  have hs (y : ℝ) : Specs.D11.Ch10.LpDefinition.powerNorm_value volume p
      (fun x => F (x,y)) = ‖h y‖ₑ * eLpNorm g (ENNReal.ofReal p) volume := by
    erw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm volume p _ hp
      (hF.comp measurable_prodMk_right)]
    change eLpNorm ((h y) • (fun x => g (x-y))) (ENNReal.ofReal p) volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖h y‖ₑ * ·) (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
      (measurePreserving_sub_right volume y))
  have hR : Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value volume
      (fun y => Specs.D11.Ch10.LpDefinition.powerNorm_value volume p (fun x => F (x,y))) =
      eLpNorm h 1 volume * eLpNorm g (ENNReal.ofReal p) volume := by
    have hbridge : Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value volume
        (fun y => Specs.D11.Ch10.LpDefinition.powerNorm_value volume p (fun x => F (x,y))) =
        ∫⁻ y, Specs.D11.Ch10.LpDefinition.powerNorm_value volume p (fun x => F (x,y)) :=
      D11.Ch05.NonnegativeIntegral.integral_eq_lintegral _ _
    rw [hbridge]
    simp_rw [hs]
    rw [lintegral_mul_const _ hm.enorm, ← eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable]
  obtain ⟨_, hiF, _, _, hgF, hb⟩ := D11.Ch10.MinkowskiIntegral.scalar_minkowski
    volume volume inferInstance inferInstance p hp F hF (by
      rw [hR]
      exact ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hi).eLpNorm_lt_top
        hg.eLpNorm_lt_top)
  have hI : Specs.D11.Ch08.Fubini.sectionIntegralLeft_value volume F =
      lineConvolution h g := D11.Ch08.Fubini.sectionIntegralLeft_eq_integral volume F hF
  rw [hI] at hb hgF
  rw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm volume p _ hp hgF.1, hR] at hb
  refine ⟨?_, hb⟩
  apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native _ _).mp at hiF
  exact hiF.mono fun x hx => (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mp hx |>.2

lemma lineConvolution_congr {𝕜 : Type} [RCLike 𝕜] (h : ℝ → ℝ) {g g' : ℝ → 𝕜}
    (hgg : g =ᵐ[volume] g') (x : ℝ) :
    (fun y => h y • g (x-y)) =ᵐ[volume] (fun y => h y • g' (x-y)) :=
  ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hgg).mono
    fun y hy => congrArg (h y • ·) hy

lemma young {𝕜 : Type} [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h)
    {g : ℝ → 𝕜} (hg : MemLp g (ENNReal.ofReal p) volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => h y • g (x-y))) ∧
      MemLp (lineConvolution h g) (ENNReal.ofReal p) volume ∧
      eLpNorm (lineConvolution h g) (ENNReal.ofReal p) volume ≤
        eLpNorm h 1 volume * eLpNorm g (ENNReal.ofReal p) volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let gm := hg.aestronglyMeasurable
  let g' := gm.mk g
  have hgg : g =ᵐ[volume] g' := gm.ae_eq_mk
  have hconv : lineConvolution h g = lineConvolution h g' := funext fun x =>
    integral_congr_ae (lineConvolution_congr h hgg x)
  obtain ⟨hiF, hb⟩ := young_measurable hp hm hi gm.stronglyMeasurable_mk.measurable
    (hg.ae_eq hgg)
  rw [← hconv, eLpNorm_congr_ae hgg.symm] at hb
  have hmeas : AEStronglyMeasurable (lineConvolution h g) volume :=
    hi.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg.aestronglyMeasurable
  refine ⟨hiF.mono fun x hx => (integrable_congr (lineConvolution_congr h hgg x)).mpr hx,
    ?_, hb⟩
  exact hb.trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hi).eLpNorm_lt_top
    hg.eLpNorm_lt_top)


def convolutionLinearMap (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h) :
    Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) →ₗ[𝕜] Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) where
  toFun f := ((young hp hm hi (Lp.memLp f)).2.1).toLp (lineConvolution h f)
  map_add' f g := by
    apply Lp.ext
    let cf := ((young hp hm hi (Lp.memLp f)).2.1).toLp (lineConvolution h f)
    let cg := ((young hp hm hi (Lp.memLp g)).2.1).toLp (lineConvolution h g)
    filter_upwards [((young hp hm hi (Lp.memLp (f+g))).2.1).coeFn_toLp,
      Lp.coeFn_add cf cg, ((young hp hm hi (Lp.memLp f)).2.1).coeFn_toLp,
      ((young hp hm hi (Lp.memLp g)).2.1).coeFn_toLp,
      (young hp hm hi (Lp.memLp f)).1, (young hp hm hi (Lp.memLp g)).1]
      with x hsum hadd hf hg hif hig
    change _ = (cf+cg) x
    rw [hsum, hadd]
    change cf x = lineConvolution h f x at hf
    change cg x = lineConvolution h g x at hg
    change lineConvolution h (f+g) x = cf x + cg x
    rw [hf, hg]
    unfold lineConvolution
    calc
      _ = ∫ y, h y • (f (x-y) + g (x-y)) :=
        integral_congr_ae (lineConvolution_congr h (Lp.coeFn_add f g) x)
      _ = _ := by simp_rw [smul_add]; exact integral_add hif hig
  map_smul' c f := by
    apply Lp.ext
    let cf := ((young hp hm hi (Lp.memLp f)).2.1).toLp (lineConvolution h f)
    filter_upwards [((young hp hm hi (Lp.memLp (c • f))).2.1).coeFn_toLp,
      Lp.coeFn_smul c cf, ((young hp hm hi (Lp.memLp f)).2.1).coeFn_toLp]
      with x hc hs hf
    change _ = (c • cf) x
    rw [hc, hs]
    change cf x = lineConvolution h f x at hf
    change lineConvolution h (c • f) x = c • cf x
    rw [hf]
    unfold lineConvolution
    calc
      _ = ∫ y, h y • (c • f (x-y)) :=
        integral_congr_ae (lineConvolution_congr h (Lp.coeFn_smul c f) x)
      _ = c • ∫ y, h y • f (x-y) := by simp_rw [smul_comm (h _) c]; exact integral_smul c _

lemma convolutionLinearMap_bound (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h)
    (f : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ)) :
    ‖convolutionLinearMap 𝕜 hp hm hi f‖ ≤ (∫ y, ‖h y‖) * ‖f‖ := by
  change ‖((young hp hm hi (Lp.memLp f)).2.1).toLp (lineConvolution h f)‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hi).ne (Lp.memLp f).ne)
    (young hp hm hi (Lp.memLp f)).2.2
  simp only [ENNReal.toReal_mul, toReal_eLpNorm] at hb
  rw [lpNorm_one_eq_integral_norm hi.aestronglyMeasurable] at hb
  exact hb

/-- Convolution by an integrable real scalar kernel as a bounded scalar-linear map. -/
def convolutionOperator (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h) :
    Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) →L[𝕜] Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) :=
  (convolutionLinearMap 𝕜 hp hm hi).mkContinuous (∫ y, ‖h y‖)
    (convolutionLinearMap_bound 𝕜 hp hm hi)

lemma convolutionOperator_ae (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h)
    (f : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ)) :
    (convolutionOperator 𝕜 hp hm hi f : ℝ → 𝕜) =ᵐ[volume] lineConvolution h f :=
  ((young hp hm hi (Lp.memLp f)).2.1).coeFn_toLp

lemma convolutionOperator_norm_le (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ} (hm : Measurable h) (hi : Integrable h) :
    ‖convolutionOperator 𝕜 hp hm hi‖ ≤ ∫ y, ‖h y‖ := by
  apply (convolutionOperator 𝕜 hp hm hi).opNorm_le_bound (integral_nonneg fun _ => norm_nonneg _)
  exact convolutionLinearMap_bound 𝕜 hp hm hi

lemma lineConvolution_swap {𝕜 : Type} [RCLike 𝕜] (h : ℝ → ℝ) (g : ℝ → 𝕜) (x : ℝ) :
    lineConvolution h g x = ∫ y, h (x-y) • g y := by
  rw [lineConvolution, ← integral_sub_left_eq_self (fun y => h (x-y) • g y) volume x]
  simp

lemma lineConvolution_integrable_swap {𝕜 : Type} [RCLike 𝕜] (h : ℝ → ℝ) (g : ℝ → 𝕜) (x : ℝ) :
    Integrable (fun y => h y • g (x-y)) ↔ Integrable (fun y => h (x-y) • g y) := by
  constructor
  · intro hi
    simpa [Function.comp_def] using (volume.measurePreserving_sub_left x).integrable_comp_of_integrable hi
  · intro hi
    simpa [Function.comp_def] using (volume.measurePreserving_sub_left x).integrable_comp_of_integrable hi


/-- Bounded convolution with the absolute integral formula on every Lp representative. -/
theorem exists_convolutionOperator (𝕜 : Type) [RCLike 𝕜] {p : ℝ} (hp : 1 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] {h : ℝ → ℝ}
    (hm : Measurable h) (hi : Integrable h) (hn : ∀ y, 0 ≤ h y) :
    ∃ T : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) →L[𝕜]
        Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ),
      ‖T‖ ≤ ∫ y, h y ∧
      ∀ (g : ℝ → 𝕜) (hg : MemLp g (ENNReal.ofReal p) volume),
        (∀ᵐ x ∂volume, Integrable (fun y => h (x-y) • g y)) ∧
        (T (hg.toLp g) : ℝ → 𝕜) =ᵐ[volume] (fun x => ∫ y, h (x-y) • g y) := by
  refine ⟨convolutionOperator 𝕜 hp hm hi, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _)] using
      convolutionOperator_norm_le 𝕜 hp hm hi
  · intro g hg
    refine ⟨(young hp hm hi hg).1.mono (fun x hx =>
      (lineConvolution_integrable_swap h g x).mp hx), ?_⟩
    have heq : lineConvolution h (hg.toLp g) = lineConvolution h g :=
      funext fun x => integral_congr_ae (lineConvolution_congr h hg.coeFn_toLp x)
    filter_upwards [convolutionOperator_ae 𝕜 hp hm hi (hg.toLp g)] with x hx
    rw [hx, heq, lineConvolution_swap]

end LineConvolution

namespace PositiveConvolution

def exponentialTest (ε x : ℝ) : ℝ := Real.exp (-ε * |x|)
lemma exponentialTest_pos (ε x : ℝ) : 0 < exponentialTest ε x := Real.exp_pos _
lemma exponentialTest_le_one {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : exponentialTest ε x ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (abs_nonneg x))
lemma exponentialTest_continuous (ε : ℝ) : Continuous (exponentialTest ε) := by unfold exponentialTest; fun_prop
lemma integrable_exponentialTest {ε : ℝ} (hε : 0 < ε) : Integrable (exponentialTest ε) := by
  have hl : IntegrableOn (exponentialTest ε) (Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := ε) hε 0
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change x ≤ 0 at hx
    simp only [exponentialTest, abs_of_nonpos hx]
    congr 1
    ring
  have hr : IntegrableOn (exponentialTest ε) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -ε) (by linarith) 0
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [exponentialTest, abs_of_pos hx]
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

lemma memLp_exponentialTest (𝕜 : Type*) [RCLike 𝕜] {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    MemLp (fun x => (exponentialTest ε x : 𝕜)) (ENNReal.ofReal p) volume := by
  apply (integrable_norm_rpow_iff
    ((RCLike.continuous_ofReal.comp (exponentialTest_continuous ε)).aestronglyMeasurable)
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top).mp
  have ht := integrable_exponentialTest (mul_pos hε hp)
  convert ht using 1
  funext x
  simp only [RCLike.norm_ofReal, ENNReal.toReal_ofReal hp.le, exponentialTest,
    abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  ring

lemma exponentialTest_mul_le (ε x y : ℝ) (hε : 0 ≤ ε) :
    exponentialTest ε x * exponentialTest ε y ≤ exponentialTest ε (x-y) := by
  rw [exponentialTest, exponentialTest, exponentialTest, ← Real.exp_add, Real.exp_le_exp]
  have h := abs_sub x y
  nlinarith

lemma integral_weighted_integrable {h : ℝ → ℝ} (hh : Integrable h)
    {ε : ℝ} (hε : 0 ≤ ε) : Integrable (fun x => h x * exponentialTest ε x) := by
  apply hh.mul_bdd (exponentialTest_continuous ε).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_pos (exponentialTest_pos ε x)] using exponentialTest_le_one hε x

lemma convolution_exponentialTest_lower (𝕜 : Type*) [RCLike 𝕜] {h : ℝ → ℝ}
    (hh : Integrable h) (hn : ∀ x, 0 ≤ h x) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    (∫ z, h z * exponentialTest ε z) * exponentialTest ε x ≤
      ‖∫ y, h (x-y) • (exponentialTest ε y : 𝕜)‖ := by
  have hi : Integrable (fun z => h z * exponentialTest ε (x-z)) := by
    apply hh.mul_bdd ((exponentialTest_continuous ε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      simpa only [Function.comp_apply, Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_pos (exponentialTest_pos ε _)] using exponentialTest_le_one hε (x-z)
  have hnint : 0 ≤ ∫ z, h z * exponentialTest ε (x-z) :=
    integral_nonneg fun z => mul_nonneg (hn z) (exponentialTest_pos _ _).le
  have heq : (∫ y, h (x-y) • (exponentialTest ε y : 𝕜)) =
      ((∫ z, h z * exponentialTest ε (x-z) : ℝ) : 𝕜) := by
    simp_rw [RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_mul]
    rw [integral_ofReal]
    congr 1
    convert integral_sub_left_eq_self (fun z => h z * exponentialTest ε (x-z)) volume x using 1
    congr 1
    funext y
    simp only [sub_sub_cancel]
  rw [heq, RCLike.norm_ofReal, abs_of_nonneg hnint]
  rw [← integral_mul_const]
  exact integral_mono ((integral_weighted_integrable hh hε).mul_const _) hi
    fun z => by
      have htest := exponentialTest_mul_le ε x z hε
      calc
        h z * exponentialTest ε z * exponentialTest ε x = h z * (exponentialTest ε x * exponentialTest ε z) := by ring
        _ ≤ h z * exponentialTest ε (x-z) := mul_le_mul_of_nonneg_left htest (hn z)

lemma integral_weighted_le_opNorm (𝕜 : Type*) [RCLike 𝕜] {h : ℝ → ℝ}
    (hh : Integrable h) (hn : ∀ x, 0 ≤ h x) {p : ℝ} (hp : 1 < p)
    {ε : ℝ} (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (T : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) →L[𝕜]
      Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ))
    (hT : ∀ g : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ),
      (T g : ℝ → 𝕜) =ᵐ[volume] fun x => ∫ y, h (x-y) • g y) :
    (∫ z, h z * exponentialTest ε z) ≤ ‖T‖ := by
  let hf := memLp_exponentialTest 𝕜 (by linarith : 0 < p) hε
  let g := hf.toLp (fun x => (exponentialTest ε x : 𝕜))
  let C := ∫ z, h z * exponentialTest ε z
  have hC : 0 ≤ C := integral_nonneg fun z => mul_nonneg (hn z) (exponentialTest_pos _ _).le
  have hg : g ≠ 0 := by
    intro hz
    have htest : (fun x => (exponentialTest ε x : 𝕜)) =ᵐ[volume] (0 : ℝ → 𝕜) := by
      apply hf.coeFn_toLp.symm.trans
      change (g : ℝ → 𝕜) =ᵐ[volume] _
      rw [hz]
      exact Lp.coeFn_zero _ _ _
    obtain ⟨x,hx⟩ := htest.exists
    exact (RCLike.ofReal_ne_zero.mpr (exponentialTest_pos ε x).ne') hx
  have hconv : ∀ x, (∫ y, h (x-y) • g y) = ∫ y, h (x-y) • (exponentialTest ε y : 𝕜) := by
    intro x
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    change g y = (exponentialTest ε y : 𝕜) at hy
    exact congrArg (fun a : 𝕜 => h (x-y) • a) hy
  have hbound : ‖C • g‖ ≤ ‖T g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul C g, hf.coeFn_toLp, hT g] with x hs hgx hTx
    rw [hs, Pi.smul_apply, hgx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC,
      RCLike.norm_ofReal, abs_of_pos (exponentialTest_pos ε x), hTx, hconv]
    exact convolution_exponentialTest_lower 𝕜 hh hn hε.le x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at hbound
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hg)).mp
    (hbound.trans (T.le_opNorm g))

lemma tendsto_weighted_mass {h : ℝ → ℝ} (hh : Integrable h)
    (hn : ∀ x, 0 ≤ h x) :
    Tendsto (fun n : ℕ => ∫ x, h x * exponentialTest (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 (∫ x, h x)) := by
  apply tendsto_integral_of_dominated_convergence h
  · intro n
    exact hh.aestronglyMeasurable.mul (exponentialTest_continuous _).aestronglyMeasurable
  · exact hh
  · intro n
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn x) (exponentialTest_pos _ _).le)]
      exact mul_le_of_le_one_right (hn x) (exponentialTest_le_one (by positivity) x)
  · exact ae_of_all _ fun x => by
      have ht : Tendsto (fun n : ℕ => exponentialTest (1 / ((n : ℝ) + 1)) x) atTop (𝓝 1) := by
        have he := Real.continuous_exp.continuousAt.tendsto.comp
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.mul_const |x|)
        simpa only [exponentialTest, Function.comp_def, neg_zero, zero_mul, Real.exp_zero] using he
      simpa only [mul_one] using tendsto_const_nhds.mul ht

lemma lower_norm (𝕜 : Type*) [RCLike 𝕜] {h : ℝ → ℝ}
    (hh : Integrable h) (hn : ∀ x, 0 ≤ h x) {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (T : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ) →L[𝕜]
      Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ))
    (hT : ∀ g : Lp 𝕜 (ENNReal.ofReal p) (volume : Measure ℝ),
      (T g : ℝ → 𝕜) =ᵐ[volume] fun x => ∫ y, h (x-y) • g y) :
    (∫ z, h z) ≤ ‖T‖ := by
  apply le_of_tendsto (tendsto_weighted_mass hh hn)
  exact Filter.Eventually.of_forall fun n => integral_weighted_le_opNorm 𝕜 hh hn hp (by positivity) T hT

end PositiveConvolution


/-- Every bounded realization of the original Carleman integral obeys the
sharp reverse estimate. -/
theorem reverse_bound : ReverseBound := by
  apply reverse_bound_of_convolution
  intro 𝕜 _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le⟩
  intro T hT
  exact PositiveConvolution.lower_norm 𝕜 (kernel_integrable hp)
    (fun x => (kernel_pos p x).le) hp T hT


/-- The Carleman integral on every interior Lp space has the exact norm
π / sin(π/p), with the original integral formula on every representative. -/
theorem carleman_norm : CarlemanTheorem := by
  intro 𝕜 _ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le⟩
  obtain ⟨T, hupper, hT⟩ := LineConvolution.exists_convolutionOperator 𝕜 hp.le
    (kernel_continuous p).measurable (kernel_integrable hp)
    (fun x => (kernel_pos p x).le)
  have hlower : (∫ x, kernel p x) ≤ ‖T‖ := by
    apply PositiveConvolution.lower_norm 𝕜 (kernel_integrable hp)
      (fun x => (kernel_pos p x).le) hp T
    intro g
    simpa only [Lp.toLp_coeFn] using (hT g (Lp.memLp g)).2
  exact carlemanAtExponent_of_convolution 𝕜 hp (sharpConstant p) T
    ((le_antisymm hupper hlower).trans (kernel_mass p hp).2.2.2) hT

/-- The accepted Laplace operator satisfies the C*-norm identity with its
actual Carleman square. -/
lemma laplace_norm_square (𝕜 : Type) [RCLike 𝕜] :
    ‖LaplaceL2.carlemanOperator 𝕜‖ = ‖LaplaceL2.laplaceOperator 𝕜‖ ^ 2 := by
  have hsym : (LaplaceL2.laplaceOperator 𝕜).IsSymmetric :=
    LaplaceL2.laplace_selfAdjoint 𝕜
  have h := ContinuousLinearMap.norm_adjoint_comp_self (LaplaceL2.laplaceOperator 𝕜)
  rw [hsym.clm_adjoint_eq] at h
  simpa only [LaplaceL2.carlemanOperator, pow_two] using h

/-- Once the interior-p Carleman theorem is available, the final sharp Laplace
assertion follows for the canonical accepted operator, not merely some model. -/
lemma sharp_laplace_of_carleman (hc : CarlemanTheorem) : SharpLaplaceTheorem := by
  intro 𝕜 _
  have h2 := hc 𝕜 2 (by norm_num)
  have hp : ENNReal.ofReal (2:ℝ) = 2 := by norm_num
  simp only [hp] at h2
  unfold CarlemanAtExponent at h2
  obtain ⟨H, hnorm, hae⟩ := h2
  have hH : H = LaplaceL2.carlemanOperator 𝕜 := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    have h := (hae f (Lp.memLp f)).2
    have h' := LaplaceL2.carleman_ae f (Lp.memLp f)
    simp only [Lp.toLp_coeFn] at h h'
    exact h.trans h'.symm
  have hHnorm : ‖LaplaceL2.carlemanOperator 𝕜‖ = Real.pi := by
    rw [← hH, hnorm]
    simp [sharpConstant, Real.sin_pi_div_two]
  have hLnorm : ‖LaplaceL2.laplaceOperator 𝕜‖ = Real.sqrt Real.pi := by
    rw [laplace_norm_square] at hHnorm
    rw [← hHnorm, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨LaplaceL2.laplaceOperator 𝕜, LaplaceL2.carlemanOperator 𝕜,
    hLnorm, hHnorm, LaplaceL2.laplace_selfAdjoint 𝕜, rfl, ?_⟩
  intro f hf
  exact ⟨LaplaceL2.laplace_ae f hf, LaplaceL2.carleman_ae f hf⟩

/-- The sharp L² norm of the actual bounded self-adjoint Laplace transform. -/
theorem sharp_laplace_norm : SharpLaplaceTheorem :=
  sharp_laplace_of_carleman carleman_norm

end ExpandedFA.PartIV.CarlemanNorm
