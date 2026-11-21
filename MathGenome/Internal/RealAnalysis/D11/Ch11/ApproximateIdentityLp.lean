import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ApproximateIdentityLp
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionYoung
import MathGenome.Internal.RealAnalysis.D11.Ch09.LinearJacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Approximate identities, paper.tex:3728. The error estimate is obtained
from scalar Minkowski, and the translation norm is continuous and bounded
by twice the norm of f. Borel versions justify product measurability;
completed linear change of variables and representative independence return
the conclusion to every completed-measurable representative. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch11.ApproximateIdentityLp
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch03.LebesgueMeasures
open ConvolutionBound (convolution)

abbrev scaledKernel : Specs.D11.Ch11.ApproximateIdentityLp.scaledKernel_type :=
  Specs.D11.Ch11.ApproximateIdentityLp.scaledKernel_value

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

omit [NeZero d] in
lemma dilation_det (t : ℝ) (ht : t ≠ 0) :
    LinearMap.det (LinearEquiv.smulOfNeZero ℝ (Point d) t ht).toLinearMap = t ^ d := by
  change LinearMap.det (t • (1 : Point d →ₗ[ℝ] Point d)) = _
  simp [LinearMap.det_smul, finrank_euclideanSpace]

/-- Only scalar Borel functions are composed with joint subtraction. -/
lemma borel_error_measurable [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {φ f : Point d → 𝕜} (hφ : Measurable φ) (hf : Measurable f) (t : ℝ) :
    @Measurable _ _ ((lebesgueSpace_value d).prod (lebesgueSpace_value d)) _
      (fun z : Point d × Point d => φ z.2 * (f (z.1-t • z.2) - f z.1)) := by
  have hi : @Measurable (Point d) (Point d) (lebesgueSpace_value d) _ id :=
    measurable_id'' (native_borel_le d)
  letI : MeasurableSpace (Point d × Point d) :=
    (lebesgueSpace_value d).prod (lebesgueSpace_value d)
  exact (hφ.comp (hi.comp measurable_snd)).mul
    ((hf.comp ((hi.comp measurable_fst).sub ((hi.comp measurable_snd).const_smul t))).sub
      (hf.comp (hi.comp measurable_fst)))

section Completed
local instance : MeasurableSpace (Point d) := lebesgueSpace_value d
local instance : OpensMeasurableSpace (Point d) := ⟨borel_le_lebesgue d⟩

lemma integral_dilation (t : ℝ) (ht : 0 < t) (g : Point d → 𝕜) :
    (∫ z, g (t • z) ∂lebesgue_value d) =
      (t ^ d)⁻¹ • ∫ z, g z ∂lebesgue_value d := by
  let T := LinearEquiv.smulOfNeZero ℝ (Point d) t ht.ne'
  have H := integral_map_equiv (μ := lebesgue_value d)
    (D11.Ch09.LinearJacobian.completedEquiv d T) g
  change (∫ z, g z ∂Measure.map T (lebesgue_value d)) =
    ∫ z, g (T z) ∂lebesgue_value d at H
  have hm : Measure.map T (lebesgue_value d) =
      ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • lebesgue_value d :=
    D11.Ch09.LinearJacobian.map_lebesgue d T
  rw [hm, integral_smul_measure] at H
  simpa only [T, LinearEquiv.smulOfNeZero_apply, dilation_det, abs_of_pos (inv_pos.mpr (pow_pos ht _)),
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (pow_pos ht _)))] using H.symm

lemma integrable_dilation (t : ℝ) (ht : t ≠ 0) (g : Point d → 𝕜) :
    Integrable (fun z => g (t • z)) (lebesgue_value d) ↔ Integrable g (lebesgue_value d) := by
  let T := LinearEquiv.smulOfNeZero ℝ (Point d) t ht
  have H := integrable_map_equiv (μ := lebesgue_value d)
    (D11.Ch09.LinearJacobian.completedEquiv d T) g
  change Integrable g (Measure.map T (lebesgue_value d)) ↔
    Integrable (g ∘ T) (lebesgue_value d) at H
  have hm : Measure.map T (lebesgue_value d) =
      ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • lebesgue_value d :=
    D11.Ch09.LinearJacobian.map_lebesgue d T
  rw [hm] at H
  rw [integrable_smul_measure (by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, abs_pos]
    exact inv_ne_zero (LinearEquiv.isUnit_det' T).ne_zero) ENNReal.ofReal_ne_top] at H
  exact H.symm

lemma scaledKernel_memLp (φ : Point d → 𝕜) (hφ : MemLp φ 1 (lebesgue_value d))
    (t : ℝ) (ht : 0 < t) : MemLp (scaledKernel d φ t) 1 (lebesgue_value d) := by
  apply memLp_one_iff_integrable.mpr
  exact ((integrable_dilation t⁻¹ (inv_ne_zero ht.ne') φ).mpr
    (memLp_one_iff_integrable.mp hφ)).smul ((t ^ d)⁻¹ : ℝ)

lemma scaled_convolution_formula (φ f : Point d → 𝕜) (t : ℝ) (ht : 0 < t)
    (x : Point d) : convolution d (scaledKernel d φ t) f x =
      ∫ z, φ z * f (x-t • z) ∂lebesgue_value d := by
  have H := integral_dilation t ht
    (fun y => scaledKernel d φ t y * f (x-y))
  change (∫ z, ((t ^ d)⁻¹ • φ (t⁻¹ • (t • z))) * f (x-t • z)
    ∂lebesgue_value d) = (t ^ d)⁻¹ • convolution d (scaledKernel d φ t) f x at H
  simp only [inv_smul_smul₀ ht.ne', smul_mul_assoc, integral_smul] at H
  have H' := congrArg (fun v : 𝕜 => (t ^ d) • v) H
  simpa only [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_smul] using H'.symm

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma scaledKernel_measurable {φ : Point d → 𝕜} (hφ : Measurable φ)
    (t : ℝ) (ht : t ≠ 0) : Measurable (scaledKernel d φ t) :=
  (hφ.comp (D11.Ch09.LinearJacobian.completed_measurable d
    (LinearEquiv.smulOfNeZero ℝ (Point d) t⁻¹ (inv_ne_zero ht)))).const_smul _

lemma scaledKernel_congr_ae {φ ψ : Point d → 𝕜} (hφ : φ =ᵐ[lebesgue_value d] ψ)
    (t : ℝ) (ht : t ≠ 0) :
    scaledKernel d φ t =ᵐ[lebesgue_value d] scaledKernel d ψ t := by
  let T := LinearEquiv.smulOfNeZero ℝ (Point d) t⁻¹ (inv_ne_zero ht)
  have hq : QuasiMeasurePreserving T (lebesgue_value d) (lebesgue_value d) := by
    refine ⟨D11.Ch09.LinearJacobian.completed_measurable d T, ?_⟩
    have hm : Measure.map T (lebesgue_value d) =
        ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • lebesgue_value d :=
      D11.Ch09.LinearJacobian.map_lebesgue d T
    rw [hm]
    exact Measure.smul_absolutelyContinuous
  exact (hq.ae hφ).mono fun z hz => congrArg ((t ^ d)⁻¹ • ·) hz

lemma translation_error_continuous (hp : p ≠ ∞) {f : Point d → 𝕜}
    (hf : MemLp f p (lebesgue_value d)) :
    Continuous (fun h : Point d => eLpNorm ((fun x => f (x-h)) - f) p (lebesgue_value d)) := by
  obtain ⟨τ, hτ, hc⟩ := TranslationContinuity.translation_continuity d 𝕜 p hp
  have hcont : Continuous (fun h => τ h (hf.toLp f)) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (hc (hf.toLp f) k)
  have he (h : Point d) :
      eLpNorm ((fun x => f (x-h)) - f) p (lebesgue_value d) =
        ‖τ h (hf.toLp f) - hf.toLp f‖ₑ := by
    obtain ⟨ht, he⟩ := hτ h f hf
    rw [he, ← MemLp.toLp_sub ht hf, Lp.enorm_toLp]
  simpa only [he, Pi.sub_apply] using (hcont.sub continuous_const).enorm

lemma translation_error_le {f : Point d → 𝕜} (hf : MemLp f p (lebesgue_value d))
    (h : Point d) :
    eLpNorm ((fun x => f (x-h)) - f) p (lebesgue_value d) ≤
      2 * eLpNorm f p (lebesgue_value d) := by
  calc
    _ ≤ eLpNorm (fun x => f (x-h)) p (lebesgue_value d) +
        eLpNorm f p (lebesgue_value d) := eLpNorm_sub_le Fact.out
    _ = _ := by
      have H := eLpNorm_comp_measurePreserving (p := p) hf.aestronglyMeasurable
        (TranslationContinuity.measurePreserving_sub_const h)
      change eLpNorm (fun x => f (x-h)) p (lebesgue_value d) = _ at H
      rw [H]
      exact (two_mul _).symm

lemma translation_dominated_convergence (hp : p ≠ ∞) {φ f : Point d → 𝕜}
    (hφ : Measurable φ) (hφ1 : MemLp φ 1 (lebesgue_value d))
    (hf : MemLp f p (lebesgue_value d)) :
    Tendsto (fun t : ℝ => ∫⁻ z, ‖φ z‖ₑ *
      eLpNorm ((fun x => f (x-t • z)) - f) p (lebesgue_value d) ∂lebesgue_value d)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hc := translation_error_continuous hp hf
  have hzero : eLpNorm ((fun x => f (x-(0 : Point d))) - f) p (lebesgue_value d) = 0 := by
    simp
  have hfinite : (∫⁻ z, ‖φ z‖ₑ * (2 * eLpNorm f p (lebesgue_value d))
      ∂lebesgue_value d) ≠ ∞ := by
    rw [lintegral_mul_const _ hφ.enorm, ← eLpNorm_one_eq_lintegral_enorm
      hφ1.aestronglyMeasurable]
    exact (ENNReal.mul_lt_top hφ1 (ENNReal.mul_lt_top (by norm_num) hf)).ne
  have H := tendsto_lintegral_filter_of_dominated_convergence
    (μ := lebesgue_value d) (l := 𝓝 (0 : ℝ)) (f := fun _ => 0)
    (F := fun t z => ‖φ z‖ₑ * eLpNorm ((fun x => f (x-t • z)) - f) p (lebesgue_value d))
    (fun z => ‖φ z‖ₑ * (2 * eLpNorm f p (lebesgue_value d)))
    (Eventually.of_forall fun t => hφ.enorm.mul
      (hc.comp (continuous_id.const_smul t)).measurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun z =>
      mul_le_mul' le_rfl (translation_error_le hf (t • z)))
    hfinite (Eventually.of_forall fun z => ?_)
  · simpa using H
  · have hh : Tendsto (fun t : ℝ =>
        eLpNorm ((fun x => f (x-t • z)) - f) p (lebesgue_value d)) (𝓝 0) (𝓝 0) := by
      have hz := (continuous_id.smul continuous_const :
        Continuous (fun t : ℝ => t • z)).tendsto 0
      change Tendsto (fun t : ℝ => t • z) (𝓝 0) (𝓝 ((0 : ℝ) • z)) at hz
      rw [zero_smul] at hz
      have H := (hc.tendsto 0).comp hz
      change Tendsto (fun t : ℝ => eLpNorm ((fun x => f (x-t • z)) - f)
        p (lebesgue_value d)) (𝓝 0)
        (𝓝 (eLpNorm ((fun x => f (x-0)) - f) p (lebesgue_value d))) at H
      rw [hzero] at H
      exact H
    simpa using ENNReal.Tendsto.const_mul hh (Or.inr (show ‖φ z‖ₑ ≠ ∞ from enorm_ne_top))

/-- Native extended-norm form of the accepted scalar Minkowski inequality. -/
lemma eLpNorm_integral_le (hp : p ≠ ∞) (F : Point d × Point d → 𝕜)
    (hF : Measurable F)
    (hfin : (∫⁻ z, eLpNorm (fun x => F (x,z)) p (lebesgue_value d)
      ∂lebesgue_value d) < ∞) :
    (∀ᵐ x ∂lebesgue_value d, Integrable (fun z => F (x,z)) (lebesgue_value d)) ∧
      eLpNorm (fun x => ∫ z, F (x,z) ∂lebesgue_value d) p (lebesgue_value d) ≤
        ∫⁻ z, eLpNorm (fun x => F (x,z)) p (lebesgue_value d) ∂lebesgue_value d := by
  letI : SigmaFinite (lebesgue_value d) := lebesgue_sigmaFinite d
  have hpR : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr Fact.out
  have hs (z : Point d) : Specs.D11.Ch10.LpDefinition.powerNorm_value
      (lebesgue_value d) p.toReal (fun x => F (x,z)) =
      eLpNorm (fun x => F (x,z)) p (lebesgue_value d) := by
    erw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm _ _ _ hpR
      (hF.comp measurable_prodMk_right), ENNReal.ofReal_toReal hp]
    rfl
  have hR : Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value (lebesgue_value d)
      (fun z => Specs.D11.Ch10.LpDefinition.powerNorm_value (lebesgue_value d)
        p.toReal (fun x => F (x,z))) =
      ∫⁻ z, eLpNorm (fun x => F (x,z)) p (lebesgue_value d) ∂lebesgue_value d := by
    calc
      _ = ∫⁻ z, Specs.D11.Ch10.LpDefinition.powerNorm_value (lebesgue_value d)
          p.toReal (fun x => F (x,z)) ∂lebesgue_value d :=
        D11.Ch05.NonnegativeIntegral.integral_eq_lintegral _ _
      _ = _ := lintegral_congr hs
  obtain ⟨_, hi, _, _, hg, hb⟩ := D11.Ch10.MinkowskiIntegral.scalar_minkowski
    (lebesgue_value d) (lebesgue_value d) inferInstance inferInstance p.toReal hpR F hF
      (by rw [hR]; exact hfin)
  have he : Specs.D11.Ch08.Fubini.sectionIntegralLeft_value (lebesgue_value d) F =
      (fun x => ∫ z, F (x,z) ∂lebesgue_value d) :=
    D11.Ch08.Fubini.sectionIntegralLeft_eq_integral _ _ hF
  rw [he] at hg hb
  rw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm _ _ _ hpR hg.1,
    ENNReal.ofReal_toReal hp, hR] at hb
  refine ⟨?_, hb⟩
  apply (D11.Ch04.AeCommonException.almostEverywhere_iff_native _ _).mp at hi
  exact hi.mono fun x hx => (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mp hx |>.2

lemma error_bound (hp : p ≠ ∞) {φ f : Point d → 𝕜}
    (hφ : Measurable φ) (hφ1 : MemLp φ 1 (lebesgue_value d))
    (hf : MemLp f p (lebesgue_value d)) (t : ℝ) (ht : 0 < t)
    (hF : Measurable (fun z : Point d × Point d => φ z.2 * (f (z.1-t • z.2) - f z.1))) :
    eLpNorm (convolution d f (scaledKernel d φ t) -
        (∫ z, φ z ∂lebesgue_value d) • f) p (lebesgue_value d) ≤
      ∫⁻ z, ‖φ z‖ₑ * eLpNorm ((fun x => f (x-t • z)) - f) p (lebesgue_value d)
        ∂lebesgue_value d := by
  let F : Point d × Point d → 𝕜 := fun z => φ z.2 * (f (z.1-t • z.2) - f z.1)
  have hs (z : Point d) : eLpNorm (fun x => F (x,z)) p (lebesgue_value d) =
      ‖φ z‖ₑ * eLpNorm ((fun x => f (x-t • z)) - f) p (lebesgue_value d) := by
    change eLpNorm ((φ z) • ((fun x => f (x-t • z)) - f)) p (lebesgue_value d) = _
    exact eLpNorm_const_smul (φ z) ((fun x => f (x-t • z)) - f) p (lebesgue_value d)
  have hfin : (∫⁻ z, eLpNorm (fun x => F (x,z)) p (lebesgue_value d)
      ∂lebesgue_value d) < ∞ := by
    calc
      _ ≤ ∫⁻ z, ‖φ z‖ₑ * (2 * eLpNorm f p (lebesgue_value d)) ∂lebesgue_value d := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [hs]
        exact mul_le_mul' le_rfl (translation_error_le hf (t • z))
      _ = eLpNorm φ 1 (lebesgue_value d) * (2 * eLpNorm f p (lebesgue_value d)) := by
        rw [lintegral_mul_const _ hφ.enorm, ← eLpNorm_one_eq_lintegral_enorm
          hφ1.aestronglyMeasurable]
      _ < ∞ := ENNReal.mul_lt_top hφ1 (ENNReal.mul_lt_top (by norm_num) hf)
  obtain ⟨hi, hb⟩ := eLpNorm_integral_le hp F hF hfin
  have he : (fun x => ∫ z, F (x,z) ∂lebesgue_value d) =ᵐ[lebesgue_value d]
      convolution d f (scaledKernel d φ t) - (∫ z, φ z ∂lebesgue_value d) • f := by
    filter_upwards [hi] with x hx
    have hconst := (memLp_one_iff_integrable.mp hφ1).mul_const (f x)
    have hfirst : Integrable (fun z => φ z * f (x-t • z)) (lebesgue_value d) := by
      convert hx.add hconst using 1
      ext z
      dsimp [F]
      ring
    change (∫ z, φ z * (f (x-t • z) - f x) ∂lebesgue_value d) = _
    simp_rw [mul_sub]
    rw [integral_sub hfirst hconst, integral_mul_const,
      ConvolutionYoung.commutative f (scaledKernel d φ t)]
    change _ = convolution d (scaledKernel d φ t) f x - _
    rw [scaled_convolution_formula φ f t ht x]
    rfl
  rw [eLpNorm_congr_ae he] at hb
  exact hb.trans_eq (lintegral_congr hs)

end Completed

/-- Arbitrary real or complex L¹ kernels approximate their integral times f
in every finite Lᵖ norm, on the full completed Lebesgue space. -/
theorem approximate_identity_lp : Specs.D11.Ch11.ApproximateIdentityLp.approximate_identity_lp := by
  intro d _ 𝕜 _ _ _ p _ hp
  letI : MeasurableSpace (Point d) := lebesgueSpace_value d
  letI : OpensMeasurableSpace (Point d) := ⟨borel_le_lebesgue d⟩
  intro φ f hφ hf hφ1 hfp
  constructor
  · intro t ht
    have hk := scaledKernel_memLp φ hφ1 t ht
    refine ⟨hk, ?_⟩
    have H := (ConvolutionYoung.young d 𝕜 p Fact.out (scaledKernel d φ t) f
      (scaledKernel_measurable hφ t ht.ne') hf hk hfp).2.2.1
    change MemLp (convolution d (scaledKernel d φ t) f) p (lebesgue_value d) at H
    rw [ConvolutionYoung.commutative (scaledKernel d φ t) f] at H
    exact H
  · obtain ⟨φB, hφB, heφ⟩ := ConvolutionBound.borel_version φ hφ
    obtain ⟨fB, hfB, hef⟩ := ConvolutionBound.borel_version f hf
    have hφBm : Measurable φB := hφB.mono (native_borel_le d) le_rfl
    have hφB1 := hφ1.ae_eq heφ
    have hfBp := hfp.ae_eq hef
    have hB : Tendsto (fun t : ℝ => eLpNorm
        (convolution d fB (scaledKernel d φB t) -
          (∫ z, φB z ∂lebesgue_value d) • fB) p (lebesgue_value d))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        ((translation_dominated_convergence hp hφBm hφB1 hfBp).mono_left nhdsWithin_le_nhds)
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact error_bound hp hφBm hφB1 hfBp t ht (borel_error_measurable hφB hfB t)
    apply hB.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hk := scaledKernel_congr_ae heφ t (ne_of_gt ht)
    have hconv := (ConvolutionYoung.representative_independence d 𝕜 f fB
      (scaledKernel d φ t) (scaledKernel d φB t) hef hk).2
    have ha : (∫ z, φ z ∂lebesgue_value d) = ∫ z, φB z ∂lebesgue_value d :=
      integral_congr_ae heφ
    exact (eLpNorm_congr_ae ((EventuallyEq.of_eq hconv).sub (by
      rw [ha]
      exact hef.const_smul _))).symm

end D11.Ch11.ApproximateIdentityLp
