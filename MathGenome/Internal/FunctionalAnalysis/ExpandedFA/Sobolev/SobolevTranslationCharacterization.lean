import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open MeasureTheory Set TopologicalSpace Filter Metric
open scoped ENNReal Topology Convolution

namespace ExpandedFA.Sobolev.Translation
open ExpandedFA.Distributions

@[simp] theorem natIndex_firstIndex {d : ℕ} (j : Fin d) :
    natIndex (firstIndex j) = fun i => if i = j then 1 else 0 := rfl

@[simp] theorem euclideanLength_zero (d : ℕ) :
    euclideanLength (0 : Domain d) = 0 := by simp [euclideanLength]

@[simp] theorem euclideanLength_neg {d : ℕ} (h : Domain d) :
    euclideanLength (-h) = euclideanLength h := by
  change ‖-(WithLp.toLp 2 h)‖ = ‖WithLp.toLp 2 h‖
  exact norm_neg _

/-- Sharp finite-dimensional Cauchy--Schwarz estimate for a real-linear
scalar map, with Euclidean norms on both coordinate vectors. -/
theorem norm_apply_le_euclidean {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (A : Domain d →L[ℝ] 𝕜) (h : Domain d) :
    ‖A h‖ ≤ euclideanLength h *
      ‖WithLp.toLp 2 (fun j => A (coordinateVector j))‖ := by
  have hh : h = ∑ j, h j • coordinateVector j := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  calc
    ‖A h‖ = ‖∑ j, h j • A (coordinateVector j)‖ := by
      conv_lhs => rw [hh, map_sum]
      simp
    _ ≤ ∑ j, ‖h j • A (coordinateVector j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖h j‖ * ‖A (coordinateVector j)‖ := by simp [norm_smul]
    _ ≤ Real.sqrt (∑ j, ‖h j‖ ^ 2) *
        Real.sqrt (∑ j, ‖A (coordinateVector j)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp [euclideanLength, PiLp.norm_eq_of_L2]

/-- A smooth function whose Euclidean gradient is bounded has the sharp
pointwise translation bound. This is the smooth L-infinity step. -/
theorem smooth_translation_bound_of_gradient_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain d → 𝕜) (hf : Differentiable ℝ f) (M : ℝ)
    (hM : ∀ y, ‖WithLp.toLp 2 (fun j => fderiv ℝ f y (coordinateVector j))‖ ≤ M)
    (x h : Domain d) : ‖f (x+h) - f x‖ ≤ euclideanLength h * M := by
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • h))
      (fderiv ℝ f (x + t • h) h) t := by
    convert (hf (x + t • h)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h)) using 1
    · rfl
    · simp
  have hb (t : ℝ) : ‖fderiv ℝ f (x + t • h) h‖ ≤ euclideanLength h * M :=
    (norm_apply_le_euclidean _ h).trans
      (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => hb t)
  simpa using hm

/-- The sharp finite-p estimate for a C¹ scalar function.  Minkowski is
applied on the probability interval [0,1], keeping the Euclidean gradient
inside its Lp norm. -/
theorem smooth_translation_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain d → 𝕜) (hf : ContDiff ℝ 1 f)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hg : MemLp (fun y => WithLp.toLp 2
      (fun j => fderiv ℝ f y (coordinateVector j))) p volume) (h : Domain d) :
    eLpNorm (fun x => f (x+h) - f x) p volume ≤
      ENNReal.ofReal (euclideanLength h) * eLpNorm
        (fun y => WithLp.toLp 2 (fun j => fderiv ℝ f y (coordinateVector j))) p volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let G := fun y => WithLp.toLp 2 (fun j => fderiv ℝ f y (coordinateVector j))
  let F : Domain d × ℝ → 𝕜 := fun z => fderiv ℝ f (z.1 + z.2 • h) h
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hF : Continuous F :=
    (hc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hs (t : ℝ) : eLpNorm (fun x => F (x,t)) p volume ≤
      ENNReal.ofReal (euclideanLength h) * eLpNorm G p volume := by
    calc
      _ ≤ ENNReal.ofReal (euclideanLength h) *
          eLpNorm (fun x => G (x + t • h)) p volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun x => norm_apply_le_euclidean _ _) p
      _ = _ := congrArg (ENNReal.ofReal (euclideanLength h) * ·)
        (eLpNorm_comp_measurePreserving (g := G) hg.aestronglyMeasurable
          (measurePreserving_add_right volume (t • h)))
  have hR : (∫⁻ t in Ioc (0 : ℝ) 1, eLpNorm (fun x => F (x,t)) p volume) ≤
      ENNReal.ofReal (euclideanLength h) * eLpNorm G p volume := by
    calc
      _ ≤ ∫⁻ _t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (euclideanLength h) * eLpNorm G p volume := lintegral_mono hs
      _ = _ := by simp
  have hfin : (∫⁻ t in Ioc (0 : ℝ) 1, eLpNorm (fun x => F (x,t)) p volume) < ∞ :=
    hR.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)
  obtain ⟨_, hb⟩ := minkowski_integral_eLpNorm volume (volume.restrict (Ioc (0 : ℝ) 1))
    p hp hpt F hF.measurable hfin
  have hid (x : Domain d) : (∫ t in Ioc (0 : ℝ) 1, F (x,t)) = f (x+h) - f x := by
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • h)) (F (x,t)) t := by
      convert (hf.differentiable (by simp) (x + t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h)) using 1
      · rfl
      · simp [F]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
  simpa only [hid] using hb.trans hR

/-- Convolution by a nonnegative probability kernel contracts the Lp norm
of a vector-valued function, including the Euclidean gradient. -/
theorem eLpNorm_convolution_probability_le {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {d : ℕ}
    (K : Domain d → ℝ) (hK : Continuous K) (hcK : HasCompactSupport K)
    (hnK : ∀ y, 0 ≤ K y) (hiK : ∫ y, K y = 1)
    (G : Domain d → E) (p : ℝ≥0∞) (hp : 1 ≤ p) (hG : MemLp G p volume) :
    eLpNorm (convolution K G (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm G p volume := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hi : ConvolutionExists K G L volume := by
    intro x
    exact (convolutionExistsAt_flip (L := L)).mp
      (hcK.convolutionExists_right L.flip (hG.locallyIntegrable hp) hK x)
  have hnorm (x : Domain d) : ‖convolution K G L volume x‖ ≤
      ConvolutionEndpointBoundsSpec.ConvolutionValue K (fun y => ‖G y‖) x := by
    calc
      _ ≤ ∫ y, ‖K y • G (x-y)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by simp [norm_smul, Real.norm_of_nonneg (hnK y)]
  have hKm : MemLp K 1 volume := memLp_one_iff_integrable.mpr
    (hK.integrable_of_hasCompactSupport hcK)
  have hKn : eLpNorm K 1 volume = 1 := by
    rw [eLpNorm_one_eq_lintegral_enorm hKm.aestronglyMeasurable]
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (hnK _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (memLp_one_iff_integrable.mp hKm)
      (Eventually.of_forall hnK), hiK, ENNReal.ofReal_one]
  calc
    _ ≤ eLpNorm (ConvolutionEndpointBoundsSpec.ConvolutionValue K (fun y => ‖G y‖)) p volume :=
      eLpNorm_mono_real (hK.aestronglyMeasurable.convolution L hG.aestronglyMeasurable) hnorm
    _ ≤ eLpNorm K 1 volume * eLpNorm (fun y => ‖G y‖) p volume :=
      (young_l1_lp_endpoint p hp K (fun y => ‖G y‖) hKm hG.norm).2.2.2
    _ = _ := by rw [hKn, one_mul, eLpNorm_norm G hG.aestronglyMeasurable]

/-- The forward assertion retains the zero-dimensional case. -/
theorem forward_estimate_zero_dimension (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevSpace 𝕜 0 (⊤ : Opens (Domain 0)) 1 p) (h : Domain 0) :
    eLpNorm (fun x => u.val (zeroIndex 0 1) (x+h) - u.val (zeroIndex 0 1) x)
      p volume ≤ ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) p volume := by
  have hh : h = 0 := Subsingleton.elim _ _
  rw [hh, euclideanLength_zero]
  simp only [add_zero, sub_self, eLpNorm_fun_zero, ENNReal.ofReal_zero, zero_mul, le_refl]

/-- Every Lp class in dimension zero belongs to W^{1,p}; the coordinate
bounds in the converse are vacuous, even for a negative proposed constant. -/
theorem converse_zero_dimension (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Domain 0)) p) (C : ℝ) :
    ∃ v : SobolevSpace 𝕜 0 (⊤ : Opens (Domain 0)) 1 p,
      v.val (zeroIndex 0 1) = u ∧ ∀ j : Fin 0, ‖v.val (firstIndex j)‖ ≤ C := by
  let v : SobolevSpace 𝕜 0 (⊤ : Opens (Domain 0)) 1 p :=
    ⟨WithLp.toLp 1 (fun _ => u), by
      intro α
      change lpDistribution u =
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 0 ⊤ (natIndex α) (lpDistribution u)
      have hα : natIndex α = fun _ => 0 := Subsingleton.elim _ _
      rw [hα, derivative_zero]⟩
  exact ⟨v, rfl, fun j => Fin.elim0 j⟩

/-- The explicit endpoint example is an ordinary L1 function. -/
theorem intervalIndicator_memLp : MemLp intervalIndicator 1 volume := by
  apply memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet 1
  right
  simp

/-- The coordinate multi-index represents exactly one coordinate derivative. -/
@[simp] theorem multiIndexWord_firstIndex {d : ℕ} (j : Fin d) :
    multiIndexWord (natIndex (firstIndex j)) = [j] := by
  have hl : (multiIndexWord (natIndex (firstIndex j))).length = 1 := by simp
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hl
  have hc := multiIndexWord_count (natIndex (firstIndex j)) j
  rw [hi, natIndex_firstIndex] at hc
  have hij : i = j := by
    by_contra hij
    simp [hij] at hc
  simpa [hij] using hi

/-- The accepted derivative graph implies the usual integration-by-parts
identity for every first coordinate. -/
theorem first_weakDerivative_test_identity {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SobolevSpace 𝕜 d (⊤ : Opens (Domain d)) 1 p) (j : Fin d)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    (∫ x, φ x * u.val (firstIndex j) x) =
      -(∫ x, testPartialCLM [j] φ x * u.val (zeroIndex d 1) x) := by
  have heq := congrArg (fun T : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) => T φ)
    (u.property (firstIndex j))
  change lpDistribution (u.val (firstIndex j)) φ =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d ⊤ (natIndex (firstIndex j))
        (lpDistribution (u.val (zeroIndex d 1))) φ at heq
  unfold Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue at heq
  rw [multiIndexWord_firstIndex] at heq
  simpa only [List.length_singleton, pow_one, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul, lpDistribution_apply,
    Opens.coe_top, Measure.restrict_univ] using heq

/-- Each coordinate is an Lp function, so the Euclidean gradient is too. -/
theorem gradient_memLp :
    Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization.GradientMemLp := by
  intro 𝕜 _ d p _ u
  apply MemLp.of_eval_piLp
  intro j
  simpa only [gradient, PiLp.toLp_apply, Opens.coe_top, Measure.restrict_univ] using
    Lp.memLp (u.val (firstIndex j))

open SmoothApproximateIdentitiesSpec Smoothing

/-- The vector convolution retains the joint Euclidean geometry. -/
def mollifiedGradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ) (ε : ℝ) (u : SobolevSpace 𝕜 d ⊤ 1 p) :
    Domain d → EuclideanSpace 𝕜 (Fin d) :=
  convolution (ScaledKernelValue ρ ε) (gradient u) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- At every positive scale, every coordinate derivative is the corresponding
coordinate of one vector convolution.  No compact-set scale restriction is
needed on the whole space. -/
theorem regularized_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (x : Domain d) :
    WithLp.toLp 2 (fun j =>
      fderiv ℝ (regularize ρ ε (u.val (zeroIndex d 1))) x (coordinateVector j)) =
      mollifiedGradient ρ ε u x := by
  let K := ScaledKernelValue ρ ε
  have hk := scaledKernel_properties ρ hρ ε hε
  have hi : ConvolutionExists K (gradient u)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro y
    exact (convolutionExistsAt_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)).mp
      (hk.2.1.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ).flip
        ((gradient_memLp 𝕜 d p u).locallyIntegrable Fact.out) hk.1.continuous y)
  apply PiLp.ext
  intro j
  have hj := interior_convolution_identity u (firstIndex j)
    (scaledKernelTest (𝕜 := 𝕜) ρ hρ ε hε) x (subset_univ _)
  rw [← regularize_eq_kernelTest ρ hρ hε, ← regularize_eq_kernelTest ρ hρ hε] at hj
  have hd : classicalDerivative (firstIndex j)
      (regularize ρ ε (u.val (zeroIndex d 1))) x =
      fderiv ℝ (regularize ρ ε (u.val (zeroIndex d 1))) x (coordinateVector j) := by
    unfold classicalDerivative
    rw [multiIndexWord_firstIndex]
    rfl
  rw [hd] at hj
  change fderiv ℝ (regularize ρ ε (u.val (zeroIndex d 1))) x (coordinateVector j) = _
  rw [hj]
  have hv := eval_integral_piLp (q := 2)
    (fun j => (hi x).eval_piLp j) j
  change (∫ y, K y • gradient u (x-y)) j =
    ∫ y, K y • (gradient u (x-y)) j at hv
  change (∫ y, K y • zeroExtend (u.val (firstIndex j)) (x-y)) =
    (∫ y, K y • gradient u (x-y)) j
  rw [hv]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [gradient, PiLp.toLp_apply, zeroExtend, Opens.coe_top, indicator_univ]

/-- Vector-valued contraction gives the sharp gradient norm at each scale. -/
theorem regularized_gradient_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ρ : Domain d → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (u : SobolevSpace 𝕜 d ⊤ 1 p) :
    eLpNorm (fun x => WithLp.toLp 2 (fun j =>
      fderiv ℝ (regularize ρ ε (u.val (zeroIndex d 1))) x (coordinateVector j))) p volume ≤
      eLpNorm (gradient u) p volume := by
  simp_rw [regularized_gradient ρ hρ hε]
  have hk := scaledKernel_properties ρ hρ ε hε
  exact eLpNorm_convolution_probability_le _ hk.1.continuous hk.2.1 hk.2.2.1 hk.2.2.2
    _ p Fact.out (gradient_memLp 𝕜 d p u)

/-- Translation differences preserve convergence in the whole-space Lp
seminorm, with error at most twice the original error. -/
theorem translation_difference_error_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f g : Domain d → 𝕜)
    (hm : AEStronglyMeasurable (f-g) volume) (h : Domain d) :
    eLpNorm (fun x => (f (x+h)-f x) - (g (x+h)-g x)) p volume ≤
      eLpNorm (f-g) p volume + eLpNorm (f-g) p volume := by
  have heq : (fun x => (f (x+h)-f x) - (g (x+h)-g x)) =
      (fun x => (f-g) (x+h)) - (f-g) := by funext x; simp only [Pi.sub_apply]; abel
  rw [heq]
  exact (eLpNorm_sub_le hp).trans_eq
    (congrArg (· + eLpNorm (f-g) p volume)
      (eLpNorm_comp_measurePreserving (g := f-g) hm (measurePreserving_add_right volume h)))

/-- The full sharp forward estimate for every finite exponent, including 1. -/
theorem forward_estimate_finite (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (h : Domain d) :
    eLpNorm (fun x => u.val (zeroIndex d 1) (x+h) - u.val (zeroIndex d 1) x)
      p volume ≤ ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) p volume := by
  obtain ⟨ρ, hρ⟩ := exists_mollifier d
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall ha⟩
  let f : ℕ → Domain d → 𝕜 := fun n => regularize ρ (a n) (u.val (zeroIndex d 1))
  have hf (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f n) := regularize_contDiff ρ hρ (ha n) _
  have hgm (n : ℕ) : MemLp (fun x => WithLp.toLp 2
      (fun j => fderiv ℝ (f n) x (coordinateVector j))) p volume := by
    exact (regularized_gradient_eLpNorm_le ρ hρ (ha n) u).trans_lt
      (gradient_memLp 𝕜 d p u).eLpNorm_lt_top
  have hb (n : ℕ) : eLpNorm (fun x => f n (x+h)-f n x) p volume ≤
      ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) p volume :=
    (smooth_translation_eLpNorm_le (f n) ((hf n).of_le (by simp)) p Fact.out hpt (hgm n) h).trans
      (mul_le_mul' le_rfl (regularized_gradient_eLpNorm_le ρ hρ (ha n) u))
  have hu : MemLp (u.val (zeroIndex d 1)) p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (u.val (zeroIndex d 1))
  have ht : Tendsto (fun n => eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) p volume)
      atTop (𝓝 0) := by
    simpa only [f, Function.comp_def, zeroExtend, Opens.coe_top, indicator_univ] using
      (regularize_zeroExtend_tendsto hpt ρ hρ (u.val (zeroIndex d 1))).comp hat
  have herr : Tendsto (fun n => eLpNorm
      (fun x => (f n (x+h)-f n x) -
        (u.val (zeroIndex d 1) (x+h)-u.val (zeroIndex d 1) x)) p volume) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) p volume +
          eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) p volume) atTop (𝓝 0) by
        simpa using ht.add ht)
    · intro n; exact bot_le
    · intro n
      exact translation_difference_error_le Fact.out _ _
        ((hf n).continuous.aestronglyMeasurable.sub hu.aestronglyMeasurable) h
  exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hb)
    (tendstoInMeasure_of_tendsto_eLpNorm (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one Fact.out)) herr)
    (fun n => ((hf n).continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable.sub
      (hf n).continuous.aestronglyMeasurable)

/-- The unit interval indicator changes only near its two endpoints. -/
theorem intervalIndicator_translation_bound (h : ℝ) :
    eLpNorm (fun x => intervalIndicator (x + h) - intervalIndicator x) 1 volume ≤
      ENNReal.ofReal (2 * |h|) := by
  let A := Icc (min (-h) 0) (max (-h) 0)
  let B := Icc (min (1-h) 1) (max (1-h) 1)
  let a : ℝ → ℝ := A.indicator (fun _ => 1)
  let b : ℝ → ℝ := B.indicator (fun _ => 1)
  have hsupport (x : ℝ) (hx : intervalIndicator (x+h) ≠ intervalIndicator x) :
      x ∈ A ∨ x ∈ B := by
    by_cases ht : x+h ∈ Icc (0 : ℝ) 1
    · have hx' : x ∉ Icc (0 : ℝ) 1 := by
        intro hx'
        exact hx (by simp [intervalIndicator, ht, hx'])
      simp only [mem_Icc, not_and_or, not_le] at hx'
      rcases hx' with hx' | hx'
      · left
        exact ⟨(min_le_left _ _).trans (by linarith [ht.1]),
          (le_of_lt hx').trans (le_max_right _ _)⟩
      · right
        exact ⟨(min_le_right _ _).trans hx'.le,
          (show x ≤ 1-h by linarith [ht.2]).trans (le_max_left _ _)⟩
    · have hx' : x ∈ Icc (0 : ℝ) 1 := by
        by_contra hx'
        exact hx (by simp [intervalIndicator, ht, hx'])
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · left
        exact ⟨(min_le_right _ _).trans hx'.1,
          (show x ≤ -h by linarith).trans (le_max_left _ _)⟩
      · right
        exact ⟨(min_le_left _ _).trans (by linarith),
          hx'.2.trans (le_max_right _ _)⟩
  have hpoint (x : ℝ) :
      ‖intervalIndicator (x+h) - intervalIndicator x‖ ≤ ‖a x + b x‖ := by
    have ha : 0 ≤ a x := by simp only [a, indicator]; split_ifs <;> norm_num
    have hb : 0 ≤ b x := by simp only [b, indicator]; split_ifs <;> norm_num
    by_cases heq : intervalIndicator (x+h) = intervalIndicator x
    · simp only [heq, sub_self, norm_zero, norm_nonneg]
    · have hle : ‖intervalIndicator (x+h) - intervalIndicator x‖ ≤ 1 := by
        by_cases h₁ : x+h ∈ Icc (0 : ℝ) 1 <;>
          by_cases h₂ : x ∈ Icc (0 : ℝ) 1 <;> simp [intervalIndicator, h₁, h₂]
      apply hle.trans
      rw [Real.norm_of_nonneg (add_nonneg ha hb)]
      rcases hsupport x heq with hx | hx
      · have : a x = 1 := by simp [a, hx]
        linarith
      · have : b x = 1 := by simp [b, hx]
        linarith
  have hmeas : AEStronglyMeasurable
      (fun x => intervalIndicator (x+h) - intervalIndicator x) volume := by
    exact ((intervalIndicator_memLp.aestronglyMeasurable).comp_measurePreserving
      (measurePreserving_add_right volume h)).sub intervalIndicator_memLp.aestronglyMeasurable
  have hA : eLpNorm a 1 volume = ENNReal.ofReal |h| := by
    rw [eLpNorm_indicator_const measurableSet_Icc.nullMeasurableSet (by simp) (by simp)]
    simp only [enorm_one, ENNReal.toReal_one, div_one, ENNReal.rpow_one, one_mul,
      Real.volume_Icc]
    congr 1
    rcases le_total 0 h with hh | hh
    · simp [min_eq_left (neg_nonpos.mpr hh), max_eq_right (neg_nonpos.mpr hh), abs_of_nonneg hh]
    · simp [min_eq_right (neg_nonneg.mpr hh), max_eq_left (neg_nonneg.mpr hh), abs_of_nonpos hh]
  have hB : eLpNorm b 1 volume = ENNReal.ofReal |h| := by
    rw [eLpNorm_indicator_const measurableSet_Icc.nullMeasurableSet (by simp) (by simp)]
    simp only [enorm_one, ENNReal.toReal_one, div_one, ENNReal.rpow_one, one_mul,
      Real.volume_Icc]
    congr 1
    rcases le_total 0 h with hh | hh
    · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg hh]
      ring
    · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos hh]
      ring
  calc
    _ ≤ eLpNorm (fun x => a x + b x) 1 volume := eLpNorm_mono hmeas hpoint
    _ ≤ eLpNorm a 1 volume + eLpNorm b 1 volume := eLpNorm_add_le (by simp)
    _ = ENNReal.ofReal (2 * |h|) := by
      rw [hA, hB, ← ENNReal.ofReal_add (abs_nonneg h) (abs_nonneg h)]
      congr 1
      ring

/-- Integration of the derivative of a smooth test over the unit interval. -/
theorem integral_deriv_mul_intervalIndicator (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ x, deriv φ x * intervalIndicator x) = φ 1 - φ 0 := by
  have heq : (fun x => deriv φ x * intervalIndicator x) =
      (Icc (0 : ℝ) 1).indicator (deriv φ) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [intervalIndicator, hx]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hφ.differentiable (by simp) x)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)

/-- Smooth tests concentrate at 0, with support strictly separated from 1. -/
def shrinkingBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 4
  rOut := (1 / ((n : ℝ) + 1)) / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

@[simp] theorem shrinkingBump_zero (n : ℕ) : shrinkingBump n 0 = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp [Metric.mem_closedBall, (shrinkingBump n).rIn_pos.le]

@[simp] theorem shrinkingBump_one (n : ℕ) : shrinkingBump n 1 = 0 := by
  apply ContDiffBump.zero_of_le_dist
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hn
  simpa [shrinkingBump, Real.dist_eq] using (show 1 / ((n : ℝ) + 1) / 2 ≤ 1 by linarith)

/-- For any integrable density, these concentrating test integrals vanish.
This uses atomlessness at 0, so it is specific to the real line. -/
theorem integral_shrinkingBump_tendsto_zero (g : ℝ → ℝ) (hg : Integrable g volume) :
    Tendsto (fun n => ∫ x, shrinkingBump n x * g x) atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => shrinkingBump n x * g x) atTop (𝓝 (0 : ℝ)) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with x hx
    have hd : 0 < dist x 0 := dist_pos.mpr hx
    have hr : Tendsto (fun n : ℕ => (shrinkingBump n).rOut) atTop (𝓝 0) := by
      simpa [shrinkingBump] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    apply tendsto_const_nhds.congr'
    filter_upwards [hr.eventually (gt_mem_nhds hd)] with n hn
    simp [ContDiffBump.zero_of_le_dist _ hn.le]
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
    (fun n => (shrinkingBump n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    hg.norm (fun n => Eventually.of_forall fun x => by
      change ‖shrinkingBump n x * g x‖ ≤ ‖g x‖
      rw [norm_mul, Real.norm_of_nonneg (shrinkingBump n).nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) (shrinkingBump n).le_one) hlim
  simpa using h

/-- The interval indicator has no integrable weak derivative: its derivative
is the difference of endpoint point masses, detected by shrinking smooth tests. -/
theorem intervalIndicator_no_integrable_weakDerivative :
    ¬ ∃ g : ℝ → ℝ, Integrable g volume ∧ HasRealWeakDerivative intervalIndicator g := by
  rintro ⟨g, hg, hder⟩
  have heq (n : ℕ) : (∫ x, shrinkingBump n x * g x) = 1 := by
    rw [hder _ (shrinkingBump n).contDiff (shrinkingBump n).hasCompactSupport,
      integral_deriv_mul_intervalIndicator _ (shrinkingBump n).contDiff,
      shrinkingBump_one, shrinkingBump_zero]
    norm_num
  have ht := integral_shrinkingBump_tendsto_zero g hg
  simp only [heq] at ht
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

/-- The standard linear, topological and measure equivalence ℝ¹ ≃ ℝ. -/
def lineEquiv : Domain 1 ≃L[ℝ] ℝ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

/-- Lift a real test to the coordinate model used by the accepted Sobolev space. -/
def lineTest (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : Tests ℝ (⊤ : Opens (Domain 1)) :=
  ⟨φ ∘ lineEquiv, hφ.comp lineEquiv.contDiff,
    hc.comp_homeomorph lineEquiv.toHomeomorph, subset_univ _⟩

@[simp] theorem lineTest_partial (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (x : Domain 1) :
    testPartialCLM [0] (lineTest φ hφ hc) x = deriv φ (x 0) := by
  rw [testPartial_single_apply]
  change fderiv ℝ (φ ∘ lineEquiv) x (coordinateVector 0) = _
  rw [fderiv_comp x (hφ.differentiable (by simp) _) lineEquiv.differentiableAt]
  rw [lineEquiv.hasFDerivAt.fderiv]
  change fderiv ℝ φ (x 0) 1 = deriv φ (x 0)
  exact fderiv_apply_one_eq_deriv

/-- The obstruction holds in the actual accepted W^{1,1} graph as well as in
the ordinary real-line weak-derivative formulation. -/
theorem intervalIndicator_not_sobolev :
    Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization.GraphEndpointObstruction := by
  rintro ⟨u, hu⟩
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  let g : ℝ → ℝ := fun t => u.val (firstIndex (0 : Fin 1)) (e.symm t)
  have hg : Integrable g volume := by
    apply he.symm.integrable_comp_of_integrable
    exact (memLp_one_iff_integrable.mp
      (Lp.memLp (u.val (firstIndex (0 : Fin 1))))).mono_measure (by simp)
  apply intervalIndicator_no_integrable_weakDerivative
  refine ⟨g, hg, ?_⟩
  intro φ hφ hc
  have hid := first_weakDerivative_test_identity u 0 (lineTest φ hφ hc)
  have hleft : (∫ x, lineTest φ hφ hc x * u.val (firstIndex (0 : Fin 1)) x) =
      ∫ t, φ t * g t := by
    have h := he.symm.integral_comp' (fun x =>
      lineTest φ hφ hc x * u.val (firstIndex (0 : Fin 1)) x)
    exact h.symm
  have hright : (∫ x, testPartialCLM [0] (lineTest φ hφ hc) x *
      u.val (zeroIndex 1 1) x) = ∫ t, deriv φ t * intervalIndicator t := by
    calc
      _ = ∫ x : Domain 1, deriv φ (x 0) * intervalIndicator (x 0) := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        rw [lineTest_partial, hx]
      _ = _ := he.integral_comp' (fun t => deriv φ t * intervalIndicator t)
  rwa [hleft, hright] at hid

theorem endpoint_obstruction :
    Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization.EndpointObstruction :=
  ⟨intervalIndicator_memLp, intervalIndicator_translation_bound,
    intervalIndicator_no_integrable_weakDerivative⟩

/-- Every order-at-most-one multi-index is zero or a coordinate index. -/

theorem derivativeIndex_one_cases {d : ℕ} (α : DerivativeIndex d 1) :
    α = zeroIndex d 1 ∨ ∃ j : Fin d, α = firstIndex j := by
  have hl : (multiIndexWord (natIndex α)).length ≤ 1 := by
    simpa only [multiIndexWord_length, natIndex] using α.property
  have hext (β : DerivativeIndex d 1)
      (hw : multiIndexWord (natIndex α) = multiIndexWord (natIndex β)) : α = β := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact (multiIndexWord_count (natIndex α) i).symm.trans
      ((congrArg (List.count i) hw).trans (multiIndexWord_count (natIndex β) i))
  by_cases hz : (multiIndexWord (natIndex α)).length = 0
  · left
    apply hext
    have hα := List.length_eq_zero_iff.mp hz
    rw [hα]
    apply Eq.symm
    apply List.length_eq_zero_iff.mp
    simp [natIndex, zeroIndex]
  · right
    obtain ⟨j, hj⟩ := List.length_eq_one_iff.mp (by omega : (multiIndexWord (natIndex α)).length = 1)
    exact ⟨j, hext (firstIndex j) (hj.trans (multiIndexWord_firstIndex j).symm)⟩

/-- Coordinate weak derivatives determine a member of the accepted Sobolev graph. -/
theorem exists_sobolev_of_coordinate_derivatives {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (g : Fin d → DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hg : ∀ j (φ : Tests 𝕜 (⊤ : Opens (Domain d))),
      (∫ x, φ x * g j x) = -(∫ x, testPartialCLM [j] φ x * u x)) :
    ∃ v : SobolevSpace 𝕜 d ⊤ 1 p,
      v.val (zeroIndex d 1) = u ∧ ∀ j, v.val (firstIndex j) = g j := by
  have hd (j : Fin d) : lpDistribution (g j) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d ⊤ (natIndex (firstIndex j)) (lpDistribution u) := by
    ext φ
    simpa only [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
      multiIndexWord_firstIndex, List.length_singleton, pow_one, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, neg_one_mul, lpDistribution_apply,
      Opens.coe_top, Measure.restrict_univ] using hg j φ
  obtain ⟨v, hv⟩ := (sobolev_membership 𝕜 d ⊤ 1 p u).mpr (by
    intro α hα
    have hnat : natIndex (boundedIndex α hα) = α := rfl
    rcases derivativeIndex_one_cases (boundedIndex α hα) with hz | ⟨j, hj⟩
    · refine ⟨u, ?_⟩
      rw [← hnat, hz]
      exact (derivative_zero _).symm
    · exact ⟨g j, by rw [← hnat, hj]; exact hd j⟩)
  refine ⟨v, hv, ?_⟩
  intro j
  apply lpDistribution_injective
  exact (v.property (firstIndex j)).trans (by rw [hv]; exact (hd j).symm)



/-- The Euclidean gradient bound is preserved jointly, pointwise. -/
theorem regularized_gradient_norm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SobolevSpace 𝕜 d ⊤ 1 ∞) (x : Domain d) :
    ‖WithLp.toLp 2 (fun j =>
      fderiv ℝ (regularize ρ ε (u.val (zeroIndex d 1))) x (coordinateVector j))‖ ≤
      (eLpNorm (gradient u) ∞ volume).toReal := by
  rw [regularized_gradient ρ hρ hε]
  have hk := scaledKernel_properties ρ hρ ε hε
  have hb := enorm_convolution_le (p := 1) (q := ∞)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      EuclideanSpace 𝕜 (Fin d) →L[ℝ] EuclideanSpace 𝕜 (Fin d))
    hk.1.continuous.aestronglyMeasurable
    (gradient_memLp 𝕜 d ∞ u).aestronglyMeasurable x
  have he : ‖mollifiedGradient ρ ε u x‖ₑ ≤ eLpNorm (gradient u) ∞ volume := by
    calc
      _ ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
          EuclideanSpace 𝕜 (Fin d) →L[ℝ] EuclideanSpace 𝕜 (Fin d))‖ₑ *
          eLpNorm (gradient u) ∞ volume := by
        simpa only [mollifiedGradient, scaledKernel_eLpNorm_one ρ hρ hε, mul_one] using hb
      _ ≤ 1 * eLpNorm (gradient u) ∞ volume := by
        gcongr
        exact ContinuousLinearMap.opENorm_lsmul_le
      _ = _ := one_mul _
  exact ENNReal.toReal_le_toReal (by simp) (gradient_memLp 𝕜 d ∞ u).eLpNorm_ne_top |>.mpr he

/-- Translation shifts the compact integration set exactly. -/
theorem translation_difference_error_restrict_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f g : Domain d → 𝕜) (hm : AEStronglyMeasurable (f-g) volume)
    (K : Set (Domain d)) (h : Domain d) :
    eLpNorm (fun x => (f (x+h)-f x) - (g (x+h)-g x)) 1 (volume.restrict K) ≤
      eLpNorm (f-g) 1 (volume.restrict ((fun x => x+h) '' K)) +
      eLpNorm (f-g) 1 (volume.restrict K) := by
  have heq : (fun x => (f (x+h)-f x) - (g (x+h)-g x)) =
      (fun x => (f-g) (x+h)) - (f-g) := by funext x; simp only [Pi.sub_apply]; abel
  rw [heq]
  refine (eLpNorm_sub_le le_rfl).trans_eq ?_
  congr 1
  have mp := (measurePreserving_add_right volume h).restrict_image_emb
    (Homeomorph.addRight h).measurableEmbedding K
  exact eLpNorm_comp_measurePreserving (g := f-g) hm.restrict mp

/-- The full sharp forward estimate at the infinity endpoint. -/
theorem forward_estimate_infinity (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u : SobolevSpace 𝕜 d ⊤ 1 ∞) (h : Domain d) :
    eLpNorm (fun x => u.val (zeroIndex d 1) (x+h) - u.val (zeroIndex d 1) x)
      ∞ volume ≤ ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) ∞ volume := by
  obtain ⟨ρ, hρ⟩ := exists_mollifier d
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall ha⟩
  let f : ℕ → Domain d → 𝕜 := fun n => regularize ρ (a n) (u.val (zeroIndex d 1))
  let g : Domain d → 𝕜 := fun x => u.val (zeroIndex d 1) (x+h) - u.val (zeroIndex d 1) x
  let R := ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) ∞ volume
  have hf (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f n) := regularize_contDiff ρ hρ (ha n) _
  have hu : MemLp (u.val (zeroIndex d 1)) ∞ volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (u.val (zeroIndex d 1))
  have hb (n : ℕ) (x : Domain d) : ‖f n (x+h) - f n x‖ₑ ≤ R := by
    have hp := smooth_translation_bound_of_gradient_bound (f n)
      ((hf n).differentiable (by simp)) (eLpNorm (gradient u) ∞ volume).toReal
      (regularized_gradient_norm_le ρ hρ (ha n) u) x h
    rw [← ofReal_norm]
    calc
      _ ≤ ENNReal.ofReal (euclideanLength h * (eLpNorm (gradient u) ∞ volume).toReal) :=
        ENNReal.ofReal_le_ofReal hp
      _ = R := by
        rw [ENNReal.ofReal_mul (show 0 ≤ euclideanLength h from norm_nonneg _), ENNReal.ofReal_toReal
          (gradient_memLp 𝕜 d ∞ u).eLpNorm_ne_top]
  have ht (K : Set (Domain d)) (hK : IsCompact K) :
      Tendsto (fun n => eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) 1
        (volume.restrict K)) atTop (𝓝 0) := by
    simpa only [f, Function.comp_def] using
      (regularize_local_finite_tendsto ρ hρ (u.val (zeroIndex d 1)) hK (subset_univ _)
        1 le_rfl ENNReal.one_ne_top).comp hat
  have hlocal (K : Set (Domain d)) (hK : IsCompact K) : eLpNorm g ∞ (volume.restrict K) ≤ R := by
    have hshift : IsCompact ((fun x : Domain d => x+h) '' K) :=
      hK.image (continuous_id.add continuous_const)
    have herr : Tendsto (fun n => eLpNorm (fun x => (f n (x+h)-f n x)-g x) 1
        (volume.restrict K)) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n =>
            eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) 1
              (volume.restrict ((fun x => x+h) '' K)) +
            eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) 1
              (volume.restrict K)) atTop (𝓝 0) by
          simpa using (ht _ hshift).add (ht K hK))
      · intro n; exact bot_le
      · intro n
        exact translation_difference_error_restrict_le _ _
          ((hf n).continuous.aestronglyMeasurable.sub hu.aestronglyMeasurable) K h
    have hfm (n : ℕ) : AEStronglyMeasurable (fun x => f n (x+h)-f n x) (volume.restrict K) :=
      (((hf n).continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable.sub
        (hf n).continuous.aestronglyMeasurable).restrict
    exact eLpNorm_le_of_tendstoInMeasure (f := fun n x => f n (x+h)-f n x)
      (Eventually.of_forall fun n => by
        rw [eLpNorm_exponent_top (hfm n)]
        exact eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall (hb n)))
      (tendstoInMeasure_of_tendsto_eLpNorm (by simp : (1 : ℝ≥0∞) ≠ 0) herr)
      hfm
  change eLpNorm g ∞ volume ≤ R
  have hg : AEStronglyMeasurable g volume :=
    (hu.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right volume h)).sub
      hu.aestronglyMeasurable
  rw [eLpNorm_exponent_top hg]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  have hballs : ∀ n : ℕ, ∀ᵐ x ∂volume.restrict (closedBall (0 : Domain d) n), ‖g x‖ₑ ≤ R := by
    intro n
    exact (enorm_ae_le_eLpNormEssSup g _).mono fun x hx =>
      hx.trans (eLpNormEssSup_le_eLpNorm_top.trans (hlocal _ (isCompact_closedBall _ _)))
  have hall := (ae_restrict_iUnion_iff (fun n : ℕ => closedBall (0 : Domain d) n)
    (fun x => ‖g x‖ₑ ≤ R)).mpr hballs
  simpa only [iUnion_closedBall_nat, Measure.restrict_univ] using hall

/-- Sharp Euclidean Sobolev translation estimate for all 1 ≤ p ≤ ∞. -/
theorem forward_estimate :
    Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization.ForwardEstimate := by
  intro 𝕜 _ d p _ u h
  by_cases hp : p = ∞
  · subst p
    exact forward_estimate_infinity 𝕜 d u h
  · exact forward_estimate_finite 𝕜 d p hp u h


@[simp] theorem euclideanLength_smul {d : ℕ} (t : ℝ) (h : Domain d) :
    euclideanLength (t • h) = |t| * euclideanLength h := by
  change ‖t • WithLp.toLp 2 h‖ = _
  rw [norm_smul, Real.norm_eq_abs]
  rfl

@[simp] theorem euclideanLength_coordinateVector {d : ℕ} (j : Fin d) :
    euclideanLength (coordinateVector j) = 1 := by
  simp [euclideanLength, coordinateVector, PiLp.toLp_single]

/-- In positive dimension a proposed translation Lipschitz constant is nonnegative. -/
theorem translation_constant_nonneg {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) (C : ℝ)
    (hC : ∀ h : Domain d,
      (eLpNorm (fun x => u (x+h)-u x) p volume).toReal ≤ C * euclideanLength h)
    (j : Fin d) : 0 ≤ C := by
  have hc := hC (coordinateVector j)
  rw [euclideanLength_coordinateVector, mul_one] at hc
  exact ENNReal.toReal_nonneg.trans hc

theorem translation_difference_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) (h : Domain d) :
    MemLp (fun x => u (x+h)-u x) p volume := by
  have hu : MemLp u p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp u
  exact (hu.comp_measurePreserving (measurePreserving_add_right volume h)).sub hu


open ExpandedFA.FunctionSpaces


/-- A scalar-linear functional controlled by the Lq size of a linear image
has an Lp density, with the same quantitative bound. -/
theorem exists_lp_density_of_linear_bound {X : Type} [MeasurableSpace X]
    {𝕜 : Type} [RCLike 𝕜] (μ : Measure X) [SigmaFinite μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hqt : q ≠ ∞) {V : Type} [AddCommGroup V] [Module 𝕜 V]
    (J : V →ₗ[𝕜] Lp 𝕜 q μ) (F : V →ₗ[𝕜] 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ v, ‖F v‖ ≤ C * ‖J v‖) :
    ∃ g : Lp 𝕜 p μ, ‖g‖ ≤ C ∧ ∀ v, F v = ∫ x, J v x * g x ∂μ := by
  have hker : LinearMap.ker J.rangeRestrict ≤ LinearMap.ker F := by
    intro v hv
    have hJ : J v = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hJ] using hF v) (norm_nonneg _)
  let F₀ : LinearMap.range J →ₗ[𝕜] 𝕜 :=
    J.rangeRestrict.liftOfSurjective J.surjective_rangeRestrict ⟨F, hker⟩
  have hF₀ (v : V) : F₀ (J.rangeRestrict v) = F v :=
    LinearMap.equivOfSurjective_apply J.surjective_rangeRestrict hker
  have hbound (v : LinearMap.range J) : ‖F₀ v‖ ≤ C * ‖v‖ := by
    obtain ⟨w, rfl⟩ := J.surjective_rangeRestrict v
    rw [hF₀]
    exact hF w
  let F₁ : LinearMap.range J →L[𝕜] 𝕜 := F₀.mkContinuous C hbound
  obtain ⟨L, hL, hnorm⟩ := exists_extension_norm_eq (LinearMap.range J) F₁
  obtain ⟨g, hg, _⟩ := ExpandedFA.FunctionSpaces.lp_duality_sigmaFinite μ q p hqt L
  refine ⟨g, hg.2.trans_le (hnorm.le.trans ?_), ?_⟩
  · exact F₁.opNorm_le_bound hC hbound
  · intro v
    calc
      F v = F₁ (J.rangeRestrict v) := (hF₀ v).symm
      _ = L (J v) := (hL _).symm
      _ = ∫ x, J v x * g x ∂μ := (hg.1 (J v)).2

/-- The canonical scalar-linear map from compact smooth tests to their Lq
classes on the whole Euclidean space. -/
def testToLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (μ : Measure (Domain d)) [IsFiniteMeasureOnCompacts μ]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Tests 𝕜 (⊤ : Opens (Domain d)) →ₗ[𝕜] Lp 𝕜 q μ where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem norm_testToLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (μ : Measure (Domain d)) [IsFiniteMeasureOnCompacts μ]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ‖testToLp μ q φ‖ = (eLpNorm φ q μ).toReal :=
  Lp.norm_toLp φ (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

@[simp] theorem testToLp_coeFn {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (μ : Measure (Domain d)) [IsFiniteMeasureOnCompacts μ]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    testToLp μ q φ =ᵐ[μ] (φ : Domain d → 𝕜) :=
  MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

/-- A distribution bounded on tests by their Lq norm has an Lp density. -/
theorem exists_lp_density_of_test_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (μ : Measure (Domain d)) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hqt : q ≠ ∞) (F : Tests 𝕜 (⊤ : Opens (Domain d)) →ₗ[𝕜] 𝕜)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ φ, ‖F φ‖ ≤ C * (eLpNorm φ q μ).toReal) :
    ∃ g : Lp 𝕜 p μ,
      ‖g‖ ≤ C ∧ ∀ φ, F φ = ∫ x, φ x * g x ∂μ := by
  obtain ⟨g, hg, hrepr⟩ := exists_lp_density_of_linear_bound μ p q hqt
    (testToLp μ q) F C hC (by simpa only [norm_testToLp] using hF)
  refine ⟨g, hg, fun φ => (hrepr φ).trans ?_⟩
  apply integral_congr_ae
  exact (testToLp_coeFn μ q φ).mul (Filter.EventuallyEq.refl _ _)

/-- The representation bridge for a first distributional derivative. -/
theorem exists_weak_derivative_of_test_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate q p]
    (hqt : q ≠ ∞) (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) (j : Fin d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ : Tests 𝕜 (⊤ : Opens (Domain d)),
      ‖∫ x, testPartialCLM [j] φ x * u x‖ ≤ C * (eLpNorm φ q volume).toReal) :
    ∃ g : DomainLp 𝕜 (⊤ : Opens (Domain d)) p,
      ‖g‖ ≤ C ∧ ∀ φ : Tests 𝕜 (⊤ : Opens (Domain d)),
        (∫ x, φ x * g x) = -(∫ x, testPartialCLM [j] φ x * u x) := by
  let F : Tests 𝕜 (⊤ : Opens (Domain d)) →ₗ[𝕜] 𝕜 :=
    (-((lpDistribution u).comp (testPartialCLM [j]))).toLinearMap
  have hF (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
      F φ = -(∫ x, testPartialCLM [j] φ x * u x) := by
    simp [F, lpDistribution_apply]
  obtain ⟨g, hg, hrepr⟩ := exists_lp_density_of_test_bound
    (volume.restrict (↑(⊤ : Opens (Domain d)))) p q hqt F C hC
    (fun φ => by simpa only [hF, norm_neg, Opens.coe_top, Measure.restrict_univ] using hbound φ)
  refine ⟨g, hg, fun φ => ?_⟩
  have he := (hrepr φ).symm.trans (hF φ)
  simpa only [Opens.coe_top, Measure.restrict_univ] using he


lemma raw_integral_mul_norm_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {f g : Domain d → 𝕜} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    ‖∫ x, f x * g x‖ ≤ (eLpNorm g q volume).toReal * (eLpNorm f p volume).toReal := by
  rw [← lp_pairing_on_representatives volume p q f g hf hg]
  simpa only [Lp.norm_toLp] using lp_pairing_apply_bound volume p q (hg.toLp g) (hf.toLp f)

lemma euclideanLength_smul_coordinate {d : ℕ} (j : Fin d) (t : ℝ) :
    euclideanLength (t • coordinateVector j) = |t| := by
  simp [euclideanLength, coordinateVector, PiLp.norm_eq_of_L2,
    Real.sqrt_sq_eq_abs]

lemma test_convolution_hasDerivAt {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Domain d → 𝕜) (hu : LocallyIntegrable u volume)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (j : Fin d) :
    HasDerivAt (fun t : ℝ => ∫ x, φ x * u (x + t • coordinateVector j))
      (-(∫ x, testPartialCLM [j] φ x * u x)) 0 := by
  let ψ : Domain d → 𝕜 := fun x => φ (-x)
  let L : 𝕜 →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.mul ℝ 𝕜
  have hc : HasCompactSupport ψ := φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg _)
  have hd : ContDiff ℝ 1 ψ := φ.contDiff.of_le (by simp) |>.comp contDiff_neg
  have hf := hc.hasFDerivAt_convolution_right L hu hd (0 : Domain d)
  have hψ (x : Domain d) : fderiv ℝ ψ (-x) (coordinateVector j) =
      -(testPartialCLM [j] φ x) := by
    have hh : HasFDerivAt ψ
        ((fderiv ℝ φ x).comp (-(ContinuousLinearMap.id ℝ (Domain d)))) (-x) := by
      convert (φ.contDiff.differentiable (by simp) (-(-x))).hasFDerivAt.comp (-x)
        ((hasFDerivAt_id (-x)).neg) using 1 <;> simp [ψ, Function.comp_def]
    rw [hh.fderiv]
    simp [testPartial_single_apply]
  have hi : Integrable (fun x => (L.precompR (Domain d)) (u x) (fderiv ℝ ψ (-x))) volume := by
    have h := (hc.fderiv ℝ).convolutionExists_right (L.precompR (Domain d)) hu
      (hd.continuous_fderiv (by simp)) (0 : Domain d)
    simpa only [ConvolutionExistsAt, zero_sub] using h
  have hf' : HasFDerivAt (u ⋆[L, volume] ψ)
      ((u ⋆[L.precompR (Domain d), volume] fderiv ℝ ψ) 0)
      ((0 : ℝ) • coordinateVector j) := by simpa only [zero_smul] using hf
  have hder := hf'.comp_hasDerivAt (0 : ℝ)
    (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)) :
      HasDerivAt (fun t : ℝ => t • coordinateVector j) (coordinateVector j) 0)
  have hde : ((u ⋆[L.precompR (Domain d), volume] fderiv ℝ ψ) 0)
      (coordinateVector j) = -(∫ x, testPartialCLM [j] φ x * u x) := by
    simp only [convolution_def, zero_sub]
    rw [ContinuousLinearMap.integral_apply hi]
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hψ]
    change (∫ x, u x * -(testPartialCLM [j] φ x)) = _
    simp_rw [mul_neg, mul_comm (u _)]
    exact integral_neg _
  rw [hde] at hder
  convert hder using 1
  funext t
  change (∫ x, φ x * u (x + t • coordinateVector j)) =
    (∫ x, u x * ψ (t • coordinateVector j - x))
  rw [← integral_add_right_eq_self (fun x => u x * ψ (t • coordinateVector j - x))
    (t • coordinateVector j)]
  congr 1
  funext x
  simp [ψ, mul_comm]

/-- A translation Lipschitz bound controls each weak derivative on compact tests.
The proof differentiates a convolution with the reflected test function. -/
lemma translation_test_integral_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (u : Domain d → 𝕜) (hu : MemLp u p volume) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ h : Domain d,
      (eLpNorm (fun x => u (x+h) - u x) p volume).toReal ≤ C * euclideanLength h)
    (j : Fin d) (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ‖∫ x, testPartialCLM [j] φ x * u x‖ ≤ C * (eLpNorm φ q volume).toReal := by
  have hφ : MemLp φ q volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  let F : ℝ → 𝕜 := fun t => ∫ x, φ x * u (x + t • coordinateVector j)
  have hint (t : ℝ) : Integrable (fun x => φ x * u (x+t • coordinateVector j)) := by
    have hh := (hu.comp_measurePreserving
      (measurePreserving_add_right volume (t • coordinateVector j))).integrable_mul hφ
    exact hh.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hder : HasDerivAt F (-(∫ x, testPartialCLM [j] φ x * u x)) 0 :=
    test_convolution_hasDerivAt u (hu.locallyIntegrable Fact.out) φ j
  have hinc (t : ℝ) : ‖F t - F 0‖ ≤
      (C * (eLpNorm φ q volume).toReal) * ‖t - 0‖ := by
    have hdiff : MemLp (fun x => u (x + t • coordinateVector j) - u x) p volume :=
      (hu.comp_measurePreserving
        (measurePreserving_add_right volume (t • coordinateVector j))).sub hu
    have heq : F t - F 0 = ∫ x, (u (x + t • coordinateVector j) - u x) * φ x := by
      rw [← integral_sub (hint t) (hint 0)]
      simp only [zero_smul, add_zero, sub_mul, mul_comm]
    rw [heq]
    calc
      _ ≤ (eLpNorm φ q volume).toReal *
          (eLpNorm (fun x => u (x + t • coordinateVector j) - u x) p volume).toReal :=
        raw_integral_mul_norm_bound hdiff hφ
      _ ≤ (eLpNorm φ q volume).toReal * (C * |t|) := by
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        simpa only [euclideanLength_smul_coordinate] using hbound (t • coordinateVector j)
      _ = _ := by rw [sub_zero, Real.norm_eq_abs]; ring
  have hb := hder.le_of_lip' (mul_nonneg hC ENNReal.toReal_nonneg)
    (Eventually.of_forall hinc)
  simpa only [norm_neg] using hb

/-- Conjugate exponents remain interior when the original exponent is interior. -/
theorem exists_interior_holder_conjugate {p : ℝ≥0∞} (hp : 1 < p) (hpt : p ≠ ∞) :
    ∃ q : ℝ≥0∞, 1 < q ∧ q ≠ ∞ ∧ ENNReal.HolderConjugate p q := by
  let q : ℝ≥0∞ := (1-p⁻¹)⁻¹
  have hpi : p⁻¹ ≤ 1 := by
    simpa only [inv_one] using (ENNReal.inv_le_inv.mpr hp.le)
  haveI hpq : ENNReal.HolderConjugate p q := ⟨by
    simp only [q, inv_inv, inv_one]
    exact add_tsub_cancel_of_le hpi⟩
  refine ⟨q, (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hpt.lt_top,
    (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp.ne', hpq⟩


/-- Translation Lipschitz bounds imply membership in the accepted first
Sobolev graph, with the sharp bound for every coordinate derivative. -/
theorem converse :
    Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization.Converse := by
  intro 𝕜 _ d p _ hp hpt u C hC
  obtain ⟨q, hq, hqt, hpq⟩ := exists_interior_holder_conjugate hp hpt
  letI : Fact (1 ≤ q) := ⟨hq.le⟩
  haveI : ENNReal.HolderConjugate p q := hpq
  have hu : MemLp u p volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp u
  have hcoord (j : Fin d) : ∃ g : DomainLp 𝕜 (⊤ : Opens (Domain d)) p,
      ‖g‖ ≤ C ∧ ∀ φ : Tests 𝕜 (⊤ : Opens (Domain d)),
        (∫ x, φ x * g x) = -(∫ x, testPartialCLM [j] φ x * u x) := by
    have hnonneg : 0 ≤ C := translation_constant_nonneg u C hC j
    exact exists_weak_derivative_of_test_bound p q hqt u j C hnonneg
      (fun φ => translation_test_integral_bound u hu C hnonneg hC j φ)
  choose g hg hgi using hcoord
  obtain ⟨v, hv, hvj⟩ := exists_sobolev_of_coordinate_derivatives u g hgi
  refine ⟨v, hv, fun j => ?_⟩
  rw [hvj]
  exact hg j


end ExpandedFA.Sobolev.Translation
