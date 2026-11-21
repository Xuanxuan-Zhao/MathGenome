import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Sobolev Hilbert scales on compact smooth curves. At every real order,
finite smooth chart partitions give complete Hilbert spaces of intrinsic scalar
distributions, with the exact chart square-sum norm and atlas equivalences
preserving the underlying distribution. Smooth reparametrizations act by scalar
pullback, transposed against the inverse absolute Jacobian on density tests.
The construction covers both canonical real and complex Fourier scales,
including empty and disconnected curves. The supporting local estimates and
intrinsic test-density geometry are proved below. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal

namespace ExpandedFA.Sobolev.Curve

private theorem inverse_image_target (e : OpenPartialHomeomorph ℝ ℝ) :
    e.symm '' e.target = e.source := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact e.symm.map_source hy
  · intro hx
    exact ⟨e x, e.map_source hx, e.left_inv hx⟩

theorem density_pairing :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.densityPairingType := by
  intro 𝕜 _ e he f φ
  have h := integral_image_eq_integral_abs_deriv_smul e.open_target.measurableSet
    (fun y hy => (he y hy).hasDerivAt.hasDerivWithinAt)
    e.symm.injOn (fun x => f (e x) * φ x)
  rw [inverse_image_target] at h
  rw [h]
  apply setIntegral_congr_fun e.open_target.measurableSet
  intro y hy
  simp only [e.right_inv hy, inverseDensity, mul_smul_comm]

theorem density_integrability :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.densityIntegrabilityType := by
  intro 𝕜 _ e he f φ
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    e.open_target.measurableSet
    (fun y hy => (he y hy).hasDerivAt.hasDerivWithinAt)
    e.symm.injOn (fun x => f (e x) * φ x)
  rw [inverse_image_target] at h
  refine h.trans (integrableOn_congr_fun ?_ e.open_target.measurableSet)
  intro y hy
  simp only [e.right_inv hy, inverseDensity, mul_smul_comm]

/-- Exact whole-line square-energy formula for a localized coordinate
pullback. The formula also holds for infinite energies. -/
theorem localizedPullback_energy {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a f : ℝ → 𝕜) :
    (∫⁻ x, ‖localizedPullback e a f x‖ₑ ^ 2) =
      ∫⁻ y in e.target, ENNReal.ofReal |deriv e.symm y| *
        ‖a (e.symm y)‖ₑ ^ 2 * ‖f y‖ₑ ^ 2 := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul e.open_target.measurableSet
    (fun y hy => (he y hy).hasDerivAt.hasDerivWithinAt)
    e.symm.injOn (fun x => ‖a x * f (e x)‖ₑ ^ 2)
  rw [inverse_image_target] at h
  have hind : (fun x => ‖localizedPullback e a f x‖ₑ ^ 2) =
      e.source.indicator (fun x => ‖a x * f (e x)‖ₑ ^ 2) := by
    ext x
    by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx]
  rw [hind, lintegral_indicator e.open_source.measurableSet, h]
  apply setLIntegral_congr_fun e.open_target.measurableSet
  intro y hy
  simp only [e.right_inv hy, enorm_mul, mul_pow, mul_assoc]

theorem localizedPullback_energy_le {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a f : ℝ → 𝕜)
    {C : ℝ} (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2)) :
    (∫⁻ x, ‖localizedPullback e a f x‖ₑ ^ 2) ≤
      ENNReal.ofReal (C ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 := by
  rw [localizedPullback_energy e he]
  calc
    _ ≤ ∫⁻ y in e.target, ENNReal.ofReal (C ^ 2) * ‖f y‖ₑ ^ 2 := by
      apply setLIntegral_mono' e.open_target.measurableSet
      intro y hy
      gcongr
      exact hC y hy
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ y in e.target, ‖f y‖ₑ ^ 2 :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 :=
      by
        gcongr
        exact Measure.restrict_le_self

/-- Compact localization supplies the inverse-Jacobian bound. No bound on
the coordinate transformation away from this compact set is required. -/
theorem localizedPullback_jacobian_bound {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a : ℝ → 𝕜)
    (ha : Continuous a) (hcompact : HasCompactSupport a)
    (hsupp : tsupport a ⊆ e.source)
    (he : ContinuousOn (deriv e.symm) e.target) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
  have hcont : ContinuousOn (fun x => |deriv e.symm (e x)| * ‖a x‖ ^ 2)
      (tsupport a) :=
    ((he.comp (e.continuousOn.mono hsupp) (fun x hx => e.map_source (hsupp hx))).abs).mul
      (ha.norm.pow 2).continuousOn
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hcont
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro y hy
  have hb : |deriv e.symm y| * ‖a (e.symm y)‖ ^ 2 ≤ (max 1 B) ^ 2 := by
    by_cases ha0 : a (e.symm y) = 0
    · simp [ha0]
    have hmem : e.symm y ∈ tsupport a := subset_tsupport a ha0
    have h := hB (mem_image_of_mem _ hmem)
    simp only [e.right_inv hy] at h
    have h1 : 1 ≤ max 1 B := le_max_left _ _
    have h2 : B ≤ max 1 B := le_max_right _ _
    nlinarith
  convert ENNReal.ofReal_le_ofReal hb using 1
  rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]

theorem localizedPullback_stronglyMeasurable {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f : ℝ → 𝕜)
    (ha : Measurable a) (hf : StronglyMeasurable f) :
    StronglyMeasurable (localizedPullback e a f) := by
  classical
  let e' : ℝ → ℝ := e.source.piecewise e (fun _ => 0)
  have he' : Measurable e' := e.continuousOn.measurable_piecewise
    continuousOn_const e.open_source.measurableSet
  have hm : StronglyMeasurable (e.source.indicator (fun x => a x * f (e' x))) :=
    (ha.stronglyMeasurable.mul (hf.comp_measurable he')).indicator
      e.open_source.measurableSet
  convert hm using 1
  ext x
  by_cases hx : x ∈ e.source <;> simp [localizedPullback, e', hx]

@[simp] theorem localizedPullback_add {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f g : ℝ → 𝕜) :
    localizedPullback e a (f + g) = localizedPullback e a f + localizedPullback e a g := by
  ext x
  by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx, mul_add]

@[simp] theorem localizedPullback_sub {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f g : ℝ → 𝕜) :
    localizedPullback e a (f - g) = localizedPullback e a f - localizedPullback e a g := by
  ext x
  by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx, mul_sub]

@[simp] theorem localizedPullback_smul {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f : ℝ → 𝕜) (c : 𝕜) :
    localizedPullback e a (c • f) = c • localizedPullback e a f := by
  ext x
  by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx, mul_left_comm]

private theorem eLpNorm_two_sq {𝕜 : Type*} [RCLike 𝕜]
    (f : ℝ → 𝕜) (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hf)

/-- The energy estimate makes the localized coordinate operation independent
of the representative of an L² class. -/
theorem localizedPullback_congr_ae {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a : ℝ → 𝕜)
    (ha : Measurable a) {C : ℝ} (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2))
    (f g : ℝ → 𝕜) (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hfg : f =ᵐ[volume] g) :
    localizedPullback e a f =ᵐ[volume] localizedPullback e a g := by
  have hzero : (∫⁻ x, ‖(f - g) x‖ₑ ^ 2) = 0 := by
    have h : (fun x => ‖(f - g) x‖ₑ ^ 2) =ᵐ[volume] 0 := by
      filter_upwards [hfg] with x hx
      simp [hx]
    rw [lintegral_congr_ae h]
    simp
  have hle := localizedPullback_energy_le e he a (f - g) hC
  rw [hzero, mul_zero] at hle
  have hm := localizedPullback_stronglyMeasurable e a (f - g) ha (hf.sub hg)
  have hz := (lintegral_eq_zero_iff' (hm.enorm.pow_const 2).aemeasurable).mp
    (le_antisymm hle bot_le)
  filter_upwards [hz] with x hx
  have hx' : localizedPullback e a (f - g) x = 0 := by simpa using hx
  simpa only [localizedPullback_sub, Pi.sub_apply, sub_eq_zero] using hx'

theorem localizedPullback_memLp {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a : ℝ → 𝕜)
    (ha : Measurable a) {C : ℝ} (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2))
    (f : ℝ → 𝕜) (hf : StronglyMeasurable f) (hf2 : MemLp f 2 volume) :
    MemLp (localizedPullback e a f) 2 volume := by
  have hm : AEStronglyMeasurable (localizedPullback e a f) volume :=
    (localizedPullback_stronglyMeasurable e a f ha hf).aestronglyMeasurable
  have hle := localizedPullback_energy_le e he a f hC
  rw [← eLpNorm_two_sq _ hm, ← eLpNorm_two_sq _ hf2.aestronglyMeasurable] at hle
  have hfin : eLpNorm (localizedPullback e a f) 2 volume ^ (2 : ℕ) < ⊤ :=
    hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top_iff.mpr (Or.inl hf2)))
  exact (ENNReal.pow_lt_top_iff.mp hfin).resolve_right (by decide)

theorem localizedPullback_norm_toLp_le {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a : ℝ → 𝕜)
    (ha : Measurable a) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2))
    (f : Lp 𝕜 2 (volume : Measure ℝ)) :
    ‖(localizedPullback_memLp e he a ha hC f (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp
      (localizedPullback e a f)‖ ≤ C * ‖f‖ := by
  let hf := localizedPullback_memLp e he a ha hC f (Lp.stronglyMeasurable f) (Lp.memLp f)
  have hle := localizedPullback_energy_le e he a f hC
  rw [← eLpNorm_two_sq _ hf.aestronglyMeasurable,
    ← eLpNorm_two_sq _ (Lp.aestronglyMeasurable f)] at hle
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f))) hle
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg C)] at hreal
  rw [Lp.norm_toLp, Lp.norm_def]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg hC0 ENNReal.toReal_nonneg)).mp
  simpa only [mul_pow] using hreal

/-- The genuine localized scalar coordinate operator on whole-line L².
Its agreement on representatives is proved, rather than assumed. -/
def localizedL2Pullback {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a : ℝ → 𝕜)
    (ha : Measurable a) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2)) :
    Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ) := by
  let F (f : Lp 𝕜 2 (volume : Measure ℝ)) : Lp 𝕜 2 (volume : Measure ℝ) :=
    (localizedPullback_memLp e he a ha hC f (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp
      (localizedPullback e a f)
  have hF (f : Lp 𝕜 2 (volume : Measure ℝ)) :
      F f =ᵐ[volume] localizedPullback e a f := MemLp.coeFn_toLp _
  refine LinearMap.mkContinuous
    { toFun := F
      map_add' := ?_
      map_smul' := ?_ } C (localizedPullback_norm_toLp_le e he a ha hC0 hC)
  · intro f g
    apply Lp.ext
    have hadd := localizedPullback_congr_ae e he a ha hC
      ((f + g : Lp 𝕜 2 (volume : Measure ℝ)) : ℝ → 𝕜) (fun x => f x + g x) (Lp.stronglyMeasurable (f + g))
      ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)
    filter_upwards [hF (f + g), hF f, hF g, Lp.coeFn_add (F f) (F g), hadd]
      with x hx hxf hxg hxadd hcomp
    rw [hx, hcomp, hxadd, Pi.add_apply, hxf, hxg]
    exact congrFun (localizedPullback_add e a f g) x
  · intro c f
    simp only [RingHom.id_apply]
    apply Lp.ext
    have hsmul := localizedPullback_congr_ae e he a ha hC
      ((c • f : Lp 𝕜 2 (volume : Measure ℝ)) : ℝ → 𝕜) (fun x => c • f x) (Lp.stronglyMeasurable (c • f))
      ((Lp.stronglyMeasurable f).const_smul c) (Lp.coeFn_smul c f)
    filter_upwards [hF (c • f), hF f, Lp.coeFn_smul c (F f), hsmul]
      with x hx hxf hxsmul hcomp
    rw [hx, hcomp, hxsmul, Pi.smul_apply, hxf]
    exact congrFun (localizedPullback_smul e a f c) x

theorem localizedL2Pullback_apply_ae {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a : ℝ → 𝕜)
    (ha : Measurable a) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y ∈ e.target,
      ENNReal.ofReal |deriv e.symm y| * ‖a (e.symm y)‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2))
    (f : Lp 𝕜 2 (volume : Measure ℝ)) :
    localizedL2Pullback e he a ha hC0 hC f =ᵐ[volume] localizedPullback e a f :=
  (localizedPullback_memLp e he a ha hC f (Lp.stronglyMeasurable f) (Lp.memLp f)).coeFn_toLp

theorem localized_energy :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedEnergyType := by
  intro 𝕜 _ e he a f
  exact localizedPullback_energy e he a f

theorem localized_L2 :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedL2Type := by
  intro 𝕜 _ e he a ha hcompact hsupp
  have hd : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y := by
    intro y hy
    exact (he.differentiableOn (by norm_num) y hy).differentiableAt
      (e.open_target.mem_nhds hy)
  obtain ⟨C, hC1, hC⟩ := localizedPullback_jacobian_bound e a ha hcompact hsupp
    (he.continuousOn_deriv_of_isOpen e.open_target le_rfl)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  refine ⟨C, hC1, localizedL2Pullback e hd a ha.measurable hC0 hC, ⟨?_, ?_⟩, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hC0
    exact localizedPullback_norm_toLp_le e hd a ha.measurable hC0 hC
  · exact localizedL2Pullback_apply_ae e hd a ha.measurable hC0 hC
  · intro A hA
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hA.2 f).trans (localizedL2Pullback_apply_ae e hd a ha.measurable hC0 hC f).symm

section DualTransport
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F Eneg Fneg : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup Eneg] [NormedSpace 𝕜 Eneg]
variable [NormedAddCommGroup Fneg] [NormedSpace 𝕜 Fneg]

/-- Transfer the Banach transpose through specified scalar-linear dualities.
This helper does not assert existence of a bounded coordinate operator. -/
def transportTranspose (eE : Eneg ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜))
    (eF : Fneg ≃ₗᵢ[𝕜] (F →L[𝕜] 𝕜)) (A : E →L[𝕜] F) :
    Fneg →L[𝕜] Eneg :=
  eE.symm.toLinearIsometry.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜 E F 𝕜).flip A).comp
      eF.toLinearIsometry.toContinuousLinearMap)

@[simp] theorem transportTranspose_pairing
    (eE : Eneg ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜)) (eF : Fneg ≃ₗᵢ[𝕜] (F →L[𝕜] 𝕜))
    (A : E →L[𝕜] F) (u : E) (v : Fneg) :
    eE (transportTranspose eE eF A v) u = eF v (A u) := by
  simp [transportTranspose]

theorem transportTranspose_norm_le
    (eE : Eneg ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜)) (eF : Fneg ≃ₗᵢ[𝕜] (F →L[𝕜] 𝕜))
    (A : E →L[𝕜] F) : ‖transportTranspose eE eF A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  calc
    ‖transportTranspose eE eF A v‖ = ‖(eF v).comp A‖ := by
      simp [transportTranspose]
    _ ≤ ‖eF v‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A‖ * ‖v‖ := by rw [eF.norm_map]; exact mul_comm _ _

theorem transportTranspose_unique
    (eE : Eneg ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜)) (eF : Fneg ≃ₗᵢ[𝕜] (F →L[𝕜] 𝕜))
    (A : E →L[𝕜] F) (B : Fneg →L[𝕜] Eneg)
    (hB : ∀ u v, eE (B v) u = eF v (A u)) :
    B = transportTranspose eE eF A := by
  ext v
  apply eE.injective
  ext u
  rw [transportTranspose_pairing, hB]

/-- The inverse of a transported transpose is the transported transpose of the
inverse. This is purely scalar-linear duality, without an antidual. -/
def transportTransposeEquiv (eE : Eneg ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜))
    (eF : Fneg ≃ₗᵢ[𝕜] (F →L[𝕜] 𝕜)) (A : E ≃L[𝕜] F) : Fneg ≃L[𝕜] Eneg where
  toLinearMap := (transportTranspose eE eF A.toContinuousLinearMap).toLinearMap
  invFun := transportTranspose eF eE A.symm.toContinuousLinearMap
  left_inv v := by
    apply eF.injective
    ext u
    change eF (transportTranspose eF eE A.symm.toContinuousLinearMap
      (transportTranspose eE eF A.toContinuousLinearMap v)) u = eF v u
    simp only [transportTranspose_pairing, ContinuousLinearEquiv.coe_coe,
      A.apply_symm_apply]
  right_inv v := by
    apply eE.injective
    ext u
    change eE (transportTranspose eE eF A.toContinuousLinearMap
      (transportTranspose eF eE A.symm.toContinuousLinearMap v)) u = eE v u
    simp only [transportTranspose_pairing, ContinuousLinearEquiv.coe_coe,
      A.symm_apply_apply]
  continuous_toFun := (transportTranspose eE eF A.toContinuousLinearMap).continuous
  continuous_invFun := (transportTranspose eF eE A.symm.toContinuousLinearMap).continuous

end DualTransport

open FourierScale
open ExpandedFA.Fourier

theorem pairing_symmetry {d : ℕ} {s : ℝ} (u : Hs d s) (v : Hs d (-s)) :
    dualPairing (s := s) u v = dualPairing (s := -s) v u := by
  unfold dualPairing
  simp only [pairing_integrand]
  rw [← integral_neg_eq_self (fun ξ : Euclidean d =>
    coordinates d (-s) v ξ * coordinates d (-(-s)) u (-ξ)) volume]
  simp only [neg_neg, coordinates]
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact mul_comm _ _

theorem real_pairing_symmetry {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) :
    realDualPairing (s := s) u v = realDualPairing (s := -s) v u := by
  exact congrArg Complex.re
    (pairing_symmetry (s := s) (realCoordinates d s u) (realCoordinates d (-s) v))

theorem negative_transpose :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.negativeTransposeType := by
  intro d e s t A
  obtain ⟨eE, hE⟩ := duality d s
  obtain ⟨eF, hF⟩ := duality e t
  refine ⟨transportTranspose eE eF A, ⟨?_, transportTranspose_norm_le eE eF A⟩, ?_⟩
  · intro u v
    rw [← hE, ← hF]
    exact transportTranspose_pairing eE eF A u v
  · intro B hB
    apply transportTranspose_unique eE eF A B
    intro u v
    rw [hE, hF]
    exact hB.1 u v

theorem real_negative_transpose :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realNegativeTransposeType := by
  intro d e s t A
  obtain ⟨eE, hE⟩ := real_duality d s
  obtain ⟨eF, hF⟩ := real_duality e t
  refine ⟨transportTranspose eE eF A, ⟨?_, transportTranspose_norm_le eE eF A⟩, ?_⟩
  · intro u v
    rw [← hE, ← hF]
    exact transportTranspose_pairing eE eF A u v
  · intro B hB
    apply transportTranspose_unique eE eF A B
    intro u v
    rw [hE, hF]
    exact hB.1 u v

theorem negative_equivalence :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.negativeEquivalenceType := by
  intro d e s t A
  obtain ⟨eE, hE⟩ := duality d s
  obtain ⟨eF, hF⟩ := duality e t
  refine ⟨transportTransposeEquiv eE eF A, ?_,
    transportTranspose_norm_le eE eF A.toContinuousLinearMap,
    transportTranspose_norm_le eF eE A.symm.toContinuousLinearMap⟩
  intro u v
  rw [← hE, ← hF]
  exact transportTranspose_pairing eE eF A.toContinuousLinearMap u v

theorem real_negative_equivalence :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realNegativeEquivalenceType := by
  intro d e s t A
  obtain ⟨eE, hE⟩ := real_duality d s
  obtain ⟨eF, hF⟩ := real_duality e t
  refine ⟨transportTransposeEquiv eE eF A, ?_,
    transportTranspose_norm_le eE eF A.toContinuousLinearMap,
    transportTranspose_norm_le eF eE A.symm.toContinuousLinearMap⟩
  intro u v
  rw [← hE, ← hF]
  exact transportTranspose_pairing eE eF A.toContinuousLinearMap u v

theorem transpose_realization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.transposeRealizationType := by
  intro d e s t A B hB φ ψ u v hu hAu
  calc
    realization (s := -s) (B v) φ = dualPairing (s := -s) (B v) u := by
      symm
      apply pairing_test d (-s) (B v) φ u
      exact (congrArg (fun r : ℝ => @realization d r u) (neg_neg s)).trans hu
    _ = dualPairing (s := s) u (B v) := (pairing_symmetry u (B v)).symm
    _ = dualPairing (s := t) (A u) v := hB u v
    _ = dualPairing (s := -t) v (A u) := pairing_symmetry (A u) v
    _ = realization (s := -t) v ψ := by
      apply pairing_test e (-t) v ψ (A u)
      exact (congrArg (fun r : ℝ => @realization e r (A u)) (neg_neg t)).trans hAu

theorem real_transpose_realization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realTransposeRealizationType := by
  intro d e s t A B hB φ ψ u v hu hAu
  calc
    realRealization (s := -s) (B v) φ = realDualPairing (s := -s) (B v) u := by
      symm
      apply real_pairing_test (s := -s) (B v) φ u
      exact (congrArg (fun r : ℝ => @realRealization d r u) (neg_neg s)).trans hu
    _ = realDualPairing (s := s) u (B v) := (real_pairing_symmetry u (B v)).symm
    _ = realDualPairing (s := t) (A u) v := hB u v
    _ = realDualPairing (s := -t) v (A u) := real_pairing_symmetry (A u) v
    _ = realRealization (s := -t) v ψ := by
      apply real_pairing_test (s := -t) v ψ (A u)
      exact (congrArg (fun r : ℝ => @realRealization e r (A u)) (neg_neg t)).trans hAu

theorem finite_localization_bound :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteLocalizationBoundType := by
  intro 𝕜 _ E _ _ m n a b T h
  calc
    ∑ i, ‖a i‖ ≤ ∑ i, ∑ j, ‖T i j‖ * ‖b j‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [h i]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (T i j).le_opNorm _)
    _ ≤ ∑ i, ∑ j, ‖T i j‖ * ∑ k, ‖b k‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum (fun k _ => norm_nonneg (b k)) (Finset.mem_univ j)
    _ = (∑ i, ∑ j, ‖T i j‖) * ∑ j, ‖b j‖ := by simp_rw [Finset.sum_mul]

end ExpandedFA.Sobolev.Curve

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace ExpandedFA.Sobolev.Curve

theorem localizedPullback_tsupport_subset {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f : ℝ → 𝕜) :
    tsupport (localizedPullback e a f) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  by_contra hxa
  have : a x = 0 := by simpa only [Function.mem_support, not_not] using hxa
  exact hx (by simp [localizedPullback, this])

theorem localizedPullback_contDiff {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (he : ContDiffOn ℝ ∞ e e.source)
    (a f : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (hsupp : tsupport a ⊆ e.source) :
    ContDiff ℝ ∞ (localizedPullback e a f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport a
  · have hxs := hsupp hx
    have hcomp := hf.contDiffAt.comp x ((he x hxs).contDiffAt (e.open_source.mem_nhds hxs))
    apply (ha.contDiffAt.mul hcomp).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hxs] with y hy
    simp [localizedPullback, hy]
  · apply (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp [localizedPullback, hy]

theorem localizedPullback_hasCompactSupport {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f : ℝ → 𝕜) (ha : HasCompactSupport a) :
    HasCompactSupport (localizedPullback e a f) :=
  ha.of_isClosed_subset (isClosed_tsupport _) (localizedPullback_tsupport_subset e a f)

-- Check derivative nonvanishing from both directions, rather than add a certificate.
theorem inverse_deriv_ne_zero (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ x ∈ e.source, DifferentiableAt ℝ e x)
    (hi : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y)
    {y : ℝ} (hy : y ∈ e.target) : deriv e.symm y ≠ 0 := by
  have hcomp := (he (e.symm y) (e.symm.map_source hy)).hasDerivAt.comp y (hi y hy).hasDerivAt
  have hid : (fun z => e (e.symm z)) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hval := hcomp.congr_of_eventuallyEq hid.symm
  have hmul : deriv e (e.symm y) * deriv e.symm y = 1 := hval.unique (hasDerivAt_id y)
  exact right_ne_zero_of_mul_eq_one hmul


theorem localizedDensity_tsupport_subset {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a φ : ℝ → 𝕜)
    (hcompact : HasCompactSupport a) (hsupp : tsupport a ⊆ e.source) :
    tsupport (localizedDensity e a φ) ⊆ e '' tsupport a := by
  have hk : IsCompact (e '' tsupport a) :=
    hcompact.image_of_continuousOn (e.continuousOn.mono hsupp)
  apply closure_minimal _ hk.isClosed
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra ht
    exact hy (by simp [localizedDensity, ht])
  have ha0 : a (e.symm y) ≠ 0 := by
    intro hz
    exact hy (by simp [localizedDensity, inverseDensity, hz])
  exact ⟨e.symm y, subset_tsupport a ha0, e.right_inv hyt⟩

theorem localizedDensity_contDiff {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a φ : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport a) (hsupp : tsupport a ⊆ e.source) :
    ContDiff ℝ ∞ (localizedDensity e a φ) := by
  have hn : ∀ y ∈ e.target, deriv e.symm y ≠ 0 := by
    intro y hy
    apply inverse_deriv_ne_zero e _ _ hy
    · intro x hx
      exact (he.differentiableOn (by simp) x hx).differentiableAt (e.open_source.mem_nhds hx)
    · intro z hz
      exact (hi.differentiableOn (by simp) z hz).differentiableAt (e.open_target.mem_nhds hz)
  have hd : ContDiffOn ℝ ∞ (fun y => |deriv e.symm y|) e.target :=
    (hi.deriv_of_isOpen e.open_target (by simp)).abs hn
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport (localizedDensity e a φ)
  · obtain ⟨x, hx, rfl⟩ := localizedDensity_tsupport_subset e a φ hcompact hsupp hy
    have hyt := e.map_source (hsupp hx)
    have hsi := (hi (e x) hyt).contDiffAt (e.open_target.mem_nhds hyt)
    have hc : ContDiffAt ℝ ∞ (inverseDensity e (a * φ)) (e x) :=
      ((hd (e x) hyt).contDiffAt (e.open_target.mem_nhds hyt)).smul
        ((ha.mul hφ).contDiffAt.comp _ hsi)
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hyt] with z hz
    simp [localizedDensity, hz]
  · exact (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hy)

theorem localizedDensity_hasCompactSupport {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a φ : ℝ → 𝕜)
    (hcompact : HasCompactSupport a) (hsupp : tsupport a ⊆ e.source) :
    HasCompactSupport (localizedDensity e a φ) :=
  (hcompact.image_of_continuousOn (e.continuousOn.mono hsupp)).of_isClosed_subset
    (isClosed_tsupport _) (localizedDensity_tsupport_subset e a φ hcompact hsupp)

theorem localizedPullback_pairing {𝕜 : Type} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) (a f φ : ℝ → 𝕜) :
    (∫ x, localizedPullback e a f x * φ x) = ∫ y, f y * localizedDensity e a φ y := by
  have h1 : (fun x => localizedPullback e a f x * φ x) =
      e.source.indicator (fun x => f (e x) * (a x * φ x)) := by
    ext x
    by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx, mul_left_comm, mul_comm, mul_assoc]
  have h2 : (fun y => f y * localizedDensity e a φ y) =
      e.target.indicator (fun y => f y * inverseDensity e (a * φ) y) := by
    ext y
    by_cases hy : y ∈ e.target <;> simp [localizedDensity, hy]
  rw [h1, h2, integral_indicator e.open_source.measurableSet,
    integral_indicator e.open_target.measurableSet]
  exact density_pairing 𝕜 e he f (a * φ)

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
open scoped SchwartzMap

theorem contDiff_indicator_of_support {𝕜 : Type*} [RCLike 𝕜]
    (s : Set ℝ) (hs : IsOpen s) (a : ℝ → 𝕜) (ha : ContDiffOn ℝ ∞ a s)
    (hsub : tsupport (s.indicator a) ⊆ s) : ContDiff ℝ ∞ (s.indicator a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (s.indicator a)
  · have hxs := hsub hx
    apply ((ha x hxs).contDiffAt (hs.mem_nhds hxs)).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hxs] with y hy
    simp [hy]
  · exact (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)

theorem global_extension_of_cutoff (s : Set ℝ) (hs : IsOpen s)
    (g χ : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g s) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ s) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h.HasTemperateGrowth ∧
      (∀ x, χ x = 1 → h x = g x) ∧
      ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖h x‖) ^ k := by
  let d := s.indicator (fun x => χ x * (g x - x))
  have hdsub : tsupport d ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra hxχ
    have hxχ : χ x = 0 := by simpa only [Function.mem_support, not_not] using hxχ
    exact hx (by simp [d, hxχ])
  have hdc : HasCompactSupport d :=
    hc.of_isClosed_subset (isClosed_tsupport d) hdsub
  have hdd : ContDiff ℝ ∞ d := contDiff_indicator_of_support s hs _
    (hχ.contDiffOn.mul (hg.sub contDiffOn_id)) (hdsub.trans hsub)
  let h : ℝ → ℝ := id + d
  have hht : h.HasTemperateGrowth := by
    exact (show Function.HasTemperateGrowth (id : ℝ → ℝ) from by fun_prop).add
      (hdc.hasTemperateGrowth hdd)
  refine ⟨h, contDiff_id.add hdd, hht, ?_, ?_⟩
  · intro x hxχ
    have hxs : x ∈ s := hsub (subset_tsupport χ (by simp [hxχ]))
    simp [h, d, hxs, hxχ]
  · obtain ⟨B, hB⟩ := hdd.continuous.norm.bddAbove_range_of_hasCompactSupport hdc.norm
    refine ⟨1, max 1 B, ?_⟩
    intro x
    have hb : ‖d x‖ ≤ max 1 B := (hB (mem_range_self x)).trans (le_max_right _ _)
    have hnorm : ‖x‖ ≤ ‖h x‖ + ‖d x‖ := by
      have hid : x = h x - d x := by simp [h]
      calc
        ‖x‖ = ‖h x - d x‖ := congrArg norm hid
        _ ≤ ‖h x‖ + ‖d x‖ := norm_sub_le _ _
    have hB1 : 1 ≤ max 1 B := le_max_left _ _
    simp only [pow_one]
    nlinarith [norm_nonneg (h x)]

end ExpandedFA.Sobolev.Curve

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap
namespace ExpandedFA.Sobolev.Curve

-- Generic extension requires a compact cutoff; this lemma uses the compact/open Urysohn construction.
theorem compact_smoothCutoff {K U : Set ℝ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨V, hV, hKV, hVL⟩ := hK.exists_isOpen_closure_subset
    (show interior L ∈ 𝓝ˢ K from isOpen_interior.mem_nhdsSet.mpr hKL)
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff hV hK.isClosed hKV (n := ⊤)
  have hsup : tsupport χ ⊆ L := by
    rw [tsupport, hχs]
    exact hVL.trans interior_subset
  refine ⟨χ, hχ, hL.of_isClosed_subset (isClosed_tsupport _) hsup,
    hsup.trans hLU, ?_⟩
  intro x hx
  exact (hχ1 x).mp hx

theorem localizedSchwartzPullback_exists {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (he : ContDiffOn ℝ ∞ e e.source)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source) :
    ∃ P : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜,
      ∀ φ x, P φ x = localizedPullback e a φ x := by
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := compact_smoothCutoff hc e.open_source hs
  obtain ⟨h, hh, hht, hheq, hhgrowth⟩ :=
    global_extension_of_cutoff e.source e.open_source e χ he hχ hχc hχs
  let P : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜 :=
    (SchwartzMap.smulLeftCLM 𝕜 a).comp (SchwartzMap.compCLM 𝕜 hht hhgrowth)
  refine ⟨P, ?_⟩
  intro φ x
  change (SchwartzMap.smulLeftCLM 𝕜 a (SchwartzMap.compCLM 𝕜 hht hhgrowth φ)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth ha)]
  change a x * φ (h x) = _
  by_cases hx : x ∈ tsupport a
  · rw [hheq x (hχ1 x hx)]
    simp [localizedPullback, hs hx]
  · have hax := image_eq_zero_of_notMem_tsupport hx
    by_cases hxs : x ∈ e.source <;> simp [localizedPullback, hax, hxs]

theorem localizedSchwartzDensity_exists {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source) :
    ∃ Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜,
      ∀ φ x, Q φ x = localizedDensity e a φ x := by
  let K := e '' tsupport a
  have hK : IsCompact K := hc.image_of_continuousOn (e.continuousOn.mono hs)
  have hKt : K ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := compact_smoothCutoff hK e.open_target hKt
  obtain ⟨h, hh, hht, hheq, hhgrowth⟩ :=
    global_extension_of_cutoff e.target e.open_target e.symm χ hi hχ hχc hχs
  let q := localizedDensity e a (1 : ℝ → 𝕜)
  have hqc : HasCompactSupport q := localizedDensity_hasCompactSupport e a 1 hc hs
  have hqd : ContDiff ℝ ∞ q := localizedDensity_contDiff e he hi a 1 ha contDiff_const hc hs
  let Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜 :=
    (SchwartzMap.smulLeftCLM 𝕜 q).comp (SchwartzMap.compCLM 𝕜 hht hhgrowth)
  refine ⟨Q, ?_⟩
  intro φ x
  change (SchwartzMap.smulLeftCLM 𝕜 q (SchwartzMap.compCLM 𝕜 hht hhgrowth φ)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (hqc.hasTemperateGrowth hqd)]
  change q x * φ (h x) = _
  by_cases hx : x ∈ K
  · rw [hheq x (hχ1 x hx)]
    simp [q, localizedDensity, inverseDensity, hKt hx, Algebra.smul_mul_assoc]
  · have ha0 : a (e.symm x) = 0 ∨ x ∉ e.target := by
      by_cases hxt : x ∈ e.target
      · left
        by_contra ha0
        exact hx ⟨e.symm x, subset_tsupport a ha0, e.right_inv hxt⟩
      · exact Or.inr hxt
    rcases ha0 with ha0 | ha0
    · by_cases hxt : x ∈ e.target <;> simp [q, localizedDensity, inverseDensity, ha0, hxt]
    · simp [q, localizedDensity, ha0]

end ExpandedFA.Sobolev.Curve

noncomputable section
open Set ChartedSpace IsManifold Filter
open scoped Topology
open scoped Manifold ContDiff

namespace ExpandedFA.Sobolev.Curve

universe u
variable (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

namespace FiniteChartPartition
variable {M}

theorem source_cover (A : FiniteChartPartition M) :
    ⋃ i, (A.chart i).source = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  by_contra hx
  have hn (i : Fin A.n) : A.cutoff i x = 0 := by
    by_contra hn
    have hs : x ∈ tsupport (A.cutoff i) := subset_closure hn
    exact hx (mem_iUnion.mpr ⟨i, A.subordinate i hs⟩)
  have := A.sum_one x
  simp only [hn, Finset.sum_const_zero] at this
  exact zero_ne_one this

end FiniteChartPartition

/-- Compact smooth curves admit finite smooth chart partitions. -/
theorem exists_finiteChartPartition [T2Space M] [CompactSpace M] :
    Nonempty (FiniteChartPartition M) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt ℝ x).source)
    (fun x => (chartAt ℝ x).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source ℝ x⟩)
  let κ := {x : M // x ∈ s}
  let U : κ → Set M := fun i => (chartAt ℝ i.val).source
  have hcover : (univ : Set M) ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hy', hxy⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨y, hy'⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ)) isClosed_univ U (fun i => (chartAt ℝ i.val).open_source) hcover
  let q : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨{
    n := Fintype.card κ
    chart := fun i => chartAt ℝ (q i).val
    chart_smooth := fun i => chart_mem_maximalAtlas (q i).val
    cutoff := fun i => ρ (q i)
    nonneg := fun i x => ρ.nonneg (q i) x
    sum_one := ?_
    subordinate := fun i => hρ (q i) }⟩
  intro x
  calc
    ∑ i, ρ (q i) x = ∑ j, ρ j x := Equiv.sum_comp q (fun i => ρ i x)
    _ = ∑ᶠ j, ρ j x := (finsum_eq_sum_of_fintype _).symm
    _ = 1 := ρ.sum_eq_one (mem_univ x)


namespace FiniteChartPartition
variable {M}

theorem cutoff_hasCompactSupport [CompactSpace M] (A : FiniteChartPartition M)
    (i : Fin A.n) : HasCompactSupport (A.cutoff i) :=
  HasCompactSupport.of_compactSpace _

theorem transition_smooth (A B : FiniteChartPartition M) (i : Fin A.n) (j : Fin B.n) :
    ContDiffOn ℝ ∞ (A.transition B i j) (A.transition B i j).source := by
  exact (contMDiffOn_of_mem_contDiffGroupoid
    (compatible_of_mem_maximalAtlas (A.chart_smooth i) (B.chart_smooth j))).contDiffOn

theorem transition_symm_smooth (A B : FiniteChartPartition M)
    (i : Fin A.n) (j : Fin B.n) :
    ContDiffOn ℝ ∞ (A.transition B i j).symm (A.transition B i j).target := by
  exact (contMDiffOn_of_mem_contDiffGroupoid
    (compatible_of_mem_maximalAtlas (B.chart_smooth j) (A.chart_smooth i))).contDiffOn

end FiniteChartPartition

/-- A smooth compact cutoff exists around every compact set inside an open set.
The value is one on a whole neighborhood, and full topological support is inside U. -/
theorem exists_smoothCutoff [T2Space M] [CompactSpace M]
    {K U : Set M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ K, f x = 1) ∧ tsupport f ⊆ U ∧
      (∀ x, f x ∈ Icc 0 1) ∧ HasCompactSupport f := by
  obtain ⟨f, h0, h1, hf⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ)) hU.isClosed_compl hK
    (Set.disjoint_left.mpr (fun x hxc hxK => hxc (hKU hxK))) (n := ⊤)
  refine ⟨f, h1, ?_, hf, HasCompactSupport.of_compactSpace _⟩
  intro x hx
  by_contra hxu
  have hz : ∀ᶠ y in 𝓝 x, f y = 0 := h0.filter_mono (nhds_le_nhdsSet hxu)
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx

/-- An overlap cutoff is derived from the compact chart supports; it is not
an extra hypothesis on atlases or their overlaps. Empty overlaps are allowed. -/
theorem exists_overlapCutoff [T2Space M] [CompactSpace M]
    (A B : FiniteChartPartition M) (i : Fin A.n) (j : Fin B.n) :
    ∃ f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ (tsupport (A.cutoff i) ∩ tsupport (B.cutoff j)), f x = 1) ∧
      tsupport f ⊆ (A.chart i).source ∩ (B.chart j).source ∧
      (∀ x, f x ∈ Icc 0 1) ∧ HasCompactSupport f := by
  apply exists_smoothCutoff M (isClosed_tsupport _ |>.inter (isClosed_tsupport _))
    ((A.chart i).open_source.inter (B.chart j).open_source)
  exact inter_subset_inter (A.subordinate i) (B.subordinate j)


/-- Restriction to an open chart keeps compact support when the ambient
full support is contained in that chart. -/
theorem compactSupport_restrict {N : Type*} [TopologicalSpace N]
    {𝕜 : Type*} [RCLike 𝕜] {f : N → 𝕜} (hf : HasCompactSupport f) {U : Set N} (hU : tsupport f ⊆ U) :
    HasCompactSupport (fun x : U => f x.val) := by
  have hc : IsCompact ((Subtype.val : U → N) ⁻¹' tsupport f) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hf (by simpa using hU)
  exact hc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage f continuous_subtype_val)

/-- Inverse-chart transport of a compactly supported scalar function has
compact support as a function on the coordinate target. -/
theorem compactSupport_in_chart [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (e : OpenPartialHomeomorph M ℝ) (f : M → 𝕜)
    (h : tsupport f ⊆ e.source) :
    HasCompactSupport (fun y : e.target => f (e.symm y)) := by
  exact (compactSupport_restrict (HasCompactSupport.of_compactSpace f) h).comp_homeomorph
    e.toHomeomorphSourceTarget.symm


/-- A smooth scalar function supported in a chart becomes a genuine
whole-line test function supported inside the chart target. -/
def chartTest [T2Space M] [CompactSpace M] {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph M ℝ) (he : e ∈ maximalAtlas (𝓘(ℝ)) ∞ M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (hs : tsupport f ⊆ e.source) :
    TestFunction (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens ℝ) 𝕜 ⊤ := by
  let V : TopologicalSpace.Opens ℝ := ⟨e.target, e.open_target⟩
  let g : V → 𝕜 := fun y => f (e.symm y)
  have hg : ContMDiff (𝓘(ℝ)) (𝓘(ℝ, 𝕜)) ∞ g := by
    intro y
    change ContMDiffAt (𝓘(ℝ)) (𝓘(ℝ, 𝕜)) ∞ (fun y : V => (fun z : ℝ => f (e.symm z)) y.val) y
    apply (contMDiffAt_subtype_iff (U := V) (f := fun z : ℝ => f (e.symm z))).mpr
    exact f.contMDiff.contMDiffAt.comp y.val (contMDiffAt_symm_of_mem_maximalAtlas he y.property)
  have hc : HasCompactSupport g := compactSupport_in_chart M e f hs
  refine {
    toFun := (Subtype.val : V → ℝ).extend g 0
    contDiff' := contMDiff_iff_contDiff.mp (hg.extend_zero hc)
    hasCompactSupport' := hc.extend_zero continuous_subtype_val
    tsupport_subset' := ?_ }
  exact (hc.tsupport_extend_zero_subset continuous_subtype_val).trans (Subtype.coe_image_subset _ _)

@[simp] theorem chartTest_apply [T2Space M] [CompactSpace M] {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph M ℝ) (he : e ∈ maximalAtlas (𝓘(ℝ)) ∞ M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (hs : tsupport f ⊆ e.source)
    (y : ℝ) (hy : y ∈ e.target) : chartTest M e he f hs y = f (e.symm y) := by
  change (Subtype.val : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens ℝ) → ℝ).extend
    (fun y => f (e.symm y)) 0 (⟨y, hy⟩ : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens ℝ)) = _
  exact Subtype.val_injective.extend_apply _ _ _


/-- A scalar chart-supported smooth function has one and only one coordinate
test function on the full line, with actual pointwise coordinate formula. -/
theorem chartTest_exists_unique [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph M ℝ) (he : e ∈ maximalAtlas (𝓘(ℝ)) ∞ M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (hs : tsupport f ⊆ e.source) :
    ∃! φ : TestFunction (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens ℝ) 𝕜 ⊤,
      ∀ y ∈ e.target, φ y = f (e.symm y) := by
  refine ⟨chartTest M e he f hs, ?_, ?_⟩
  · exact chartTest_apply M e he f hs
  · intro ψ hψ
    ext y
    by_cases hy : y ∈ e.target
    · exact (hψ y hy).trans (chartTest_apply M e he f hs y hy).symm
    · rw [ψ.zero_on_compl hy, (chartTest M e he f hs).zero_on_compl hy]

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

theorem finite_chart_partition :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteChartPartitionType := by
  intro M _ _ _ _ _
  exact exists_finiteChartPartition M

theorem chart_transition_smooth :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.chartTransitionSmoothType := by
  intro M _ _ _ A B i j
  exact ⟨A.transition_smooth B i j, A.transition_symm_smooth B i j⟩

theorem overlap_cutoff :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.overlapCutoffType := by
  intro M _ _ _ _ _ A B i j
  exact exists_overlapCutoff M A B i j

theorem chart_test :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.chartTestType := by
  intro M _ _ _ _ _ 𝕜 _ e he f hs
  exact chartTest_exists_unique M e he f hs

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
lemma differenceKernel_comp_le {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (hp : 0 ≤ p) (f : ℝ → E) (e : ℝ → ℝ) (L : ℝ)
    (hL : 0 < L) (x y : ℝ)
    (h : |e x - e y| ≤ L * |x - y|) :
    differenceKernel p (f ∘ e) x y ≤
      ENNReal.ofReal (L ^ p) * differenceKernel p f (e x) (e y) := by
  by_cases he : e x = e y
  · simp [differenceKernel, he]
  have hxy : x ≠ y := by intro H; simp [H] at he
  have hxyp : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hexyp : 0 < |e x-e y| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hh : |e x - e y| ^ p ≤ L ^ p * |x-y| ^ p := by
    simpa only [Real.mul_rpow hL.le hxyp.le] using Real.rpow_le_rpow hexyp.le h hp
  have hd : ‖f (e x) - f (e y)‖ ^ 2 / |x-y| ^ p ≤
      L ^ p * (‖f (e x) - f (e y)‖ ^ 2 / |e x-e y| ^ p) := by
    have h₁ := Real.rpow_pos_of_pos hxyp p
    have h₂ := Real.rpow_pos_of_pos hexyp p
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ h₁ h₂).mpr
    have H := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖f (e x)-f (e y)‖)
    nlinarith
  simpa only [differenceKernel, Function.comp_def,
    ENNReal.ofReal_mul (Real.rpow_nonneg hL.le p)] using ENNReal.ofReal_le_ofReal hd

lemma double_lintegral_change (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y)
    (g : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ x in e.source, ∫⁻ y in e.source, g x y) =
      ∫⁻ X in e.target, ∫⁻ Y in e.target,
        ENNReal.ofReal |deriv e.symm X| * ENNReal.ofReal |deriv e.symm Y| *
          g (e.symm X) (e.symm Y) := by
  have change (h : ℝ → ℝ≥0∞) :
      (∫⁻ x in e.source, h x) =
        ∫⁻ X in e.target, ENNReal.ofReal |deriv e.symm X| * h (e.symm X) := by
    simpa only [e.symm_image_target_eq_source] using
      lintegral_image_eq_lintegral_abs_deriv_mul e.open_target.measurableSet
        (fun x hx => (he x hx).hasDerivAt.hasDerivWithinAt) e.symm.injOn h
  rw [change]
  apply lintegral_congr
  intro X
  rw [change (g (e.symm X)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  ext Y
  exact (mul_assoc _ _ _).symm

lemma differenceEnergy_comp_le {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (hp : 0 ≤ p) (f : ℝ → E)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y)
    (L J : ℝ) (hL : 0 < L) (hJ : 0 ≤ J)
    (hLip : ∀ x ∈ e.source, ∀ y ∈ e.source, |e x - e y| ≤ L * |x-y|)
    (hJac : ∀ y ∈ e.target, |deriv e.symm y| ≤ J) :
    differenceEnergy p (f ∘ e) e.source ≤
      ENNReal.ofReal (J ^ 2 * L ^ p) * differenceEnergy p f e.target := by
  unfold differenceEnergy
  rw [double_lintegral_change e he]
  calc
    _ ≤ ∫⁻ X in e.target, ∫⁻ Y in e.target,
        ENNReal.ofReal (J ^ 2 * L ^ p) * differenceKernel p f X Y := by
      apply setLIntegral_mono' e.open_target.measurableSet
      intro X hX
      apply setLIntegral_mono' e.open_target.measurableSet
      intro Y hY
      have hk := differenceKernel_comp_le p hp f e L hL (e.symm X) (e.symm Y)
        (hLip (e.symm X) (e.map_target hX) (e.symm Y) (e.map_target hY))
      simp only [e.right_inv hX, e.right_inv hY] at hk
      have hjX := ENNReal.ofReal_le_ofReal (hJac X hX)
      have hjY := ENNReal.ofReal_le_ofReal (hJac Y hY)
      calc
        _ ≤ (ENNReal.ofReal J * ENNReal.ofReal J) *
            (ENNReal.ofReal (L ^ p) * differenceKernel p f X Y) :=
          mul_le_mul' (mul_le_mul' hjX hjY) hk
        _ = _ := by
          rw [ENNReal.ofReal_mul (sq_nonneg J), ENNReal.ofReal_pow hJ]
          ring
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


end ExpandedFA.Sobolev.Curve

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier
lemma fourier_translate_difference {d : ℕ} (f : Euclidean d → ℂ)
    (hf : Integrable f) (h ξ : Euclidean d) :
    𝓕 (fun x => f (x + h) - f x) ξ =
      ((Real.fourierChar (inner ℝ h ξ) : ℂ) - 1) * 𝓕 f ξ := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (Euclidean d)) f h) ξ
  have h1 := (Real.fourierIntegral_convergent_iff ξ).mpr (hf.comp_add_right h)
  have h2 := (Real.fourierIntegral_convergent_iff ξ).mpr hf
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • (f (x + h) - f x)) = _
  simp_rw [smul_sub]
  rw [integral_sub h1 h2]
  change (VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (Euclidean d)) (f ∘ fun x => x + h) ξ) - 𝓕 f ξ = _
  rw [ht]
  change (Real.fourierChar (inner ℝ h ξ) : ℂ) * 𝓕 f ξ - 𝓕 f ξ = _
  ring
lemma translation_difference_parseval {d : ℕ} (f : Euclidean d → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2) (h : Euclidean d) :
    (∫ x, ‖f (x + h) - f x‖ ^ 2) =
      ∫ ξ, ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have ht : MemLp (fun x => f (x + h) - f x) 2 :=
    (h2.comp_measurePreserving (measurePreserving_add_right volume h)).sub h2
  have hp := ExpandedFA.Fourier.Plancherel.classical_norm d
    (fun x => f (x + h) - f x) ((h1.comp_add_right h).sub h1) ht
  rw [← hp]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [ExpandedFA.Fourier.integralFourier_eq_native,
    fourier_translate_difference f h1 h ξ, norm_mul, mul_pow]
lemma translation_difference_lintegral {d : ℕ} (f : Euclidean d → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2) (h : Euclidean d) :
    (∫⁻ x, ‖f (x + h) - f x‖ₑ ^ 2) =
      ∫⁻ ξ, ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ₑ ^ 2 * ‖𝓕 f ξ‖ₑ ^ 2 := by
  let g := fun x => f (x + h) - f x
  have hg1 : Integrable g := (h1.comp_add_right h).sub h1
  have hg2 : MemLp g 2 :=
    (h2.comp_measurePreserving (measurePreserving_add_right volume h)).sub h2
  have hgF := ExpandedFA.Fourier.Plancherel.integral_memLp d g hg1 hg2
  have hp := congrArg ENNReal.ofReal
    (ExpandedFA.Fourier.Plancherel.classical_norm d g hg1 hg2)
  rw [ofReal_integral_eq_lintegral_ofReal (hgF.integrable_norm_pow (by norm_num))
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal (hg2.integrable_norm_pow (by norm_num))
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at hp
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hp
  rw [← hp]
  apply lintegral_congr
  intro ξ
  rw [ExpandedFA.Fourier.integralFourier_eq_native]
  change ‖𝓕 (fun x => f (x + h) - f x) ξ‖ₑ ^ 2 = _
  rw [fourier_translate_difference f h1 h ξ, enorm_mul, mul_pow]
lemma weighted_translation_difference_lintegral {d : ℕ} (f : Euclidean d → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2) (w : Euclidean d → ENNReal)
    (hw : Measurable w) :
    (∫⁻ h, w h * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ 2) =
      ∫⁻ ξ, (∫⁻ h, w h * ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ₑ ^ 2) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hphase : Continuous (fun p : Euclidean d × Euclidean d =>
      (Real.fourierChar (inner ℝ p.1 p.2) : ℂ) - 1) := by fun_prop
  have hF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  have hm : Measurable (fun p : Euclidean d × Euclidean d =>
      w p.1 * ‖(Real.fourierChar (inner ℝ p.1 p.2) : ℂ) - 1‖ₑ ^ 2 *
        ‖𝓕 f p.2‖ₑ ^ 2) :=
    ((hw.comp measurable_fst).mul (hphase.enorm.measurable.pow_const 2)).mul
      (((hF.comp continuous_snd).enorm.measurable).pow_const 2)
  calc
    _ = ∫⁻ h, ∫⁻ ξ, w h * ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ₑ ^ 2 *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
      apply lintegral_congr
      intro h
      rw [translation_difference_lintegral f h1 h2 h]
      rw [← lintegral_const_mul (w h)]
      · simp_rw [mul_assoc]
      · exact ((hphase.comp (continuous_const.prodMk continuous_id)).enorm.measurable.pow_const 2).mul
          (hF.enorm.measurable.pow_const 2)
    _ = ∫⁻ ξ, ∫⁻ h, w h * ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ₑ ^ 2 *
        ‖𝓕 f ξ‖ₑ ^ 2 := lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro ξ
      exact lintegral_mul_const _ ((hw.mul
        ((hphase.comp (continuous_id.prodMk continuous_const)).enorm.measurable.pow_const 2)))
end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

theorem localized_pairing :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedPairingType :=
  fun 𝕜 _ e he a f φ => localizedPullback_pairing e he a f φ

theorem localized_schwartz :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedSchwartzType := by
  intro 𝕜 _ e he hi a ha hc hs
  obtain ⟨P, hP⟩ := localizedSchwartzPullback_exists e he a ha hc hs
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  exact ⟨P, Q, hP, hQ⟩

theorem fractional_coordinate_bound :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalCoordinateType := by
  intro 𝕜 _ p hp f e he L J hL hJ hLip hJac
  exact differenceEnergy_comp_le p hp f e he L J hL hJ hLip hJac

theorem weighted_difference_fourier :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.weightedDifferenceFourierType := by
  intro d f h1 h2 w hw
  simpa only [ExpandedFA.Fourier.integralFourier_eq_native] using
    weighted_translation_difference_lintegral f h1 h2 w hw

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
lemma separated_rpow_bound (p δ d : ℝ) (hp : 0 ≤ p) (hδ : 0 < δ) (hd : δ ≤ d) :
    d ^ (-p) ≤ (1 + δ⁻¹) ^ p * (1 + d) ^ (-p) := by
  have hd0 : 0 < d := hδ.trans_le hd
  have hc : 0 < 1 + δ⁻¹ := by positivity
  have hb : 1 + d ≤ (1 + δ⁻¹) * d := by
    have H : 1 ≤ δ⁻¹ * d := (one_le_inv_mul₀ hδ).mpr hd
    nlinarith
  have H := Real.rpow_le_rpow (by positivity : 0 ≤ 1+d) hb hp
  rw [Real.mul_rpow hc.le hd0.le] at H
  rw [Real.rpow_neg hd0.le, Real.rpow_neg (by positivity : 0 ≤ 1+d)]
  simp only [inv_eq_one_div] at H ⊢
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hd0 p)
    (Real.rpow_pos_of_pos (by positivity : 0 < 1+d) p)).mpr (by simpa using H)


lemma uniform_tail_bound (p δ : ℝ) (hp : 1 < p) (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : ℝ,
      (∫⁻ y in {y : ℝ | δ ≤ |x-y|}, ENNReal.ofReal (|x-y| ^ (-p))) ≤ C := by
  let c := ENNReal.ofReal ((1 + δ⁻¹) ^ p)
  let w := fun t : ℝ => ENNReal.ofReal ((1 + |t|) ^ (-p))
  have hw : (∫⁻ t, w t) < ⊤ := by
    simpa only [w, Real.norm_eq_abs] using
      (finite_integral_one_add_norm (E := ℝ) (μ := volume) (by simpa using hp))
  refine ⟨c * ∫⁻ t, w t, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw, ?_⟩
  intro x
  calc
    _ ≤ ∫⁻ y in {y : ℝ | δ ≤ |x-y|}, c * w (x-y) := by
      apply setLIntegral_mono' (isClosed_le continuous_const (continuous_const.sub continuous_id).abs).measurableSet
      intro y hy
      change ENNReal.ofReal _ ≤ ENNReal.ofReal ((1 + δ⁻¹) ^ p) *
        ENNReal.ofReal ((1 + |x-y|) ^ (-p))
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : 0 ≤ 1+δ⁻¹) p)]
      exact ENNReal.ofReal_le_ofReal (separated_rpow_bound p δ |x-y| (by linarith) hδ hy)
    _ ≤ ∫⁻ y, c * w (x-y) := by simpa using (lintegral_mono_set (μ := volume) (f := fun y => c * w (x-y)) (subset_univ {y : ℝ | δ ≤ |x-y|}))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_sub_left_eq_self w x]


lemma compact_separation (K : Set ℝ) (hK : IsCompact K)
    (U : Set ℝ) (hU : IsOpen U) (hsub : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∉ U, δ ≤ |x-y| := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hsub
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  by_contra! H
  apply hy
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  exact ⟨x, hx, by simpa only [Real.dist_eq, abs_sub_comm] using H⟩

lemma compact_cross_energy_bound {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (hp : 1 < p) (K : Set ℝ) (hK : IsCompact K)
    (U : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g : ℝ → E, tsupport g ⊆ K →
      (∫⁻ x in U, ∫⁻ y in Uᶜ, differenceKernel p g x y) ≤
        C * ∫⁻ x in U, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨δ, hδ, hsep⟩ := compact_separation K hK U hU hKU
  obtain ⟨C, hC, htail⟩ := uniform_tail_bound p δ hp hδ
  refine ⟨C, hC, ?_⟩
  intro g hsub
  have gz (y : ℝ) (hy : y ∉ U) : g y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun H => hy (hKU (hsub H)))
  calc
    _ ≤ ∫⁻ x in U, C * ENNReal.ofReal (‖g x‖ ^ 2) := by
      apply setLIntegral_mono' hU.measurableSet
      intro x hx
      by_cases hxg : x ∈ tsupport g
      · have heq : (∫⁻ y in Uᶜ, differenceKernel p g x y) =
            ENNReal.ofReal (‖g x‖ ^ 2) *
              ∫⁻ y in Uᶜ, ENNReal.ofReal (|x-y| ^ (-p)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply setLIntegral_congr_fun hU.measurableSet.compl
          intro y hy
          simp only [differenceKernel, gz y hy, sub_zero, div_eq_mul_inv,
            Real.rpow_neg (abs_nonneg (x-y)), ENNReal.ofReal_mul (sq_nonneg ‖g x‖)]
        rw [heq, mul_comm C]
        apply mul_le_mul' le_rfl
        calc
          _ ≤ ∫⁻ y in {y : ℝ | δ ≤ |x-y|}, ENNReal.ofReal (|x-y| ^ (-p)) :=
            lintegral_mono_set (fun y hy => hsep x (hsub hxg) y hy)
          _ ≤ C := htail x
      · have hzero := image_eq_zero_of_notMem_tsupport hxg
        have heq : (∫⁻ y in Uᶜ, differenceKernel p g x y) = 0 := by
          apply setLIntegral_eq_zero hU.measurableSet.compl
          intro y hy
          simp [differenceKernel, hzero, gz y hy]
        simp only [heq, zero_le]
    _ = _ := lintegral_const_mul' _ _ hC.ne

lemma differenceKernel_symm {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (g : ℝ → E) (x y : ℝ) :
    differenceKernel p g x y = differenceKernel p g y x := by
  simp only [differenceKernel, norm_sub_rev (g x) (g y), abs_sub_comm x y]

lemma differenceEnergy_decomposition {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (g : ℝ → E) (hgc : Continuous g)
    (U : Set ℝ) (hU : IsOpen U) (hsub : tsupport g ⊆ U) :
    differenceEnergy p g univ = differenceEnergy p g U +
      2 * (∫⁻ x in U, ∫⁻ y in Uᶜ, differenceKernel p g x y) := by
  have hk : Measurable (Function.uncurry (differenceKernel p g)) := by
    unfold differenceKernel Function.uncurry
    have hc : Continuous fun z : ℝ × ℝ => ‖g z.1 - g z.2‖ :=
      ((hgc.comp continuous_fst).sub (hgc.comp continuous_snd)).norm
    exact ((hc.measurable.pow_const 2).div
      ((continuous_fst.sub continuous_snd).abs.measurable.pow_const p)).ennreal_ofReal
  have hinner (V : Set ℝ) : Measurable fun x => ∫⁻ y in V, differenceKernel p g x y :=
    hk.lintegral_prod_right
  have hz (y : ℝ) (hy : y ∈ Uᶜ) : g y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun H => hy (hsub H))
  have hcc : (∫⁻ x in Uᶜ, ∫⁻ y in Uᶜ, differenceKernel p g x y) = 0 := by
    apply setLIntegral_eq_zero hU.measurableSet.compl
    intro x hx
    apply setLIntegral_eq_zero hU.measurableSet.compl
    intro y hy
    simp [differenceKernel, hz x hx, hz y hy]
  have hcu : (∫⁻ x in Uᶜ, ∫⁻ y in U, differenceKernel p g x y) =
      ∫⁻ x in U, ∫⁻ y in Uᶜ, differenceKernel p g x y := by
    rw [lintegral_lintegral_swap hk.aemeasurable]
    apply setLIntegral_congr_fun hU.measurableSet
    intro x hx
    apply setLIntegral_congr_fun hU.measurableSet.compl
    intro y hy
    exact differenceKernel_symm p g y x
  unfold differenceEnergy
  simp only [Measure.restrict_univ]
  calc
    _ = ∫⁻ x, ((∫⁻ y in U, differenceKernel p g x y) +
        (∫⁻ y in Uᶜ, differenceKernel p g x y)) := by
      apply lintegral_congr
      intro x
      exact (lintegral_add_compl _ hU.measurableSet).symm
    _ = (∫⁻ x, ∫⁻ y in U, differenceKernel p g x y) +
        ∫⁻ x, ∫⁻ y in Uᶜ, differenceKernel p g x y :=
      lintegral_add_left (hinner U) _
    _ = ((∫⁻ x in U, ∫⁻ y in U, differenceKernel p g x y) +
          (∫⁻ x in Uᶜ, ∫⁻ y in U, differenceKernel p g x y)) +
        ((∫⁻ x in U, ∫⁻ y in Uᶜ, differenceKernel p g x y) +
          ∫⁻ x in Uᶜ, ∫⁻ y in Uᶜ, differenceKernel p g x y) := by
      rw [← lintegral_add_compl (fun x => ∫⁻ y in U, differenceKernel p g x y) hU.measurableSet,
        ← lintegral_add_compl (fun x => ∫⁻ y in Uᶜ, differenceKernel p g x y) hU.measurableSet]
    _ = _ := by rw [hcc, hcu]; ring


lemma compact_extension_energy_bound {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (hp : 1 < p) (K : Set ℝ) (hK : IsCompact K)
    (U : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g : ℝ → E, Continuous g → tsupport g ⊆ K →
      differenceEnergy p g univ ≤ differenceEnergy p g U +
        C * ∫⁻ x in U, ENNReal.ofReal (‖g x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := compact_cross_energy_bound (E := E) p hp K hK U hU hKU
  refine ⟨2 * C, ENNReal.mul_lt_top (by norm_num) hC, ?_⟩
  intro g hgc hsub
  rw [differenceEnergy_decomposition p g hgc U hU (hsub.trans hKU)]
  exact add_le_add le_rfl ((mul_le_mul' le_rfl (hbound g hsub)).trans_eq (mul_assoc _ _ _).symm)


end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
lemma phase_norm_le_linear (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
  rw [Real.fourierChar_apply, mul_comm _ Complex.I]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using h

lemma phase_norm_le_two (t : ℝ) :
    ‖(Real.fourierChar t : ℂ) - 1‖ ≤ 2 := by
  simpa only [Circle.norm_coe, norm_one, one_add_one_eq_two] using (norm_sub_le (Real.fourierChar t : ℂ) 1)

lemma fractionalKernel_near_bound (σ t : ℝ) (ht : t ≠ 0) :
    ‖fractionalKernel σ t‖ ≤ (2 * Real.pi) ^ 2 * |t| ^ (1 - 2 * σ) := by
  have ht0 : 0 < |t| := abs_pos.mpr ht
  have hp := sq_le_sq₀ (norm_nonneg ((Real.fourierChar t : ℂ) - 1))
    (by positivity : 0 ≤ 2 * Real.pi * |t|)
  have hb := hp.mpr (phase_norm_le_linear t)
  have he : (|t| ^ (2 : ℕ)) * |t| ^ (-1 - 2 * σ) = |t| ^ (1 - 2 * σ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_add ht0]
    congr 1
    ring
  rw [fractionalKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2 * Real.pi * |t|) ^ 2 * |t| ^ (-1 - 2 * σ) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (abs_nonneg _) _)
    _ = (2 * Real.pi) ^ 2 * (|t| ^ 2 * |t| ^ (-1 - 2 * σ)) := by ring
    _ = _ := by rw [he]

lemma fractionalKernel_far_bound (σ t : ℝ) :
    ‖fractionalKernel σ t‖ ≤ 4 * |t| ^ (-1 - 2 * σ) := by
  rw [fractionalKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  convert (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mpr (phase_norm_le_two t) using 1; norm_num

lemma fractionalKernel_measurable (σ : ℝ) : Measurable (fractionalKernel σ) := by
  unfold fractionalKernel
  fun_prop

lemma fractionalKernel_integrable (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Integrable (fractionalKernel σ) := by
  have hm : AEStronglyMeasurable (fractionalKernel σ) volume := (fractionalKernel_measurable σ).aestronglyMeasurable
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hnear : IntegrableOn (fractionalKernel σ) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (α := 2 * σ - 1) (C := (2 * Real.pi) ^ 2)
    · simp only [Module.finrank_self, Nat.cast_one]
      linarith
    · filter_upwards [ae_restrict_of_ae hne] with t ht
      simpa only [Real.norm_eq_abs, neg_sub, neg_mul, one_mul] using
        fractionalKernel_near_bound σ t ht
    · exact hm
  have htail_base : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(1 + 2 * σ))) := by
    apply integrable_one_add_norm
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hfar : IntegrableOn (fractionalKernel σ) (Metric.ball (0:ℝ) 1)ᶜ := by
    apply (htail_base.const_mul (4 * (2:ℝ) ^ (1 + 2 * σ))).integrableOn.mono' hm.restrict
    filter_upwards [self_mem_ae_restrict (Metric.isOpen_ball.measurableSet.compl)] with t ht
    have ht1 : 1 ≤ |t| := by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
    have hpos : 0 < (1 + |t|) / 2 := by positivity
    have hb := Real.rpow_le_rpow_of_nonpos hpos
      (show (1 + |t|) / 2 ≤ |t| by linarith) (show -1 - 2 * σ ≤ 0 by linarith)
    have he : ((1 + |t|) / 2) ^ (-1 - 2 * σ) =
        (2:ℝ) ^ (1 + 2 * σ) * (1 + |t|) ^ (-1 - 2 * σ) := by
      rw [Real.div_rpow (by positivity) (by norm_num)]
      rw [show -1 - 2 * σ = -(1 + 2 * σ) by ring,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have hb' := (fractionalKernel_far_bound σ t).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    rw [he] at hb'
    simpa only [Real.norm_eq_abs, neg_add, sub_eq_add_neg, mul_assoc] using hb'
  have hall := hnear.union hfar
  simpa only [Set.union_compl_self, integrableOn_univ] using hall
lemma fractionalKernel_integral_pos (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < ∫ t, fractionalKernel σ t := by
  have hnonneg : 0 ≤ fractionalKernel σ := by
    intro t
    unfold fractionalKernel
    positivity
  have hcont : ContinuousAt (fractionalKernel σ) (1 / 2) := by
    unfold fractionalKernel
    fun_prop (disch := norm_num)
  have hphase : (Real.fourierChar (1 / 2) : ℂ) = -1 := by
    rw [Real.fourierChar_apply, show 2 * Real.pi * (1 / 2) = Real.pi by ring,
      Complex.exp_pi_mul_I]
  have hvalue : fractionalKernel σ (1 / 2) ≠ 0 := by
    unfold fractionalKernel
    rw [hphase]
    apply mul_ne_zero
    · norm_num
    · exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  apply (integral_pos_iff_support_of_nonneg hnonneg
    (fractionalKernel_integrable σ hσ0 hσ1)).mpr
  exact volume.measure_pos_of_mem_nhds (hcont.eventually_ne hvalue)

end ExpandedFA.Sobolev.Curve

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ExpandedFA.Sobolev.Curve

theorem localizedDistribution_exists {𝕜 : Type} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source)
    (T : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜) :
    ∃! S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
      ∀ φ ψ : SchwartzMap ℝ 𝕜,
        (∀ x, ψ x = localizedDensity e a φ x) → S φ = T ψ := by
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  refine ⟨T.comp Q, ?_, ?_⟩
  · intro φ ψ hψ
    have hq : Q φ = ψ := SchwartzMap.ext (fun x => (hQ φ x).trans (hψ x).symm)
    change T (Q φ) = T ψ
    rw [hq]
  · intro S hS
    apply ContinuousLinearMap.ext
    intro φ
    exact hS φ (Q φ) (hQ φ)

theorem localizedDistribution_regular {𝕜 : Type} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source)
    (T S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)
    (hS : ∀ φ ψ : SchwartzMap ℝ 𝕜,
      (∀ x, ψ x = localizedDensity e a φ x) → S φ = T ψ)
    (f : ℝ → 𝕜) (hT : ∀ ψ : SchwartzMap ℝ 𝕜, T ψ = ∫ x, f x * ψ x)
    (φ : SchwartzMap ℝ 𝕜) : S φ = ∫ x, localizedPullback e a f x * φ x := by
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  have hd : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y := by
    intro y hy
    exact (hi.differentiableOn (by simp) y hy).differentiableAt (e.open_target.mem_nhds hy)
  calc
    S φ = T (Q φ) := hS φ (Q φ) (hQ φ)
    _ = ∫ x, f x * Q φ x := hT (Q φ)
    _ = ∫ x, f x * localizedDensity e a φ x := by simp_rw [hQ φ]
    _ = ∫ x, localizedPullback e a f x * φ x := (localizedPullback_pairing e hd a f φ).symm

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

theorem localized_distribution :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedDistributionType := by
  intro 𝕜 _ e he hi a ha hc hs T
  exact localizedDistribution_exists e he hi a ha hc hs T

theorem localized_distribution_regular :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedDistributionRegularType := by
  intro 𝕜 _ e he hi a ha hc hs T S hS f hT φ
  exact localizedDistribution_regular e he hi a ha hc hs T S hS f hT φ

theorem fractional_extension_bound :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalExtensionType := by
  intro 𝕜 _ p hp K hK U hU hKU
  exact compact_extension_energy_bound (E := 𝕜) p hp K hK U hU hKU

theorem fractional_constant :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalConstantType := by
  intro σ hσ0 hσ1
  exact ⟨fractionalKernel_integrable σ hσ0 hσ1, fractionalKernel_integral_pos σ hσ0 hσ1⟩

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M]

theorem chartTest_tsupport_subset_image [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph M ℝ) (he : e ∈ maximalAtlas (𝓘(ℝ)) ∞ M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (hs : tsupport f ⊆ e.source) :
    tsupport (chartTest M e he f hs) ⊆ e '' tsupport f := by
  let V : TopologicalSpace.Opens ℝ := ⟨e.target, e.open_target⟩
  let g : V → 𝕜 := fun y => f (e.symm y)
  have hc : HasCompactSupport g := compactSupport_in_chart M e f hs
  have hcont : Continuous (fun y : V => e.symm y) :=
    e.symm.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)
  have hg : tsupport g ⊆ (fun y : V => e.symm y) ⁻¹' tsupport f :=
    tsupport_comp_subset_preimage f hcont
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hc.tsupport_extend_zero_subset continuous_subtype_val hy
  exact ⟨e.symm z, hg hz, e.right_inv z.property⟩

@[simp] theorem chartLocalFunction_apply {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (f : M → 𝕜) (i : Fin A.n)
    {y : ℝ} (hy : y ∈ (A.chart i).target) :
    chartLocalFunction A f i y = A.cutoff i ((A.chart i).symm y) • f ((A.chart i).symm y) :=
  indicator_of_mem hy _

theorem chartLocalFunction_test [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (i : Fin A.n) :
    ∃ φ : TestFunction (⟨(A.chart i).target, (A.chart i).open_target⟩ :
        TopologicalSpace.Opens ℝ) 𝕜 ⊤,
      (φ : ℝ → 𝕜) = chartLocalFunction A f i := by
  let g : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
    ⟨fun x => A.cutoff i x • f x, (A.cutoff i).contMDiff.smul f.contMDiff⟩
  have hs : tsupport g ⊆ (A.chart i).source :=
    (tsupport_smul_subset_left (A.cutoff i) f).trans (A.subordinate i)
  refine ⟨chartTest M (A.chart i) (A.chart_smooth i) g hs, ?_⟩
  funext y
  by_cases hy : y ∈ (A.chart i).target
  · rw [chartTest_apply M (A.chart i) (A.chart_smooth i) g hs y hy,
      chartLocalFunction_apply A f i hy]
    rfl
  · rw [(chartTest M (A.chart i) (A.chart_smooth i) g hs).zero_on_compl hy,
      chartLocalFunction, indicator_of_notMem hy]
    rfl

theorem chartLocalFunction_smooth_compact [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (i : Fin A.n) :
    ContDiff ℝ ∞ (chartLocalFunction A f i) ∧
      HasCompactSupport (chartLocalFunction A f i) ∧
      tsupport (chartLocalFunction A f i) ⊆ (A.chart i).target := by
  obtain ⟨φ, hφ⟩ := chartLocalFunction_test A f i
  rw [← hφ]
  exact ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩


/-- Local coordinate support is contained in the image of the original
scalar support, not merely somewhere in the chart target. -/
theorem chartLocalFunction_tsupport_subset_image [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (i : Fin A.n) :
    tsupport (chartLocalFunction A f i) ⊆ (A.chart i) '' tsupport f := by
  let g : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
    ⟨fun x => A.cutoff i x • f x, (A.cutoff i).contMDiff.smul f.contMDiff⟩
  have hs : tsupport g ⊆ (A.chart i).source :=
    (tsupport_smul_subset_left (A.cutoff i) f).trans (A.subordinate i)
  have htest : (chartTest M (A.chart i) (A.chart_smooth i) g hs : ℝ → 𝕜) =
      chartLocalFunction A f i := by
    funext y
    by_cases hy : y ∈ (A.chart i).target
    · rw [chartTest_apply M (A.chart i) (A.chart_smooth i) g hs y hy,
        chartLocalFunction_apply A f i hy]
      rfl
    · rw [(chartTest M (A.chart i) (A.chart_smooth i) g hs).zero_on_compl hy,
        chartLocalFunction, indicator_of_notMem hy]
      rfl
  rw [← htest]
  exact (chartTest_tsupport_subset_image (A.chart i) (A.chart_smooth i) g hs).trans
    (image_mono (tsupport_smul_subset_right (A.cutoff i) f))

/-- Smooth overlap cutoffs produce genuine compact smooth transition
coefficients with support strictly within the transition source. -/
theorem chartOverlapCoefficient_properties [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (A B : FiniteChartPartition M)
    (i : Fin A.n) (j : Fin B.n)
    (θ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hθ : tsupport θ ⊆ (A.chart i).source ∩ (B.chart j).source) :
    ContDiff ℝ ∞ (chartLocalFunction A (fun x => (θ x : 𝕜)) i) ∧
      HasCompactSupport (chartLocalFunction A (fun x => (θ x : 𝕜)) i) ∧
      tsupport (chartLocalFunction A (fun x => (θ x : 𝕜)) i) ⊆
        (A.transition B i j).source := by
  let fθ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
    ⟨fun x => (θ x : 𝕜), (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contMDiff.comp θ.contMDiff⟩
  obtain ⟨hsmooth, hcompact, htarget⟩ := chartLocalFunction_smooth_compact A fθ i
  refine ⟨hsmooth, hcompact, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := chartLocalFunction_tsupport_subset_image A fθ i hy
  have hxθ : x ∈ tsupport θ :=
    tsupport_comp_subset (show (RCLike.ofReal : ℝ → 𝕜) 0 = 0 from RCLike.ofReal_zero) θ hx
  have hxs := hθ hxθ
  refine ⟨(A.chart i).map_source hxs.1, ?_⟩
  change (A.chart i).symm ((A.chart i) x) ∈ (B.chart j).source
  rw [(A.chart i).left_inv hxs.1]
  exact hxs.2

/-- Exact scalar overlap identity, before applying any Sobolev estimate. -/
theorem chartLocalFunction_overlap {𝕜 : Type*} [RCLike 𝕜]
    (A B : FiniteChartPartition M) (i : Fin A.n) (j : Fin B.n)
    (θ : M → ℝ)
    (hθ : ∀ x ∈ tsupport (A.cutoff i) ∩ tsupport (B.cutoff j), θ x = 1)
    (f : M → 𝕜) :
    localizedPullback (A.transition B i j)
      (chartLocalFunction A (fun x => (θ x : 𝕜)) i)
      (chartLocalFunction B f j) =
      (A.chart i).target.indicator (fun y =>
        (A.cutoff i ((A.chart i).symm y) * B.cutoff j ((A.chart i).symm y)) •
          f ((A.chart i).symm y)) := by
  classical
  funext y
  by_cases hy : y ∈ (A.chart i).target
  · let x := (A.chart i).symm y
    have hxA : x ∈ (A.chart i).source := (A.chart i).map_target hy
    by_cases hxB : x ∈ (B.chart j).source
    · have he : y ∈ (A.transition B i j).source := ⟨hy, hxB⟩
      have hb : (A.transition B i j) y ∈ (B.chart j).target := (B.chart j).map_source hxB
      have hinv : (B.chart j).symm ((A.transition B i j) y) = x :=
        (B.chart j).left_inv hxB
      rw [localizedPullback, indicator_of_mem he, chartLocalFunction_apply A _ i hy,
        chartLocalFunction_apply B f j hb, hinv, indicator_of_mem hy]
      change (A.cutoff i x • (θ x : 𝕜)) * (B.cutoff j x • f x) =
        (A.cutoff i x * B.cutoff j x) • f x
      by_cases hχ : A.cutoff i x = 0
      · simp [hχ]
      by_cases hη : B.cutoff j x = 0
      · simp [hη]
      have hθx : θ x = 1 := hθ x ⟨subset_closure hχ, subset_closure hη⟩
      simp [hθx, Algebra.smul_def, mul_assoc]
    · have he : y ∉ (A.transition B i j).source := fun h => hxB h.2
      have hη : B.cutoff j x = 0 := by
        by_contra hn
        exact hxB (B.subordinate j (subset_closure hn))
      rw [localizedPullback, indicator_of_notMem he, indicator_of_mem hy]
      change 0 = (A.cutoff i x * B.cutoff j x) • f x
      simp [hη]
  · have he : y ∉ (A.transition B i j).source := fun h => hy h.1
    rw [localizedPullback, indicator_of_notMem he, indicator_of_notMem hy]

/-- Finite partitions yield the exact change-of-atlas decomposition on actual
scalar functions. This equality contains no boundedness assumptions. -/
theorem chartLocalFunction_decomposition {𝕜 : Type*} [RCLike 𝕜]
    (A B : FiniteChartPartition M)
    (θ : Fin A.n → Fin B.n → M → ℝ)
    (hθ : ∀ i j x, x ∈ tsupport (A.cutoff i) ∩ tsupport (B.cutoff j) → θ i j x = 1)
    (f : M → 𝕜) (i : Fin A.n) :
    chartLocalFunction A f i = fun y => ∑ j,
      localizedPullback (A.transition B i j)
        (chartLocalFunction A (fun x => (θ i j x : 𝕜)) i)
        (chartLocalFunction B f j) y := by
  classical
  have hparts (j : Fin B.n) := chartLocalFunction_overlap A B i j (θ i j) (hθ i j) f
  simp_rw [hparts]
  funext y
  by_cases hy : y ∈ (A.chart i).target
  · simp_rw [chartLocalFunction_apply A f i hy, indicator_of_mem hy]
    rw [← Finset.sum_smul, ← Finset.mul_sum, B.sum_one, mul_one]
  · simp [chartLocalFunction, indicator_of_notMem hy]


/-- The actual compact smooth coefficients needed for finite atlas comparison
exist for any two finite chart partitions. Their exact action on all ordinary
scalar functions is proved, without any analytic boundedness premise. -/
theorem exists_chartTransitionCoefficients [T2Space M] [CompactSpace M]
    {𝕜 : Type*} [RCLike 𝕜] (A B : FiniteChartPartition M) :
    ∃ a : Fin A.n → Fin B.n → ℝ → 𝕜,
      (∀ i j, ContDiff ℝ ∞ (a i j) ∧ HasCompactSupport (a i j) ∧
        tsupport (a i j) ⊆ (A.transition B i j).source) ∧
      ∀ (f : M → 𝕜) (i : Fin A.n), chartLocalFunction A f i = fun y =>
        ∑ j, localizedPullback (A.transition B i j) (a i j)
          (chartLocalFunction B f j) y := by
  classical
  choose θ hθ using fun i j => exists_overlapCutoff M A B i j
  let a (i : Fin A.n) (j : Fin B.n) : ℝ → 𝕜 :=
    chartLocalFunction A (fun x => (θ i j x : 𝕜)) i
  refine ⟨a, ?_, ?_⟩
  · intro i j
    exact chartOverlapCoefficient_properties A B i j (θ i j) (hθ i j).2.1
  · intro f i
    apply chartLocalFunction_decomposition A B (fun i j => θ i j) _ f i
    intro i j x hx
    exact (hθ i j).1.self_of_nhdsSet x hx


/-- The localizations recover the original scalar function pointwise. -/
theorem chartLocalFunction_reconstruct {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (f : M → 𝕜) (x : M) :
    (∑ i, (A.chart i).source.indicator
      (fun z => chartLocalFunction A f i ((A.chart i) z)) x) = f x := by
  classical
  have hpiece (i : Fin A.n) : (A.chart i).source.indicator
      (fun z => chartLocalFunction A f i ((A.chart i) z)) x = A.cutoff i x • f x := by
    by_cases hx : x ∈ (A.chart i).source
    · rw [indicator_of_mem hx,
        chartLocalFunction_apply A f i ((A.chart i).map_source hx), (A.chart i).left_inv hx]
    · have hz : A.cutoff i x = 0 := by
        by_contra hn
        exact hx (A.subordinate i (subset_closure hn))
      simp [indicator_of_notMem hx, hz]
  simp_rw [hpiece]
  rw [← Finset.sum_smul, A.sum_one, one_smul]

/-- Hence coordinate localization is faithful, including for the empty curve. -/
theorem chartLocalFunction_injective {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) :
    Function.Injective (fun f : M → 𝕜 => chartLocalFunction A f) := by
  intro f g hfg
  change chartLocalFunction A f = chartLocalFunction A g at hfg
  funext x
  rw [← chartLocalFunction_reconstruct A f x, ← chartLocalFunction_reconstruct A g x]
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun hfg i]

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

theorem smooth_compact_localization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.smoothCompactLocalizationType := by
  intro M _ _ _ _ _ 𝕜 _ A f i
  exact chartLocalFunction_smooth_compact A f i

theorem finite_coordinate_decomposition :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteCoordinateDecompositionType := by
  intro M _ _ _ _ _ 𝕜 _ A B
  exact exists_chartTransitionCoefficients (𝕜 := 𝕜) A B

theorem chart_reconstruction :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.chartReconstructionType := by
  intro M _ _ _ 𝕜 _ A f x
  exact chartLocalFunction_reconstruct A f x

end ExpandedFA.Sobolev.Curve

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier


@[simp] lemma realLineIsometry_apply (t : ℝ) : realLineIsometry t 0 = t := by
  exact OrthonormalBasis.singleton_repr t 0

lemma fourier_realLineIsometry (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (f ∘ realLineIsometry.symm) (realLineIsometry ξ) = 𝓕 f ξ := by
  change (∫ x : Euclidean 1, Real.fourierChar (-inner ℝ x (realLineIsometry ξ)) •
    f (realLineIsometry.symm x)) =
      ∫ t : ℝ, Real.fourierChar (-inner ℝ t ξ) • f t
  rw [← realLineIsometry.measurePreserving.integral_comp
    realLineIsometry.toMeasurableEquiv.measurableEmbedding]
  simp only [realLineIsometry.symm_apply_apply, realLineIsometry.inner_map_map]

lemma realLineIsometry_lintegral (f : Euclidean 1 → ENNReal) :
    (∫⁻ t : ℝ, f (realLineIsometry t)) = ∫⁻ x : Euclidean 1, f x :=
  realLineIsometry.measurePreserving.lintegral_comp_emb
    realLineIsometry.toMeasurableEquiv.measurableEmbedding f

lemma realLineIsometry_symm_lintegral (f : ℝ → ENNReal) :
    (∫⁻ x : Euclidean 1, f (realLineIsometry.symm x)) = ∫⁻ t : ℝ, f t :=
  realLineIsometry.symm.measurePreserving.lintegral_comp_emb
    realLineIsometry.symm.toMeasurableEquiv.measurableEmbedding f

lemma weighted_translation_difference_line (f : ℝ → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2) (w : ℝ → ENNReal) (hw : Measurable w) :
    (∫⁻ h, w h * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ 2) =
      ∫⁻ ξ, (∫⁻ h, w h * ‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ₑ ^ 2) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hf1 : Integrable (f ∘ realLineIsometry.symm) :=
    realLineIsometry.symm.measurePreserving.integrable_comp_emb
      realLineIsometry.symm.toMeasurableEquiv.measurableEmbedding |>.mpr h1
  have hf2 : MemLp (f ∘ realLineIsometry.symm) 2 :=
    h2.comp_measurePreserving realLineIsometry.symm.measurePreserving
  have H := weighted_translation_difference_lintegral
    (f ∘ realLineIsometry.symm) hf1 hf2 (w ∘ realLineIsometry.symm)
      (hw.comp realLineIsometry.symm.continuous.measurable)
  simp_rw [← realLineIsometry_lintegral] at H
  simpa only [Function.comp_apply, map_add, realLineIsometry.symm_apply_apply,
    realLineIsometry.inner_map_map, real_inner_comm, Real.inner_apply,
    fourier_realLineIsometry, mul_comm] using H
end ExpandedFA.Sobolev.Curve

open MeasureTheory
noncomputable section
namespace ExpandedFA.Sobolev.Curve


lemma scaled_fractionalKernel_eq (σ ξ : ℝ) (hξ : ξ ≠ 0) (h : ℝ) :
    ‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ ^ 2 * |h| ^ (-1 - 2 * σ) =
      |ξ| ^ (1 + 2 * σ) * fractionalKernel σ (h * ξ) := by
  have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
  have hp : |ξ| ^ (1 + 2 * σ) * |ξ| ^ (-1 - 2 * σ) = 1 := by
    rw [← Real.rpow_add hξ0,
      show (1 + 2 * σ) + (-1 - 2 * σ) = 0 by ring, Real.rpow_zero]
  unfold fractionalKernel
  rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  calc
    _ = (‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ ^ 2 * |h| ^ (-1 - 2 * σ)) *
        (|ξ| ^ (1 + 2 * σ) * |ξ| ^ (-1 - 2 * σ)) := by rw [hp, mul_one]
    _ = _ := by ring

lemma scaled_fractionalKernel_integrable (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ξ : ℝ) :
    Integrable (fun h : ℝ =>
      ‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ ^ 2 * |h| ^ (-1 - 2 * σ)) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  · have hi := ((fractionalKernel_integrable σ hσ0 hσ1).comp_mul_right' hξ).const_mul
      (|ξ| ^ (1 + 2 * σ))
    exact hi.congr (Filter.Eventually.of_forall fun h => (scaled_fractionalKernel_eq σ ξ hξ h).symm)

lemma scaled_fractionalKernel_integral (σ : ℝ) (hσ0 : 0 < σ) (_hσ1 : σ < 1)
    (ξ : ℝ) :
    (∫ h : ℝ, ‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ ^ 2 * |h| ^ (-1 - 2 * σ)) =
      |ξ| ^ (2 * σ) * ∫ t, fractionalKernel σ t := by
  by_cases hξ : ξ = 0
  · simp [hξ, Real.zero_rpow (show 2 * σ ≠ 0 by positivity)]
  · have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
    have hp : |ξ| ^ (1 + 2 * σ) * |ξ⁻¹| = |ξ| ^ (2 * σ) := by
      rw [abs_inv, show 1 + 2 * σ = 2 * σ + 1 by ring,
        Real.rpow_add hξ0, Real.rpow_one, mul_assoc, mul_inv_cancel₀ hξ0.ne', mul_one]
    calc
      _ = ∫ h : ℝ, |ξ| ^ (1 + 2 * σ) * fractionalKernel σ (h * ξ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h => scaled_fractionalKernel_eq σ ξ hξ h
      _ = |ξ| ^ (1 + 2 * σ) * ∫ h : ℝ, fractionalKernel σ (h * ξ) := integral_const_mul _ _
      _ = |ξ| ^ (1 + 2 * σ) * (|ξ⁻¹| * ∫ t, fractionalKernel σ t) := by
        rw [Measure.integral_comp_mul_right, smul_eq_mul]
      _ = _ := by rw [← mul_assoc, hp]

lemma scaled_fractionalKernel_lintegral (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ξ : ℝ) :
    (∫⁻ h : ℝ, ENNReal.ofReal (|h| ^ (-1 - 2 * σ)) *
      ‖(Real.fourierChar (h * ξ) : ℂ) - 1‖ₑ ^ 2) =
      ENNReal.ofReal (|ξ| ^ (2 * σ)) * ∫⁻ t, ENNReal.ofReal (fractionalKernel σ t) := by
  have H := congrArg ENNReal.ofReal (scaled_fractionalKernel_integral σ hσ0 hσ1 ξ)
  rw [ofReal_integral_eq_lintegral_ofReal (scaled_fractionalKernel_integrable σ hσ0 hσ1 ξ)
      (Filter.Eventually.of_forall (fun h => by positivity)),
    ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg ξ) _),
    ofReal_integral_eq_lintegral_ofReal (fractionalKernel_integrable σ hσ0 hσ1)
      (Filter.Eventually.of_forall (fun t => by unfold fractionalKernel; positivity))] at H
  rw [← H]
  apply lintegral_congr
  intro h
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  exact mul_comm _ _

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
lemma fractional_plancherel_line (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫⁻ h, ENNReal.ofReal (|h| ^ (-1 - 2 * σ)) * ∫⁻ x, ‖f (x+h) - f x‖ₑ ^ 2) =
      ENNReal.ofReal (∫ t, fractionalKernel σ t) *
        ∫⁻ ξ, ENNReal.ofReal (|ξ| ^ (2 * σ)) * ‖𝓕 f ξ‖ₑ ^ 2 := by
  rw [weighted_translation_difference_line f hf1 hf2 _ (by fun_prop)]
  simp_rw [scaled_fractionalKernel_lintegral σ hσ0 hσ1]
  have hc := ofReal_integral_eq_lintegral_ofReal (fractionalKernel_integrable σ hσ0 hσ1)
    (Filter.Eventually.of_forall (fun t => by unfold fractionalKernel; positivity))
  rw [← hc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ξ
  ring

lemma differenceEnergy_translation {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f : ℝ → E) (hf : Continuous f) :
    differenceEnergy p f Set.univ =
      ∫⁻ h, ENNReal.ofReal (|h| ^ (-p)) * ∫⁻ x, ‖f (x+h) - f x‖ₑ ^ 2 := by
  have hm : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (|z.2| ^ (-p)) * ‖f (z.1 + z.2) - f z.1‖ₑ ^ 2) := by
    exact ((continuous_snd.abs.measurable.pow_const _).ennreal_ofReal).mul
      ((((hf.comp (continuous_fst.add continuous_snd)).sub
        (hf.comp continuous_fst)).enorm.measurable).pow_const 2)
  unfold differenceEnergy
  simp only [Measure.restrict_univ]
  calc
    _ = ∫⁻ x, ∫⁻ h, ENNReal.ofReal (|h| ^ (-p)) * ‖f (x+h) - f x‖ₑ ^ 2 := by
      apply lintegral_congr
      intro x
      rw [← lintegral_add_left_eq_self (fun y => differenceKernel p f x y) x]
      apply lintegral_congr
      intro h
      simp only [differenceKernel, sub_add_cancel_left, abs_neg,
        div_eq_mul_inv, ← Real.rpow_neg (abs_nonneg h), norm_sub_rev (f x) (f (x+h)),
        ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      exact mul_comm _ _
    _ = ∫⁻ h, ∫⁻ x, ENNReal.ofReal (|h| ^ (-p)) * ‖f (x+h) - f x‖ₑ ^ 2 :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

theorem fractional_plancherel :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalPlancherelType := by
  intro σ hσ0 hσ1 f hfc hf1 hf2
  rw [differenceEnergy_translation _ f hfc,
    show -(1 + 2 * σ) = -1 - 2 * σ by ring]
  exact fractional_plancherel_line σ hσ0 hσ1 f hf1 hf2

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
lemma fractional_frequency_weight_lower (σ ξ : ℝ) (hσ : 0 ≤ σ) :
    1 + |ξ| ^ (2 * σ) ≤ 2 * (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ σ := by
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hbase : 1 ≤ 1 + 4 * Real.pi ^ 2 * |ξ| ^ 2 := by
    have H : 0 ≤ 4 * Real.pi ^ 2 * |ξ| ^ 2 := by positivity
    linarith
  have hpow : |ξ| ^ (2 * σ) = (|ξ| ^ (2 : ℕ)) ^ σ :=
    Real.rpow_natCast_mul (abs_nonneg ξ) 2 σ
  have hsmall : |ξ| ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * |ξ| ^ 2 := by
    nlinarith [sq_nonneg |ξ|]
  have h₁ := Real.one_le_rpow hbase hσ
  have h₂ := Real.rpow_le_rpow (sq_nonneg |ξ|) hsmall hσ
  rw [← hpow] at h₂
  linarith

lemma fractional_frequency_weight_upper (σ ξ : ℝ) (hσ : 0 ≤ σ) :
    (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ σ ≤
      (1 + 4 * Real.pi ^ 2) ^ σ * (1 + |ξ| ^ (2 * σ)) := by
  have hbase : 1 + 4 * Real.pi ^ 2 * |ξ| ^ 2 ≤
      (1 + 4 * Real.pi ^ 2) * max 1 (|ξ| ^ 2) := by
    have h₁ : 1 ≤ max 1 (|ξ| ^ 2) := le_max_left _ _
    have h₂ : |ξ| ^ 2 ≤ max 1 (|ξ| ^ 2) := le_max_right _ _
    have hπ : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    nlinarith
  calc
    _ ≤ ((1 + 4 * Real.pi ^ 2) * max 1 (|ξ| ^ 2)) ^ σ :=
      Real.rpow_le_rpow (by positivity) hbase hσ
    _ = (1 + 4 * Real.pi ^ 2) ^ σ * max 1 (|ξ| ^ (2 * σ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_max (by norm_num) (sq_nonneg _) hσ, Real.one_rpow,
        ← Real.rpow_natCast_mul (abs_nonneg ξ) 2 σ]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (max_le_add_of_nonneg (by norm_num) (Real.rpow_nonneg (abs_nonneg ξ) _))
      (Real.rpow_nonneg (by positivity) _)


theorem fractional_weight_comparison :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalWeightComparisonType := by
  intro σ ξ hσ
  exact ⟨fractional_frequency_weight_lower σ ξ hσ, fractional_frequency_weight_upper σ ξ hσ⟩
end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve

theorem localizedPullback_ae_congr {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : DifferentiableOn ℝ e.symm e.target) (a : ℝ → 𝕜)
    {f g : ℝ → 𝕜} (hfg : f =ᵐ[volume] g) :
    localizedPullback e a f =ᵐ[volume] localizedPullback e a g := by
  let N : Set ℝ := e.target ∩ {y | f y ≠ g y}
  have hN : volume N = 0 := measure_mono_null inter_subset_right (ae_iff.mp hfg)
  have him : volume (e.symm '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (he.mono inter_subset_left) hN
  apply ae_iff.mpr
  apply measure_mono_null _ him
  intro x hx
  have hs : x ∈ e.source := by
    by_contra h
    exact hx (by simp [localizedPullback, h])
  refine ⟨e x, ⟨e.map_source hs, ?_⟩, e.left_inv hs⟩
  intro h
  exact hx (by simp [localizedPullback, hs, h])

theorem localizedPullback_aestronglyMeasurable {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : DifferentiableOn ℝ e.symm e.target) (a : ℝ → 𝕜)
    (ha : Measurable a) {f : ℝ → 𝕜} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (localizedPullback e a f) volume := by
  exact ((localizedPullback_stronglyMeasurable e a (hf.mk f) ha hf.stronglyMeasurable_mk).aestronglyMeasurable).congr (localizedPullback_ae_congr e he a hf.ae_eq_mk).symm

 theorem localizedPullback_memLp_of_memLp {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ 1 e.symm e.target) (a : ℝ → 𝕜)
    (ha : Continuous a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source)
    {f : ℝ → 𝕜} (hf : MemLp f 2 volume) :
    MemLp (localizedPullback e a f) 2 volume := by
  have hd : DifferentiableOn ℝ e.symm e.target := he.differentiableOn (by norm_num)
  obtain ⟨C, _, hC⟩ := localizedPullback_jacobian_bound e a ha hc hs
    (he.continuousOn_deriv_of_isOpen e.open_target le_rfl)
  have hmk := localizedPullback_memLp e
    (fun y hy => (hd y hy).differentiableAt (e.open_target.mem_nhds hy)) a ha.measurable hC
    (hf.aestronglyMeasurable.mk f) hf.aestronglyMeasurable.stronglyMeasurable_mk
    ((memLp_congr_ae hf.aestronglyMeasurable.ae_eq_mk).mp hf)
  exact (memLp_congr_ae (localizedPullback_ae_congr e hd a hf.aestronglyMeasurable.ae_eq_mk)).mpr hmk



theorem localizedPullback_eLpNorm_bound {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ 1 e.symm e.target) (a : ℝ → 𝕜)
    (ha : Continuous a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f : ℝ → 𝕜,
      eLpNorm (localizedPullback e a f) 2 volume ≤ ENNReal.ofReal C * eLpNorm f 2 volume := by
  obtain ⟨C, hC1, hC⟩ := localizedPullback_jacobian_bound e a ha hc hs
    (he.continuousOn_deriv_of_isOpen e.open_target le_rfl)
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  refine ⟨C, hC1, fun f => ?_⟩
  by_cases hf : MemLp f 2 volume
  · have hg := localizedPullback_memLp_of_memLp e he a ha hc hs hf
    have hle := localizedPullback_energy_le e
      (fun y hy => (he.differentiableOn (by norm_num) y hy).differentiableAt
        (e.open_target.mem_nhds hy)) a f hC
    have hsq (g : ℝ → 𝕜) (hg : AEStronglyMeasurable g volume) :
        eLpNorm g 2 volume ^ (2 : ℕ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) := by
      simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hg)
    apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rw [mul_pow, ← ENNReal.ofReal_pow hC0.le, hsq _ hf.aestronglyMeasurable,
      hsq _ hg.aestronglyMeasurable]
    exact hle
  · have htop : eLpNorm f 2 volume = ⊤ := top_unique (not_lt.mp hf)
    simp [htop, (ENNReal.ofReal_pos.mpr hC0).ne']

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]

theorem chartL2Size_bound {𝕜 : Type*} [RCLike 𝕜]
    (A B : FiniteChartPartition M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f : M → 𝕜,
      chartL2Size A f ≤ ENNReal.ofReal C * chartL2Size B f := by
  classical
  obtain ⟨a, ha, hdecomp⟩ := exists_chartTransitionCoefficients (𝕜 := 𝕜) A B
  have hbounds (i : Fin A.n) (j : Fin B.n) :=
    localizedPullback_eLpNorm_bound (A.transition B i j)
      ((A.transition_symm_smooth B i j).of_le (by norm_num)) (a i j)
      (ha i j).1.continuous (ha i j).2.1 (ha i j).2.2
  choose C hC hbound using hbounds
  let K : ℝ := ∑ i, ∑ j, C i j
  have hC0 : ∀ i j, 0 ≤ C i j := fun i j => zero_le_one.trans (hC i j)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC0 i j
  refine ⟨max 1 K, le_max_left _ _, fun f => ?_⟩
  calc
    chartL2Size A f ≤ ∑ i, ∑ j, ENNReal.ofReal (C i j) *
        eLpNorm (chartLocalFunction B f j) 2 volume := by
      apply Finset.sum_le_sum
      intro i _
      rw [hdecomp]
      calc
        eLpNorm (fun y => ∑ j, localizedPullback (A.transition B i j) (a i j)
            (chartLocalFunction B f j) y) 2 volume ≤
            ∑ j, eLpNorm (localizedPullback (A.transition B i j) (a i j)
              (chartLocalFunction B f j)) 2 volume := by
          convert eLpNorm_sum_le (p := (2 : ℝ≥0∞))
            (μ := (volume : Measure ℝ)) (s := Finset.univ)
            (f := fun j => localizedPullback (A.transition B i j) (a i j)
              (chartLocalFunction B f j)) (by norm_num) using 1
          congr 1
          ext y
          simp
        _ ≤ _ := Finset.sum_le_sum fun j _ => hbound i j _
    _ ≤ ∑ i, ∑ j, ENNReal.ofReal (C i j) * chartL2Size B f := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      gcongr
      change eLpNorm (chartLocalFunction B f j) 2 volume ≤
        ∑ k, eLpNorm (chartLocalFunction B f k) 2 volume
      exact Finset.single_le_sum (f := fun k => eLpNorm (chartLocalFunction B f k) 2 volume) (fun _ _ => bot_le) (Finset.mem_univ j)
    _ = ENNReal.ofReal K * chartL2Size B f := by
      simp only [← Finset.sum_mul]
      congr 1
      dsimp [K]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Finset.sum_nonneg fun j _ => hC0 i j)]
      congr 1
      ext i
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => hC0 i j)).symm
    _ ≤ ENNReal.ofReal (max 1 K) * chartL2Size B f := by
      gcongr
      exact le_max_right _ _

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
open scoped Manifold ContDiff
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]

theorem chartL2Size_equivalence {𝕜 : Type*} [RCLike 𝕜]
    (A B : FiniteChartPartition M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f : M → 𝕜,
      (chartL2Size A f ≤ ENNReal.ofReal C * chartL2Size B f) ∧
      (chartL2Size B f ≤ ENNReal.ofReal C * chartL2Size A f) := by
  obtain ⟨C, hC, hAB⟩ := chartL2Size_bound (𝕜 := 𝕜) A B
  obtain ⟨D, hD, hBA⟩ := chartL2Size_bound (𝕜 := 𝕜) B A
  refine ⟨max C D, hC.trans (le_max_left _ _), fun f => ⟨?_, ?_⟩⟩
  · exact (hAB f).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  · exact (hBA f).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _)

theorem chartL2_mem_iff {𝕜 : Type*} [RCLike 𝕜]
    (A B : FiniteChartPartition M) (f : M → 𝕜) :
    (∀ i, MemLp (chartLocalFunction A f i) 2 volume) ↔
      ∀ j, MemLp (chartLocalFunction B f j) 2 volume := by
  classical
  have hmem (A : FiniteChartPartition M) :
      (∀ i, MemLp (chartLocalFunction A f i) 2 volume) ↔ chartL2Size A f < ⊤ := by
    simp only [chartL2Size, ENNReal.sum_lt_top, memLp_iff, Finset.mem_univ, forall_true_left]
  rw [hmem A, hmem B]
  obtain ⟨C, _, hb⟩ := chartL2Size_equivalence (𝕜 := 𝕜) A B
  constructor
  · intro h
    exact (hb f).2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)
  · intro h
    exact (hb f).1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)
end ExpandedFA.Sobolev.Curve

noncomputable section
open Set ChartedSpace IsManifold
open scoped Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ℝ N] [IsManifold (𝓘(ℝ)) ∞ N]

namespace FiniteChartPartition

def pullback (A : FiniteChartPartition N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    FiniteChartPartition M where
  n := A.n
  chart i := e.toHomeomorph.toOpenPartialHomeomorph.trans (A.chart i)
  chart_smooth i := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · apply (contMDiffOn_of_mem_maximalAtlas (A.chart_smooth i)).comp
        e.contMDiff.contMDiffOn
      intro x hx
      exact hx.2
    · apply e.symm.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_symm_of_mem_maximalAtlas (A.chart_smooth i)).mono
      intro y hy
      exact hy.1
  cutoff i := (A.cutoff i).comp e.toContMDiffMap
  nonneg i x := A.nonneg i (e x)
  sum_one x := A.sum_one (e x)
  subordinate i := by
    change tsupport ((A.cutoff i) ∘ e.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro x hx
    exact ⟨mem_univ _, A.subordinate i hx⟩

@[simp] theorem pullback_target (A : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (i : Fin A.n) :
    ((A.pullback e).chart i).target = (A.chart i).target := by
  simp [pullback]

@[simp] theorem pullback_localFunction {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (f : N → 𝕜) (i : Fin A.n) :
    chartLocalFunction (A.pullback e) (f ∘ e) i = chartLocalFunction A f i := by
  ext y
  by_cases hy : y ∈ (A.chart i).target
  · simp [chartLocalFunction, pullback, hy]
  · simp [chartLocalFunction, pullback, hy]
end FiniteChartPartition


open MeasureTheory
open scoped ENNReal
variable [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]

theorem chartL2Size_pullback {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (f : N → 𝕜) :
    chartL2Size (A.pullback e) (f ∘ e) = chartL2Size A f := by
  classical
  unfold chartL2Size
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteChartPartition.pullback_localFunction]

theorem reparametrizationL2_equivalence {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (B : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f : N → 𝕜,
      (chartL2Size A (f ∘ e) ≤ ENNReal.ofReal C * chartL2Size B f) ∧
      (chartL2Size B f ≤ ENNReal.ofReal C * chartL2Size A (f ∘ e)) := by
  obtain ⟨C, hC, hb⟩ := chartL2Size_equivalence (𝕜 := 𝕜) A (B.pullback e)
  refine ⟨C, hC, fun f => ?_⟩
  simpa only [chartL2Size_pullback] using hb (f ∘ e)

theorem reparametrizationL2_mem_iff {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (B : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (f : N → 𝕜) :
    (∀ i, MemLp (chartLocalFunction A (f ∘ e) i) 2 volume) ↔
      ∀ j, MemLp (chartLocalFunction B f j) 2 volume := by
  have h := chartL2_mem_iff A (B.pullback e) (f ∘ e)
  change (∀ i, MemLp (chartLocalFunction A (f ∘ e) i) 2 volume) ↔
    ∀ j : Fin B.n, MemLp (chartLocalFunction (B.pullback e) (f ∘ e) j) 2 volume at h
  simpa only [FiniteChartPartition.pullback_localFunction] using h
end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem atlas_L2 : Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.atlasL2Type := by
  intro M _ _ _ _ _ 𝕜 _ A B
  obtain ⟨C, hC, hb⟩ := chartL2Size_equivalence (𝕜 := 𝕜) A B
  exact ⟨C, hC, hb, chartL2_mem_iff A B⟩

theorem reparametrization_L2 :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.reparametrizationL2Type := by
  intro M _ _ _ _ _ N _ _ _ _ _ 𝕜 _ A B e
  obtain ⟨C, hC, hb⟩ := reparametrizationL2_equivalence (𝕜 := 𝕜) A B e
  exact ⟨C, hC, hb, reparametrizationL2_mem_iff A B e⟩

end ExpandedFA.Sobolev.Curve


noncomputable section
open Set Filter
open scoped Topology NNReal
namespace ExpandedFA.Sobolev.Curve

lemma compact_lipschitz_of_contDiffOn_open {f : ℝ → ℝ} {U K : Set ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L, W, hW, hLip⟩ := ((hf x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
  exact ⟨L, W, mem_nhdsWithin_of_mem_nhds hW, hLip⟩

lemma compact_coordinate_restriction (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ 1 e e.source) (hi : ContDiffOn ℝ 1 e.symm e.target)
    (K : Set ℝ) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    ∃ U : Set ℝ, IsOpen U ∧ K ⊆ U ∧ closure U ⊆ e.source ∧ IsCompact (closure U) ∧
      ∃ L J : ℝ, 0 < L ∧ 0 ≤ J ∧
        (∀ x ∈ U, ∀ y ∈ U, |e x - e y| ≤ L * |x-y|) ∧
        (∀ y ∈ e '' U, |deriv e.symm y| ≤ J) := by
  obtain ⟨C, hCc, hKC, hCs⟩ := exists_compact_between hK e.open_source hKs
  have hcl : closure (interior C) ⊆ C := closure_minimal interior_subset hCc.isClosed
  obtain ⟨L, hL⟩ := compact_lipschitz_of_contDiffOn_open e.open_source hCc hCs he
  have hEc : IsCompact (e '' C) := hCc.image_of_continuousOn (e.continuousOn.mono hCs)
  have hd : ContinuousOn (fun y => |deriv e.symm y|) (e '' C) :=
    (hi.continuousOn_deriv_of_isOpen e.open_target (by norm_num)).abs.mono (image_subset_iff.mpr fun x hx => e.map_source (hCs hx))
  obtain ⟨J, hJ⟩ := hEc.bddAbove_image hd
  refine ⟨interior C, isOpen_interior, hKC, hcl.trans hCs,
    hCc.of_isClosed_subset isClosed_closure hcl,
    (L : ℝ) + 1, max J 0, by positivity, le_max_right _ _, ?_, ?_⟩
  · intro x hx y hy
    have H := hL.dist_le_mul x (interior_subset hx) y (interior_subset hy)
    simp only [Real.dist_eq] at H
    exact H.trans (mul_le_mul_of_nonneg_right (by simp) (abs_nonneg _))
  · intro y hy
    exact (hJ (mem_image_of_mem _ ((image_mono interior_subset) hy))).trans (le_max_left _ _)

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ENNReal Topology NNReal
namespace ExpandedFA.Sobolev.Curve

private def cutoffKernel (p t : ℝ) : ℝ :=
  if |t| < 1 then |t| ^ (2-p) else |t| ^ (-p)

private lemma cutoffKernel_nonneg (p t : ℝ) : 0 ≤ cutoffKernel p t := by
  unfold cutoffKernel
  split <;> positivity

private lemma cutoffKernel_measurable (p : ℝ) : Measurable (cutoffKernel p) := by
  unfold cutoffKernel
  exact Measurable.ite (isOpen_lt continuous_abs continuous_const).measurableSet
    (by fun_prop) (by fun_prop)

private lemma cutoffKernel_integrable (p : ℝ) (hp1 : 1 < p) (hp3 : p < 3) :
    Integrable (cutoffKernel p) := by
  have hm : AEStronglyMeasurable (cutoffKernel p) volume := (cutoffKernel_measurable p).aestronglyMeasurable
  have hnear : IntegrableOn (cutoffKernel p) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (α := p-2) (C := 1)
    · simp only [Module.finrank_self, Nat.cast_one]
      linarith
    · filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with t ht
      have ht : |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
      simp [cutoffKernel, ht, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), neg_sub]
    · exact hm
  have htail : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-p)) := by
    apply integrable_one_add_norm
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hfar : IntegrableOn (cutoffKernel p) (Metric.ball (0:ℝ) 1)ᶜ := by
    apply (htail.const_mul ((2:ℝ)^p)).integrableOn.mono' hm.restrict
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet.compl] with t ht
    have ht : ¬ |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    have ht1 : 1 ≤ |t| := le_of_not_gt ht
    have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1+|t|)/2)
      (show (1+|t|)/2 ≤ |t| by linarith) (show -p ≤ 0 by linarith)
    have he : ((1+|t|)/2)^(-p) = (2:ℝ)^p * (1+|t|)^(-p) := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    simpa [cutoffKernel, ht, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), he] using hb
  exact (integrableOn_univ.mp (by simpa only [union_compl_self] using hnear.union hfar))

lemma differenceKernel_cutoff_bound {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (a : ℝ → 𝕜) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x, ‖a x‖ ≤ A)
    (B : ℝ≥0) (hB : LipschitzWith B a) (x y : ℝ) :
    differenceKernel p a x y ≤
      ENNReal.ofReal ((B : ℝ)^2 + 4*A^2) * ENNReal.ofReal (cutoffKernel p (x-y)) := by
  have hC : 0 ≤ (B:ℝ)^2+4*A^2 := by positivity
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  by_cases hxy : x=y
  · simp only [hxy, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    exact mul_nonneg hC (cutoffKernel_nonneg p 0)
  have hd : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hD : 0 < |x-y|^p := Real.rpow_pos_of_pos hd p
  have hn : ‖a x-a y‖ ≤ 2*A := by
    calc
      _ ≤ ‖a x‖+‖a y‖ := norm_sub_le _ _
      _ ≤ 2*A := by linarith [ha x, ha y]
  have hLip : ‖a x-a y‖ ≤ (B:ℝ)*|x-y| := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hB.dist_le_mul x y
  change ‖a x-a y‖^2 / |x-y|^p ≤ _
  unfold cutoffKernel
  split_ifs with hnear
  · have hn2 : ‖a x-a y‖^2 ≤ (B:ℝ)^2*|x-y|^2 := by
      have := sq_le_sq₀ (norm_nonneg _) (mul_nonneg B.coe_nonneg hd.le) |>.mpr hLip
      nlinarith
    have he : |x-y|^2 / |x-y|^p = |x-y|^(2-p) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_sub hd]
      norm_num
    calc
      _ ≤ (B:ℝ)^2 * (|x-y|^2 / |x-y|^p) := by simpa [mul_div_assoc] using div_le_div_of_nonneg_right hn2 hD.le
      _ = (B:ℝ)^2 * |x-y|^(2-p) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg A]) (Real.rpow_nonneg hd.le _)
  · have hn2 : ‖a x-a y‖^2 ≤ 4*A^2 := by
      have := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*A) |>.mpr hn
      nlinarith
    calc
      _ ≤ 4*A^2 / |x-y|^p := div_le_div_of_nonneg_right hn2 hD.le
      _ = 4*A^2 * |x-y|^(-p) := by rw [Real.rpow_neg hd.le, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (B:ℝ)]) (Real.rpow_nonneg hd.le _)

lemma cutoff_row_energy_bound {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (hp1 : 1 < p) (hp3 : p < 3)
    (a : ℝ → 𝕜) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x, ‖a x‖ ≤ A)
    (B : ℝ≥0) (hB : LipschitzWith B a) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ y : ℝ, (∫⁻ x, differenceKernel p a x y) ≤ C := by
  let C := ENNReal.ofReal ((B:ℝ)^2+4*A^2)
  have hw : (∫⁻ t, ENNReal.ofReal (cutoffKernel p t)) < ⊤ := by
    exact lt_of_le_of_lt (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (le_abs_self _))
      (by simpa [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using (cutoffKernel_integrable p hp1 hp3).hasFiniteIntegral)
  refine ⟨C * ∫⁻ t, ENNReal.ofReal (cutoffKernel p t), ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw, ?_⟩
  intro y
  calc
    _ ≤ ∫⁻ x, C * ENNReal.ofReal (cutoffKernel p (x-y)) :=
      lintegral_mono (fun x => differenceKernel_cutoff_bound p a A hA ha B hB x y)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self (fun t => ENNReal.ofReal (cutoffKernel p t)) y]

lemma differenceKernel_mul_le {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (a f : ℝ → 𝕜) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x, ‖a x‖ ≤ A) (x y : ℝ) :
    differenceKernel p (a*f) x y ≤
      ENNReal.ofReal (2*A^2) * differenceKernel p f x y +
        2 * differenceKernel p a x y * ENNReal.ofReal (‖f y‖^2) := by
  have hn : ‖a x*f x-a y*f y‖ ≤ A*‖f x-f y‖ + ‖a x-a y‖*‖f y‖ := by
    calc
      _ = ‖a x*(f x-f y)+(a x-a y)*f y‖ := by congr 1; ring
      _ ≤ ‖a x*(f x-f y)‖+‖(a x-a y)*f y‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul]; gcongr; exact ha x
  have hs : ‖a x*f x-a y*f y‖^2 ≤ 2*A^2*‖f x-f y‖^2+2*‖a x-a y‖^2*‖f y‖^2 := by
    have hnn : 0 ≤ A*‖f x-f y‖ + ‖a x-a y‖*‖f y‖ := by positivity
    have H := (sq_le_sq₀ (norm_nonneg _) hnn).mpr hn
    nlinarith [sq_nonneg (A*‖f x-f y‖-‖a x-a y‖*‖f y‖)]
  have hd : 0 ≤ |x-y|^p := Real.rpow_nonneg (abs_nonneg _) _
  have H := div_le_div_of_nonneg_right hs hd
  simp only [add_div, mul_div_assoc] at H
  apply (ENNReal.ofReal_le_ofReal H).trans_eq
  unfold differenceKernel
  rw [show 2*‖a x-a y‖^2*(‖f y‖^2/|x-y|^p) = 2*(‖a x-a y‖^2/|x-y|^p)*‖f y‖^2 by ring,
    ENNReal.ofReal_add (by positivity : 0 ≤ 2*A^2*(‖f x-f y‖^2/|x-y|^p)) (by positivity : 0 ≤ 2*(‖a x-a y‖^2/|x-y|^p)*‖f y‖^2),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2*A^2),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(‖a x-a y‖^2/|x-y|^p)),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma differenceKernel_measurable {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f : ℝ → E) (hf : Continuous f) :
    Measurable (Function.uncurry (differenceKernel p f)) := by
  unfold differenceKernel Function.uncurry
  have hc : Continuous fun z : ℝ×ℝ => ‖f z.1-f z.2‖ :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
  exact ((hc.measurable.pow_const 2).div
    ((continuous_fst.sub continuous_snd).abs.measurable.pow_const p)).ennreal_ofReal

lemma differenceEnergy_mul_le_of_row_bound {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (a f : ℝ → 𝕜) (hac : Continuous a) (hfc : Continuous f)
    (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x, ‖a x‖ ≤ A)
    (C : ℝ≥0∞) (hC : ∀ y, (∫⁻ x, differenceKernel p a x y) ≤ C)
    (U : Set ℝ) :
    differenceEnergy p (a*f) U ≤ ENNReal.ofReal (2*A^2) * differenceEnergy p f U +
      2*C*(∫⁻ y in U, ENNReal.ofReal (‖f y‖^2)) := by
  let D := ENNReal.ofReal (2*A^2)
  have hmF := differenceKernel_measurable p f hfc
  have hmA := differenceKernel_measurable p a hac
  have hm2 : Measurable (fun z : ℝ×ℝ => 2*differenceKernel p a z.1 z.2 * ENNReal.ofReal (‖f z.2‖^2)) :=
    (measurable_const.mul hmA).mul ((hfc.comp continuous_snd).norm.measurable.pow_const 2).ennreal_ofReal
  unfold differenceEnergy
  calc
    _ ≤ ∫⁻ x in U, ∫⁻ y in U, D*differenceKernel p f x y +
        2*differenceKernel p a x y * ENNReal.ofReal (‖f y‖^2) :=
      lintegral_mono fun x => lintegral_mono fun y => differenceKernel_mul_le p a f A hA ha x y
    _ = (∫⁻ x in U, ∫⁻ y in U, D*differenceKernel p f x y) +
        ∫⁻ x in U, ∫⁻ y in U, 2*differenceKernel p a x y * ENNReal.ofReal (‖f y‖^2) := by
      calc
        _ = ∫⁻ x in U, ((∫⁻ y in U, D*differenceKernel p f x y) +
            ∫⁻ y in U, 2*differenceKernel p a x y*ENNReal.ofReal (‖f y‖^2)) := by
          apply lintegral_congr
          intro x
          exact lintegral_add_left ((measurable_const.mul hmF).comp (measurable_const.prodMk measurable_id)) _
        _ = _ := lintegral_add_left ((measurable_const.mul hmF).lintegral_prod_right) _
    _ = D*(∫⁻ x in U, ∫⁻ y in U, differenceKernel p f x y) +
        ∫⁻ y in U, ∫⁻ x in U, 2*differenceKernel p a x y * ENNReal.ofReal (‖f y‖^2) := by
      congr 1
      · dsimp only [D]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      · exact lintegral_lintegral_swap hm2.aemeasurable
    _ ≤ D*(∫⁻ x in U, ∫⁻ y in U, differenceKernel p f x y) +
        ∫⁻ y in U, 2*C*ENNReal.ofReal (‖f y‖^2) := by
      apply add_le_add le_rfl
      apply lintegral_mono
      intro y
      dsimp only
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
      exact mul_le_mul' (mul_le_mul' le_rfl ((show (∫⁻ x in U, differenceKernel p a x y) ≤ ∫⁻ x, differenceKernel p a x y by simpa using lintegral_mono_set (μ := volume) (f := fun x => differenceKernel p a x y) (subset_univ U)).trans (hC y))) le_rfl
    _ = _ := by rw [lintegral_const_mul _ ((hfc.norm.measurable.pow_const 2).ennreal_ofReal)]

lemma differenceEnergy_mul_bound {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (hp1 : 1 < p) (hp3 : p < 3)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : ℝ → 𝕜), Continuous f → ∀ U : Set ℝ,
      differenceEnergy p (a*f) U ≤
        C*(differenceEnergy p f U + ∫⁻ y in U, ENNReal.ofReal (‖f y‖^2)) := by
  obtain ⟨A, hAb⟩ := hc.exists_bound_of_continuous ha.continuous
  let A' := max A 0
  have hA : 0 ≤ A' := le_max_right _ _
  have hAb' : ∀ x, ‖a x‖ ≤ A' := fun x => (hAb x).trans (le_max_left _ _)
  obtain ⟨B, hB⟩ := ha.lipschitzWith_of_hasCompactSupport hc (by norm_num)
  obtain ⟨C, hC, hrow⟩ := cutoff_row_energy_bound p hp1 hp3 a A' hA hAb' B hB
  let D := ENNReal.ofReal (2*A'^2)+2*C
  refine ⟨D, ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by norm_num) hC⟩,
    fun f hf U => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2*A'^2)*differenceEnergy p f U + 2*C*∫⁻ y in U, ENNReal.ofReal (‖f y‖^2) :=
      differenceEnergy_mul_le_of_row_bound p a f ha.continuous hf A' hA hAb' C hrow U
    _ ≤ D*(differenceEnergy p f U+∫⁻ y in U, ENNReal.ofReal (‖f y‖^2)) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul' le_self_add le_rfl) (mul_le_mul' le_add_self le_rfl)

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

lemma differenceEnergy_congrOn {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f g : ℝ → E) (U : Set ℝ) (hU : MeasurableSet U)
    (hfg : EqOn f g U) : differenceEnergy p f U = differenceEnergy p g U := by
  apply setLIntegral_congr_fun hU
  intro x hx
  apply setLIntegral_congr_fun hU
  intro y hy
  simp only [differenceKernel, hfg hx, hfg hy]

lemma differenceEnergy_mono_set {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f : ℝ → E) {U V : Set ℝ} (hUV : U ⊆ V) :
    differenceEnergy p f U ≤ differenceEnergy p f V := by
  unfold differenceEnergy
  exact (lintegral_mono fun x => lintegral_mono_set hUV).trans (lintegral_mono_set hUV)

lemma square_lintegral_comp_le {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ)
    (hi : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y)
    (J : ℝ) (hJ : ∀ y ∈ e.target, |deriv e.symm y| ≤ J) (f : ℝ → 𝕜) :
    (∫⁻ x in e.source, ENNReal.ofReal (‖f (e x)‖^2)) ≤
      ENNReal.ofReal J * ∫⁻ y, ENNReal.ofReal (‖f y‖^2) := by
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul e.open_target.measurableSet
    (fun y hy => (hi y hy).hasDerivAt.hasDerivWithinAt) e.symm.injOn
    (fun x => ENNReal.ofReal (‖f (e x)‖^2))
  rw [e.symm_image_target_eq_source] at hchange
  rw [hchange]
  calc
    _ ≤ ∫⁻ y in e.target, ENNReal.ofReal J * ENNReal.ofReal (‖f y‖^2) := by
      apply setLIntegral_mono' e.open_target.measurableSet
      intro y hy
      simp only [e.right_inv hy]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hJ y hy)) le_rfl
    _ = ENNReal.ofReal J * ∫⁻ y in e.target, ENNReal.ofReal (‖f y‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (by
      simpa only [Measure.restrict_univ] using (lintegral_mono_set (μ := volume) (f := fun y => ENNReal.ofReal (‖f y‖^2)) (subset_univ e.target)))

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve

open scoped ContDiff

/-- Compact scalar coordinate localization is bounded for the full difference
energy plus the L² term. All constants are derived before the input function. -/
lemma localizedPullback_differenceEnergy_bound {𝕜 : Type*} [RCLike 𝕜]
    (p : ℝ) (hp1 : 1 < p) (hp3 : p < 3)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℝ → 𝕜, Continuous f →
      differenceEnergy p (localizedPullback e a f) univ ≤
        C*(differenceEnergy p f univ + ∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := by
  obtain ⟨U, hU, hKU, hcl, hclc, L, J, hL, hJ, hLip, hJac⟩ :=
    compact_coordinate_restriction e (he.of_le (by simp)) (hi.of_le (by simp)) (tsupport a) hc hs
  have hUs : U ⊆ e.source := subset_closure.trans hcl
  let e' := e.restrOpen U hU
  have hsource : e'.source = U := inter_eq_right.mpr hUs
  have hi' : ∀ y ∈ e'.target, DifferentiableAt ℝ e'.symm y := by
    intro y hy
    change y ∈ e.target ∩ e.symm ⁻¹' U at hy
    exact (((hi y hy.1).contDiffAt (e.open_target.mem_nhds hy.1)).differentiableAt (by simp))
  have hJac' : ∀ y ∈ e'.target, |deriv e'.symm y| ≤ J := by
    intro y hy
    change y ∈ e.target ∩ e.symm ⁻¹' U at hy
    exact hJac y ⟨e.symm y, hy.2, e.right_inv hy.1⟩
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := compact_smoothCutoff hclc e.open_source hcl
  obtain ⟨h, hh, _, hheq, _⟩ := global_extension_of_cutoff e.source e.open_source e χ he hχ hχc hχs
  have hhe (x : ℝ) (hx : x ∈ U) : h x = e x := hheq x (hχ1 x (subset_closure hx))
  obtain ⟨CP, hCP, hmul⟩ := differenceEnergy_mul_bound p hp1 hp3 a (ha.of_le (by simp)) hc
  obtain ⟨CE, hCE, hext⟩ := compact_extension_energy_bound (E := 𝕜) p hp1 (tsupport a) hc U hU hKU
  obtain ⟨D, hD, hDb⟩ := localizedPullback_jacobian_bound e a ha.continuous hc hs
    (hi.continuousOn_deriv_of_isOpen e.open_target (by simp))
  let CC := ENNReal.ofReal (J^2*L^p)
  let CJ := ENNReal.ofReal J
  let CD := ENNReal.ofReal (D^2)
  let C := CP*(CC+CJ)+CE*CD
  have hCC : CC < ⊤ := ENNReal.ofReal_lt_top
  have hCJ : CJ < ⊤ := ENNReal.ofReal_lt_top
  have hCD : CD < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨C, ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hCP
      (ENNReal.add_lt_top.mpr ⟨hCC, hCJ⟩), ENNReal.mul_lt_top hCE hCD⟩, ?_⟩
  intro f hf
  let g : ℝ → 𝕜 := f ∘ h
  have hg : Continuous g := hf.comp hh.continuous
  have hloc : localizedPullback e a f = a*g := by
    ext x
    by_cases hx : x ∈ tsupport a
    · simp [localizedPullback, hs hx, g, hhe x (hKU hx)]
    · have hax := image_eq_zero_of_notMem_tsupport hx
      simp [localizedPullback, hax]
  have hgc : Continuous (localizedPullback e a f) := by rw [hloc]; exact ha.continuous.mul hg
  have hEq : EqOn g (f ∘ e') U := by intro x hx; simp [g, hhe x hx, e']
  have hcomp : differenceEnergy p g U ≤ CC*differenceEnergy p f univ := by
    rw [differenceEnergy_congrOn p g (f ∘ e') U hU.measurableSet hEq, ← hsource]
    exact (differenceEnergy_comp_le p (by linarith) f e' hi' L J hL hJ
      (fun x hx y hy => hLip x (hsource ▸ hx) y (hsource ▸ hy)) hJac').trans
      (mul_le_mul' le_rfl (differenceEnergy_mono_set p f (subset_univ e'.target)))
  have hgL2 : (∫⁻ x in U, ENNReal.ofReal (‖g x‖^2)) ≤ CJ*∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
    calc
      _ = ∫⁻ x in e'.source, ENNReal.ofReal (‖f (e' x)‖^2) := by
        rw [hsource]
        apply setLIntegral_congr_fun hU.measurableSet
        intro x hx
        dsimp only
        rw [hEq hx]
        rfl
      _ ≤ _ := square_lintegral_comp_le e' hi' J hJac' f
  have hlocL2 : (∫⁻ x in U, ENNReal.ofReal (‖localizedPullback e a f x‖^2)) ≤
      CD*∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
    have H := localizedPullback_energy_le e (fun y hy =>
      ((hi y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)) a f hDb
    simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at H
    exact (show (∫⁻ x in U, ENNReal.ofReal (‖localizedPullback e a f x‖^2)) ≤
      ∫⁻ x, ENNReal.ofReal (‖localizedPullback e a f x‖^2) by
      simpa only [Measure.restrict_univ] using lintegral_mono_set (μ := volume)
        (f := fun x => ENNReal.ofReal (‖localizedPullback e a f x‖^2)) (subset_univ U)).trans H
  calc
    _ ≤ differenceEnergy p (localizedPullback e a f) U +
        CE*(∫⁻ x in U, ENNReal.ofReal (‖localizedPullback e a f x‖^2)) :=
      hext _ hgc (localizedPullback_tsupport_subset e a f)
    _ ≤ CP*(CC*differenceEnergy p f univ+CJ*∫⁻ x, ENNReal.ofReal (‖f x‖^2)) +
        CE*(CD*∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := by
      apply add_le_add
      · rw [hloc]
        exact (hmul g hg U).trans (mul_le_mul' le_rfl (add_le_add hcomp hgL2))
      · exact mul_le_mul' le_rfl hlocL2
    _ ≤ C*(differenceEnergy p f univ+∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := by
      let E := differenceEnergy p f univ
      let N := ∫⁻ x, ENNReal.ofReal (‖f x‖^2)
      change CP*(CC*E+CJ*N)+CE*(CD*N) ≤ C*(E+N)
      have hsum : CC*E+CJ*N ≤ (CC+CJ)*(E+N) := by
        rw [add_mul]
        exact add_le_add (mul_le_mul' le_rfl le_self_add) (mul_le_mul' le_rfl le_add_self)
      calc
        _ ≤ CP*((CC+CJ)*(E+N))+(CE*CD)*(E+N) :=
          add_le_add (mul_le_mul' le_rfl hsum) (by
            rw [← mul_assoc]
            exact mul_le_mul' le_rfl le_add_self)
        _ = _ := by dsimp only [C]; ring

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
open scoped ContDiff

lemma localizedPullback_fractionalEnergy_bound {𝕜 : Type*} [RCLike 𝕜]
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℝ → 𝕜, Continuous f →
      (differenceEnergy (1+2*σ) (localizedPullback e a f) univ +
          ∫⁻ x, ENNReal.ofReal (‖localizedPullback e a f x‖^2)) ≤
        C*(differenceEnergy (1+2*σ) f univ + ∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := by
  obtain ⟨CE, hCE, hE⟩ := localizedPullback_differenceEnergy_bound (1+2*σ)
    (by linarith) (by linarith) e he hi a ha hc hs
  obtain ⟨D, hD, hDb⟩ := localizedPullback_jacobian_bound e a ha.continuous hc hs
    (hi.continuousOn_deriv_of_isOpen e.open_target (by simp))
  let CD := ENNReal.ofReal (D^2)
  refine ⟨CE+CD, ENNReal.add_lt_top.mpr ⟨hCE, ENNReal.ofReal_lt_top⟩, ?_⟩
  intro f hf
  have hL := localizedPullback_energy_le e (fun y hy =>
    ((hi y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)) a f hDb
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hL
  calc
    _ ≤ CE*(differenceEnergy (1+2*σ) f univ+∫⁻ x, ENNReal.ofReal (‖f x‖^2)) +
        CD*(∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := add_le_add (hE f hf) hL
    _ ≤ CE*(differenceEnergy (1+2*σ) f univ+∫⁻ x, ENNReal.ofReal (‖f x‖^2)) +
        CD*(differenceEnergy (1+2*σ) f univ+∫⁻ x, ENNReal.ofReal (‖f x‖^2)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl le_add_self)
    _ = _ := (add_mul _ _ _).symm

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

def schwartzHs {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) : Hs d s :=
  (coordinates d s).symm
    ((SchwartzMap.smulLeftCLM ℂ (complexWeight s) (schwartzFourier f)).toLp 2)

lemma schwartzHs_realization {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) :
    realization (schwartzHs s f) = schwartzRegularDistribution f := by
  apply weighted_fourier_injective d s
  dsimp only
  rw [weighted_fourier_realization, Inversion.fourier_regular_distribution]
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, Inversion.regular_distribution_pairing]
  apply integral_congr_ae
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (complexWeight s)
    (schwartzFourier f)).coeFn_toLp 2] with ξ hξ
  simp only [schwartzHs, LinearIsometryEquiv.apply_symm_apply] at *
  rw [hξ]
  simp only [SchwartzMap.smulLeftCLM_apply_apply
    (complexWeight_hasTemperateGrowth s), smul_eq_mul]
  ring

lemma schwartzHs_norm_sq {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) :
    ‖schwartzHs s f‖ ^ 2 = ∫ ξ, frequencyWeight ξ ^ s * ‖schwartzFourier f ξ‖ ^ 2 := by
  rw [schwartzHs, LinearIsometryEquiv.norm_map, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (complexWeight s)
    (schwartzFourier f)).coeFn_toLp 2] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth s)]
  simp only [smul_eq_mul, norm_mul, complexWeight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (weight_pos s ξ), mul_pow, weight_sq]

lemma schwartzHs_norm_sq_lintegral {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) :
    ENNReal.ofReal (‖schwartzHs s f‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (frequencyWeight ξ ^ s) * ‖schwartzFourier f ξ‖ₑ ^ 2 := by
  let g := SchwartzMap.smulLeftCLM ℂ (complexWeight s) (schwartzFourier f)
  have hi := (g.memLp 2).integrable_norm_pow (by decide)
  have he : (fun ξ => ‖g ξ‖ ^ 2) =
      (fun ξ => frequencyWeight ξ ^ s * ‖schwartzFourier f ξ‖ ^ 2) := by
    ext ξ
    simp only [g, SchwartzMap.smulLeftCLM_apply_apply (complexWeight_hasTemperateGrowth s),
      smul_eq_mul, norm_mul, complexWeight, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (weight_pos s ξ), mul_pow, weight_sq]
  rw [he] at hi
  rw [schwartzHs_norm_sq, ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [] with ξ
    exact mul_nonneg (Real.rpow_nonneg (frequencyWeight_pos ξ).le s) (sq_nonneg _))]
  apply lintegral_congr
  intro ξ
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (frequencyWeight_pos ξ).le s), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma lineSchwartzToEuclidean_fourier (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    schwartzFourier (lineSchwartzToEuclidean f) (realLineIsometry ξ) = 𝓕 (⇑f) ξ := by
  exact fourier_realLineIsometry f ξ

lemma line_schwartz_hs_norm_sq (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ENNReal.ofReal (‖schwartzHs s (lineSchwartzToEuclidean f)‖ ^ 2) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ s) *
        ‖𝓕 (⇑f) ξ‖ₑ ^ 2 := by
  rw [schwartzHs_norm_sq_lintegral, ← realLineIsometry_lintegral]
  apply lintegral_congr
  intro ξ
  rw [lineSchwartzToEuclidean_fourier]
  congr 3
  simp only [frequencyWeight, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]

lemma line_schwartz_plancherel_lintegral (f : SchwartzMap ℝ ℂ) :
    (∫⁻ ξ : ℝ, ‖𝓕 (⇑f) ξ‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 := by
  have hp := congrArg ENNReal.ofReal (SchwartzMap.integral_norm_sq_fourier f)
  rw [ofReal_integral_eq_lintegral_ofReal
      ((𝓕 f).memLp (μ := volume) 2 |>.integrable_norm_pow (by norm_num))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal
      (f.memLp (μ := volume) 2 |>.integrable_norm_pow (by norm_num))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)] at hp
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, SchwartzMap.fourier_coe] using hp

lemma line_schwartz_fractional_energy (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (f : SchwartzMap ℝ ℂ) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) +
      (ENNReal.ofReal (∫ t, fractionalKernel σ t))⁻¹ *
        differenceEnergy (1 + 2 * σ) f univ =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (1 + |ξ| ^ (2 * σ)) * ‖𝓕 (⇑f) ξ‖ₑ ^ 2 := by
  have hc : ENNReal.ofReal (∫ t, fractionalKernel σ t) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (fractionalKernel_integral_pos σ hσ0 hσ1)
  rw [fractional_plancherel σ hσ0 hσ1 f f.continuous f.integrable (f.memLp 2),
    ← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_mul,
    ← line_schwartz_plancherel_lintegral]
  simp_rw [ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1)
    (Real.rpow_nonneg (abs_nonneg _) _), ENNReal.ofReal_one, add_mul, one_mul]
  rw [lintegral_add_left]
  exact ((𝓕 f).continuous.enorm.measurable.pow_const 2)

lemma line_schwartz_fractional_norm_comparison (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (f : SchwartzMap ℝ ℂ) :
    let E := (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) +
      (ENNReal.ofReal (∫ t, fractionalKernel σ t))⁻¹ *
        differenceEnergy (1 + 2 * σ) f univ
    let N := ENNReal.ofReal (‖schwartzHs σ (lineSchwartzToEuclidean f)‖ ^ 2)
    E ≤ 2 * N ∧
      N ≤ ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ σ) * E := by
  dsimp only
  rw [line_schwartz_fractional_energy σ hσ0 hσ1,
    line_schwartz_hs_norm_sq]
  constructor
  · rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply lintegral_mono
    intro ξ
    dsimp only
    rw [← mul_assoc]
    apply mul_le_mul' ?_ le_rfl
    have hh := ENNReal.ofReal_le_ofReal (fractional_frequency_weight_lower σ ξ hσ0.le)
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hh
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro ξ
    dsimp only
    rw [← mul_assoc]
    apply mul_le_mul' ?_ le_rfl
    have hh := ENNReal.ofReal_le_ofReal (fractional_frequency_weight_upper σ ξ hσ0.le)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + 4 * Real.pi ^ 2) σ)] at hh
    exact hh

lemma schwartzHs_unique {d : ℕ} (s : ℝ) (f : Schwartz ℂ d) (u : Hs d s)
    (hu : realization u = schwartzRegularDistribution f) : u = schwartzHs s f :=
  realization_injective d s (hu.trans (schwartzHs_realization s f).symm)

lemma line_schwartz_hs_norm_integrable (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ s * ‖𝓕 (⇑f) ξ‖ ^ 2) := by
  let g := SchwartzMap.smulLeftCLM ℂ (complexWeight s)
    (schwartzFourier (lineSchwartzToEuclidean f))
  have hi := (g.memLp (μ := volume) 2).integrable_norm_pow (by decide)
  have h := realLineIsometry.measurePreserving.integrable_comp_emb
    realLineIsometry.toMeasurableEquiv.measurableEmbedding |>.mpr hi
  convert h using 1
  ext ξ
  simp only [Function.comp_apply, g, SchwartzMap.smulLeftCLM_apply_apply
    (complexWeight_hasTemperateGrowth s), smul_eq_mul, norm_mul, complexWeight,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos s _), mul_pow, weight_sq,
    lineSchwartzToEuclidean_fourier, frequencyWeight, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs]

lemma line_schwartz_hs_norm_sq_real (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzHs s (lineSchwartzToEuclidean f)‖ ^ 2 =
      ∫ ξ : ℝ, (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ s * ‖𝓕 (⇑f) ξ‖ ^ 2 := by
  rw [schwartzHs_norm_sq,
    ← realLineIsometry.measurePreserving.integral_comp
      realLineIsometry.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [lineSchwartzToEuclidean_fourier]
  congr 2
  simp only [frequencyWeight, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]

lemma lineSchwartzDeriv_fourier (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (⇑(lineSchwartzDeriv f)) ξ =
      (2 * Real.pi * Complex.I) * (ξ : ℂ) * 𝓕 (⇑f) ξ := by
  rw [← SchwartzMap.fourier_coe]
  change (𝓕 (LineDeriv.lineDerivOp (1 : ℝ) f)) ξ = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : ℝ => x).HasTemperateGrowth := by fun_prop
  simp only [Real.inner_apply, mul_one]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal, SchwartzMap.fourier_coe]
  ring

lemma lineSchwartzDeriv_fourier_norm_sq (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ‖𝓕 (⇑(lineSchwartzDeriv f)) ξ‖ ^ 2 =
      (4 * Real.pi ^ 2 * |ξ| ^ 2) * ‖𝓕 (⇑f) ξ‖ ^ 2 := by
  rw [lineSchwartzDeriv_fourier]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, mul_pow, sq_abs]
  ring

lemma line_schwartz_hs_successor (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖schwartzHs (s+1) (lineSchwartzToEuclidean f)‖ ^ 2 =
      ‖schwartzHs s (lineSchwartzToEuclidean f)‖ ^ 2 +
        ‖schwartzHs s (lineSchwartzToEuclidean (lineSchwartzDeriv f))‖ ^ 2 := by
  simp_rw [line_schwartz_hs_norm_sq_real]
  rw [← integral_add (line_schwartz_hs_norm_integrable s f)
    (line_schwartz_hs_norm_integrable s (lineSchwartzDeriv f))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [lineSchwartzDeriv_fourier_norm_sq,
    Real.rpow_add (by positivity : 0 < 1 + 4 * Real.pi ^ 2 * |ξ| ^ 2), Real.rpow_one]
  ring

def schwartzHsCLM (d : ℕ) (s : ℝ) : Schwartz ℂ d →L[ℂ] Hs d s :=
  (coordinates d s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((SchwartzMap.toLpCLM ℂ ℂ 2).comp
      ((SchwartzMap.smulLeftCLM ℂ (complexWeight s)).comp schwartzFourier))

@[simp] lemma schwartzHsCLM_apply (d : ℕ) (s : ℝ) (f : Schwartz ℂ d) :
    schwartzHsCLM d s f = schwartzHs s f := rfl

lemma schwartzHs_dense (d : ℕ) (s : ℝ) : DenseRange (schwartzHsCLM d s) := by
  apply Dense.mono ?_ (schwartz_dense d s)
  rintro u ⟨f, hf⟩
  exact ⟨f, (schwartzHs_unique s f u hf).symm⟩

/-- A proved bound on actual Schwartz representatives extends uniquely to Hs.
No coordinate boundedness assertion is assumed by this extension lemma. -/
lemma schwartz_operator_extension (d : ℕ) (s : ℝ)
    (P : Schwartz ℂ d →ₗ[ℂ] Schwartz ℂ d) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ f, ‖schwartzHs s (P f)‖ ≤ C * ‖schwartzHs s f‖) :
    ∃! A : Hs d s →L[ℂ] Hs d s,
      ‖A‖ ≤ C ∧ ∀ f, A (schwartzHs s f) = schwartzHs s (P f) := by
  let e := (schwartzHsCLM d s).toLinearMap
  let g := (schwartzHsCLM d s).toLinearMap.comp P
  let A : Hs d s →L[ℂ] Hs d s := g.extendOfNorm e
  have hA : ∀ f, A (schwartzHs s f) = schwartzHs s (P f) := by
    intro f
    exact LinearMap.extendOfNorm_eq (schwartzHs_dense d s) ⟨C, hP⟩ f
  refine ⟨A, ⟨LinearMap.opNorm_extendOfNorm_le (schwartzHs_dense d s) hC hP, hA⟩, ?_⟩
  intro B hB
  apply DFunLike.ext
  intro u
  exact (schwartzHs_dense d s).induction_on u (isClosed_eq B.continuous A.continuous)
    (fun f => (hB.2 f).trans (hA f).symm)

lemma hs_realization_test_continuous (d : ℕ) (s : ℝ) (φ : Schwartz ℂ d) :
    Continuous (fun u : Hs d s => realization u φ) := by
  obtain ⟨e, he⟩ := duality d s
  have hv := schwartzHs_realization (-s) φ
  have h : (fun u : Hs d s => realization u φ) =
      fun u => e (schwartzHs (-s) φ) u := by
    funext u
    exact ((he u (schwartzHs (-s) φ)).trans
      (pairing_test d s u φ (schwartzHs (-s) φ) hv)).symm
  rw [h]
  exact (e (schwartzHs (-s) φ)).continuous

/-- Agreement with a test-density transpose on Schwartz representatives
passes to the genuine distribution realization of the Hs extension. -/
lemma schwartz_extension_realization (d : ℕ) (s : ℝ)
    (P Q : Schwartz ℂ d →L[ℂ] Schwartz ℂ d)
    (A : Hs d s →L[ℂ] Hs d s)
    (hA : ∀ f, A (schwartzHs s f) = schwartzHs s (P f))
    (hPQ : ∀ f φ, schwartzRegularDistribution (P f) φ =
      schwartzRegularDistribution f (Q φ)) (u : Hs d s) :
    realization (A u) = (realization u).comp Q := by
  ext φ
  change realization (A u) φ = realization u (Q φ)
  refine (schwartzHs_dense d s).induction_on (p := fun v : Hs d s =>
    realization (A v) φ = realization v (Q φ)) u
    (isClosed_eq ((hs_realization_test_continuous d s φ).comp A.continuous)
      (hs_realization_test_continuous d s (Q φ))) ?_
  intro f
  change realization (A (schwartzHs s f)) φ = realization (schwartzHs s f) (Q φ)
  rw [hA, schwartzHs_realization, schwartzHs_realization]
  exact hPQ f φ

end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

theorem localized_fractional_energy :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.localizedFractionalEnergyType := by
  intro 𝕜 _ σ hσ0 hσ1 e he hi a ha hc hs
  exact localizedPullback_fractionalEnergy_bound σ hσ0 hσ1 e he hi a ha hc hs

theorem line_schwartz_hs :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.lineSchwartzHsType := by
  intro s f
  exact ⟨schwartzHs s (lineSchwartzToEuclidean f), schwartzHs_realization s _,
    line_schwartz_hs_norm_sq s f⟩

theorem fractional_hs_comparison :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.fractionalHsComparisonType := by
  intro σ hσ0 hσ1 f u hu
  rw [schwartzHs_unique σ _ u hu]
  exact line_schwartz_fractional_norm_comparison σ hσ0 hσ1 f

theorem successor_hs :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.successorHsType := by
  intro s f u v w hu hv hw
  rw [schwartzHs_unique (s + 1) _ u hu, schwartzHs_unique s _ v hv,
    schwartzHs_unique s _ w hw]
  exact line_schwartz_hs_successor s f

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ExpandedFA.Sobolev.Curve

def localizedDerivativeCoefficient {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a : ℝ → 𝕜) : ℝ → 𝕜 :=
  e.source.indicator (fun x => deriv e x • a x)

lemma localizedDerivativeCoefficient_tsupport_subset {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a : ℝ → 𝕜) :
    tsupport (localizedDerivativeCoefficient e a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx hxa
  have hax : a x = 0 := by simpa only [Function.mem_support, not_not] using hxa
  exact hx (by simp [localizedDerivativeCoefficient, hax])

lemma localizedDerivativeCoefficient_contDiff {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (he : ContDiffOn ℝ ∞ e e.source)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ e.source) :
    ContDiff ℝ ∞ (localizedDerivativeCoefficient e a) := by
  apply contDiff_indicator_of_support e.source e.open_source
  · exact (he.deriv_of_isOpen e.open_source (by simp)).smul ha.contDiffOn
  · exact (localizedDerivativeCoefficient_tsupport_subset e a).trans hs

lemma localizedDerivativeCoefficient_hasCompactSupport {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a : ℝ → 𝕜) (hc : HasCompactSupport a) :
    HasCompactSupport (localizedDerivativeCoefficient e a) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (localizedDerivativeCoefficient_tsupport_subset e a)

lemma deriv_localizedPullback {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (he : ContDiffOn ℝ ∞ e e.source)
    (a f : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (hs : tsupport a ⊆ e.source) :
    deriv (localizedPullback e a f) =
      localizedPullback e (deriv a) f +
        localizedPullback e (localizedDerivativeCoefficient e a) (deriv f) := by
  ext x
  by_cases hx : x ∈ e.source
  · have hex := ((he x hx).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    have hfx := hf.differentiable (by simp) (e x)
    have hax := ha.differentiable (by simp) x
    have hc := hax.hasDerivAt.mul (hfx.hasDerivAt.scomp x hex.hasDerivAt)
    have hcongr : localizedPullback e a f =ᶠ[𝓝 x] a * (f ∘ e) := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      simp [localizedPullback, hy]
    rw [hc.congr_of_eventuallyEq hcongr |>.deriv]
    simp only [Pi.add_apply, localizedPullback, indicator_of_mem hx,
      localizedDerivativeCoefficient, Function.comp_apply]
    rw [smul_mul_assoc, mul_smul_comm]
  · have hxa : x ∉ tsupport a := fun h => hx (hs h)
    have hxloc : x ∉ tsupport (localizedPullback e a f) :=
      fun h => hxa (localizedPullback_tsupport_subset e a f h)
    change deriv (localizedPullback e a f) x = _
    rw [deriv_of_notMem_tsupport hxloc]
    simp [localizedPullback, hx]

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

lemma ennreal_weighted_sum_compare (c a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a + c⁻¹*b ≤ (1+c⁻¹)*(a+b) ∧
      a+b ≤ (1+c)*(a+c⁻¹*b) := by
  constructor
  · calc
      a+c⁻¹*b = 1*a+c⁻¹*b := by rw [one_mul]
      _ ≤ (1+c⁻¹)*a+(1+c⁻¹)*b := add_le_add
        (mul_le_mul' le_self_add le_rfl) (mul_le_mul' le_add_self le_rfl)
      _ = _ := (mul_add _ _ _).symm
  · calc
      a+b = 1*a+c*(c⁻¹*b) := by rw [← mul_assoc, ENNReal.mul_inv_cancel hc hc', one_mul, one_mul]
      _ ≤ (1+c)*a+(1+c)*(c⁻¹*b) := add_le_add
        (mul_le_mul' le_self_add le_rfl) (mul_le_mul' le_add_self le_rfl)
      _ = _ := (mul_add _ _ _).symm

lemma line_schwartz_fractional_bound_of_energy
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (P : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hP : ∀ f : SchwartzMap ℝ ℂ,
      (differenceEnergy (1+2*σ) (P f) univ + ∫⁻ x, ENNReal.ofReal (‖P f x‖^2)) ≤
        C*(differenceEnergy (1+2*σ) f univ + ∫⁻ x, ENNReal.ofReal (‖f x‖^2))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzHs σ (lineSchwartzToEuclidean (P f))‖ ≤
        D * ‖schwartzHs σ (lineSchwartzToEuclidean f)‖ := by
  let c := ENNReal.ofReal (∫ t, fractionalKernel σ t)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (fractionalKernel_integral_pos σ hσ0 hσ1)
  have hc' : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let B := ENNReal.ofReal ((1+4*Real.pi^2)^σ)
  let N (f : SchwartzMap ℝ ℂ) :=
    ENNReal.ofReal (‖schwartzHs σ (lineSchwartzToEuclidean f)‖^2)
  let R (f : SchwartzMap ℝ ℂ) :=
    differenceEnergy (1+2*σ) f univ + ∫⁻ x, ENNReal.ofReal (‖f x‖^2)
  let E (f : SchwartzMap ℝ ℂ) :=
    (∫⁻ x, ‖f x‖ₑ^2) + c⁻¹*differenceEnergy (1+2*σ) f univ
  have hcR (f : SchwartzMap ℝ ℂ) :
      E f ≤ (1+c⁻¹)*R f ∧ R f ≤ (1+c)*E f := by
    have h := ennreal_weighted_sum_compare c (∫⁻ x, ‖f x‖ₑ^2)
      (differenceEnergy (1+2*σ) f univ) hc hc'
    simpa only [E, R, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      add_comm (differenceEnergy (1+2*σ) f univ)] using h
  have hn (f : SchwartzMap ℝ ℂ) : E f ≤ 2*N f ∧ N f ≤ B*E f :=
    line_schwartz_fractional_norm_comparison σ hσ0 hσ1 f
  let K := B*(1+c⁻¹)*C*((1+c)*2)
  have hK : K < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc)⟩)) hC)
      (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩)
        (by norm_num))
  have hb (f : SchwartzMap ℝ ℂ) : N (P f) ≤ K*N f := by
    calc
      N (P f) ≤ B*E (P f) := (hn (P f)).2
      _ ≤ B*((1+c⁻¹)*R (P f)) := mul_le_mul' le_rfl (hcR (P f)).1
      _ ≤ B*((1+c⁻¹)*(C*R f)) := mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (hP f))
      _ ≤ B*((1+c⁻¹)*(C*((1+c)*E f))) := mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hcR f).2))
      _ ≤ B*((1+c⁻¹)*(C*((1+c)*(2*N f)))) := mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hn f).1)))
      _ = K*N f := by dsimp only [K]; ring
  refine ⟨Real.sqrt K.toReal, Real.sqrt_nonneg _, fun f => ?_⟩
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hK.ne ENNReal.ofReal_ne_top) (hb f)
  simp only [N, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg] using hr

lemma localizedPullback_fractional_schwartz_bound
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source)
    (P : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hP : ∀ f x, P f x = localizedPullback e a f x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖schwartzHs σ (lineSchwartzToEuclidean (P f))‖ ≤
        D * ‖schwartzHs σ (lineSchwartzToEuclidean f)‖ := by
  obtain ⟨C, hC, hE⟩ := localizedPullback_fractionalEnergy_bound σ hσ0 hσ1 e he hi a ha hc hs
  apply line_schwartz_fractional_bound_of_energy σ hσ0 hσ1 P C hC
  intro f
  have hpf : (⇑(P f)) = localizedPullback e a f := funext (hP f)
  simpa only [hpf] using hE f f.continuous


def lineSchwartzHsCLM (s : ℝ) : SchwartzMap ℝ ℂ →L[ℂ] Hs 1 s :=
  (schwartzHsCLM 1 s).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    realLineIsometry.symm.toContinuousLinearEquiv)

@[simp] lemma lineSchwartzHsCLM_apply (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    lineSchwartzHsCLM s f = schwartzHs s (lineSchwartzToEuclidean f) := rfl

lemma lineSchwartzHsCLM_dense (s : ℝ) : DenseRange (lineSchwartzHsCLM s) := by
  apply Dense.mono ?_ (schwartzHs_dense 1 s)
  rintro u ⟨f, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    realLineIsometry.toContinuousLinearEquiv f, ?_⟩
  change schwartzHs s _ = schwartzHs s f
  congr 1
  ext x
  exact congrArg f (realLineIsometry.apply_symm_apply x)

lemma line_schwartz_operator_extension (s : ℝ)
    (P : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ f, ‖schwartzHs s (lineSchwartzToEuclidean (P f))‖ ≤
      C * ‖schwartzHs s (lineSchwartzToEuclidean f)‖) :
    ∃! A : Hs 1 s →L[ℂ] Hs 1 s,
      ‖A‖ ≤ C ∧ ∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
        schwartzHs s (lineSchwartzToEuclidean (P f)) := by
  let e := (lineSchwartzHsCLM s).toLinearMap
  let g := (lineSchwartzHsCLM s).toLinearMap.comp P.toLinearMap
  let A : Hs 1 s →L[ℂ] Hs 1 s := g.extendOfNorm e
  have hA : ∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
      schwartzHs s (lineSchwartzToEuclidean (P f)) := by
    intro f
    exact LinearMap.extendOfNorm_eq (lineSchwartzHsCLM_dense s) ⟨C, hP⟩ f
  refine ⟨A, ⟨LinearMap.opNorm_extendOfNorm_le (lineSchwartzHsCLM_dense s) hC hP, hA⟩, ?_⟩
  intro B hB
  apply DFunLike.ext
  intro u
  exact (lineSchwartzHsCLM_dense s).induction_on u (isClosed_eq B.continuous A.continuous)
    (fun f => (hB.2 f).trans (hA f).symm)

lemma line_schwartz_regular_pairing (f φ : SchwartzMap ℝ ℂ) :
    schwartzRegularDistribution (lineSchwartzToEuclidean f) (lineSchwartzToEuclidean φ) =
      ∫ x : ℝ, f x * φ x := by
  rw [Inversion.regular_distribution_pairing,
    ← realLineIsometry.measurePreserving.integral_comp
      realLineIsometry.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with x
  change f (realLineIsometry.symm (realLineIsometry x)) *
    φ (realLineIsometry.symm (realLineIsometry x)) = _
  rw [realLineIsometry.symm_apply_apply]

lemma line_schwartz_extension_realization (s : ℝ)
    (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (hA : ∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
      schwartzHs s (lineSchwartzToEuclidean (P f)))
    (hPQ : ∀ f φ, (∫ x : ℝ, P f x * φ x) = ∫ x : ℝ, f x * Q φ x)
    (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ) :
    realization (A u) (lineSchwartzToEuclidean φ) =
      realization u (lineSchwartzToEuclidean (Q φ)) := by
  refine (lineSchwartzHsCLM_dense s).induction_on (p := fun v : Hs 1 s =>
    realization (A v) (lineSchwartzToEuclidean φ) =
      realization v (lineSchwartzToEuclidean (Q φ))) u
    (isClosed_eq ((hs_realization_test_continuous 1 s _).comp A.continuous)
      (hs_realization_test_continuous 1 s _)) ?_
  intro f
  change realization (A (schwartzHs s (lineSchwartzToEuclidean f)))
    (lineSchwartzToEuclidean φ) = realization (schwartzHs s (lineSchwartzToEuclidean f))
      (lineSchwartzToEuclidean (Q φ))
  rw [hA, schwartzHs_realization, schwartzHs_realization,
    line_schwartz_regular_pairing, line_schwartz_regular_pairing]
  exact hPQ f φ

lemma localizedPullback_fractional_Hs_bound
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 σ →L[ℂ] Hs 1 σ) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ f, A (schwartzHs σ (lineSchwartzToEuclidean f)) =
        schwartzHs σ (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 σ) (φ : SchwartzMap ℝ ℂ),
        realization (A u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ))) := by
  obtain ⟨P, hP⟩ := localizedSchwartzPullback_exists e he a ha hc hs
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  obtain ⟨C, hC, hb⟩ := localizedPullback_fractional_schwartz_bound σ hσ0 hσ1
    e he hi a ha hc hs P hP
  obtain ⟨A, hA, _⟩ := line_schwartz_operator_extension σ P C hC hb
  refine ⟨P, Q, A, C, hC, hA.1, hP, hQ, hA.2, ?_⟩
  apply line_schwartz_extension_realization σ P Q A hA.2
  intro f φ
  have hd : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y := by
    intro y hy
    exact (hi.differentiableOn (by simp) y hy).differentiableAt (e.open_target.mem_nhds hy)
  calc
    _ = ∫ x, localizedPullback e a f x * φ x := by simp_rw [hP]
    _ = ∫ x, f x * localizedDensity e a φ x := localizedPullback_pairing e hd a f φ
    _ = _ := by simp_rw [hQ]

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale
lemma lineSchwartzDeriv_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzDeriv f x = deriv (⇑f) x := rfl

lemma lineSchwartzDeriv_localizedPullback
    (e : OpenPartialHomeomorph ℝ ℝ) (he : ContDiffOn ℝ ∞ e e.source)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ e.source)
    (P P₁ P₂ : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (hP : ∀ f x, P f x = localizedPullback e a f x)
    (hP₁ : ∀ f x, P₁ f x = localizedPullback e (deriv a) f x)
    (hP₂ : ∀ f x, P₂ f x = localizedPullback e (localizedDerivativeCoefficient e a) f x)
    (f : SchwartzMap ℝ ℂ) :
    lineSchwartzDeriv (P f) = P₁ f + P₂ (lineSchwartzDeriv f) := by
  ext x
  have hPf : (⇑(P f)) = localizedPullback e a f := funext (hP f)
  simp only [lineSchwartzDeriv_apply, hPf]
  rw [deriv_localizedPullback e he a f ha (f.smooth ⊤) hs]
  change localizedPullback e (deriv a) f x +
    localizedPullback e (localizedDerivativeCoefficient e a) (deriv (⇑f)) x =
      P₁ f x + P₂ (lineSchwartzDeriv f) x
  rw [hP₁, hP₂]
  rfl

/-- The bound quantifies over the actual Schwartz scalar pullback.
It does not assume bounds on any coordinate map. -/
def LocalizedSchwartzHsBound (s : ℝ) : Prop :=
  ∀ (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∀ P : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ,
      (∀ f x, P f x = localizedPullback e a f x) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap ℝ ℂ,
        ‖lineSchwartzHsCLM s (P f)‖ ≤ C*‖lineSchwartzHsCLM s f‖

lemma lineSchwartzHsCLM_successor (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖lineSchwartzHsCLM (s+1) f‖^2 =
      ‖lineSchwartzHsCLM s f‖^2 + ‖lineSchwartzHsCLM s (lineSchwartzDeriv f)‖^2 :=
  line_schwartz_hs_successor s f

lemma lineSchwartzHsCLM_le_successor (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖lineSchwartzHsCLM s f‖ ≤ ‖lineSchwartzHsCLM (s+1) f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), lineSchwartzHsCLM_successor]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma lineSchwartzHsCLM_deriv_le_successor (s : ℝ) (f : SchwartzMap ℝ ℂ) :
    ‖lineSchwartzHsCLM s (lineSchwartzDeriv f)‖ ≤ ‖lineSchwartzHsCLM (s+1) f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), lineSchwartzHsCLM_successor]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma localizedSchwartzHsBound_successor (s : ℝ)
    (hs : LocalizedSchwartzHsBound s) : LocalizedSchwartzHsBound (s+1) := by
  intro e he hi a ha hc hsub P hP
  obtain ⟨C₀, hC₀, h₀⟩ := hs e he hi a ha hc hsub P hP
  have ha₁ : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  have hsub₁ : tsupport (deriv a) ⊆ e.source := tsupport_deriv_subset.trans hsub
  obtain ⟨P₁, hP₁⟩ := localizedSchwartzPullback_exists e he (deriv a) ha₁ hc.deriv hsub₁
  obtain ⟨C₁, hC₁, h₁⟩ := hs e he hi (deriv a) ha₁ hc.deriv hsub₁ P₁ hP₁
  let b := localizedDerivativeCoefficient e a
  have hb : ContDiff ℝ ∞ b := localizedDerivativeCoefficient_contDiff e he a ha hsub
  have hbc : HasCompactSupport b := localizedDerivativeCoefficient_hasCompactSupport e a hc
  have hbs : tsupport b ⊆ e.source := (localizedDerivativeCoefficient_tsupport_subset e a).trans hsub
  obtain ⟨P₂, hP₂⟩ := localizedSchwartzPullback_exists e he b hb hbc hbs
  obtain ⟨C₂, hC₂, h₂⟩ := hs e he hi b hb hbc hbs P₂ hP₂
  refine ⟨C₀+C₁+C₂, by positivity, fun f => ?_⟩
  have hder := lineSchwartzDeriv_localizedPullback e he a ha hsub P P₁ P₂ hP hP₁ hP₂ f
  have hnorm₀ : ‖lineSchwartzHsCLM s (P f)‖ ≤ C₀*‖lineSchwartzHsCLM (s+1) f‖ :=
    (h₀ f).trans (mul_le_mul_of_nonneg_left (lineSchwartzHsCLM_le_successor s f) hC₀)
  have hnorm₁ : ‖lineSchwartzHsCLM s (lineSchwartzDeriv (P f))‖ ≤
      (C₁+C₂)*‖lineSchwartzHsCLM (s+1) f‖ := by
    rw [hder, map_add]
    calc
      _ ≤ ‖lineSchwartzHsCLM s (P₁ f)‖+‖lineSchwartzHsCLM s (P₂ (lineSchwartzDeriv f))‖ := norm_add_le _ _
      _ ≤ C₁*‖lineSchwartzHsCLM s f‖+C₂*‖lineSchwartzHsCLM s (lineSchwartzDeriv f)‖ :=
        add_le_add (h₁ f) (h₂ (lineSchwartzDeriv f))
      _ ≤ _ := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (lineSchwartzHsCLM_le_successor s f) hC₁)
          (mul_le_mul_of_nonneg_left (lineSchwartzHsCLM_deriv_le_successor s f) hC₂)
  have hsucc := lineSchwartzHsCLM_successor s (P f)
  have h0sq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C₀*‖lineSchwartzHsCLM (s+1) f‖)).mpr hnorm₀
  have h1sq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (C₁+C₂)*‖lineSchwartzHsCLM (s+1) f‖)).mpr hnorm₁
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (C₀+C₁+C₂)*‖lineSchwartzHsCLM (s+1) f‖)).mp
  nlinarith [mul_nonneg hC₀ (add_nonneg hC₁ hC₂), sq_nonneg ‖lineSchwartzHsCLM (s+1) f‖]

lemma localizedSchwartzHsBound_nat_add (σ : ℝ) (hσ : LocalizedSchwartzHsBound σ)
    (m : ℕ) : LocalizedSchwartzHsBound (σ+m) := by
  induction m with
  | zero => simpa using hσ
  | succ m ih =>
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
      localizedSchwartzHsBound_successor (σ+m) ih


lemma lineSchwartzHsCLM_zero_norm_lintegral (f : SchwartzMap ℝ ℂ) :
    ENNReal.ofReal (‖lineSchwartzHsCLM 0 f‖^2) = ∫⁻ x, ‖f x‖ₑ^2 := by
  rw [lineSchwartzHsCLM_apply, line_schwartz_hs_norm_sq]
  simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using line_schwartz_plancherel_lintegral f

lemma localizedSchwartzHsBound_zero : LocalizedSchwartzHsBound 0 := by
  intro e he hi a ha hc hs P hP
  obtain ⟨D, hD, hDb⟩ := localizedPullback_jacobian_bound e a ha.continuous hc hs
    (hi.continuousOn_deriv_of_isOpen e.open_target (by simp))
  refine ⟨D, by linarith, fun f => ?_⟩
  have H := localizedPullback_energy_le e (fun y hy =>
    ((hi y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)) a f hDb
  have hPf : (⇑(P f)) = localizedPullback e a f := funext (hP f)
  rw [← hPf, ← lineSchwartzHsCLM_zero_norm_lintegral (P f),
    ← lineSchwartzHsCLM_zero_norm_lintegral f, ← ENNReal.ofReal_mul (sq_nonneg D)] at H
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ D^2*‖lineSchwartzHsCLM 0 f‖^2)).mp H
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ D*‖lineSchwartzHsCLM 0 f‖)).mp
  simpa only [mul_pow] using hr


lemma localizedSchwartzHsBound_fractional (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    LocalizedSchwartzHsBound σ := by
  intro e he hi a ha hc hs P hP
  exact localizedPullback_fractional_schwartz_bound σ hσ0 hσ1 e he hi a ha hc hs P hP

lemma localizedSchwartzHsBound_nonneg (s : ℝ) (hs : 0 ≤ s) : LocalizedSchwartzHsBound s := by
  let m := Nat.floor s
  let σ := s-(m:ℝ)
  have hσ0 : 0 ≤ σ := sub_nonneg.mpr (Nat.floor_le hs)
  have hσ1 : σ < 1 := by dsimp only [σ, m]; linarith [Nat.lt_floor_add_one s]
  have hbase : LocalizedSchwartzHsBound σ := by
    by_cases hz : σ=0
    · simpa only [hz] using localizedSchwartzHsBound_zero
    · exact localizedSchwartzHsBound_fractional σ (lt_of_le_of_ne hσ0 (Ne.symm hz)) hσ1
  have H := localizedSchwartzHsBound_nat_add σ hbase m
  have heq : σ+(m:ℝ)=s := sub_add_cancel _ _
  simpa only [heq] using H

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe uc
variable {M : Type uc} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

namespace SmoothChart

lemma transition_smooth (e f : SmoothChart M) :
    ContDiffOn ℝ ∞ (e.transition f) (e.transition f).source := by
  exact (contMDiffOn_of_mem_contDiffGroupoid
    (compatible_of_mem_maximalAtlas e.property f.property)).contDiffOn

lemma transition_differentiableAt (e f : SmoothChart M) {x : M}
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    DifferentiableAt ℝ (e.transition f) (e.val x) := by
  have hx : e.val x ∈ (e.transition f).source := by
    change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source
    exact ⟨e.val.map_source he, by simpa only [e.val.left_inv he] using hf⟩
  exact ((e.transition_smooth f).differentiableOn (by simp) _ hx).differentiableAt
    ((e.transition f).open_source.mem_nhds hx)

lemma transition_apply (e f : SmoothChart M) {x : M} (he : x ∈ e.val.source) :
    e.transition f (e.val x) = f.val x := by
  simp only [transition, OpenPartialHomeomorph.trans_apply,
    e.val.left_inv he]

lemma transition_deriv_comp (e f g : SmoothChart M) {x : M}
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) (hg : x ∈ g.val.source) :
    deriv (e.transition g) (e.val x) =
      deriv (f.transition g) (f.val x) * deriv (e.transition f) (e.val x) := by
  have hfder : HasDerivAt (f.transition g) (deriv (f.transition g) (f.val x))
      (e.transition f (e.val x)) := by
    rw [e.transition_apply f he]
    exact (f.transition_differentiableAt g hf hg).hasDerivAt
  have hcomp := hfder.comp (e.val x) (e.transition_differentiableAt f he hf).hasDerivAt
  apply HasDerivAt.unique _ hcomp
  apply ((e.transition_differentiableAt g he hg).hasDerivAt).congr_of_eventuallyEq
  filter_upwards [(e.transition f).open_source.mem_nhds
    (show e.val x ∈ (e.transition f).source from
      by
          change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source
          exact ⟨e.val.map_source he, by simpa only [e.val.left_inv he] using hf⟩)] with y hy
  simp only [transition, OpenPartialHomeomorph.trans_apply]
  change y ∈ e.val.target ∧ e.val.symm y ∈ f.val.source at hy
  change g.val (f.val.symm (f.val (e.val.symm y))) = g.val (e.val.symm y)
  rw [f.val.left_inv hy.2]

lemma transition_deriv_ne_zero (e f : SmoothChart M) {x : M}
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    deriv (e.transition f) (e.val x) ≠ 0 := by
  have hfder : HasDerivAt (f.transition e) (deriv (f.transition e) (f.val x))
      (e.transition f (e.val x)) := by
    rw [e.transition_apply f he]
    exact (f.transition_differentiableAt e hf he).hasDerivAt
  have hcomp := hfder.comp (e.val x) (e.transition_differentiableAt f he hf).hasDerivAt
  have hId : (fun z => (f.transition e) ((e.transition f) z)) =ᶠ[𝓝 (e.val x)] id := by
    filter_upwards [(e.transition f).open_source.mem_nhds
      (show e.val x ∈ (e.transition f).source from
        by
          change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source
          exact ⟨e.val.map_source he, by simpa only [e.val.left_inv he] using hf⟩)] with y hy
    simp only [transition, OpenPartialHomeomorph.trans_apply]
    change y ∈ e.val.target ∧ e.val.symm y ∈ f.val.source at hy
    rw [f.val.left_inv hy.2, e.val.right_inv hy.1]
    rfl
  exact right_ne_zero_of_mul_eq_one
    ((hcomp.congr_of_eventuallyEq hId.symm).unique (hasDerivAt_id _))

lemma densityJacobian_pos (e : SmoothChart M) {x : M} (hx : x ∈ e.val.source) :
    0 < e.densityJacobian x :=
  abs_pos.mpr (transition_deriv_ne_zero _ e (mem_chart_source ℝ x) hx)

lemma densityJacobian_transition (e f : SmoothChart M) {x : M}
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    f.densityJacobian x = |deriv (e.transition f) (e.val x)| * e.densityJacobian x := by
  rw [densityJacobian, densityJacobian,
    transition_deriv_comp _ e f (mem_chart_source ℝ x) he hf, abs_mul]

end SmoothChart

/-- The density presentation is faithful on each chart. -/
theorem chartDensityFunction_injective {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M) :
    Function.Injective (chartDensityFunction (𝕜 := 𝕜) e) := by
  classical
  intro φ ψ h
  apply TestFunction.ext
  intro y
  by_cases hy : y ∈ e.val.target
  · have hx : e.val.symm y ∈ e.val.source := e.val.symm.map_source hy
    have heq := congrFun h (e.val.symm y)
    change (if e.val.symm y ∈ e.val.source then
        e.densityJacobian (e.val.symm y) • φ (e.val (e.val.symm y)) else 0) =
      (if e.val.symm y ∈ e.val.source then
        e.densityJacobian (e.val.symm y) • ψ (e.val (e.val.symm y)) else 0) at heq
    rw [ite_eq_left hx, ite_eq_left hx, e.val.right_inv hy] at heq
    exact smul_right_injective 𝕜 (ne_of_gt (e.densityJacobian_pos hx)) heq
  · exact (φ.zero_on_compl hy).trans (ψ.zero_on_compl hy).symm

/-- Equality of chart density sections uses the inverse absolute Jacobian,
including orientation-reversing transitions. The support hypothesis merely
means the first test is supported in the overlap. -/
theorem chartDensityFunction_transition {𝕜 : Type*} [RCLike 𝕜] (e f : SmoothChart M)
    (φ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (ψ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤)
    (hs : tsupport φ ⊆ (e.transition f).source)
    (hψ : ∀ y, ψ y = (e.transition f).target.indicator (inverseDensity (e.transition f) φ) y) :
    chartDensityFunction e φ = chartDensityFunction f ψ := by
  funext x
  by_cases he : x ∈ e.val.source
  · by_cases hf : x ∈ f.val.source
    · have htarget : f.val x ∈ (e.transition f).target := by
        change f.val x ∈ f.val.target ∧ f.val.symm (f.val x) ∈ e.val.source
        exact ⟨f.val.map_source hf, by simpa only [f.val.left_inv hf] using he⟩
      have hsym : (e.transition f).symm (f.val x) = e.val x := by
        change e.val (f.val.symm (f.val x)) = e.val x
        rw [f.val.left_inv hf]
      have hder : deriv (e.transition f).symm (f.val x) =
          deriv (f.transition e) (f.val x) := rfl
      rw [chartDensityFunction, chartDensityFunction, indicator_of_mem he,
        indicator_of_mem hf, hψ, indicator_of_mem htarget, inverseDensity, hsym, hder,
        smul_smul, mul_comm (f.densityJacobian x) _, ← f.densityJacobian_transition e hf he]
    · have hz : φ (e.val x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hx
        have hx' := hs hx
        change e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ f.val.source at hx'
        exact hf (by simpa only [e.val.left_inv he] using hx'.2)
      simp [chartDensityFunction, he, hf, hz]
  · by_cases hf : x ∈ f.val.source
    · have hz : ψ (f.val x) = 0 := by
        have ht : f.val x ∉ (e.transition f).target := by
          intro hx
          change f.val x ∈ f.val.target ∧ f.val.symm (f.val x) ∈ e.val.source at hx
          exact he (by simpa only [f.val.left_inv hf] using hx.2)
        simp [hψ, ht]
      simp [chartDensityFunction, he, hf, hz]
    · simp [chartDensityFunction, he, hf]

namespace ScalarCurveDistribution
variable {𝕜 : Type*} [RCLike 𝕜]

@[ext] theorem ext {T S : ScalarCurveDistribution 𝕜 M}
    (h : ∀ e, T.inChart e = S.inChart e) : T = S := by
  have hlin : T.toLinearMap = S.toLinearMap := by
    apply LinearMap.ext
    rintro ⟨ρ, hρ⟩
    change ρ ∈ Submodule.span 𝕜 _ at hρ
    induction hρ using Submodule.span_induction with
    | mem ρ hρ =>
      obtain ⟨e, φ, rfl⟩ := mem_iUnion.mp hρ
      exact congrArg (fun L => L φ) (h e)
    | zero => exact (map_zero T.toLinearMap).trans (map_zero S.toLinearMap).symm
    | add ρ σ hρ hσ ihρ ihσ =>
      change T.toLinearMap (⟨ρ, hρ⟩ + ⟨σ, hσ⟩) = S.toLinearMap (⟨ρ, hρ⟩ + ⟨σ, hσ⟩)
      rw [map_add, map_add, ihρ, ihσ]
    | smul c ρ hρ ihρ =>
      change T.toLinearMap (c • ⟨ρ, hρ⟩) = S.toLinearMap (c • ⟨ρ, hρ⟩)
      rw [map_smul, map_smul, ihρ]
  exact Subtype.ext hlin

end ScalarCurveDistribution

/-- A Schwartz operator whose outputs have one fixed compact support factors
continuously through that compact test-function step. -/
def schwartzToTestStep {𝕜 : Type*} [RCLike 𝕜]
    (K : Compacts ℝ) (Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜)
    (hs : ∀ φ, tsupport (Q φ) ⊆ K) :
    SchwartzMap ℝ 𝕜 →L[𝕜] ContDiffMapSupportedIn ℝ 𝕜 ⊤ K := by
  let L : SchwartzMap ℝ 𝕜 →ₗ[𝕜] ContDiffMapSupportedIn ℝ 𝕜 ⊤ K :=
    { toFun := fun φ => .of_support_subset ((Q φ).smooth ⊤)
        ((subset_tsupport _).trans (hs φ))
      map_add' := fun φ ψ => by ext x; exact congrArg (fun f : SchwartzMap ℝ 𝕜 => f x) (map_add Q φ ψ)
      map_smul' := fun c φ => by ext x; exact congrArg (fun f : SchwartzMap ℝ 𝕜 => f x) (map_smul Q c φ) }
  refine ⟨L, (ContDiffMapSupportedIn.continuous_iff_comp L).mpr (fun i => ?_)⟩
  let Li := (ContDiffMapSupportedIn.structureMapLM 𝕜 ⊤ i).comp L
  change Continuous Li
  refine (WithSeminorms.continuous_iff_continuous_comp
    (norm_withSeminorms 𝕜 (BoundedContinuousFunction ℝ (ℝ [×i]→L[ℝ] 𝕜))) Li).mpr ?_
  intro _
  have hq : Continuous ((SchwartzMap.seminorm 𝕜 0 i).comp Q.toLinearMap) := by
    change Continuous ((SchwartzMap.seminorm 𝕜 0 i) ∘ Q)
    apply Continuous.comp _ Q.continuous
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
      ((schwartz_withSeminorms 𝕜 ℝ 𝕜).continuous_seminorm (0, i))
  apply Seminorm.continuous_of_le hq
  intro φ
  change ‖Li φ‖ ≤ SchwartzMap.seminorm 𝕜 0 i (Q φ)
  apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
  intro x
  change ‖ContDiffMapSupportedIn.structureMapLM 𝕜 ⊤ i (L φ) x‖ ≤ _
  rw [ContDiffMapSupportedIn.structureMapLM_top_apply]
  exact (Q φ).norm_iteratedFDeriv_le_seminorm 𝕜 i x

/-- Multiplication of a Schwartz test by a compact smooth chart coefficient,
with the genuine local LF codomain. -/
def schwartzCutoffToTest {𝕜 : Type*} [RCLike 𝕜] (U : TopologicalSpace.Opens ℝ)
    (a : TestFunction U 𝕜 ⊤) :
    SchwartzMap ℝ 𝕜 →L[𝕜] TestFunction U 𝕜 ⊤ := by
  let Q := SchwartzMap.smulLeftCLM 𝕜 (a : ℝ → 𝕜)
  have ha : (a : ℝ → 𝕜).HasTemperateGrowth :=
    a.hasCompactSupport.hasTemperateGrowth a.contDiff
  have hs : ∀ φ, tsupport (Q φ) ⊆ tsupport a := by
    intro φ
    have hq : (Q φ : ℝ → 𝕜) = fun x => a x * φ x := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply ha]
      rfl
    rw [hq]
    exact (tsupport_mul_subset_left ..)
  exact (TestFunction.ofSupportedInCLM 𝕜 a.tsupport_subset).comp
    (schwartzToTestStep ⟨tsupport a, a.hasCompactSupport⟩ Q hs)

@[simp] lemma schwartzCutoffToTest_apply {𝕜 : Type*} [RCLike 𝕜]
    (U : TopologicalSpace.Opens ℝ) (a : TestFunction U 𝕜 ⊤)
    (φ : SchwartzMap ℝ 𝕜) (x : ℝ) :
    schwartzCutoffToTest U a φ x = a x * φ x := by
  unfold schwartzCutoffToTest schwartzToTestStep
  change SchwartzMap.smulLeftCLM 𝕜 (a : ℝ → 𝕜) φ x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (a.hasCompactSupport.hasTemperateGrowth a.contDiff)]
  rfl

namespace ScalarCurveDistribution
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Compactly supported chart localization as an actual whole-line tempered
scalar distribution. The coefficient multiplies the scalar distribution. -/
def localize (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤) :
    SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜 :=
  (T.inChart e).comp (schwartzCutoffToTest _ a)

@[simp] lemma localize_apply (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (φ : SchwartzMap ℝ 𝕜) :
    T.localize e a φ = T.inChart e (schwartzCutoffToTest _ a φ) := rfl

/-- For regular coordinate representatives, compact localization is the scalar
product a f, as opposed to multiplication by an extra density Jacobian. -/
theorem localize_regular (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤) (f : ℝ → 𝕜)
    (hT : ∀ φ, T.inChart e φ = ∫ x, f x * φ x) (φ : SchwartzMap ℝ 𝕜) :
    T.localize e a φ = ∫ x, (a x * f x) * φ x := by
  rw [localize_apply, hT]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [schwartzCutoffToTest_apply]; ring)

/-- The same intrinsic scalar distribution, tested in two coordinates, has
exactly the inverse absolute Jacobian in the test-density transformation. -/
theorem inChart_transition (T : ScalarCurveDistribution 𝕜 M) (e f : SmoothChart M)
    (φ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (ψ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤)
    (hs : tsupport φ ⊆ (e.transition f).source)
    (hψ : ∀ y, ψ y = (e.transition f).target.indicator (inverseDensity (e.transition f) φ) y) :
    T.inChart e φ = T.inChart f ψ := by
  change T.toLinearMap (chartTestDensity 𝕜 e φ) = T.toLinearMap (chartTestDensity 𝕜 f ψ)
  apply congrArg T.toLinearMap
  apply Subtype.ext
  exact chartDensityFunction_transition e f φ ψ hs hψ

/-- All compact chart localizations jointly determine the scalar distribution. -/
theorem ext_localize {T S : ScalarCurveDistribution 𝕜 M}
    (h : ∀ e a, T.localize e a = S.localize e a) : T = S := by
  apply ext
  intro e
  apply ContinuousLinearMap.ext
  intro φ
  obtain ⟨χ, hχ, hχc, hχs, hχ1⟩ := compact_smoothCutoff φ.hasCompactSupport
    e.val.open_target φ.tsupport_subset
  let a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ :=
    ⟨fun x => (χ x : 𝕜), by
        simpa only [Function.comp_def, RCLike.ofRealCLM_apply] using
          ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hχ),
      hχc.comp_left (by simp), (tsupport_comp_subset (by simp) χ).trans hχs⟩
  let Φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have haΦ : schwartzCutoffToTest _ a Φ = φ := by
    apply TestFunction.ext
    intro x
    rw [schwartzCutoffToTest_apply]
    change (χ x : 𝕜) * φ x = φ x
    by_cases hx : x ∈ tsupport φ
    · rw [hχ1 x hx]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hEq := congrArg (fun L : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜 => L Φ) (h e a)
  simpa only [localize_apply, haΦ] using hEq

end ScalarCurveDistribution

/-- The compact scalar cutoff in an actual finite chart partition. -/
def chartCutoffTest [T2Space M] [CompactSpace M] {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) :
    TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤ := by
  let f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ := ⟨fun _ => 1, contMDiff_const⟩
  have h := chartLocalFunction_smooth_compact A f i
  exact ⟨chartLocalFunction A f i, h.1, h.2.1, h.2.2⟩

@[simp] lemma chartCutoffTest_apply [T2Space M] [CompactSpace M] {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) (y : ℝ) :
    chartCutoffTest (𝕜 := 𝕜) A i y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y := rfl

/-- The finite-chart localizations appearing in the compact-curve Sobolev norm.
Every component is a genuine whole-line tempered scalar distribution. -/
def partitionDistribution [T2Space M] [CompactSpace M] {𝕜 : Type*} [RCLike 𝕜]
    (T : ScalarCurveDistribution 𝕜 M) (A : FiniteChartPartition M) (i : Fin A.n) :
    SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜 :=
  T.localize ⟨A.chart i, A.chart_smooth i⟩ (chartCutoffTest A i)

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

lemma lineSchwartzToEuclidean_surjective :
    Function.Surjective lineSchwartzToEuclidean := by
  intro f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    realLineIsometry.toContinuousLinearEquiv f, ?_⟩
  ext x
  exact congrArg f (realLineIsometry.apply_symm_apply x)

lemma tempered_ext_line {T S : Tempered ℂ 1}
    (h : ∀ φ : SchwartzMap ℝ ℂ, T (lineSchwartzToEuclidean φ) =
      S (lineSchwartzToEuclidean φ)) : T = S := by
  ext ψ
  obtain ⟨φ, rfl⟩ := lineSchwartzToEuclidean_surjective ψ
  exact h φ

/-- The density transpose is itself a compactly localized scalar pullback
by the inverse coordinate map. -/
lemma localizedDensity_as_pullback (e : OpenPartialHomeomorph ℝ ℝ)
    (a φ : ℝ → ℂ) :
    localizedDensity e a φ =
      localizedPullback e.symm (localizedDensity e a (fun _ => 1)) φ := by
  ext y
  by_cases hy : y ∈ e.target
  · simp [localizedDensity, localizedPullback, inverseDensity, hy,
      mul_assoc]
  · simp [localizedDensity, localizedPullback, hy]

lemma line_negative_schwartz_extension (s : ℝ)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (A : Hs 1 (-s) →L[ℂ] Hs 1 (-s))
    (hA : ∀ φ, A (schwartzHs (-s) (lineSchwartzToEuclidean φ)) =
      schwartzHs (-s) (lineSchwartzToEuclidean (Q φ))) :
    ∃ B : Hs 1 s →L[ℂ] Hs 1 s, ‖B‖ ≤ ‖A‖ ∧
      ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (B u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ)) := by
  obtain ⟨B, hB, _⟩ := negative_transpose 1 1 (-s) (-s) A
  refine ⟨B, hB.2, fun u φ => ?_⟩
  have hv := schwartzHs_realization (-s) (lineSchwartzToEuclidean φ)
  have hAv : realization
      (A (schwartzHs (-s) (lineSchwartzToEuclidean φ))) =
      schwartzRegularDistribution (lineSchwartzToEuclidean (Q φ)) := by
    rw [hA, schwartzHs_realization]
  have hh := transpose_realization 1 1 (-s) (-s) A B hB.1
    (lineSchwartzToEuclidean φ) (lineSchwartzToEuclidean (Q φ))
    (schwartzHs (-s) (lineSchwartzToEuclidean φ)) u hv hAv
  exact (congrArg (fun r : ℝ => @realization 1 r (B u) (lineSchwartzToEuclidean φ))
      (neg_neg s).symm).trans (hh.trans
    (congrArg (fun r : ℝ => @realization 1 r u (lineSchwartzToEuclidean (Q φ)))
      (neg_neg s)))

lemma line_schwartz_action_of_density (s : ℝ)
    (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (hAQ : ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
      realization (A u) (lineSchwartzToEuclidean φ) =
        realization u (lineSchwartzToEuclidean (Q φ)))
    (hPQ : ∀ f φ, (∫ x : ℝ, P f x * φ x) = ∫ x : ℝ, f x * Q φ x)
    (f : SchwartzMap ℝ ℂ) :
    A (schwartzHs s (lineSchwartzToEuclidean f)) =
      schwartzHs s (lineSchwartzToEuclidean (P f)) := by
  apply realization_injective 1 s
  apply tempered_ext_line
  intro φ
  rw [hAQ, schwartzHs_realization, schwartzHs_realization,
    line_schwartz_regular_pairing, line_schwartz_regular_pairing]
  exact (hPQ f φ).symm

lemma localizedPullback_negative_Hs_bound_of_schwartz_bound
    (s : ℝ) (hb : LocalizedSchwartzHsBound (-s))
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 s →L[ℂ] Hs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
        schwartzHs s (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (A u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ))) := by
  obtain ⟨P, hP⟩ := localizedSchwartzPullback_exists e he a ha hc hs
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  let b := localizedDensity e a (fun _ => 1)
  have hbs : tsupport b ⊆ e.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := localizedDensity_tsupport_subset e a (fun _ => 1) hc hs hy
    exact e.map_source (hs hx)
  have hbc := localizedDensity_hasCompactSupport e a (fun _ => 1) hc hs
  have hbd := localizedDensity_contDiff e he hi a (fun _ => 1) ha contDiff_const hc hs
  have hQb : ∀ f x, Q f x = localizedPullback e.symm b f x := by
    intro f x
    rw [hQ, localizedDensity_as_pullback]
  obtain ⟨C, hC, hQbound⟩ := hb e.symm hi he b hbd hbc hbs Q hQb
  obtain ⟨D, hD, _⟩ := line_schwartz_operator_extension (-s) Q C hC hQbound
  obtain ⟨A, hA, hAQ⟩ := line_negative_schwartz_extension s Q D hD.2
  have hPQ : ∀ f φ : SchwartzMap ℝ ℂ,
      (∫ x : ℝ, P f x * φ x) = ∫ x : ℝ, f x * Q φ x := by
    intro f φ
    have hd : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y := by
      intro y hy
      exact (hi.differentiableOn (by simp) y hy).differentiableAt (e.open_target.mem_nhds hy)
    calc
      _ = ∫ x, localizedPullback e a f x * φ x := by simp_rw [hP]
      _ = ∫ x, f x * localizedDensity e a φ x := localizedPullback_pairing e hd a f φ
      _ = _ := by simp_rw [hQ]
  exact ⟨P, Q, A, C, hC, hA.trans hD.1, hP, hQ,
    line_schwartz_action_of_density s P Q A hAQ hPQ, hAQ⟩

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale
lemma localizedPullback_nonneg_Hs_bound
    (s : ℝ) (hs0 : 0 ≤ s)
    (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 s →L[ℂ] Hs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
        schwartzHs s (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (A u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ))) := by
  obtain ⟨P, hP⟩ := localizedSchwartzPullback_exists e he a ha hc hs
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  obtain ⟨C, hC, hb⟩ := localizedSchwartzHsBound_nonneg s hs0
    e he hi a ha hc hs P hP
  obtain ⟨A, hA, _⟩ := line_schwartz_operator_extension s P C hC hb
  refine ⟨P, Q, A, C, hC, hA.1, hP, hQ, hA.2, ?_⟩
  apply line_schwartz_extension_realization s P Q A hA.2
  intro f φ
  have hd : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y := by
    intro y hy
    exact (hi.differentiableOn (by simp) y hy).differentiableAt (e.open_target.mem_nhds hy)
  calc
    _ = ∫ x, localizedPullback e a f x * φ x := by simp_rw [hP]
    _ = ∫ x, f x * localizedDensity e a φ x := localizedPullback_pairing e hd a f φ
    _ = _ := by simp_rw [hQ]

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

/-- All real orders of the genuine compactly localized scalar coordinate map,
including its action on actual distributions through the inverse density. -/
lemma localizedPullback_all_real_Hs_bound
    (s : ℝ) (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 s →L[ℂ] Hs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ (f : SchwartzMap ℝ ℂ) (u : Hs 1 s),
        realization u = schwartzRegularDistribution (lineSchwartzToEuclidean f) →
        realization (A u) = schwartzRegularDistribution (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (A u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ))) := by
  have H : ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 s →L[ℂ] Hs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ f, A (schwartzHs s (lineSchwartzToEuclidean f)) =
        schwartzHs s (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (A u) (lineSchwartzToEuclidean φ) =
          realization u (lineSchwartzToEuclidean (Q φ))) := by
    by_cases hs0 : 0 ≤ s
    · exact localizedPullback_nonneg_Hs_bound s hs0 e he hi a ha hc hs
    · exact localizedPullback_negative_Hs_bound_of_schwartz_bound s
        (localizedSchwartzHsBound_nonneg (-s) (by linarith)) e he hi a ha hc hs
  obtain ⟨P, Q, A, C, hC, hAC, hP, hQ, hA, hAQ⟩ := H
  refine ⟨P, Q, A, C, hC, hAC, hP, hQ, ?_, hAQ⟩
  intro f u hu
  rw [schwartzHs_unique s _ u hu, hA, schwartzHs_realization]

end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem coordinate_hs :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.coordinateHsType :=
  localizedPullback_all_real_Hs_bound

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe ud
variable {M : Type ud} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

/-- A compact test density supported in a chart overlap has its actual smooth
compact coefficient in the other chart. No transition-test existence is assumed. -/
theorem chartDensityTransfer_exists {𝕜 : Type*} [RCLike 𝕜] (e f : SmoothChart M)
    (φ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (hs : tsupport φ ⊆ (e.transition f).source) :
    ∃ ψ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤,
      ∀ y, ψ y = (e.transition f).target.indicator (inverseDensity (e.transition f) φ) y := by
  let t := e.transition f
  have he : ContDiffOn ℝ ∞ t t.source := e.transition_smooth f
  have hi : ContDiffOn ℝ ∞ t.symm t.target := f.transition_smooth e
  have hd := localizedDensity_contDiff t he hi φ (fun _ => (1 : 𝕜)) φ.contDiff
    contDiff_const φ.hasCompactSupport hs
  have hc := localizedDensity_hasCompactSupport t φ (fun _ => (1 : 𝕜)) φ.hasCompactSupport hs
  have hsub : tsupport (localizedDensity t φ (fun _ => (1 : 𝕜))) ⊆ f.val.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := localizedDensity_tsupport_subset t φ (fun _ => (1 : 𝕜))
      φ.hasCompactSupport hs hy
    have htarget := t.map_source (hs hx)
    change t x ∈ f.val.target ∧ _ at htarget
    exact htarget.1
  refine ⟨⟨localizedDensity t φ (fun _ => (1 : 𝕜)), hd, hc, hsub⟩, ?_⟩
  intro y
  change t.target.indicator (inverseDensity t ((φ : ℝ → 𝕜) * 1)) y =
    t.target.indicator (inverseDensity t φ) y
  rw [mul_one]

namespace ScalarCurveDistribution
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Existence and uniqueness of the actual compact chart localization, with
its full test-function action given independently of the chosen constructor. -/
theorem localize_exists_unique (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤) :
    ∃! S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
      ∀ (φ : SchwartzMap ℝ 𝕜) (ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
        (∀ x, ψ x = a x * φ x) → S φ = T.inChart e ψ := by
  refine ⟨T.localize e a, ?_, ?_⟩
  · intro φ ψ hψ
    rw [localize_apply]
    congr 1
    exact TestFunction.ext (fun x => (schwartzCutoffToTest_apply _ a φ x).trans (hψ x).symm)
  · intro S hS
    apply ContinuousLinearMap.ext
    intro φ
    exact hS φ (schwartzCutoffToTest _ a φ) (schwartzCutoffToTest_apply _ a φ)

end ScalarCurveDistribution
end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem curve_distribution_chart :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveDistributionChartType := by
  intro M _ _ _ 𝕜 _ T e f φ hs
  obtain ⟨ψ, hψ⟩ := chartDensityTransfer_exists e f φ hs
  exact ⟨ψ, hψ, T.inChart_transition e f φ ψ hs hψ⟩

theorem curve_distribution_localization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveDistributionLocalizationType := by
  intro M _ _ _ 𝕜 _ T e a
  exact T.localize_exists_unique e a

theorem curve_distribution_regular :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveDistributionRegularType := by
  intro M _ _ _ 𝕜 _ T e a S hS f hf φ
  rw [hS φ (schwartzCutoffToTest _ a φ) (schwartzCutoffToTest_apply _ a φ), hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [schwartzCutoffToTest_apply]; ring)

theorem curve_distribution_faithfulness :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveDistributionFaithfulnessType := by
  intro M _ _ _ 𝕜 _ T S h
  apply ScalarCurveDistribution.ext_localize
  intro e a
  apply ContinuousLinearMap.ext
  intro φ
  exact h e a φ (schwartzCutoffToTest _ a φ) (schwartzCutoffToTest_apply _ a φ)

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

def lineComplexifySchwartz : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

lemma lineSchwartzToEuclidean_complexify (φ : SchwartzMap ℝ ℝ) :
    lineSchwartzToEuclidean (lineComplexifySchwartz φ) =
      complexifySchwartz (lineRealSchwartzToEuclidean φ) := by
  ext x
  rfl

lemma lineRealSchwartzToEuclidean_surjective : Function.Surjective lineRealSchwartzToEuclidean := by
  intro φ
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ realLineIsometry.toContinuousLinearEquiv φ, ?_⟩
  ext x
  exact congrArg φ (realLineIsometry.apply_symm_apply x)

lemma localizedDensity_complexify (e : OpenPartialHomeomorph ℝ ℝ)
    (a φ : ℝ → ℝ) (y : ℝ) :
    localizedDensity e (fun x => (a x : ℂ)) (fun x => (φ x : ℂ)) y =
      (localizedDensity (𝕜 := ℝ) e a φ y : ℂ) := by
  by_cases hy : y ∈ e.target
  · simp [localizedDensity, inverseDensity, hy, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  · simp [localizedDensity, hy]

lemma localizedDensitySchwartz_complexify (e : OpenPartialHomeomorph ℝ ℝ)
    (a : ℝ → ℝ)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (QR : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (hQ : ∀ φ y, Q φ y = localizedDensity e (fun x => (a x : ℂ)) φ y)
    (hQR : ∀ φ y, QR φ y = localizedDensity e a φ y) :
    ∀ φ : SchwartzMap ℝ ℝ, Q (lineComplexifySchwartz φ) = lineComplexifySchwartz (QR φ) := by
  intro φ
  ext y
  rw [hQ]
  change localizedDensity e (fun x => (a x : ℂ)) (fun x => (φ x : ℂ)) y = (QR φ y : ℂ)
  rw [hQR, localizedDensity_complexify]

lemma hs_map_mem_real_of_line_density (s : ℝ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (QR : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (hAQ : ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
      realization (s := s) (A u) (lineSchwartzToEuclidean φ) =
        realization (s := s) u (lineSchwartzToEuclidean (Q φ)))
    (hQ : ∀ φ, Q (lineComplexifySchwartz φ) = lineComplexifySchwartz (QR φ))
    (u : RealHs 1 s) : A (realCoordinates 1 s u) ∈ hermitianL2 1 := by
  apply (realization_real_iff (s := s) _).mpr
  intro Φ
  obtain ⟨φ, rfl⟩ := lineRealSchwartzToEuclidean_surjective Φ
  rw [← lineSchwartzToEuclidean_complexify, hAQ, hQ, lineSchwartzToEuclidean_complexify]
  exact (realization_real_iff (s := s) (realCoordinates 1 s u)).mp u.property _

def realHsMapOfDensity (s : ℝ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (QR : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (hAQ : ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
      realization (s := s) (A u) (lineSchwartzToEuclidean φ) =
        realization (s := s) u (lineSchwartzToEuclidean (Q φ)))
    (hQ : ∀ φ, Q (lineComplexifySchwartz φ) = lineComplexifySchwartz (QR φ)) :
    RealHs 1 s →L[ℝ] RealHs 1 s :=
  ((A.restrictScalars ℝ).comp (realCoordinates 1 s).toContinuousLinearMap).codRestrict
    (hermitianL2 1) (hs_map_mem_real_of_line_density s A Q QR hAQ hQ)

lemma realHsMapOfDensity_norm_le (s : ℝ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (QR : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (hAQ : ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
      realization (s := s) (A u) (lineSchwartzToEuclidean φ) =
        realization (s := s) u (lineSchwartzToEuclidean (Q φ)))
    (hQ : ∀ φ, Q (lineComplexifySchwartz φ) = lineComplexifySchwartz (QR φ)) :
    ‖realHsMapOfDensity s A Q QR hAQ hQ‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖A (realCoordinates 1 s u)‖ ≤ ‖A‖*‖u‖
  simpa only [(realCoordinates 1 s).norm_map] using A.le_opNorm (realCoordinates 1 s u)

lemma realHsMapOfDensity_realization (s : ℝ)
    (A : Hs 1 s →L[ℂ] Hs 1 s)
    (Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (QR : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (hAQ : ∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
      realization (s := s) (A u) (lineSchwartzToEuclidean φ) =
        realization (s := s) u (lineSchwartzToEuclidean (Q φ)))
    (hQ : ∀ φ, Q (lineComplexifySchwartz φ) = lineComplexifySchwartz (QR φ))
    (u : RealHs 1 s) (φ : SchwartzMap ℝ ℝ) :
    realRealization (s := s) (realHsMapOfDensity s A Q QR hAQ hQ u) (lineRealSchwartzToEuclidean φ) =
      realRealization (s := s) u (lineRealSchwartzToEuclidean (QR φ)) := by
  change (realization (s := s) (A (realCoordinates 1 s u))
    (complexifySchwartz (lineRealSchwartzToEuclidean φ))).re = _
  rw [← lineSchwartzToEuclidean_complexify, hAQ, hQ, lineSchwartzToEuclidean_complexify]
  rfl


lemma localizedPullback_complexify (e : OpenPartialHomeomorph ℝ ℝ)
    (a f : ℝ → ℝ) (x : ℝ) :
    localizedPullback e (fun y => (a y : ℂ)) (fun y => (f y : ℂ)) x =
      (localizedPullback (𝕜 := ℝ) e a f x : ℂ) := by
  by_cases hx : x ∈ e.source <;> simp [localizedPullback, hx]

lemma localizedPullback_real_Hs_bound
    (s : ℝ) (e : OpenPartialHomeomorph ℝ ℝ)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ e.source) :
    ∃ (P Q : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
      (A : RealHs 1 s →L[ℝ] RealHs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ (f : SchwartzMap ℝ ℝ) (u : RealHs 1 s),
        realRealization (s := s) u = realSchwartzRegularDistribution (lineRealSchwartzToEuclidean f) →
        realRealization (s := s) (A u) =
          realSchwartzRegularDistribution (lineRealSchwartzToEuclidean (P f))) ∧
      (∀ (u : RealHs 1 s) (φ : SchwartzMap ℝ ℝ),
        realRealization (s := s) (A u) (lineRealSchwartzToEuclidean φ) =
          realRealization (s := s) u (lineRealSchwartzToEuclidean (Q φ))) := by
  let ac : ℝ → ℂ := fun x => (a x : ℂ)
  have hac : ContDiff ℝ ∞ ac := Complex.ofRealCLM.contDiff.comp ha
  have hacc : HasCompactSupport ac := by
    change HasCompactSupport (Complex.ofReal ∘ a)
    exact hc.comp_left rfl
  have hacs : tsupport ac ⊆ e.source := by
    change tsupport (Complex.ofReal ∘ a) ⊆ e.source
    exact (tsupport_comp_subset rfl a).trans hs
  obtain ⟨PC, QC, AC, C, hC, hAC, hPC, hQC, hreg, hAQ⟩ :=
    localizedPullback_all_real_Hs_bound s e he hi ac hac hacc hacs
  obtain ⟨P, hP⟩ := localizedSchwartzPullback_exists e he a ha hc hs
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists e he hi a ha hc hs
  have hQc : ∀ φ, QC (lineComplexifySchwartz φ) = lineComplexifySchwartz (Q φ) :=
    localizedDensitySchwartz_complexify e a QC Q hQC hQ
  let A := realHsMapOfDensity s AC QC Q hAQ hQc
  refine ⟨P, Q, A, C, hC, (realHsMapOfDensity_norm_le s AC QC Q hAQ hQc).trans hAC,
    hP, hQ, ?_, realHsMapOfDensity_realization s AC QC Q hAQ hQc⟩
  intro f u hu
  have hPc : PC (lineComplexifySchwartz f) = lineComplexifySchwartz (P f) := by
    ext x
    rw [hPC]
    change localizedPullback e ac (fun x => (f x : ℂ)) x = (P f x : ℂ)
    rw [hP]
    exact localizedPullback_complexify e a f x
  have huC : realization (s := s) (realCoordinates 1 s u) =
      schwartzRegularDistribution (lineSchwartzToEuclidean (lineComplexifySchwartz f)) := by
    rw [lineSchwartzToEuclidean_complexify, ← complexify_realSchwartzRegularDistribution,
      ← hu, complexify_realRealization]
  apply complexifyTempered_injective 1
  rw [complexify_realRealization, complexify_realSchwartzRegularDistribution]
  change realization (s := s) (AC (realCoordinates 1 s u)) = _
  rw [← lineSchwartzToEuclidean_complexify, ← hPc]
  exact hreg (lineComplexifySchwartz f) (realCoordinates 1 s u) huC

end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem real_coordinate_hs :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realCoordinateHsType :=
  localizedPullback_real_Hs_bound

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe ue
variable {M : Type ue} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

/-- Multiplying a chart density by a smooth scalar supported in another chart
produces an actual compact test density coefficient in that other chart. -/
theorem densityCoefficient_exists {𝕜 : Type*} [RCLike 𝕜] (e f : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (φ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤) :
    ∃ ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤,
      chartDensityFunction e ψ = fun x => ρ x • chartDensityFunction f φ x := by
  let b : ℝ → 𝕜 := f.val.target.indicator (fun y => ρ (f.val.symm y) • φ y)
  have hbsub : tsupport b ⊆ tsupport φ := by
    apply closure_mono
    intro y hy
    by_contra hφ
    have hz : φ y = 0 := by simpa only [Function.mem_support, not_not] using hφ
    exact hy (by simp [b, hz])
  have hρf : ContDiffOn ℝ ∞ (fun y => ρ (f.val.symm y)) f.val.target :=
    (ρ.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas f.property)).contDiffOn
  have hbd : ContDiff ℝ ∞ b :=
    contDiff_indicator_of_support f.val.target f.val.open_target _
      (hρf.smul φ.contDiff.contDiffOn) (hbsub.trans φ.tsupport_subset)
  have hbc : HasCompactSupport b :=
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport b) hbsub
  let β : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤ :=
    ⟨b, hbd, hbc, hbsub.trans φ.tsupport_subset⟩
  have hbsource : tsupport β ⊆ (f.transition e).source := by
    intro y hy
    have hyt : y ∈ f.val.target := φ.tsupport_subset (hbsub hy)
    have hxρ : f.val.symm y ∈ tsupport ρ := by
      by_contra hxρ
      have hz := notMem_tsupport_iff_eventuallyEq.mp hxρ
      have hfi : ContinuousAt f.val.symm y :=
        f.val.symm.continuousOn.continuousAt (f.val.open_target.mem_nhds hyt)
      have hbzero : b =ᶠ[𝓝 y] 0 := by
        filter_upwards [hz.comp_tendsto hfi.tendsto] with z hz
        dsimp only [Function.comp_def, Pi.zero_apply] at hz
        simp [b, hz]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hbzero) hy
    change y ∈ f.val.target ∧ f.val.symm y ∈ e.val.source
    exact ⟨hyt, hρ hxρ⟩
  obtain ⟨ψ, hψ⟩ := chartDensityTransfer_exists f e β hbsource
  refine ⟨ψ, (chartDensityFunction_transition f e β ψ hbsource hψ).symm.trans ?_⟩
  funext x
  by_cases hx : x ∈ f.val.source
  · have hy : f.val x ∈ f.val.target := f.val.map_source hx
    simp only [chartDensityFunction, indicator_of_mem hx]
    change f.densityJacobian x • b (f.val x) = ρ x • f.densityJacobian x • φ (f.val x)
    rw [show b (f.val x) = ρ x • φ (f.val x) by simp [b, hy, f.val.left_inv hx]]
    exact smul_comm _ _ _
  · simp [chartDensityFunction, hx]

/-- Every intrinsic compact test density multiplied by a chart-supported
smooth scalar has a unique actual compact coefficient in that chart. -/
theorem densityCoefficient_exists_unique {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (density : ↥(TestDensities 𝕜 M)) :
    ∃! ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤,
      chartDensityFunction e ψ = fun x => ρ x • density.val x := by
  have hex : ∃ ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤,
      chartDensityFunction e ψ = fun x => ρ x • density.val x := by
    rcases density with ⟨density, hdensity⟩
    change density ∈ Submodule.span 𝕜 _ at hdensity
    induction hdensity using Submodule.span_induction with
    | mem density hdensity =>
      obtain ⟨f, φ, rfl⟩ := mem_iUnion.mp hdensity
      exact densityCoefficient_exists e f ρ hρ φ
    | zero => exact ⟨0, by ext x; simp [chartDensityFunction]⟩
    | add density eta hdensity heta ihdensity iheta =>
      obtain ⟨φ, hφ⟩ := ihdensity
      obtain ⟨ψ, hψ⟩ := iheta
      refine ⟨φ + ψ, ?_⟩
      rw [show chartDensityFunction e (φ + ψ) = chartDensityFunction e φ + chartDensityFunction e ψ
        from (chartDensityLM 𝕜 e).map_add φ ψ, hφ, hψ]
      ext x
      exact (smul_add ..).symm
    | smul c density hdensity ihdensity =>
      obtain ⟨φ, hφ⟩ := ihdensity
      refine ⟨c • φ, ?_⟩
      rw [show chartDensityFunction e (c • φ) = c • chartDensityFunction e φ
        from (chartDensityLM 𝕜 e).map_smul c φ, hφ]
      ext x
      exact smul_comm c (ρ x) (density x)
  obtain ⟨ψ, hψ⟩ := hex
  exact ⟨ψ, hψ, fun φ hφ => chartDensityFunction_injective e (hφ.trans hψ.symm)⟩

/-- The unique compact coordinate coefficient of a cutoff density. -/
def densityCoefficient {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (density : ↥(TestDensities 𝕜 M)) :
    TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ :=
  Classical.choose (densityCoefficient_exists_unique e ρ hρ density).exists

lemma densityCoefficient_spec {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (density : ↥(TestDensities 𝕜 M)) :
    chartDensityFunction e (densityCoefficient e ρ hρ density) = fun x => ρ x • density.val x :=
  Classical.choose_spec (densityCoefficient_exists_unique e ρ hρ density).exists

/-- Density extraction is an actual scalar-linear map; continuity is a separate
remaining obligation, not a field or a hypothesis of this construction. -/
def densityCoefficientLM {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source) :
    TestDensities 𝕜 M →ₗ[𝕜] TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ where
  toFun := densityCoefficient e ρ hρ
  map_add' density eta := by
    apply chartDensityFunction_injective e
    rw [densityCoefficient_spec,
      show chartDensityFunction e (densityCoefficient e ρ hρ density + densityCoefficient e ρ hρ eta) =
        chartDensityFunction e (densityCoefficient e ρ hρ density) +
          chartDensityFunction e (densityCoefficient e ρ hρ eta) from (chartDensityLM 𝕜 e).map_add _ _,
      densityCoefficient_spec, densityCoefficient_spec]
    ext x
    exact smul_add _ _ _
  map_smul' c density := by
    change densityCoefficient e ρ hρ (c • density) = c • densityCoefficient e ρ hρ density
    apply chartDensityFunction_injective e
    rw [densityCoefficient_spec,
      show chartDensityFunction e (c • densityCoefficient e ρ hρ density) =
        c • chartDensityFunction e (densityCoefficient e ρ hρ density) from (chartDensityLM 𝕜 e).map_smul _ _,
      densityCoefficient_spec]
    ext x
    exact smul_comm (ρ x) c (density.val x)

end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem density_coefficient_extraction :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.densityCoefficientExtractionType := by
  intro M _ _ _ 𝕜 _ e ρ hρ
  exact ⟨densityCoefficientLM e ρ hρ, densityCoefficient_spec e ρ hρ⟩

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe uf
variable {M : Type uf} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]

/-- A chart-supported smooth scalar equal to one around a partition cutoff. -/
def partitionReconstructionCutoff (A : FiniteChartPartition M) (i : Fin A.n) :
    C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯ :=
  Classical.choose (exists_smoothCutoff M (isClosed_tsupport (A.cutoff i))
    (A.chart i).open_source (A.subordinate i))

lemma partitionReconstructionCutoff_support (A : FiniteChartPartition M) (i : Fin A.n) :
    tsupport (partitionReconstructionCutoff A i) ⊆ (A.chart i).source :=
  (Classical.choose_spec (exists_smoothCutoff M (isClosed_tsupport (A.cutoff i))
    (A.chart i).open_source (A.subordinate i))).2.1

lemma partitionReconstructionCutoff_eq_one (A : FiniteChartPartition M) (i : Fin A.n)
    {x : M} (hx : x ∈ tsupport (A.cutoff i)) :
    partitionReconstructionCutoff A i x = 1 :=
  subset_of_mem_nhdsSet
    (Classical.choose_spec (exists_smoothCutoff M (isClosed_tsupport (A.cutoff i))
      (A.chart i).open_source (A.subordinate i))).1 hx

lemma partitionReconstructionCutoff_hasCompactSupport (A : FiniteChartPartition M)
    (i : Fin A.n) : HasCompactSupport (partitionReconstructionCutoff A i) :=
  (Classical.choose_spec (exists_smoothCutoff M (isClosed_tsupport (A.cutoff i))
    (A.chart i).open_source (A.subordinate i))).2.2.2

lemma partitionReconstructionCutoff_mul (A : FiniteChartPartition M) (i : Fin A.n)
    (x : M) : A.cutoff i x * partitionReconstructionCutoff A i x = A.cutoff i x := by
  by_cases hx : x ∈ tsupport (A.cutoff i)
  · rw [partitionReconstructionCutoff_eq_one A i hx, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- The compact coefficient of a density, extracted in one partition chart. -/
def partitionDensityCoefficient {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) :
    TestDensities 𝕜 M →ₗ[𝕜]
      TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤ :=
  densityCoefficientLM ⟨A.chart i, A.chart_smooth i⟩
    (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i)

lemma partitionDensityCoefficient_spec {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) (d : TestDensities 𝕜 M) :
    chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩ (partitionDensityCoefficient A i d) =
      fun x => partitionReconstructionCutoff A i x • d.val x :=
  densityCoefficient_spec ⟨A.chart i, A.chart_smooth i⟩
    (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i) d

/-- Applying the partition cutoff to the extracted coefficient is exactly
multiplication of the intrinsic density by that scalar cutoff. -/
lemma chartDensity_partitionDensityCoefficient {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) (d : TestDensities 𝕜 M) :
    chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩
      (schwartzCutoffToTest _ (chartCutoffTest A i)
        ((partitionDensityCoefficient A i d).hasCompactSupport.toSchwartzMap
          (partitionDensityCoefficient A i d).contDiff)) =
      fun x => A.cutoff i x • d.val x := by
  funext x
  let e : SmoothChart M := ⟨A.chart i, A.chart_smooth i⟩
  have hR := congrFun (partitionDensityCoefficient_spec A i d) x
  by_cases hx : x ∈ (A.chart i).source
  · have hy := (A.chart i).map_source hx
    simp only [chartDensityFunction, indicator_of_mem hx] at hR ⊢
    rw [schwartzCutoffToTest_apply, chartCutoffTest_apply,
      chartLocalFunction_apply A (fun _ => (1 : 𝕜)) i hy, (A.chart i).left_inv hx]
    change e.densityJacobian x • ((A.cutoff i x • (1 : 𝕜)) *
      partitionDensityCoefficient A i d ((A.chart i) x)) = _
    rw [smul_mul_assoc, one_mul, smul_comm, hR, smul_smul,
      partitionReconstructionCutoff_mul]
  · have hz : A.cutoff i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.subordinate i h))
    simp [chartDensityFunction, hx, hz]

/-- A finite partition recovers every actual intrinsic compact test density. -/
theorem partitionDensity_reconstruct {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (d : TestDensities 𝕜 M) :
    (∑ i, chartTestDensity 𝕜 ⟨A.chart i, A.chart_smooth i⟩
      (schwartzCutoffToTest _ (chartCutoffTest A i)
        ((partitionDensityCoefficient A i d).hasCompactSupport.toSchwartzMap
          (partitionDensityCoefficient A i d).contDiff))) = d := by
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  ext x
  simp only [Finset.sum_apply]
  change (∑ i, chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩
    (schwartzCutoffToTest _ (chartCutoffTest A i)
      ((partitionDensityCoefficient A i d).hasCompactSupport.toSchwartzMap
        (partitionDensityCoefficient A i d).contDiff)) x) = d.val x
  simp_rw [chartDensity_partitionDensityCoefficient]
  rw [← Finset.sum_smul, A.sum_one x, one_smul]

namespace ScalarCurveDistribution
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every distribution value is recovered from the finitely many actual
whole-line localizations determined by any finite smooth chart partition. -/
theorem partitionDistribution_reconstruct (T : ScalarCurveDistribution 𝕜 M)
    (A : FiniteChartPartition M) (d : TestDensities 𝕜 M) :
    (∑ i, partitionDistribution T A i
      ((partitionDensityCoefficient A i d).hasCompactSupport.toSchwartzMap
        (partitionDensityCoefficient A i d).contDiff)) = T.toLinearMap d := by
  calc
    _ = T.toLinearMap (∑ i, chartTestDensity 𝕜 ⟨A.chart i, A.chart_smooth i⟩
        (schwartzCutoffToTest _ (chartCutoffTest A i)
          ((partitionDensityCoefficient A i d).hasCompactSupport.toSchwartzMap
            (partitionDensityCoefficient A i d).contDiff))) := by
      rw [map_sum]
      rfl
    _ = T.toLinearMap d := by rw [partitionDensity_reconstruct]

/-- A finite partition's compact chart localizations jointly determine the
intrinsic scalar distribution, including on the empty curve. -/
theorem ext_partitionDistribution (A : FiniteChartPartition M)
    {T S : ScalarCurveDistribution 𝕜 M}
    (h : ∀ i, partitionDistribution T A i = partitionDistribution S A i) : T = S := by
  apply Subtype.ext
  apply LinearMap.ext
  intro d
  change T.toLinearMap d = S.toLinearMap d
  rw [← partitionDistribution_reconstruct T A d, ← partitionDistribution_reconstruct S A d]
  simp_rw [h]

end ScalarCurveDistribution
end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff SchwartzMap NNReal
namespace ExpandedFA.Sobolev.Curve
universe ue
variable {M : Type ue} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

/-- Inclusion of a fixed compact test step into the Schwartz space. -/
def testStepToSchwartz {𝕜 : Type*} [RCLike 𝕜] (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ 𝕜 ⊤ K →L[𝕜] SchwartzMap ℝ 𝕜 := by
  let L : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K →ₗ[𝕜] SchwartzMap ℝ 𝕜 :=
    { toFun := fun φ => φ.hasCompactSupport.toSchwartzMap φ.contDiff
      map_add' := fun φ ψ => by ext x; rfl
      map_smul' := fun c φ => by ext x; rfl }
  refine ⟨L, ?_⟩
  apply (schwartz_withSeminorms 𝕜 ℝ 𝕜).continuous_of_continuous_comp L
  rintro ⟨k, n⟩
  obtain ⟨B, hB⟩ := K.isCompact.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (id : ℝ → ℝ) K)
  have hseminorm := (ContDiffMapSupportedIn.withSeminorms 𝕜 ℝ 𝕜 ⊤ K).continuous_seminorm n
  let c : ℝ≥0 := ⟨(max 0 B)^k, by positivity⟩
  apply Seminorm.continuous_of_le (q := c • ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K n)
    (show Continuous (c • ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K n) from hseminorm.const_smul c)
  intro φ
  change SchwartzMap.seminorm 𝕜 k n (L φ) ≤ (max 0 B)^k *
    ContDiffMapSupportedIn.seminorm 𝕜 ℝ 𝕜 ⊤ K n φ
  apply SchwartzMap.seminorm_le_bound 𝕜 k n (L φ) (by positivity)
  intro x
  change ‖x‖^k * ‖iteratedFDeriv ℝ n (φ : ℝ → 𝕜) x‖ ≤ _
  by_cases hx : x ∈ K
  · apply mul_le_mul _ (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜)
      (norm_nonneg _) (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) ((hB x hx).trans (le_max_right _ _)) _
  · simp only [φ.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
    positivity

@[simp] lemma testStepToSchwartz_apply {𝕜 : Type*} [RCLike 𝕜] (K : Compacts ℝ)
    (φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K) (x : ℝ) :
    testStepToSchwartz K φ x = φ x := rfl

/-- The exact coordinate coefficient, regarded as a Schwartz function. -/
def densityCoefficientSchwartzLM {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source) :
    TestDensities 𝕜 M →ₗ[𝕜] SchwartzMap ℝ 𝕜 where
  toFun density := (densityCoefficient e ρ hρ density).hasCompactSupport.toSchwartzMap
    (densityCoefficient e ρ hρ density).contDiff
  map_add' d eta := by
    ext x
    change densityCoefficientLM e ρ hρ (d + eta) x = _
    rw [map_add]
    rfl
  map_smul' c d := by
    ext x
    change densityCoefficientLM e ρ hρ (c • d) x = _
    rw [map_smul]
    rfl

@[simp] lemma densityCoefficientSchwartzLM_apply {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (density : TestDensities 𝕜 M) (x : ℝ) :
    densityCoefficientSchwartzLM e ρ hρ density x = densityCoefficient e ρ hρ density x := rfl


/-- A fixed compact input step allows one smooth compact multiplier on the overlap. -/
lemma densityExtractionStepCoefficient_exists {𝕜 : Type*} [RCLike 𝕜]
    (e f : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) (K : Compacts ℝ) (hK : (K : Set ℝ) ⊆ f.val.target) :
    ∃ a : ℝ → 𝕜, ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
      tsupport a ⊆ (f.transition e).source ∧
      ∀ y ∈ K, a y = (ρ (f.val.symm y) : 𝕜) := by
  obtain ⟨θ, hθ, hθc, hθs, hθ1⟩ := compact_smoothCutoff K.isCompact f.val.open_target hK
  let a : ℝ → 𝕜 := f.val.target.indicator (fun y => ρ (f.val.symm y) • (θ y : 𝕜))
  have hasub : tsupport a ⊆ tsupport θ := by
    apply closure_mono
    intro y hy
    by_contra hθy
    have hz : θ y = 0 := by simpa only [Function.mem_support, not_not] using hθy
    exact hy (by simp [a, hz])
  have hρf : ContDiffOn ℝ ∞ (fun y => ρ (f.val.symm y)) f.val.target :=
    (ρ.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas f.property)).contDiffOn
  have hθk : ContDiff ℝ ∞ (fun y => (θ y : 𝕜)) :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hθ
  have had : ContDiff ℝ ∞ a :=
    contDiff_indicator_of_support f.val.target f.val.open_target _
      (hρf.smul hθk.contDiffOn) (hasub.trans hθs)
  have hac : HasCompactSupport a := hθc.of_isClosed_subset (isClosed_tsupport a) hasub
  refine ⟨a, had, hac, ?_, ?_⟩
  · intro y hy
    have hyt : y ∈ f.val.target := hθs (hasub hy)
    have hxρ : f.val.symm y ∈ tsupport ρ := by
      by_contra hxρ
      have hz := notMem_tsupport_iff_eventuallyEq.mp hxρ
      have hfi : ContinuousAt f.val.symm y :=
        f.val.symm.continuousOn.continuousAt (f.val.open_target.mem_nhds hyt)
      have hazero : a =ᶠ[𝓝 y] 0 := by
        filter_upwards [hz.comp_tendsto hfi.tendsto] with z hz
        dsimp only [Function.comp_def, Pi.zero_apply] at hz
        simp [a, hz]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hazero) hy
    change y ∈ f.val.target ∧ f.val.symm y ∈ e.val.source
    exact ⟨hyt, hρ hxρ⟩
  · intro y hy
    simp [a, hK hy, hθ1 y hy]

/-- On every fixed compact LF step, extraction is one existing continuous
localized density operator after the compact-step inclusion into Schwartz. -/
lemma densityCoefficientSchwartz_step_eq {𝕜 : Type*} [RCLike 𝕜]
    (e f : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) (K : Compacts ℝ) (hK : (K : Set ℝ) ⊆ f.val.target) :
    ∃ Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜,
      ∀ φ : ContDiffMapSupportedIn ℝ 𝕜 ⊤ K,
        densityCoefficientSchwartzLM e ρ hρ (chartTestDensity 𝕜 f (TestFunction.ofSupportedIn hK φ)) =
          Q (testStepToSchwartz K φ) := by
  obtain ⟨a, ha, hac, has, haK⟩ := densityExtractionStepCoefficient_exists (𝕜 := 𝕜) e f ρ hρ K hK
  let t := f.transition e
  obtain ⟨Q, hQ⟩ := localizedSchwartzDensity_exists t (f.transition_smooth e)
    (e.transition_smooth f) a ha hac has
  refine ⟨Q, fun φ => ?_⟩
  let Φ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤ := TestFunction.ofSupportedIn hK φ
  let β : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤ :=
    ⟨fun y => a y * Φ y, ha.mul Φ.contDiff,
      hac.mul_right, (tsupport_mul_subset_left ..).trans (has.trans (fun _ hy => hy.1))⟩
  have hβs : tsupport β ⊆ t.source := (tsupport_mul_subset_left ..).trans has
  obtain ⟨ψ, hψ⟩ := chartDensityTransfer_exists f e β hβs
  have hψQ : (ψ : ℝ → 𝕜) = Q (testStepToSchwartz K φ) := by
    funext y
    rw [hψ, hQ]
    rfl
  have hβ : chartDensityFunction f β = fun x => ρ x • chartDensityFunction f Φ x := by
    funext x
    by_cases hx : x ∈ f.val.source
    · have hy : f.val x ∈ f.val.target := f.val.map_source hx
      simp only [chartDensityFunction, indicator_of_mem hx]
      change f.densityJacobian x • (a (f.val x) * Φ (f.val x)) =
        ρ x • f.densityJacobian x • Φ (f.val x)
      by_cases hyK : f.val x ∈ K
      · rw [haK _ hyK, f.val.left_inv hx]
        rw [← RCLike.real_smul_eq_coe_mul]
        exact smul_comm _ _ _
      · have hz : Φ (f.val x) = 0 := φ.zero_on_compl hyK
        simp [hz]
    · simp [chartDensityFunction, hx]
  have heq : densityCoefficient e ρ hρ (chartTestDensity 𝕜 f Φ) = ψ := by
    apply chartDensityFunction_injective e
    rw [densityCoefficient_spec]
    exact hβ.symm.trans (chartDensityFunction_transition f e β ψ hβs hψ)
  ext y
  change densityCoefficient e ρ hρ (chartTestDensity 𝕜 f Φ) y = Q (testStepToSchwartz K φ) y
  rw [heq]
  exact congrFun hψQ y

/-- Extraction of an intrinsic density coefficient is continuous on every
native chart LF test space. -/
theorem continuous_densityCoefficientSchwartz_chart {𝕜 : Type*} [RCLike 𝕜]
    (e f : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) :
    Continuous ((densityCoefficientSchwartzLM (𝕜 := 𝕜) e ρ hρ).comp (chartTestDensity 𝕜 f)) := by
  apply (TestFunction.continuous_iff_continuous_comp
    ((densityCoefficientSchwartzLM (𝕜 := 𝕜) e ρ hρ).comp (chartTestDensity 𝕜 f))).mpr
  intro K hK
  obtain ⟨Q, hQ⟩ := densityCoefficientSchwartz_step_eq (𝕜 := 𝕜) e f ρ hρ K hK
  have heq : ((densityCoefficientSchwartzLM (𝕜 := 𝕜) e ρ hρ).comp (chartTestDensity 𝕜 f)) ∘
      TestFunction.ofSupportedIn hK = Q ∘ testStepToSchwartz K := funext hQ
  rw [heq]
  exact Q.continuous.comp (testStepToSchwartz K).continuous

/-- The chartwise LF-to-Schwartz continuous extraction operator. -/
def densityCoefficientSchwartzChartCLM {𝕜 : Type*} [RCLike 𝕜]
    (e f : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) :
    TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤ →L[𝕜] SchwartzMap ℝ 𝕜 :=
  ⟨(densityCoefficientSchwartzLM e ρ hρ).comp (chartTestDensity 𝕜 f),
    continuous_densityCoefficientSchwartz_chart e f ρ hρ⟩

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe ug
variable {M : Type ug} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]

/-- The chart density extraction used for finite synthesis, as a genuine
Schwartz-valued linear map. -/
def partitionDensitySchwartzLM {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) :
    TestDensities 𝕜 M →ₗ[𝕜] SchwartzMap ℝ 𝕜 :=
  densityCoefficientSchwartzLM ⟨A.chart i, A.chart_smooth i⟩
    (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i)

@[simp] lemma partitionDensitySchwartzLM_apply {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (i : Fin A.n) (d : TestDensities 𝕜 M) (x : ℝ) :
    partitionDensitySchwartzLM A i d x = partitionDensityCoefficient A i d x := rfl

/-- Pairing a finite tuple of tempered chart distributions against intrinsic
densities through their exact smooth compact coefficient extractions. -/
def partitionSynthesisLinear {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) :
    TestDensities 𝕜 M →ₗ[𝕜] 𝕜 :=
  ∑ i, (v i).toLinearMap.comp (partitionDensitySchwartzLM A i)

@[simp] lemma partitionSynthesisLinear_apply {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (d : TestDensities 𝕜 M) :
    partitionSynthesisLinear A v d = ∑ i, v i (partitionDensitySchwartzLM A i d) := by
  simp only [partitionSynthesisLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

lemma partitionSynthesisLinear_continuous_chart {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (f : SmoothChart M) :
    Continuous ((partitionSynthesisLinear A v).comp (chartTestDensity 𝕜 f)) := by
  change Continuous (fun φ => partitionSynthesisLinear A v (chartTestDensity 𝕜 f φ))
  simp_rw [partitionSynthesisLinear_apply]
  apply continuous_finsetSum
  intro i _
  exact (v i).continuous.comp (continuous_densityCoefficientSchwartz_chart
    ⟨A.chart i, A.chart_smooth i⟩ f (partitionReconstructionCutoff A i)
      (partitionReconstructionCutoff_support A i))

/-- Synthesis of arbitrary finite tempered chart tuples is an actual intrinsic
scalar distribution; local LF continuity follows from proved extraction continuity. -/
def partitionSynthesis {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) :
    ScalarCurveDistribution 𝕜 M :=
  ⟨partitionSynthesisLinear A v, partitionSynthesisLinear_continuous_chart A v⟩

@[simp] lemma partitionSynthesis_apply {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (d : TestDensities 𝕜 M) :
    (partitionSynthesis A v).toLinearMap d =
      ∑ i, v i (partitionDensitySchwartzLM A i d) :=
  partitionSynthesisLinear_apply A v d

/-- The finite synthesis operation is scalar linear. -/
def partitionSynthesisLM {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M) :
    (Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) →ₗ[𝕜] ScalarCurveDistribution 𝕜 M where
  toFun := partitionSynthesis A
  map_add' v w := by
    apply Subtype.ext
    apply LinearMap.ext
    intro d
    change (partitionSynthesis A (v + w)).toLinearMap d =
      (partitionSynthesis A v).toLinearMap d + (partitionSynthesis A w).toLinearMap d
    simp only [partitionSynthesis_apply, Pi.add_apply, add_apply,
      Finset.sum_add_distrib]
  map_smul' c v := by
    apply Subtype.ext
    apply LinearMap.ext
    intro d
    change (partitionSynthesis A (c • v)).toLinearMap d =
      c • (partitionSynthesis A v).toLinearMap d
    simp only [partitionSynthesis_apply, Pi.smul_apply, smul_apply,
      Finset.smul_sum]

/-- The finite localization operation is scalar linear. -/
def partitionLocalizationLM {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M) :
    ScalarCurveDistribution 𝕜 M →ₗ[𝕜] (Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) where
  toFun T := fun i => partitionDistribution T A i
  map_add' T S := by ext i φ; rfl
  map_smul' c T := by ext i φ; rfl

/-- Exact reconstruction of every scalar distribution from its finite chart
localizations, with no regularity restriction on the distribution. -/
theorem partitionSynthesis_partitionLocalization {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (T : ScalarCurveDistribution 𝕜 M) :
    partitionSynthesis A (partitionLocalizationLM A T) = T := by
  apply Subtype.ext
  apply LinearMap.ext
  intro d
  change (partitionSynthesis A (partitionLocalizationLM A T)).toLinearMap d = T.toLinearMap d
  rw [partitionSynthesis_apply]
  exact ScalarCurveDistribution.partitionDistribution_reconstruct T A d

lemma partitionSynthesisLM_leftInverse {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) :
    Function.LeftInverse (partitionSynthesisLM (𝕜 := 𝕜) A) (partitionLocalizationLM A) :=
  partitionSynthesis_partitionLocalization A

/-- Testing a synthesized distribution in any compact chart localization is
exactly the finite transpose sum fixed by its density coefficient extraction. -/
theorem partitionSynthesis_localize {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (v : Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (e : SmoothChart M) (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (φ : SchwartzMap ℝ 𝕜) :
    (partitionSynthesis A v).localize e a φ =
      ∑ i, v i (partitionDensitySchwartzLM A i
        (chartTestDensity 𝕜 e (schwartzCutoffToTest _ a φ))) := by
  change (partitionSynthesis A v).toLinearMap
    (chartTestDensity 𝕜 e (schwartzCutoffToTest _ a φ)) = _
  exact partitionSynthesis_apply A v _

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The scalar coefficient for localizing a chart-supported synthesis term. -/
def chartSynthesisCoefficient (B : FiniteChartPartition M) (j : Fin B.n)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) :
    TestFunction ⟨(B.chart j).target, (B.chart j).open_target⟩ 𝕜 ⊤ := by
  let g : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
    ⟨fun x => (B.cutoff j x * ρ x : ℝ),
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contMDiff.comp
        ((B.cutoff j).contMDiff.mul ρ.contMDiff)⟩
  have hs : tsupport g ⊆ (B.chart j).source :=
    (tsupport_comp_subset (RCLike.ofReal_zero) (fun x => B.cutoff j x * ρ x)).trans
      ((tsupport_mul_subset_left (f := fun x => B.cutoff j x) (g := fun x => ρ x)).trans (B.subordinate j))
  exact chartTest M (B.chart j) (B.chart_smooth j) g hs

lemma chartSynthesisCoefficient_apply (B : FiniteChartPartition M) (j : Fin B.n)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) {y : ℝ} (hy : y ∈ (B.chart j).target) :
    chartSynthesisCoefficient (𝕜 := 𝕜) B j ρ y =
      ((B.cutoff j ((B.chart j).symm y) * ρ ((B.chart j).symm y) : ℝ) : 𝕜) := by
  unfold chartSynthesisCoefficient
  exact chartTest_apply M (B.chart j) (B.chart_smooth j) _ _ y hy

lemma chartSynthesisCoefficient_support (B : FiniteChartPartition M) (j : Fin B.n)
    (e : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) :
    tsupport (chartSynthesisCoefficient (𝕜 := 𝕜) B j ρ) ⊆
      ((⟨B.chart j, B.chart_smooth j⟩ : SmoothChart M).transition e).source := by
  let g : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯ :=
    ⟨fun x => ((B.cutoff j x * ρ x : ℝ) : 𝕜),
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contMDiff.comp
        ((B.cutoff j).contMDiff.mul ρ.contMDiff)⟩
  have hs : tsupport g ⊆ (B.chart j).source :=
    (tsupport_comp_subset RCLike.ofReal_zero (fun x => B.cutoff j x * ρ x)).trans
      ((tsupport_mul_subset_left (f := fun x => B.cutoff j x) (g := fun x => ρ x)).trans (B.subordinate j))
  have hsρ : tsupport g ⊆ e.val.source :=
    (tsupport_comp_subset RCLike.ofReal_zero (fun x => B.cutoff j x * ρ x)).trans
      ((tsupport_mul_subset_right (f := fun x => B.cutoff j x) (g := fun x => ρ x)).trans hρ)
  intro y hy
  have hyt := (chartSynthesisCoefficient (𝕜 := 𝕜) B j ρ).tsupport_subset hy
  obtain ⟨x, hx, hxy⟩ := chartTest_tsupport_subset_image (B.chart j) (B.chart_smooth j) g hs hy
  change y ∈ (B.chart j).target ∧ (B.chart j).symm y ∈ e.val.source
  refine ⟨hyt, ?_⟩
  rw [← hxy, (B.chart j).left_inv (hs hx)]
  exact hsρ hx

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma chartDensity_synthesisCoefficient (B : FiniteChartPartition M) (j : Fin B.n)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (φ : SchwartzMap ℝ 𝕜) :
    chartDensityFunction ⟨B.chart j, B.chart_smooth j⟩
      (schwartzCutoffToTest _ (chartSynthesisCoefficient B j ρ) φ) =
    fun x => ρ x • chartDensityFunction ⟨B.chart j, B.chart_smooth j⟩
      (schwartzCutoffToTest _ (chartCutoffTest B j) φ) x := by
  funext x
  by_cases hx : x ∈ (B.chart j).source
  · have hy := (B.chart j).map_source hx
    simp only [chartDensityFunction, indicator_of_mem hx, schwartzCutoffToTest_apply]
    rw [chartSynthesisCoefficient_apply B j ρ hy, chartCutoffTest_apply,
      chartLocalFunction_apply B (fun _ => (1 : 𝕜)) j hy, (B.chart j).left_inv hx]
    simp [Algebra.smul_def, mul_left_comm, mul_comm]
  · simp [chartDensityFunction, hx]

lemma densityCoefficient_localization (B : FiniteChartPartition M) (j : Fin B.n)
    (e : SmoothChart M) (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ e.val.source) (φ : SchwartzMap ℝ 𝕜) (y : ℝ) :
    densityCoefficient e ρ hρ
      (chartTestDensity 𝕜 ⟨B.chart j, B.chart_smooth j⟩
        (schwartzCutoffToTest _ (chartCutoffTest B j) φ)) y =
      localizedDensity ((⟨B.chart j, B.chart_smooth j⟩ : SmoothChart M).transition e)
        (chartSynthesisCoefficient B j ρ) φ y := by
  let f : SmoothChart M := ⟨B.chart j, B.chart_smooth j⟩
  let β := schwartzCutoffToTest _ (chartSynthesisCoefficient B j ρ) φ
  have hβ : tsupport β ⊆ (f.transition e).source := by
    have hb : (β : ℝ → 𝕜) = fun x => chartSynthesisCoefficient B j ρ x * φ x :=
      funext (schwartzCutoffToTest_apply _ _ φ)
    rw [hb]
    exact tsupport_mul_subset_left.trans (chartSynthesisCoefficient_support B j e ρ hρ)
  obtain ⟨ψ, hψ⟩ := chartDensityTransfer_exists f e β hβ
  have hEq : densityCoefficient e ρ hρ
      (chartTestDensity 𝕜 f (schwartzCutoffToTest _ (chartCutoffTest B j) φ)) = ψ := by
    apply chartDensityFunction_injective e
    rw [densityCoefficient_spec, ← chartDensityFunction_transition f e β ψ hβ hψ]
    exact (chartDensity_synthesisCoefficient B j ρ φ).symm
  rw [hEq, hψ]
  have hβfun : (β : ℝ → 𝕜) = (chartSynthesisCoefficient B j ρ : ℝ → 𝕜) * φ :=
    funext (schwartzCutoffToTest_apply _ _ φ)
  rw [hβfun]
  rfl

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ℝ N] [IsManifold (𝓘(ℝ)) ∞ N]

namespace SmoothChart

lemma eq_of_val_eq {c d : SmoothChart M} (h : c.val = d.val) : c = d := by
  cases c
  cases d
  cases h
  rfl

def pullback (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) : SmoothChart M where
  val := e.toHomeomorph.transOpenPartialHomeomorph c.val
  property := by
    rw [Homeomorph.transOpenPartialHomeomorph_eq_trans]
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · apply (contMDiffOn_of_mem_maximalAtlas c.property).comp e.contMDiff.contMDiffOn
      intro x hx
      exact hx.2
    · apply e.symm.contMDiff.comp_contMDiffOn
      apply (contMDiffOn_symm_of_mem_maximalAtlas c.property).mono
      intro y hy
      exact hy.1

@[simp] lemma pullback_target (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    (c.pullback e).val.target = c.val.target := rfl

@[simp] lemma pullback_source (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    (c.pullback e).val.source = e ⁻¹' c.val.source := rfl

@[simp] lemma pullback_apply (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (x : M) :
    (c.pullback e).val x = c.val (e x) := rfl

@[simp] lemma pullback_transition (c d : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    (c.pullback e).transition (d.pullback e) = c.transition d := by
  exact Homeomorph.transOpenPartialHomeomorph_symm_trans e.toHomeomorph

/-- The absolute Jacobian of a smooth map measured in the preferred source and target charts. -/
def mapJacobian (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (x : M) : ℝ :=
  ((⟨chartAt ℝ (e x), chart_mem_maximalAtlas (e x)⟩ : SmoothChart N).pullback e).densityJacobian x

lemma mapJacobian_pos (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (x : M) :
    0 < mapJacobian e x := by
  apply densityJacobian_pos
  exact mem_chart_source ℝ (e x)

lemma pullback_densityJacobian (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    {x : M} (hx : e x ∈ c.val.source) :
    (c.pullback e).densityJacobian x = c.densityJacobian (e x) * mapJacobian e x := by
  let c₀ : SmoothChart N := ⟨chartAt ℝ (e x), chart_mem_maximalAtlas (e x)⟩
  have h := densityJacobian_transition (c₀.pullback e) (c.pullback e)
    (show x ∈ (c₀.pullback e).val.source from mem_chart_source ℝ (e x)) hx
  simpa only [pullback_transition, pullback_apply, densityJacobian, mapJacobian, c₀] using h

@[simp] lemma pullback_symm (c : SmoothChart N) (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    (c.pullback e).pullback e.symm = c := by
  have hv : ((c.pullback e).pullback e.symm).val = c.val := by
    change e.symm.toHomeomorph.transOpenPartialHomeomorph
      (e.toHomeomorph.transOpenPartialHomeomorph c.val) = c.val
    rw [← Homeomorph.trans_transOpenPartialHomeomorph]
    have hid : e.symm.toHomeomorph.trans e.toHomeomorph = Homeomorph.refl N := by ext x; simp
    rw [hid]
    rfl
  have hinj : Function.Injective (SmoothChart.val (M := N)) := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  exact hinj hv

lemma mapJacobian_symm_mul (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (x : M) :
    mapJacobian e x * mapJacobian e.symm (e x) = 1 := by
  let c : SmoothChart N := ⟨chartAt ℝ (e x), chart_mem_maximalAtlas (e x)⟩
  have hx : e x ∈ c.val.source := mem_chart_source ℝ (e x)
  have h := (c.pullback e).pullback_densityJacobian e.symm
    (x := e x) (show e.symm (e x) ∈ (c.pullback e).val.source from by simpa using hx)
  rw [pullback_symm] at h
  simp only [e.symm_apply_apply] at h
  rw [c.pullback_densityJacobian e hx] at h
  apply mul_left_cancel₀ (ne_of_gt (c.densityJacobian_pos hx))
  simpa only [mul_assoc, mul_one] using h.symm

lemma mapJacobian_symm (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (y : N) :
    mapJacobian e.symm y = (mapJacobian e (e.symm y))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have hee : e.symm.symm = e := by ext x; rfl
  simpa only [hee] using mapJacobian_symm_mul e.symm y

lemma mapJacobian_eq_deriv (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (x : M) :
    mapJacobian e x =
      |deriv (fun z : ℝ => (chartAt ℝ (e x)) (e ((chartAt ℝ x).symm z)))
        ((chartAt ℝ x) x)| := rfl

end SmoothChart

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pullback of actual test density sections, with the absolute map Jacobian. -/
def densityPullbackFunction (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) : (N → 𝕜) →ₗ[𝕜] (M → 𝕜) where
  toFun ρ x := SmoothChart.mapJacobian e x • ρ (e x)
  map_add' ρ σ := by ext x; exact smul_add _ _ _
  map_smul' c ρ := by
    ext x
    change SmoothChart.mapJacobian e x • (c • ρ (e x)) =
      c • (SmoothChart.mapJacobian e x • ρ (e x))
    exact smul_comm _ _ _

lemma densityPullbackFunction_chart (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (c : SmoothChart N)
    (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    densityPullbackFunction e (chartDensityFunction c φ) =
      chartDensityFunction (c.pullback e) φ := by
  ext x
  by_cases hx : e x ∈ c.val.source
  · simp [densityPullbackFunction, chartDensityFunction, hx,
      c.pullback_densityJacobian e hx, smul_smul, mul_comm]
  · simp [densityPullbackFunction, chartDensityFunction, hx]

lemma densityPullbackFunction_mem (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    {ρ : N → 𝕜} (hρ : ρ ∈ TestDensities 𝕜 N) :
    densityPullbackFunction e ρ ∈ TestDensities 𝕜 M := by
  change ρ ∈ Submodule.span 𝕜 _ at hρ
  induction hρ using Submodule.span_induction with
  | mem ρ hρ =>
    obtain ⟨c, φ, rfl⟩ := mem_iUnion.mp hρ
    rw [show chartDensityLM 𝕜 c φ = chartDensityFunction c φ from rfl,
      densityPullbackFunction_chart]
    exact (chartTestDensity 𝕜 (c.pullback e) φ).property
  | zero => simpa only [map_zero] using (TestDensities 𝕜 M).zero_mem
  | add ρ σ hρ hσ ihρ ihσ => simpa only [map_add] using (TestDensities 𝕜 M).add_mem ihρ ihσ
  | smul c ρ hρ ihρ => simpa only [map_smul] using (TestDensities 𝕜 M).smul_mem c ihρ

/-- The geometric pullback of compact smooth test densities. -/
def densityPullback (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    TestDensities 𝕜 N →ₗ[𝕜] TestDensities 𝕜 M :=
  ((densityPullbackFunction (𝕜 := 𝕜) e).domRestrict (TestDensities 𝕜 N)).codRestrict
    (TestDensities 𝕜 M) (fun ρ => densityPullbackFunction_mem e ρ.property)

@[simp] lemma densityPullback_apply (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (ρ : TestDensities 𝕜 N) (x : M) :
    (densityPullback e ρ).val x = SmoothChart.mapJacobian e x • ρ.val (e x) := rfl

lemma densityPullback_chart (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (c : SmoothChart N) :
    (densityPullback e).comp (chartTestDensity 𝕜 c) = chartTestDensity 𝕜 (c.pullback e) := by
  ext φ x
  exact congrFun (densityPullbackFunction_chart e c φ) x

@[simp] lemma densityPullback_symm_apply (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (ρ : TestDensities 𝕜 N) : densityPullback e.symm (densityPullback e ρ) = ρ := by
  apply Subtype.ext
  ext y
  simp only [densityPullback_apply, e.apply_symm_apply, smul_smul]
  have h := SmoothChart.mapJacobian_symm_mul e.symm y
  have hee : e.symm.symm = e := by ext x; rfl
  rw [hee] at h
  rw [h, one_smul]

/-- Smooth changes of variables act invertibly on actual compact test densities. -/
def densityPullbackEquiv (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    TestDensities 𝕜 N ≃ₗ[𝕜] TestDensities 𝕜 M where
  toLinearMap := densityPullback e
  invFun := densityPullback e.symm
  left_inv := densityPullback_symm_apply e
  right_inv := densityPullback_symm_apply e.symm

namespace ScalarCurveDistribution

/-- Scalar distribution pullback is the transpose of the inverse-map density pullback. -/
def pullbackLM (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    ScalarCurveDistribution 𝕜 N →ₗ[𝕜] ScalarCurveDistribution 𝕜 M where
  toFun T := ⟨T.toLinearMap.comp (densityPullback e.symm), by
    intro c
    change Continuous ((T.toLinearMap.comp (densityPullback e.symm)).comp (chartTestDensity 𝕜 c))
    rw [LinearMap.comp_assoc, densityPullback_chart]
    exact T.continuous_chart (c.pullback e.symm)⟩
  map_add' T S := rfl
  map_smul' c T := rfl

@[simp] lemma pullbackLM_apply (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M) :
    (pullbackLM e T).toLinearMap ρ = T.toLinearMap (densityPullback e.symm ρ) := rfl

/-- The intrinsic reparametrization of scalar distributions is a linear equivalence. -/
def pullback (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) :
    ScalarCurveDistribution 𝕜 N ≃ₗ[𝕜] ScalarCurveDistribution 𝕜 M where
  toLinearMap := pullbackLM e
  invFun := pullbackLM e.symm
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro ρ
    change T.toLinearMap (densityPullback e.symm (densityPullback e ρ)) = T.toLinearMap ρ
    rw [densityPullback_symm_apply]
  right_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro ρ
    change T.toLinearMap (densityPullback e (densityPullback e.symm ρ)) = T.toLinearMap ρ
    have h := densityPullback_symm_apply e.symm ρ
    exact congrArg T.toLinearMap h

lemma pullback_inChart (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (c : SmoothChart M)
    (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    (pullback e T).inChart c φ = T.inChart (c.pullback e.symm) φ := by
  change T.toLinearMap (densityPullback e.symm (chartTestDensity 𝕜 c φ)) =
    T.toLinearMap (chartTestDensity 𝕜 (c.pullback e.symm) φ)
  exact congrArg T.toLinearMap (congrArg (fun L => L φ) (densityPullback_chart e.symm c))

lemma inChart_congr (T : ScalarCurveDistribution 𝕜 M) {c d : SmoothChart M}
    (h : c = d) (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤)
    (ψ : TestFunction ⟨d.val.target, d.val.open_target⟩ 𝕜 ⊤)
    (hφ : ∀ y, φ y = ψ y) : T.inChart c φ = T.inChart d ψ := by
  subst d
  have htest : φ = ψ := TestFunction.ext hφ
  rw [htest]

lemma localize_congr (T : ScalarCurveDistribution 𝕜 M) {c d : SmoothChart M}
    (h : c = d) (a : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤)
    (b : TestFunction ⟨d.val.target, d.val.open_target⟩ 𝕜 ⊤)
    (hab : ∀ y, a y = b y) : T.localize c a = T.localize d b := by
  subst d
  have htest : a = b := TestFunction.ext hab
  rw [htest]

lemma pullback_transported_inChart (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (c : SmoothChart N)
    (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    (pullback e T).inChart (c.pullback e) φ = T.inChart c φ := by
  refine (pullback_inChart e T (c.pullback e) φ).trans ?_
  have h : (c.pullback e).pullback e.symm = c := c.pullback_symm e
  exact inChart_congr T h φ φ (fun _ => rfl)

lemma pullback_localize (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (c : SmoothChart N)
    (a : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    (pullback e T).localize (c.pullback e) a = T.localize c a := by
  ext φ
  exact pullback_transported_inChart e T c (schwartzCutoffToTest _ a φ)

/-- In pointwise density gauges, scalar pullback transposes the inverse absolute Jacobian. -/
lemma pullback_density_pairing (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M) :
    (pullback e T).toLinearMap ρ = T.toLinearMap (densityPullback e.symm ρ) ∧
      ∀ y, (densityPullback e.symm ρ).val y =
        (SmoothChart.mapJacobian e (e.symm y))⁻¹ • ρ.val (e.symm y) := by
  refine ⟨rfl, ?_⟩
  intro y
  rw [densityPullback_apply, SmoothChart.mapJacobian_symm]

/-- On regular chart representatives, intrinsic reparametrization is scalar composition. -/
lemma pullback_regular_inChart (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (T : ScalarCurveDistribution 𝕜 N) (c : SmoothChart N) (f : N → 𝕜)
    (hT : ∀ φ, T.inChart c φ = ∫ y, f (c.val.symm y) * φ y)
    (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    (pullback e T).inChart (c.pullback e) φ =
      ∫ y, (f ∘ e) ((c.pullback e).val.symm y) * φ y := by
  rw [pullback_transported_inChart, hT]
  congr 1
  funext y
  change f (c.val.symm y) * φ y = f (e (e.symm (c.val.symm y))) * φ y
  rw [e.apply_symm_apply]

end ScalarCurveDistribution

lemma partitionSmoothChart_pullback (A : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (i : Fin A.n) :
    (⟨(A.pullback e).chart i, (A.pullback e).chart_smooth i⟩ : SmoothChart M) =
      (⟨A.chart i, A.chart_smooth i⟩ : SmoothChart N).pullback e := by
  apply SmoothChart.eq_of_val_eq
  exact (Homeomorph.transOpenPartialHomeomorph_eq_trans e.toHomeomorph (A.chart i)).symm

/-- Reparametrization preserves each actual localized tempered distribution
when the finite chart partition is transported with the diffeomorphism. -/
lemma partitionDistribution_pullback [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (T : ScalarCurveDistribution 𝕜 N)
    (A : FiniteChartPartition N) (i : Fin A.n) :
    partitionDistribution (ScalarCurveDistribution.pullback e T) (A.pullback e) i =
      partitionDistribution T A i := by
  let c : SmoothChart N := ⟨A.chart i, A.chart_smooth i⟩
  change (ScalarCurveDistribution.pullback e T).localize
    (⟨(A.pullback e).chart i, (A.pullback e).chart_smooth i⟩ : SmoothChart M)
      (chartCutoffTest (𝕜 := 𝕜) (A.pullback e) i) = T.localize c (chartCutoffTest A i)
  calc
    _ = (ScalarCurveDistribution.pullback e T).localize (c.pullback e) (chartCutoffTest A i) := by
      apply ScalarCurveDistribution.localize_congr _ (partitionSmoothChart_pullback A e i)
      intro y
      exact congrFun (FiniteChartPartition.pullback_localFunction (𝕜 := 𝕜) A e (fun _ => 1) i) y
    _ = _ := ScalarCurveDistribution.pullback_localize e T c (chartCutoffTest A i)

/-- Actual intrinsic scalar reparametrization, specified by its full density transpose. -/
theorem curve_distribution_reparametrization :
    ∀ (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N),
    ∃ (D : TestDensities 𝕜 M ≃ₗ[𝕜] TestDensities 𝕜 N)
      (P : ScalarCurveDistribution 𝕜 N ≃ₗ[𝕜] ScalarCurveDistribution 𝕜 M),
      (∀ (ρ : TestDensities 𝕜 M) (y : N), (D ρ).val y =
        |deriv (fun z : ℝ => (chartAt ℝ (e.symm y))
          (e.symm ((chartAt ℝ y).symm z))) ((chartAt ℝ y) y)| • ρ.val (e.symm y)) ∧
      (∀ (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M),
        (P T).toLinearMap ρ = T.toLinearMap (D ρ)) := by
  intro e
  refine ⟨densityPullbackEquiv e.symm, ScalarCurveDistribution.pullback e, ?_, ?_⟩
  · intro ρ y
    exact congrArg (fun r : ℝ => r • ρ.val (e.symm y)) (SmoothChart.mapJacobian_eq_deriv e.symm y)
  · intro T ρ
    rfl

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

/-- Actual Euclidean Hs realization, tested in line coordinates. -/
def lineHsRealization (s : ℝ) : Hs 1 s →ₗ[ℂ] (SchwartzMap ℝ ℂ →L[ℂ] ℂ) where
  toFun u := (realization (s := s) u).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ realLineIsometry.symm.toContinuousLinearEquiv)
  map_add' u v := by
    ext φ
    change realization (s := s) (u+v) (lineSchwartzToEuclidean φ) = _
    rw [(realization_linear 1 s).1]
    rfl
  map_smul' c u := by
    ext φ
    change realization (s := s) (c • u) (lineSchwartzToEuclidean φ) = _
    rw [(realization_linear 1 s).2]
    rfl

@[simp] lemma lineHsRealization_apply (s : ℝ) (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ) :
    lineHsRealization s u φ = realization (s := s) u (lineSchwartzToEuclidean φ) := rfl

lemma lineHsRealization_injective (s : ℝ) : Function.Injective (lineHsRealization s) := by
  intro u v h
  apply realization_injective 1 s
  ext Φ
  obtain ⟨φ, rfl⟩ := lineSchwartzToEuclidean_surjective Φ
  exact congrArg (fun T : SchwartzMap ℝ ℂ →L[ℂ] ℂ => T φ) h

/-- Actual canonical real Hs realization, tested in line coordinates. -/
def lineRealHsRealization (s : ℝ) : RealHs 1 s →ₗ[ℝ] (SchwartzMap ℝ ℝ →L[ℝ] ℝ) where
  toFun u := (realRealization (s := s) u).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ realLineIsometry.symm.toContinuousLinearEquiv)
  map_add' u v := by
    ext φ
    change realRealization (s := s) (u+v) (lineRealSchwartzToEuclidean φ) = _
    rw [real_realization_add]
    rfl
  map_smul' c u := by
    ext φ
    change realRealization (s := s) (c • u) (lineRealSchwartzToEuclidean φ) = _
    rw [real_realization_smul]
    rfl

@[simp] lemma lineRealHsRealization_apply (s : ℝ) (u : RealHs 1 s) (φ : SchwartzMap ℝ ℝ) :
    lineRealHsRealization s u φ = realRealization (s := s) u (lineRealSchwartzToEuclidean φ) := rfl

lemma lineRealHsRealization_injective (s : ℝ) : Function.Injective (lineRealHsRealization s) := by
  intro u v h
  apply real_realization_injective 1 s
  ext Φ
  obtain ⟨φ, rfl⟩ := lineRealSchwartzToEuclidean_surjective Φ
  exact congrArg (fun T : SchwartzMap ℝ ℝ →L[ℝ] ℝ => T φ) h

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Finite matrix assembly, retaining the actual synthesized distribution.
Its local premise is discharged below by the proved all-order coordinate theorem. -/
theorem partitionScaleMap_exists
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (hloc : ∀ (e : OpenPartialHomeomorph ℝ ℝ),
      ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
      ∀ a : ℝ → 𝕜, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
      ∃ (D : H →L[𝕜] H) (Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜),
        (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
        ∀ u φ, R (D u) φ = R u (Q φ))
    (A B : FiniteChartPartition M) :
    ∃ K : PiLp 2 (fun _ : Fin A.n => H) →L[𝕜] PiLp 2 (fun _ : Fin B.n => H),
      ∀ v j φ, R ((K v) j) φ =
        partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ := by
  have hentry : ∀ (j : Fin B.n) (i : Fin A.n),
      ∃ (D : H →L[𝕜] H) (Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜),
        (∀ φ y, Q φ y = localizedDensity (B.transition A j i)
          (chartSynthesisCoefficient B j (partitionReconstructionCutoff A i)) φ y) ∧
        ∀ u φ, R (D u) φ = R u (Q φ) := by
    intro j i
    let a := chartSynthesisCoefficient (𝕜 := 𝕜) B j (partitionReconstructionCutoff A i)
    exact hloc (B.transition A j i) (B.transition_smooth A j i) (B.transition_symm_smooth A j i)
      a a.contDiff a.hasCompactSupport
      (chartSynthesisCoefficient_support B j ⟨A.chart i, A.chart_smooth i⟩
        (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i))
  choose D Q hQ hD using hentry
  let T : (Fin A.n → H) →L[𝕜] (Fin B.n → H) :=
    ContinuousLinearMap.pi (fun j => ∑ i, (D j i).comp (ContinuousLinearMap.proj i))
  let EA := PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin A.n => H)
  let EB := PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin B.n => H)
  let K := EB.symm.toContinuousLinearMap.comp (T.comp EA.toContinuousLinearMap)
  have hK : ∀ v j, (K v) j = ∑ i, D j i (v i) := by
    intro v j
    simp [K, T, EA, EB]
  refine ⟨K, ?_⟩
  intro v j φ
  rw [hK, map_sum]
  simp only [sum_apply]
  simp_rw [hD]
  rw [partitionDistribution, partitionSynthesis_localize]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (R (v i))
  ext y
  rw [hQ]
  exact (densityCoefficient_localization B j ⟨A.chart i, A.chart_smooth i⟩
    (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i) φ y).symm

/-- The genuine bounded chart synthesis/localization matrix for complex Hs,
at every real order. -/
theorem partitionHsMap_exists (s : ℝ) (A B : FiniteChartPartition M) :
    ∃ K : PiLp 2 (fun _ : Fin A.n => Hs 1 s) →L[ℂ] PiLp 2 (fun _ : Fin B.n => Hs 1 s),
      ∀ v j φ, realization (s := s) ((K v) j) (lineSchwartzToEuclidean φ) =
        partitionDistribution (partitionSynthesis A (fun i => lineHsRealization s (v i))) B j φ := by
  apply partitionScaleMap_exists (lineHsRealization s) ?_ A B
  intro e he hi a ha hc hs
  obtain ⟨P, Q, D, C, hC, hDC, hP, hQ, hreg, hpair⟩ :=
    localizedPullback_all_real_Hs_bound s e he hi a ha hc hs
  exact ⟨D, Q, hQ, hpair⟩

/-- The same actual bounded matrix for the canonical real Hs scale. -/
theorem partitionRealHsMap_exists (s : ℝ) (A B : FiniteChartPartition M) :
    ∃ K : PiLp 2 (fun _ : Fin A.n => RealHs 1 s) →L[ℝ] PiLp 2 (fun _ : Fin B.n => RealHs 1 s),
      ∀ v j φ, realRealization (s := s) ((K v) j) (lineRealSchwartzToEuclidean φ) =
        partitionDistribution (partitionSynthesis A (fun i => lineRealHsRealization s (v i))) B j φ := by
  apply partitionScaleMap_exists (lineRealHsRealization s) ?_ A B
  intro e he hi a ha hc hs
  obtain ⟨P, Q, D, C, hC, hDC, hP, hQ, hreg, hpair⟩ :=
    localizedPullback_real_Hs_bound s e he hi a ha hc hs
  exact ⟨D, Q, hQ, hpair⟩

end ExpandedFA.Sobolev.Curve


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve

theorem density_coefficient_schwartz_continuity :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.densityCoefficientSchwartzContinuityType := by
  intro M _ _ _ 𝕜 _ e ρ hρ
  exact ⟨densityCoefficientLM e ρ hρ, densityCoefficientSchwartzLM e ρ hρ,
    densityCoefficient_spec e ρ hρ, fun _ _ => rfl,
    fun f => continuous_densityCoefficientSchwartz_chart e f ρ hρ⟩

theorem finite_density_reconstruction :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteDensityReconstructionType := by
  intro M _ _ _ 𝕜 _ A
  let R := fun i : Fin A.n => densityCoefficientLM (𝕜 := 𝕜)
    ⟨A.chart i, A.chart_smooth i⟩ (A.cutoff i) (A.subordinate i)
  have hR : ∀ i d, chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩ (R i d) =
      fun x => A.cutoff i x • d.val x := by
    intro i d
    exact densityCoefficient_spec _ _ (A.subordinate i) d
  refine ⟨R, hR, fun d => ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  ext x
  simp only [Finset.sum_apply]
  change (∑ i, chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩ (R i d) x) = d.val x
  simp_rw [hR]
  rw [← Finset.sum_smul, A.sum_one x, one_smul]

theorem finite_distribution_synthesis :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteDistributionSynthesisType := by
  intro M _ _ _ _ _ 𝕜 _ A
  refine ⟨partitionReconstructionCutoff A, partitionDensityCoefficient A,
    partitionDensitySchwartzLM A, partitionLocalizationLM A, partitionSynthesisLM A,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨partitionReconstructionCutoff_support A i,
      fun x hx => partitionReconstructionCutoff_eq_one A i hx⟩
  · exact partitionDensityCoefficient_spec A
  · intro i d y
    rfl
  · intro i f
    exact continuous_densityCoefficientSchwartz_chart
      ⟨A.chart i, A.chart_smooth i⟩ f (partitionReconstructionCutoff A i)
      (partitionReconstructionCutoff_support A i)
  · intro T i φ ψ hψ
    change T.inChart ⟨A.chart i, A.chart_smooth i⟩
      (schwartzCutoffToTest _ (chartCutoffTest A i) φ) = _
    congr 1
    apply TestFunction.ext
    intro y
    rw [schwartzCutoffToTest_apply, hψ]
    rfl
  · exact partitionSynthesis_apply A
  · exact partitionSynthesis_partitionLocalization A

theorem finite_distribution_faithfulness :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.finiteDistributionFaithfulnessType := by
  intro M _ _ _ _ _ 𝕜 _ A T S h
  apply ScalarCurveDistribution.ext_partitionDistribution A
  intro i
  apply ContinuousLinearMap.ext
  intro φ
  apply h i φ (schwartzCutoffToTest _ (chartCutoffTest A i) φ)
  intro y
  rw [schwartzCutoffToTest_apply]
  rfl

end ExpandedFA.Sobolev.Curve

namespace ExpandedFA.Sobolev.Curve
theorem curve_distribution_reparametrization_spec :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveDistributionReparametrizationType := by
  intro M _ _ _ N _ _ _ 𝕜 _ e
  exact curve_distribution_reparametrization e
end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace ExpandedFA.Sobolev.ProjectionModel

variable {𝕜 E F D R S : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [AddCommGroup D] [Module 𝕜 D]
  [AddCommGroup R] [Module 𝕜 R]
  [AddCommGroup S] [Module 𝕜 S]

/-- The closed Hilbert subspace on which a continuous linear projection is the identity. -/
def fixedSpace (P : E →L[𝕜] E) : Submodule 𝕜 E :=
  (P - ContinuousLinearMap.id 𝕜 E).toLinearMap.ker

@[simp] theorem mem_fixedSpace (P : E →L[𝕜] E) (x : E) :
    x ∈ fixedSpace P ↔ P x = x := by
  change P x - x = 0 ↔ P x = x
  exact sub_eq_zero

theorem fixedSpace_closed (P : E →L[𝕜] E) : IsClosed (fixedSpace P : Set E) :=
  (P - ContinuousLinearMap.id 𝕜 E).isClosed_ker

instance fixedSpace_completeSpace (P : E →L[𝕜] E) : CompleteSpace (fixedSpace P) :=
  (fixedSpace_closed P).completeSpace_coe

/-- The fixed subspace is exactly the image of an idempotent continuous linear map. -/
theorem fixedSpace_eq_range (P : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x) :
    (fixedSpace P : Set E) = Set.range P := by
  ext x
  constructor
  · intro hx
    exact ⟨x, (mem_fixedSpace P x).mp hx⟩
  · rintro ⟨x, rfl⟩
    exact (mem_fixedSpace P (P x)).mpr (hP x)

/-- A realization is injective on fixed tuples whenever a faithful localizer
recovers the coordinates of the projection. -/
theorem injective_restriction
    (P : E →L[𝕜] E) (U : E →ₗ[𝕜] D)
    (rE : E →ₗ[𝕜] R) (L : D →ₗ[𝕜] R)
    (hrE : Function.Injective rE) (hcompat : ∀ x, rE (P x) = L (U x)) :
    Function.Injective (U.comp (fixedSpace P).subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply hrE
  have hx := (mem_fixedSpace P (x : E)).mp x.property
  have hy := (mem_fixedSpace P (y : E)).mp y.property
  have h := congrArg L hxy
  change L (U (x : E)) = L (U (y : E)) at h
  simpa only [← hcompat, hx, hy] using h

/-- Projection idempotence follows from exact reconstruction of distributions
and injectivity of the coordinate realization. -/
theorem idempotent_of_reconstruction
    (P : E →L[𝕜] E) (rE : E →ₗ[𝕜] R)
    (L : D →ₗ[𝕜] R) (G : R →ₗ[𝕜] D)
    (hrE : Function.Injective rE) (hrec : ∀ T, G (L T) = T)
    (hcompat : ∀ x, rE (P x) = L (G (rE x))) :
    (∀ x, G (rE (P x)) = G (rE x)) ∧ (∀ x, P (P x) = P x) := by
  have hU : ∀ x, G (rE (P x)) = G (rE x) := by
    intro x
    rw [hcompat, hrec]
  refine ⟨hU, fun x => hrE ?_⟩
  rw [hcompat, hU, ← hcompat]

/-- Exact distribution image of the fixed Hilbert subspace. -/
theorem exact_image
    (P : E →L[𝕜] E) (rE : E →ₗ[𝕜] R)
    (L : D →ₗ[𝕜] R) (G : R →ₗ[𝕜] D)
    (hrE : Function.Injective rE) (hrec : ∀ T, G (L T) = T)
    (hcompat : ∀ x, rE (P x) = L (G (rE x))) (T : D) :
    (∃ x : fixedSpace P, G (rE x.val) = T) ↔ ∃ x : E, rE x = L T := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.val, ?_⟩
    have hfixed := (mem_fixedSpace P x.val).mp x.property
    rw [← hfixed, hcompat, hx]
  · rintro ⟨x, hx⟩
    have hreal : G (rE x) = T := by rw [hx, hrec]
    have hfixed : P x = x := by
      apply hrE
      rw [hcompat, hreal, hx]
    exact ⟨⟨x, (mem_fixedSpace P x).mpr hfixed⟩, hreal⟩

/-- A coordinate transition sends a fixed tuple to a fixed tuple when its
realization agrees with the source distribution. -/
theorem transition_mem_fixedSpace
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F) (K : E →L[𝕜] F)
    (rE : E →ₗ[𝕜] R) (rF : F →ₗ[𝕜] S)
    (L : D →ₗ[𝕜] R) (N : D →ₗ[𝕜] S)
    (G : R →ₗ[𝕜] D) (H : S →ₗ[𝕜] D)
    (hrF : Function.Injective rF) (hrec : ∀ T, H (N T) = T)
    (hQ : ∀ y, rF (Q y) = N (H (rF y)))
    (hK : ∀ x, rF (K x) = N (G (rE x))) (x : E) :
    K x ∈ fixedSpace Q := by
  apply (mem_fixedSpace Q (K x)).mpr
  apply hrF
  rw [hQ, hK, hrec]

/-- Restrict bounded coordinate maps to closed fixed subspaces. -/
def fixedSpaceMap (P : E →L[𝕜] E) (Q : F →L[𝕜] F) (K : E →L[𝕜] F)
    (hK : ∀ x ∈ fixedSpace P, K x ∈ fixedSpace Q) :
    fixedSpace P →L[𝕜] fixedSpace Q := K.restrict hK

@[simp] theorem fixedSpaceMap_apply
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F) (K : E →L[𝕜] F)
    (hK : ∀ x ∈ fixedSpace P, K x ∈ fixedSpace Q) (x : fixedSpace P) :
    (fixedSpaceMap P Q K hK x : F) = K x := rfl

/-- Two bounded coordinate transitions which preserve a faithful realization
are inverse continuous linear equivalences of the closed Hilbert models. -/
def fixedSpaceEquiv
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F)
    (K : fixedSpace P →L[𝕜] fixedSpace Q)
    (J : fixedSpace Q →L[𝕜] fixedSpace P)
    (U : fixedSpace P →ₗ[𝕜] D) (V : fixedSpace Q →ₗ[𝕜] D)
    (hU : Function.Injective U) (hV : Function.Injective V)
    (hK : ∀ x, V (K x) = U x) (hJ : ∀ y, U (J y) = V y) :
    fixedSpace P ≃L[𝕜] fixedSpace Q where
  toLinearEquiv :=
    { toLinearMap := K.toLinearMap
      invFun := J
      left_inv := fun x => hU (by change U (J (K x)) = U x; rw [hJ, hK])
      right_inv := fun y => hV (by change V (K (J y)) = V y; rw [hK, hJ]) }
  continuous_toFun := K.continuous
  continuous_invFun := J.continuous

/-- One common constant controls the atlas map and its inverse. -/
theorem equiv_two_sided_bound
    (P : E →L[𝕜] E) (Q : F →L[𝕜] F) (e : fixedSpace P ≃L[𝕜] fixedSpace Q) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ x, ‖e x‖ ≤ C * ‖x‖) ∧
      ∀ y, ‖e.symm y‖ ≤ C * ‖y‖ := by
  refine ⟨max 1 (max ‖e.toContinuousLinearMap‖ ‖e.symm.toContinuousLinearMap‖),
    le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg x))
  · intro y
    exact (e.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg y))

end ExpandedFA.Sobolev.ProjectionModel


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Sobolev.ProjectionModel
universe uh
variable {M : Type uh} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The finite square-sum Hilbert space of local representatives. -/
abbrev CurveScaleTuples (H : Type*) [NormedAddCommGroup H]
    (A : FiniteChartPartition M) := PiLp 2 (fun _ : Fin A.n => H)

/-- Coordinate realization of a finite Hilbert tuple as actual tempered distributions. -/
def curveScaleTupleRealizationLM (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (A : FiniteChartPartition M) :
    CurveScaleTuples H A →ₗ[𝕜] (Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) where
  toFun v := fun i => R (v i)
  map_add' v w := by ext i φ; simp
  map_smul' c v := by ext i φ; simp

/-- The actual intrinsic distribution synthesized from a Hilbert tuple. -/
def curveScaleSynthesisLM (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (A : FiniteChartPartition M) : CurveScaleTuples H A →ₗ[𝕜] ScalarCurveDistribution 𝕜 M :=
  (partitionSynthesisLM A).comp (curveScaleTupleRealizationLM R A)

/-- The global Hilbert model is the closed fixed subspace of the localization-synthesis matrix. -/
def curveScaleModel
    (K : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
    (A : FiniteChartPartition M) : Submodule 𝕜 (CurveScaleTuples H A) := fixedSpace (K A A)

instance curveScaleModel_completeSpace
    (K : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
    (A : FiniteChartPartition M) : CompleteSpace (curveScaleModel K A) :=
  inferInstanceAs (CompleteSpace (fixedSpace (K A A)))

/-- Faithful distribution realization of the closed Hilbert model. -/
def curveScaleRealization
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (K : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
    (A : FiniteChartPartition M) : curveScaleModel K A →ₗ[𝕜] ScalarCurveDistribution 𝕜 M :=
  (curveScaleSynthesisLM R A).comp (curveScaleModel K A).subtype

variable (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
  (K : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
  (hR : Function.Injective R)
  (hK : ∀ A B (v : CurveScaleTuples H A) j φ,
    R ((K A B v) j) φ =
      partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)

include hR hK

/-- Coordinate matrices preserve the synthesized intrinsic distribution. -/
lemma curveScaleMap_synthesis (A B : FiniteChartPartition M) (v : CurveScaleTuples H A) :
    curveScaleSynthesisLM R B (K A B v) = curveScaleSynthesisLM R A v := by
  change partitionSynthesis B (fun j => R ((K A B v) j)) =
    partitionSynthesis A (fun i => R (v i))
  have heq : (fun j => R ((K A B v) j)) =
      partitionLocalizationLM B (partitionSynthesis A (fun i => R (v i))) := by
    funext j
    ext φ
    exact hK A B v j φ
  rw [heq]
  exact partitionSynthesis_partitionLocalization B _

/-- The localization-synthesis diagonal matrix is idempotent. -/
lemma curveScaleMap_idempotent (A : FiniteChartPartition M) (v : CurveScaleTuples H A) :
    K A A (K A A v) = K A A v := by
  apply PiLp.ext
  intro i
  apply hR
  ext φ
  rw [hK, hK]
  change partitionDistribution (curveScaleSynthesisLM R A (K A A v)) A i φ =
    partitionDistribution (curveScaleSynthesisLM R A v) A i φ
  rw [curveScaleMap_synthesis R K hR hK]

/-- Every transition matrix lands in the closed target model. -/
lemma curveScaleMap_mem (A B : FiniteChartPartition M) (v : CurveScaleTuples H A) :
    K A B v ∈ curveScaleModel K B := by
  apply (mem_fixedSpace (K B B) (K A B v)).mpr
  apply PiLp.ext
  intro j
  apply hR
  ext φ
  rw [hK, hK]
  change partitionDistribution (curveScaleSynthesisLM R B (K A B v)) B j φ =
    partitionDistribution (curveScaleSynthesisLM R A v) B j φ
  rw [curveScaleMap_synthesis R K hR hK]

/-- The fixed coordinates are exactly the chart localizations of the realized distribution. -/
lemma curveScaleRealization_localization (A : FiniteChartPartition M)
    (v : curveScaleModel K A) (i : Fin A.n) :
    R ((v : CurveScaleTuples H A) i) =
      partitionDistribution (curveScaleRealization R K A v) A i := by
  ext φ
  have hv : K A A v.val = v.val := (mem_fixedSpace (K A A) v.val).mp v.property
  have h := hK A A v.val i φ
  rw [hv] at h
  exact h

/-- Distinct global Hilbert elements give distinct actual scalar distributions. -/
lemma curveScaleRealization_injective (A : FiniteChartPartition M) :
    Function.Injective (curveScaleRealization R K A) := by
  intro u v huv
  apply Subtype.ext
  apply PiLp.ext
  intro i
  apply hR
  rw [curveScaleRealization_localization R K hR hK, curveScaleRealization_localization R K hR hK, huv]

/-- Exact distribution membership: every finite chart localization must have
an actual representative in the original Hilbert scale, and this condition suffices. -/
theorem curveScaleRealization_exact_image (A : FiniteChartPartition M)
    (T : ScalarCurveDistribution 𝕜 M) :
    (∃ v : curveScaleModel K A, curveScaleRealization R K A v = T) ↔
      ∀ i : Fin A.n, ∃ u : H, R u = partitionDistribution T A i := by
  constructor
  · rintro ⟨v, rfl⟩ i
    exact ⟨v.val i, curveScaleRealization_localization R K hR hK A v i⟩
  · intro hT
    choose u hu using hT
    let v : CurveScaleTuples H A := WithLp.toLp 2 u
    have hvT : curveScaleSynthesisLM R A v = T := by
      change partitionSynthesis A (fun i => R (v i)) = T
      have heq : (fun i => R (v i)) = partitionLocalizationLM A T := by
        funext i
        exact hu i
      rw [heq]
      exact partitionSynthesis_partitionLocalization A T
    have hvfixed : K A A v = v := by
      apply PiLp.ext
      intro i
      apply hR
      ext φ
      rw [hK]
      change partitionDistribution (curveScaleSynthesisLM R A v) A i φ = R (u i) φ
      rw [hvT, hu]
    exact ⟨⟨v, (mem_fixedSpace (K A A) v).mpr hvfixed⟩, hvT⟩

/-- The closed tuple subspace is canonically characterized by actual distribution
compatibility, independently of the auxiliary projection choice. -/
theorem curveScaleModel_mem_iff (A : FiniteChartPartition M) (v : CurveScaleTuples H A) :
    v ∈ curveScaleModel K A ↔ ∃ T : ScalarCurveDistribution 𝕜 M,
      ∀ i : Fin A.n, R (v i) = partitionDistribution T A i := by
  constructor
  · intro hv
    exact ⟨curveScaleRealization R K A ⟨v, hv⟩,
      curveScaleRealization_localization R K hR hK A ⟨v, hv⟩⟩
  · rintro ⟨T, hv⟩
    apply (mem_fixedSpace (K A A) v).mpr
    have hreal : curveScaleSynthesisLM R A v = T := by
      change partitionSynthesis A (fun i => R (v i)) = T
      have heq : (fun i => R (v i)) = partitionLocalizationLM A T := funext hv
      rw [heq]
      exact partitionSynthesis_partitionLocalization A T
    apply PiLp.ext
    intro i
    apply hR
    ext φ
    rw [hK]
    change partitionDistribution (curveScaleSynthesisLM R A v) A i φ = R (v i) φ
    rw [hreal, hv]

omit hR hK
/-- The inherited Hilbert norm is exactly the finite chart square-sum norm. -/
theorem curveScaleModel_norm_sq (A : FiniteChartPartition M) (v : curveScaleModel K A) :
    ‖v‖^2 = ∑ i : Fin A.n, ‖(v : CurveScaleTuples H A) i‖^2 :=
  PiLp.norm_sq_eq_of_L2 _ v.val

include hR hK

/-- The bounded atlas transition on the actual closed curve Hilbert models. -/
def curveScaleAtlasMap (A B : FiniteChartPartition M) :
    curveScaleModel K A →L[𝕜] curveScaleModel K B :=
  (K A B).restrict (fun v _ => curveScaleMap_mem R K hR hK A B v)

lemma curveScaleAtlasMap_realization (A B : FiniteChartPartition M)
    (v : curveScaleModel K A) :
    curveScaleRealization R K B (curveScaleAtlasMap R K hR hK A B v) =
      curveScaleRealization R K A v :=
  curveScaleMap_synthesis R K hR hK A B v.val

/-- Atlas independence as a continuous linear equivalence preserving the
same actual scalar distribution. -/
def curveScaleAtlasEquiv (A B : FiniteChartPartition M) :
    curveScaleModel K A ≃L[𝕜] curveScaleModel K B :=
  fixedSpaceEquiv (K A A) (K B B)
    (curveScaleAtlasMap R K hR hK A B) (curveScaleAtlasMap R K hR hK B A)
    (curveScaleRealization R K A) (curveScaleRealization R K B)
    (curveScaleRealization_injective R K hR hK A)
    (curveScaleRealization_injective R K hR hK B)
    (curveScaleAtlasMap_realization R K hR hK A B)
    (curveScaleAtlasMap_realization R K hR hK B A)

@[simp] lemma curveScaleAtlasEquiv_realization (A B : FiniteChartPartition M)
    (v : curveScaleModel K A) :
    curveScaleRealization R K B (curveScaleAtlasEquiv R K hR hK A B v) =
      curveScaleRealization R K A v :=
  curveScaleAtlasMap_realization R K hR hK A B v

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Sobolev.ProjectionModel
open ExpandedFA.Sobolev.FourierScale
universe ui
variable {M : Type ui} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {𝕜 H : Type} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Equality with a compact chart localization, expressed independently through
all native chart test coefficients with their prescribed pointwise values. -/
lemma eq_partitionDistribution_iff (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (A : FiniteChartPartition M) (u : H) (T : ScalarCurveDistribution 𝕜 M) (i : Fin A.n) :
    R u = partitionDistribution T A i ↔
      ∀ (φ : SchwartzMap ℝ 𝕜)
        (ψ : TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤),
        (∀ y, ψ y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y * φ y) →
        R u φ = T.inChart ⟨A.chart i, A.chart_smooth i⟩ ψ := by
  constructor
  · intro h φ ψ hψ
    have heq : ψ = schwartzCutoffToTest _ (chartCutoffTest A i) φ := by
      ext y
      rw [hψ, schwartzCutoffToTest_apply]
      rfl
    rw [heq, h]
    rfl
  · intro h
    ext φ
    exact h φ (schwartzCutoffToTest _ (chartCutoffTest A i) φ)
      (fun y => schwartzCutoffToTest_apply _ _ _ _)

/-- The constructed closed model has exactly the independent source presentation:
actual density testing, exact distribution image and the chart square-sum norm. -/
theorem curveScalePresentation_proved
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (K : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
    (hR : Function.Injective R)
    (hK : ∀ A B (v : CurveScaleTuples H A) j φ,
      R ((K A B v) j) φ =
        partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)
    (A : FiniteChartPartition M) :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.CurveScalePresentation
      (fun u φ => R u φ) A (curveScaleModel K A) (curveScaleRealization R K A) := by
  refine ⟨fixedSpace_closed (K A A), inferInstance,
    curveScaleRealization_injective R K hR hK A, ?_, ?_, curveScaleModel_norm_sq K A⟩
  · intro u i
    exact (eq_partitionDistribution_iff R A _ _ i).mp
      (curveScaleRealization_localization R K hR hK A u i)
  · intro T
    rw [curveScaleRealization_exact_image R K hR hK A T]
    constructor
    · intro h i
      obtain ⟨u, hu⟩ := h i
      exact ⟨u, (eq_partitionDistribution_iff R A u T i).mp hu⟩
    · intro h i
      obtain ⟨u, hu⟩ := h i
      exact ⟨u, (eq_partitionDistribution_iff R A u T i).mpr hu⟩

/-- Choice of the proved bounded chart matrix for the actual complex Fourier scale. -/
def curveHsMatrix (s : ℝ) (A B : FiniteChartPartition M) :
    CurveScaleTuples (Hs 1 s) A →L[ℂ] CurveScaleTuples (Hs 1 s) B :=
  Classical.choose (partitionHsMap_exists s A B)

lemma curveHsMatrix_spec (s : ℝ) (A B : FiniteChartPartition M)
    (v : CurveScaleTuples (Hs 1 s) A) (j : Fin B.n) (φ : SchwartzMap ℝ ℂ) :
    lineHsRealization s ((curveHsMatrix s A B v) j) φ =
      partitionDistribution (partitionSynthesis A (fun i => lineHsRealization s (v i))) B j φ :=
  Classical.choose_spec (partitionHsMap_exists s A B) v j φ

/-- Choice of the proved bounded chart matrix for the actual canonical real scale. -/
def curveRealHsMatrix (s : ℝ) (A B : FiniteChartPartition M) :
    CurveScaleTuples (RealHs 1 s) A →L[ℝ] CurveScaleTuples (RealHs 1 s) B :=
  Classical.choose (partitionRealHsMap_exists s A B)

lemma curveRealHsMatrix_spec (s : ℝ) (A B : FiniteChartPartition M)
    (v : CurveScaleTuples (RealHs 1 s) A) (j : Fin B.n) (φ : SchwartzMap ℝ ℝ) :
    lineRealHsRealization s ((curveRealHsMatrix s A B v) j) φ =
      partitionDistribution (partitionSynthesis A (fun i => lineRealHsRealization s (v i))) B j φ :=
  Classical.choose_spec (partitionRealHsMap_exists s A B) v j φ

/-- Global complex curve Hilbert scales, with exact membership and all-order
atlas equivalences preserving the same intrinsic scalar distribution. -/
theorem curve_hilbert_atlas :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveHilbertAtlasType := by
  intro s M _ _ _ _ _
  let K := curveHsMatrix (M := M) s
  let R := lineHsRealization s
  have hR := lineHsRealization_injective s
  have hK := curveHsMatrix_spec (M := M) s
  refine ⟨curveScaleModel K, curveScaleRealization R K, ?_, ?_⟩
  · intro A
    exact curveScalePresentation_proved R K hR hK A
  · intro A B
    let E := curveScaleAtlasEquiv R K hR hK A B
    refine ⟨E, max 1 (max ‖E.toContinuousLinearMap‖ ‖E.symm.toContinuousLinearMap‖),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _), ?_⟩
    exact curveScaleAtlasEquiv_realization R K hR hK A B

/-- The same exact global Hilbert construction and atlas equivalences over the
canonical real Fourier Sobolev scale, for every real order. -/
theorem real_curve_hilbert_atlas :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realCurveHilbertAtlasType := by
  intro s M _ _ _ _ _
  let K := curveRealHsMatrix (M := M) s
  let R := lineRealHsRealization s
  have hR := lineRealHsRealization_injective s
  have hK := curveRealHsMatrix_spec (M := M) s
  refine ⟨curveScaleModel K, curveScaleRealization R K, ?_, ?_⟩
  · intro A
    exact curveScalePresentation_proved R K hR hK A
  · intro A B
    let E := curveScaleAtlasEquiv R K hR hK A B
    refine ⟨E, max 1 (max ‖E.toContinuousLinearMap‖ ‖E.symm.toContinuousLinearMap‖),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _), ?_⟩
    exact curveScaleAtlasEquiv_realization R K hR hK A B

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ℝ N]
  [IsManifold (𝓘(ℝ)) ∞ N] [T2Space N] [CompactSpace N]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Equality of actual coordinate compatibility subspaces in a transported atlas. -/
theorem partitionCompatibleSubmodule_pullback
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N)
    (P Q : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
    (hP : ∀ v, v ∈ P ↔ ∃ T : ScalarCurveDistribution 𝕜 N,
      ∀ i, R (v i) = partitionDistribution T A i)
    (hQ : ∀ v, v ∈ Q ↔ ∃ T : ScalarCurveDistribution 𝕜 M,
      ∀ i, R (v i) = partitionDistribution T (A.pullback e) i) : P = Q := by
  ext v
  constructor
  · intro hv
    obtain ⟨T, hT⟩ := (hP v).mp hv
    apply (hQ v).mpr
    refine ⟨ScalarCurveDistribution.pullback e T, fun i => ?_⟩
    rw [partitionDistribution_pullback]
    exact hT i
  · intro hv
    obtain ⟨T, hT⟩ := (hQ v).mp hv
    apply (hP v).mpr
    refine ⟨ScalarCurveDistribution.pullback e.symm T, fun i => ?_⟩
    have hinv : ScalarCurveDistribution.pullback e (ScalarCurveDistribution.pullback e.symm T) = T := by
      change (ScalarCurveDistribution.pullback e) ((ScalarCurveDistribution.pullback e).symm T) = T
      exact (ScalarCurveDistribution.pullback e).apply_symm_apply T
    have h := partitionDistribution_pullback e (ScalarCurveDistribution.pullback e.symm T) A i
    rw [hinv] at h
    exact (hT i).trans h

/-- Reparametrization is an exact isometry in the transported finite atlas. -/
def partitionCompatibleSubmoduleEquiv
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N)
    (P Q : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
    (hP : ∀ v, v ∈ P ↔ ∃ T : ScalarCurveDistribution 𝕜 N,
      ∀ i, R (v i) = partitionDistribution T A i)
    (hQ : ∀ v, v ∈ Q ↔ ∃ T : ScalarCurveDistribution 𝕜 M,
      ∀ i, R (v i) = partitionDistribution T (A.pullback e) i) : P ≃ₗᵢ[𝕜] Q :=
  LinearIsometryEquiv.ofEq P Q (partitionCompatibleSubmodule_pullback R e A P Q hP hQ)

/-- The transported isometry acts on the intrinsic distributions by the actual scalar pullback. -/
theorem partitionCompatibleSubmoduleEquiv_realization
    (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N)
    (P Q : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
    (hP : ∀ v, v ∈ P ↔ ∃ T : ScalarCurveDistribution 𝕜 N,
      ∀ i, R (v i) = partitionDistribution T A i)
    (hQ : ∀ v, v ∈ Q ↔ ∃ T : ScalarCurveDistribution 𝕜 M,
      ∀ i, R (v i) = partitionDistribution T (A.pullback e) i)
    (U : P →ₗ[𝕜] ScalarCurveDistribution 𝕜 N)
    (V : Q →ₗ[𝕜] ScalarCurveDistribution 𝕜 M)
    (hU : ∀ x i, partitionDistribution (U x) A i = R (x.val i))
    (hV : ∀ x i, partitionDistribution (V x) (A.pullback e) i = R (x.val i)) (x : P) :
    V (partitionCompatibleSubmoduleEquiv R e A P Q hP hQ x) =
      ScalarCurveDistribution.pullback e (U x) := by
  apply ScalarCurveDistribution.ext_partitionDistribution (A.pullback e)
  intro i
  rw [partitionDistribution_pullback, hV, hU]
  rfl

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ℝ N]
  [IsManifold (𝓘(ℝ)) ∞ N] [T2Space N] [CompactSpace N]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
  (KM : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
  (KN : ∀ A B : FiniteChartPartition N, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
  (hR : Function.Injective R)
  (hKM : ∀ A B (v : CurveScaleTuples H A) j φ,
    R ((KM A B v) j) φ = partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)
  (hKN : ∀ A B (v : CurveScaleTuples H A) j φ,
    R ((KN A B v) j) φ = partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)

/-- Smooth reparametrization is an exact isometry for transported finite chart norms. -/
def curveScaleTransportedEquiv (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N) :
    curveScaleModel KN A ≃ₗᵢ[𝕜] curveScaleModel KM (A.pullback e) :=
  partitionCompatibleSubmoduleEquiv R e A (curveScaleModel KN A)
    (curveScaleModel KM (A.pullback e))
    (curveScaleModel_mem_iff R KN hR hKN A)
    (curveScaleModel_mem_iff R KM hR hKM (A.pullback e))

lemma curveScaleTransportedEquiv_realization
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N)
    (v : curveScaleModel KN A) :
    curveScaleRealization R KM (A.pullback e) (curveScaleTransportedEquiv R KM KN hR hKM hKN e A v) =
      ScalarCurveDistribution.pullback e (curveScaleRealization R KN A v) := by
  apply ScalarCurveDistribution.ext_partitionDistribution (A.pullback e)
  intro i
  rw [partitionDistribution_pullback,
    ← curveScaleRealization_localization R KM hR hKM,
    ← curveScaleRealization_localization R KN hR hKN]
  rfl

/-- Smooth reparametrization on arbitrary finite atlas Hilbert models. -/
def curveScaleReparametrization (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (A : FiniteChartPartition N) (B : FiniteChartPartition M) :
    curveScaleModel KN A ≃L[𝕜] curveScaleModel KM B :=
  (curveScaleTransportedEquiv R KM KN hR hKM hKN e A).toContinuousLinearEquiv.trans
    (curveScaleAtlasEquiv R KM hR hKM (A.pullback e) B)

lemma curveScaleReparametrization_realization
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N) (B : FiniteChartPartition M)
    (v : curveScaleModel KN A) :
    curveScaleRealization R KM B (curveScaleReparametrization R KM KN hR hKM hKN e A B v) =
      ScalarCurveDistribution.pullback e (curveScaleRealization R KN A v) := by
  change curveScaleRealization R KM B
    (curveScaleAtlasEquiv R KM hR hKM (A.pullback e) B
      (curveScaleTransportedEquiv R KM KN hR hKM hKN e A v)) = _
  rw [curveScaleAtlasEquiv_realization, curveScaleTransportedEquiv_realization]

lemma curveScaleReparametrization_two_sided_bound
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N) (A : FiniteChartPartition N) (B : FiniteChartPartition M) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ v, ‖curveScaleReparametrization R KM KN hR hKM hKN e A B v‖ ≤ C * ‖v‖) ∧
      ∀ w, ‖(curveScaleReparametrization R KM KN hR hKM hKN e A B).symm w‖ ≤ C * ‖w‖ :=
  ExpandedFA.Sobolev.ProjectionModel.equiv_two_sided_bound (KN A A) (KM B B)
    (curveScaleReparametrization R KM KN hR hKM hKN e A B)

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
open Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
universe u v
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace ℝ N]
  [IsManifold (𝓘(ℝ)) ∞ N] [T2Space N] [CompactSpace N]
variable {𝕜 : Type} [RCLike 𝕜]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (R : H →ₗ[𝕜] (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜))
  (KM : ∀ A B : FiniteChartPartition M, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
  (KN : ∀ A B : FiniteChartPartition N, CurveScaleTuples H A →L[𝕜] CurveScaleTuples H B)
  (hR : Function.Injective R)
  (hKM : ∀ A B (v : CurveScaleTuples H A) j φ,
    R ((KM A B v) j) φ = partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)
  (hKN : ∀ A B (v : CurveScaleTuples H A) j φ,
    R ((KN A B v) j) φ = partitionDistribution (partitionSynthesis A (fun i => R (v i))) B j φ)

include hR hKM hKN

/-- Assemble the precise source reparametrization assertion from the proved
closed-model presentation, actual density transpose and transported-atlas isometry. -/
theorem curveScaleReparametrization_presentation
    (A : FiniteChartPartition M) (B : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N)
    (hPM : CurveScalePresentation (fun u φ => R u φ) A
      (curveScaleModel KM A) (curveScaleRealization R KM A))
    (hPN : CurveScalePresentation (fun u φ => R u φ) B
      (curveScaleModel KN B) (curveScaleRealization R KN B)) :
    ∃ (SM : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
      (SN : Submodule 𝕜 (PiLp 2 (fun _ : Fin B.n => H)))
      (UM : SM →ₗ[𝕜] ScalarCurveDistribution 𝕜 M)
      (UN : SN →ₗ[𝕜] ScalarCurveDistribution 𝕜 N)
      (D : TestDensities 𝕜 M ≃ₗ[𝕜] TestDensities 𝕜 N)
      (P : ScalarCurveDistribution 𝕜 N ≃ₗ[𝕜] ScalarCurveDistribution 𝕜 M)
      (F : SN ≃L[𝕜] SM),
      CurveScalePresentation (fun u φ => R u φ) A SM UM ∧
      CurveScalePresentation (fun u φ => R u φ) B SN UN ∧
      (∀ (ρ : TestDensities 𝕜 M) (y : N), (D ρ).val y =
        |deriv (fun z : ℝ => (chartAt ℝ (e.symm y))
          (e.symm ((chartAt ℝ y).symm z))) ((chartAt ℝ y) y)| • ρ.val (e.symm y)) ∧
      (∀ (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M),
        (P T).toLinearMap ρ = T.toLinearMap (D ρ)) ∧
      ∀ u : SN, UM (F u) = P (UN u) := by
  refine ⟨curveScaleModel KM A, curveScaleModel KN B,
    curveScaleRealization R KM A, curveScaleRealization R KN B,
    densityPullbackEquiv e.symm, ScalarCurveDistribution.pullback e,
    curveScaleReparametrization R KM KN hR hKM hKN e B A, hPM, hPN, ?_, ?_, ?_⟩
  · intro ρ y
    change SmoothChart.mapJacobian e.symm y • ρ.val (e.symm y) = _
    rw [SmoothChart.mapJacobian_eq_deriv]
  · intro T ρ
    rfl
  · intro u
    exact curveScaleReparametrization_realization R KM KN hR hKM hKN e B A u

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve

/-- For every real order, every smooth reparametrization is an isomorphism of
the actual complex curve Sobolev spaces, with the inverse absolute Jacobian
in its scalar-density transpose. -/
theorem curve_hilbert_reparametrization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.curveHilbertReparametrizationType := by
  intro s M _ _ _ _ _ N _ _ _ _ _ A B e
  let KM := curveHsMatrix (M := M) s
  let KN := curveHsMatrix (M := N) s
  let R := lineHsRealization s
  have hR := lineHsRealization_injective s
  have hKM := curveHsMatrix_spec (M := M) s
  have hKN := curveHsMatrix_spec (M := N) s
  exact curveScaleReparametrization_presentation R KM KN hR hKM hKN A B e
    (curveScalePresentation_proved R KM hR hKM A)
    (curveScalePresentation_proved R KN hR hKN B)

/-- The same actual global reparametrization theorem over the canonical real
Sobolev scale, including fractional and negative real orders. -/
theorem real_curve_hilbert_reparametrization :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.realCurveHilbertReparametrizationType := by
  intro s M _ _ _ _ _ N _ _ _ _ _ A B e
  let KM := curveRealHsMatrix (M := M) s
  let KN := curveRealHsMatrix (M := N) s
  let R := lineRealHsRealization s
  have hR := lineRealHsRealization_injective s
  have hKM := curveRealHsMatrix_spec (M := M) s
  have hKN := curveRealHsMatrix_spec (M := N) s
  exact curveScaleReparametrization_presentation R KM KN hR hKM hKN A B e
    (curveScalePresentation_proved R KM hR hKM A)
    (curveScalePresentation_proved R KN hR hKN B)

end ExpandedFA.Sobolev.Curve

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe ur
variable {M : Type ur} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]
variable {𝕜 : Type} [RCLike 𝕜]

/-- An overlap coefficient gives the exact density extraction on a chart generator. -/
lemma densityCoefficient_chartTest_eq (e c : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯) (hρ : tsupport ρ ⊆ e.val.source)
    (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤)
    (a : ℝ → 𝕜) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ (c.transition e).source)
    (haφ : ∀ y ∈ tsupport φ, a y = (ρ (c.val.symm y) : 𝕜)) :
    (densityCoefficient e ρ hρ (chartTestDensity 𝕜 c φ) : ℝ → 𝕜) =
      localizedDensity (c.transition e) a φ := by
  let β : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤ :=
    ⟨fun y => a y * φ y, ha.mul φ.contDiff, hac.mul_right,
      (tsupport_mul_subset_left ..).trans (has.trans (fun _ hy => hy.1))⟩
  have hβs : tsupport β ⊆ (c.transition e).source := (tsupport_mul_subset_left ..).trans has
  obtain ⟨ψ, hψ⟩ := chartDensityTransfer_exists c e β hβs
  have hβ : chartDensityFunction c β = fun x => ρ x • chartDensityFunction c φ x := by
    funext x
    by_cases hx : x ∈ c.val.source
    · simp only [chartDensityFunction, indicator_of_mem hx]
      change c.densityJacobian x • (a (c.val x) * φ (c.val x)) =
        ρ x • c.densityJacobian x • φ (c.val x)
      by_cases hy : c.val x ∈ tsupport φ
      · rw [haφ _ hy, c.val.left_inv hx]
        rw [← RCLike.real_smul_eq_coe_mul]
        exact smul_comm _ _ _
      · rw [image_eq_zero_of_notMem_tsupport hy]
        simp
    · simp [chartDensityFunction, hx]
  have heq : densityCoefficient e ρ hρ (chartTestDensity 𝕜 c φ) = ψ := by
    apply chartDensityFunction_injective e
    rw [densityCoefficient_spec]
    exact hβ.symm.trans (chartDensityFunction_transition c e β ψ hβs hψ)
  funext y
  rw [heq, hψ]
  rfl

/-- The bilinear regular distribution of a scalar Schwartz function on the line. -/
def lineSchwartzScalarDistribution (g : SchwartzMap ℝ 𝕜) :
    SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜 :=
  (SchwartzMap.integralCLM 𝕜 volume).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) g)

@[simp] lemma lineSchwartzScalarDistribution_apply (g φ : SchwartzMap ℝ 𝕜) :
    lineSchwartzScalarDistribution g φ = ∫ x, g x * φ x := rfl

/-- The genuine scalar chart localization of a smooth function, as a Schwartz test. -/
def chartScalarSchwartz [T2Space M] [CompactSpace M] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (i : Fin A.n) : SchwartzMap ℝ 𝕜 :=
  (chartLocalFunction_smooth_compact A f i).2.1.toSchwartzMap
    (chartLocalFunction_smooth_compact A f i).1

@[simp] lemma chartScalarSchwartz_apply [T2Space M] [CompactSpace M]
    (A : FiniteChartPartition M) (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯)
    (i : Fin A.n) (x : ℝ) : chartScalarSchwartz A f i x = chartLocalFunction A f i x := rfl

/-- The intrinsic scalar distribution associated to a smooth scalar function,
constructed from finite chart pairings against the exact extracted densities. -/
def smoothScalarDistribution [T2Space M] [CompactSpace M] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) : ScalarCurveDistribution 𝕜 M :=
  partitionSynthesis A (fun i => lineSchwartzScalarDistribution (chartScalarSchwartz A f i))


lemma regularSynthesis_integrand [T2Space M] [CompactSpace M]
    (A : FiniteChartPartition M) (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯)
    (c : SmoothChart M) (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤)
    (i : Fin A.n) (a : ℝ → 𝕜)
    (haφ : ∀ y ∈ tsupport φ,
      a y = (partitionReconstructionCutoff A i (c.val.symm y) : 𝕜)) (y : ℝ) :
    localizedPullback (c.transition ⟨A.chart i, A.chart_smooth i⟩) a
        (chartScalarSchwartz A f i) y * φ y =
      A.cutoff i (c.val.symm y) • f (c.val.symm y) * φ y := by
  by_cases hyφ : y ∈ tsupport φ
  · have hy : y ∈ c.val.target := φ.tsupport_subset hyφ
    by_cases hi : c.val.symm y ∈ (A.chart i).source
    · have ht : y ∈ (c.transition ⟨A.chart i, A.chart_smooth i⟩).source := ⟨hy, hi⟩
      rw [localizedPullback, indicator_of_mem ht, chartScalarSchwartz_apply]
      change (a y * chartLocalFunction A f i ((A.chart i) (c.val.symm y))) * φ y = _
      rw [chartLocalFunction_apply A f i ((A.chart i).map_source hi),
        (A.chart i).left_inv hi, haφ y hyφ]
      simp only [RCLike.real_smul_eq_coe_mul]
      have hmul : (partitionReconstructionCutoff A i (c.val.symm y) : 𝕜) *
          (A.cutoff i (c.val.symm y) : 𝕜) = (A.cutoff i (c.val.symm y) : 𝕜) := by
        rw [← RCLike.ofReal_mul, mul_comm, partitionReconstructionCutoff_mul]
      simp only [← mul_assoc]
      rw [hmul]
    · have ht : y ∉ (c.transition ⟨A.chart i, A.chart_smooth i⟩).source :=
        fun h => hi h.2
      have hz : A.cutoff i (c.val.symm y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hi (A.subordinate i h))
      simp [localizedPullback, ht, hz]
  · rw [image_eq_zero_of_notMem_tsupport hyφ]
    simp

/-- The intrinsic distribution of a smooth scalar has its ordinary scalar
representative in every chart, paired against the coordinate density coefficient. -/
theorem smoothScalarDistribution_inChart [T2Space M] [CompactSpace M]
    (A : FiniteChartPartition M) (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯)
    (c : SmoothChart M) (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤) :
    (smoothScalarDistribution A f).inChart c φ = ∫ y, f (c.val.symm y) * φ y := by
  have hex : ∀ i : Fin A.n, ∃ a : ℝ → 𝕜, ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
      tsupport a ⊆ (c.transition ⟨A.chart i, A.chart_smooth i⟩).source ∧
      ∀ y ∈ tsupport φ, a y = (partitionReconstructionCutoff A i (c.val.symm y) : 𝕜) := by
    intro i
    exact densityExtractionStepCoefficient_exists ⟨A.chart i, A.chart_smooth i⟩ c
      (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i)
      ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset
  choose a ha hac has haφ using hex
  have heq : ∀ i, (partitionDensitySchwartzLM A i (chartTestDensity 𝕜 c φ) : ℝ → 𝕜) =
      localizedDensity (c.transition ⟨A.chart i, A.chart_smooth i⟩) (a i) φ := by
    intro i
    exact densityCoefficient_chartTest_eq ⟨A.chart i, A.chart_smooth i⟩ c
      (partitionReconstructionCutoff A i) (partitionReconstructionCutoff_support A i)
      φ (a i) (ha i) (hac i) (has i) (haφ i)
  have hint : ∀ i : Fin A.n, Integrable (fun y =>
      localizedPullback (c.transition ⟨A.chart i, A.chart_smooth i⟩) (a i)
        (chartScalarSchwartz A f i) y * φ y) := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((localizedPullback_contDiff _ (c.transition_smooth _) _ _ (ha i)
        ((chartScalarSchwartz A f i).smooth ⊤) (has i)).continuous.mul φ.contDiff.continuous)
    · exact (localizedPullback_hasCompactSupport _ _ _ (hac i)).mul_right
  change (partitionSynthesis A (fun i =>
    lineSchwartzScalarDistribution (chartScalarSchwartz A f i))).toLinearMap
      (chartTestDensity 𝕜 c φ) = _
  rw [partitionSynthesis_apply]
  simp only [lineSchwartzScalarDistribution_apply]
  calc
    _ = ∑ i, ∫ y, localizedPullback (c.transition ⟨A.chart i, A.chart_smooth i⟩) (a i)
        (chartScalarSchwartz A f i) y * φ y := by
      apply Finset.sum_congr rfl
      intro i _
      have hr : (fun y => chartScalarSchwartz A f i y *
          partitionDensitySchwartzLM A i (chartTestDensity 𝕜 c φ) y) =
          fun y => chartScalarSchwartz A f i y *
            localizedDensity (c.transition ⟨A.chart i, A.chart_smooth i⟩) (a i) φ y := by
        ext y
        rw [heq]
      rw [hr]
      exact (localizedPullback_pairing _
        (fun y hy => (((⟨A.chart i, A.chart_smooth i⟩ : SmoothChart M).transition_smooth c)
          y hy).contDiffAt ((c.transition ⟨A.chart i, A.chart_smooth i⟩).open_target.mem_nhds hy)
            |>.differentiableAt (by simp)) (a i) (chartScalarSchwartz A f i) φ).symm
    _ = ∫ y, ∑ i, localizedPullback (c.transition ⟨A.chart i, A.chart_smooth i⟩) (a i)
        (chartScalarSchwartz A f i) y * φ y := (integral_finsetSum _ (fun i _ => hint i)).symm
    _ = ∫ y, f (c.val.symm y) * φ y := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        simp_rw [regularSynthesis_integrand A f c φ _ _ (haφ _) y]
        rw [← Finset.sum_mul, ← Finset.sum_smul, A.sum_one, one_smul])

end ExpandedFA.Sobolev.Curve


namespace ExpandedFA.Sobolev.Curve

theorem smooth_curve_regular_distribution :
    Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales.smoothCurveRegularDistributionType := by
  intro M _ _ _ _ _ 𝕜 _ f
  obtain ⟨A⟩ := finite_chart_partition M
  refine ⟨smoothScalarDistribution A f, smoothScalarDistribution_inChart A f, ?_⟩
  intro T hT
  apply ScalarCurveDistribution.ext
  intro c
  ext φ
  rw [hT, smoothScalarDistribution_inChart]

end ExpandedFA.Sobolev.Curve
