import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.CzBmoEndpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyBMODuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyCZEndpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.HilbertTransform
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.PartIV.CzBmoEndpoint
open Hardy Hardy.HardyDualBMORepresentationSpec Hardy.BMOQuotientSpec
open SingularIntegrals.StandardConvolution

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Choose a representative; uniqueness modulo constants removes the choice
from the resulting quotient map. -/
def dualRepresentative (L : H1 d 𝕜 →L[𝕜] 𝕜) : BMOFunction d 𝕜 :=
  Classical.choose ((HardyBMODuality.hardy_bmo_duality.2 d).choose_spec.2 𝕜 |>.1 L)

lemma dualRepresentative_represents (L : H1 d 𝕜 →L[𝕜] 𝕜) :
    Represents L (dualRepresentative L).val :=
  Classical.choose_spec ((HardyBMODuality.hardy_bmo_duality.2 d).choose_spec.2 𝕜 |>.1 L)

lemma represents_add {L K : H1 d 𝕜 →L[𝕜] 𝕜}
    {g h : BMOFunction d 𝕜} (hg : Represents L g.val) (hh : Represents K h.val) :
    Represents (L + K) (g + h).val := by
  apply HardyDualBMORepresentation.represents_of_atom_pairings _ _ (g + h).property.1
  intro a
  rw [add_apply, HardyBMODuality.atom_value_of_represents hg a,
    HardyBMODuality.atom_value_of_represents hh a]
  change _ = ∫ x, a.val x * (g.val x + h.val x)
  simp only [mul_add]
  exact (integral_add
    (HardyDualBMORepresentation.integrable_atom_mul g.val g.property.1 a)
    (HardyDualBMORepresentation.integrable_atom_mul h.val h.property.1 a)).symm

lemma represents_smul {L : H1 d 𝕜 →L[𝕜] 𝕜} {g : BMOFunction d 𝕜}
    (hg : Represents L g.val) (c : 𝕜) : Represents (c • L) (c • g).val := by
  apply HardyDualBMORepresentation.represents_of_atom_pairings _ _ (c • g).property.1
  intro a
  rw [smul_apply, HardyBMODuality.atom_value_of_represents hg a]
  change c * (∫ x, a.val x * g.val x) = ∫ x, a.val x * (c * g.val x)
  calc
    _ = ∫ x, c * (a.val x * g.val x) := (integral_const_mul _ _).symm
    _ = _ := by congr 1; funext x; ring

def dualToBMOLinear : (H1 d 𝕜 →L[𝕜] 𝕜) →ₗ[𝕜] BMO d 𝕜 where
  toFun L := classOf (dualRepresentative L)
  map_add' L K := by
    rw [← bmo_class_add]
    exact Quotient.sound (HardyBMODuality.modConstants_of_represents
      (represents_add (dualRepresentative_represents L) (dualRepresentative_represents K))
      (dualRepresentative_represents (L + K)))
  map_smul' c L := by
    rw [← bmo_class_smul]
    exact Quotient.sound (HardyBMODuality.modConstants_of_represents
      (represents_smul (dualRepresentative_represents L) c)
      (dualRepresentative_represents (c • L)))

lemma dualToBMOLinear_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (L : H1 d 𝕜 →L[𝕜] 𝕜),
      ‖dualToBMOLinear L‖ ≤ C * ‖L‖ := by
  obtain ⟨C, hC, h⟩ := HardyBMODuality.hardy_bmo_duality.2 d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ L
  exact (h 𝕜).2 (dualRepresentative L) L (dualRepresentative_represents L) |>.2.1

/-- The inverse Hardy–BMO representation on the actual quotient. -/
def dualToBMO : (H1 d 𝕜 →L[𝕜] 𝕜) →L[𝕜] BMO d 𝕜 := by
  let C := Classical.choose (dualToBMOLinear_bound (d := d))
  have hC : ∀ L : H1 d 𝕜 →L[𝕜] 𝕜, ‖dualToBMOLinear L‖ ≤ C * ‖L‖ :=
    (Classical.choose_spec (dualToBMOLinear_bound (d := d))).2 𝕜
  exact LinearMap.mkContinuous (E := H1 d 𝕜 →L[𝕜] 𝕜) (F := BMO d 𝕜)
    (σ := RingHom.id 𝕜) dualToBMOLinear C hC

@[simp] lemma dualToBMO_apply (L : H1 d 𝕜 →L[𝕜] 𝕜) :
    dualToBMO L = classOf (dualRepresentative L) := rfl

lemma dualToBMO_unique {L : H1 d 𝕜 →L[𝕜] 𝕜} {g : BMOFunction d 𝕜}
    (hg : Represents L g.val) : dualToBMO L = classOf g := by
  rw [dualToBMO_apply]
  exact Quotient.sound (HardyBMODuality.modConstants_of_represents hg
    (dualRepresentative_represents L))

/-- The bounded bilinear integral used in the source's transposition argument.
This is defined for every bounded h and every L¹ vector. -/
def transposeFunctional (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜) :
    Lp 𝕜 ∞ (volume : Measure (Hardy.Point d)) →L[𝕜] (H1 d 𝕜 →L[𝕜] 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 _ _ _).flip A |>.comp
    (FunctionSpaces.lpIntegralPairing volume 1 ∞)

lemma transposeFunctional_apply
    (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜)
    (h : Lp 𝕜 ∞ (volume : Measure (Hardy.Point d))) (f : H1 d 𝕜) :
    transposeFunctional A h f = ∫ x, A f x * h x :=
  (FunctionSpaces.lp_pairing_integral volume 1 ∞ h (A f)).2

lemma transposeFunctional_bound
    (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜)
    (h : Lp 𝕜 ∞ (volume : Measure (Hardy.Point d))) :
    ‖transposeFunctional A h‖ ≤ ‖A‖ * ‖h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  calc
    _ ≤ ‖h‖ * ‖A f‖ := FunctionSpaces.lp_pairing_apply_bound volume 1 ∞ h (A f)
    _ ≤ ‖h‖ * (‖A‖ * ‖f‖) := mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg h)
    _ = (‖A‖ * ‖h‖) * ‖f‖ := by ring

/-- Bilinear transposition, as a scalar-linear map into BMO modulo constants. -/
def endpointOfHardyMap (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜) :
    Lp 𝕜 ∞ (volume : Measure (Hardy.Point d)) →L[𝕜] BMO d 𝕜 :=
  dualToBMO.comp (transposeFunctional A)

lemma endpointOfHardyMap_represents
    (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜)
    (h : Lp 𝕜 ∞ (volume : Measure (Hardy.Point d))) :
    ∃ g : BMOFunction d 𝕜, endpointOfHardyMap A h = classOf g ∧
      Represents (transposeFunctional A h) g.val :=
  ⟨dualRepresentative _, rfl, dualRepresentative_represents _⟩

lemma endpointOfHardyMap_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜]
      (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜),
      ‖endpointOfHardyMap A‖ ≤ C * ‖A‖ := by
  obtain ⟨C, hC, h⟩ := dualToBMOLinear_bound (d := d)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ A
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h₀
  change ‖dualToBMOLinear (transposeFunctional A h₀)‖ ≤ _
  calc
    _ ≤ C * ‖transposeFunctional A h₀‖ := h 𝕜 _
    _ ≤ C * (‖A‖ * ‖h₀‖) :=
      mul_le_mul_of_nonneg_left (transposeFunctional_bound A h₀) hC.le
    _ = _ := by ring

open CzBmoEndpointSpec

lemma canonicalQuotientStructure : QuotientStructure (d := d) (𝕜 := 𝕜) := by
  refine ⟨inferInstance, norm_bmo_class, ?_, ?_⟩
  · intro f g
    exact ⟨(f + g).property, rfl⟩
  · intro c f
    exact ⟨(c • f).property, rfl⟩

lemma transposeFunctional_eq
    (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜)
    (h : Linfty d 𝕜) : transposeFunctional A h = functional A h := rfl

/-- A complete, unconditional functional-to-BMO construction. The actual
standard operator is instantiated later; no transpose estimate is assumed here. -/
theorem abstract_transposition : AbstractTransposition := by
  intro d
  obtain ⟨C, hC, h⟩ := endpointOfHardyMap_bound (d := d)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _
  refine ⟨bmoNormedAddCommGroup, bmoNormedSpace, canonicalQuotientStructure, ?_⟩
  intro A
  refine ⟨endpointOfHardyMap A, h 𝕜 A, ?_⟩
  intro h₀
  obtain ⟨g, hg, hr⟩ := endpointOfHardyMap_represents A h₀
  refine ⟨g, hg, hr, ?_⟩
  intro g' hg'
  change classOf g' = dualToBMO (transposeFunctional A h₀)
  exact (dualToBMO_unique hg').symm

lemma integral_bilinear_eq_inner (f g : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    (∫ x, f x * g x) = inner 𝕜 (star g) f := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  simp only [RCLike.inner_apply, hx, Pi.star_apply, starRingEnd_apply, star_star]

/-- The conjugations convert the Hilbert adjoint to the source's scalar-linear
transpose for both scalar fields. -/
theorem transpose_pairing : TransposePairing := by
  intro 𝕜 _ d T f g
  rw [integral_bilinear_eq_inner, integral_bilinear_eq_inner]
  simp only [transposeValue, star_star, ContinuousLinearMap.adjoint_inner_left]

/-- The endpoint class agrees with the original L² operator on every bounded
L² input, using atom separation of locally integrable functions. -/
lemma endpointOfHardyMap_consistent
    (T : StandardConvolutionOperator 𝕜 d)
    (A : H1 d 𝕜 →L[𝕜] HardyDualBMORepresentationSpec.L1 d 𝕜)
    (hA : HardyTransposeAgreement T A) :
    ConsistentWithL2 T (endpointOfHardyMap A) := by
  intro h h2
  obtain ⟨g, hg, hrep⟩ := endpointOfHardyMap_represents A h
  refine ⟨g, hg, ?_⟩
  apply HardyDualBMORepresentation.atom_separation d 𝕜
    (T.operator (h2.toLp _)) g.val
    ((Lp.memLp _).locallyIntegrable (by norm_num)) g.property.1
  intro a
  obtain ⟨c, r, hr, hs, ha2, hb⟩ := HardyCZEndpoint.atom_energy a
  let af := AtomicHardySpace.atomElement volume a
  have haE : MemLp (AtomicHardySpaceSpec.EmbeddingValue volume af
      : SingularIntegrals.StandardConvolution.Space d → 𝕜) 2 := by
    simpa only [af, AtomicHardySpace.embedding_atomElement] using ha2
  have hAe : (A af : SingularIntegrals.StandardConvolution.Space d → 𝕜) =ᵐ[volume]
      transposeValue T.operator (ha2.toLp a.val) := by
    simpa only [af, AtomicHardySpace.embedding_atomElement] using hA af haE
  calc
    (∫ x, a.val x * T.operator (h2.toLp _) x) =
        ∫ x, T.operator (h2.toLp _) x * (ha2.toLp a.val) x := by
      apply integral_congr_ae
      filter_upwards [ha2.coeFn_toLp] with x hx
      rw [hx, mul_comm]
    _ = ∫ x, (h2.toLp _) x * transposeValue T.operator (ha2.toLp a.val) x :=
      transpose_pairing 𝕜 d T.operator _ _
    _ = ∫ x, A af x * h x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp, hAe] with x hx hy
      rw [hx, hy, mul_comm]
    _ = transposeFunctional A h af := (transposeFunctional_apply A h af).symm
    _ = ∫ x, a.val x * g.val x := HardyBMODuality.atom_value_of_represents hrep a

/-- Conditional assembly isolates the remaining standard-transpose construction.
The premise is not an accepted theorem or part of the final Endpoint statement. -/
theorem endpoint_of_standardTranspose (hTranspose : StandardTranspose) : Endpoint := by
  intro d
  obtain ⟨C, hC, h⟩ := endpointOfHardyMap_bound (d := d)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _
  refine ⟨bmoNormedAddCommGroup, bmoNormedSpace, canonicalQuotientStructure, ?_⟩
  intro T
  obtain ⟨S, hS, hk, hn⟩ := hTranspose 𝕜 d T
  obtain ⟨A, hAn, hAc⟩ := HardyCZEndpoint.endpoint 𝕜 d S
  have he : Hardy.HardyCZEndpointSpec.endpointConstant S =
      Hardy.HardyCZEndpointSpec.endpointConstant T := by
    unfold Hardy.HardyCZEndpointSpec.endpointConstant
    rw [hk, hn]
  have hA : HardyTransposeAgreement T A := by
    obtain ⟨W, hW, _⟩ := SingularIntegrals.CZWeak.unique_extension 𝕜 d S
    intro f h2
    have h₁ := hAc W hW f
    have h₂ := hW.1 (AtomicHardySpaceSpec.EmbeddingValue volume f)
      (Lp.memLp _) h2
    rw [Lp.toLp_coeFn] at h₂
    exact h₁.trans (h₂.trans (Filter.Eventually.of_forall
      (fun x => congrArg (fun v : SingularIntegrals.StandardConvolution.L2 𝕜 d => v x)
        (hS (h2.toLp _)))))
  refine ⟨A, endpointOfHardyMap A, hA, he ▸ hAn, ?_, ?_,
    endpointOfHardyMap_consistent T A hA⟩
  · calc
      _ ≤ C * ‖A‖ := h 𝕜 A
      _ ≤ C * Hardy.HardyCZEndpointSpec.endpointConstant T :=
        mul_le_mul_of_nonneg_left (he ▸ hAn) hC.le
  · intro h₀
    exact endpointOfHardyMap_represents A h₀

/-- Spatial reflection on L² is an isometry preserving the a.e. quotient. -/
def reflectL2 : SingularIntegrals.StandardConvolution.L2 𝕜 d →L[𝕜]
    SingularIntegrals.StandardConvolution.L2 𝕜 d :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 Neg.neg (Measure.measurePreserving_neg volume)).toContinuousLinearMap

lemma reflectL2_coe (f : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    (reflectL2 f : SingularIntegrals.StandardConvolution.Space d → 𝕜) =ᵐ[volume]
      fun x => f (-x) := Lp.coeFn_compMeasurePreserving _ _

@[simp] lemma reflectL2_norm (f : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    ‖reflectL2 f‖ = ‖f‖ := Lp.norm_compMeasurePreserving _ _

@[simp] lemma reflectL2_reflectL2 (f : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    reflectL2 (reflectL2 f) = f := by
  apply Lp.ext
  filter_upwards [reflectL2_coe (reflectL2 f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae (reflectL2_coe f)] with x hx hy
  simpa only [hx, neg_neg] using hy

/-- Reflection is continuous on the original LF test space. -/
def reflectTest : Tests 𝕜 d →L[𝕜] Tests 𝕜 d :=
  Distributions.ProperSupportConvolution.pullbackCLM
    (LinearIsometryEquiv.neg ℝ : Space d ≃ₗᵢ[ℝ] Space d).toContinuousLinearEquiv

@[simp] lemma reflectTest_apply (φ : Tests 𝕜 d) (x : Space d) :
    reflectTest φ x = φ (-x) := rfl

@[simp] lemma reflectL2_test (φ : Tests 𝕜 d) :
    reflectL2 (testL2 φ) = testL2 (reflectTest φ) := by
  apply Lp.ext
  filter_upwards [reflectL2_coe (testL2 φ),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae (testL2_coe φ),
    testL2_coe (reflectTest φ)] with x hx hy hz
  simpa only [hx, hz, reflectTest_apply] using hy

lemma kernelGradientNorm_reflect (k : Space d → 𝕜) (hk : ContDiffOn ℝ 1 k {0}ᶜ)
    (x : Space d) (hx : x ≠ 0) :
    kernelGradientNorm (fun y => k (-y)) x = kernelGradientNorm k (-x) := by
  have hd : DifferentiableAt ℝ k (-x) :=
    hk.differentiableOn (by simp) (-x) (by simpa) |>.differentiableAt
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa))
  have he : fderiv ℝ (fun y => k (-y)) x =
      (fderiv ℝ k (-x)).comp (-ContinuousLinearMap.id ℝ (Space d)) :=
    (hd.hasFDerivAt.comp x (hasFDerivAt_id x).neg).fderiv
  simp [kernelGradientNorm, he]

/-- The reflected physical kernel retains exactly the same kernel constant. -/
def reflectedKernel (k : StandardKernel 𝕜 d) : StandardKernel 𝕜 d where
  function x := k.function (-x)
  contDiff := k.contDiff.comp contDiff_neg.contDiffOn (by intro x hx; simpa using hx)
  constant := k.constant
  constant_nonneg := k.constant_nonneg
  size x hx := by simpa using k.size (-x) (neg_ne_zero.mpr hx)
  gradient x hx := by
    rw [kernelGradientNorm_reflect k.function k.contDiff x hx]
    simpa using k.gradient (-x) (neg_ne_zero.mpr hx)

/-- The spatial reflection R T R has the reflected distribution kernel. -/
def reflectedOperator (T : StandardConvolutionOperator 𝕜 d) :
    StandardConvolutionOperator 𝕜 d where
  operator := reflectL2.comp (T.operator.comp reflectL2)
  distribution := T.distribution.comp reflectTest
  kernel := reflectedKernel T.kernel
  translation_invariant := by
    intro a f g hfg
    have hRfg : (reflectL2 g : Space d → 𝕜) =ᵐ[volume]
        fun x => reflectL2 f (x - (-a)) := by
      filter_upwards [reflectL2_coe g,
        (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hfg,
        (measurePreserving_sub_right volume (-a)).quasiMeasurePreserving.ae (reflectL2_coe f)] with x hx hy hz
      simp only [hx, hz]
      convert hy using 1 <;> congr 1 <;> abel
    have ht := T.translation_invariant (-a) (reflectL2 f) (reflectL2 g) hRfg
    filter_upwards [reflectL2_coe (T.operator (reflectL2 g)),
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae ht,
      (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae
        (reflectL2_coe (T.operator (reflectL2 f)))] with x hx hy hz
    change reflectL2 (T.operator (reflectL2 g)) x = reflectL2 (T.operator (reflectL2 f)) (x-a)
    rw [hx, hz, hy]
    congr 1
    abel
  agrees_off_zero := by
    intro φ hφ
    have h : (0 : Space d) ∉ tsupport (reflectTest φ) := by
      intro hz
      have hs := tsupport_comp_subset_preimage φ (continuous_neg : Continuous (Neg.neg : Space d → Space d))
      exact hφ (by simpa using hs hz)
    change T.distribution (reflectTest φ) = _
    rw [T.agrees_off_zero _ h]
    simpa only [reflectTest_apply, reflectedKernel, neg_neg] using
      (integral_neg_eq_self (fun x => T.kernel.function x * φ (-x)) volume).symm
  kernel_action := by
    intro φ
    have ht := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae (T.kernel_action (reflectTest φ))
    filter_upwards [reflectL2_coe (T.operator (reflectL2 (testL2 φ))), ht] with x hx hy
    change reflectL2 (T.operator (reflectL2 (testL2 φ))) x = _
    rw [hx, reflectL2_test, hy]
    change T.distribution (reflectedTest (reflectTest φ) (-x)) =
      T.distribution (reflectTest (reflectedTest φ x))
    congr 1
    ext y
    simp [reflectedTest, sub_eq_add_neg, add_comm]

open ExpandedFA.Distributions

def reflectCoordinates : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)) →L[𝕜]
    Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)) :=
  Distributions.ProperSupportConvolution.pullbackCLM
    (LinearIsometryEquiv.neg ℝ : Domain d ≃ₗᵢ[ℝ] Domain d).toContinuousLinearEquiv

@[simp] lemma reflectCoordinates_apply
    (φ : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d))) (x : Domain d) :
    reflectCoordinates φ x = φ (-x) := rfl

lemma reflectedCoordinateFunction_reflectCoordinates {k : ℕ} (φ : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)))
    (a : Fin k → Fin d) (z : Domain d) :
    reflectedCoordinateFunction (reflectCoordinates φ) a z =
      iteratedFDeriv ℝ k φ (-z) (fun j => coordinateVector (a j)) := by
  let N : Domain d →L[ℝ] Domain d := -ContinuousLinearMap.id ℝ _
  have he : ⇑(reflectCoordinates φ) = φ ∘ N := rfl
  rw [reflectedCoordinateFunction, he,
    N.iteratedFDeriv_comp_right φ.contDiff z (i := k) (by simp)]
  simp [N]

/-- Integration by parts transfers every jet coordinate, including order zero.
The two integrated jets therefore have exactly the same value. -/
lemma integratedReflectedJet_reflection (φ ψ : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d))) (m : ℕ) :
    integratedReflectedJet (reflectCoordinates ψ) (reflectCoordinates φ) m =
      integratedReflectedJet φ ψ m := by
  ext a y
  rw [integratedReflectedJet_apply, integratedReflectedJet_apply_by_parts]
  simp only [reflectCoordinates_apply, reflectedCoordinateFunction_reflectCoordinates]
  have he : (fun x : Domain d => φ (-x) * iteratedFDeriv ℝ a.1.val ψ (-(x-y))
      (fun j => coordinateVector (a.2 j))) =
      (fun x => φ (-x) * iteratedFDeriv ℝ a.1.val ψ (-x+y)
        (fun j => coordinateVector (a.2 j))) := by
    funext x
    congr 2
    abel
  rw [he]
  exact integral_neg_eq_self (fun x : Domain d => φ x *
    iteratedFDeriv ℝ a.1.val ψ (x+y) (fun j => coordinateVector (a.2 j))) volume

lemma coordinate_distribution_pairing (U : ScalarDistribution 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)))
    (φ ψ : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d))) :
    (∫ x, U (reflectedTranslate φ x) * ψ x) =
      ∫ x, U (reflectedTranslate (reflectCoordinates ψ) x) * reflectCoordinates φ x := by
  obtain ⟨K₁, hK₁⟩ := reflectedTranslate_common_support φ (tsupport ψ) ψ.hasCompactSupport
  obtain ⟨K₂, hK₂⟩ := reflectedTranslate_common_support
    (reflectCoordinates ψ) (tsupport (reflectCoordinates φ)) (reflectCoordinates φ).hasCompactSupport
  let K := K₁ ⊔ K₂
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization U K
  have h₁ := distributionConvolution_transpose_finiteJet U φ ψ K
    (fun x hx => (hK₁ x hx).trans (show (K₁ : Set (Domain d)) ⊆ K from le_sup_left)) m L hL
  have h₂ := distributionConvolution_transpose_finiteJet U
    (reflectCoordinates ψ) (reflectCoordinates φ) K
    (fun x hx => (hK₂ x hx).trans (show (K₂ : Set (Domain d)) ⊆ K from le_sup_right)) m L hL
  rw [integratedReflectedJet_reflection] at h₂
  exact h₁.trans h₂.symm

def coordinateEquiv (d : ℕ) : Space d ≃L[ℝ] Domain d := EuclideanSpace.equiv (Fin d) ℝ

def toCoordinateTest : SingularIntegrals.StandardConvolution.Tests 𝕜 d →L[𝕜]
    Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)) :=
  Distributions.ProperSupportConvolution.pullbackCLM (coordinateEquiv d).symm

def toEuclideanTest : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)) →L[𝕜]
    SingularIntegrals.StandardConvolution.Tests 𝕜 d :=
  Distributions.ProperSupportConvolution.pullbackCLM (coordinateEquiv d)

@[simp] lemma toCoordinateTest_apply (φ : SingularIntegrals.StandardConvolution.Tests 𝕜 d)
    (x : Domain d) : toCoordinateTest φ x = φ ((coordinateEquiv d).symm x) := rfl

@[simp] lemma toEuclideanTest_apply
    (φ : Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)))
    (x : SingularIntegrals.StandardConvolution.Space d) :
    toEuclideanTest φ x = φ (coordinateEquiv d x) := rfl

@[simp] lemma toEuclidean_reflectedTranslate
    (φ : SingularIntegrals.StandardConvolution.Tests 𝕜 d) (z : Domain d) :
    toEuclideanTest (reflectedTranslate (toCoordinateTest φ) z) =
      reflectedTest φ ((coordinateEquiv d).symm z) := by
  ext y
  simp [reflectedTest, reflectedTranslate_apply, map_sub]

@[simp] lemma toCoordinate_reflect (φ : SingularIntegrals.StandardConvolution.Tests 𝕜 d) :
    toCoordinateTest (reflectTest φ) = reflectCoordinates (toCoordinateTest φ) := by
  ext z
  simp [map_neg]

lemma reflected_distribution_pairing (T : StandardConvolutionOperator 𝕜 d)
    (φ ψ : SingularIntegrals.StandardConvolution.Tests 𝕜 d) :
    (∫ x, T.distribution (reflectedTest φ x) * ψ x) =
      ∫ x, T.distribution (reflectedTest (reflectTest ψ) x) * reflectTest φ x := by
  let U : ScalarDistribution 𝕜 (⊤ : TopologicalSpace.Opens (Domain d)) :=
    T.distribution.comp toEuclideanTest
  have he := coordinate_distribution_pairing U (toCoordinateTest φ) (toCoordinateTest ψ)
  rw [← toCoordinate_reflect, ← toCoordinate_reflect] at he
  have hI (F : Domain d → 𝕜) :
      (∫ x : SingularIntegrals.StandardConvolution.Space d, F (coordinateEquiv d x)) =
        ∫ z, F z :=
    (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
      (coordinateEquiv d).toHomeomorph.measurableEmbedding F
  rw [← hI, ← hI] at he
  simpa only [U, ContinuousLinearMap.comp_apply, toEuclidean_reflectedTranslate,
    toCoordinateTest_apply, ContinuousLinearEquiv.symm_apply_apply] using he

lemma integral_reflectL2 (f g : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    (∫ x, f x * reflectL2 g x) = ∫ x, reflectL2 f x * g x := by
  calc
    _ = ∫ x, f x * g (-x) := integral_congr_ae
      ((reflectL2_coe g).mono fun x hx => by rw [hx])
    _ = ∫ x, f (-x) * g x := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun x => f (-x) * g x) volume)
    _ = _ := integral_congr_ae
      ((reflectL2_coe f).mono fun x hx => by rw [hx])

lemma reflectedOperator_test_pairing (T : StandardConvolutionOperator 𝕜 d)
    (φ ψ : Tests 𝕜 d) :
    (∫ x, T.operator (testL2 φ) x * testL2 ψ x) =
      ∫ x, testL2 φ x * (reflectedOperator T).operator (testL2 ψ) x := by
  have h₁ : (∫ x, T.operator (testL2 φ) x * testL2 ψ x) =
      ∫ x, T.distribution (reflectedTest φ x) * ψ x := by
    apply integral_congr_ae
    filter_upwards [T.kernel_action φ, testL2_coe ψ] with x hx hy
    rw [hx, hy]
  have h₂ : (∫ x, T.operator (testL2 (reflectTest ψ)) x * testL2 (reflectTest φ) x) =
      ∫ x, T.distribution (reflectedTest (reflectTest ψ) x) * reflectTest φ x := by
    apply integral_congr_ae
    filter_upwards [T.kernel_action (reflectTest ψ), testL2_coe (reflectTest φ)] with x hx hy
    rw [hx, hy]
  rw [h₁, reflected_distribution_pairing, ← h₂]
  change _ = ∫ x, testL2 φ x * reflectL2 (T.operator (reflectL2 (testL2 ψ))) x
  rw [integral_reflectL2, reflectL2_test, reflectL2_test]
  congr 1
  funext x
  exact mul_comm _ _

lemma testL2_dense : DenseRange (testL2 : Tests 𝕜 d → SingularIntegrals.StandardConvolution.L2 𝕜 d) := by
  intro f
  have hd := Lp.dense_hasCompactSupport_contDiff (F := 𝕜)
    (μ := (volume : Measure (Space d))) (p := 2) (by norm_num) f
  apply closure_mono _ hd
  rintro g ⟨u, hgu, huc, hus⟩
  refine ⟨⟨u, hus, huc, Set.subset_univ _⟩, ?_⟩
  apply Lp.ext
  exact (testL2_coe _).trans hgu.symm

lemma reflectedOperator_pairing (T : StandardConvolutionOperator 𝕜 d)
    (f g : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    (∫ x, T.operator f x * g x) =
      ∫ x, f x * (reflectedOperator T).operator g x := by
  let B := (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
    (volume : Measure (Space d)) 2 2
  have ht (φ ψ : Tests 𝕜 d) :
      B (T.operator (testL2 φ)) (testL2 ψ) =
        B (testL2 φ) ((reflectedOperator T).operator (testL2 ψ)) := by
    simpa only [B, ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply'] using
      reflectedOperator_test_pairing T φ ψ
  have hfirst (ψ : Tests 𝕜 d) (v : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
      B (T.operator v) (testL2 ψ) = B v ((reflectedOperator T).operator (testL2 ψ)) := by
    let F := (B.flip (testL2 ψ)).comp T.operator
    let G := B.flip ((reflectedOperator T).operator (testL2 ψ))
    exact congrFun (testL2_dense.equalizer F.continuous G.continuous
      (funext fun φ => ht φ ψ)) v
  let F := B (T.operator f)
  let G := (B f).comp (reflectedOperator T).operator
  have he := congrFun (testL2_dense.equalizer F.continuous G.continuous
    (funext fun ψ => hfirst ψ f)) g
  simpa only [F, G, B, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply'] using he

lemma reflectedOperator_transpose (T : StandardConvolutionOperator 𝕜 d)
    (g : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
    (reflectedOperator T).operator g = transposeValue T.operator g := by
  apply ext_inner_left 𝕜
  intro v
  have he := (reflectedOperator_pairing T (star v) g).symm.trans
    (transpose_pairing 𝕜 d T.operator (star v) g)
  have hj (h : SingularIntegrals.StandardConvolution.L2 𝕜 d) :
      (∫ x, star v x * h x) = inner 𝕜 v h := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with x hx
    simp [RCLike.inner_apply, hx, mul_comm]
  simpa only [hj] using he

/-- Actual standard closure, with the same physical-kernel constant and L² norm. -/
theorem standard_transpose : StandardTranspose := by
  intro 𝕜 _ d T
  refine ⟨reflectedOperator T, reflectedOperator_transpose T, rfl, ?_⟩
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖reflectL2 (T.operator (reflectL2 f))‖ ≤ _
    rw [reflectL2_norm]
    simpa only [reflectL2_norm] using T.operator.le_opNorm (reflectL2 f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have hb := (reflectedOperator T).operator.le_opNorm (reflectL2 f)
    change ‖reflectL2 (T.operator (reflectL2 (reflectL2 f)))‖ ≤ _ at hb
    simpa only [reflectL2_reflectL2, reflectL2_norm] using hb

/-- The full real/complex standard convolution endpoint, including d=0. -/
theorem endpoint : Endpoint := endpoint_of_standardTranspose standard_transpose

open SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

/-- Isometric transport of bounded data from ℝ to ℝ¹. -/
def lineToEuclideanLinfty : LineLp 𝕜 ∞ →L[𝕜] Linfty 1 𝕜 :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 lineIsometry.symm
    lineIsometry.symm.measurePreserving).toContinuousLinearMap

lemma lineToEuclideanLinfty_apply (h : LineLp 𝕜 ∞) :
    lineToEuclideanLinfty h = toEuclidean ∞ h := rfl

@[simp] lemma lineToEuclideanLinfty_norm (h : LineLp 𝕜 ∞) :
    ‖lineToEuclideanLinfty h‖ = ‖h‖ := Lp.norm_compMeasurePreserving _ _

/-- Generic endpoint specialization, with explicit transport back to line L²
representatives for consistency. -/
lemma line_endpoint_of_realization (H : LineLp 𝕜 2 → LineLp 𝕜 2)
    (hH : HasStandardRealization 𝕜 H) : LineHilbertEndpoint 𝕜 H := by
  obtain ⟨T, _hk, _hd, hT⟩ := hH
  obtain ⟨C, hC, h⟩ := endpoint 1
  obtain ⟨G, S, hQ, h⟩ := h 𝕜
  letI := G
  letI : AddCommGroup (BMOValue 1 𝕜) := G.toAddCommGroup
  letI : Norm (BMOValue 1 𝕜) := G.toNorm
  letI := S
  letI : Module 𝕜 (BMOValue 1 𝕜) := S.toModule
  obtain ⟨A, E, hA, hAn, hE, hrep, hc⟩ := h T
  let F : LineLp 𝕜 ∞ →L[𝕜] BMOValue 1 𝕜 := E.comp lineToEuclideanLinfty
  let K := max 1 (C * Hardy.HardyCZEndpointSpec.endpointConstant T)
  have hEK : ‖E‖ ≤ K := hE.trans (le_max_right _ _)
  have hFK : ‖F‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _))
    intro h₀
    change ‖E (lineToEuclideanLinfty h₀)‖ ≤ _
    calc
      _ ≤ ‖E‖ * ‖lineToEuclideanLinfty h₀‖ := E.le_opNorm _
      _ = ‖E‖ * ‖h₀‖ := by rw [lineToEuclideanLinfty_norm]
      _ ≤ K * ‖h₀‖ := mul_le_mul_of_nonneg_right hEK (norm_nonneg _)
  refine ⟨K, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    G, S, hQ, T, A, E, F, hT, hA, hAn, hEK, hFK, (fun _ => rfl),
    (fun h₀ => hrep (toEuclidean ∞ h₀)), hc, ?_⟩
  intro h₀ h2
  have he : (toEuclidean ∞ h₀ : Space 1 → 𝕜) =ᵐ[volume]
      fun x => h₀ (lineIsometry.symm x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2E : MemLp (toEuclidean ∞ h₀ : Space 1 → 𝕜) 2 volume :=
    (memLp_congr_ae he).mpr
      (h2.comp_measurePreserving lineIsometry.symm.measurePreserving)
  have hLp : h2E.toLp _ = toEuclidean 2 (h2.toLp _) := by
    apply Lp.ext
    filter_upwards [h2E.coeFn_toLp, he,
      lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae h2.coeFn_toLp,
      Lp.coeFn_compMeasurePreserving (h2.toLp _) lineIsometry.symm.measurePreserving]
      with x hx hy hz hw
    exact hx.trans (hy.trans (hz.symm.trans hw.symm))
  obtain ⟨g, hg, c, hgc⟩ := hc (toEuclidean ∞ h₀) h2E
  refine ⟨g, hg, c, ?_⟩
  have hback : (fromEuclidean 2 (T.operator (toEuclidean 2 (h2.toLp _))) : ℝ → 𝕜)
      =ᵐ[volume] fun x => T.operator (toEuclidean 2 (h2.toLp _)) (lineIsometry x) :=
    Lp.coeFn_compMeasurePreserving _ _
  rw [hT] at hback
  filter_upwards [lineIsometry.measurePreserving.quasiMeasurePreserving.ae hgc,
    hback] with x hx hy
  rw [hLp] at hx
  exact hx.trans (congrArg (fun z : 𝕜 => z + c) hy.symm)

/-- Assembly uses the original Fourier operator and its actual real restriction. -/
theorem hilbert_endpoint_of_realization : HilbertAssembly := by
  rintro ⟨hC, H, hH, hR⟩
  exact ⟨line_endpoint_of_realization complexHilbert hC,
    H, hH, line_endpoint_of_realization H hR⟩

/-- The named Hilbert endpoint, with no realization hypothesis left open. -/
theorem hilbert_endpoint : HilbertEndpoint :=
  hilbert_endpoint_of_realization SingularIntegrals.HilbertTransform.standard_realizations

/-- The full generic endpoint together with both named Hilbert specializations. -/
theorem full_endpoint : FullEndpoint := ⟨endpoint, hilbert_endpoint⟩

end ExpandedFA.PartIV.CzBmoEndpoint
