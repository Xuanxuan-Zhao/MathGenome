import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.HilbertTransform
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundLp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace ExpandedFA.SingularIntegrals.HilbertTransform

/-- The source operator, with its independently fixed expected value. -/
def H : Specs.ExpandedFA.SingularIntegrals.HilbertTransform.complexHilbertType :=
  complexHilbert

lemma frequencyAction_coe (f : ComplexL2) :
    (frequencyAction f : ℝ → ℂ) =ᵐ[volume] fun ξ => multiplier ξ * f ξ :=
  (multiplier_mul_memLp f).coeFn_toLp

lemma multiplier_norm (ξ : ℝ) (hξ : ξ ≠ 0) : ‖multiplier ξ‖ = 1 := by
  simp only [multiplier, ite_eq_right hξ]
  split_ifs <;> simp

lemma multiplier_square (ξ : ℝ) (hξ : ξ ≠ 0) :
    multiplier ξ * multiplier ξ = -1 := by
  simp only [multiplier, ite_eq_right hξ]
  split_ifs <;> simp

lemma frequencyAction_norm (f : ComplexL2) : ‖frequencyAction f‖ = ‖f‖ := by
  have hn : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖frequencyAction f ξ‖ = ‖f ξ‖ := by
    filter_upwards [frequencyAction_coe f, (Measure.ae_ne volume (0 : ℝ))] with ξ hx hξ
    rw [hx, norm_mul, multiplier_norm ξ hξ, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.ge))

lemma frequencyAction_square (f : ComplexL2) :
    frequencyAction (frequencyAction f) = -f := by
  apply Lp.ext
  filter_upwards [frequencyAction_coe (frequencyAction f), frequencyAction_coe f,
    Lp.coeFn_neg f, (Measure.ae_ne volume (0 : ℝ))] with ξ hx hy hz hξ
  rw [hx, hy, ← mul_assoc, multiplier_square ξ hξ, hz]
  simp

lemma frequencyAction_add (f g : ComplexL2) :
    frequencyAction (f + g) = frequencyAction f + frequencyAction g := by
  apply Lp.ext
  filter_upwards [frequencyAction_coe (f + g), frequencyAction_coe f,
    frequencyAction_coe g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencyAction f) (frequencyAction g)] with ξ ha hb hc hd he
  simp only [ha, hd, he, Pi.add_apply, hb, hc, mul_add]

lemma frequencyAction_smul (c : ℂ) (f : ComplexL2) :
    frequencyAction (c • f) = c • frequencyAction f := by
  apply Lp.ext
  filter_upwards [frequencyAction_coe (c • f), frequencyAction_coe f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (frequencyAction f)] with ξ ha hb hc hd
  simp only [ha, hb, hc, hd, Pi.smul_apply, smul_eq_mul]
  ring

/-- A continuous linear isometry on frequency space. -/
def frequencyIsometry : ComplexL2 →ₗᵢ[ℂ] ComplexL2 where
  toFun := frequencyAction
  map_add' := frequencyAction_add
  map_smul' := frequencyAction_smul
  norm_map' := frequencyAction_norm

/-- A continuous linear operator, built from the fixed Fourier multiplier. -/
def operator : ComplexL2 →L[ℂ] ComplexL2 :=
  lineFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (frequencyIsometry.toContinuousLinearMap.comp
      lineFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem multiplier_formula : Specs.ExpandedFA.SingularIntegrals.HilbertTransform.MultiplierFormula := by
  intro f
  simpa only [complexHilbert, lineFourier.apply_symm_apply] using
    frequencyAction_coe (lineFourier f)

theorem isometry : Specs.ExpandedFA.SingularIntegrals.HilbertTransform.Isometry := by
  intro f
  rw [complexHilbert, lineFourier.symm.norm_map, frequencyAction_norm, lineFourier.norm_map]

theorem square : Specs.ExpandedFA.SingularIntegrals.HilbertTransform.Square := by
  intro f
  apply lineFourier.injective
  simp only [complexHilbert, lineFourier.apply_symm_apply, map_neg]
  exact frequencyAction_square (lineFourier f)

theorem bounded_linear : Specs.ExpandedFA.SingularIntegrals.HilbertTransform.BoundedLinear :=
  ⟨operator, fun _ => rfl⟩

theorem normalized_principal_value :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.NormalizedPrincipalValue := by
  obtain ⟨T, hT⟩ := PrincipalValue.temperedness
  refine ⟨(Real.pi : ℂ)⁻¹ • T, ?_, ?_⟩
  · intro φ
    simp only [smul_apply, smul_eq_mul, hT]
  · intro φ
    simp only [smul_apply, smul_eq_mul, hT]
    have hf := PrincipalValue.fourier_principal_value φ
    change Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.principalValuePairingValue
      (FourierTransform.fourierCLM ℂ LineSchwartz φ) = signPairing φ at hf
    rw [hf, signPairing, ← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun ξ => by
      by_cases hz : ξ = 0
      · simp [multiplier, hz]
      · by_cases hp : 0 < ξ
        · simp [multiplier, hz, hp, mul_assoc, mul_left_comm,
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
        · simp [multiplier, hz, hp, mul_assoc, mul_left_comm,
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]

/-- Uniqueness among all classes having the prescribed multiplier transform. -/
lemma eq_of_multiplier_formula (f g : ComplexL2)
    (h : (lineFourier g : ℝ → ℂ) =ᵐ[volume]
      fun ξ => multiplier ξ * (lineFourier f) ξ) : g = complexHilbert f := by
  apply lineFourier.injective
  apply Lp.ext
  exact h.trans (multiplier_formula f).symm

theorem coordinate_transport :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.CoordinateTransport := by
  refine ⟨lineIsometry.measurePreserving, ?_, ?_⟩
  · intro 𝕜 _ p f
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (lineIsometry.symm ∘ lineIsometry) = id := funext lineIsometry.symm_apply_apply
    simp [hi]
  · intro 𝕜 _ p f
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (lineIsometry ∘ lineIsometry.symm) = id := funext lineIsometry.apply_symm_apply
    simp [hi]

/-- The kernel after removing a symmetric interval around its singularity. -/
def cutKernel (𝕜 : Type) [RCLike 𝕜] (ε : ℝ) (t : ℝ) : 𝕜 :=
  if ε < |t| then ((Real.pi * t : ℝ) : 𝕜)⁻¹ else 0

lemma cutKernel_measurable (𝕜 : Type) [RCLike 𝕜] (ε : ℝ) :
    Measurable (cutKernel 𝕜 ε) := by
  apply Measurable.ite (isOpen_lt continuous_const continuous_abs).measurableSet
  · fun_prop
  · exact measurable_const

/-- Cauchy--Schwarz applies to the actual tails, even though the untruncated
kernel is not locally integrable at zero. -/
lemma cutKernel_memLp (𝕜 : Type) [RCLike 𝕜] {ε : ℝ} (hε : 0 < ε) :
    MemLp (cutKernel 𝕜 ε) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (cutKernel_measurable 𝕜 ε).aestronglyMeasurable).2
  let C : ℝ := (1 + ε ^ 2) / (Real.pi ^ 2 * ε ^ 2)
  apply (integrable_inv_one_add_sq.const_mul C).mono'
    ((cutKernel_measurable 𝕜 ε).aestronglyMeasurable.norm.pow 2)
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖cutKernel 𝕜 ε t‖)]
  by_cases ht : ε < |t|
  · have ht0 : t ≠ 0 := by intro h; simp [h] at ht; linarith
    have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
    have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have het : ε ^ 2 ≤ t ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    simp only [cutKernel, ite_eq_left ht, norm_inv, RCLike.norm_ofReal,
      abs_mul, abs_of_pos Real.pi_pos, mul_pow, sq_abs, inv_pow]
    change (Real.pi ^ 2 * t ^ 2)⁻¹ ≤
      ((1 + ε ^ 2) / (Real.pi ^ 2 * ε ^ 2)) * (1 + t ^ 2)⁻¹
    rw [← div_eq_mul_inv, div_div, ← one_div,
      div_le_div_iff₀ (mul_pos hp2 ht2) (by positivity)]
    nlinarith [mul_nonneg hp2.le (sub_nonneg.mpr het)]
  · simp only [cutKernel, ite_eq_right ht, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    dsimp [C]
    positivity

lemma truncated_integrable (𝕜 : Type) [RCLike 𝕜] {ε : ℝ} (hε : 0 < ε)
    (f : LineLp 𝕜 2) (x : ℝ) :
    IntegrableOn (fun t => ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t))
      {t : ℝ | ε < |t|} := by
  have hf : MemLp (fun t => f (x - t)) 2 (volume : Measure ℝ) :=
    (Lp.memLp f).comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hi := (cutKernel_memLp 𝕜 hε).integrable_mul hf
  apply hi.integrableOn.congr_fun _ (isOpen_lt continuous_const continuous_abs).measurableSet
  intro t ht
  change ε < |t| at ht
  simp only [Pi.mul_apply, cutKernel, ite_eq_left ht]

/-- Complex conjugation on the scalar L² space, regarded as a real map. -/
def conjugateL2 : ComplexL2 →L[ℝ] ComplexL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

lemma conjugateL2_coe (f : ComplexL2) :
    (conjugateL2 f : ℝ → ℂ) =ᵐ[volume] fun x => star (f x) := by
  exact Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

lemma conjugateL2_schwartz (φ : SchwartzMap ℝ ℂ) :
    conjugateL2 (φ.toLp 2) =
      (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap).toLp 2 := by
  apply Lp.ext
  filter_upwards [conjugateL2_coe (φ.toLp 2), φ.coeFn_toLp 2,
    (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap).coeFn_toLp 2] with x ha hb hc
  simp only [ha, hb, hc, SchwartzMap.postcompCLM_apply]
  rfl

lemma fourier_conjugate_schwartz (φ : SchwartzMap ℝ ℂ) :
    FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      (φ.postcompCLM Complex.conjCLE.toContinuousLinearMap) =
    (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ) φ).postcompCLM
      Complex.conjCLE.toContinuousLinearMap := by
  ext ξ
  rw [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe,
    SchwartzMap.postcompCLM_apply, FourierTransform.fourierInvCLM_apply,
    SchwartzMap.fourierInv_coe, Real.fourier_eq', Real.fourierInv_eq']
  change (∫ x : ℝ, _ * star (φ x)) = star (∫ x : ℝ, _ * φ x)
  simp only [RCLike.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma fourier_conjugate (f : ComplexL2) :
    lineFourier (conjugateL2 f) = conjugateL2 (lineFourier.symm f) := by
  let P : ComplexL2 → Prop := fun f =>
    lineFourier (conjugateL2 f) = conjugateL2 (lineFourier.symm f)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact lineFourier.continuous.comp conjugateL2.continuous
    · exact conjugateL2.continuous.comp lineFourier.symm.continuous
  intro φ
  change lineFourier (conjugateL2 (φ.toLp 2)) = conjugateL2 (lineFourier.symm (φ.toLp 2))
  rw [conjugateL2_schwartz]
  change FourierTransform.fourier
    ((φ.postcompCLM Complex.conjCLE.toContinuousLinearMap).toLp 2) =
    conjugateL2 (FourierTransform.fourierInv (φ.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq, conjugateL2_schwartz]
  exact congrArg (fun ψ : SchwartzMap ℝ ℂ => ψ.toLp 2) (fourier_conjugate_schwartz φ)

/-- Reflection of the physical or frequency variable. -/
def reflectL2 : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ Neg.neg (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma reflectL2_coe (f : ComplexL2) :
    (reflectL2 f : ℝ → ℂ) =ᵐ[volume] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

lemma reflectL2_schwartz (φ : SchwartzMap ℝ ℂ) :
    reflectL2 (φ.toLp 2) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)) φ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [reflectL2_coe (φ.toLp 2),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae (φ.coeFn_toLp 2 volume),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)) φ).coeFn_toLp 2 volume] with x ha hb hc
  rw [ha, hb, hc]
  rfl

lemma inverseFourier_eq_reflect (f : ComplexL2) :
    lineFourier.symm f = reflectL2 (lineFourier f) := by
  let P : ComplexL2 → Prop := fun f =>
    lineFourier.symm f = reflectL2 (lineFourier f)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · apply isClosed_eq lineFourier.symm.continuous
      (reflectL2.continuous.comp lineFourier.continuous)
  intro φ
  change FourierTransform.fourierInv (φ.toLp 2) = reflectL2 (FourierTransform.fourier (φ.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq, reflectL2_schwartz]
  rfl

lemma multiplier_conj_neg (ξ : ℝ) : multiplier ξ = star (multiplier (-ξ)) := by
  by_cases hz : ξ = 0
  · simp [hz, multiplier]
  · by_cases hp : 0 < ξ
    · simp [multiplier, hz, neg_ne_zero.mpr hz, hp, not_lt.mpr (by linarith : -ξ ≤ 0)]
    · have hn : 0 < -ξ := by grind
      simp [multiplier, hz, neg_ne_zero.mpr hz, hp, hn]

lemma frequencyAction_hermitian (f : ComplexL2) :
    frequencyAction (conjugateL2 (reflectL2 f)) =
      conjugateL2 (reflectL2 (frequencyAction f)) := by
  apply Lp.ext
  filter_upwards [frequencyAction_coe (conjugateL2 (reflectL2 f)),
    conjugateL2_coe (reflectL2 f), reflectL2_coe f,
    conjugateL2_coe (reflectL2 (frequencyAction f)), reflectL2_coe (frequencyAction f),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (frequencyAction_coe f)] with ξ ha hb hc hd he hf
  rw [ha, hb, hc, hd, he, hf, star_mul, ← multiplier_conj_neg]
  exact mul_comm _ _

lemma conjugate_commutes (f : ComplexL2) :
    complexHilbert (conjugateL2 f) = conjugateL2 (complexHilbert f) := by
  apply lineFourier.injective
  rw [complexHilbert, lineFourier.apply_symm_apply, fourier_conjugate,
    inverseFourier_eq_reflect, frequencyAction_hermitian]
  rw [fourier_conjugate, inverseFourier_eq_reflect,
    complexHilbert, lineFourier.apply_symm_apply]

lemma conjugateL2_eq_iff (f : ComplexL2) :
    conjugateL2 f = f ↔ ∀ᵐ x : ℝ ∂volume, (f x).im = 0 := by
  constructor
  · intro h
    filter_upwards [conjugateL2_coe f] with x hx
    rw [h] at hx
    have hi := congrArg Complex.im hx
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  · intro h
    apply Lp.ext
    filter_upwards [conjugateL2_coe f, h] with x hx hi
    rw [hx]
    apply Complex.ext <;> simp [hi]

theorem real_valued_preservation :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.RealValuedPreservation := by
  intro f hf
  apply (conjugateL2_eq_iff _).1
  rw [← conjugate_commutes, (conjugateL2_eq_iff f).2 hf]

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma complexify_coe (f : RealL2) :
    (complexify 2 f : ℝ → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma complexify_norm (f : RealL2) : ‖complexify 2 f‖ = ‖f‖ := by
  have hn : ∀ᵐ x : ℝ ∂volume, ‖complexify 2 f x‖ = ‖f x‖ := by
    filter_upwards [complexify_coe f] with x hx
    rw [hx, Complex.norm_real]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.ge))

/-- The real part, on actual L² equivalence classes. -/
def realPartL2 : ComplexL2 →L[ℝ] RealL2 := Complex.reCLM.compLpL 2 volume

lemma realPartL2_coe (f : ComplexL2) :
    (realPartL2 f : ℝ → ℝ) =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma complexify_realPart (f : ComplexL2) (hf : ∀ᵐ x : ℝ ∂volume, (f x).im = 0) :
    complexify 2 (realPartL2 f) = f := by
  apply Lp.ext
  filter_upwards [complexify_coe (realPartL2 f), realPartL2_coe f, hf] with x ha hb hc
  rw [ha, hb]
  apply Complex.ext <;> simp [hc]

/-- The real operator is obtained by restricting the complex multiplier. -/
def realOperator : RealL2 →L[ℝ] RealL2 :=
  realPartL2.comp ((operator.restrictScalars ℝ).comp
    (Specs.ExpandedFA.SingularIntegrals.HilbertTransform.complexify 2))

theorem real_restriction :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.IsRealRestriction realOperator := by
  intro f
  apply (complexify_realPart _ ?_).symm
  apply real_valued_preservation
  filter_upwards [complexify_coe f] with x hx
  simp [hx]

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma complexify_injective : Function.Injective (complexify 2) := by
  intro f g h
  apply Lp.ext
  have he := Lp.ext_iff.mp h
  filter_upwards [complexify_coe f, complexify_coe g, he] with x hf hg he
  rw [hf, hg] at he
  exact Complex.ofReal_injective he

theorem real_isometry (f : RealL2) : ‖realOperator f‖ = ‖f‖ := by
  rw [← complexify_norm (realOperator f), ← real_restriction, isometry, complexify_norm]

theorem real_square (f : RealL2) : realOperator (realOperator f) = -f := by
  apply complexify_injective
  rw [← real_restriction, ← real_restriction, square, map_neg]

theorem truncated_integrability :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.TruncatedIntegrability :=
  fun 𝕜 _ _ hε f x => truncated_integrable 𝕜 hε f x

theorem real_l2_properties :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.RealL2Properties :=
  ⟨realOperator, real_restriction, real_isometry, real_square⟩

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma kernelFunction_eq (𝕜 : Type) [RCLike 𝕜] :
    kernelFunction 𝕜 = fun x =>
      ((Real.pi⁻¹ * (lineIsometry.symm x)⁻¹ : ℝ) : 𝕜) := by
  ext x
  simp [kernelFunction, RCLike.ofReal_mul, mul_inv_rev, mul_comm]

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma kernelFunction_contDiff (𝕜 : Type) [RCLike 𝕜] :
    ContDiffOn ℝ 1 (kernelFunction 𝕜) ({0}ᶜ : Set (ExpandedFA.Fourier.Euclidean 1)) := by
  rw [kernelFunction_eq]
  apply (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn
  apply contDiffOn_const.mul
  apply lineIsometry.symm.toContinuousLinearEquiv.contDiff.contDiffOn.inv
  intro x hx
  exact fun h => hx (lineIsometry.symm.injective (h.trans (map_zero _).symm))

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma kernelFunction_fderiv (𝕜 : Type) [RCLike 𝕜]
    (x : ExpandedFA.Fourier.Euclidean 1) (hx : x ≠ 0) :
    fderiv ℝ (kernelFunction 𝕜) x =
      RCLike.ofRealCLM.comp
        ((Real.pi⁻¹ * (-(lineIsometry.symm x ^ 2)⁻¹)) •
          lineIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have ht : lineIsometry.symm x ≠ 0 := by
    exact fun h => hx (lineIsometry.symm.injective (h.trans (map_zero _).symm))
  have hd := ((hasDerivAt_inv ht).comp_hasFDerivAt x
    lineIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).const_mul Real.pi⁻¹
  have he := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp x hd
  rw [kernelFunction_eq]
  simpa only [Function.comp_def, smul_smul, RCLike.ofRealCLM_apply] using he.fderiv

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma kernelFunction_norm (𝕜 : Type) [RCLike 𝕜] (x : ExpandedFA.Fourier.Euclidean 1) :
    ‖kernelFunction 𝕜 x‖ = Real.pi⁻¹ / ‖x‖ := by
  rw [kernelFunction, norm_inv, RCLike.norm_ofReal, abs_mul, abs_of_pos Real.pi_pos,
    ← Real.norm_eq_abs (lineIsometry.symm x), lineIsometry.symm.norm_map]
  simp [mul_inv_rev, div_eq_mul_inv, mul_comm]

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma kernelFunction_gradient (𝕜 : Type) [RCLike 𝕜]
    (x : ExpandedFA.Fourier.Euclidean 1) (hx : x ≠ 0) :
    StandardConvolution.kernelGradientNorm (kernelFunction 𝕜) x = Real.pi⁻¹ / ‖x‖ ^ 2 := by
  unfold StandardConvolution.kernelGradientNorm
  rw [Fintype.sum_unique, kernelFunction_fderiv 𝕜 x hx]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    RCLike.ofRealCLM_apply, smul_eq_mul, RCLike.norm_ofReal,
    abs_mul, abs_inv, abs_neg, abs_pow, abs_of_pos Real.pi_pos,
    ← Real.norm_eq_abs, lineIsometry.symm.norm_map]
  rw [Real.sqrt_sq_eq_abs]
  simp [div_eq_mul_inv, abs_of_nonneg (norm_nonneg x), abs_of_pos Real.pi_pos]

/-- The same transported kernel in the shared real/complex CZ interface. -/
def standardKernel (𝕜 : Type) [RCLike 𝕜] : StandardConvolution.StandardKernel 𝕜 1 where
  function := Specs.ExpandedFA.SingularIntegrals.HilbertTransform.kernelFunction 𝕜
  contDiff := kernelFunction_contDiff 𝕜
  constant := Real.pi⁻¹
  constant_nonneg := inv_nonneg.mpr Real.pi_pos.le
  size x hx := by simp [kernelFunction_norm]
  gradient x hx := by simp [kernelFunction_gradient 𝕜 x hx]

theorem standard_kernel_bounds :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.StandardKernelBounds :=
  fun 𝕜 _ => ⟨standardKernel 𝕜, rfl⟩

/-- Translation on the ordinary real line. -/
def translateL2 (a : ℝ) : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x - a) (measurePreserving_sub_right volume a)

lemma translateL2_coe (a : ℝ) (f : ComplexL2) :
    (translateL2 a f : ℝ → ℂ) =ᵐ[volume] fun x => f (x - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

private def phase (a ξ : ℝ) : ℂ := (Real.fourierChar (inner ℝ (-a) ξ) : ℂ)

private lemma phase_continuous (a : ℝ) : Continuous (phase a) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_const.inner continuous_id))

private lemma phase_memLp (a : ℝ) (f : ComplexL2) :
    MemLp (fun ξ => phase a ξ * f ξ) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).of_le
    ((phase_continuous a).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact .of_forall fun ξ => by simp [phase]

private def phaseAction (a : ℝ) (f : ComplexL2) : ComplexL2 :=
  (phase_memLp a f).toLp _

private lemma phaseAction_coe (a : ℝ) (f : ComplexL2) :
    (phaseAction a f : ℝ → ℂ) =ᵐ[volume] fun ξ => phase a ξ * f ξ :=
  (phase_memLp a f).coeFn_toLp

private lemma phaseAction_isometry (a : ℝ) : Isometry (phaseAction a) := by
  intro f g
  simp only [edist_dist, dist_eq_norm]
  congr 1
  have hn : ∀ᵐ ξ : ℝ ∂volume,
      ‖(phaseAction a f - phaseAction a g) ξ‖ = ‖(f - g) ξ‖ := by
    filter_upwards [Lp.coeFn_sub (phaseAction a f) (phaseAction a g),
      Lp.coeFn_sub f g, phaseAction_coe a f, phaseAction_coe a g] with ξ ha hb hc hd
    simp only [ha, hb, Pi.sub_apply, hc, hd, ← mul_sub, norm_mul, phase, Circle.norm_coe, one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h => h.ge))

private lemma fourier_translate_schwartz (a : ℝ) (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (φ.compSubConstCLM ℂ a)) ξ =
    phase a ξ * (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) φ) ξ := by
  rw [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe,
    FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun x => φ (x - a)) ξ = phase a ξ *
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) φ ξ
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) (φ : ℝ → ℂ) (-a)) ξ
  simpa only [Function.comp_def, sub_eq_add_neg, phase, innerₗ_apply_apply, Circle.smul_def, smul_eq_mul] using h

private lemma fourier_translate (a : ℝ) (f : ComplexL2) :
    lineFourier (translateL2 a f) = phaseAction a (lineFourier f) := by
  let P : ComplexL2 → Prop := fun f =>
    lineFourier (translateL2 a f) = phaseAction a (lineFourier f)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (lineFourier.continuous.comp (translateL2 a).continuous)
      ((phaseAction_isometry a).continuous.comp lineFourier.continuous)
  intro φ
  have hτ : translateL2 a (φ.toLp 2) = (φ.compSubConstCLM ℂ a).toLp 2 := by
    apply Lp.ext
    filter_upwards [translateL2_coe a (φ.toLp 2),
      (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae
        (φ.coeFn_toLp 2 volume), (φ.compSubConstCLM ℂ a).coeFn_toLp 2 volume] with x ha hb hc
    rw [ha, hb, hc]
    rfl
  change lineFourier (translateL2 a (φ.toLp 2)) = phaseAction a (lineFourier (φ.toLp 2))
  rw [hτ]
  change FourierTransform.fourier ((φ.compSubConstCLM ℂ a).toLp 2) =
    phaseAction a (FourierTransform.fourier (φ.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [phaseAction_coe a ((FourierTransform.fourierCLM ℂ _ φ).toLp 2),
    (FourierTransform.fourierCLM ℂ _ φ).coeFn_toLp 2 volume,
    (FourierTransform.fourierCLM ℂ _ (φ.compSubConstCLM ℂ a)).coeFn_toLp 2 volume]
    with ξ ha hb hc
  simp only [FourierTransform.fourierCLM_apply] at ha hb hc
  rw [ha, hb, hc]
  exact fourier_translate_schwartz a φ ξ

private lemma frequencyAction_phaseAction (a : ℝ) (f : ComplexL2) :
    frequencyAction (phaseAction a f) = phaseAction a (frequencyAction f) := by
  apply Lp.ext
  filter_upwards [frequencyAction_coe (phaseAction a f), phaseAction_coe a f,
    phaseAction_coe a (frequencyAction f), frequencyAction_coe f] with ξ ha hb hc hd
  rw [ha, hb, hc, hd]
  ring

lemma hilbert_translate (a : ℝ) (f : ComplexL2) :
    complexHilbert (translateL2 a f) = translateL2 a (complexHilbert f) := by
  apply lineFourier.injective
  rw [complexHilbert, lineFourier.apply_symm_apply, fourier_translate,
    frequencyAction_phaseAction, fourier_translate, complexHilbert, lineFourier.apply_symm_apply]

theorem complex_translation_invariant :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.LineTranslationInvariant ℂ complexHilbert := by
  intro a f g hfg
  have hg : g = translateL2 a f := Lp.ext (hfg.trans (translateL2_coe a f).symm)
  rw [hg, hilbert_translate]
  exact translateL2_coe a (complexHilbert f)

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
theorem real_translation_invariant : LineTranslationInvariant ℝ realOperator := by
  intro a f g hfg
  have hfgC : (complexify 2 g : ℝ → ℂ) =ᵐ[volume]
      fun x => (complexify 2 f) (x - a) := by
    filter_upwards [hfg, complexify_coe g,
      (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae
        (complexify_coe f)] with x ha hb hc
    rw [hb, hc, ha]
  have ht := complex_translation_invariant a (complexify 2 f) (complexify 2 g) hfgC
  rw [real_restriction, real_restriction] at ht
  filter_upwards [ht, complexify_coe (realOperator g),
    (measurePreserving_sub_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae
      (complexify_coe (realOperator f))] with x ha hb hc
  rw [hb, hc] at ha
  exact Complex.ofReal_injective ha

theorem translation_properties :
    Specs.ExpandedFA.SingularIntegrals.HilbertTransform.TranslationProperties :=
  ⟨complex_translation_invariant, realOperator, real_restriction, real_translation_invariant⟩

open Specs.ExpandedFA.SingularIntegrals.HilbertTransform in
lemma truncated_ofReal (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    truncated ε (fun t => (f t : ℂ)) x = ((truncated (𝕜 := ℝ) ε f x : ℝ) : ℂ) := by
  unfold truncated
  simpa [RCLike.ofReal] using
    (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ).restrict {t : ℝ | ε < |t|})
      (f := fun t => (Real.pi * t)⁻¹ * f (x - t)))

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

private def toEuclideanL (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    LineLp 𝕜 p →L[𝕜] Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1)) :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 lineIsometry.symm lineIsometry.symm.measurePreserving).toContinuousLinearMap

private def fromEuclideanL (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1)) →L[𝕜] LineLp 𝕜 p :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 lineIsometry lineIsometry.measurePreserving).toContinuousLinearMap

lemma fromEuclidean_coe {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞)
    (f : Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1))) :
    (fromEuclidean p f : ℝ → 𝕜) =ᵐ[volume] fun x => f (lineIsometry x) :=
  Lp.coeFn_compMeasurePreserving f lineIsometry.measurePreserving

private lemma fromEuclidean_ae_eq {𝕜 : Type} [RCLike 𝕜] (p q : ℝ≥0∞)
    (f : Lp 𝕜 p (volume : Measure (StandardConvolution.Space 1)))
    (g : Lp 𝕜 q (volume : Measure (StandardConvolution.Space 1)))
    (h : (f : StandardConvolution.Space 1 → 𝕜) =ᵐ[volume] (g : StandardConvolution.Space 1 → 𝕜)) :
    (fromEuclidean p f : ℝ → 𝕜) =ᵐ[volume] (fromEuclidean q g : ℝ → 𝕜) := by
  filter_upwards [fromEuclidean_coe p f, fromEuclidean_coe q g,
    lineIsometry.measurePreserving.quasiMeasurePreserving.ae h] with x ha hb hc
  rw [ha, hb, hc]

private def measurablePullback (𝕜 : Type) [RCLike 𝕜] :
    CZWeak.MeasurableClasses 𝕜 1 →ₗ[𝕜] (ℝ →ₘ[(volume : Measure ℝ)] 𝕜) where
  toFun f := f.compMeasurePreserving lineIsometry lineIsometry.measurePreserving
  map_add' f g := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_compMeasurePreserving (f + g) lineIsometry.measurePreserving,
      AEEqFun.coeFn_add (f.compMeasurePreserving lineIsometry lineIsometry.measurePreserving)
        (g.compMeasurePreserving lineIsometry lineIsometry.measurePreserving),
      AEEqFun.coeFn_compMeasurePreserving f lineIsometry.measurePreserving,
      AEEqFun.coeFn_compMeasurePreserving g lineIsometry.measurePreserving,
      lineIsometry.measurePreserving.quasiMeasurePreserving.ae (AEEqFun.coeFn_add f g)]
      with x ha hb hc hd he
    simp only [Function.comp_apply] at ha hc hd he
    simp only [Pi.add_apply] at hb he
    rw [ha, hb, hc, hd, he]
  map_smul' c f := by
    apply AEEqFun.ext
    filter_upwards [AEEqFun.coeFn_compMeasurePreserving (c • f) lineIsometry.measurePreserving,
      AEEqFun.coeFn_smul c (f.compMeasurePreserving lineIsometry lineIsometry.measurePreserving),
      AEEqFun.coeFn_compMeasurePreserving f lineIsometry.measurePreserving,
      lineIsometry.measurePreserving.quasiMeasurePreserving.ae (AEEqFun.coeFn_smul c f)]
      with x ha hb hc hd
    simp only [Function.comp_apply] at ha hc hd
    change _ = (c • f.compMeasurePreserving lineIsometry lineIsometry.measurePreserving) x
    simp only [Pi.smul_apply] at hb hd
    rw [ha, hb, hc, hd]

private lemma measurablePullback_coe {𝕜 : Type} [RCLike 𝕜]
    (f : CZWeak.MeasurableClasses 𝕜 1) :
    (measurablePullback 𝕜 f : ℝ → 𝕜) =ᵐ[volume] fun x => f (lineIsometry x) :=
  AEEqFun.coeFn_compMeasurePreserving f lineIsometry.measurePreserving

/-- Transporting the actual shared CZ extensions preserves all intersections
and the weak estimate, with the same constant. -/
theorem extensions_of_standard_realization (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (hA : HasStandardRealization 𝕜 A) :
    Nonempty (Extensions 𝕜 A) := by
  obtain ⟨T, _, _, hT⟩ := hA
  obtain ⟨S, hS, hpair, hSW⟩ := CZLp.compatible_family 𝕜 1 T
  obtain ⟨W, hW, _⟩ := CZWeak.unique_extension 𝕜 1 T
  let strong : ∀ p : CZLp.InteriorExponent, LineLp 𝕜 p.val →L[𝕜] LineLp 𝕜 p.val :=
    fun p => (fromEuclideanL 𝕜 p.val).comp ((S p).comp (toEuclideanL 𝕜 p.val))
  let weak : LineLp 𝕜 1 →ₗ[𝕜] (ℝ →ₘ[(volume : Measure ℝ)] 𝕜) :=
    (measurablePullback 𝕜).comp (W.comp (toEuclideanL 𝕜 1).toLinearMap)
  have hstrong (p : CZLp.InteriorExponent) (f : ℝ → 𝕜) (hp : MemLp f p.val volume) :
      strong p (hp.toLp f) =
      fromEuclidean p.val (S p ((hp.comp_measurePreserving lineIsometry.symm.measurePreserving).toLp
        (fun x => f (lineIsometry.symm x)))) := rfl
  have hweak (f : ℝ → 𝕜) (h1 : MemLp f 1 volume) :
      weak (h1.toLp f) = measurablePullback 𝕜
        (W ((h1.comp_measurePreserving lineIsometry.symm.measurePreserving).toLp
          (fun x => f (lineIsometry.symm x)))) := rfl
  have hweak_strong (p : CZLp.InteriorExponent) (f : ℝ → 𝕜)
      (h1 : MemLp f 1 volume) (hp : MemLp f p.val volume) :
      (weak (h1.toLp f) : ℝ → 𝕜) =ᵐ[volume] (strong p (hp.toLp f) : ℝ → 𝕜) := by
    rw [hweak, hstrong]
    have he := hSW W hW p (fun x => f (lineIsometry.symm x))
      (h1.comp_measurePreserving lineIsometry.symm.measurePreserving)
      (hp.comp_measurePreserving lineIsometry.symm.measurePreserving)
    filter_upwards [measurablePullback_coe (W ((h1.comp_measurePreserving lineIsometry.symm.measurePreserving).toLp
        (fun x => f (lineIsometry.symm x)))), fromEuclidean_coe p.val
        (S p ((hp.comp_measurePreserving lineIsometry.symm.measurePreserving).toLp
          (fun x => f (lineIsometry.symm x)))),
      lineIsometry.measurePreserving.quasiMeasurePreserving.ae he] with x ha hb hc
    exact ha.trans (hc.symm.trans hb.symm)
  refine ⟨{ strong := strong
            weak := weak
            strong_agrees := ?_
            pairwise_agrees := ?_
            weak_agrees := ?_
            weak_strong_agrees := hweak_strong
            weak_bound := ?_ }⟩
  · intro p f hp h2
    rw [hstrong, ← hT]
    exact fromEuclidean_ae_eq _ _ _ _ (hS p (fun x => f (lineIsometry.symm x))
      (hp.comp_measurePreserving lineIsometry.symm.measurePreserving)
      (h2.comp_measurePreserving lineIsometry.symm.measurePreserving))
  · intro p q f hp hq
    rw [hstrong, hstrong]
    exact fromEuclidean_ae_eq _ _ _ _ (hpair p q (fun x => f (lineIsometry.symm x))
      (hp.comp_measurePreserving lineIsometry.symm.measurePreserving)
      (hq.comp_measurePreserving lineIsometry.symm.measurePreserving))
  · intro f h1 h2
    rw [hweak, ← hT]
    have he := hW.1 (fun x => f (lineIsometry.symm x))
      (h1.comp_measurePreserving lineIsometry.symm.measurePreserving)
      (h2.comp_measurePreserving lineIsometry.symm.measurePreserving)
    filter_upwards [measurablePullback_coe (W ((h1.comp_measurePreserving lineIsometry.symm.measurePreserving).toLp
        (fun x => f (lineIsometry.symm x)))),
      fromEuclidean_coe 2 (T.operator (toEuclidean 2 (h2.toLp f))),
      lineIsometry.measurePreserving.quasiMeasurePreserving.ae he] with x ha hb hc
    rw [ha, hb, hc]
    rfl
  · obtain ⟨B, hB, hbound⟩ := hW.2
    refine ⟨B, hB, fun f t ht => ?_⟩
    have he : (weak f : ℝ → 𝕜) =ᵐ[volume]
        fun x => W (toEuclidean 1 f) (lineIsometry x) := measurablePullback_coe _
    calc
      volume {x : ℝ | t < ‖weak f x‖} =
          volume (lineIsometry ⁻¹' {x | t < ‖W (toEuclidean 1 f) x‖}) := by
        apply measure_congr
        filter_upwards [he] with x hx
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, hx]
      _ = volume {x | t < ‖W (toEuclidean 1 f) x‖} :=
        lineIsometry.measurePreserving.measure_preimage_emb
          lineIsometry.toHomeomorph.measurableEmbedding _
      _ ≤ ENNReal.ofReal (B / t) * ENNReal.ofReal ‖toEuclidean 1 f‖ :=
        hbound _ t ht
      _ = ENNReal.ofReal (B / t) * ENNReal.ofReal ‖f‖ := by
        rw [Specs.ExpandedFA.SingularIntegrals.HilbertTransform.toEuclidean, Lp.norm_compMeasurePreserving]

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform

def hardSoftDifference (t : ℝ) : ℝ :=
  (if 1 < |t| then (Real.pi * t)⁻¹ else 0) -
    t / (Real.pi * (1 + t ^ 2))

lemma hardSoftDifference_measurable : Measurable hardSoftDifference := by
  unfold hardSoftDifference
  apply Measurable.sub
  · apply Measurable.ite (isOpen_lt continuous_const continuous_abs).measurableSet
    · fun_prop
    · exact measurable_const
  · fun_prop

lemma hardSoftDifference_bound (t : ℝ) :
    |hardSoftDifference t| ≤ Real.pi⁻¹ * (1 + t ^ 2)⁻¹ := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hd : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : 1 < |t|
  · have ht0 : t ≠ 0 := by intro h; simp [h] at ht; linarith
    have heq : hardSoftDifference t = (Real.pi * t * (1 + t ^ 2))⁻¹ := by
      simp only [hardSoftDifference, ite_eq_left ht]
      field_simp
      <;> ring
    rw [heq, abs_inv, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hd]
    rw [← mul_inv]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    calc
      Real.pi * (1 + t ^ 2) = (Real.pi * 1) * (1 + t ^ 2) := by ring
      _ ≤ (Real.pi * |t|) * (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.le hp.le) hd.le
  · have ht' : |t| ≤ 1 := le_of_not_gt ht
    simp only [hardSoftDifference, ite_eq_right ht, zero_sub, abs_neg, abs_div,
      abs_mul, abs_of_pos hp, abs_of_pos hd]
    rw [← mul_inv, ← one_div]
    exact (div_le_div_iff_of_pos_right (mul_pos hp hd)).2 ht'

lemma hardSoftDifference_integrable : Integrable hardSoftDifference := by
  apply (integrable_inv_one_add_sq.const_mul Real.pi⁻¹).mono'
    hardSoftDifference_measurable.aestronglyMeasurable
  exact .of_forall hardSoftDifference_bound

lemma hardSoftDifference_odd (t : ℝ) :
    hardSoftDifference (-t) = -hardSoftDifference t := by
  unfold hardSoftDifference
  simp only [abs_neg, neg_sq, mul_neg, inv_neg, neg_div]
  split_ifs <;> ring

lemma hardSoftDifference_integral : ∫ t : ℝ, hardSoftDifference t = 0 := by
  have h := integral_neg_eq_self hardSoftDifference volume
  simp only [hardSoftDifference_odd, integral_neg] at h
  linarith

lemma cutKernel_sub_regularized {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    cutKernel ℝ ε t - t / (Real.pi * (t ^ 2 + ε ^ 2)) =
      ε⁻¹ * hardSoftDifference (t / ε) := by
  have hc : 1 < |t / ε| ↔ ε < |t| := by
    rw [abs_div, abs_of_pos hε, one_lt_div hε]
  have hd : t ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have hd' : 1 + (t / ε) ^ 2 ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases ht : ε < |t|
  · have ht0 : t ≠ 0 := by intro h; simp [h] at ht; linarith
    simp only [cutKernel, RCLike.ofReal_real_eq_id, id_eq, hardSoftDifference, ite_eq_left ht, ite_eq_left (hc.mpr ht)]
    field_simp
    <;> ring
  · simp only [cutKernel, RCLike.ofReal_real_eq_id, id_eq, hardSoftDifference, ite_eq_right ht,
      ite_eq_right (mt hc.mp ht), zero_sub]
    field_simp
    <;> ring

lemma cutKernel_sub_regularized_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t : ℝ => cutKernel ℝ ε t - t / (Real.pi * (t ^ 2 + ε ^ 2))) := by
  simp_rw [cutKernel_sub_regularized hε]
  exact (hardSoftDifference_integrable.comp_div hε.ne').const_mul _

lemma cutKernel_sub_regularized_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, cutKernel ℝ ε t - t / (Real.pi * (t ^ 2 + ε ^ 2))) = 0 := by
  simp_rw [cutKernel_sub_regularized hε]
  rw [integral_const_mul, Measure.integral_comp_div, hardSoftDifference_integral]
  simp

lemma translateL2_continuous (f : ComplexL2) : Continuous (fun a : ℝ => translateL2 a f) := by
  let g : ℝ → C(ℝ, ℝ) := fun a => ⟨fun x => x - a, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_sub_right volume a) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

lemma translateL2_zero (f : ComplexL2) : translateL2 0 f = f := by
  apply Lp.ext
  filter_upwards [translateL2_coe 0 f] with x hx
  simpa using hx

/-- The zero-mean L¹ correction tends to zero in the L² norm. -/
lemma hardSoftDifference_L2_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, hardSoftDifference t • translateL2 (ε * t) f)
      (𝓝 0) (𝓝 (0 : ComplexL2)) := by
  have hi (ε : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => hardSoftDifference t • translateL2 (ε * t) f) volume :=
    hardSoftDifference_measurable.aestronglyMeasurable.smul
      ((translateL2_continuous f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hb (ε t : ℝ) : ‖hardSoftDifference t • translateL2 (ε * t) f‖ ≤
      |hardSoftDifference t| * ‖f‖ := by
    rw [norm_smul, (translateL2 (ε * t)).norm_map, Real.norm_eq_abs]
  have hh : Tendsto
      (fun ε : ℝ => ∫ t : ℝ, hardSoftDifference t • translateL2 (ε * t) f)
      (𝓝 0) (𝓝 (∫ t : ℝ, hardSoftDifference t • f)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t => |hardSoftDifference t| * ‖f‖)
    · exact .of_forall hi
    · exact .of_forall fun ε => .of_forall (hb ε)
    · exact hardSoftDifference_integrable.norm.mul_const _
    · exact .of_forall fun t => by
        have ht := ((translateL2_continuous f).comp (continuous_id.mul_const t)).tendsto 0
        simpa only [Function.comp_apply, id_eq, zero_mul, translateL2_zero] using (tendsto_const_nhds (x := hardSoftDifference t)).smul ht
  simpa only [integral_smul_const, hardSoftDifference_integral, zero_smul] using hh

lemma normalized_dampedSign_norm_le (ε : ℝ) (hε : 0 ≤ ε) (ξ : ℝ) :
    ‖(Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * Real.pi := mul_le_mul_of_nonneg_left
      (PrincipalValue.dampedSign_bound ε hε ξ) (by positivity)
    _ = 1 := inv_mul_cancel₀ Real.pi_ne_zero

lemma normalized_dampedSign_tendsto (ξ : ℝ) (hξ : ξ ≠ 0) :
    Tendsto (fun ε : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ)
      (𝓝 0) (𝓝 (multiplier ξ)) := by
  have hc : ContinuousAt
      (fun ε : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ) 0 := by
    unfold PrincipalValue.dampedSign
    split_ifs <;> fun_prop
  convert hc.tendsto using 1
  unfold PrincipalValue.dampedSign multiplier
  by_cases hp : 0 < ξ
  · simp [hξ, hp, not_le.mpr hp, mul_left_comm, mul_assoc, Real.pi_ne_zero]
  · simp [hξ, hp, le_of_not_gt hp, mul_left_comm, mul_assoc, Real.pi_ne_zero]

/-- Dominated convergence on frequency space for the genuine soft multiplier. -/
lemma softMultiplier_L2_error_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ => ∫ ξ : ℝ,
      ‖(Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ - multiplier ξ * f ξ‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hh : Tendsto (fun ε : ℝ => ∫ ξ : ℝ,
      ‖(Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ - multiplier ξ * f ξ‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∫ ξ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ => 4 * ‖f ξ‖ ^ 2)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (((aestronglyMeasurable_const.mul
        (PrincipalValue.dampedSign_integrable ε hε).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable f)).sub
        (multiplier_measurable.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))).norm.pow 2
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      apply Filter.Eventually.of_forall
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hfirst : ‖(Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ‖ ≤ ‖f ξ‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (normalized_dampedSign_norm_le ε hε.le ξ)
      have hsecond : ‖multiplier ξ * f ξ‖ ≤ ‖f ξ‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le ξ)
      have hx := (norm_sub_le ((Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ)
        (multiplier ξ * f ξ)).trans (add_le_add hfirst hsecond)
      nlinarith [norm_nonneg ((Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ -
        multiplier ξ * f ξ), norm_nonneg (f ξ)]
    · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
        (Lp.memLp f)).const_mul 4
    · filter_upwards [volume.ae_ne (0 : ℝ)] with ξ hξ
      have ht := (((normalized_dampedSign_tendsto ξ hξ).mul_const (f ξ)).sub_const
        (multiplier ξ * f ξ)).norm.pow 2
      simpa using ht.mono_left nhdsWithin_le_nhds
  simpa using hh

lemma lineL2_norm_sq (g : ComplexL2) : ‖g‖ ^ 2 = ∫ ξ : ℝ, ‖g ξ‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ _ _ _]
  rw [L2.inner_def, ← integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) g g)]
  simp only [inner_self_eq_norm_sq]

lemma softFrequency_memLp (ε : ℝ) (f : ComplexL2) :
    MemLp (fun ξ : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign (max ε 0) ξ * f ξ)
      2 volume := by
  have hm : Measurable (PrincipalValue.dampedSign (max ε 0)) := by
    unfold PrincipalValue.dampedSign
    apply Measurable.ite measurableSet_Iic <;> fun_prop
  apply (Lp.memLp f).of_le
    ((aestronglyMeasurable_const.mul hm.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f))
  exact .of_forall fun ξ => by
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (normalized_dampedSign_norm_le _ (le_max_right _ _) ξ)

def softFrequencyAction (ε : ℝ) (f : ComplexL2) : ComplexL2 :=
  (softFrequency_memLp ε f).toLp _

lemma softFrequencyAction_coe (ε : ℝ) (f : ComplexL2) :
    (softFrequencyAction ε f : ℝ → ℂ) =ᵐ[volume]
      (fun ξ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign (max ε 0) ξ * f ξ) :=
  (softFrequency_memLp ε f).coeFn_toLp

lemma softFrequencyAction_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ => softFrequencyAction ε f) (𝓝[>] 0) (𝓝 (frequencyAction f)) := by
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖softFrequencyAction ε f - frequencyAction f‖ ^ 2 = ∫ ξ : ℝ,
      ‖(Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ * f ξ - multiplier ξ * f ξ‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    rw [lineL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (softFrequencyAction ε f) (frequencyAction f),
      softFrequencyAction_coe ε f, frequencyAction_coe f] with ξ hs ha hb
    simp only [hs, Pi.sub_apply, ha, hb, max_eq_left hε.le]
  have hh : Tendsto (fun ε : ℝ => ‖softFrequencyAction ε f - frequencyAction f‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := (softMultiplier_L2_error_tendsto f).congr' (heq.mono fun _ h => h.symm)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

/-- An actual L² family tending strongly to the fixed Fourier Hilbert transform. -/
def softHilbert (ε : ℝ) (f : ComplexL2) : ComplexL2 :=
  lineFourier.symm (softFrequencyAction ε (lineFourier f))

lemma softHilbert_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ => softHilbert ε f) (𝓝[>] 0) (𝓝 (complexHilbert f)) :=
  lineFourier.symm.continuous.continuousAt.tendsto.comp
    (softFrequencyAction_tendsto (lineFourier f))

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform


lemma indicator_tail_lower {x : ℝ} (hx : 1 < x) :
    Real.pi⁻¹ * x⁻¹ ≤ indicatorImage x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxm : 0 < x - 1 := sub_pos.mpr hx
  have hq : 0 < x / (x-1) := div_pos hx0 hxm
  have hlog := Real.one_sub_inv_le_log_of_pos hq
  have hid : 1 - (x / (x - 1))⁻¹ = x⁻¹ := by
    field_simp
    ring
  rw [hid] at hlog
  unfold indicatorImage
  rw [abs_of_pos hq]
  exact mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr Real.pi_pos.le)

lemma indicatorImage_not_integrable : ¬ Integrable indicatorImage (volume : Measure ℝ) := by
  intro h
  have h' := (h.integrableOn : IntegrableOn indicatorImage (Ioi (1 : ℝ)))
  have hi : IntegrableOn (fun x : ℝ => Real.pi⁻¹ * x⁻¹) (Ioi (1 : ℝ)) := by
    apply h'.mono' (measurable_const.mul measurable_inv).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change |Real.pi⁻¹ * x⁻¹| ≤ indicatorImage x
    rw [abs_of_pos (mul_pos (inv_pos.mpr Real.pi_pos)
      (inv_pos.mpr (lt_trans zero_lt_one hx)))]
    exact indicator_tail_lower hx
  have hz : Real.pi⁻¹ ≠ 0 := inv_ne_zero Real.pi_ne_zero
  exact not_integrableOn_Ioi_inv ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hz) (fun x : ℝ => x⁻¹)).mp hi)
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform
lemma indicator_large_near_one (C : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (1 : ℝ) (1 + (Real.exp (Real.pi * (C + 1)))⁻¹)) :
    C < indicatorImage x := by
  have hp : 0 < Real.exp (Real.pi * (C + 1)) := Real.exp_pos _
  have hx0 : 0 < x := lt_trans zero_lt_one hx.1
  have hxm : 0 < x - 1 := sub_pos.mpr hx.1
  have hmul : Real.exp (Real.pi * (C+1)) * (x - 1) < 1 := by
    have he : x - 1 < (Real.exp (Real.pi * (C+1)))⁻¹ := by linarith [hx.2]
    simpa only [mul_inv_cancel₀ hp.ne'] using mul_lt_mul_of_pos_left he hp
  have hq : 0 < x / (x-1) := div_pos hx0 hxm
  have hlog : Real.pi * (C+1) < Real.log (x / (x-1)) := by
    apply (Real.lt_log_iff_exp_lt hq).2
    apply (lt_div_iff₀ hxm).2
    exact hmul.trans hx.1
  unfold indicatorImage
  rw [abs_of_pos hq]
  have hf := mul_lt_mul_of_pos_left hlog (inv_pos.mpr Real.pi_pos)
  have hp' : Real.pi⁻¹ * (Real.pi * (C + 1)) = C + 1 := by field_simp
  rw [hp'] at hf
  linarith

lemma indicatorImage_not_memLp_top : ¬ MemLp indicatorImage ∞ (volume : Measure ℝ) := by
  intro h
  have ht : eLpNormEssSup indicatorImage (volume : Measure ℝ) < ⊤ := by
    simpa only [eLpNorm_exponent_top h.aestronglyMeasurable] using h.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp ht
  have hi : (volume : Measure ℝ)
      (Ioo (1 : ℝ) (1 + (Real.exp (Real.pi * ((C : ℝ) + 1)))⁻¹)) ≠ 0 := by
    apply ne_of_gt
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    simp only [add_sub_cancel_left]
    exact inv_pos.mpr (Real.exp_pos _)
  obtain ⟨x, hx, hcx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hi (ae_restrict_of_ae hC)
  have hxlarge := indicator_large_near_one (C : ℝ) hx
  have hcx' : ‖indicatorImage x‖ ≤ (C : ℝ) := hcx
  exact (not_le.mpr hxlarge) ((le_abs_self _).trans hcx')
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma indicatorImage_measurable : Measurable indicatorImage := by
  unfold indicatorImage
  fun_prop

lemma indicatorImage_not_memLp_one (𝕜 : Type) [RCLike 𝕜] :
    ¬ MemLp (fun x : ℝ => (indicatorImage x : 𝕜)) 1 volume := by
  intro h
  have hr : MemLp indicatorImage 1 (volume : Measure ℝ) := by
    apply h.of_le indicatorImage_measurable.aestronglyMeasurable
    exact .of_forall fun x => by simp [Real.norm_eq_abs]
  exact indicatorImage_not_integrable (memLp_one_iff_integrable.mp hr)

lemma indicatorImage_not_memLp_infty (𝕜 : Type) [RCLike 𝕜] :
    ¬ MemLp (fun x : ℝ => (indicatorImage x : 𝕜)) ∞ volume := by
  intro h
  apply indicatorImage_not_memLp_top
  apply h.of_le indicatorImage_measurable.aestronglyMeasurable
  exact .of_forall fun x => by simp [Real.norm_eq_abs]

lemma endpointFailure_of_indicatorFormula (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (hF : IndicatorFormula 𝕜 A) :
    EndpointFailure 𝕜 A := by
  constructor
  · intro h
    exact indicatorImage_not_memLp_one 𝕜 ((memLp_congr_ae hF.1).mp h)
  · intro h
    exact indicatorImage_not_memLp_infty 𝕜 ((memLp_congr_ae hF.1).mp h)
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma complexify_coe_p (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : LineLp ℝ p) :
    (complexify p f : ℝ → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

lemma complexify_schwartz (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : SchwartzMap ℝ ℝ) :
    complexify p (φ.toLp p) = (φ.postcompCLM Complex.ofRealCLM).toLp p := by
  apply Lp.ext
  filter_upwards [complexify_coe_p p (φ.toLp p), φ.coeFn_toLp p,
    (φ.postcompCLM Complex.ofRealCLM).coeFn_toLp p] with x ha hb hc
  rw [ha, hb, hc]
  rfl

lemma extensions_strong_compatible
    (R : Extensions ℝ realOperator) (C : Extensions ℂ complexHilbert)
    (p : CZLp.InteriorExponent) (f : LineLp ℝ p.val) :
    C.strong p (complexify p.val f) = complexify p.val (R.strong p f) := by
  let P : LineLp ℝ p.val → Prop := fun f =>
    C.strong p (complexify p.val f) = complexify p.val (R.strong p f)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ) (p := p.val) p.lt_top.ne) f
  · apply isClosed_eq
    · exact (C.strong p).continuous.comp (complexify p.val).continuous
    · exact (complexify p.val).continuous.comp (R.strong p).continuous
  intro φ
  change C.strong p (complexify p.val (φ.toLp p.val)) =
    complexify p.val (R.strong p (φ.toLp p.val))
  rw [complexify_schwartz]
  let ψ := φ.postcompCLM Complex.ofRealCLM
  have hc := C.strong_agrees p ψ (ψ.memLp p.val volume) (ψ.memLp 2 volume)
  have hr := R.strong_agrees p φ (φ.memLp p.val volume) (φ.memLp 2 volume)
  have h2 : ψ.toLp 2 = complexify 2 (φ.toLp 2) := (complexify_schwartz 2 φ).symm
  change (C.strong p (ψ.toLp p.val) : ℝ → ℂ) =ᵐ[volume]
    (complexHilbert (ψ.toLp 2) : ℝ → ℂ) at hc
  change (R.strong p (φ.toLp p.val) : ℝ → ℝ) =ᵐ[volume]
    (realOperator (φ.toLp 2) : ℝ → ℝ) at hr
  rw [h2, real_restriction] at hc
  apply Lp.ext
  filter_upwards [hc, hr, complexify_coe_p p.val (R.strong p (φ.toLp p.val)),
    complexify_coe (realOperator (φ.toLp 2))] with x ha hb hc hd
  rw [ha, hd, hc, hb]



/-- The weak bound makes each extension continuous for convergence in measure. -/
lemma extensions_weak_tendstoInMeasure (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (E : Extensions 𝕜 A)
    (u : ℕ → LineLp 𝕜 1) (f : LineLp 𝕜 1) (hu : Tendsto u atTop (𝓝 f)) :
    TendstoInMeasure volume (fun n => (E.weak (u n) : ℝ → 𝕜)) atTop (E.weak f) := by
  obtain ⟨B, hB, hbound⟩ := E.weak_bound
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  have herr := (tendsto_iff_norm_sub_tendsto_zero.mp hu).const_mul (B / (δ / 2))
  have hupper : Tendsto (fun n => ENNReal.ofReal (B / (δ / 2)) *
      ENNReal.ofReal ‖u n - f‖) atTop (𝓝 0) := by
    simp_rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ B / (δ / 2))]
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => bot_le)
  intro n
  have ha : (E.weak (u n - f) : ℝ → 𝕜) =ᵐ[volume]
      fun x => E.weak (u n) x - E.weak f x := by
    rw [map_sub]
    exact AEEqFun.coeFn_sub _ _
  apply le_trans (measure_mono_ae (t := {x | δ / 2 < ‖E.weak (u n - f) x‖}) ?_)
    (hbound _ _ (by positivity))
  filter_upwards [ha] with x hx hlarge
  change δ ≤ ‖E.weak (u n) x - E.weak f x‖ at hlarge
  rw [hx]
  linarith

lemma tendstoInMeasure_ofReal {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h : TendstoInMeasure volume u atTop f) :
    TendstoInMeasure volume (fun n x => (u n x : ℂ)) atTop (fun x => (f x : ℂ)) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

lemma extensions_weak_compatible
    (R : Extensions ℝ realOperator) (C : Extensions ℂ complexHilbert)
    (f : LineLp ℝ 1) :
    (C.weak (complexify 1 f) : ℝ → ℂ) =ᵐ[volume] fun x => (R.weak f x : ℂ) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℝ)
    (μ := (volume : Measure ℝ)) (p := 1) (by norm_num)
  obtain ⟨u, hu, hul⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose φ hφeq using hu
  have hφ : Tendsto (fun n => (φ n).toLp 1) atTop (𝓝 f) := by
    have he : (fun n => (φ n).toLp 1) = u := funext hφeq
    rw [he]
    exact hul
  have he (n : ℕ) : (C.weak (complexify 1 ((φ n).toLp 1)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (R.weak ((φ n).toLp 1) x : ℂ) := by
    let ψ := (φ n).postcompCLM Complex.ofRealCLM
    rw [complexify_schwartz]
    have hc := C.weak_agrees ψ (ψ.memLp 1 volume) (ψ.memLp 2 volume)
    have hr := R.weak_agrees (φ n) ((φ n).memLp 1 volume) ((φ n).memLp 2 volume)
    change (C.weak (ψ.toLp 1) : ℝ → ℂ) =ᵐ[volume]
      (complexHilbert (ψ.toLp 2) : ℝ → ℂ) at hc
    change (R.weak ((φ n).toLp 1) : ℝ → ℝ) =ᵐ[volume]
      (realOperator ((φ n).toLp 2) : ℝ → ℝ) at hr
    have hψ : ψ.toLp 2 = complexify 2 ((φ n).toLp 2) := (complexify_schwartz 2 _).symm
    rw [hψ, real_restriction] at hc
    filter_upwards [hc, hr, complexify_coe (realOperator ((φ n).toLp 2))] with x ha hb hc
    rw [ha, hc, ← hb]
  have hC := extensions_weak_tendstoInMeasure ℂ complexHilbert C
    (fun n => complexify 1 ((φ n).toLp 1)) (complexify 1 f)
    (((complexify 1).continuous.tendsto f).comp
      (f := fun n : ℕ => (φ n).toLp 1 volume) hφ)
  have hR := tendstoInMeasure_ofReal (extensions_weak_tendstoInMeasure ℝ realOperator R
    (fun n => (φ n).toLp 1) f hφ)
  exact tendstoInMeasure_ae_unique hC (hR.congr_left fun n => (he n).symm)

lemma extensions_compatible
    (R : Extensions ℝ realOperator) (C : Extensions ℂ complexHilbert) :
    ExtensionsCompatible realOperator R C :=
  ⟨extensions_strong_compatible R C, extensions_weak_compatible R C⟩

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma real_restriction_unique (A : RealL2 →L[ℝ] RealL2) (hA : IsRealRestriction A) :
    A = realOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply complexify_injective
  exact (hA f).symm.trans (real_restriction f)

theorem extensions_scalar_compatibility :
    ∀ (A : RealL2 →L[ℝ] RealL2), IsRealRestriction A →
    ∀ (R : Extensions ℝ A) (C : Extensions ℂ complexHilbert),
      ExtensionsCompatible A R C := by
  intro A hA
  obtain rfl := real_restriction_unique A hA
  exact extensions_compatible

theorem compatible_extensions_of_realizations :
    ∀ (A : RealL2 →L[ℝ] RealL2), IsRealRestriction A →
    HasStandardRealization ℝ A → HasStandardRealization ℂ complexHilbert →
    ∃ (R : Extensions ℝ A) (C : Extensions ℂ complexHilbert), ExtensionsCompatible A R C := by
  intro A hA hR hC
  obtain ⟨R⟩ := extensions_of_standard_realization ℝ A hR
  obtain ⟨C⟩ := extensions_of_standard_realization ℂ complexHilbert hC
  exact ⟨R, C, extensions_scalar_compatibility A hA R C⟩

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma truncated_indicator_interval (ε x : ℝ) :
    truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) x =
      ∫ t in (x - 1)..x, cutKernel ℝ ε t := by
  unfold truncated
  rw [← integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet]
  calc
    (∫ t : ℝ, {t | ε < |t|}.indicator
      (fun t => (Real.pi * t)⁻¹ * (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (x-t)) t) =
      ∫ t : ℝ, (Icc (x-1) x).indicator (cutKernel ℝ ε) t := by
        apply integral_congr_ae
        exact .of_forall fun t => by
          have he : x-t ∈ Icc (0 : ℝ) 1 ↔ t ∈ Icc (x-1) x := by
            simp only [mem_Icc]
            constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
          by_cases hc : ε < |t| <;> by_cases ht : t ∈ Icc (x-1) x <;>
            simp only [Set.indicator_apply, he, mem_ofPred_eq, cutKernel, hc, ht,
              ite_true, ite_false, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq]
    _ = ∫ t in Icc (x-1) x, cutKernel ℝ ε t := integral_indicator measurableSet_Icc
    _ = ∫ t in (x-1)..x, cutKernel ℝ ε t := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]

lemma cutKernel_intervalIntegrable {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    IntervalIntegrable (cutKernel ℝ ε) volume a b := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  have hi : IntegrableOn (cutKernel ℝ ε) (uIcc a b) volume :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((cutKernel_memLp ℝ hε).restrict (uIcc a b))
  exact IntegrableOn.intervalIntegrable hi

lemma cutKernel_integral_eq_inv {ε a b : ℝ}
    (h : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b → ε < |t|) :
    (∫ t in a..b, cutKernel ℝ ε t) = Real.pi⁻¹ * ∫ t in a..b, t⁻¹ := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [h] with t ht htab
  simp only [cutKernel, ht htab, ite_true, RCLike.ofReal_real_eq_id, id_eq,
    mul_inv_rev, mul_comm]

lemma truncated_indicator_eq_small_real {ε x : ℝ} (hε : 0 < ε)
    (h0 : ε < |x|) (h1 : ε < |x-1|) :
    truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) x = indicatorImage x := by
  rw [truncated_indicator_interval]
  have hx : x - 1 ≤ x := by linarith
  by_cases hxn : x < 0
  · have hxm : x - 1 < 0 := by linarith
    rw [cutKernel_integral_eq_inv, integral_inv_of_neg hxm hxn]
    · simp only [indicatorImage, Real.log_abs]
    · apply Filter.Eventually.of_forall
      intro t ht
      rw [uIoc_of_le hx] at ht
      have ht0 : t < 0 := lt_of_le_of_lt ht.2 hxn
      rw [abs_of_neg ht0]
      rw [abs_of_neg hxn] at h0
      linarith [ht.2]
  · have hxp : 0 < x := by
      rw [abs_of_nonneg (le_of_not_gt hxn)] at h0
      linarith
    by_cases hxl : x < 1
    · have hxm : x - 1 < 0 := by linarith
      have hle1 : x - 1 ≤ -ε := by
        rw [abs_of_neg hxm] at h1
        linarith
      have hle2 : ε ≤ x := by simpa [abs_of_pos hxp] using h0.le
      have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
        (cutKernel_intervalIntegrable hε (x-1) (-ε))
        (cutKernel_intervalIntegrable hε (-ε) x)
      have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
        (cutKernel_intervalIntegrable hε (-ε) ε)
        (cutKernel_intervalIntegrable hε ε x)
      rw [← hsplit1, ← hsplit2]
      have hleft : (∫ t in (x-1)..(-ε), cutKernel ℝ ε t) =
          Real.pi⁻¹ * Real.log ((-ε) / (x-1)) := by
        rw [cutKernel_integral_eq_inv, integral_inv_of_neg hxm (neg_neg_of_pos hε)]
        filter_upwards [(volume : Measure ℝ).ae_ne (-ε)] with t ht htab
        rw [uIoc_of_le hle1] at htab
        have ht0 : t < 0 := by linarith [htab.2]
        rw [abs_of_neg ht0]
        have : t < -ε := lt_of_le_of_ne htab.2 ht
        linarith
      have hmid : (∫ t in (-ε)..ε, cutKernel ℝ ε t) = 0 := by
        rw [← intervalIntegral.integral_zero (a := -ε) (b := ε)]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : -ε ≤ ε)] at ht
        have hc : ¬ ε < |t| := by
          rw [not_lt, abs_le]
          exact ht
        simp [cutKernel, hc]
      have hright : (∫ t in ε..x, cutKernel ℝ ε t) =
          Real.pi⁻¹ * Real.log (x / ε) := by
        rw [cutKernel_integral_eq_inv, integral_inv_of_pos hε hxp]
        apply Filter.Eventually.of_forall
        intro t ht
        rw [uIoc_of_le hle2] at ht
        have ht0 : 0 < t := hε.trans ht.1
        simpa only [abs_of_pos ht0] using ht.1
      rw [hleft, hmid, hright]
      unfold indicatorImage
      rw [Real.log_abs, Real.log_div (neg_ne_zero.mpr hε.ne') hxm.ne,
        Real.log_div hxp.ne' hε.ne', Real.log_div hxp.ne' hxm.ne,
        Real.log_neg_eq_log]
      ring
    · have hxm : 0 < x-1 := by
        have hx1 : 0 ≤ x-1 := by linarith
        rw [abs_of_nonneg hx1] at h1
        linarith
      rw [cutKernel_integral_eq_inv, integral_inv_of_pos hxm hxp]
      · simp only [indicatorImage, Real.log_abs]
      · apply Filter.Eventually.of_forall
        intro t ht
        rw [uIoc_of_le hx] at ht
        have ht0 : 0 < t := hxm.trans ht.1
        rw [abs_of_pos ht0]
        rw [abs_of_pos hxm] at h1
        exact h1.trans ht.1
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma truncated_indicator_ofReal (𝕜 : Type) [RCLike 𝕜] (ε x : ℝ) :
    truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x =
      ((truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) x : ℝ) : 𝕜) := by
  unfold truncated
  rw [← integral_ofReal]
  apply integral_congr_ae
  exact .of_forall fun t => by
    dsimp only
    simp only [RCLike.ofReal_real_eq_id, id_eq, RCLike.ofReal_mul, RCLike.ofReal_inv]
    congr 1
    by_cases ht : x-t ∈ Icc (0 : ℝ) 1 <;> simp [ht]

lemma truncated_indicator_eq_small (𝕜 : Type) [RCLike 𝕜]
    {ε x : ℝ} (hε : 0 < ε) (h0 : ε < |x|) (h1 : ε < |x-1|) :
    truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x = (indicatorImage x : 𝕜) := by
  rw [truncated_indicator_ofReal, truncated_indicator_eq_small_real hε h0 h1]

lemma indicator_principal_value (𝕜 : Type) [RCLike 𝕜]
    (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    Tendsto (fun ε : ℝ =>
      truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x)
      (𝓝[>] 0) (𝓝 (indicatorImage x : 𝕜)) := by
  have heq : (fun ε : ℝ => (indicatorImage x : 𝕜)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => truncated ε ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (abs_pos.mpr hx0)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (abs_pos.mpr (sub_ne_zero.mpr hx1))).filter_mono
        nhdsWithin_le_nhds] with ε hε h0 h1
    exact (truncated_indicator_eq_small 𝕜 hε h0 h1).symm
  exact tendsto_const_nhds.congr' heq
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma truncated_congr_ae {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (hfg : f =ᵐ[(volume : Measure ℝ)] g) (ε x : ℝ) :
    truncated ε f x = truncated ε g x := by
  unfold truncated
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    ((Measure.measurePreserving_sub_left (volume : Measure ℝ) x).quasiMeasurePreserving.ae hfg)]
    with t ht
  rw [ht]

lemma indicatorFormula_of_truncationConvergence (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (hT : TruncationConvergence 𝕜 A) :
    IndicatorFormula 𝕜 A := by
  refine ⟨?_, indicator_principal_value 𝕜⟩
  have hinput : (indicatorL2 𝕜 : ℝ → 𝕜) =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn
  have hconv := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (hT.2 (indicatorL2 𝕜))
  obtain ⟨ns, hns, hlim⟩ := hconv.exists_seq_tendsto_ae'
  filter_upwards [hlim, (volume : Measure ℝ).ae_ne (0 : ℝ),
    (volume : Measure ℝ).ae_ne (1 : ℝ)] with x hxlim hx0 hx1
  have hpoint := (indicator_principal_value 𝕜 x hx0 hx1).comp hns
  have heq : (fun n => truncated (ns n) (indicatorL2 𝕜) x) =
      (fun n => truncated (ns n) ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜))) x) := by
    funext n
    exact truncated_congr_ae hinput (ns n) x
  exact tendsto_nhds_unique hxlim (heq ▸ hpoint)
end ExpandedFA.SingularIntegrals.HilbertTransform

-- Conditional on genuine L² truncation convergence, both endpoint failures.
namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform
lemma endpointFailure_of_truncationConvergence (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) (hT : TruncationConvergence 𝕜 A) :
    EndpointFailure 𝕜 A :=
  endpointFailure_of_indicatorFormula 𝕜 A (indicatorFormula_of_truncationConvergence 𝕜 A hT)
end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform

lemma inverseFourier_ae_integral (f : ComplexL2)
    (hf : Integrable (f : ℝ → ℂ)) :
    (lineFourier.symm f : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourierInv (f : ℝ → ℂ) := by
  have hc : Continuous (FourierTransform.fourierInv (f : ℝ → ℂ)) := by
    have hi : MemLp (f : ℝ → ℂ) 1 volume := memLp_one_iff_integrable.mpr hf
    rw [← Real.Lp.fourierTransformInv_toLp hi]
    exact (Real.Lp.fourierTransformInv (hi.toLp f)).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (lineFourier.symm f)).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hs
  let ψ : SchwartzMap ℝ ℂ :=
    (hs.comp_left (by simp : Complex.ofRealCLM 0 = 0)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have ht := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at ht
  have hp := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ ℝ)) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) Real.continuous_fourierChar
    (by fun_prop) ψ.integrable hf
  have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by
    ext x y
    simp [real_inner_comm]
  rw [hflip] at hp
  change (∫ x : ℝ, (FourierTransform.fourierInv (ψ : ℝ → ℂ)) x • f x) =
    ∫ x : ℝ, ψ x • (FourierTransform.fourierInv (f : ℝ → ℂ)) x at hp
  rw [← SchwartzMap.fourierInv_coe] at hp
  have heq := ht.symm.trans hp
  change (∫ x : ℝ, (g x : ℂ) • lineFourier.symm f x) =
    ∫ x : ℝ, (g x : ℂ) • (FourierTransform.fourierInv (f : ℝ → ℂ)) x at heq
  simpa only [Complex.coe_smul] using heq

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open StandardConvolution
open Set TopologicalSpace
open scoped _root_.Distributions ContDiff

/-- A compactly supported smooth test viewed as a Schwartz function. -/
def testSchwartz (φ : Tests ℂ 1) : SchwartzMap (Space 1) ℂ :=
  φ.hasCompactSupport.toSchwartzMap φ.contDiff

lemma testSchwartz_add (φ ψ : Tests ℂ 1) :
    testSchwartz (φ + ψ) = testSchwartz φ + testSchwartz ψ := by
  ext x
  rfl

lemma testSchwartz_smul (c : ℂ) (φ : Tests ℂ 1) :
    testSchwartz (c • φ) = c • testSchwartz φ := by
  ext x
  rfl

/-- The LF inclusion of compact smooth tests into Schwartz space. -/
def testSchwartzCLM : Tests ℂ 1 →L[ℂ] SchwartzMap (Space 1) ℂ :=
  TestFunction.mkCLM ℂ testSchwartz testSchwartz_add testSchwartz_smul (by
    intro K hK
    let A : ContDiffMapSupportedIn (Space 1) ℂ ⊤ K →ₗ[ℂ] SchwartzMap (Space 1) ℂ :=
      { toFun := fun φ => testSchwartz (TestFunction.ofSupportedIn hK φ)
        map_add' := fun φ ψ => by ext x; rfl
        map_smul' := fun c φ => by ext x; rfl }
    apply WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ℂ _ _ _ _)
      (schwartz_withSeminorms ℂ _ _) A
    apply Seminorm.IsBounded.of_real
    rintro ⟨k, n⟩
    obtain ⟨R, hR, hKR⟩ := K.isCompact.isBounded.subset_ball_lt 0 (0 : Space 1)
    refine ⟨{n}, R ^ k, ?_⟩
    intro φ
    simp only [Finset.sup_singleton]
    apply SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg (pow_nonneg hR.le _) (apply_nonneg _ _))
    intro x
    change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (φ : Space 1 → ℂ) x‖ ≤ _
    by_cases hx : x ∈ K
    · apply mul_le_mul
      · exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (by simpa using hKR hx)) _
      · exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
      · exact norm_nonneg _
      · exact pow_nonneg hR.le _
    · simp only [φ.iteratedFDeriv_zero_on_compl hx, Pi.zero_apply, norm_zero, mul_zero]
      exact mul_nonneg (pow_nonneg hR.le _) (apply_nonneg _ _))

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open StandardConvolution
open Set TopologicalSpace
open scoped _root_.Distributions ContDiff

/-- Compact smooth tests pulled back to the ordinary line. -/
def lineTestSchwartzCLM : Tests ℂ 1 →L[ℂ] LineSchwartz :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    lineIsometry.toContinuousLinearEquiv).comp testSchwartzCLM

lemma lineTestSchwartz_apply (φ : Tests ℂ 1) (t : ℝ) :
    lineTestSchwartzCLM φ t = φ (lineIsometry t) := rfl

/-- The normalized principal value already constructed from its symmetric limits. -/
def normalizedTempered : LineTempered := Classical.choose normalized_principal_value

lemma normalizedTempered_apply (φ : LineSchwartz) :
    normalizedTempered φ = (Real.pi : ℂ)⁻¹ *
      Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.principalValuePairingValue φ :=
  (Classical.choose_spec normalized_principal_value).1 φ

lemma normalizedTempered_fourier (φ : LineSchwartz) :
    normalizedTempered (FourierTransform.fourierCLM ℂ LineSchwartz φ) =
      ∫ ξ : ℝ, multiplier ξ * φ ξ :=
  (Classical.choose_spec normalized_principal_value).2 φ

/-- The actual principal value as a distribution in the standard CZ coordinates. -/
def complexKernelDistribution : KernelDistribution ℂ 1 :=
  normalizedTempered.comp lineTestSchwartzCLM

lemma complexKernelDistribution_limit (φ : Tests ℂ 1) :
    Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t|},
      ((Real.pi * t : ℝ) : ℂ)⁻¹ * φ (lineIsometry t))
      (𝓝[>] 0) (𝓝 (complexKernelDistribution φ)) := by
  have ht := (PrincipalValue.symmetric_limit (lineTestSchwartzCLM φ)).const_mul
    (Real.pi : ℂ)⁻¹
  convert ht using 1
  · ext ε
    simp only [Specs.ExpandedFA.SingularIntegrals.PrincipalValueAndBoundaryValues.symmetricTruncationValue]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun t => by
      simp [lineTestSchwartz_apply, div_eq_mul_inv, mul_inv_rev,
        mul_assoc, mul_left_comm, mul_comm, Complex.ofReal_mul]
  · exact congrArg (fun z : ℂ => 𝓝 z) (normalizedTempered_apply _)

lemma complexKernelDistribution_off_zero (φ : Tests ℂ 1)
    (hφ : (0 : Space 1) ∉ tsupport φ) :
    complexKernelDistribution φ = ∫ x, (standardKernel ℂ).function x * φ x := by
  have hzero : lineTestSchwartzCLM φ 0 = 0 := by
    rw [lineTestSchwartz_apply, map_zero]
    exact image_eq_zero_of_notMem_tsupport hφ
  change normalizedTempered (lineTestSchwartzCLM φ) = _
  rw [normalizedTempered_apply, PrincipalValue.compensated_formula]
  rw [compensatedPairing, ← integral_const_mul]
  rw [← lineIsometry.measurePreserving.integral_comp lineIsometry.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  exact .of_forall fun t => by
    simp only [hzero, sub_zero, ite_self, lineTestSchwartz_apply]
    simp [standardKernel, Specs.ExpandedFA.SingularIntegrals.HilbertTransform.kernelFunction,
      div_eq_mul_inv, Complex.ofReal_mul, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform

lemma complexHilbert_schwartz_inverseIntegral (φ : LineSchwartz) :
    (complexHilbert (φ.toLp 2) : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourierInv (fun ξ : ℝ => multiplier ξ *
        (FourierTransform.fourierCLM ℂ LineSchwartz φ) ξ) := by
  let ψ : LineSchwartz := FourierTransform.fourierCLM ℂ LineSchwartz φ
  have hf : lineFourier (φ.toLp 2) = ψ.toLp 2 := SchwartzMap.toLp_fourier_eq φ
  have he : (frequencyAction (lineFourier (φ.toLp 2)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => multiplier ξ * ψ ξ := by
    rw [hf]
    filter_upwards [frequencyAction_coe (ψ.toLp 2), ψ.coeFn_toLp 2 volume] with ξ ha hb
    rw [ha, hb]
  have hi : Integrable (fun ξ : ℝ => multiplier ξ * ψ ξ) := by
    have hψ : Integrable (ψ : ℝ → ℂ) volume := ψ.integrable
    apply hψ.norm.mono'
      (multiplier_measurable.aestronglyMeasurable.mul ψ.continuous.aestronglyMeasurable)
    exact .of_forall fun ξ => by
      change ‖multiplier ξ * ψ ξ‖ ≤ ‖ψ ξ‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_norm_le ξ)
  exact (inverseFourier_ae_integral _ (hi.congr he.symm)).trans
    (.of_forall fun x => Real.fourierInv_congr_ae he x)

/-- Reflection about a line point, in Schwartz space. -/
def reflectedSchwartz (φ : LineSchwartz) (x : ℝ) : LineSchwartz :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) (φ.compSubConstCLM ℂ (-x))

lemma reflectedSchwartz_apply (φ : LineSchwartz) (x t : ℝ) :
    reflectedSchwartz φ x t = φ (x - t) := by
  change φ (-t - -x) = φ (x - t)
  congr 1
  ring

lemma inverseFourier_reflectedSchwartz (φ : LineSchwartz) (x ξ : ℝ) :
    (FourierTransform.fourierInvCLM ℂ LineSchwartz (reflectedSchwartz φ x)) ξ =
      (Real.fourierChar (inner ℝ x ξ) : ℂ) *
        (FourierTransform.fourierCLM ℂ LineSchwartz φ) ξ := by
  rw [FourierTransform.fourierInvCLM_apply, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq_fourier_comp_neg]
  have he : (fun t : ℝ => reflectedSchwartz φ x (-t)) = fun t : ℝ => φ (t + x) := by
    ext t
    rw [reflectedSchwartz_apply]
    congr 1
    ring
  rw [he, FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun t : ℝ => φ (t + x)) ξ = _
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (innerₗ ℝ) (φ : ℝ → ℂ) x) ξ
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun t : ℝ => φ (t + x)) ξ =
    (Real.fourierChar (inner ℝ x ξ) : ℂ) *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) φ ξ
  simpa only [Function.comp_def, innerₗ_apply_apply, Circle.smul_def, smul_eq_mul] using ht

lemma normalizedTempered_inverse_formula (φ : LineSchwartz) :
    normalizedTempered φ = ∫ ξ : ℝ, multiplier ξ *
      (FourierTransform.fourierInvCLM ℂ LineSchwartz φ) ξ := by
  have hf := normalizedTempered_fourier (FourierTransform.fourierInvCLM ℂ LineSchwartz φ)
  simpa only [FourierTransform.fourierInvCLM_apply, FourierTransform.fourierCLM_apply,
    FourierTransform.fourier_fourierInv_eq] using hf

lemma normalizedTempered_reflectedSchwartz (φ : LineSchwartz) (x : ℝ) :
    normalizedTempered (reflectedSchwartz φ x) =
      FourierTransform.fourierInv (fun ξ : ℝ => multiplier ξ *
        (FourierTransform.fourierCLM ℂ LineSchwartz φ) ξ) x := by
  rw [normalizedTempered_inverse_formula, Real.fourierInv_eq]
  apply integral_congr_ae
  exact .of_forall fun ξ => by
    dsimp only
    rw [inverseFourier_reflectedSchwartz]
    simp only [Circle.smul_def, smul_eq_mul]
    rw [real_inner_comm ξ x]
    ring

lemma complexHilbert_schwartz_action (φ : LineSchwartz) :
    (complexHilbert (φ.toLp 2) : ℝ → ℂ) =ᵐ[volume]
      fun x => normalizedTempered (reflectedSchwartz φ x) := by
  filter_upwards [complexHilbert_schwartz_inverseIntegral φ] with x hx
  exact hx.trans (normalizedTempered_reflectedSchwartz φ x).symm

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open StandardConvolution
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

/-- Coordinate conjugation of an actual line operator. -/
def transportL2Operator (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 →L[𝕜] LineLp 𝕜 2) : L2 𝕜 1 →L[𝕜] L2 𝕜 1 :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 lineIsometry.symm lineIsometry.symm.measurePreserving).toContinuousLinearMap.comp
    (A.comp (Lp.compMeasurePreservingₗᵢ 𝕜 lineIsometry lineIsometry.measurePreserving).toContinuousLinearMap)

lemma transportL2Operator_apply (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 →L[𝕜] LineLp 𝕜 2) (f : L2 𝕜 1) :
    transportL2Operator 𝕜 A f = toEuclidean 2 (A (fromEuclidean 2 f)) := rfl

lemma transportL2Operator_coe (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 →L[𝕜] LineLp 𝕜 2) (f : L2 𝕜 1) :
    (transportL2Operator 𝕜 A f : Space 1 → 𝕜) =ᵐ[volume]
      fun x => A (fromEuclidean 2 f) (lineIsometry.symm x) :=
  Lp.coeFn_compMeasurePreserving _ lineIsometry.symm.measurePreserving

lemma fromEuclidean_coe' (𝕜 : Type) [RCLike 𝕜] (f : L2 𝕜 1) :
    (fromEuclidean 2 f : ℝ → 𝕜) =ᵐ[volume] fun x => f (lineIsometry x) :=
  Lp.coeFn_compMeasurePreserving _ lineIsometry.measurePreserving

lemma fromEuclidean_transportL2Operator (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 →L[𝕜] LineLp 𝕜 2) (f : LineLp 𝕜 2) :
    fromEuclidean 2 (transportL2Operator 𝕜 A (toEuclidean 2 f)) = A f := by
  rw [transportL2Operator_apply, coordinate_transport.2.1, coordinate_transport.2.1]

lemma transportL2Operator_translationInvariant (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 →L[𝕜] LineLp 𝕜 2)
    (hA : LineTranslationInvariant 𝕜 A) :
    TranslationInvariant (transportL2Operator 𝕜 A) := by
  intro a f g hfg
  have he : (fromEuclidean 2 g : ℝ → 𝕜) =ᵐ[volume]
      fun t => fromEuclidean 2 f (t - lineIsometry.symm a) := by
    filter_upwards [fromEuclidean_coe' 𝕜 g,
      lineIsometry.measurePreserving.quasiMeasurePreserving.ae hfg,
      (measurePreserving_sub_right (volume : Measure ℝ) (lineIsometry.symm a)).quasiMeasurePreserving.ae
        (fromEuclidean_coe' 𝕜 f)] with t ha hb hc
    rw [ha, hb, hc]
    congr 1
    simp only [map_sub, lineIsometry.apply_symm_apply]
  have ht := hA (lineIsometry.symm a) (fromEuclidean 2 f) (fromEuclidean 2 g) he
  filter_upwards [transportL2Operator_coe 𝕜 A g,
    lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae ht,
    (measurePreserving_sub_right (volume : Measure (Space 1)) a).quasiMeasurePreserving.ae
      (transportL2Operator_coe 𝕜 A f)] with x ha hb hc
  rw [ha, hb, hc]
  congr 1

lemma testSchwartz_lineL2 (φ : Tests ℂ 1) :
    (lineTestSchwartzCLM φ).toLp 2 = fromEuclidean 2 (testL2 φ) := by
  apply Lp.ext
  filter_upwards [(lineTestSchwartzCLM φ).coeFn_toLp 2 volume,
    fromEuclidean_coe' ℂ (testL2 φ),
    lineIsometry.measurePreserving.quasiMeasurePreserving.ae
      (show (testL2 φ : Space 1 → ℂ) =ᵐ[volume] φ from MemLp.coeFn_toLp _)] with t ha hb hc
  rw [ha, hb, hc, lineTestSchwartz_apply]

lemma lineTestSchwartz_reflected (φ : Tests ℂ 1) (x : Space 1) :
    lineTestSchwartzCLM (reflectedTest φ x) =
      reflectedSchwartz (lineTestSchwartzCLM φ) (lineIsometry.symm x) := by
  ext t
  rw [reflectedSchwartz_apply, lineTestSchwartz_apply, lineTestSchwartz_apply]
  change φ (x - lineIsometry t) = φ (lineIsometry (lineIsometry.symm x - t))
  simp only [map_sub, lineIsometry.apply_symm_apply]

lemma complex_kernel_action (φ : Tests ℂ 1) :
    (transportL2Operator ℂ operator (testL2 φ) : Space 1 → ℂ) =ᵐ[volume]
      fun x => complexKernelDistribution (reflectedTest φ x) := by
  have ha := complexHilbert_schwartz_action (lineTestSchwartzCLM φ)
  rw [testSchwartz_lineL2] at ha
  filter_upwards [transportL2Operator_coe ℂ operator (testL2 φ),
    lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae ha] with x hb hc
  rw [hb]
  change complexHilbert (fromEuclidean 2 (testL2 φ)) (lineIsometry.symm x) = _
  rw [hc]
  change normalizedTempered _ = normalizedTempered _
  exact congrArg normalizedTempered (lineTestSchwartz_reflected φ x).symm

/-- The multiplier-defined Hilbert transform in the shared standard CZ setting. -/
def complexStandardOperator : StandardConvolutionOperator ℂ 1 where
  operator := transportL2Operator ℂ operator
  translation_invariant := transportL2Operator_translationInvariant ℂ operator complex_translation_invariant
  distribution := complexKernelDistribution
  kernel := standardKernel ℂ
  agrees_off_zero := complexKernelDistribution_off_zero
  kernel_action := complex_kernel_action

theorem complex_standard_realization : HasStandardRealization ℂ complexHilbert := by
  refine ⟨complexStandardOperator, ?_, complexKernelDistribution_limit, ?_⟩
  · intro t ht
    simp [complexStandardOperator, standardKernel, kernelFunction]
  · intro f
    exact fromEuclidean_transportL2Operator ℂ operator f

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform

lemma bilinear_parseval (u v : ComplexL2) :
    (∫ t : ℝ, u t * v t) = ∫ ξ : ℝ, lineFourier u ξ * lineFourier.symm v ξ := by
  have h := lineFourier.inner_map_map (conjugateL2 v) u
  rw [fourier_conjugate, L2.inner_def, L2.inner_def] at h
  have hl : (∫ ξ : ℝ, inner ℂ (conjugateL2 (lineFourier.symm v) ξ) (lineFourier u ξ)) =
      ∫ ξ : ℝ, lineFourier u ξ * lineFourier.symm v ξ := by
    apply integral_congr_ae
    filter_upwards [conjugateL2_coe (lineFourier.symm v)] with ξ hx
    simp only [RCLike.inner_apply, hx, starRingEnd_apply, star_star, mul_comm]
  have hr : (∫ t : ℝ, inner ℂ (conjugateL2 v t) (u t)) = ∫ t : ℝ, u t * v t := by
    apply integral_congr_ae
    filter_upwards [conjugateL2_coe v] with t hx
    simp only [RCLike.inner_apply, hx, starRingEnd_apply, star_star, mul_comm]
  rw [hl, hr] at h
  exact h.symm

lemma reflectL2_involution (f : ComplexL2) : reflectL2 (reflectL2 f) = f := by
  apply Lp.ext
  filter_upwards [reflectL2_coe (reflectL2 f),
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (reflectL2_coe f)] with x ha hb
  rw [ha, hb]
  simp

lemma inverseFourier_reflect (f : ComplexL2) : lineFourier.symm (reflectL2 f) = lineFourier f := by
  have h : reflectL2 f = lineFourier (lineFourier f) := by
    have hi := inverseFourier_eq_reflect (lineFourier f)
    rw [lineFourier.symm_apply_apply] at hi
    have hc := congrArg reflectL2 hi
    simpa only [reflectL2_involution] using hc
  rw [h, lineFourier.symm_apply_apply]

lemma inverseFourier_reflectedTranslate (x : ℝ) (f : ComplexL2) :
    (lineFourier.symm (reflectL2 (translateL2 (-x) f)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (Real.fourierChar (inner ℝ x ξ) : ℂ) * lineFourier f ξ := by
  rw [inverseFourier_reflect, fourier_translate]
  filter_upwards [phaseAction_coe (-x) (lineFourier f)] with ξ hx
  simpa only [phase, neg_neg] using hx

lemma L2_convolution_parseval (u f : ComplexL2) (x : ℝ) :
    (∫ t : ℝ, u t * f (x - t)) = ∫ ξ : ℝ,
      (Real.fourierChar (inner ℝ x ξ) : ℂ) * lineFourier u ξ * lineFourier f ξ := by
  let v := reflectL2 (translateL2 (-x) f)
  have hv : (v : ℝ → ℂ) =ᵐ[volume] fun t : ℝ => f (x - t) := by
    filter_upwards [reflectL2_coe (translateL2 (-x) f),
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
        (translateL2_coe (-x) f)] with t ha hb
    change reflectL2 (translateL2 (-x) f) t = _
    rw [ha, hb]
    congr 1
    ring
  calc
    _ = ∫ t : ℝ, u t * v t := by
      apply integral_congr_ae
      filter_upwards [hv] with t ht
      rw [ht]
    _ = ∫ ξ : ℝ, lineFourier u ξ * lineFourier.symm v ξ := bilinear_parseval u v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [inverseFourier_reflectedTranslate x f] with ξ hx
      change lineFourier u ξ * lineFourier.symm (reflectL2 (translateL2 (-x) f)) ξ = _
      rw [hx]
      ring
lemma normalizedDampedSign_memLp {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun ξ : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ) 2 volume := by
  have hi := (PrincipalValue.dampedSign_integrable ε hε).const_mul (Real.pi : ℂ)⁻¹
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
  apply hi.norm.mono' (hi.aestronglyMeasurable.norm.pow 2)
  exact .of_forall fun ξ => by
    simp only [Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hx := normalized_dampedSign_norm_le ε hε.le ξ
    nlinarith [norm_nonneg ((Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ)]

def softKernelL2 (ε : ℝ) (hε : 0 < ε) : ComplexL2 :=
  lineFourier.symm ((normalizedDampedSign_memLp hε).toLp _)

lemma softKernelL2_coe (ε : ℝ) (hε : 0 < ε) :
    (softKernelL2 ε hε : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ => (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) := by
  have hi := (PrincipalValue.dampedSign_integrable ε hε).const_mul (Real.pi : ℂ)⁻¹
  have heq := (normalizedDampedSign_memLp hε).coeFn_toLp
  have hinv := inverseFourier_ae_integral ((normalizedDampedSign_memLp hε).toLp _)
    (hi.congr heq.symm)
  filter_upwards [hinv] with x hx
  change lineFourier.symm ((normalizedDampedSign_memLp hε).toLp _) x = _
  rw [hx, Real.fourierInv_congr_ae heq]
  rw [← PrincipalValue.inverse_dampedSign ε hε x, Real.fourierInv_eq', Real.fourierInv_eq', ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t => by simp only [smul_eq_mul]; ring

lemma softHilbert_coe {ε : ℝ} (hε : 0 < ε) (f : ComplexL2) :
    (softHilbert ε f : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => ∫ t : ℝ,
        (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) * f (x - t) := by
  let m := (normalizedDampedSign_memLp hε).toLp
    (fun ξ : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ)
  have hm : (m : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => (Real.pi : ℂ)⁻¹ * PrincipalValue.dampedSign ε ξ :=
    (normalizedDampedSign_memLp hε).coeFn_toLp
  have hprod : Integrable (fun ξ : ℝ => m ξ * lineFourier f ξ) :=
    (Lp.memLp m).integrable_mul (Lp.memLp (lineFourier f))
  have hs : (softFrequencyAction ε (lineFourier f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => m ξ * lineFourier f ξ := by
    filter_upwards [softFrequencyAction_coe ε (lineFourier f), hm] with ξ ha hb
    rw [ha, hb, max_eq_left hε.le]
  have hinv := inverseFourier_ae_integral (softFrequencyAction ε (lineFourier f))
    (hprod.congr hs.symm)
  filter_upwards [hinv] with x hx
  change lineFourier.symm (softFrequencyAction ε (lineFourier f)) x = _
  rw [hx, Real.fourierInv_congr_ae hs, Real.fourierInv_eq]
  have hc := L2_convolution_parseval (softKernelL2 ε hε) f x
  have hk : lineFourier (softKernelL2 ε hε) = m := lineFourier.apply_symm_apply _
  rw [hk] at hc
  have he : (∫ (v : ℝ), Real.fourierChar (inner ℝ v x) • (m v * lineFourier f v)) =
      ∫ ξ : ℝ, (Real.fourierChar (inner ℝ x ξ) : ℂ) * m ξ * lineFourier f ξ := by
    apply integral_congr_ae
    exact .of_forall fun ξ => by simp only [Circle.smul_def, smul_eq_mul, real_inner_comm ξ x, mul_assoc]
  rw [he, ← hc]
  apply integral_congr_ae
  filter_upwards [softKernelL2_coe ε hε] with t ht
  rw [ht]

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open StandardConvolution
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform
open scoped _root_.Distributions

/-- Complexification of compact smooth tests. -/
def complexifyTest : Tests ℝ 1 →L[ℝ] Tests ℂ 1 :=
  TestFunction.postcompCLM Complex.ofRealCLM

lemma complexifyTest_apply (φ : Tests ℝ 1) (x : Space 1) :
    complexifyTest φ x = (φ x : ℂ) := rfl

/-- The real kernel is the restriction of the same distribution. -/
def realKernelDistribution : KernelDistribution ℝ 1 :=
  Complex.reCLM.comp ((complexKernelDistribution.restrictScalars ℝ).comp complexifyTest)

lemma complexKernelPairing_ofReal (φ : Tests ℝ 1) (ε : ℝ) :
    (∫ t in {t : ℝ | ε < |t|}, ((Real.pi * t : ℝ) : ℂ)⁻¹ *
      complexifyTest φ (lineIsometry t)) =
      ((∫ t in {t : ℝ | ε < |t|}, (Real.pi * t)⁻¹ * φ (lineIsometry t) : ℝ) : ℂ) := by
  simp only [complexifyTest_apply, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ).restrict {t : ℝ | ε < |t|})
    (f := fun t => (Real.pi * t)⁻¹ * φ (lineIsometry t)))

lemma realKernelDistribution_complexify (φ : Tests ℝ 1) :
    (realKernelDistribution φ : ℂ) = complexKernelDistribution (complexifyTest φ) := by
  have ht := Complex.continuous_im.tendsto _ |>.comp
    (complexKernelDistribution_limit (complexifyTest φ))
  have hz : (complexKernelDistribution (complexifyTest φ)).im = 0 := by
    apply tendsto_nhds_unique ht
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    ext ε
    dsimp only [Function.comp_def]
    rw [complexKernelPairing_ofReal]
    simp
  apply Complex.ext <;> simp [realKernelDistribution, hz]

lemma realKernelDistribution_limit (φ : Tests ℝ 1) :
    Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t|},
      (Real.pi * t)⁻¹ * φ (lineIsometry t))
      (𝓝[>] 0) (𝓝 (realKernelDistribution φ)) := by
  have ht := Complex.continuous_re.tendsto _ |>.comp
    (complexKernelDistribution_limit (complexifyTest φ))
  convert ht using 1
  · ext ε
    dsimp only [Function.comp_def]
    rw [complexKernelPairing_ofReal]
    simp
  · rfl

lemma realKernelDistribution_off_zero (φ : Tests ℝ 1)
    (hφ : (0 : Space 1) ∉ tsupport φ) :
    realKernelDistribution φ = ∫ x, (standardKernel ℝ).function x * φ x := by
  have hs : tsupport (complexifyTest φ) ⊆ tsupport φ :=
    tsupport_comp_subset (by simp : Complex.ofRealCLM 0 = 0) (φ : Space 1 → ℝ)
  have ht := complexKernelDistribution_off_zero (complexifyTest φ) (fun h => hφ (hs h))
  have he : (∫ x, (standardKernel ℂ).function x * complexifyTest φ x) =
      ((∫ x, (standardKernel ℝ).function x * φ x : ℝ) : ℂ) := by
    calc
      _ = ∫ x : Space 1, (((standardKernel ℝ).function x * φ x : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp [standardKernel, kernelFunction, complexifyTest_apply]
      _ = _ := integral_ofReal
  have := congrArg Complex.re (realKernelDistribution_complexify φ |>.trans (ht.trans he))
  simpa using this

lemma complexify_fromEuclidean (f : L2 ℝ 1) :
    complexify 2 (fromEuclidean 2 f) =
      fromEuclidean 2 (Complex.ofRealCLM.compLpL 2 volume f) := by
  apply Lp.ext
  filter_upwards [complexify_coe (fromEuclidean 2 f), fromEuclidean_coe' ℝ f,
    fromEuclidean_coe' ℂ (Complex.ofRealCLM.compLpL 2 volume f),
    lineIsometry.measurePreserving.quasiMeasurePreserving.ae
      (Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := (volume : Measure (Space 1))) f)]
    with t ha hb hc hd
  rw [ha, hb, hc, hd]
  rfl

lemma complexify_testL2 (φ : Tests ℝ 1) :
    Complex.ofRealCLM.compLpL 2 volume (testL2 φ) = testL2 (complexifyTest φ) := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2)
      (μ := (volume : Measure (Space 1))) (testL2 φ),
    (show (testL2 φ : Space 1 → ℝ) =ᵐ[volume] φ from MemLp.coeFn_toLp _),
    (show (testL2 (complexifyTest φ) : Space 1 → ℂ) =ᵐ[volume] complexifyTest φ
      from MemLp.coeFn_toLp _)] with x ha hb hc
  rw [ha, hb, hc, complexifyTest_apply]
  rfl

lemma transported_real_restriction (f : L2 ℝ 1) :
    Complex.ofRealCLM.compLpL 2 volume (transportL2Operator ℝ realOperator f) =
      transportL2Operator ℂ operator (Complex.ofRealCLM.compLpL 2 volume f) := by
  apply Lp.ext
  have hr := real_restriction (fromEuclidean 2 f)
  rw [complexify_fromEuclidean] at hr
  have he := Lp.ext_iff.mp hr
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := 2)
      (μ := (volume : Measure (Space 1))) (transportL2Operator ℝ realOperator f),
    transportL2Operator_coe ℝ realOperator f,
    transportL2Operator_coe ℂ operator (Complex.ofRealCLM.compLpL 2 volume f),
    lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae he,
    lineIsometry.symm.measurePreserving.quasiMeasurePreserving.ae
      (complexify_coe (realOperator (fromEuclidean 2 f)))] with x ha hb hc hd he
  rw [ha, hb, hc, Complex.ofRealCLM_apply, ← he]
  exact hd.symm

lemma complexifyTest_reflected (φ : Tests ℝ 1) (x : Space 1) :
    complexifyTest (reflectedTest φ x) = reflectedTest (complexifyTest φ) x := by
  ext t
  rfl

lemma real_kernel_action (φ : Tests ℝ 1) :
    (transportL2Operator ℝ realOperator (testL2 φ) : Space 1 → ℝ) =ᵐ[volume]
      fun x => realKernelDistribution (reflectedTest φ x) := by
  have hc := complex_kernel_action (complexifyTest φ)
  rw [← complexify_testL2, ← transported_real_restriction] at hc
  filter_upwards [hc, Complex.ofRealCLM.coeFn_compLpL (p := 2)
    (μ := (volume : Measure (Space 1))) (transportL2Operator ℝ realOperator (testL2 φ))]
    with x ha hb
  rw [hb, ← complexifyTest_reflected, ← realKernelDistribution_complexify] at ha
  exact Complex.ofReal_injective ha

/-- The restriction of the multiplier-defined transform in the real CZ setting. -/
def realStandardOperator : StandardConvolutionOperator ℝ 1 where
  operator := transportL2Operator ℝ realOperator
  translation_invariant := transportL2Operator_translationInvariant ℝ realOperator real_translation_invariant
  distribution := realKernelDistribution
  kernel := standardKernel ℝ
  agrees_off_zero := realKernelDistribution_off_zero
  kernel_action := real_kernel_action

theorem real_standard_realization : HasStandardRealization ℝ realOperator := by
  refine ⟨realStandardOperator, ?_, realKernelDistribution_limit, ?_⟩
  · intro t ht
    simp [realStandardOperator, standardKernel, kernelFunction]
  · intro f
    exact fromEuclidean_transportL2Operator ℝ realOperator f

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma truncated_complexify (ε : ℝ) (f : RealL2) (x : ℝ) :
    truncated ε (complexify 2 f) x = ((truncated ε f x : ℝ) : ℂ) := by
  rw [truncated_congr_ae (complexify_coe f), truncated_ofReal]

lemma real_truncation_of_complex
    (hC : TruncationConvergence ℂ complexHilbert) :
    TruncationConvergence ℝ realOperator := by
  have hmem (ε : ℝ) (hε : 0 < ε) (f : RealL2) : MemLp (truncated ε f) 2 volume := by
    have hc := (hC.1 ε hε (complexify 2 f)).2
    have he : truncated ε (complexify 2 f) = fun x => ((truncated ε f x : ℝ) : ℂ) :=
      funext (truncated_complexify ε f)
    rw [he] at hc
    have hm : AEStronglyMeasurable (truncated ε f) volume := by
      simpa using
        Complex.reCLM.continuous.comp_aestronglyMeasurable hc.aestronglyMeasurable
    apply hc.of_le hm
    exact .of_forall fun x => by simp
  constructor
  · intro ε hε f
    exact ⟨fun x => truncated_integrable ℝ hε f x, hmem ε hε f⟩
  · intro f
    have he (ε : ℝ) (hε : 0 < ε) : eLpNorm (fun x => truncated ε f x - realOperator f x) 2 volume =
        eLpNorm (fun x => truncated ε (complexify 2 f) x - complexHilbert (complexify 2 f) x)
          2 volume := by
      apply eLpNorm_congr_norm_ae
        ((hmem ε hε f).sub (Lp.memLp (realOperator f))).aestronglyMeasurable
        (((hC.1 ε hε (complexify 2 f)).2).sub (Lp.memLp _)).aestronglyMeasurable
      rw [real_restriction]
      filter_upwards [complexify_coe (realOperator f)] with x hx
      simp only [Pi.sub_apply]
      rw [truncated_complexify, hx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply (hC.2 (complexify 2 f)).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (he ε hε).symm

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

theorem standard_realizations : StandardRealizations :=
  ⟨complex_standard_realization, realOperator, real_restriction, real_standard_realization⟩

theorem compatible_extensions : CompatibleExtensions :=
  ⟨realOperator, real_restriction, compatible_extensions_of_realizations realOperator
    real_restriction real_standard_realization complex_standard_realization⟩

theorem indicator_principal_values : IndicatorPrincipalValue := indicator_principal_value

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

lemma cutKernel_sub_soft_complex {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    cutKernel ℂ ε t - (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) =
      (ε : ℂ)⁻¹ * (hardSoftDifference (t / ε) : ℂ) := by
  have hc := congrArg Complex.ofReal (cutKernel_sub_regularized hε t)
  have hk : (cutKernel ℝ ε t : ℂ) = cutKernel ℂ ε t := by
    simp only [cutKernel, RCLike.ofReal_real_eq_id, id_eq]
    split_ifs <;> simp
  rw [Complex.ofReal_sub, hk] at hc
  have he : (↑(t / (Real.pi * (t ^ 2 + ε ^ 2))) : ℂ) =
      (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) := by
    simp only [PrincipalValue.realBoundaryKernel, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
    field_simp
  simpa only [he, Complex.ofReal_mul, Complex.ofReal_inv] using hc

lemma cutKernel_integral (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    truncated ε f x = ∫ t : ℝ, cutKernel ℂ ε t * f (x - t) := by
  rw [truncated, ← integral_indicator (isOpen_lt continuous_const continuous_abs).measurableSet]
  apply integral_congr_ae
  exact .of_forall fun t => by
    by_cases ht : ε < |t| <;> simp [cutKernel, ht]

lemma hard_soft_integral_difference {ε : ℝ} (hε : 0 < ε) (f : ComplexL2) (x : ℝ) :
    truncated ε f x - (∫ t : ℝ,
      (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) * f (x - t)) =
      ∫ s : ℝ, (hardSoftDifference s : ℂ) * f (x - ε * s) := by
  have hf : MemLp (fun t => f (x - t)) 2 (volume : Measure ℝ) :=
    (Lp.memLp f).comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hi := (cutKernel_memLp ℂ hε).integrable_mul hf
  have hq : MemLp (fun t : ℝ =>
      (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ)) 2 volume :=
    (Lp.memLp (softKernelL2 ε hε)).ae_eq (softKernelL2_coe ε hε)
  have hqi := hq.integrable_mul hf
  change Integrable (fun t : ℝ => cutKernel ℂ ε t * f (x - t)) at hi
  change Integrable (fun t : ℝ => (Real.pi : ℂ)⁻¹ *
    (PrincipalValue.realBoundaryKernel ε t : ℂ) * f (x - t)) at hqi
  rw [cutKernel_integral, ← integral_sub hi hqi]
  have he (t : ℝ) : cutKernel ℂ ε t * f (x - t) -
      (Real.pi : ℂ)⁻¹ * (PrincipalValue.realBoundaryKernel ε t : ℂ) * f (x - t) =
      (ε : ℂ)⁻¹ * ((hardSoftDifference (t / ε) : ℂ) * f (x - t)) := by
    rw [← sub_mul, cutKernel_sub_soft_complex hε]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hc := Measure.integral_comp_mul_left
    (fun t : ℝ => (hardSoftDifference (t / ε) : ℂ) * f (x - t)) ε
  simp only [mul_div_cancel_left₀ _ hε.ne', abs_of_pos (inv_pos.mpr hε),
    Complex.real_smul, Complex.ofReal_inv] at hc
  exact hc.symm
lemma truncated_eq_soft_add_correction {ε : ℝ} (hε : 0 < ε) (f : ComplexL2) :
    (truncated ε f : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (∫ s : ℝ, (hardSoftDifference s : ℂ) * f (x - ε * s)) + softHilbert ε f x := by
  filter_upwards [softHilbert_coe hε f] with x hx
  have h := hard_soft_integral_difference hε f x
  rw [← hx] at h
  exact sub_eq_iff_eq_add.mp h

/-- Combine the regularized limit with a vanishing hard-cutoff correction. -/
lemma complex_truncation_assembly
    (hmem : ∀ (f : ComplexL2) (ε : ℝ), MemLp
      (fun x : ℝ => ∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x - ε * t)) 2 volume)
    (hlim : ∀ (f : ComplexL2), Tendsto
      (fun ε : ℝ => eLpNorm
        (fun x : ℝ => ∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x - ε * t)) 2 volume)
        (𝓝 0) (𝓝 0)) :
    TruncationConvergence ℂ complexHilbert := by
  constructor
  · intro ε hε f
    refine ⟨truncated_integrable ℂ hε f, ?_⟩
    exact ((hmem f ε).add (Lp.memLp (softHilbert ε f))).ae_eq
      (truncated_eq_soft_add_correction hε f).symm
  · intro f
    have hs := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun ε : ℝ => softHilbert ε f) (complexHilbert f)).mp (softHilbert_tendsto f)
    have hc := (hlim f).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hh := hc.add hs
    simp only [zero_add] at hh
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
      (Filter.Eventually.of_forall fun ε => bot_le)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have heq : (fun x : ℝ => truncated ε f x - complexHilbert f x) =ᵐ[volume]
        fun x : ℝ => (∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x - ε * t)) +
          (softHilbert ε f x - complexHilbert f x) := by
      filter_upwards [truncated_eq_soft_add_correction hε f] with x hx
      rw [hx]
      ring
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform

lemma translation_difference_norm_bound (f : ComplexL2) (a : ℝ) :
    ‖translateL2 a f - f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖translateL2 a f‖ + ‖f‖ := norm_sub_le _ _
    _ = 2 * ‖f‖ := by rw [(translateL2 a).norm_map]; ring

lemma correction_norm_integrable (f : ComplexL2) (ε : ℝ) :
    Integrable (fun t : ℝ => |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖) := by
  have hm : AEStronglyMeasurable
      (fun t : ℝ => ‖translateL2 (ε*t) f - f‖) volume :=
    ((((translateL2_continuous f).comp (continuous_const.mul continuous_id)).sub
      continuous_const).norm).aestronglyMeasurable
  apply (hardSoftDifference_integrable.norm.mul_const (2 * ‖f‖)).mono'
    (hardSoftDifference_measurable.aestronglyMeasurable.norm.mul hm)
  exact .of_forall fun t => by
    change |(|hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖)| ≤
      ‖hardSoftDifference t‖ * (2 * ‖f‖)
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (translation_difference_norm_bound f (ε*t)) (abs_nonneg _)

lemma hardSoftDifference_pointwise_bound (f : ComplexL2) (ε : ℝ) :
    (∀ᵐ x : ℝ ∂volume, Integrable (fun t : ℝ =>
      hardSoftDifference t • f (x-ε*t))) ∧
    eLpNorm (fun x : ℝ => ∫ t : ℝ, hardSoftDifference t • f (x-ε*t)) 2 volume ≤
      ENNReal.ofReal (∫ t : ℝ, |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖) := by
  let F : ℝ × ℝ → ℂ := fun z =>
    hardSoftDifference z.2 • (f (z.1-ε*z.2) - f z.1)
  have hfm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hF : Measurable F :=
    (hardSoftDifference_measurable.comp measurable_snd).smul
      ((hfm.comp (measurable_fst.sub (measurable_const.mul measurable_snd))).sub
        (hfm.comp measurable_fst))
  have hslice (t : ℝ) : eLpNorm (fun x : ℝ => F (x,t)) 2 volume =
      ENNReal.ofReal (|hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖) := by
    change eLpNorm ((hardSoftDifference t) •
      (fun x : ℝ => f (x-ε*t) - f x)) 2 volume = _
    rw [eLpNorm_const_smul]
    have he : (fun x : ℝ => f (x-ε*t) - f x) =ᵐ[volume]
        ((translateL2 (ε*t) f - f : ComplexL2) : ℝ → ℂ) := by
      filter_upwards [translateL2_coe (ε*t) f, Lp.coeFn_sub (translateL2 (ε*t) f) f]
        with x hx hs
      rw [hs]
      change f (x-ε*t) - f x = translateL2 (ε*t) f x - f x
      rw [hx]
    rw [eLpNorm_congr_ae he, ← Lp.enorm_def]
    simp only [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
  have hR : (∫⁻ t : ℝ, eLpNorm (fun x : ℝ => F (x,t)) 2 volume) =
      ENNReal.ofReal (∫ t : ℝ, |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖) := by
    simp_rw [hslice]
    exact (ofReal_integral_eq_lintegral_ofReal (correction_norm_integrable f ε)
      (.of_forall fun _ => by positivity)).symm
  obtain ⟨hi, hb⟩ := ExpandedFA.Distributions.minkowski_integral_eLpNorm
    volume volume 2 (by norm_num) (by norm_num) F hF (by rw [hR]; exact ENNReal.ofReal_lt_top)
  have heq : (fun x : ℝ => ∫ t : ℝ, F (x,t)) =ᵐ[volume]
      (fun x : ℝ => ∫ t : ℝ, hardSoftDifference t • f (x-ε*t)) := by
    filter_upwards [hi] with x hx
    have hc : Integrable (fun t : ℝ => hardSoftDifference t • f x) :=
      hardSoftDifference_integrable.smul_const (f x)
    have hfull : Integrable (fun t : ℝ => hardSoftDifference t • f (x-ε*t)) := by
      convert hx.add hc using 1
      funext t
      simp [F, smul_sub]
    change (∫ t : ℝ, hardSoftDifference t • (f (x-ε*t) - f x)) = _
    simp_rw [smul_sub]
    rw [integral_sub hfull hc, integral_smul_const, hardSoftDifference_integral, zero_smul, sub_zero]
  refine ⟨?_, ?_⟩
  · filter_upwards [hi] with x hx
    have hc : Integrable (fun t : ℝ => hardSoftDifference t • f x) :=
      hardSoftDifference_integrable.smul_const (f x)
    convert hx.add hc using 1
    funext t
    simp [F, smul_sub]
  · rw [← eLpNorm_congr_ae heq]
    exact hb.trans_eq hR

lemma correction_norm_integral_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖)
      (𝓝 0) (𝓝 0) := by
  have hm (ε : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖) volume :=
    hardSoftDifference_measurable.aestronglyMeasurable.norm.mul
      ((((translateL2_continuous f).comp (continuous_const.mul continuous_id)).sub
        continuous_const).norm).aestronglyMeasurable
  have h : Tendsto
      (fun ε : ℝ => ∫ t : ℝ, |hardSoftDifference t| * ‖translateL2 (ε*t) f - f‖)
      (𝓝 0) (𝓝 (∫ t : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => |hardSoftDifference t| * (2 * ‖f‖))
    · exact .of_forall hm
    · exact .of_forall fun ε => .of_forall fun t => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (translation_difference_norm_bound f (ε*t)) (abs_nonneg _)
    · exact hardSoftDifference_integrable.norm.mul_const (2 * ‖f‖)
    · exact .of_forall fun t => by
        have ht := (((translateL2_continuous f).comp
          (continuous_id.mul_const t)).tendsto 0).sub_const f |>.norm
        simpa only [Function.comp_apply, id_eq, zero_mul, translateL2_zero, sub_self, norm_zero, mul_zero]
          using ht.const_mul |hardSoftDifference t|
  simpa only [integral_zero] using h

lemma hardSoftDifference_pointwise_integrable (f : ComplexL2) (ε : ℝ) :
    ∀ᵐ x : ℝ ∂volume, Integrable (fun t : ℝ =>
      (hardSoftDifference t : ℂ) * f (x-ε*t)) := by
  simpa only [Complex.real_smul] using
    (hardSoftDifference_pointwise_bound f ε).1

lemma hardSoftDifference_pointwise_memLp (f : ComplexL2) (ε : ℝ) :
    MemLp (fun x : ℝ => ∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x-ε*t)) 2 volume := by
  change eLpNorm (fun x : ℝ => ∫ t : ℝ,
    (hardSoftDifference t : ℂ) * f (x-ε*t)) 2 volume < ⊤
  have hb := (hardSoftDifference_pointwise_bound f ε).2
  simp only [Complex.real_smul] at hb
  exact hb.trans_lt ENNReal.ofReal_lt_top

lemma hardSoftDifference_pointwise_tendsto (f : ComplexL2) :
    Tendsto (fun ε : ℝ =>
      eLpNorm (fun x : ℝ => ∫ t : ℝ, (hardSoftDifference t : ℂ) * f (x-ε*t)) 2 volume)
      (𝓝 0) (𝓝 0) := by
  have hupper := ENNReal.tendsto_ofReal (correction_norm_integral_tendsto f)
  rw [ENNReal.ofReal_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le)
  intro ε
  simpa only [Complex.real_smul] using (hardSoftDifference_pointwise_bound f ε).2

end ExpandedFA.SingularIntegrals.HilbertTransform

namespace ExpandedFA.SingularIntegrals.HilbertTransform
open Specs.ExpandedFA.SingularIntegrals.HilbertTransform

theorem complex_truncation_convergence : TruncationConvergence ℂ complexHilbert :=
  complex_truncation_assembly hardSoftDifference_pointwise_memLp hardSoftDifference_pointwise_tendsto

theorem real_truncation_convergence : TruncationConvergence ℝ realOperator :=
  real_truncation_of_complex complex_truncation_convergence

theorem complex_indicator_formula : IndicatorFormula ℂ complexHilbert :=
  indicatorFormula_of_truncationConvergence ℂ complexHilbert complex_truncation_convergence

theorem real_indicator_formula : IndicatorFormula ℝ realOperator :=
  indicatorFormula_of_truncationConvergence ℝ realOperator real_truncation_convergence

theorem complex_endpoint_failure : EndpointFailure ℂ complexHilbert :=
  endpointFailure_of_indicatorFormula ℂ complexHilbert complex_indicator_formula

theorem real_endpoint_failure : EndpointFailure ℝ realOperator :=
  endpointFailure_of_indicatorFormula ℝ realOperator real_indicator_formula

/-- The complete Hilbert-transform theorem for the fixed Fourier multiplier
and its real restriction, including both endpoint failures. -/
theorem full_theorem : FullTheorem := by
  obtain ⟨R, C, hRC⟩ := compatible_extensions_of_realizations realOperator real_restriction
    real_standard_realization complex_standard_realization
  exact ⟨multiplier_formula, isometry, square, bounded_linear, normalized_principal_value,
    real_valued_preservation, complex_standard_realization, complex_truncation_convergence,
    complex_indicator_formula, complex_endpoint_failure,
    realOperator, real_restriction, real_isometry, real_square, real_standard_realization,
    real_truncation_convergence, real_indicator_formula, real_endpoint_failure, R, C, hRC⟩

end ExpandedFA.SingularIntegrals.HilbertTransform
