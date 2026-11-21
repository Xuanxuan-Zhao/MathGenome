import MathGenome.Internal.RealAnalysis.D11.Ch19.FunctionalJordan
import MathGenome.Internal.RealAnalysis.D11.Ch19.FinitePositiveCzero
import MathGenome.Internal.RealAnalysis.D11.Ch19.VariationTestFunction
import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarIntegration
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroDuality
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory
namespace D11.Ch19.CzeroDuality
open D11.Ch14.ScalarIntegration D11.Ch14.TotalVariation D11.Ch14.Jordan
universe u
variable {X : Type u} [TopologicalSpace X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma signed_czero_integrable (ν : SignedMeasure X) (f : Czero X 𝕜) :
    signedIntegrable ν (f : X → 𝕜) := by
  let : IsFiniteMeasure (totalVariation ν) := signed_finite ν
  exact (signedIntegrable_iff ν f).mpr ⟨f.continuous.measurable, f.toBCF.integrable _⟩

lemma complex_czero_integrable (ν : ComplexMeasure X) (f : Czero X ℂ) :
    complexIntegrable ν (f : X → ℂ) := by
  let : IsFiniteMeasure (totalVariation ν) := complex_finite ν
  exact (complexIntegrable_iff ν f).mpr ⟨f.continuous.measurable, f.toBCF.integrable _⟩

lemma integral_norm_czero_le (μ : Measure X) [IsFiniteMeasure μ] (f : Czero X 𝕜) :
    (∫ x, ‖f x‖ ∂μ) ≤ (μ univ).toReal * ‖f‖ := by
  calc
    (∫ x, ‖f x‖ ∂μ) ≤ ∫ _, ‖f‖ ∂μ :=
      integral_mono (f.toBCF.integrable μ).norm (integrable_const _)
        (fun x => f.toBCF.norm_coe_le_norm x)
    _ = (μ univ).toReal * ‖f‖ := by simp [integral_const, smul_eq_mul, measureReal_def]

def signedFunctional (ν : SignedMeasure X) : Czero X 𝕜 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => signedIntegral ν f (signed_czero_integrable ν f)
      map_add' := fun f g => signedIntegral_add ν f g _ _ _
      map_smul' := fun a f => signedIntegral_const_mul ν a f _ _ }
    ((totalVariation ν) univ).toReal (fun f => by
      let : IsFiniteMeasure (totalVariation ν) := signed_finite ν
      exact (D11.Ch14.IntegralVariationBound.norm_signedIntegral_le ν f (signed_czero_integrable ν f)).trans
        (integral_norm_czero_le (totalVariation ν) f))

def complexFunctional (ν : ComplexMeasure X) : Czero X ℂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => complexIntegral ν f (complex_czero_integrable ν f)
      map_add' := fun f g => complexIntegral_add ν f g _ _ _
      map_smul' := fun a f => complexIntegral_const_mul ν a f _ _ }
    ((totalVariation ν) univ).toReal (fun f => by
      let : IsFiniteMeasure (totalVariation ν) := complex_finite ν
      exact (D11.Ch14.IntegralVariationBound.norm_complexIntegral_le ν f (complex_czero_integrable ν f)).trans
        (integral_norm_czero_le (totalVariation ν) f))

/-- Scalar linearity is in the measure and the test function, with no conjugation. -/
def signedMap : SignedMeasure X →ₗ[ℝ] (Czero X ℝ →L[ℝ] ℝ) where
  toFun := signedFunctional
  map_add' ν η := by
    ext f
    exact signedIntegral_add_measure ν η f (signed_czero_integrable ν f)
      (signed_czero_integrable η f) (signed_czero_integrable (ν + η) f)
  map_smul' c ν := by
    ext f
    exact signedIntegral_smul_measure ν c f (signed_czero_integrable ν f)
      (signed_czero_integrable (c • ν) f)

def complexMap : ComplexMeasure X →ₗ[ℂ] (Czero X ℂ →L[ℂ] ℂ) where
  toFun := complexFunctional
  map_add' ν η := by
    ext f
    exact complexIntegral_add_measure ν η f (complex_czero_integrable ν f)
      (complex_czero_integrable η f) (complex_czero_integrable (ν + η) f)
  map_smul' c ν := by
    ext f
    exact complexIntegral_smul_measure ν c f (complex_czero_integrable ν f)
      (complex_czero_integrable (c • ν) f)

lemma signedMap_sub (ν η : SignedMeasure X) :
    signedMap (ν - η) = signedMap ν - signedMap η := by
  have h := (signedMap (X := X)).map_add (ν - η) η
  rw [sub_add_cancel ν η] at h
  ext f
  have hf := congrArg (fun (L : Czero X ℝ →L[ℝ] ℝ) => L f) h
  change signedMap ν f = signedMap (ν - η) f + signedMap η f at hf
  change signedMap (ν - η) f = signedMap ν f - signedMap η f
  linarith

lemma complexMap_sub (ν η : ComplexMeasure X) :
    complexMap (ν - η) = complexMap ν - complexMap η := by
  have h := (complexMap (X := X)).map_add (ν - η) η
  rw [sub_add_cancel ν η] at h
  ext f
  have hf := congrArg (fun (L : Czero X ℂ →L[ℂ] ℂ) => L f) h
  change complexMap ν f = complexMap (ν - η) f + complexMap η f at hf
  change complexMap (ν - η) f = complexMap ν f - complexMap η f
  exact eq_sub_of_add_eq hf.symm

variable [T2Space X] [LocallyCompactSpace X]

lemma signed_radon_sub (ν η : SignedMeasure X) (hν : isSignedRadon ν)
    (hη : isSignedRadon η) : isSignedRadon (ν - η) := by
  let : IsFiniteMeasure (totalVariation ν) := signed_finite ν
  let : IsFiniteMeasure (totalVariation η) := signed_finite η
  exact (signedRadon_iff_variation _).mpr
    (finite_radon_of_le _ _ (finite_radon_add _ _
      ((signedRadon_iff_variation _).mp hν) ((signedRadon_iff_variation _).mp hη))
      VectorMeasure.variation_sub_le)

lemma complex_radon_sub (ν η : ComplexMeasure X) (hν : isComplexRadon ν)
    (hη : isComplexRadon η) : isComplexRadon (ν - η) := by
  let : IsFiniteMeasure (totalVariation ν) := complex_finite ν
  let : IsFiniteMeasure (totalVariation η) := complex_finite η
  exact (complexRadon_iff_variation _).mpr
    (finite_radon_of_le _ _ (finite_radon_add _ _
      ((complexRadon_iff_variation _).mp hν) ((complexRadon_iff_variation _).mp hη))
      VectorMeasure.variation_sub_le)

lemma signedFunctional_norm (ν : SignedMeasure X) (hν : isSignedRadon ν) :
    ‖signedFunctional (𝕜 := ℝ) ν‖ = (totalVariation ν univ).toReal := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro f
    exact (D11.Ch14.IntegralVariationBound.norm_signedIntegral_le ν f (signed_czero_integrable ν f)).trans
      (by let : IsFiniteMeasure (totalVariation ν) := signed_finite ν
          exact integral_norm_czero_le (totalVariation ν) f)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hfn, hf, htest⟩ :=
      VariationTestFunction.signed_variation_test_function ν hν ε hε
    have hb : ‖signedIntegral ν f hf‖ ≤ ‖signedFunctional (𝕜 := ℝ) ν‖ := by
      calc
        _ = ‖signedFunctional ν (ccInclusion X ℝ f)‖ := rfl
        _ ≤ ‖signedFunctional (𝕜 := ℝ) ν‖ * ‖ccInclusion X ℝ f‖ :=
          (signedFunctional (𝕜 := ℝ) ν).le_opNorm (ccInclusion X ℝ f)
        _ ≤ ‖signedFunctional (𝕜 := ℝ) ν‖ := by
          have hni : ‖ccInclusion X _ f‖ ≤ 1 :=
            (czero_norm_le_iff X _ _ 1 zero_le_one).mpr (fun x =>
              (f.toBoundedContinuousFunction.norm_coe_le_norm x).trans hfn)
          simpa using mul_le_mul_of_nonneg_left hni (norm_nonneg (signedFunctional (𝕜 := ℝ) ν))
    change (totalVariation ν univ).toReal - ε ≤ ‖signedIntegral ν f hf‖ at htest
    linarith

lemma complexFunctional_norm (ν : ComplexMeasure X) (hν : isComplexRadon ν) :
    ‖complexFunctional ν‖ = (totalVariation ν univ).toReal := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro f
    exact (D11.Ch14.IntegralVariationBound.norm_complexIntegral_le ν f (complex_czero_integrable ν f)).trans
      (by let : IsFiniteMeasure (totalVariation ν) := complex_finite ν
          exact integral_norm_czero_le (totalVariation ν) f)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hfn, hf, htest⟩ :=
      VariationTestFunction.complex_variation_test_function ν hν ε hε
    have hb : ‖complexIntegral ν f hf‖ ≤ ‖complexFunctional ν‖ := by
      calc
        _ = ‖complexFunctional ν (ccInclusion X ℂ f)‖ := rfl
        _ ≤ ‖complexFunctional ν‖ * ‖ccInclusion X ℂ f‖ :=
          (complexFunctional ν).le_opNorm (ccInclusion X ℂ f)
        _ ≤ ‖complexFunctional ν‖ := by
          have hni : ‖ccInclusion X _ f‖ ≤ 1 :=
            (czero_norm_le_iff X _ _ 1 zero_le_one).mpr (fun x =>
              (f.toBoundedContinuousFunction.norm_coe_le_norm x).trans hfn)
          simpa using mul_le_mul_of_nonneg_left hni (norm_nonneg (complexFunctional ν))
    change (totalVariation ν univ).toReal - ε ≤ ‖complexIntegral ν f hf‖ at htest
    linarith

/-- A bounded positive functional has a finite Radon positive representative. -/
lemma positive_representation (P : Czero X ℝ →L[ℝ] ℝ)
    (hP : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ P f) :
    ∃ μ : Measure X, D11.Ch18.isRadon μ ∧ IsFiniteMeasure μ ∧
      ∀ f : Czero X ℝ, P f = ∫ x, f x ∂μ := by
  let I := P.toLinearMap.comp (ccInclusion X ℝ)
  have hI : Specs.D11.Ch19.PositiveContentOuterMeasure.Positive I := by
    intro f hf
    exact hP _ hf
  obtain ⟨μ, hμ, _⟩ := PositiveRieszMarkov.real_representation I hI
  have hExt : Specs.D11.Ch19.FinitePositiveCzero.ExtendsIntegral μ P := by
    intro f
    exact (hμ.2 f).choose_spec
  have hfin : μ univ < ⊤ :=
    (FinitePositiveCzero.mass_le_norm ℝ μ hμ.1 P hExt).trans_lt ENNReal.ofReal_lt_top
  refine ⟨μ, hμ.1, ⟨hfin⟩, ?_⟩
  exact fun f => (FinitePositiveCzero.extension_identification ℝ μ hμ.1 P hExt).2.2.1 f |>.2.2

lemma signed_surjective (L : Czero X ℝ →L[ℝ] ℝ) :
    ∃ ν : SignedMeasure X, isSignedRadon ν ∧ signedMap ν = L := by
  obtain ⟨P, _, hP, hN, _, _⟩ := D11.Ch19.functional_jordan X L
  obtain ⟨μ, hμ, hμfin, hμrep⟩ := positive_representation P hP
  obtain ⟨η, hη, hηfin, hηrep⟩ := positive_representation (P - L) hN
  letI := hμfin
  letI := hηfin
  let ν := μ.toSignedMeasure - η.toSignedMeasure
  have hν (E : Set X) (hE : MeasurableSet E) :
      ν E = (μ E).toReal - (η E).toReal := Measure.toSignedMeasure_sub_apply hE
  have hmin := jordan_minimal ν μ η hν
  have hRad : isSignedRadon ν :=
    ⟨finite_radon_of_le μ _ hμ hmin.1, finite_radon_of_le η _ hη hmin.2⟩
  refine ⟨ν, hRad, ?_⟩
  ext f
  change signedIntegral ν f (signed_czero_integrable ν f) = L f
  rw [signed_decomposition_independent ν f _ μ η hν
    (f.toBCF.integrable μ) (f.toBCF.integrable η), ← hμrep f, ← hηrep f]
  simp

lemma signed_injective (ν η : SignedMeasure X) (hν : isSignedRadon ν)
    (hη : isSignedRadon η) (he : signedMap ν = signedMap η) : ν = η := by
  apply sub_eq_zero.mp
  apply (signed_norm_eq_zero_iff (ν - η)).mp
  change (totalVariation (ν - η) univ).toReal = 0
  rw [← signedFunctional_norm _ (signed_radon_sub ν η hν hη)]
  change ‖signedMap (ν - η)‖ = 0
  rw [signedMap_sub, he]
  have hz : signedMap η - signedMap η = 0 := by ext f; exact sub_self _
  rw [hz]
  exact @norm_zero (Czero X ℝ →L[ℝ] ℝ) inferInstance

theorem real_duality : Specs.D11.Ch19.CzeroDuality.real_duality.{u} := by
  intro X _ _ _
  refine ⟨signedMap, ?_, ?_, ?_, ?_⟩
  · intro ν f
    exact ⟨signed_czero_integrable ν f, rfl⟩
  · exact signedFunctional_norm
  · intro ν η hν hη
    rw [← signedMap_sub]
    exact signedFunctional_norm _ (signed_radon_sub ν η hν hη)
  · intro L
    obtain ⟨ν, hν, he⟩ := signed_surjective L
    exact ⟨ν, ⟨hν, he⟩, fun η hη => signed_injective η ν hη.1 hν (hη.2.trans he.symm)⟩

/-- The ordinary real-to-complex inclusion of the canonical C0 spaces. -/
def complexify (f : Czero X ℝ) : Czero X ℂ where
  toFun x := (f x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous
  zero_at_infty' := by
    simpa using! (Complex.continuous_ofReal.tendsto 0).comp (zero_at_infty f)

def realEmbedding : Czero X ℝ →L[ℝ] Czero X ℂ :=
  LinearMap.mkContinuous
    { toFun := complexify
      map_add' := by intro f g; ext x; simp [complexify]
      map_smul' := by intro a f; ext x; simp [complexify, smul_eq_mul] }
    1 (fun f => by
      rw [one_mul]
      apply (czero_norm_le_iff X ℂ _ ‖f‖ (norm_nonneg f)).mpr
      intro x
      change ‖(f x : ℂ)‖ ≤ ‖f‖
      simpa only [Complex.norm_real, Real.norm_eq_abs, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using! f.toBCF.norm_coe_le_norm x)

def realFunction (f : Czero X ℂ) : Czero X ℝ where
  toFun x := (f x).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  zero_at_infty' := by
    simpa using! (Complex.continuous_re.tendsto 0).comp (zero_at_infty f)

def imaginaryFunction (f : Czero X ℂ) : Czero X ℝ where
  toFun x := (f x).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  zero_at_infty' := by
    simpa using! (Complex.continuous_im.tendsto 0).comp (zero_at_infty f)

lemma function_decomposition (f : Czero X ℂ) :
    f = realEmbedding (realFunction f) + Complex.I • realEmbedding (imaginaryFunction f) := by
  ext x
  change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (f x)).symm

lemma complex_functional_ext (L M : Czero X ℂ →L[ℂ] ℂ)
    (h : ∀ f : Czero X ℝ, L (realEmbedding f) = M (realEmbedding f)) : L = M := by
  ext f
  rw [function_decomposition f, map_add, map_add, map_smul, map_smul, h, h]

lemma complexFunctional_parts (α β : SignedMeasure X) (f : Czero X ℝ) :
    complexFunctional (α.toComplexMeasure β) (realEmbedding f) =
      (signedMap α f : ℂ) + Complex.I * (signedMap β f : ℂ) := by
  change ((∫ x, (f x : ℂ) ∂positivePart α) - (∫ x, (f x : ℂ) ∂negativePart α)) +
      Complex.I * ((∫ x, (f x : ℂ) ∂positivePart β) - (∫ x, (f x : ℂ) ∂negativePart β)) =
    (((∫ x, f x ∂positivePart α) - (∫ x, f x ∂negativePart α) : ℝ) : ℂ) +
      Complex.I * (((∫ x, f x ∂positivePart β) - (∫ x, f x ∂negativePart β) : ℝ) : ℂ)
  simp only [integral_complex_ofReal, Complex.ofReal_sub]

lemma complex_surjective (L : Czero X ℂ →L[ℂ] ℂ) :
    ∃ ν : ComplexMeasure X, isComplexRadon ν ∧ complexMap ν = L := by
  let R := (L.restrictScalars ℝ).comp realEmbedding
  let A := Complex.reCLM.comp R
  let B := Complex.imCLM.comp R
  obtain ⟨α, hα, heα⟩ := signed_surjective A
  obtain ⟨β, hβ, heβ⟩ := signed_surjective B
  refine ⟨α.toComplexMeasure β, ⟨hα, hβ⟩, ?_⟩
  apply complex_functional_ext
  intro f
  change complexFunctional (α.toComplexMeasure β) (realEmbedding f) = L (realEmbedding f)
  rw [complexFunctional_parts, heα, heβ]
  change ((L (realEmbedding f)).re : ℂ) + Complex.I * ((L (realEmbedding f)).im : ℂ) = _
  simpa only [mul_comm] using Complex.re_add_im (L (realEmbedding f))

lemma complex_injective (ν η : ComplexMeasure X) (hν : isComplexRadon ν)
    (hη : isComplexRadon η) (he : complexMap ν = complexMap η) : ν = η := by
  apply sub_eq_zero.mp
  apply (complex_norm_eq_zero_iff (ν - η)).mp
  change (totalVariation (ν - η) univ).toReal = 0
  rw [← complexFunctional_norm _ (complex_radon_sub ν η hν hη)]
  change ‖complexMap (ν - η)‖ = 0
  rw [complexMap_sub, he]
  have hz : complexMap η - complexMap η = 0 := by ext f; exact sub_self _
  rw [hz]
  exact @norm_zero (Czero X ℂ →L[ℂ] ℂ) inferInstance

theorem complex_duality : Specs.D11.Ch19.CzeroDuality.complex_duality.{u} := by
  intro X _ _ _
  refine ⟨complexMap, ?_, ?_, ?_, ?_⟩
  · intro ν f
    exact ⟨complex_czero_integrable ν f, rfl⟩
  · exact complexFunctional_norm
  · intro ν η hν hη
    rw [← complexMap_sub]
    exact complexFunctional_norm _ (complex_radon_sub ν η hν hη)
  · intro L
    obtain ⟨ν, hν, he⟩ := complex_surjective L
    exact ⟨ν, ⟨hν, he⟩, fun η hη => complex_injective η ν hη.1 hν (hη.2.trans he.symm)⟩

end D11.Ch19.CzeroDuality
