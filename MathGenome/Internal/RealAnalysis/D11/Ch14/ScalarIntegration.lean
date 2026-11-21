import MathGenome.Internal.RealAnalysis.D11.Ch14.TotalVariation
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

open Set MeasureTheory
open scoped ENNReal MeasureTheory
universe u
noncomputable section
namespace D11.Ch14.ScalarIntegration

open D11.Ch14 Jordan TotalVariation

variable {X : Type u} [MeasurableSpace X]
variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

def signedIntegrable (ν : SignedMeasure X) (f : X → 𝕜) : Prop :=
  D11.Ch06.ScalarIntegral.scalarIntegrable (totalVariation ν) f

def complexIntegrable (ν : ComplexMeasure X) (f : X → ℂ) : Prop :=
  D11.Ch06.ScalarIntegral.scalarIntegrable (totalVariation ν) f

def signedIntegral (ν : SignedMeasure X) (f : X → 𝕜)
    (_ : signedIntegrable ν f) : 𝕜 :=
  (∫ x, f x ∂(positivePart ν)) - (∫ x, f x ∂(negativePart ν))

def complexIntegral (ν : ComplexMeasure X) (f : X → ℂ)
    (_ : complexIntegrable ν f) : ℂ :=
  ((∫ x, f x ∂(positivePart ν.re)) - (∫ x, f x ∂(negativePart ν.re))) +
  Complex.I * ((∫ x, f x ∂(positivePart ν.im)) - (∫ x, f x ∂(negativePart ν.im)))

theorem signedIntegrable_iff (ν : SignedMeasure X) (f : X → 𝕜) :
    signedIntegrable ν f ↔ Measurable f ∧ Integrable f (totalVariation ν) :=
  D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _

theorem complexIntegrable_iff (ν : ComplexMeasure X) (f : X → ℂ) :
    complexIntegrable ν f ↔ Measurable f ∧ Integrable f (totalVariation ν) :=
  D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _

theorem signed_parts_integrable (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) :
    Integrable f (positivePart ν) ∧ Integrable f (negativePart ν) := by
  have hi := ((signedIntegrable_iff ν f).mp hf).2
  rw [signed_totalVariation_eq_jordan] at hi
  exact integrable_add_measure.mp hi

theorem real_variation_le (ν : ComplexMeasure X) :
    totalVariation ν.re ≤ totalVariation ν := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E _
  calc
    ‖ν.re E‖ₑ = ENNReal.ofReal |(ν E).re| := by rw [← ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖ν E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
    _ ≤ totalVariation ν E := norm_le_totalVariation ν E

theorem imaginary_variation_le (ν : ComplexMeasure X) :
    totalVariation ν.im ≤ totalVariation ν := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E _
  calc
    ‖ν.im E‖ₑ = ENNReal.ofReal |(ν E).im| := by rw [← ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖ν E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)
    _ ≤ totalVariation ν E := norm_le_totalVariation ν E

theorem complex_parts_integrable (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) :
    signedIntegrable ν.re f ∧ signedIntegrable ν.im f := by
  obtain ⟨hm, hi⟩ := (complexIntegrable_iff ν f).mp hf
  exact ⟨(signedIntegrable_iff _ _).mpr ⟨hm, hi.mono_measure (real_variation_le ν)⟩,
    (signedIntegrable_iff _ _).mpr ⟨hm, hi.mono_measure (imaginary_variation_le ν)⟩⟩

/-- The native vector integral is used only after checking its absolute
integrability, and is identified with the required Jordan construction. -/
theorem signedIntegral_eq_native (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) :
    signedIntegral ν f hf = ∫ᵛ x, f x ∂<•ν := by
  obtain ⟨hp, hn⟩ := signed_parts_integrable ν f hf
  have hps : (positivePart ν).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hns : (negativePart ν).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  have heq := signed_eq_of_difference ν (positivePart ν) (negativePart ν)
    (jordan_decomposition ν).2
  calc
    signedIntegral ν f hf =
        ∫ᵛ x, f x ∂<•((positivePart ν).toSignedMeasure - (negativePart ν).toSignedMeasure) := by
      rw [VectorMeasure.integral_sub_vectorMeasure hps hns]
      simp only [VectorMeasure.integral_toSignedMeasure, signedIntegral]
    _ = ∫ᵛ x, f x ∂<•ν := by rw [← heq]

theorem signed_decomposition_independent (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) (μ η : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hν : ∀ E, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal)
    (hμ : Integrable f μ) (hη : Integrable f η) :
    signedIntegral ν f hf = (∫ x, f x ∂μ) - (∫ x, f x ∂η) := by
  rw [signedIntegral_eq_native, signed_eq_of_difference ν μ η hν]
  rw [VectorMeasure.integral_sub_vectorMeasure]
  · simp only [VectorMeasure.integral_toSignedMeasure]
  · simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hμ
  · simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hη

theorem signedIntegrable_add (ν : SignedMeasure X) {f g : X → 𝕜}
    (hf : signedIntegrable ν f) (hg : signedIntegrable ν g) :
    signedIntegrable ν (fun x => f x + g x) := by
  obtain ⟨hmf, hif⟩ := (signedIntegrable_iff _ _).mp hf
  obtain ⟨hmg, hig⟩ := (signedIntegrable_iff _ _).mp hg
  exact (signedIntegrable_iff _ _).mpr ⟨hmf.add hmg, hif.add hig⟩

theorem signedIntegrable_const_mul (ν : SignedMeasure X) (c : 𝕜) {f : X → 𝕜}
    (hf : signedIntegrable ν f) : signedIntegrable ν (fun x => c * f x) := by
  obtain ⟨hm, hi⟩ := (signedIntegrable_iff _ _).mp hf
  exact (signedIntegrable_iff _ _).mpr ⟨measurable_const.mul hm, hi.const_mul c⟩

theorem signedIntegral_add (ν : SignedMeasure X) (f g : X → 𝕜)
    (hf : signedIntegrable ν f) (hg : signedIntegrable ν g)
    (hfg : signedIntegrable ν (fun x => f x + g x)) :
    signedIntegral ν (fun x => f x + g x) hfg =
      signedIntegral ν f hf + signedIntegral ν g hg := by
  obtain ⟨hfp, hfn⟩ := signed_parts_integrable ν f hf
  obtain ⟨hgp, hgn⟩ := signed_parts_integrable ν g hg
  simp only [signedIntegral, integral_add hfp hgp, integral_add hfn hgn]
  abel

theorem signedIntegral_const_mul (ν : SignedMeasure X) (c : 𝕜) (f : X → 𝕜)
    (hf : signedIntegrable ν f) (hcf : signedIntegrable ν (fun x => c * f x)) :
    signedIntegral ν (fun x => c * f x) hcf = c * signedIntegral ν f hf := by
  simp only [signedIntegral, integral_const_mul, mul_sub]

theorem signedIntegrable_add_measure (ν η : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) (hg : signedIntegrable η f) :
    signedIntegrable (ν + η) f := by
  obtain ⟨hm, hi⟩ := (signedIntegrable_iff _ _).mp hf
  have hj := ((signedIntegrable_iff _ _).mp hg).2
  exact (signedIntegrable_iff _ _).mpr ⟨hm,
    VectorMeasure.Integrable.add_vectorMeasure hi hj⟩

theorem signedIntegral_add_measure (ν η : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable ν f) (hg : signedIntegrable η f)
    (hfg : signedIntegrable (ν + η) f) :
    signedIntegral (ν + η) f hfg = signedIntegral ν f hf + signedIntegral η f hg := by
  simp only [signedIntegral_eq_native]
  exact VectorMeasure.integral_add_vectorMeasure
    ((signedIntegrable_iff _ _).mp hf).2 ((signedIntegrable_iff _ _).mp hg).2

theorem signedIntegrable_smul_measure (ν : SignedMeasure X) (c : ℝ) (f : X → 𝕜)
    (hf : signedIntegrable ν f) : signedIntegrable (c • ν) f := by
  obtain ⟨hm, hi⟩ := (signedIntegrable_iff _ _).mp hf
  exact (signedIntegrable_iff _ _).mpr ⟨hm,
    VectorMeasure.Integrable.smul_vectorMeasure hi c⟩

theorem signedIntegral_smul_measure (ν : SignedMeasure X) (c : ℝ) (f : X → 𝕜)
    (hf : signedIntegrable ν f) (hcf : signedIntegrable (c • ν) f) :
    signedIntegral (c • ν) f hcf = c • signedIntegral ν f hf := by
  simp only [signedIntegral_eq_native, VectorMeasure.integral_smul_vectorMeasure]

theorem complexIntegral_eq_parts (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) (hr : signedIntegrable ν.re f)
    (hi : signedIntegrable ν.im f) :
    complexIntegral ν f hf = signedIntegral ν.re f hr + Complex.I * signedIntegral ν.im f hi := rfl

theorem complex_decomposition_independent (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) (μ₁ μ₂ μ₃ μ₄ : Measure X)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (hν : ∀ E, MeasurableSet E → ν E =
      ((μ₁ E).toReal : ℂ) - ((μ₂ E).toReal : ℂ) +
      Complex.I * (((μ₃ E).toReal : ℂ) - ((μ₄ E).toReal : ℂ)))
    (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂)
    (h₃ : Integrable f μ₃) (h₄ : Integrable f μ₄) :
    complexIntegral ν f hf = ((∫ x, f x ∂μ₁) - (∫ x, f x ∂μ₂)) +
      Complex.I * ((∫ x, f x ∂μ₃) - (∫ x, f x ∂μ₄)) := by
  obtain ⟨hr, hi⟩ := complex_parts_integrable ν f hf
  rw [complexIntegral_eq_parts ν f hf hr hi]
  rw [signed_decomposition_independent ν.re f hr μ₁ μ₂ _ h₁ h₂,
    signed_decomposition_independent ν.im f hi μ₃ μ₄ _ h₃ h₄]
  · intro E hE
    change (ν E).im = _
    simpa using congrArg Complex.im (hν E hE)
  · intro E hE
    change (ν E).re = _
    simpa using congrArg Complex.re (hν E hE)

theorem complexIntegrable_add (ν : ComplexMeasure X) {f g : X → ℂ}
    (hf : complexIntegrable ν f) (hg : complexIntegrable ν g) :
    complexIntegrable ν (fun x => f x + g x) := by
  obtain ⟨hmf, hif⟩ := (complexIntegrable_iff _ _).mp hf
  obtain ⟨hmg, hig⟩ := (complexIntegrable_iff _ _).mp hg
  exact (complexIntegrable_iff _ _).mpr ⟨hmf.add hmg, hif.add hig⟩

theorem complexIntegrable_const_mul (ν : ComplexMeasure X) (c : ℂ) {f : X → ℂ}
    (hf : complexIntegrable ν f) : complexIntegrable ν (fun x => c * f x) := by
  obtain ⟨hm, hi⟩ := (complexIntegrable_iff _ _).mp hf
  exact (complexIntegrable_iff _ _).mpr ⟨measurable_const.mul hm, hi.const_mul c⟩

theorem complexIntegral_add (ν : ComplexMeasure X) (f g : X → ℂ)
    (hf : complexIntegrable ν f) (hg : complexIntegrable ν g)
    (hfg : complexIntegrable ν (fun x => f x + g x)) :
    complexIntegral ν (fun x => f x + g x) hfg =
      complexIntegral ν f hf + complexIntegral ν g hg := by
  obtain ⟨hfr, hfi⟩ := complex_parts_integrable ν f hf
  obtain ⟨hgr, hgi⟩ := complex_parts_integrable ν g hg
  obtain ⟨hfgr, hfgi⟩ := complex_parts_integrable ν _ hfg
  rw [complexIntegral_eq_parts _ _ hfg hfgr hfgi,
    complexIntegral_eq_parts _ _ hf hfr hfi,
    complexIntegral_eq_parts _ _ hg hgr hgi,
    signedIntegral_add _ _ _ hfr hgr, signedIntegral_add _ _ _ hfi hgi]
  ring

theorem complexIntegral_const_mul (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable ν f) (hcf : complexIntegrable ν (fun x => c * f x)) :
    complexIntegral ν (fun x => c * f x) hcf = c * complexIntegral ν f hf := by
  simp only [complexIntegral, integral_const_mul]
  ring

theorem complexIntegrable_add_measure (ν η : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) (hg : complexIntegrable η f) :
    complexIntegrable (ν + η) f := by
  obtain ⟨hm, hi⟩ := (complexIntegrable_iff _ _).mp hf
  have hj := ((complexIntegrable_iff _ _).mp hg).2
  exact (complexIntegrable_iff _ _).mpr ⟨hm,
    VectorMeasure.Integrable.add_vectorMeasure hi hj⟩

theorem complexIntegral_add_measure (ν η : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable ν f) (hg : complexIntegrable η f)
    (hfg : complexIntegrable (ν + η) f) :
    complexIntegral (ν + η) f hfg = complexIntegral ν f hf + complexIntegral η f hg := by
  obtain ⟨hfr, hfi⟩ := complex_parts_integrable ν f hf
  obtain ⟨hgr, hgi⟩ := complex_parts_integrable η f hg
  obtain ⟨hfgr, hfgi⟩ := complex_parts_integrable (ν + η) f hfg
  rw [complexIntegral_eq_parts _ _ hfg hfgr hfgi,
    complexIntegral_eq_parts _ _ hf hfr hfi,
    complexIntegral_eq_parts _ _ hg hgr hgi]
  simp only [map_add] at hfgr hfgi ⊢
  rw [signedIntegral_add_measure _ _ _ hfr hgr,
    signedIntegral_add_measure _ _ _ hfi hgi]
  ring

theorem complexIntegrable_smul_measure (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable ν f) : complexIntegrable (c • ν) f := by
  obtain ⟨hm, hi⟩ := (complexIntegrable_iff _ _).mp hf
  apply (complexIntegrable_iff _ _).mpr
  refine ⟨hm, ?_⟩
  simpa only [totalVariation, VectorMeasure.variation_smul] using
    (hi.smul_measure_nnreal (c := ‖c‖₊))

theorem complex_smul_re (ν : ComplexMeasure X) (c : ℂ) :
    (c • ν).re = c.re • ν.re - c.im • ν.im := by
  apply VectorMeasure.ext
  intro E hE
  change (c * ν E).re = c.re * (ν E).re - c.im * (ν E).im
  exact Complex.mul_re c (ν E)

theorem complex_smul_im (ν : ComplexMeasure X) (c : ℂ) :
    (c • ν).im = c.re • ν.im + c.im • ν.re := by
  apply VectorMeasure.ext
  intro E hE
  change (c * ν E).im = c.re * (ν E).im + c.im * (ν E).re
  exact Complex.mul_im c (ν E)

theorem complexIntegral_smul_measure (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable ν f) (hcf : complexIntegrable (c • ν) f) :
    complexIntegral (c • ν) f hcf = c * complexIntegral ν f hf := by
  obtain ⟨hr, hi⟩ := complex_parts_integrable ν f hf
  obtain ⟨hcr, hci⟩ := complex_parts_integrable (c • ν) f hcf
  have hr' := ((signedIntegrable_iff _ _).mp hr).2
  have hi' := ((signedIntegrable_iff _ _).mp hi).2
  have hrr := VectorMeasure.Integrable.smul_vectorMeasure hr' c.re
  have hri := VectorMeasure.Integrable.smul_vectorMeasure hr' c.im
  have hir := VectorMeasure.Integrable.smul_vectorMeasure hi' c.re
  have hii := VectorMeasure.Integrable.smul_vectorMeasure hi' c.im
  rw [complexIntegral_eq_parts _ _ hcf hcr hci, complexIntegral_eq_parts _ _ hf hr hi]
  simp only [signedIntegral_eq_native]
  rw [complex_smul_re, complex_smul_im,
    VectorMeasure.integral_sub_vectorMeasure hrr hii,
    VectorMeasure.integral_add_vectorMeasure hir hri]
  simp only [VectorMeasure.integral_smul_vectorMeasure, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq, mul_neg, mul_one, sub_eq_add_neg]

theorem signedIntegrable_simple (ν : SignedMeasure X) (s : SimpleFunc X 𝕜) :
    signedIntegrable ν s := by
  letI := signed_finite ν
  exact (signedIntegrable_iff _ _).mpr ⟨s.measurable, s.integrable_of_isFiniteMeasure⟩

theorem complexIntegrable_simple (ν : ComplexMeasure X) (s : SimpleFunc X ℂ) :
    complexIntegrable ν s := by
  letI := complex_finite ν
  exact (complexIntegrable_iff _ _).mpr ⟨s.measurable, s.integrable_of_isFiniteMeasure⟩

theorem signedIntegral_simple (ν : SignedMeasure X) (s : SimpleFunc X 𝕜)
    (hs : signedIntegrable ν s) :
    signedIntegral ν s hs = ∑ c ∈ s.range, ν (s ⁻¹' {c}) • c := by
  obtain ⟨hp, hn⟩ := signed_parts_integrable ν s hs
  rw [signedIntegral, s.integral_eq_sum hp, s.integral_eq_sum hn, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [(jordan_decomposition ν).2 _ (s.measurableSet_fiber c), sub_smul]
  rfl

theorem complexIntegral_simple (ν : ComplexMeasure X) (s : SimpleFunc X ℂ)
    (hs : complexIntegrable ν s) :
    complexIntegral ν s hs = ∑ c ∈ s.range, c * ν (s ⁻¹' {c}) := by
  obtain ⟨hr, hi⟩ := complex_parts_integrable ν s hs
  rw [complexIntegral_eq_parts _ _ hs hr hi, signedIntegral_simple _ _ hr,
    signedIntegral_simple _ _ hi, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Complex.real_smul]
  change ((ν _).re : ℂ) * c + Complex.I * (((ν _).im : ℂ) * c) = _
  conv_rhs => rw [← Complex.re_add_im (ν (s ⁻¹' {c}))]
  ring

theorem signedIntegrable_indicator (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : 𝕜) :
    signedIntegrable ν (E.indicator (fun _ => c)) := by
  letI := signed_finite ν
  exact (signedIntegrable_iff _ _).mpr
    ⟨measurable_const.indicator hE, (integrable_const c).indicator hE⟩

theorem complexIntegrable_indicator (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : ℂ) :
    complexIntegrable ν (E.indicator (fun _ => c)) := by
  letI := complex_finite ν
  exact (complexIntegrable_iff _ _).mpr
    ⟨measurable_const.indicator hE, (integrable_const c).indicator hE⟩

theorem signedIntegral_indicator_const (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : 𝕜) (hf : signedIntegrable ν (E.indicator (fun _ => c))) :
    signedIntegral ν (E.indicator (fun _ => c)) hf = ν E • c := by
  rw [signedIntegral, integral_indicator_const _ hE, integral_indicator_const _ hE,
    (jordan_decomposition ν).2 E hE, sub_smul]
  rfl

theorem complexIntegral_indicator_const (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : ℂ) (hf : complexIntegrable ν (E.indicator (fun _ => c))) :
    complexIntegral ν (E.indicator (fun _ => c)) hf = c * ν E := by
  obtain ⟨hr, hi⟩ := complex_parts_integrable ν _ hf
  rw [complexIntegral_eq_parts _ _ hf hr hi,
    signedIntegral_indicator_const _ _ hE c hr, signedIntegral_indicator_const _ _ hE c hi]
  simp only [Complex.real_smul]
  change ((ν _).re : ℂ) * c + Complex.I * (((ν _).im : ℂ) * c) = _
  conv_rhs => rw [← Complex.re_add_im (ν E)]
  ring

theorem signedIntegral_indicator (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (hf : signedIntegrable ν (E.indicator (fun _ => (1 : ℝ)))) :
    signedIntegral ν (E.indicator (fun _ => (1 : ℝ))) hf = ν E := by
  rw [signedIntegral_indicator_const _ _ hE]
  exact mul_one _

theorem complexIntegral_indicator (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (hf : complexIntegrable ν (E.indicator (fun _ => (1 : ℂ)))) :
    complexIntegral ν (E.indicator (fun _ => (1 : ℂ))) hf = ν E := by
  rw [complexIntegral_indicator_const _ _ hE, one_mul]

end D11.Ch14.ScalarIntegration
