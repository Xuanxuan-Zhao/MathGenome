import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.VolterraResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolvent

/-! Scalar continuous kernels in `fa2:p2:kernel-compactness`.
The operator and its Banach-valued specialization are definitionally the same.
The affine identification below verifies the actual integral after translating
both variables by a; the supremum norm is preserved by this coordinate change. -/
noncomputable section
open Set MeasureTheory
open ExpandedFA.PartV
namespace ExpandedFA.IntegralOperators.VolterraResolvent

universe u v

theorem compact_kernels : Spec.CompactKernels.{u,v} :=
  ContinuousKernelCompactness.canonical_properties

theorem neumann_series : Spec.NeumannSeries := by
  intro 𝕜 X _ _ _ _ T hT
  exact ⟨isUnit_one_sub_of_norm_lt_one hT, hasSum_geom_series_inverse T hT⟩

theorem scalar_formula : Spec.ScalarFormula := by
  intro 𝕜 _ a b hab k
  refine ⟨?_, ?_, ?_⟩
  · intro f x
    rw [volterra_apply_integral hab (multiplicationKernel k)]
    change @intervalIntegral 𝕜 _ (NormedSpace.restrictScalars ℝ 𝕜 𝕜)
      (scalarIntegrand hab k f x) a (x : ℝ) volume = _
    rw [NormedSpace.restrictScalars_eq]
  · intro f x y hy
    exact volterraIntegrand_eq hab (multiplicationKernel k) f x y hy
  · intro p
    exact ContinuousLinearMap.opNorm_mul_apply 𝕜 𝕜 (k p)

theorem factorial_bound : Spec.FactorialBound := by
  intro 𝕜 _ a b hab k M hM
  apply volterra_factorial_uniform_operator_norm 𝕜 𝕜 a b hab (multiplicationKernel k) M
  intro p
  simpa only [multiplicationKernel, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ContinuousLinearMap.opNorm_mul_apply] using hM p

theorem inverse_series : Spec.InverseSeries := by
  intro 𝕜 _ a b hab k lam
  have hi := volterra_inverse_series 𝕜 𝕜 a b hab (multiplicationKernel k) lam
  obtain ⟨S, hn, _, _, _, _, _⟩ :=
    volterra_resolvent 𝕜 𝕜 a b hab (multiplicationKernel k) lam
  exact ⟨hi.1, hn, hi.2.1⟩

theorem complex_spectrum : Spec.ComplexSpectrum := by
  intro a b hab k
  exact volterra_complex_spectrum ℂ a b hab.le (multiplicationKernel k)

theorem singleton_inverse : Spec.SingletonInverse := by
  intro 𝕜 _ a k
  exact volterra_singleton_resolvent 𝕜 𝕜 a (multiplicationKernel k)

section Translation
variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b)

/-- Precomposition with t ↦ t+a and its inverse x ↦ x-a. -/
def translationIsometry :
    C(VolterraInterval a b, 𝕜) ≃ₗᵢ[𝕜] C(VolterraInterval 0 (b-a), 𝕜) := by
  let e : C(VolterraInterval a b, 𝕜) ≃ₗ[𝕜] C(VolterraInterval 0 (b-a), 𝕜) :=
    { toFun := translatedFunction hab
      invFun := fun g => g.comp ⟨(intervalTranslation hab).symm, (intervalTranslation hab).symm.continuous⟩
      left_inv := by intro f; ext x; exact congrArg f ((intervalTranslation hab).apply_symm_apply x)
      right_inv := by intro g; ext t; exact congrArg g ((intervalTranslation hab).symm_apply_apply t)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine { e with norm_map' := ?_ }
  intro f
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      (fun t => f.norm_coe_le_norm (intervalTranslation hab t))
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    have h := (e f).norm_coe_le_norm ((intervalTranslation hab).symm x)
    change ‖f ((intervalTranslation hab) ((intervalTranslation hab).symm x))‖ ≤ ‖e f‖ at h
    simpa only [Homeomorph.apply_symm_apply] using h

/-- Translation of the integrand on the actual integration interval. -/
theorem translated_integrand (k : C(volterraTriangle a b, 𝕜))
    (f : C(VolterraInterval a b, 𝕜)) (t : VolterraInterval 0 (b-a))
    (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
    scalarIntegrand (sub_nonneg.mpr hab) (translatedKernel k)
      (translatedFunction hab f) t s =
    scalarIntegrand hab k f (intervalTranslation hab t) (s+a) := by
  have hsa : s+a ∈ Icc a ((intervalTranslation hab t : VolterraInterval a b) : ℝ) := by
    change a ≤ s+a ∧ s+a ≤ (t : ℝ)+a
    constructor <;> linarith [hs.1, hs.2]
  rw [(scalar_formula 𝕜 0 (b-a) (sub_nonneg.mpr hab) (translatedKernel k)).2.1 _ _ _ hs,
    (scalar_formula 𝕜 a b hab k).2.1 _ _ _ hsa]
  rfl

/-- Change of variable y=s+a has Jacobian one and endpoints a and x. -/
theorem translated_operator (k : C(volterraTriangle a b, 𝕜))
    (f : C(VolterraInterval a b, 𝕜)) :
    translatedFunction hab (scalarVolterra hab k f) =
      scalarVolterra (sub_nonneg.mpr hab) (translatedKernel k) (translatedFunction hab f) := by
  ext t
  change scalarVolterra hab k f (intervalTranslation hab t) = _
  rw [(scalar_formula 𝕜 a b hab k).1,
    (scalar_formula 𝕜 0 (b-a) (sub_nonneg.mpr hab) (translatedKernel k)).1]
  have h := intervalIntegral.integral_comp_add_right
    (a := 0) (b := (t : ℝ)) (scalarIntegrand hab k f (intervalTranslation hab t)) a
  change (∫ y in a..((t : ℝ)+a), scalarIntegrand hab k f (intervalTranslation hab t) y) = _
  simp only [zero_add] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  exact (translated_integrand hab k f t s hs).symm

end Translation

theorem affine_identification : Spec.AffineIdentification := by
  intro 𝕜 _ a b hab
  refine ⟨translationIsometry (𝕜 := 𝕜) hab, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro k f
  exact translated_operator hab k f

end ExpandedFA.IntegralOperators.VolterraResolvent
