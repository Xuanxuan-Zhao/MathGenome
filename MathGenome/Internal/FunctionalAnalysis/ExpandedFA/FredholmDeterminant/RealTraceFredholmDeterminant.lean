import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealTraceFredholmDeterminant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.RealTraceDeterminantContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceFredholmDeterminant

noncomputable section
universe u w
namespace ExpandedFA.FredholmDeterminant.RealTraceFredholmDeterminant
open RealExteriorDefinitions
open TraceIdeals.RealComplexification
open TraceIdeals.TraceClassDefinitions.Spec

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

theorem exterior_series_formula : Spec.ExteriorSeriesFormula.{u} := by
  intro H _ _ _ T hT z
  have hs := (complex_series_summable T hT z).of_norm.hasSum
  refine ⟨hs, ?_⟩
  exact hs.congr_fun (fun n => congrArg (fun a : ℝ => z ^ n * (a : ℂ))
    (exterior_construction T hT n).2.2.2.1)

theorem real_exterior_series_formula : Spec.RealExteriorSeriesFormula.{u} := by
  intro H _ _ _ T hT r
  have hs := (real_series_summable T hT r).of_norm.hasSum
  exact hs.congr_fun (fun n => congrArg (fun a : ℝ => r ^ n * a)
    (exterior_construction T hT n).2.2.2.1)

theorem product_formula : Spec.ProductFormula.{u} := by
  intro H _ _ _ T hT z
  change HasProd _ (complexParameterDeterminant T z)
  rw [determinant_complexification T hT z]
  exact TraceFredholmDeterminant.product_formula (Space H) (operator T)
    ((traceClass_operator_iff T).mpr hT) z

theorem product_identity : Spec.ProductIdentity.{u} := by
  intro H _ _ _ T hT z
  exact (product_formula T hT z).tprod_eq.symm

theorem uniform_eigenvalue_product : Spec.UniformEigenvalueProduct.{u} := by
  intro H _ _ _ T hT R hR
  have hTc := (traceClass_operator_iff T).mpr hT
  have hu := TraceFredholmDeterminant.uniform_eigenvalue_product (Space H)
    (operator T) hTc R hR
  have heq : TraceFredholmDeterminant.Spec.EigenvalueProductValue (operator T) =
      complexParameterDeterminant T := by
    funext z
    exact (product_identity T hT z).symm
  rw [heq] at hu
  exact hu

theorem complex_nonvanishing_iff_invertible : Spec.ComplexNonvanishingIffInvertible.{u} := by
  intro H _ _ _ T hT z
  change complexParameterDeterminant T z ≠ 0 ↔ _
  rw [determinant_complexification T hT z]
  exact TraceFredholmDeterminant.nonvanishing_iff_invertible (Space H) (operator T)
    ((traceClass_operator_iff T).mpr hT) z

/-- The existing explicit transport of two-sided bounded inverses is exactly
the unit criterion in the two endomorphism algebras. -/
lemma isUnit_complexification_iff (A : H →L[ℝ] H) :
    IsUnit (operator A) ↔ IsUnit A := by
  simpa only [isUnit_iff_exists, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    using (TraceIdeals.RealComplexification.invertibility H A).1.symm

theorem real_nonvanishing_iff_invertible : Spec.RealNonvanishingIffInvertible.{u} := by
  intro H _ _ _ T hT r
  have h := complex_nonvanishing_iff_invertible T hT (r : ℂ)
  change complexParameterDeterminant T (r : ℂ) ≠ 0 ↔
    IsUnit (ContinuousLinearMap.id ℂ (Space H) + (r : ℂ) • operator T) at h
  rw [determinant_real_parameter T r, ← operator_real_smul, ← operator_id,
    ← operator_add, isUnit_complexification_iff] at h
  simpa only [ne_eq, Complex.ofReal_eq_zero] using h

theorem zeros_exactly : Spec.ZerosExactly.{u} := by
  intro H _ _ _ T hT z
  change complexParameterDeterminant T z = 0 ↔ _
  rw [determinant_complexification T hT z]
  exact TraceFredholmDeterminant.zeros_exactly (Space H) (operator T)
    ((traceClass_operator_iff T).mpr hT) z

theorem real_fredholm_determinant : Spec.RealFredholmDeterminantTheorem.{u,w} := by
  exact ⟨exterior_construction, RealTraceDeterminantContinuity.entire_exterior_series,
    RealTraceDeterminantContinuity.uniform_exterior_series,
    RealTraceDeterminantContinuity.traceNorm_locally_uniform,
    RealTraceDeterminantContinuity.real_traceNorm_locally_uniform,
    RealTraceDeterminantContinuity.determinant_multiplicative,
    exterior_series_formula, real_exterior_series_formula, product_formula, product_identity,
    uniform_eigenvalue_product, complex_nonvanishing_iff_invertible,
    real_nonvanishing_iff_invertible, zeros_exactly⟩

theorem full_scalar_fredholm_determinant : Spec.FullScalarFredholmDeterminantTheorem.{u,w} := by
  exact ⟨TraceFredholmDeterminant.fredholm_determinant, real_fredholm_determinant⟩

end ExpandedFA.FredholmDeterminant.RealTraceFredholmDeterminant
