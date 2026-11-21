import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Theorem d12:01-02. Restricting and extending scalars identifies the pointwise
increment derivative with a real Fréchet derivative that respects multiplication
by i. Real slice differentiation identifies that condition with the two CR
equations. The standard (1, i) matrix then gives the signed real Jacobian.
-/
noncomputable section
open Complex
namespace D12Complex.RealComplexDifferential
abbrev partialX := D12Complex.partialX
abbrev partialY := D12Complex.partialY
abbrev realDifferentialMatrix := D12Complex.realDifferentialMatrix
end D12Complex.RealComplexDifferential

namespace D12Complex

theorem hasComplexDerivativeAt_iff_real (f : ℂ → ℂ) (c a : ℂ) :
    HasComplexDerivativeAt f c a ↔ HasFDerivAt f (c • (1 : ℂ →L[ℝ] ℂ)) a := by
  rw [hasComplexDerivativeAt_iff]
  constructor
  · exact fun h => h.complexToReal_fderiv
  · intro h
    rw [hasDerivAt_iff_hasFDerivAt]
    apply hasFDerivAt_of_restrictScalars ℝ h
    simp [Complex.restrictScalars_toSpanSingleton]

theorem complexDifferentiableAt_iff_real_complexLinear (f : ℂ → ℂ) (a : ℂ) :
    ComplexDifferentiableAt f a ↔ DifferentiableAt ℝ f a ∧
      ∀ (c z : ℂ), fderiv ℝ f a (c * z) = c * fderiv ℝ f a z := by
  rw [complexDifferentiableAt_iff, differentiableAt_complex_iff_differentiableAt_real]
  constructor
  · rintro ⟨hf, hI⟩
    exact ⟨hf, fun c z => real_linearMap_map_smul_complex hI c z⟩
  · rintro ⟨hf, h⟩
    exact ⟨hf, by simpa using h I 1⟩

theorem realDifferential_apply (f : ℂ → ℂ) (c a : ℂ)
    (h : HasComplexDerivativeAt f c a) (z : ℂ) : fderiv ℝ f a z = c * z := by
  rw [((hasComplexDerivativeAt_iff_real f c a).mp h).fderiv]
  simp

private theorem partialX_eq (g : ℂ → ℝ) (a : ℂ) (hg : DifferentiableAt ℝ g a) :
    partialX g a = fderiv ℝ g a 1 := by
  have hp : HasDerivAt (fun t : ℝ => a + (t : ℂ)) 1 0 := by
    simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add a
  have hg' : HasFDerivAt g (fderiv ℝ g a) (a + (0 : ℂ)) := by simpa using hg.hasFDerivAt
  simpa [partialX, Function.comp_def] using (hg'.comp_hasDerivAt 0 hp).deriv

private theorem partialY_eq (g : ℂ → ℝ) (a : ℂ) (hg : DifferentiableAt ℝ g a) :
    partialY g a = fderiv ℝ g a I := by
  have hp : HasDerivAt (fun t : ℝ => a + (t : ℂ) * I) I 0 := by
    simpa using ((ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).const_add a
  have hg' : HasFDerivAt g (fderiv ℝ g a) (a + (0 : ℂ) * I) := by simpa using hg.hasFDerivAt
  simpa [partialY, Function.comp_def] using (hg'.comp_hasDerivAt 0 hp).deriv

theorem coordinate_partials (f : ℂ → ℂ) (a : ℂ) (hf : DifferentiableAt ℝ f a) :
    partialX (fun z => (f z).re) a = (fderiv ℝ f a 1).re ∧
    partialY (fun z => (f z).re) a = (fderiv ℝ f a I).re ∧
    partialX (fun z => (f z).im) a = (fderiv ℝ f a 1).im ∧
    partialY (fun z => (f z).im) a = (fderiv ℝ f a I).im := by
  have hr := reCLM.hasFDerivAt.comp a hf.hasFDerivAt
  have hi := imCLM.hasFDerivAt.comp a hf.hasFDerivAt
  exact ⟨(partialX_eq _ a hr.differentiableAt).trans (by rw [hr.fderiv]; rfl),
    (partialY_eq _ a hr.differentiableAt).trans (by rw [hr.fderiv]; rfl),
    (partialX_eq _ a hi.differentiableAt).trans (by rw [hi.fderiv]; rfl),
    (partialY_eq _ a hi.differentiableAt).trans (by rw [hi.fderiv]; rfl)⟩

theorem complexDifferentiableAt_iff_CR (f : ℂ → ℂ) (a : ℂ)
    (hf : DifferentiableAt ℝ f a) :
    ComplexDifferentiableAt f a ↔
      partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a ∧
      partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a := by
  obtain ⟨hux, huy, hvx, hvy⟩ := coordinate_partials f a hf
  rw [hux, huy, hvx, hvy, complexDifferentiableAt_iff,
    differentiableAt_complex_iff_differentiableAt_real]
  simp only [hf, true_and, smul_eq_mul, Complex.ext_iff, mul_re, mul_im,
    I_re, I_im, zero_mul, one_mul, zero_sub, zero_add]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂.symm, h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, h₁.symm⟩

theorem complexDerivative_CR_formulas (f : ℂ → ℂ) (a : ℂ)
    (hf : DifferentiableAt ℝ f a)
    (h₁ : partialX (fun z => (f z).re) a = partialY (fun z => (f z).im) a)
    (h₂ : partialY (fun z => (f z).re) a = -partialX (fun z => (f z).im) a) :
    HasComplexDerivativeAt f
      ((partialX (fun z => (f z).re) a : ℂ) + I * partialX (fun z => (f z).im) a) a ∧
    HasComplexDerivativeAt f
      ((partialY (fun z => (f z).im) a : ℂ) - I * partialY (fun z => (f z).re) a) a ∧
    deriv f a = (partialX (fun z => (f z).re) a : ℂ) +
      I * partialX (fun z => (f z).im) a ∧
    deriv f a = (partialY (fun z => (f z).im) a : ℂ) -
      I * partialY (fun z => (f z).re) a := by
  have hc := (complexDifferentiableAt_iff_CR f a hf).mpr ⟨h₁, h₂⟩
  have hd := (complexDifferentiableAt_iff f a).mp hc
  have hI := (differentiableAt_complex_iff_differentiableAt_real.mp hd).2
  obtain ⟨hux, _, hvx, _⟩ := coordinate_partials f a hf
  have hx : deriv f a = (partialX (fun z => (f z).re) a : ℂ) +
      I * partialX (fun z => (f z).im) a := by
    rw [complexOfReal_deriv hf hI, hux, hvx]
    simpa [mul_comm] using (re_add_im (fderiv ℝ f a 1)).symm
  have hy : deriv f a = (partialY (fun z => (f z).im) a : ℂ) -
      I * partialY (fun z => (f z).re) a := by
    rw [← h₁, h₂, ofReal_neg]
    simpa using hx
  exact ⟨(hasComplexDerivativeAt_iff f _ a).mpr (hx ▸ hd.hasDerivAt),
    (hasComplexDerivativeAt_iff f _ a).mpr (hy ▸ hd.hasDerivAt), hx, hy⟩

theorem realDifferential_matrix (f : ℂ → ℂ) (c a : ℂ)
    (h : HasComplexDerivativeAt f c a) :
    realDifferentialMatrix f a = !![c.re, -c.im; c.im, c.re] := by
  ext i j
  simp only [realDifferentialMatrix, LinearMap.toMatrix_apply,
    Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
    ContinuousLinearMap.coe_coe]
  fin_cases i <;> fin_cases j <;>
    simp [realDifferential_apply f c a h, mul_re, mul_im]

theorem realDifferential_det (f : ℂ → ℂ) (c a : ℂ)
    (h : HasComplexDerivativeAt f c a) :
    LinearMap.det (fderiv ℝ f a).toLinearMap = ‖c‖ ^ 2 ∧
    (realDifferentialMatrix f a).det = ‖c‖ ^ 2 := by
  have hm : (realDifferentialMatrix f a).det = ‖c‖ ^ 2 := by
    rw [realDifferential_matrix f c a h, Matrix.det_fin_two,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
  refine ⟨?_, hm⟩
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  exact hm

end D12Complex
