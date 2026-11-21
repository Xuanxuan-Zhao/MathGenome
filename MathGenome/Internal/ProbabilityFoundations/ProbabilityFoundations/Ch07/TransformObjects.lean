import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects

/-!
The shared transform objects of paper.tex:2366–2382, 2391 and 2563–2567.
Definitions extend to arbitrary measures whenever the integral makes sense in
Mathlib's usual totalized sense, so they apply in particular to every Borel
probability law. No moment or density assumptions are introduced.
-/

open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate

namespace ProbabilityFoundations.Ch07

/-- The characteristic function, using the canonical Mathlib object. -/
noncomputable def characteristicFunction {d : ℕ} (μ : Measure (Euclidean d))
    (t : Euclidean d) : ℂ := charFun μ t

/-- The Fourier frequency ξ=-t/(2π), with division expressed as scalar multiplication. -/
noncomputable def fourierFrequency {d : ℕ} (t : Euclidean d) : Euclidean d :=
  (-(2 * Real.pi)⁻¹ : ℝ) • t

/-- The finite complex quadratic form from the definition of positive definiteness. -/
noncomputable def characteristicQuadraticForm {d : ℕ} (φ : Euclidean d → ℂ)
    {n : ℕ} (t : Fin n → Euclidean d) (c : Fin n → ℂ) : ℂ :=
  ∑ j, ∑ k, c j * conj (c k) * φ (t j - t k)

/-- Positive definiteness: every finite complex quadratic form is real and nonnegative. -/
def IsPositiveDefinite {d : ℕ} (φ : Euclidean d → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → Euclidean d) (c : Fin n → ℂ),
    (characteristicQuadraticForm φ t c).im = 0 ∧
    0 ≤ (characteristicQuadraticForm φ t c).re

/-- Convolution is the image of the product law by addition; reuse Mathlib's definition. -/
noncomputable def convolution {d : ℕ} (μ ν : Measure (Euclidean d)) :
    Measure (Euclidean d) := μ.conv ν

/-- The real Laplace transform of a law on the closed positive orthant. -/
noncomputable def laplaceTransform {d : ℕ} (μ : Measure (PositiveOrthant d))
    (t : PositiveOrthant d) : ℝ :=
  ∫ x, Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)) ∂μ

/-- Mathlib's real-inner-product convention agrees with the manuscript. -/
theorem characteristicFunction_eq_integral {d : ℕ} (μ : Measure (Euclidean d))
    (t : Euclidean d) :
    characteristicFunction μ t =
      ∫ x, Complex.exp (Complex.I * (inner ℝ t x : ℂ)) ∂μ := by
  simp only [characteristicFunction, charFun, real_inner_comm t, mul_comm Complex.I]

/-- Identification with the negative-sign, 2π Fourier convention. -/
theorem characteristicFunction_eq_fourierIntegral {d : ℕ} (μ : Measure (Euclidean d))
    (t : Euclidean d) :
    characteristicFunction μ t =
      VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ (Euclidean d))
        (1 : Euclidean d → ℂ) (fourierFrequency t) := by
  exact charFun_eq_fourierIntegral' t

/-- At ξ=-t/(2π), exp(-2πi⟨ξ,x⟩) is exactly exp(i⟨t,x⟩). -/
theorem fourierFrequency_kernel {d : ℕ} (t x : Euclidean d) :
    Complex.exp (((-(2 * Real.pi) * inner ℝ (fourierFrequency t) x : ℝ) : ℂ)
      * Complex.I) = Complex.exp (Complex.I * (inner ℝ t x : ℂ)) := by
  have h : -(2 * Real.pi) * inner ℝ (fourierFrequency t) x = inner ℝ t x := by
    rw [fourierFrequency, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    rw [← mul_assoc, neg_mul_neg, mul_inv_cancel₀ (by positivity), one_mul]
  rw [h, mul_comm]

/-- Closedness also applies in dimension zero, when the intersection is empty. -/
theorem isClosed_positiveOrthantSet (d : ℕ) : IsClosed (positiveOrthantSet d) := by
  simp only [positiveOrthantSet, Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)

end ProbabilityFoundations.Ch07
