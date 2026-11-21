import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.DirichletKernel

/-! Independent statements for the local estimate in K03.19.jordan,
paper.tex:4850–4869. The real part below is the real finite Dirichlet
kernel, not its singular quotient. All integrals are proper Darboux integrals.
The initial interval may be any positive length; the selected smaller interval
also lies in the half-period on which the common primitive bound holds. -/
namespace Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate
open Ch08.Integral Ch02.OneSided Ch15.Variation

/-- Subtracting the finite right limits of a Jordan decomposition produces
nonnegative nondecreasing components, including the assigned value at zero. -/
def smallJordanComponents : Prop :=
  ∀ (h : ℝ → ℝ) {δ₀ : ℝ}, 0 < δ₀ → boundedVariationValue h 0 δ₀ →
    h 0 = 0 → rightRelativeLimitValue h (Set.Icc 0 δ₀) 0 0 →
    ∃ u v : ℝ → ℝ,
      MonotoneOn u (Set.Icc 0 δ₀) ∧ MonotoneOn v (Set.Icc 0 δ₀) ∧
      u 0 = 0 ∧ v 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 δ₀, 0 ≤ u t ∧ 0 ≤ v t ∧ h t = u t - v t) ∧
      rightRelativeLimitValue u (Set.Icc 0 δ₀) 0 0 ∧
      rightRelativeLimitValue v (Set.Icc 0 δ₀) 0 0

/-- The constant is universal: it precedes the function, initial interval,
tolerance, and frequency. Integrability of every product is part of the result;
no absolute Dini hypothesis is imposed. -/
def localEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v ≤ Real.pi →
      ∃ hi : complexIntegrableValue (DirichletKernel.kernelValue N) u v,
        ‖complexIntegralValue _ hi‖ ≤ C) ∧
    ∀ (h : ℝ → ℝ) {δ₀ : ℝ}, 0 < δ₀ → boundedVariationValue h 0 δ₀ →
      h 0 = 0 → rightRelativeLimitValue h (Set.Icc 0 δ₀) 0 0 →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ,
        0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ Real.pi ∧
        ∀ N : ℕ, ∃ hi : realIntegrableValue
          (fun t => h t * (DirichletKernel.kernelValue N t).re) 0 δ,
          |realIntegralValue _ hi| ≤ 2 * C * ε


/-- The same estimate for the original complex finite sum D_N. For a real
weight the product has zero imaginary part; the norm is the real absolute value.
This also supplies its proper complex integrability rather than presuming it. -/
def complexLocalEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v ≤ Real.pi →
      ∃ hi : complexIntegrableValue (DirichletKernel.kernelValue N) u v,
        ‖complexIntegralValue _ hi‖ ≤ C) ∧
    ∀ (h : ℝ → ℝ) {δ₀ : ℝ}, 0 < δ₀ → boundedVariationValue h 0 δ₀ →
      h 0 = 0 → rightRelativeLimitValue h (Set.Icc 0 δ₀) 0 0 →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ,
        0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ Real.pi ∧
        ∀ N : ℕ, ∃ hi : complexIntegrableValue
          (fun t => (h t : ℂ) * DirichletKernel.kernelValue N t) 0 δ,
          ‖complexIntegralValue _ hi‖ ≤ 2 * C * ε

end Specs.SingleVariableAnalysis.Ch19.JordanLocalEstimate
