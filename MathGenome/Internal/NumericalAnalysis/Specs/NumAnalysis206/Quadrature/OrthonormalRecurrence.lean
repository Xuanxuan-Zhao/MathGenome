import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthogonalPolynomial
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open MeasureTheory Polynomial

namespace NumAnalysis206.Quadrature

/-- A finite orthonormal polynomial family, with its lower-degree test interface.
The sequence outside `0,…,n` is immaterial. -/
def IsOrthonormalPolynomialFamily (μ : Measure ℝ) (n : ℕ) (p : ℕ → ℝ[X]) : Prop :=
  (∀ k ≤ n, (p k).natDegree = k ∧ 0 < (p k).leadingCoeff ∧
    ∀ q : ℝ[X], q.degree < k → ∫ x : ℝ, (p k).eval x * q.eval x ∂μ = 0) ∧
  (∀ i ≤ n, ∀ j ≤ n,
    Integrable (fun x : ℝ => (p i).eval x * (p j).eval x) μ ∧
    (∫ x : ℝ, (p i).eval x * (p j).eval x ∂μ) = if i = j then 1 else 0)

/-- The diagonal coefficient of multiplication by the variable. -/
def recurrenceAlpha (μ : Measure ℝ) (p : ℕ → ℝ[X]) (j : ℕ) : ℝ :=
  ∫ x : ℝ, x * (p j).eval x ^ 2 ∂μ

/-- The positive adjacent coefficient; the boundary value is zero. -/
def recurrenceBeta (p : ℕ → ℝ[X]) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (p (k - 1)).leadingCoeff / (p k).leadingCoeff

namespace Specs

def orthonormalPolynomialsExist : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∃ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p ∧
      p 0 = C ((Real.sqrt (μ.real Set.univ))⁻¹) ∧
      (∀ π : ℝ[X], IsMonicOrthogonal μ n π →
        p n = (Real.sqrt (∫ x : ℝ, (π.eval x) ^ 2 ∂μ))⁻¹ • π)

def threeTermRecurrence : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
      recurrenceBeta p 0 = 0 ∧
      (∀ k, 1 ≤ k → k ≤ n → 0 < recurrenceBeta p k) ∧
      ∀ j, j < n →
        Integrable (fun x : ℝ => x * (p j).eval x ^ 2) μ ∧
        (∀ i ≤ n, Integrable (fun x : ℝ =>
          x * (p j).eval x * (p i).eval x) μ) ∧
        X * p j = recurrenceBeta p (j + 1) • p (j + 1) +
          recurrenceAlpha μ p j • p j +
          recurrenceBeta p j • (if j = 0 then 0 else p (j - 1))

end Specs
end NumAnalysis206.Quadrature
