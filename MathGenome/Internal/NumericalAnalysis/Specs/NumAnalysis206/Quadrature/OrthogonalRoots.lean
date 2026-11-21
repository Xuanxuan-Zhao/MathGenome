import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthogonalPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature.Specs

/-- The complete real root enumeration, simplicity, and strict location claim in W58.
The two support witnesses express strict interior location even for unbounded support. -/
def orthogonalRoots : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℝ[X], IsMonicOrthogonal μ n p →
      ∃ x : Fin n → ℝ, Function.Injective x ∧
        p = ∏ i : Fin n, (X - C (x i)) ∧
        (∀ y : ℝ, p.IsRoot y ↔ ∃ i : Fin n, x i = y) ∧
        (∀ i : Fin n, p.rootMultiplicity (x i) = 1) ∧
        (∀ i : Fin n, ∃ l ∈ μ.support, ∃ r ∈ μ.support, l < x i ∧ x i < r)

end NumAnalysis206.Quadrature.Specs
