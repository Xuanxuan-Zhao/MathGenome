import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.GramSupport

noncomputable section
open MeasureTheory Polynomial

namespace NumAnalysis206.Quadrature

/-- The monic degree-n polynomial orthogonal to every polynomial of smaller degree.
Using `degree` in the test condition includes the zero polynomial. -/
def IsMonicOrthogonal (μ : Measure ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧
    ∀ q : ℝ[X], q.degree < n → ∫ x : ℝ, p.eval x * q.eval x ∂μ = 0

namespace Specs

/-- The interval concentration restriction is unnecessary for this part of W58.
No boundedness of the support is required. -/
def orthogonalPolynomialExistsUnique : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∃! p : ℝ[X], IsMonicOrthogonal μ n p

end Specs
end NumAnalysis206.Quadrature
