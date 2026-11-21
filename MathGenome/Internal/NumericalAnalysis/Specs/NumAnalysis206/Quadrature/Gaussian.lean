import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.Lagrange
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthogonalRoots
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.AdaptiveOptimality

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature.Specs

/-- The weights are the integrals of the normalized Lagrange products at the nodes. -/
def gaussianWeightValue {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ t : ℝ, (Specs.NumAnalysis206.Approximation.cardinalValue Finset.univ x i).eval t ∂μ

def gaussianWeightType :=
  {n : ℕ} → Measure ℝ → (Fin n → ℝ) → Fin n → ℝ

/-- Polynomial division by the orthogonal polynomial upgrades interpolation exactness.
The stronger statement needs no Gram assumption once the polynomial and roots are given. -/
def gaussianExactness : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
    ∀ p : ℝ[X], p.natDegree ≤ 2 * n - 1 →
      (∫ t : ℝ, p.eval t ∂μ) = ∑ i, gaussianWeightValue μ x i * p.eval (x i)

/-- Exactness on the cardinal squares gives the square-integral formula and strict positivity. -/
def gaussianWeights : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
    ∀ i : Fin n,
      gaussianWeightValue μ x i =
        (∫ t : ℝ, ((Specs.NumAnalysis206.Approximation.cardinalValue Finset.univ x i).eval t)^2 ∂μ) ∧
      0 < gaussianWeightValue μ x i

/-- Full W58, including the nondegeneracy equivalence, unique orthogonal polynomial,
all roots with simplicity and strict support-hull location, explicitly constructed positive
weights, exactness through degree 2n-1, and arbitrary deterministic adaptive optimality.
No bounded-support hypothesis is used; every finite Borel measure on ℝ is allowed. -/
def gaussianQuadrature : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) →
    ((gramMatrix μ n).PosDef ↔ HasSupportPoints μ n) ∧
    ((gramMatrix μ n).PosDef →
      ∃ π : ℝ[X], IsMonicOrthogonal μ n π ∧
        (∀ q : ℝ[X], IsMonicOrthogonal μ n q → q = π) ∧
        ∃ x : Fin n → ℝ, Function.Injective x ∧
          π = ∏ i : Fin n, (X - C (x i)) ∧
          (∀ y : ℝ, π.IsRoot y ↔ ∃ i : Fin n, x i = y) ∧
          (∀ i : Fin n, π.rootMultiplicity (x i) = 1) ∧
          (∀ i : Fin n, ∃ l ∈ μ.support, ∃ r ∈ μ.support, l < x i ∧ x i < r) ∧
          (∀ i : Fin n, gaussianWeightValue μ x i =
            (∫ t : ℝ, ((Specs.NumAnalysis206.Approximation.cardinalValue Finset.univ x i).eval t)^2 ∂μ) ∧
            0 < gaussianWeightValue μ x i) ∧
          (∀ p : ℝ[X], p.natDegree ≤ 2 * n - 1 →
            (∫ t : ℝ, p.eval t ∂μ) = ∑ i, gaussianWeightValue μ x i * p.eval (x i)) ∧
          (∀ (q : AdaptiveQueries) (output : (Fin n → ℝ) → ℝ),
            ¬ ∀ p : ℝ[X], p.natDegree ≤ 2 * n →
              pointRule n q output (fun t => p.eval t) = ∫ t : ℝ, p.eval t ∂μ))

end NumAnalysis206.Quadrature.Specs
