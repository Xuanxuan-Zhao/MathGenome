import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.Gaussian
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthonormalRecurrence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open MeasureTheory Polynomial Matrix
open scoped BigOperators

namespace NumAnalysis206.Quadrature.Specs

/-- Matrix of multiplication by the variable followed by orthogonal projection,
in the orthonormal basis of degrees zero through n-1. -/
def jacobiMatrixValue (μ : Measure ℝ) (n : ℕ) (p : ℕ → ℝ[X]) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t : ℝ, t * (p j.val).eval t * (p i.val).eval t ∂μ

def jacobiMatrixType := (μ : Measure ℝ) → (n : ℕ) → (ℕ → ℝ[X]) →
  Matrix (Fin n) (Fin n) ℝ

/-- Rows are polynomial degrees, columns are Gaussian nodes. -/
def evaluationMatrixValue {n : ℕ} (μ : Measure ℝ) (p : ℕ → ℝ[X])
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j i => Real.sqrt (gaussianWeightValue μ x i) * (p j.val).eval (x i)

def evaluationMatrixType := {n : ℕ} → Measure ℝ → (ℕ → ℝ[X]) →
  (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ

/-- Symmetry, tridiagonality, diagonal and strictly positive adjacent entries.
For n=1 there are no adjacent entries to check. -/
def jacobiStructure : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
      (jacobiMatrixValue μ n p)ᵀ = jacobiMatrixValue μ n p ∧
      (∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val →
        jacobiMatrixValue μ n p i j = 0) ∧
      (∀ i : Fin n, jacobiMatrixValue μ n p i i = recurrenceAlpha μ p i.val) ∧
      (∀ i j : Fin n, j.val + 1 = i.val →
        jacobiMatrixValue μ n p i j = recurrenceBeta p i.val ∧
        0 < jacobiMatrixValue μ n p i j)

/-- The complete evaluation-matrix bridge: both orthogonality identities and
an actual diagonalization, for any enumeration of the Gaussian roots. -/
def jacobiEvaluation : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
    ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
      let U := evaluationMatrixValue μ p x
      U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
        jacobiMatrixValue μ n p * U = U * diagonal x

/-- The real eigenvalues are exactly the n distinct Gaussian nodes. -/
def jacobiEigenvalues : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
    ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
    ∀ ξ : ℝ,
      (∃ v : Fin n → ℝ, v ≠ 0 ∧ jacobiMatrixValue μ n p *ᵥ v = ξ • v) ↔
        ∃ i : Fin n, x i = ξ

/-- Every real unit eigenvector gives the same weight by its zeroth coordinate.
The sum of squared coordinates is the squared Euclidean norm. -/
def jacobiWeights : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (hn : 1 ≤ n),
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
    ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
    ∀ (i : Fin n) (v : Fin n → ℝ),
      jacobiMatrixValue μ n p *ᵥ v = x i • v → (∑ j, v j ^ 2) = 1 →
        gaussianWeightValue μ x i = μ.real Set.univ * |v ⟨0, by omega⟩| ^ 2

/-- Coefficients of multiplication followed by orthogonal projection are Jc.
Since the p_j form an orthonormal basis, these inner products specify the projection. -/
def jacobiProjection : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ),
    FiniteMoment μ (2 * n) →
    ∀ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p →
    ∀ (c : Fin n → ℝ) (i : Fin n),
      (∫ t : ℝ, t * (∑ j : Fin n, c j • p j.val).eval t * (p i.val).eval t ∂μ) =
        (jacobiMatrixValue μ n p *ᵥ c) i

/-- Existence and computation directly under W58's hypotheses. The chosen family
has the stated constant member and its top member is the normalized monic
orthogonal polynomial; the nodes retain their strict support-hull location. -/
def jacobiComputation : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (hn : 1 ≤ n),
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∃ p : ℕ → ℝ[X], IsOrthonormalPolynomialFamily μ n p ∧
      p 0 = C ((Real.sqrt (μ.real Set.univ))⁻¹) ∧
      ∃ π : ℝ[X], IsMonicOrthogonal μ n π ∧
        p n = (Real.sqrt (∫ t : ℝ, (π.eval t)^2 ∂μ))⁻¹ • π ∧
        ∃ x : Fin n → ℝ, Function.Injective x ∧
          (∀ y : ℝ, π.IsRoot y ↔ ∃ i : Fin n, x i = y) ∧
          (∀ i : Fin n, ∃ l ∈ μ.support, ∃ r ∈ μ.support, l < x i ∧ x i < r) ∧
          (let U := evaluationMatrixValue μ p x
           U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ jacobiMatrixValue μ n p * U = U * diagonal x) ∧
          (∀ a : ℝ,
            (∃ v : Fin n → ℝ, v ≠ 0 ∧ jacobiMatrixValue μ n p *ᵥ v = a • v) ↔
              ∃ i : Fin n, x i = a) ∧
          (∀ (i : Fin n) (v : Fin n → ℝ),
            jacobiMatrixValue μ n p *ᵥ v = x i • v → (∑ j, v j ^ 2) = 1 →
              gaussianWeightValue μ x i = μ.real Set.univ * |v ⟨0, by omega⟩| ^ 2)

end NumAnalysis206.Quadrature.Specs
