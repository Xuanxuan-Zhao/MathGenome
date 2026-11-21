import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Real.Sign

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Specs.D04.C05.SmoothSquareCompletion
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The quadratic polynomial, with the parameter held fixed. -/
def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * v i * v j

/-- Coefficients below and on the diagonal are zero; thus the full sum is
exactly the sum over j > i. -/
def triangularCoordinate {n : ℕ} (b : Fin n → Fin n → E n → ℝ)
    (x : E n) (i : Fin n) : ℝ := x i + ∑ j, b i j x * x j

def normalizedCoordinates {n : ℕ} (d : Fin n → E n → ℝ)
    (b : Fin n → Fin n → E n → ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (fun i => Real.sqrt |d i x| * triangularCoordinate b x i)

/-- The complete square-completion obligation. One regularity parameter covers
all finite orders and ∞; ∞ gives a single smooth construction and neighborhood. -/
def squareCompletionType : Prop :=
  ∀ (n : ℕ) (r : ℕ∞), 1 ≤ r →
    ∀ (U : Set (E n)) (A : E n → Matrix (Fin n) (Fin n) ℝ)
      (d₀ : Fin n → ℝ), IsOpen U → (0 : E n) ∈ U →
      (∀ i j, ContDiffOn ℝ r (fun x => A x i j) U) →
      (∀ x ∈ U, ∀ i j, A x i j = A x j i) →
      A 0 = Matrix.diagonal d₀ → (∀ i, d₀ i ≠ 0) →
    ∃ (V : Set (E n)) (d : Fin n → E n → ℝ)
      (b : Fin n → Fin n → E n → ℝ),
      IsOpen V ∧ (0 : E n) ∈ V ∧ V ⊆ U ∧
      (∀ i, ContDiffOn ℝ r (d i) V) ∧
      (∀ i j, ContDiffOn ℝ r (b i j) V) ∧
      (∀ i, d i 0 = d₀ i) ∧
      (∀ i j, b i j 0 = 0) ∧
      (∀ i j, j ≤ i → ∀ x, b i j x = 0) ∧
      (∀ x ∈ V, ∀ i, d i x ≠ 0 ∧ Real.sign (d i x) = Real.sign (d₀ i)) ∧
      (∀ x ∈ V, quadratic (A x) (fun i => x i) =
        ∑ i, d i x * (triangularCoordinate b x i) ^ 2) ∧
      ContDiffOn ℝ r (normalizedCoordinates d b) V ∧
      normalizedCoordinates d b 0 = 0 ∧
      (∃ L : E n →L[ℝ] E n,
        HasFDerivAt (normalizedCoordinates d b) L 0 ∧
        ∀ v i, L v i = Real.sqrt |d₀ i| * v i) ∧
      (∀ x ∈ V, quadratic (A x) (fun i => x i) =
        ∑ i, Real.sign (d₀ i) * (normalizedCoordinates d b x i) ^ 2)

end Specs.D04.C05.SmoothSquareCompletion
