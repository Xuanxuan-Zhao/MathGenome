import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent statements for `d04:04:inverse-stability`.
`E`, the matrix representation, and the supremum operator norm are the
shared objects. A linear equivalence packages precisely an invertible linear
map; no positive-dimension or extra smallness hypothesis is imposed. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C04.InverseStability
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The series is a sum in the operator norm topology. The additional partial
sum statement spells out convergence using the paper's supremum norm. -/
def inverse_stabilityType : Prop :=
  ∀ {n : ℕ} (A : E n ≃ₗ[ℝ] E n) (B : E n →ₗ[ℝ] E n),
    let q := linearOperatorNorm (A.symm.toLinearMap.comp (B - A.toLinearMap))
    let T := -(A.symm.toLinearMap.comp (B - A.toLinearMap))
    q < 1 → ∃ C : E n ≃ₗ[ℝ] E n,
      C.toLinearMap = B ∧
      HasSum (fun j : ℕ => LinearMap.toContinuousLinearMap ((T ^ j).comp A.symm.toLinearMap))
        (LinearMap.toContinuousLinearMap C.symm.toLinearMap) ∧
      Tendsto (fun k : ℕ => linearOperatorNorm
        ((∑ j ∈ Finset.range k, (T ^ j).comp A.symm.toLinearMap) - C.symm.toLinearMap))
        atTop (𝓝 0) ∧
      linearOperatorNorm C.symm.toLinearMap ≤ linearOperatorNorm A.symm.toLinearMap / (1 - q) ∧
      linearOperatorNorm (C.symm.toLinearMap - A.symm.toLinearMap) ≤
        linearOperatorNorm A.symm.toLinearMap ^ 2 * linearOperatorNorm (B - A.toLinearMap) / (1 - q)

/-- This bridge identifies the matrix group with invertible maps on the shared
Euclidean space, rather than using an unrelated meaning of `GL`. -/
def matrix_invertible_iffType : Prop :=
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ),
    IsUnit M ↔ ∃ A : E n ≃ₗ[ℝ] E n, A.toLinearMap = matrixLinearEquiv n n M

def matrix_inverse_representsType : Prop :=
  ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (A : E n ≃ₗ[ℝ] E n),
    A.toLinearMap = matrixLinearEquiv n n M →
    matrixLinearEquiv n n M⁻¹ = A.symm.toLinearMap

/-- The topology here is the ordinary finite product topology of matrix entries. -/
def general_linear_openType : Prop :=
  ∀ n : ℕ, IsOpen {M : Matrix (Fin n) (Fin n) ℝ | IsUnit M}

def matrix_inversion_continuousType : Prop :=
  ∀ n : ℕ, ContinuousOn (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) {M | IsUnit M}

def inverse_stability_dimension_zeroType : Prop :=
  ∀ M : Matrix (Fin 0) (Fin 0) ℝ,
    M = 1 ∧ IsUnit M ∧ M.det = 1 ∧ M⁻¹ = M ∧
    linearOperatorNorm (matrixLinearEquiv 0 0 M) = 0

end Specs.D04.C04.InverseStability
