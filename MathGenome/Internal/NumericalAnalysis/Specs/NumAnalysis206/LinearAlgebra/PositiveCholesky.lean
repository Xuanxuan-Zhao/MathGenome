import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! W24 (`paper.tex`, Positive-definite Cholesky). `PosDef` includes Hermitian
symmetry and positivity on every nonzero vector. The scalar type is uniformly
real or complex, and no assumption excludes the empty matrix. -/
open scoped ComplexOrder
namespace Specs.NumAnalysis206.PositiveCholesky
open _root_.NumAnalysis206.MatrixDefinitions

/-- The upper factor is unique among all upper triangular factors with strictly
positive real diagonal. -/
def upper_unique : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n), A.PosDef →
    ∃! R : Mat K n n,
      A = adjoint R * R ∧ IsUpperTriangular R ∧ PositiveRealDiagonal R

/-- The equivalent lower factor, with the same strict diagonal convention. -/
def lower_unique : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A : Mat K n n), A.PosDef →
    ∃! L : Mat K n n,
      A = L * adjoint L ∧ IsLowerTriangular L ∧ PositiveRealDiagonal L

/-- The lower factor associated with an upper factor is exactly its adjoint. -/
def lower_of_upper : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A R : Mat K n n),
    (A = adjoint R * R ∧ IsUpperTriangular R ∧ PositiveRealDiagonal R) →
    A = adjoint R * adjoint (adjoint R) ∧
      IsLowerTriangular (adjoint R) ∧ PositiveRealDiagonal (adjoint R)

end Specs.NumAnalysis206.PositiveCholesky
