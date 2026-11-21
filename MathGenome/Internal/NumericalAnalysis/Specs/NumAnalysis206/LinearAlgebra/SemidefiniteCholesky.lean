import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Independent statements of the canonical semidefinite Cholesky theorem (W25).
`PosSemidef` includes Hermitian symmetry. No dimension or rank is required positive. -/
namespace Specs.NumAnalysis206.SemidefiniteCholesky
open scoped ComplexOrder
open NumAnalysis206.MatrixDefinitions

def exists_unique_cholesky : Prop :=
  ∀ (K : Type*) [RCLike K] (n : ℕ) (A : Mat K n n), A.PosSemidef →
    ∃! R : Mat K n n, A = adjoint R * R ∧ SemidefiniteCholeskyNormalization R

/-- The two factors exhibited in the source are distinct; the second one fails
exactly the additional zero-row requirement. The example works over both scalars. -/
def unnormalized_nonunique : Prop :=
  ∀ (K : Type*) [RCLike K],
    let A : Mat K 2 2 := !![0, 0; 0, 1]
    let S : Mat K 2 2 := !![0, 1; 0, 0]
    A.PosSemidef ∧
      A = adjoint A * A ∧ A = adjoint S * S ∧
      IsUpperTriangular A ∧ NonnegativeRealDiagonal A ∧
      IsUpperTriangular S ∧ NonnegativeRealDiagonal S ∧
      A ≠ S ∧ ¬ SemidefiniteCholeskyNormalization S

end Specs.NumAnalysis206.SemidefiniteCholesky
