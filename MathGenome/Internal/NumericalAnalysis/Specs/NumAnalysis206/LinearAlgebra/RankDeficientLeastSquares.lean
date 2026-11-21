import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.Specs.D05.M14.Svd

/-! W35. All residual and solution norms below are Euclidean norms. Dimensions
may be zero, and no rank or consistency hypothesis is imposed on the matrix.
The SVD formula uses the manuscript's one-based singular-value indexing. -/
noncomputable section
open scoped BigOperators

namespace Specs.NumAnalysis206.RankDeficientLeastSquares
open _root_.NumAnalysis206.MatrixDefinitions
universe u

/-- The entire affine set of least-squares solutions, in both directions. -/
def minimizers : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (b : Vec K m) (x : Vec K n),
    (∀ y : Vec K n, ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖) ↔
      ∃ k : Vec K n, k ∈ A.toEuclideanLin.ker ∧
        x = (pseudoinverse A).toEuclideanLin b + k

/-- The canonical solution attains the minimum residual. -/
def pseudoinverse_minimizes : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (b : Vec K m) (y : Vec K n),
    ‖A.toEuclideanLin ((pseudoinverse A).toEuclideanLin b) - b‖ ≤
      ‖A.toEuclideanLin y - b‖

/-- Among residual minimizers, the canonical solution has least norm and is
the only vector attaining that norm. -/
def minimum_norm_unique : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (b : Vec K m) (x : Vec K n),
    (∀ y : Vec K n, ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖) →
      ‖(pseudoinverse A).toEuclideanLin b‖ ≤ ‖x‖ ∧
      (‖x‖ = ‖(pseudoinverse A).toEuclideanLin b‖ ↔
        x = (pseudoinverse A).toEuclideanLin b)

/-- Singular bases exist for every matrix, including empty dimensions. -/
def exists_svd : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
    Nonempty (D05.SingularValueDecomposition A.toEuclideanLin)

/-- The canonical orthogonal-complement inverse equals the sum over exactly
the positive singular directions, for every full SVD of A. -/
def pseudoinverse_svd : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (d : D05.SingularValueDecomposition A.toEuclideanLin) (b : Vec K m),
    (pseudoinverse A).toEuclideanLin b =
      ∑ i : Fin (rank A),
        (((singularValue A (i.val + 1) : ℝ) : K)⁻¹ *
          inner K (d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)) b) •
          d.domainBasis (Fin.castLE A.toEuclideanLin.finrank_range_le i)

/-- At rank zero, the positive-term sum is empty and the canonical solution
is zero, for every right-hand side. -/
def pseudoinverse_rank_zero : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
    rank A = 0 → ∀ b : Vec K m, (pseudoinverse A).toEuclideanLin b = 0

end Specs.NumAnalysis206.RankDeficientLeastSquares
