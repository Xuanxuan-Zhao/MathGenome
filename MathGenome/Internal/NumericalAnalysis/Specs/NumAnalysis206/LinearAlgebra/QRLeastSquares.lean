import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! Independent statements of paper.tex W29. Matrices act on Euclidean spaces;
all natural-number dimensions, including zero, are allowed. -/
noncomputable section
namespace Specs.NumAnalysis206.QRLeastSquares
open _root_.NumAnalysis206.MatrixDefinitions

/-- The global residual minimum is attained exactly at the QR formula. -/
def minimizer_iff_qr_formula : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ}
    (A Q : Mat K m n) (R : Mat K n n),
    FullColumnRank A → ReducedQR A Q R → ∀ (b : Vec K m) (x : Vec K n),
      (∀ y : Vec K n, ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖) ↔
        x = R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b)

/-- In particular the stated formula is the unique least-squares solution. -/
def exists_unique_qr_minimizer : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ}
    (A Q : Mat K m n) (R : Mat K n n),
    FullColumnRank A → ReducedQR A Q R → ∀ b : Vec K m,
      (∀ y : Vec K n,
        ‖A.toEuclideanLin (R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b)) - b‖ ≤
          ‖A.toEuclideanLin y - b‖) ∧
      ∃! x : Vec K n, ∀ y : Vec K n,
        ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖

/-- The fitted vector equals Q Q* b and the canonical orthogonal projection
onto the actual range of A. -/
def fitted_vector_eq_projection : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ}
    (A Q : Mat K m n) (R : Mat K n n),
    FullColumnRank A → ReducedQR A Q R → ∀ b : Vec K m,
      A.toEuclideanLin (R⁻¹.toEuclideanLin ((adjoint Q).toEuclideanLin b)) =
        Q.toEuclideanLin ((adjoint Q).toEuclideanLin b) ∧
      Q.toEuclideanLin ((adjoint Q).toEuclideanLin b) =
        A.toEuclideanLin.range.starProjection b

end Specs.NumAnalysis206.QRLeastSquares
