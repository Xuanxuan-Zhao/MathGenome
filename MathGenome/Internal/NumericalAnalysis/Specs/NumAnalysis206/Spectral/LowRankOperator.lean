import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W41: best rank-at-most-k approximation in the Euclidean operator norm.
The quantifier over full exact SVDs is unrestricted. Dimensions and k may be
zero, and the singular-value sequence is the shared zero-padded sequence. -/

noncomputable section

namespace Specs.NumAnalysis206.LowRankOperator
open _root_.NumAnalysis206.MatrixDefinitions

universe u

/-- Every full exact SVD gives a feasible truncation with the stated error,
and that error is a lower bound for every feasible competitor. -/
def best_approximation : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (d : D05.SingularValueDecomposition A.toEuclideanLin) (k : ℕ),
    rank (svdTruncation A d k) ≤ k ∧
    operatorNorm (A - svdTruncation A d k) = singularValue A (k + 1) ∧
    ∀ B : Mat K m n, rank B ≤ k →
      singularValue A (k + 1) ≤ operatorNorm (A - B)

/-- The minimum over all same-size matrices of rank at most k is attained
and equals the padded singular value sigma_(k+1), without a supplied SVD. -/
def minimum_error : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (k : ℕ),
    IsLeast {ε : ℝ | ∃ B : Mat K m n,
      rank B ≤ k ∧ operatorNorm (A - B) = ε} (singularValue A (k + 1))

end Specs.NumAnalysis206.LowRankOperator
