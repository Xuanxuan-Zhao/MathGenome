import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
open scoped BigOperators
namespace Specs.NumAnalysis206.LowRankFrobenius
open _root_.NumAnalysis206.MatrixDefinitions
universe u

/-- The finite tail lists all positive singular values after the first k.
The manuscript pads the remaining singular values with zeros. -/
def residual_squared : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (d : D05.SingularValueDecomposition A.toEuclideanLin) (k : ℕ),
    frobeniusNorm (A - svdTruncation A d k) ^ 2 =
      ∑ i : Fin (rank A - k), singularValue A (k + i.val + 1) ^ 2

def competitor_lower_bound : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A B : Mat K m n)
    (k : ℕ), rank B ≤ k →
    (∑ i : Fin (rank A - k), singularValue A (k + i.val + 1) ^ 2) ≤
      frobeniusNorm (A - B) ^ 2

def best_approximation : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (d : D05.SingularValueDecomposition A.toEuclideanLin) (k : ℕ),
    rank (svdTruncation A d k) ≤ k ∧
    (frobeniusNorm (A - svdTruncation A d k) ^ 2 =
      ∑ i : Fin (rank A - k), singularValue A (k + i.val + 1) ^ 2) ∧
    ∀ B : Mat K m n, rank B ≤ k →
      frobeniusNorm (A - svdTruncation A d k) ≤ frobeniusNorm (A - B)
end Specs.NumAnalysis206.LowRankFrobenius
