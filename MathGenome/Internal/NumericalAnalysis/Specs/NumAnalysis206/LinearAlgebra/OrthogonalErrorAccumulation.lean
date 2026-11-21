import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
open scoped BigOperators

namespace NumAnalysis206.OrthogonalErrorDefinitions
open MatrixDefinitions

/-- Exact forward product: step zero acts first. -/
def forwardProduct {K : Type*} [RCLike K] {m : ℕ}
    (H : ℕ → Mat K m m) : ℕ → Mat K m m
  | 0 => 1
  | j + 1 => H j * forwardProduct H j

end NumAnalysis206.OrthogonalErrorDefinitions

namespace Specs.NumAnalysis206.OrthogonalErrorAccumulation
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.OrthogonalErrorDefinitions

/-- W32's accumulation argument. There are N updates, indexed 0,...,N-1;
B j is the stored matrix after j updates. Orthogonal/unitary matrices act in
the Euclidean norm, and the pullback is the inverse exact forward product.
No independence or rank assumption is imposed on A, including empty dimensions. -/
def columnwise_accumulation : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ} (N : ℕ)
    (A : Mat K m n) (H : ℕ → Mat K m m)
    (B F : ℕ → Mat K m n) (c : ℕ → ℝ),
    B 0 = A →
    (∀ j < N, (H j).conjTranspose * H j = 1) →
    (∀ j < N, 0 ≤ c j) →
    (∀ j < N, B (j + 1) = H j * B j + F j) →
    (∀ j < N, ∀ i, ‖columns (F j) i‖ ≤ c j * ‖columns (B j) i‖) →
    (∀ j ≤ N, ∀ i, ‖columns (B j) i‖ ≤
      (∏ k ∈ Finset.range j, (1 + c k)) * ‖columns A i‖) ∧
    ((forwardProduct H N).conjTranspose * forwardProduct H N = 1 ∧
      forwardProduct H N * (forwardProduct H N).conjTranspose = 1) ∧
    (∀ i, ‖columns ((forwardProduct H N).conjTranspose * B N - A) i‖ ≤
      ((∏ k ∈ Finset.range N, (1 + c k)) - 1) * ‖columns A i‖) ∧
    (N = 0 → (forwardProduct H N).conjTranspose * B N - A = 0)

end Specs.NumAnalysis206.OrthogonalErrorAccumulation
