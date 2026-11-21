import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
open scoped BigOperators

namespace Specs.NumAnalysis206.HoffmanWielandtSorted

/-- Increasing real lists minimize the sum of squared matching distances.
Weak monotonicity permits repeated entries, and the empty list is allowed. -/
def sorted_squared_cost_le : Prop :=
  ∀ {n : ℕ} (a b : Fin n → ℝ), Monotone a → Monotone b →
    ∀ p : Equiv.Perm (Fin n),
      (∑ i, (a i - b i) ^ 2) ≤ ∑ i, (a i - b (p i)) ^ 2

/-- W43, second assertion: the increasingly ordered eigenvalues of two
Hermitian matrices satisfy the Hoffman–Wielandt bound. The canonical lists
include multiplicities. This holds over both real and complex scalars and in
all dimensions, including zero. -/
def hoffman_wielandt_sorted : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (hA : A.IsHermitian) (hB : B.IsHermitian),
    (∑ i, (NumAnalysis206.MatrixDefinitions.eigenvalue A hA i -
      NumAnalysis206.MatrixDefinitions.eigenvalue B hB i) ^ 2) ≤
      NumAnalysis206.MatrixDefinitions.frobeniusNorm (A - B) ^ 2

end Specs.NumAnalysis206.HoffmanWielandtSorted
