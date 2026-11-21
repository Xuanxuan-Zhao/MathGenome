import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
namespace Specs.NumAnalysis206.WeylHermitian
open _root_.NumAnalysis206.MatrixDefinitions

/-- W37, with the eigenvalues in increasing order. `i : Fin n` represents
the source index `i.val + 1`, including multiplicities; for n = 0 there is
no eigenvalue index. The norm is the induced Euclidean operator norm. -/
def weyl_hermitian : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (A E : Mat K n n)
    (hA : A.IsHermitian) (hE : E.IsHermitian) (i : Fin n),
    |eigenvalue (A + E) (hA.add hE) i - eigenvalue A hA i| ≤ operatorNorm E

end Specs.NumAnalysis206.WeylHermitian
