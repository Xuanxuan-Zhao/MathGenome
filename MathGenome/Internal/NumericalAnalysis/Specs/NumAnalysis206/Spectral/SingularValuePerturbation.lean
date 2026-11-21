import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W40: the Euclidean singular-value perturbation bound. The canonical
one-based sequence is padded by zero; its index zero repeats index one. -/
namespace Specs.NumAnalysis206.SingularValuePerturbation
open _root_.NumAnalysis206.MatrixDefinitions

/-- Every singular value changes by at most the Euclidean operator norm of
the perturbation, including padded indices and zero-dimensional matrices. -/
def perturbation : Prop :=
  ∀ {K : Type*} [RCLike K] {m n : ℕ} (A E : Mat K m n) (i : ℕ),
    |singularValue (A + E) i - singularValue A i| ≤ operatorNorm E

end Specs.NumAnalysis206.SingularValuePerturbation
