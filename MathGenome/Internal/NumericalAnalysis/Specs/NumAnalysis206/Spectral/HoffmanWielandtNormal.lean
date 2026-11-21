import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

noncomputable section
open scoped BigOperators

namespace Specs.NumAnalysis206.HoffmanWielandtNormal

/-- Squared overlaps of complete orthonormal bases form a doubly stochastic matrix. -/
def overlap_doublyStochastic : Prop :=
  ∀ {n : ℕ} (u v : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
    (fun i j => ‖inner ℂ (u i) (v j)‖ ^ 2) ∈ doublyStochastic ℝ (Fin n)

/-- The Frobenius cost identity in two arbitrary complete spectral bases. -/
def spectral_frobenius_cost : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (u v : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (lam mu : Fin n → ℂ),
    (∀ i, A.toEuclideanLin (u i) = lam i • u i) →
    (∀ j, B.toEuclideanLin (v j) = mu j • v j) →
    NumAnalysis206.MatrixDefinitions.frobeniusNorm (A - B) ^ 2 =
      ∑ i, ∑ j, ‖lam i - mu j‖ ^ 2 * ‖inner ℂ (u i) (v j)‖ ^ 2

/-- W43, first assertion. The lists are arbitrary multiplicity-indexed lists
from complete orthonormal spectral decompositions. All dimensions, including zero,
are allowed; no ordering or simplicity of the eigenvalues is required. -/
def hoffman_wielandt_normal : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    IsStarNormal A → IsStarNormal B →
    ∀ (lam mu : Fin n → ℂ)
      (u v : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))),
      (∀ i, A.toEuclideanLin (u i) = lam i • u i) →
      (∀ j, B.toEuclideanLin (v j) = mu j • v j) →
      ∃ p : Equiv.Perm (Fin n),
        (∑ i, ‖lam i - mu (p i)‖ ^ 2) ≤
          NumAnalysis206.MatrixDefinitions.frobeniusNorm (A - B) ^ 2

end Specs.NumAnalysis206.HoffmanWielandtNormal
