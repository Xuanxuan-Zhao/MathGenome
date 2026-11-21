import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W43, the Hermitian dilation step. All dimensions, including zero, are allowed.
The roots of the characteristic polynomial count algebraic multiplicities. Sorting
their real parts is the increasing eigenvalue list of this Hermitian matrix. -/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HermitianDilationDefinitions
open MatrixDefinitions

/-- Negative singular values, the rectangular excess `|m - n|` of zeros, and the reversed
nonnegative singular values. The singular values in these blocks include zeros. -/
def signedSingularValues {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n) : List ℝ :=
  List.ofFn (fun i : Fin (min m n) => -singularValue A (i.val + 1)) ++
    List.replicate ((m - min m n) + (n - min m n)) 0 ++
    (List.ofFn (fun i : Fin (min m n) => singularValue A (i.val + 1))).reverse
end NumAnalysis206.HermitianDilationDefinitions

namespace Specs.NumAnalysis206.HermitianDilation
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.HermitianDilationDefinitions
universe u

def isHermitian : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
    (hermitianDilation A).IsHermitian

/-- The complete increasing eigenvalue list, with all multiplicities. -/
def eigenvalue_list : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
    ((hermitianDilation A).charpoly.roots.map RCLike.re).sort (· ≤ ·) =
      signedSingularValues A

/-- The same list for the canonical Hermitian eigenvalue enumeration, reversed
from Mathlib's decreasing order to the manuscript's increasing order. -/
def canonical_eigenvalue_list : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n)
    (hA : (hermitianDilation A).IsHermitian),
    List.ofFn (fun i : Fin (m + n) =>
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
        (by simp) i.rev) = signedSingularValues A

/-- The Frobenius norm on the sum-indexed space is the actual Euclidean map
Frobenius norm. The upstream matrix norm on the right has its entrywise definition. -/
def frobenius_difference_sq : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A B : Mat K m n),
    D05.frobeniusNorm ((hermitianDilation A - hermitianDilation B).toEuclideanLin) ^ 2 =
      2 * frobeniusNorm (A - B) ^ 2
end Specs.NumAnalysis206.HermitianDilation
