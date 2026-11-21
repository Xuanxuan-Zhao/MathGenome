import MathGenome.Internal.Specs.D07.Ch08.MatrixRing
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
Independent specification for `lem:commutative-ring-adjugate`,
paper.tex:5369–5398 (chapters/M07.19.tex:137).

The matrix operations are the canonical operations of K07.08.matrix_ring.
`CommRing R` includes rings with zero divisors and the zero ring, in every
characteristic. The signed-minor formula identifies `Matrix.adjugate` with
the source's transpose of the cofactor matrix: its `(i,j)` entry deletes
row `j` and column `i`. In size one the minor has size zero, whose
determinant is one. Scalar multiplication of the identity represents
the source's `(det A) I`.
-/

universe u

namespace Specs.D07.Ch19.CommutativeRingAdjugate

/-- Identification of the canonical adjugate with the signed, transposed
cofactor formula, for every positive size. -/
def CofactorEntries : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)),
    A.adjugate i j = (-1 : R) ^ (j.val + i.val) *
      (A.submatrix j.succAbove i.succAbove).det

/-- Both adjugate identities over an arbitrary commutative unital ring;
no determinant invertibility, nontriviality, or characteristic hypothesis. -/
def AdjugateIdentities : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), 0 < n →
    ∀ A : Matrix (Fin n) (Fin n) R,
      A.adjugate * A = A.det • (1 : Matrix (Fin n) (Fin n) R) ∧
      A * A.adjugate = A.det • (1 : Matrix (Fin n) (Fin n) R)

end Specs.D07.Ch19.CommutativeRingAdjugate
