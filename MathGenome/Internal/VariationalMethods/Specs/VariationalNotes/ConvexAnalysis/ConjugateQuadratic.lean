import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The semidefinite quadratic example of `prop:conjugate-basic`, paper.tex
961–1005. Coordinates use Euclidean space and its usual real dot product.
There is no invertibility or positive-dimension assumption. The pseudoinverse
is the intrinsic inverse restriction after orthogonal projection, rather than
an inverse of a possibly singular matrix. -/
noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

/-- A matrix representation of the orthogonally defined pseudoinverse. -/
def quadraticPseudoinverse {n : Type u} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.toEuclideanLin.symm (D05.pseudoinverse Q.toEuclideanLin)

def quadraticPseudoinverseType : Type (u+1) :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n], Matrix n n ℝ → Matrix n n ℝ

/-- This is xᵀQx/2, always finite, embedded in the shared extended-real domain. -/
def matrixQuadratic {n : Type u} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (x : EuclideanSpace ℝ n) : WithTop ℝ :=
  ((inner ℝ x (Q.toEuclideanLin x) / 2 : ℝ) : WithTop ℝ)

def matrixQuadraticType : Type (u+1) :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n],
    Matrix n n ℝ → EuclideanSpace ℝ n → WithTop ℝ

/-- Explicit bridge to the coordinate expression in the manuscript. -/
def matrixQuadratic_coordinates : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ)
    (x : EuclideanSpace ℝ n),
    matrixQuadratic Q x = ((dotProduct (⇑x) (Q.mulVec (⇑x)) / 2 : ℝ) : WithTop ℝ)

/-- Symmetry is enough for the range/kernel identity. -/
def quadratic_range_kernel : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ),
    Q.IsHermitian → Q.toEuclideanLin.range = Q.toEuclideanLin.ker.orthogonal

/-- Both inverse identities and the zero-on-kernel convention, for the same
matrix that occurs in the conjugate formula. -/
def quadratic_pseudoinverse_conventions : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ),
    Q.IsHermitian →
    (∀ y : EuclideanSpace ℝ n,
      (quadraticPseudoinverse Q).toEuclideanLin y ∈ Q.toEuclideanLin.ker.orthogonal) ∧
    (∀ y ∈ Q.toEuclideanLin.range,
      Q.toEuclideanLin ((quadraticPseudoinverse Q).toEuclideanLin y) = y) ∧
    (∀ x ∈ Q.toEuclideanLin.ker.orthogonal,
      (quadraticPseudoinverse Q).toEuclideanLin (Q.toEuclideanLin x) = x) ∧
    (∀ y ∈ Q.toEuclideanLin.ker,
      (quadraticPseudoinverse Q).toEuclideanLin y = 0)

def conjugate_matrixQuadratic : Prop := by
  classical
  exact
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ),
    Q.PosSemidef → ∀ y : EuclideanSpace ℝ n,
    conjugate (matrixQuadratic Q) (innerSL ℝ y) =
      if y ∈ Q.toEuclideanLin.range then
        ((inner ℝ y ((quadraticPseudoinverse Q).toEuclideanLin y) / 2 : ℝ) : EReal)
      else ⊤

end VariationalNotes.ConvexAnalysis.Specs
