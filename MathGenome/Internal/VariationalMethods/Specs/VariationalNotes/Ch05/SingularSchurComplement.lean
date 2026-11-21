import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ConjugateQuadratic

/-! Independent scope for `prop:singular-schur`, paper.tex:2503–2533.
The singleton block index represents the scalar coordinate. No nonempty-index
or invertibility assumption is made. The pseudoinverse is the shared object
from the semidefinite quadratic conjugate, including its kernel convention. -/
noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.Ch05.SingularSchurComplement.Specs

/-- The real symmetric block matrix `[t wᵀ; w R]`. -/
def schurBlock {n : Type u} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℝ) (t : ℝ) (w : EuclideanSpace ℝ n) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ :=
  Matrix.fromBlocks (fun _ _ => t) (fun _ j => w j) (fun i _ => w i) R

def schurBlockType : Type (u + 1) :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n],
    Matrix n n ℝ → ℝ → EuclideanSpace ℝ n → Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ

/-- Explicitly retain the interpretation of the reused pseudoinverse. -/
def pseudoinverse_conventions : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ),
    R.IsHermitian →
    R.toEuclideanLin.range = R.toEuclideanLin.ker.orthogonal ∧
    (∀ y : EuclideanSpace ℝ n,
      (ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin y ∈
        R.toEuclideanLin.ker.orthogonal) ∧
    (∀ y ∈ R.toEuclideanLin.range,
      R.toEuclideanLin ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin y) = y) ∧
    (∀ x ∈ R.toEuclideanLin.ker.orthogonal,
      (ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin (R.toEuclideanLin x) = x) ∧
    (∀ y ∈ R.toEuclideanLin.ker,
      (ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin y = 0)

/-- Symmetry of the canonical matrix, also when the original matrix is singular. -/
def pseudoinverse_symmetric : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ),
    R.IsHermitian → (ConvexAnalysis.Specs.quadraticPseudoinverse R).IsHermitian

/-- The singular Schur criterion, for every finite dimension including zero. -/
def singular_schur : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ),
    R.PosSemidef → ∀ (t : ℝ) (w : EuclideanSpace ℝ n),
    (schurBlock R t w).PosSemidef ↔
      w ∈ R.toEuclideanLin.range ∧
      inner ℝ w ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin w) ≤ t

/-- Identify the pairing in the criterion with the manuscript's coordinates. -/
def pseudoinverse_coordinates : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℝ)
    (w : EuclideanSpace ℝ n),
    inner ℝ w ((ConvexAnalysis.Specs.quadraticPseudoinverse R).toEuclideanLin w) =
      dotProduct (⇑w) ((ConvexAnalysis.Specs.quadraticPseudoinverse R).mulVec (⇑w))

end VariationalNotes.Ch05.SingularSchurComplement.Specs
