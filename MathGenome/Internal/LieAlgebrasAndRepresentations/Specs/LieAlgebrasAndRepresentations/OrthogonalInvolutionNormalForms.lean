import Mathlib.Algebra.Lie.Classical
import Mathlib.Basic.Real.Basic

/-! Orthogonal matrix normal forms in the orthogonal row of LA-J07. -/

open Matrix LieAlgebra

namespace Specs.LieAlgebrasAndRepresentations.OrthogonalInvolutionNormalForms

/-- An orthogonal square root of the identity is orthogonally similar to
the signature matrix, with either multiplicity allowed to be zero. -/
def squareOneType : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ),
    Aᵀ * A = 1 → A * A = 1 →
    ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ ι) (Q : Matrix ι ι ℝ),
      Qᵀ * Q = 1 ∧ Qᵀ * A * Q =
        Matrix.reindex e e (Orthogonal.indefiniteDiagonal (Fin p) (Fin q) ℝ)

/-- An orthogonal square root of minus the identity has determinant one and
an orthonormal basis in which it has blocks `[0, I; -I, 0]`. -/
def squareNegOneType : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ),
    Aᵀ * A = 1 → A * A = -1 →
    A.det = 1 ∧
      ∃ (n : ℕ) (e : Fin n ⊕ Fin n ≃ ι) (Q : Matrix ι ι ℝ),
        Qᵀ * Q = 1 ∧ Qᵀ * A * Q =
          Matrix.reindex e e (-Matrix.J (Fin n) ℝ)

end Specs.LieAlgebrasAndRepresentations.OrthogonalInvolutionNormalForms
