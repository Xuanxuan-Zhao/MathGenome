import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-!
Independent statements for the principal-minor proof stage of
K05.15.charcoefficients, paper.tex:3183–3185.
The indeterminate is a formal polynomial. `Finset (Fin n)` enumerates every
subset once, including the empty subset. The same subtype inclusion is used
for rows and columns of each principal minor; its determinant is independent
of simultaneously reordering those indices. The scalar ring may be any
commutative ring, so every field and every characteristic are included.
-/

namespace D05.Specs.Charcoefficients.PrincipalExpansion

open scoped BigOperators

/-- The formal polynomial identity, using the shared paper determinant on
the left and the standard determinant on the principal submatrices. -/
def polynomial_expansion : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    D05.M05.determinant
        ((Polynomial.X : Polynomial R) • (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
          A.map Polynomial.C) =
      ∑ I : Finset (Fin n),
        (-1 : Polynomial R) ^ I.card * Polynomial.X ^ (n - I.card) *
          Polynomial.C (Matrix.det (A.submatrix
            (Subtype.val : I → Fin n) (Subtype.val : I → Fin n)))

/-- Evaluation at any scalar, without an infinite-field or splitting assumption. -/
def scalar_expansion : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (t : R),
    D05.M05.determinant (t • (1 : Matrix (Fin n) (Fin n) R) - A) =
      ∑ I : Finset (Fin n), (-1 : R) ^ I.card * t ^ (n - I.card) *
        Matrix.det (A.submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n))

/-- The empty principal minor is one, including when the full size is zero. -/
def empty_minor : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    Matrix.det (A.submatrix
      (Subtype.val : (∅ : Finset (Fin n)) → Fin n)
      (Subtype.val : (∅ : Finset (Fin n)) → Fin n)) = 1

end D05.Specs.Charcoefficients.PrincipalExpansion
