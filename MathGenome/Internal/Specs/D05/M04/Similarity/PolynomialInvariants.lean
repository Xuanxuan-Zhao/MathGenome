import MathGenome.Internal.Specs.D05.M04.Similarity
import MathGenome.Internal.Specs.D05.M05.DetProduct
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M08.Minpoly

/-!
Independent statements for K05.04.similarity, paper.tex:658–660.
The single change matrix converts new column coordinates to old ones.
We reuse `similar_value`, formal polynomial evaluation, the canonical monic
minimal polynomial, and the shared column Leibniz determinant. Every natural
size is allowed, including zero. Matrix identities are stated over arbitrary
commutative rings; minimal polynomials are stated over fields.
-/

noncomputable section

namespace Specs.D05.M04.Similarity.PolynomialInvariants

/-- Similar matrices have exactly the same annihilating scalar polynomials. -/
def annihilates_iff : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → ∀ p : Polynomial R,
      Polynomial.aeval B p = 0 ↔ Polynomial.aeval A p = 0

/-- The matrix minimal polynomial is the shared monic minimal polynomial of
its linear map on coordinate columns, rather than a separate convention. -/
def minimalPolynomial_matrix_bridge : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    minpoly K A = Specs.D05.M08.Minpoly.minimalPolynomial_value
      K (Fin n → K) (Matrix.toLin' A)

def minpoly_invariant : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    similar_value A B → minpoly K B = minpoly K A

/-- Invariance stated directly with the minimal polynomial of K05.08.minpoly. -/
def minimalPolynomial_invariant : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    similar_value A B →
      Specs.D05.M08.Minpoly.minimalPolynomial_value K (Fin n → K) (Matrix.toLin' B) =
      Specs.D05.M08.Minpoly.minimalPolynomial_value K (Fin n → K) (Matrix.toLin' A)

/-- In the polynomial ring, `tI - A` transforms by the same change matrix,
whose entries are embedded as constant polynomials. -/
def charmatrix_conjugation : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A P : Matrix (Fin n) (Fin n) R),
    IsUnit P →
      Matrix.scalar (Fin n) (Polynomial.X : Polynomial R) -
          (P⁻¹ * A * P).map Polynomial.C =
        P⁻¹.map Polynomial.C *
          (Matrix.scalar (Fin n) (Polynomial.X : Polynomial R) - A.map Polynomial.C) *
          P.map Polynomial.C

/-- Similarity preserves the paper's determinant of the formal polynomial matrix. -/
def determinant_invariant : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B →
      D05.M05.determinant
          (Matrix.scalar (Fin n) (Polynomial.X : Polynomial R) - B.map Polynomial.C) =
        D05.M05.determinant
          (Matrix.scalar (Fin n) (Polynomial.X : Polynomial R) - A.map Polynomial.C)

/-- The resulting equality of characteristic polynomials, with the `tI - A`
convention used in K05.08.charpoly. -/
def charpoly_invariant : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → B.charpoly = A.charpoly

end Specs.D05.M04.Similarity.PolynomialInvariants
