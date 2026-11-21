import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Polynomial

namespace Specs.Alg01SymmetricWitt.Symmetric.MonomialBasis

open Module
open Specs.Alg01SymmetricWitt.Symmetric.Algebra (degree)

universe u v

/-- Exponent vectors in `r` variables of total degree `n`. -/
abbrev Exponent (r n : ℕ) : Type :=
  { a : Fin r →₀ ℕ // ∑ i, a i = n }

def ExponentType := ℕ → ℕ → Type

/-- The basis of the actual symmetric degree and its image under the polynomial equivalence. -/
def exists_monomialBasis : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Basis (Fin r) R M) (n : ℕ),
    ∃ c : Basis (Exponent r n) R (degree R M n), ∀ a : Exponent r n,
      (c a : SymmetricAlgebra R M) = ∏ i, SymmetricAlgebra.ι R M (b i) ^ a.val i ∧
      Polynomial.equivMvPolynomial b (c a : SymmetricAlgebra R M) =
        MvPolynomial.monomial a.val 1

/-- The count concerns exponent vectors, and has no assumption on the coefficient ring. -/
def exponentCard : Prop :=
  ∀ r n : ℕ, Finite (Exponent r n) ∧ (0 < r → Nat.card (Exponent r n) = (n + r - 1).choose n)

/-- With no generators, degree zero has a single index with basis vector `1`. -/
def rankZeroDegreeZero : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (_b : Basis (Fin 0) R M),
    Nonempty (Unique (Exponent 0 0)) ∧
      ∃ c : Basis (Exponent 0 0) R (degree R M 0),
        ∀ a : Exponent 0 0, (c a : SymmetricAlgebra R M) = 1

/-- With no generators, each positive degree has an empty index set and is the zero submodule. -/
def rankZeroPositiveDegree : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (_b : Basis (Fin 0) R M) (n : ℕ), 0 < n →
    IsEmpty (Exponent 0 n) ∧ degree R M n = ⊥

end Specs.Alg01SymmetricWitt.Symmetric.MonomialBasis
