import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Specs.Alg01SymmetricWitt.Symmetric.Polynomial

open Module
open Specs.Alg01SymmetricWitt.Symmetric.Algebra

universe u v

set_option linter.checkUnivs false in
/-- The type of the symmetric algebra equivalence for a specified finite basis. -/
def equivMvPolynomialType :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ},
    Basis (Fin r) R M → (SymmetricAlgebra R M ≃ₐ[R] MvPolynomial (Fin r) R)

noncomputable def equivMvPolynomial : equivMvPolynomialType :=
  fun b => SymmetricAlgebra.equivMvPolynomial b

def equivMvPolynomial_ι : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Basis (Fin r) R M) (i : Fin r),
    equivMvPolynomial b (SymmetricAlgebra.ι R M (b i)) = MvPolynomial.X i

def equivMvPolynomial_symm_X : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Basis (Fin r) R M) (i : Fin r),
    (equivMvPolynomial b).symm (MvPolynomial.X i) = SymmetricAlgebra.ι R M (b i)

/-- The canonical equivalence maps each tensor-quotient degree onto the corresponding
total-degree homogeneous submodule. -/
def map_degree : Prop :=
  ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (b : Basis (Fin r) R M) (n : ℕ),
    (degree R M n).map (equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule (Fin r) R n

end Specs.Alg01SymmetricWitt.Symmetric.Polynomial
