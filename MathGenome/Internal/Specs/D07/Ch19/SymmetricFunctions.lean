import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Polynomial.Basic

/-!
Independent specifications for K07.19.symmetric_functions, paper.tex:5236–5252.
Variables are indexed by `Fin n` (index i denotes the notes' X_{i+1}).
The elementary polynomials, variable automorphisms, and fixed subring use the
canonical Mathlib objects. All equations are equations of formal polynomials.
`CommRing` permits the zero ring; no assertion assumes `n > 0`.
-/

universe u
noncomputable section

namespace Specs.D07.Ch19.SymmetricFunctions

open MvPolynomial

/-- Choosing a j-element subset is the same as choosing increasing indices. -/
def ElementaryDefinition : Prop :=
  ∀ (R : Type u) [CommRing R] (n j : ℕ),
    esymm (Fin n) R j =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∏ i ∈ s, X i

def ElementaryZero : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), esymm (Fin n) R 0 = 1

/-- The variable renaming is an R-algebra automorphism, fixing coefficients. -/
def PermutationAutomorphisms : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (π : Equiv.Perm (Fin n)),
    (∀ p : MvPolynomial (Fin n) R, renameEquiv R π p = rename π p) ∧
    (∀ a : R, renameEquiv R π (C a) = C a) ∧
    (∀ i : Fin n, renameEquiv R π (X i) = X (π i)) ∧
    (∀ p : MvPolynomial (Fin n) R,
      (renameEquiv R π).symm p = rename π.symm p)

/-- The convention agrees with (π * τ)(i) = π(τ(i)). -/
def PermutationAction : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin n) R),
    renameEquiv R (1 : Equiv.Perm (Fin n)) p = p ∧
    ∀ π τ : Equiv.Perm (Fin n),
      renameEquiv R (π * τ) p = renameEquiv R π (renameEquiv R τ p)

/-- On the coefficient model, variables permute exponent vectors and preserve
addition of exponents, the operation used in convolution multiplication. -/
def ExponentPermutation : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (π : Equiv.Perm (Fin n))
    (d e : Fin n →₀ ℕ) (a : R) (p : MvPolynomial (Fin n) R),
    (d + e).mapDomain π = d.mapDomain π + e.mapDomain π ∧
    rename π (monomial d a) = monomial (d.mapDomain π) a ∧
    (rename π p).coeff (d.mapDomain π) = p.coeff d ∧
    (d.mapDomain π).mapDomain π.symm = d

def SymmetryDefinition : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin n) R),
    p.IsSymmetric ↔ ∀ π : Equiv.Perm (Fin n), renameEquiv R π p = p

/-- The underlying subring of the symmetric subalgebra is exactly the fixed set. -/
def FixedSubring : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin n) R),
    p ∈ (symmetricSubalgebra (Fin n) R).toSubring ↔
      ∀ π : Equiv.Perm (Fin n), rename π p = p

def SymmetricClosure : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    IsSymmetric (0 : MvPolynomial (Fin n) R) ∧
    IsSymmetric (1 : MvPolynomial (Fin n) R) ∧
    ∀ p q : MvPolynomial (Fin n) R, p.IsSymmetric → q.IsSymmetric →
      (p + q).IsSymmetric ∧ (p - q).IsSymmetric ∧
      (p * q).IsSymmetric ∧ (-p).IsSymmetric

def ElementarySymmetry : Prop :=
  ∀ (R : Type u) [CommRing R] (n j : ℕ), (esymm (Fin n) R j).IsSymmetric

/-- T is `Polynomial.X`, with formal multivariate polynomials as coefficients. -/
def FormalVieta : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin n) R))) =
      ∑ j ∈ Finset.range (n + 1),
        (-1) ^ j * (Polynomial.C (esymm (Fin n) R j) * Polynomial.X ^ (n - j))

/-- Both sides of Vieta are one in the empty-variable case. -/
def EmptyVieta : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∏ i : Fin 0, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin 0) R))) = 1 ∧
    (∑ j ∈ Finset.range (0 + 1),
      (-1) ^ j * (Polynomial.C (esymm (Fin 0) R j) * Polynomial.X ^ (0 - j))) = 1

end Specs.D07.Ch19.SymmetricFunctions
