import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.GroupTheory.Perm.Fin

/-! Independent interface for paper.tex:354. Indices `Fin n` stand for the
ordered list of n variables. Inversions count pairs i < j with σ j < σ i.
The definitions use formal coefficient polynomials, also when n = 0. -/

noncomputable section

namespace D05.Foundations

/-- Each inverted pair is counted in the fiber of its first index. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ((Finset.Ioi i).filter (fun j => σ j < σ i)).card

/-- The paper's integer-valued sign, defined by inversion parity. -/
def permutationSign {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  (-1) ^ inversionCount σ

/-- The product ∏_{i<j} (x_j - x_i), with empty product equal to one. -/
def vandermondeProduct {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)

/-- A formal polynomial, rather than its value function. -/
def vandermondePolynomial (R : Type*) [CommRing R] (n : ℕ) : FormalPolynomial R n :=
  vandermondeProduct (fun i => MvPolynomial.X i)

end D05.Foundations

namespace D05.Specs.PermutationSign

open D05.Foundations

def signIdentification : Prop := ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
  permutationSign σ = (σ.sign : ℤ)

def signMultiplicative : Prop := ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
  permutationSign (σ * τ) = permutationSign σ * permutationSign τ

def signTransposition : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  permutationSign (Equiv.swap i j) = -1

def productPermutation : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → R),
  vandermondeProduct (fun i => x (σ i)) =
    (permutationSign σ : R) * vandermondeProduct x

def polynomialPermutation : Prop := ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
  MvPolynomial.rename σ (vandermondePolynomial ℤ n) =
    MvPolynomial.C (permutationSign σ) * vandermondePolynomial ℤ n

def scalarPolynomialMap : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ),
  MvPolynomial.map (Int.castRingHom R) (vandermondePolynomial ℤ n) =
    vandermondePolynomial R n

def scalarPolynomialPermutation : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ)
    (σ : Equiv.Perm (Fin n)),
  MvPolynomial.rename σ (vandermondePolynomial R n) =
    MvPolynomial.C (permutationSign σ : R) * vandermondePolynomial R n

def scalarSignLaws : Prop := ∀ (R : Type*) [CommRing R] (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)),
  (permutationSign (σ * τ) : R) =
    (permutationSign σ : R) * (permutationSign τ : R) ∧
  (∀ (i j : Fin n), i ≠ j → (permutationSign (Equiv.swap i j) : R) = -1)

def emptyCase : Prop :=
  (∀ σ : Equiv.Perm (Fin 0), inversionCount σ = 0 ∧ permutationSign σ = 1) ∧
  (∀ (R : Type*) [CommRing R], vandermondePolynomial R 0 = 1)

end D05.Specs.PermutationSign
