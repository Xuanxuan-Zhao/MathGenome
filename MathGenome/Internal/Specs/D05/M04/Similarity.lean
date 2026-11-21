import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Independent specifications for K05.04.similarity, paper.tex:657–660.
Similarity uses one invertible change matrix, with new coordinates converted
into old coordinates. Formal polynomial evaluation is `Polynomial.aeval`.
All matrix identities hold over commutative rings, including size zero.
Minimal polynomials are asserted over fields, without a nonzero-size premise.
-/

namespace Specs.D05.M04.Similarity

open Matrix
open MatrixOfMap ChangeBasis

universe u

def similar_type : Type (u + 1) :=
  {R : Type u} → [CommRing R] → {n : ℕ} →
    Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Prop

/-- A single invertible matrix conjugates the old matrix into the new one. -/
noncomputable def similar_value : similar_type.{u} :=
  fun {R} _ {n} A B => ∃ P : Matrix (Fin n) (Fin n) R,
    IsUnit P ∧ B = P⁻¹ * A * P

def same_basis_conjugation : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V) (T : V →ₗ[R] V),
    matrixOfMap_value b' b' T =
      (changeMatrix_value b b')⁻¹ * matrixOfMap_value b b T * changeMatrix_value b b'

def same_basis_similar : Prop :=
  ∀ {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (b b' : Module.Basis (Fin n) R V) (T : V →ₗ[R] V),
    similar_value (matrixOfMap_value b b T) (matrixOfMap_value b' b' T)

def reflexive : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    similar_value A A

def symmetric : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → similar_value B A

def transitive : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B C : Matrix (Fin n) (Fin n) R),
    similar_value A B → similar_value B C → similar_value A C

def equivalence : Prop :=
  ∀ {R : Type*} [CommRing R] (n : ℕ),
    Equivalence (similar_value (R := R) (n := n))

/-- The same specified change matrix works for every power, including power zero. -/
def power_conjugation : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A P : Matrix (Fin n) (Fin n) R),
    IsUnit P → ∀ k : ℕ, (P⁻¹ * A * P) ^ k = P⁻¹ * A ^ k * P

/-- Polynomial covariance retains the very same change matrix. -/
def polynomial_conjugation : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A P : Matrix (Fin n) (Fin n) R),
    IsUnit P → ∀ p : Polynomial R,
    Polynomial.aeval (P⁻¹ * A * P) p = P⁻¹ * Polynomial.aeval A p * P

def polynomial_similar : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → ∀ p : Polynomial R,
    similar_value (Polynomial.aeval A p) (Polynomial.aeval B p)

def annihilates_iff : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → ∀ p : Polynomial R,
    Polynomial.aeval B p = 0 ↔ Polynomial.aeval A p = 0

def minpoly_invariant : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K),
    similar_value A B → minpoly K B = minpoly K A

/-- The formal polynomial matrix `tI - A` also transforms by conjugation. -/
def charmatrix_conjugation : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A P : Matrix (Fin n) (Fin n) R),
    IsUnit P →
    (P⁻¹ * A * P).charmatrix =
      P⁻¹.map Polynomial.C * A.charmatrix * P.map Polynomial.C

def charpoly_invariant : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    similar_value A B → B.charpoly = A.charpoly

end Specs.D05.M04.Similarity
