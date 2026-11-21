import MathGenome.Internal.Specs.D05.M15.Symmetric
import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import MathGenome.Internal.Specs.D05.Foundations.StarsBars
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Independent statements for paper.tex:3011–3015. The degree-p object is
exactly the upstream quotient of tensor powers by adjacent-swap differences.
Monomials are ordinary products; no factorial or characteristic restriction is
imposed. Formal polynomials retain their coefficient-array meaning. -/
noncomputable section
namespace Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.Symmetric
open D05.Foundations

universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Canonical map from the degreewise quotient into the symmetric algebra. -/
def powerInclusion (p : ℕ) : symmetricPower K V p →ₗ[K] symmetricAlgebra K V :=
  (adjacentRelations K V p).liftQ (homogeneousMap K V p) (by
    apply Submodule.span_le.mpr
    rintro t ⟨x,i,j,_,rfl⟩
    change homogeneousMap K V p (_ - _) = 0
    have h (x : Fin p → V) : homogeneousMap K V p (PiTensorProduct.tprod K x) =
        ∏ i, _root_.SymmetricAlgebra.ι K V (x i) := by
      change _root_.SymmetricAlgebra.algHom K V
        (TensorPower.toTensorAlgebra (PiTensorProduct.tprod K x)) = _
      rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply,
        map_list_prod, List.map_ofFn, Fin.prod_ofFn]
      rfl
    rw [map_sub, h, h]
    exact sub_eq_zero.mpr
      (Equiv.prod_comp (Equiv.swap i j) (fun i => _root_.SymmetricAlgebra.ι K V (x i))).symm)

/-- The basis-dependent isomorphism, including its inverse on formal variables. -/
def polynomialEquiv {n : ℕ} (b : Module.Basis (Fin n) K V) :
    symmetricAlgebra K V ≃ₐ[K] FormalPolynomial K n :=
  _root_.SymmetricAlgebra.equivMvPolynomial b

def powerInclusion_type := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
  symmetricPower K V p →ₗ[K] symmetricAlgebra K V
def powerInclusion_value : powerInclusion_type.{u,v} := @powerInclusion

def polynomialEquiv_type := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V), symmetricAlgebra K V ≃ₐ[K] FormalPolynomial K n
def polynomialEquiv_value : polynomialEquiv_type.{u,v} := @polynomialEquiv

def inclusion_elementary : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ) (x : Fin p → V),
  powerInclusion (K := K) (V := V) p (elementary K V p x) = ∏ i, _root_.SymmetricAlgebra.ι K V (x i)

def inclusion_injective : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
  Function.Injective (powerInclusion (K := K) (V := V) p)

def polynomial_generators : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (i : Fin n),
  polynomialEquiv b (_root_.SymmetricAlgebra.ι K V (b i)) = MvPolynomial.X i ∧
  (polynomialEquiv b).symm (MvPolynomial.X i) = _root_.SymmetricAlgebra.ι K V (b i)

/-- Ordinary products map to formal monomials with the same exponent tuple. -/
def polynomial_monomials : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (a : Fin n → ℕ),
  polynomialEquiv b (∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a i) =
    MvPolynomial.monomial ((exponentEquiv n).symm a) 1

/-- Gradedness is expressed as a map on every actual degree-p quotient. -/
def graded_equiv : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (p : ℕ),
  ∃ E : symmetricPower K V p ≃ₗ[K] MvPolynomial.homogeneousSubmodule (Fin n) K p,
    ∀ q, (E q : FormalPolynomial K n) = polynomialEquiv b (powerInclusion (K := K) (V := V) p q)

/-- The inclusion identifies each basis vector with the claimed ordinary
monomial in the symmetric algebra. Together with inclusion_injective, this
specifies the vectors in the quotient itself. -/
def monomial_basis : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (p : ℕ),
  ∃ B : Module.Basis (NonnegativeTuples n p) K (symmetricPower K V p),
    ∀ a, powerInclusion (K := K) (V := V) p (B a) =
      ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a.val i

/-- Counts all monomials, including tuples with zero entries. -/
def dimension : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (p : ℕ), 1 ≤ n →
  Module.finrank K (symmetricPower K V p) = (n + p - 1).choose p

/-- There is one empty-product basis vector in degree zero, even for V=0. -/
def zero_space_degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (b : Module.Basis (Fin 0) K V),
  Module.finrank K (symmetricPower K V 0) = 1 ∧
    ∃ q : symmetricPower K V 0, powerInclusion (K := K) (V := V) 0 q = 1

/-- All positive degrees of the zero space vanish. -/
def zero_space_positive : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (b : Module.Basis (Fin 0) K V)
  (p : ℕ), 0 < p → Subsingleton (symmetricPower K V p)

end Specs.D05.M15.SymmetricBasis
