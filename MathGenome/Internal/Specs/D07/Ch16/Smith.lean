import MathGenome.Internal.Specs.D07.Ch16.SmithEuclideanSmithAlgorithm
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Independent statements for K07.16.smith (paper.tex:3142–3176,3190–3205).
Finite products below are the finite direct sums of modules. The main result
also gives the literal `DirectSum` version. Sum-indexed bases list the nonzero
block first; the rank equalities identify their sizes with the original ranks.
No Euclidean division is assumed in the PID statement. -/

universe u v w
namespace Specs.D07.Ch16.Smith
open Module
open scoped DirectSum

/-- Both bases of the original map, together with its full cokernel formula.
The remaining k source vectors map to zero and the t unused target vectors
supply the free factor. All three block sizes may be zero. -/
def SmithDecomposition : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (m n : ℕ) (A : (Fin m → R) →ₗ[R] (Fin n → R)),
    ∃ (s k t : ℕ)
      (b : Basis (Fin s ⊕ Fin k) R (Fin m → R))
      (e : Basis (Fin s ⊕ Fin t) R (Fin n → R)) (a : Fin s → R),
      s + k = m ∧ s + t = n ∧
      (∀ i, a i ≠ 0) ∧ (∀ i j, i ≤ j → a i ∣ a j) ∧
      (∀ i, A (b (Sum.inl i)) = a i • e (Sum.inl i)) ∧
      (∀ j, A (b (Sum.inr j)) = 0) ∧
      Nonempty (((Fin n → R) ⧸ LinearMap.range A) ≃ₗ[R]
        ((Fin t → R) × (∀ i : Fin s, R ⧸ Ideal.span {a i}))) ∧
      Nonempty (((Fin n → R) ⧸ LinearMap.range A) ≃ₗ[R]
        ((Fin t → R) × (⨁ i : Fin s, R ⧸ Ideal.span {a i})))

/-- Exactly the unit cyclic factors are zero. -/
def UnitQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] (a : R),
    Subsingleton (R ⧸ Ideal.span {a}) ↔ IsUnit a

/-- Deleting all unit factors is an actual linear equivalence, given by
restriction to the retained coordinates. This also applies to the empty list. -/
def UnitCancellation : Prop :=
  ∀ (R : Type u) [CommRing R] (s : ℕ) (a : Fin s → R),
    ∃ E : (∀ i : Fin s, R ⧸ Ideal.span {a i}) ≃ₗ[R]
      (∀ i : {i : Fin s // ¬ IsUnit (a i)}, R ⧸ Ideal.span {a i.val}),
      ∀ x i, E x i = x i.val

/-- A diagonal presentation with free coordinates indexed by κ and relation
coordinates indexed by ι. The zero free component is part of this actual map. -/
def diagonalPresentation {R : Type u} [CommRing R] (ι : Type v) (κ : Type w) (a : ι → R) :
    (ι → R) →ₗ[R] ((κ → R) × (ι → R)) where
  toFun x := (0, fun i => a i * x i)
  map_add' x y := by ext i <;> simp [mul_add]
  map_smul' r x := by ext i <;> simp [mul_left_comm]

/-- Delete precisely the unit generator–relation pairs from the actual
presentation. Both the relation index and the corresponding target index
shrink; the free coordinates are retained. -/
def PresentationCancellation : Prop :=
  ∀ (R : Type u) [CommRing R] (s t : ℕ) (a : Fin s → R),
    Nonempty ((((Fin t → R) × (Fin s → R)) ⧸
      LinearMap.range (diagonalPresentation (R := R) (Fin s) (Fin t) a)) ≃ₗ[R]
      (((Fin t → R) × ({i : Fin s // ¬ IsUnit (a i)} → R)) ⧸
        LinearMap.range (diagonalPresentation (R := R)
          {i : Fin s // ¬ IsUnit (a i)} (Fin t) (fun i => a i.val))))

/-- The Euclidean supplement retains a finite operation trace and invertible
factors, with the division relation fixed in its upstream specification. -/
def EuclideanConstruction : Prop :=
  SmithEuclideanSmithAlgorithm.SmithConstruction.{u}

/-- Cancelling a unit pair changes presentation ranks. The rank-one identity
has zero cokernel, as does the empty map, but their source ranks differ. -/
def IdentityCancellation : Prop :=
  Subsingleton ((Fin 1 → ℤ) ⧸ LinearMap.range (LinearMap.id :
    (Fin 1 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ))) ∧
  Subsingleton ((Fin 0 → ℤ) ⧸ LinearMap.range (0 :
    (Fin 0 → ℤ) →ₗ[ℤ] (Fin 0 → ℤ))) ∧
  ¬ Nonempty ((Fin 1 → ℤ) ≃ₗ[ℤ] (Fin 0 → ℤ))

end Specs.D07.Ch16.Smith
