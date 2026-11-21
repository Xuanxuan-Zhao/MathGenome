import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.EtaleDifferentials
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Diagonal
import Mathlib.RingTheory.TensorProduct.Quotient

/-! FL-15, paper.tex:829–856. All tensor products use the first factor for
scalar extension. The zero ring is allowed, and no flatness is assumed. -/
noncomputable section
open scoped TensorProduct

namespace Specs.AdvCommAlg.FormalLifting.DiagonalThickenings

universe u v w

abbrev Parts (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (n : ℕ) := (B ⊗[A] B) ⧸ (Differentials.diagonalIdeal A B) ^ (n + 1)

variable (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D]

/-- Apply B → D in both factors; it is linear over the first B. -/
def diagonalTensorMap : B ⊗[A] B →ₐ[B] D ⊗[A] D :=
  Algebra.TensorProduct.map (Algebra.ofId B D) (IsScalarTower.toAlgHom A B D)

lemma diagonalTensorMap_mem (x : B ⊗[A] B)
    (hx : x ∈ Differentials.diagonalIdeal A B) :
    diagonalTensorMap A B D x ∈ Differentials.diagonalIdeal A D := by
  have h : (Algebra.TensorProduct.lmul' A (S := D)).comp
      ((diagonalTensorMap A B D).restrictScalars A) =
      (IsScalarTower.toAlgHom A B D).comp (Algebra.TensorProduct.lmul' A) := by
    ext <;> simp [diagonalTensorMap]
  change Algebra.TensorProduct.lmul' A (diagonalTensorMap A B D x) = 0
  have hx' : Algebra.TensorProduct.lmul' A x = 0 := hx
  simpa [hx'] using AlgHom.congr_fun h x

/-- The canonical map on the power quotients before extending scalars. -/
def partsMap (n : ℕ) : Parts A B n →ₐ[B] Parts A D n :=
  Ideal.quotientMapₐ _ (diagonalTensorMap A B D)
    (le_trans (pow_le_pow_left' (show Differentials.diagonalIdeal A B ≤
      (Differentials.diagonalIdeal A D).comap (diagonalTensorMap A B D) from
      diagonalTensorMap_mem A B D) _)
      (Ideal.le_comap_pow _ _))

/-- The map in FL-15, defined on the original tensor product and quotient. -/
def comparison (n : ℕ) : D ⊗[B] Parts A B n →ₐ[D] Parts A D n :=
  Algebra.TensorProduct.lift (Algebra.ofId D (Parts A D n)) (partsMap A B D n)
    (fun _ _ => Commute.all _ _)

/-- Inclusion of J/J² into the first-order diagonal thickening. Under KD-03
this is the inclusion of the canonical differential module: `KaehlerDifferential A B`
is definitionally `(Differentials.diagonalIdeal A B).Cotangent`. -/
def cotangentInclusion (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    KaehlerDifferential A B →ₗ[B] Parts A B 1 :=
  (Differentials.diagonalIdeal A B).cotangentToQuotientSquare.restrictScalars B

/-- The natural inclusion after extending scalars; its injectivity will be
proved without assuming flatness. -/
def extendedCotangentInclusion :
    D ⊗[B] KaehlerDifferential A B →ₗ[D] D ⊗[B] Parts A B 1 :=
  TensorProduct.AlgebraTensorModule.lTensor D D (cotangentInclusion A B)

/-- All orders, including n = 0, with exactly formal étaleness as hypothesis. -/
def allOrders : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyEtaleValue B D → ∀ n : ℕ, Function.Bijective (comparison A B D n)

/-- The comparison of the square-zero diagonal ideals is the FL-11 map
under the KD-03 identifications. The two inclusions and their commuting
square specify the induced map, rather than merely an abstract isomorphism.
The injectivity assertion justifies scalar extension of the first ideal. -/
def firstOrder : Prop :=
  ∀ (A : Type u) (B : Type v) (D : Type w)
    [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra B D] [Algebra A D] [IsScalarTower A B D],
    formallyEtaleValue B D →
      ∃ e : (D ⊗[B] KaehlerDifferential A B) ≃ₗ[D]
          KaehlerDifferential A D,
        e.toLinearMap = Differentials.towerMapUValue A B D ∧
        Function.Injective (extendedCotangentInclusion A B D) ∧
        (comparison A B D 1).toLinearMap.comp (extendedCotangentInclusion A B D) =
          (cotangentInclusion A D).comp e.toLinearMap

end Specs.AdvCommAlg.FormalLifting.DiagonalThickenings
