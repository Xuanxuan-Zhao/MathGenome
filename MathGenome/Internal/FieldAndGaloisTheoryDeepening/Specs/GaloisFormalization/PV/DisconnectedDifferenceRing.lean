import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.PicardVessiotRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RationalDilationConstants
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.AdjoinRoot

/-! Independent specifications for the disconnected difference example in Example 1.10. -/

namespace GaloisFormalization.PV.Specs.DisconnectedDifference

universe u v

open Polynomial

def quotientRingType := (C : Type u) → [Field C] → Type u

/-- The quotient of the polynomial ring over the base field by `X² - 1`. -/
abbrev quotientRing : quotientRingType.{u} := fun C _ =>
  AdjoinRoot (X ^ 2 - 1 : Polynomial (RatFunc C))

def quotientRootType := (C : Type u) → [Field C] → quotientRing C

/-- The class of the indeterminate in the polynomial quotient. -/
noncomputable def quotientRoot : quotientRootType.{u} := fun C _ =>
  AdjoinRoot.root (X ^ 2 - 1 : Polynomial (RatFunc C))

def solutionUnitType := (C : Type u) → [Field C] → (RatFunc C × RatFunc C)ˣ

/-- The scalar solution in the product model, with its inverse. -/
noncomputable def solutionUnit : solutionUnitType.{u} := fun _ _ => Units.mkOfMulEqOne (1, -1) (1, -1) (by
  ext <;> simp)

def productOperatorType :=
  {C : Type u} → [Field C] → Cˣ → operator .difference (RatFunc C × RatFunc C)

/-- Apply the dilation to both coordinates and exchange the two factors. -/
noncomputable def productOperator : productOperatorType.{u} := fun q =>
  let σ := (rationalDilation q).toRingEquiv
  difference ((RingEquiv.prodCongr σ σ).trans RingEquiv.prodComm)

def negativeSystemType := (C : Type u) → [Field C] → linearSystem .difference (RatFunc C) 1

/-- The rank-one difference system with coefficient `-1`. -/
noncomputable def negativeSystem : negativeSystemType.{u} := fun C _ =>
  differenceSystem
    (Units.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := RatFunc C)).symm.toMonoidHom
      (-1 : (RatFunc C)ˣ))

def fundamentalMatrixType :=
  (C : Type u) → [Field C] → Matrix.GeneralLinearGroup (Fin 1) (RatFunc C × RatFunc C)

/-- The rank-one matrix whose entry is the scalar solution. -/
noncomputable def fundamentalMatrix : fundamentalMatrixType.{u} := fun C _ =>
  Units.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := RatFunc C × RatFunc C)).symm.toMonoidHom
    (solutionUnit C)

/-- The product model with its specified fundamental matrix, over the base with constants `C`. -/
def productPicardVessiot : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C] [IsAlgClosed C] (q : Cˣ), orderOf q = 0 →
    isBaseField (rationalDilationOperator q) ∧
    constantSubfield (rationalDilationOperator q) = (algebraMap C (RatFunc C)).fieldRange ∧
    (∀ x : RatFunc C, algebraMap (RatFunc C) (RatFunc C × RatFunc C) x = (x, x)) ∧
    (∀ x : RatFunc C × RatFunc C,
      apply (productOperator q) x = (rationalDilation q x.2, rationalDilation q x.1)) ∧
    apply (productOperator q) (solutionUnit C : RatFunc C × RatFunc C) =
      -(solutionUnit C : RatFunc C × RatFunc C) ∧
    isPicardVessiotRing (rationalDilationOperator q) (negativeSystem C) (productOperator q) ∧
    (fundamentalMatrix C).val 0 0 = (solutionUnit C : RatFunc C × RatFunc C) ∧
    isFundamental (negativeSystem C) (productOperator q) (fundamentalMatrix C) ∧
    matrixGeneratedSubalgebra (RatFunc C) (fundamentalMatrix C) = ⊤

/-- The coordinate idempotents are orthogonal, nonzero, and interchanged by the operator. -/
def productIdempotents : Prop :=
  ∀ {C : Type u} [Field C] (q : Cˣ),
    let ePlus : RatFunc C × RatFunc C := (1, 0)
    let eMinus : RatFunc C × RatFunc C := (0, 1)
    ePlus ≠ 0 ∧ eMinus ≠ 0 ∧ ePlus * ePlus = ePlus ∧ eMinus * eMinus = eMinus ∧ ePlus * eMinus = 0 ∧
    ePlus + eMinus = 1 ∧ apply (productOperator q) ePlus = eMinus ∧ apply (productOperator q) eMinus = ePlus

/-- Evaluation at `1` and `-1` identifies the quotient with the product as an operator
algebra over the base. It carries the two idempotents to the coordinate idempotents. -/
def quotientPresentation : Prop :=
  ∀ {C : Type u} [Field C] [CharZero C] [IsAlgClosed C] (q : Cˣ), orderOf q = 0 →
    ∃ (E : operator .difference (quotientRing C))
      (e : quotientRing C ≃ₐ[RatFunc C] RatFunc C × RatFunc C),
      commutes E (productOperator q) e ∧
      (∀ p : Polynomial (RatFunc C),
        e (AdjoinRoot.mk (X ^ 2 - 1) p) = (p.eval 1, p.eval (-1))) ∧
      e (quotientRoot C) = (solutionUnit C : RatFunc C × RatFunc C) ∧
      e ((1 + quotientRoot C) * algebraMap (RatFunc C) (quotientRing C) (2 : RatFunc C)⁻¹) =
        (1, 0) ∧
      e ((1 - quotientRoot C) * algebraMap (RatFunc C) (quotientRing C) (2 : RatFunc C)⁻¹) =
        (0, 1) ∧
      quotientRoot C ^ 2 = 1 ∧
      apply E (quotientRoot C) = -quotientRoot C ∧
      isPicardVessiotRing (rationalDilationOperator q) (negativeSystem C) E ∧
      ∃ Y : Matrix.GeneralLinearGroup (Fin 1) (quotientRing C),
        Y.val 0 0 = quotientRoot C ∧
        isFundamental (negativeSystem C) E Y ∧ matrixGeneratedSubalgebra (RatFunc C) Y = ⊤

/-- Localization at all non-zero-divisors is an isomorphism via the canonical map. -/
def quotientTotal : Prop :=
  ∀ (C : Type u) [Field C] [CharZero C],
    Function.Bijective (algebraMap (quotientRing C) (totalQuotientRing (quotientRing C)))

/-- The original quotient does not embed as a ring in any field. -/
def quotientNoFieldEmbedding : Prop :=
  ∀ (C : Type u) [Field C] [CharZero C] (F : Type v) [Field F]
    (f : quotientRing C →+* F), ¬ Function.Injective f

end GaloisFormalization.PV.Specs.DisconnectedDifference
