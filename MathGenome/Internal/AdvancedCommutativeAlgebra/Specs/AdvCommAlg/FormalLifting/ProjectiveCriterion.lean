import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplittingCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! FL-08, paper.tex:640–656. A polynomial presentation is represented by
the given compatible, surjective structural map A[ι] → B. The index type
is arbitrary, and all rings, including the zero ring, are allowed.

The last assertion is slightly stronger than the finite-presentation
specialization: a finite set of polynomial variables already makes the
middle module finite free, so no finiteness of the relations is needed.
-/
namespace Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion

universe u v w
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials

/-- The two-term criterion, with the actual conormal arrow for the presentation. -/
def polynomialCriterion : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B]
    (h : Function.Surjective (algebraMap (MvPolynomial ι A) B)),
    formallySmoothValue A B ↔
      Function.Injective (conormalMapValue A (MvPolynomial ι A) B h) ∧
        Module.Projective B (KaehlerDifferential A B)

/-- Both modules are projective direct summands of the specified free middle
module. The isomorphism identifies the conormal arrow with the first inclusion
and the differential projection with the second projection. -/
def polynomialSummands : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B]
    (h : Function.Surjective (algebraMap (MvPolynomial ι A) B)),
    formallySmoothValue A B →
      Module.Free B (B ⊗[MvPolynomial ι A] KaehlerDifferential A (MvPolynomial ι A)) ∧
      Module.Projective B (Conormal A (MvPolynomial ι A) B h) ∧
      Module.Projective B (KaehlerDifferential A B) ∧
      ∃ e : (B ⊗[MvPolynomial ι A] KaehlerDifferential A (MvPolynomial ι A)) ≃ₗ[B]
          (Conormal A (MvPolynomial ι A) B h × KaehlerDifferential A B),
        conormalMapValue A (MvPolynomial ι A) B h =
          e.symm.toLinearMap.comp (LinearMap.inl B _ _) ∧
        conormalProjectionValue A (MvPolynomial ι A) B =
          (LinearMap.snd B _ _).comp e.toLinearMap

/-- For every finite polynomial presentation, both summands are finite
projective. In particular this holds for finite presentations of finitely
presented A-algebras, as stated in the source. -/
def finiteProjective : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : Type w)
    [CommRing A] [Finite ι] [CommRing B] [Algebra A B]
    [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B]
    (h : Function.Surjective (algebraMap (MvPolynomial ι A) B)),
    formallySmoothValue A B →
      Module.Finite B (B ⊗[MvPolynomial ι A] KaehlerDifferential A (MvPolynomial ι A)) ∧
      Module.Finite B (Conormal A (MvPolynomial ι A) B h) ∧
      Module.Projective B (Conormal A (MvPolynomial ι A) B h) ∧
      Module.Finite B (KaehlerDifferential A B) ∧
      Module.Projective B (KaehlerDifferential A B)

end
end Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion
