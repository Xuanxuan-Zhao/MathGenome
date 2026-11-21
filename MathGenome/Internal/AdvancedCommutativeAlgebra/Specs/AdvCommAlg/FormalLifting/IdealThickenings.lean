import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.DirectSum.Module

/-! FL-14, paper.tex:806–828. Rings may be zero and are not assumed finite.
The base ideal is the kernel of A → B/J, expressed as the inverse image of J.
The maps below are induced by the specified structural homomorphism. -/
noncomputable section
open scoped DirectSum

namespace Specs.AdvCommAlg.FormalLifting.Thickenings

universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

abbrev baseIdeal (J : Ideal B) : Ideal A := J.comap (algebraMap A B)

def powerMap (J : Ideal B) (n : ℕ) :
    A ⧸ baseIdeal (A := A) J ^ n →+* B ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) (algebraMap A B) (Ideal.le_comap_pow _ n)

def quotientIsomorphisms : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    formallyEtaleValue A B → ∀ (J : Ideal B),
    Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap A B)) →
    ∀ n : ℕ, 1 ≤ n → Function.Bijective (powerMap (A := A) J n)

def transitionCompatibility : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) {m n : ℕ} (h : n ≤ m),
    (Ideal.Quotient.factorPow J h).comp (powerMap (A := A) J m) =
    (powerMap (A := A) J n).comp (Ideal.Quotient.factorPow (baseIdeal (A := A) J) h)


/-! A concrete associated graded ring model. The Rees algebra modulo the
constant ideal I has degree-n coefficients in I^n/I^(n+1). The decomposition
statement below supplies the explicit bridge to the direct sum, rather than
assuming an identification of these objects. -/

/-- The ideal of coefficients in one higher power, in the Rees algebra. -/
abbrev reesIdeal {R : Type*} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) :=
  I.map (algebraMap R (reesAlgebra I))

/-- The associated graded ring, in its Rees quotient realization. -/
abbrev AssociatedGraded {R : Type*} [CommRing R] (I : Ideal R) :=
  reesAlgebra I ⧸ reesIdeal I

/-- The usual degree n quotient I^n/I^(n+1). -/
abbrev GradedPiece {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :=
  ↥(I ^ n) ⧸ (Submodule.comap (I ^ n).subtype (I ^ (n + 1)))

/-- Homogeneous monomials in the Rees algebra. -/
def reesMonomial {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    ↥(I ^ n) →ₗ[R] reesAlgebra I where
  toFun a := ⟨Polynomial.monomial n a.1, reesAlgebra.monomial_mem.mpr a.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (by simpa using (Polynomial.smul_monomial r n a.1).symm)

/-- The class of a homogeneous monomial. -/
def homogeneousClass {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    ↥(I ^ n) →ₗ[R] AssociatedGraded I :=
  (Ideal.Quotient.mkₐ R (reesIdeal I)).toLinearMap.comp (reesMonomial I n)

/-- Inclusion of the degree n quotient in the Rees quotient model. -/
def pieceInclusion {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    GradedPiece I n →ₗ[R] AssociatedGraded I :=
  Submodule.liftQ _ (homogeneousClass I n) (by
    intro a ha
    change Ideal.Quotient.mk (reesIdeal I) (reesMonomial I n a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_map_algebraMap_reesAlgebra_iff]
    intro k
    change (Polynomial.monomial n a.1).coeff k ∈ I ^ (k + 1)
    by_cases h : n = k
    · subst k; simpa using ha
    · simp [Polynomial.coeff_monomial, h])

/-- The canonical additive map from the sum of the usual graded pieces. -/
noncomputable def gradedDecomposition {R : Type*} [CommRing R] (I : Ideal R) :
    (⨁ n : ℕ, GradedPiece I n) →+ AssociatedGraded I :=
  DirectSum.toAddMonoid fun n => (pieceInclusion I n).toAddMonoidHom

/-- The coefficientwise structural map on Rees algebras. -/
def reesMap (J : Ideal B) : reesAlgebra (baseIdeal (A := A) J) →+* reesAlgebra J :=
  (Polynomial.mapRingHom (algebraMap A B)).restrict
    (reesAlgebra (baseIdeal (A := A) J)).toSubsemiring
    (reesAlgebra J).toSubsemiring (by
      intro p hp n
      simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      exact Ideal.le_comap_pow (algebraMap A B) n (hp n))

/-- The induced canonical map of associated graded rings. -/
def associatedGradedMap (J : Ideal B) :
    AssociatedGraded (baseIdeal (A := A) J) →+* AssociatedGraded J :=
  Ideal.quotientMap (reesIdeal J) (reesMap (A := A) J) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
    have h : (reesMap (A := A) J).comp
        (algebraMap A (reesAlgebra (baseIdeal (A := A) J))) =
        (algebraMap B (reesAlgebra J)).comp (algebraMap A B) := by
      apply RingHom.ext
      intro a
      apply Subtype.ext
      change Polynomial.map (algebraMap A B) (Polynomial.C a) = Polynomial.C (algebraMap A B a)
      simp
    rw [h, ← Ideal.map_map]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr le_rfl))

def gradedDecompositionIsomorphism : Prop := ∀ (R : Type u) [CommRing R] (I : Ideal R),
  Function.Bijective (gradedDecomposition I)

/-- All degrees, including zero, and multiplication are covered by the
canonical ring map being bijective. The decomposition statement above
identifies these rings with the direct sums of the stated quotient modules. -/
def associatedGradedIsomorphism : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B],
    formallyEtaleValue A B → ∀ (J : Ideal B),
    Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap A B)) →
    Function.Bijective (associatedGradedMap (A := A) J)

/-- Explicit behavior on homogeneous representatives in every degree. -/
def associatedGradedHomogeneous : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (n : ℕ) (a : ↥(baseIdeal (A := A) J ^ n)),
    associatedGradedMap (A := A) J (homogeneousClass (baseIdeal (A := A) J) n a) =
      homogeneousClass J n ⟨algebraMap A B a.1, Ideal.le_comap_pow _ n a.2⟩

/-- The Rees quotient product agrees with the standard graded product. -/
def homogeneousMultiplication : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (n m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m)),
    homogeneousClass I n a * homogeneousClass I m b =
      homogeneousClass I (n + m) ⟨a.1 * b.1, by
        rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩

/-- The unit is the class of 1 in degree zero. -/
def homogeneousUnit : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R),
    homogeneousClass I 0 ⟨1, by simp⟩ = 1

end Specs.AdvCommAlg.FormalLifting.Thickenings
