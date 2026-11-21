import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.PointwiseCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! SM-10. Relation classes are represented in κ(q) ⊗_P I.
This is the residue fiber of the localized ideal, rather than a free module
on a potentially redundant list of global equations. -/
namespace Specs.AdvCommAlg.Smooth.LocalJacobianCriterion

universe u v
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]

/-- The displayed partial derivatives, reduced at q. Rows are variables. -/
def residueJacobian (q : PrimeSpectrum B) {c : ℕ}
    (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)) :
    Matrix (Fin n) (Fin c) q.asIdeal.ResidueField :=
  fun i j => algebraMap (MvPolynomial (Fin n) A) q.asIdeal.ResidueField
    (MvPolynomial.pderiv i (f j).val)

/-- The source's basis condition, using the tensor model for I_Q / Q I_Q. -/
def IsRelationBasis (q : PrimeSpectrum B) {c : ℕ}
    (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)) : Prop :=
  ∃ b : Module.Basis (Fin c) q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[MvPolynomial (Fin n) A]
        RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)),
    ∀ j, b j = 1 ⊗ₜ (f j)

/-- The original presentation localized at Q, the inverse image of q. -/
abbrev localizedPolynomialExtension
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) :=
  PointwiseCriterion.localPresentation (conormalExtension A (MvPolynomial (Fin n) A) B h) q

instance localizedPolynomialAlgebra
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) : Algebra (MvPolynomial (Fin n) A)
      (localizedPolynomialExtension h q).Ring :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) A)
    (Localization.AtPrime (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal)))

instance localizedPolynomialAtPrime
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) : IsLocalization.AtPrime (localizedPolynomialExtension h q).Ring
      (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal) :=
  inferInstanceAs (IsLocalization.AtPrime
    (Localization.AtPrime (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal))
    (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal))

instance localizedPolynomialLocal
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) : IsLocalRing (localizedPolynomialExtension h q).Ring :=
  inferInstanceAs (IsLocalRing
    (Localization.AtPrime (Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal)))

instance localizedPolynomialTower
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) :
    IsScalarTower (MvPolynomial (Fin n) A) (localizedPolynomialExtension h q).Ring
      (Localization.AtPrime q.asIdeal) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  exact (PointwiseCriterion.localizationHom
    (conormalExtension A (MvPolynomial (Fin n) A) B h) q).algebraMap_toRingHom p |>.symm

instance localizedPolynomialResidueTower
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) :
    IsScalarTower (MvPolynomial (Fin n) A) (localizedPolynomialExtension h q).Ring
      q.asIdeal.ResidueField :=
  IsScalarTower.to₁₂₄ _ _ (Localization.AtPrime q.asIdeal) _

/-- The actual localization of the equation f, as an element of I_Q. -/
def localizedRelation
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B)
    (f : RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)) :
    (localizedPolynomialExtension h q).ker :=
  (PointwiseCriterion.localizationHom
    (conormalExtension A (MvPolynomial (Fin n) A) B h) q).mapKer rfl f

/-- Literal local ideal modulo its maximal-ideal multiple. -/
abbrev LocalRelationQuotient
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) :=
  (localizedPolynomialExtension h q).ker ⧸
    (IsLocalRing.maximalIdeal (localizedPolynomialExtension h q).Ring •
      (⊤ : Submodule (localizedPolynomialExtension h q).Ring
        (localizedPolynomialExtension h q).ker))

/-- Both ideals in the literal local quotient are the localized original ideals. -/
def localizedIdealIdentifications : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B),
  let L := localizedPolynomialExtension h q
  let Q := Ideal.comap (algebraMap (MvPolynomial (Fin n) A) B) q.asIdeal
  L.ker = (RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)).map
      (algebraMap (MvPolynomial (Fin n) A) L.Ring) ∧
    IsLocalRing.maximalIdeal L.Ring = Q.map (algebraMap (MvPolynomial (Fin n) A) L.Ring)

/-- The tensor representation of relation classes is identified with the
literal quotient I_Q / (QP_Q)I_Q, including the class of every equation. -/
def relationQuotientComparison : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B),
  ∃ e : (q.asIdeal.ResidueField ⊗[MvPolynomial (Fin n) A]
      RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)) ≃ₗ[MvPolynomial (Fin n) A]
        LocalRelationQuotient h q,
    ∀ f, e (1 ⊗ₜ f) = Submodule.Quotient.mk (localizedRelation h q f)

/-- Every equation is needed to generate the localized ideal; this condition
is imposed at the specified prime, not on a redundant global presentation. -/
def IsMinimalLocalGeneratingFamily
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (q : PrimeSpectrum B) {c : ℕ}
    (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)) : Prop :=
  let v := fun j => localizedRelation h q (f j)
  Submodule.span (localizedPolynomialExtension h q).Ring (Set.range v) = ⊤ ∧
    ∀ j, v j ∉ Submodule.span (localizedPolynomialExtension h q).Ring
      (v '' (Set.univ \ {j}))

/-- Minimal local generators have exactly the required relation-basis property. -/
def minimalLocalRelationBasis : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B) (c : ℕ)
  (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)),
  IsMinimalLocalGeneratingFamily h q f → IsRelationBasis q f

/-- The criterion applies to any chosen local relation basis, including c = 0.
The algebra and its structural surjection are arbitrary, so this includes the
literal quotient by every finitely generated ideal. -/
def localJacobianCriterion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (_h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B) (c : ℕ)
  (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)),
  IsRelationBasis q f →
    (Specs.AdvCommAlg.Smooth.isSmoothAtValue A B q ↔ (residueJacobian q f).rank = c)

/-- The full column-rank test for any prescribed minimal list of local equations. -/
def minimalLocalJacobianCriterion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B) (c : ℕ)
  (f : Fin c → RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B)),
  IsMinimalLocalGeneratingFamily h q f →
    (Specs.AdvCommAlg.Smooth.isSmoothAtValue A B q ↔ (residueJacobian q f).rank = c)

end
end Specs.AdvCommAlg.Smooth.LocalJacobianCriterion
