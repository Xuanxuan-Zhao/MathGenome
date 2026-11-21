import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocusDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! SM-07, paper.tex:1106–1115 and 1161–1177. The local conormal arrow
is scalar extension of the arrow for the original presentation, not a newly
chosen presentation. The comparison below identifies it with the presentation
localized at the inverse image prime. -/
namespace Specs.AdvCommAlg.Smooth.PointwiseCriterion

universe u v w z
noncomputable section
open TensorProduct
open Algebra.Extension
open Specs.AdvCommAlg.Differentials

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- For E = (P → B), this is precisely P_Q → B_q, where Q is the
inverse image of q. The localization monoid is the inverse image of B ∖ q. -/
abbrev localPresentation (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :
    Algebra.Extension A (Localization.AtPrime q.asIdeal) :=
  E.localization (S' := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl

instance localPresentationAlgebra (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :
    Algebra E.Ring (localPresentation E q).Ring :=
  inferInstanceAs (Algebra E.Ring
    (Localization (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))))

instance localPresentationLocalization (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :
    IsLocalization (q.asIdeal.primeCompl.comap (algebraMap E.Ring B)) (localPresentation E q).Ring :=
  inferInstanceAs (IsLocalization (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))
    (Localization (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))))

instance localPresentationTower (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :
    IsScalarTower A E.Ring (localPresentation E q).Ring :=
  inferInstanceAs (IsScalarTower A E.Ring
    (Localization (q.asIdeal.primeCompl.comap (algebraMap E.Ring B))))

/-- The canonical map of the original presentation to its localization. -/
def localizationHom (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :
    E.Hom (localPresentation E q) where
  toRingHom := algebraMap E.Ring (localPresentation E q).Ring
  toRingHom_algebraMap a := (IsScalarTower.algebraMap_apply A E.Ring _ a).symm
  algebraMap_toRingHom p := by
    change IsLocalization.lift (M := q.asIdeal.primeCompl.comap (algebraMap E.Ring B)) _
      (algebraMap E.Ring (localPresentation E q).Ring p) = _
    exact IsLocalization.lift_eq _ p

/-- Localization of d_I, represented by extension of scalars to B_q. -/
def localizedConormalMap (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) :=
  E.cotangentComplex.baseChange (Localization.AtPrime q.asIdeal)

/-- A left inverse is linear over B_q, on the actual localized modules. -/
def HasLocalRetraction (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B) : Prop :=
  ∃ ρ : (Localization.AtPrime q.asIdeal ⊗[B] E.CotangentSpace) →ₗ[Localization.AtPrime q.asIdeal]
      (Localization.AtPrime q.asIdeal ⊗[B] E.Cotangent),
    ρ.comp (localizedConormalMap E q) = LinearMap.id

/-- The neighborhood and prime-local lifting conditions, with finite
presentation imposed on B over the original base A. -/
def neighborhoodIffFormal : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (q : PrimeSpectrum B),
  isSmoothAtValue A B q ↔
    FormalLifting.formallySmoothValue A (Localization.AtPrime q.asIdeal)

/-- Both vertical maps in the localized conormal diagram are canonical
isomorphisms. Their formulas identify ideal classes and differentials, and
commutativity identifies the arrows themselves. No finiteness is needed. -/
def localizationComparison : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B]
  (E : Algebra.Extension.{w} A B) (q : PrimeSpectrum B),
  (q.asIdeal.primeCompl.comap (algebraMap E.Ring B) =
    (Ideal.comap (algebraMap E.Ring B) q.asIdeal).primeCompl) ∧
  ∃ (eL : (Localization.AtPrime q.asIdeal ⊗[B] E.Cotangent) ≃ₗ[Localization.AtPrime q.asIdeal]
        (localPresentation E q).Cotangent)
    (eF : (Localization.AtPrime q.asIdeal ⊗[B] E.CotangentSpace) ≃ₗ[Localization.AtPrime q.asIdeal]
        (localPresentation E q).CotangentSpace),
    (∀ (t : Localization.AtPrime q.asIdeal) (f : E.ker),
      eL (t ⊗ₜ[B] Cotangent.mk f) = t • Cotangent.map (localizationHom E q) (Cotangent.mk f)) ∧
    (∀ (t : Localization.AtPrime q.asIdeal) (b : B) (p : E.Ring),
      eF (t ⊗ₜ[B] (b ⊗ₜ[E.Ring] KaehlerDifferential.D A E.Ring p)) =
        t • ((algebraMap B (Localization.AtPrime q.asIdeal) b) ⊗ₜ[(localPresentation E q).Ring]
          KaehlerDifferential.D A (localPresentation E q).Ring
            (algebraMap E.Ring (localPresentation E q).Ring p))) ∧
    eF.toLinearMap.comp (localizedConormalMap E q) =
      (localPresentation E q).cotangentComplex.comp eL.toLinearMap

/-- For every finite polynomial presentation, formal smoothness at q is
exactly splitting of the localization of that presentation's conormal map. -/
def formalIffRetraction : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B),
  FormalLifting.formallySmoothValue A (Localization.AtPrime q.asIdeal) ↔
    HasLocalRetraction (conormalExtension A (MvPolynomial (Fin n) A) B h) q

/-- This quantification over every finite presentation expresses presentation
independence: each splitting condition equals the same neighborhood condition. -/
def pointwiseCriterion : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
  (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
  [IsScalarTower A (MvPolynomial (Fin n) A) B]
  (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
  (q : PrimeSpectrum B),
  (isSmoothAtValue A B q ↔ FormalLifting.formallySmoothValue A (Localization.AtPrime q.asIdeal)) ∧
  (isSmoothAtValue A B q ↔ HasLocalRetraction
    (conormalExtension A (MvPolynomial (Fin n) A) B h) q)

/-- Independence of the presenting formally smooth algebra. In particular
this compares any two finite polynomial presentations of the same A-algebra. -/
def presentationIndependent : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B]
  (E : Algebra.Extension.{w} A B) (F : Algebra.Extension.{z} A B)
  [Algebra.FormallySmooth A E.Ring] [Algebra.FormallySmooth A F.Ring]
  (q : PrimeSpectrum B),
  HasLocalRetraction E q ↔ HasLocalRetraction F q

end
end Specs.AdvCommAlg.Smooth.PointwiseCriterion
