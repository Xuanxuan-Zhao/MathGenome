import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteFreeDualityModel
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfFiniteExt

open CategoryTheory Opposite IsLocalRing
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)
open CommutativeAlgebraNotes.CompletionOfFiniteExt
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (IsPowerTorsion completionModule completionScalarTower)

namespace Specs.CommutativeAlgebraNotes.GorensteinLocalDuality

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The Matlis dual with the action of the completed ring on the target hull. -/
def completedDual (E : residueFieldEnvelopeValue R) (h : IsPowerTorsion R E.carrier) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} (completionRing R) :=
  letI := completionModule h
  letI := completionScalarTower h
  { obj X := ModuleCat.of _ (X.unop →ₗ[R] E.carrier)
    map f := ModuleCat.ofHom (LinearMap.lcomp (completionRing R) E.carrier f.unop.hom)
    map_id _ := by ext; rfl
    map_comp _ _ := by ext; rfl }

abbrev ringModule (R : Type u) [CommRing R] := ModuleCat.of R R

abbrev completedRingModule (R : Type u) [CommRing R] [IsLocalRing R] :=
  ModuleCat.of (completionRing R) (completionRing R)

abbrev localDual (E : residueFieldEnvelopeValue R) (h : IsPowerTorsion R E.carrier)
    (i : ℤ) :=
  (IdealTorsion.localCohomology.{u} (maximalIdeal R) i).op ⋙ completedDual E h

/-- Gorenstein local duality, with both natural comparisons over the completed
ring. The signed Ext interfaces have zero modules in negative degrees. -/
def LocalDuality : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (_ : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (_ : ringKrullDim R = (d : WithBot ℕ∞)) (E : residueFieldEnvelopeValue R),
    ∃ (h : IsPowerTorsion R E.carrier)
      (e₁ : ∀ (X : ModuleCat.{u} R) [Module.Finite R X] (i : ℤ),
        (localDual E h i).obj (op X) ≅
          signedRestrictedExt R X (completedRingModule R) ((d : ℤ) - i))
      (e₂ : ∀ (X : ModuleCat.{u} R) [Module.Finite R X] (i : ℤ),
        signedRestrictedExt R X (completedRingModule R) ((d : ℤ) - i) ≅
          (complete R).obj (extModule R ((d : ℤ) - i) X (ringModule R))),
      ∀ (X X' : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R X']
        (f : X' ⟶ X) (i : ℤ),
        let j := (d : ℤ) - i
        (localDual E h i).map f.op ≫ (e₁ X' i).hom =
          (e₁ X i).hom ≫ restrictedPull R X X' f (completedRingModule R) j ∧
        restrictedPull R X X' f (completedRingModule R) j ≫ (e₂ X' i).hom =
          (e₂ X i).hom ≫ (complete R).map (extPull f (ringModule R) j)

end

end Specs.CommutativeAlgebraNotes.GorensteinLocalDuality
