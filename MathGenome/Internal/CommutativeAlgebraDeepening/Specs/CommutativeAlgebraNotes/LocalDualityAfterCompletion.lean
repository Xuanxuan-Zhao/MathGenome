import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion

/-! Local duality after maximal-ideal completion, with the original-ring Matlis dual. -/

noncomputable section

open CategoryTheory
open HomologicalComplex (homologyFunctor)
open IsLocalRing (maximalIdeal)

namespace Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion

open CompletionOfTorsionModules (Completion)
open LocalCohomologyCompletion (adicCompletionFunctor finiteModules)
open MatlisHullUnderCompletion (restrictedHullModule restrictedHullScalarTower)
open RegularCoverDualizingModel (ShiftedRingResolution dualizingComplex)
open CompleteLocalDuality (homFromModule)
open IdealTorsion (localCohomology)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

attribute [local instance] restrictedHullModule restrictedHullScalarTower

/-- The original-ring Matlis dual into the restricted completed residue hull.
Scalars from the completion act on the values of each original-linear map. -/
def restrictedHullDual (E : residueFieldEnvelopeValue (Completion R)) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} (Completion R) where
  obj X := ModuleCat.of (Completion R) (X.unop →ₗ[R] E.carrier)
  map f := ModuleCat.ofHom (LinearMap.lcomp (Completion R) E.carrier f.unop.hom)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

end

/-- Local duality in every integer degree, naturally on finite original-ring modules.
The choice of a complete regular cover of the completion and a bounded injective
resolution of its shifted ring specifies the normalized dualizing complex.
With this model, ordinary complex Hom computes derived Hom. -/
def LocalDualityAfterCompletionType : Prop :=
  ∀ {R S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (f : S →+* Completion R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (E : residueFieldEnvelopeValue (Completion R)) (i : ℤ),
      Nonempty
        (((finiteModules R).ι ⋙ localCohomology (maximalIdeal R) i).op ⋙ restrictedHullDual E ≅
          ((finiteModules R).ι ⋙ adicCompletionFunctor R).op ⋙
            (homFromModule (dualizingComplex f J.complex) ⋙
              homologyFunctor (ModuleCat.{u} (Completion R)) (.up ℤ) (-i)))

end Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion
