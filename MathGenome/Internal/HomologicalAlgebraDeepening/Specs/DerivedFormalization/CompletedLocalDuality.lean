import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion

/-! The completion comparison with the canonical derived coinduction object. -/

namespace Specs.DerivedFormalization.CompletedLocalDuality

open CategoryTheory
open IsLocalRing (maximalIdeal)
open Cochains (derivedCohomologyValue)
open CompleteLocalDuality (derivedHomFromModule)
open DerivedCoinduction (Coinduction)
open DerivedHomModels (Models)
open NormalizedRegularCoverDuality (normalizedObjectValue)
open _root_.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)
open _root_.Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open _root_.Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
  (adicCompletionFunctor finiteModules)
open _root_.Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion
  (restrictedHullDual)
open _root_.Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion
  (restrictedHullInclusion restrictedHullModule)
open _root_.AdvCommAlg.Gorenstein (IsInjectiveEnvelope)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

universe u

attribute [local instance] HasDerivedCategory.standard restrictedHullModule

/-- Over an arbitrary Noetherian local ring, the Matlis dual of local cohomology
is naturally the opposite-degree cohomology of derived Hom over the completion.
The codomain of each original-ring linear map is the restricted residue hull.
The completion acts on these maps by acting on their values. -/
def CompletedLocalDualityType : Prop :=
  ∀ {R S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (f : S →+* Completion R) [IsLocalHom f], Function.Surjective f →
    ∀ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) →
    ∀ (G : Coinduction.{u} f) (H : Models.{u,u} (Completion R))
      (E : residueFieldEnvelopeValue (Completion R)),
      IsInjectiveEnvelope (restrictedHullInclusion E) ∧
        ∀ q : ℤ, Nonempty
          (((finiteModules R).ι ⋙ localCohomology (maximalIdeal R) q).op ⋙ restrictedHullDual E ≅
            ((finiteModules R).ι ⋙ adicCompletionFunctor R).op ⋙
              (derivedHomFromModule H (normalizedObjectValue f G d) ⋙
                derivedCohomologyValue (Completion R) (-q)))

end Specs.DerivedFormalization.CompletedLocalDuality
