import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisHullUnderCompletion
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian
import Mathlib.RingTheory.TensorProduct.Finite

/-! Local duality for a finite module over a Noetherian local ring after completion. -/

noncomputable section

open CategoryTheory
open HomologicalComplex (homologyFunctor)
open IsLocalRing (maximalIdeal)

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion)
open Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion (finiteModules)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (dualizingComplex)
open Specs.CommutativeAlgebraNotes.CompleteLocalDuality (homFromModule)
open Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open MatlisDualFunctorSpecs (matlisDualValue residueFieldEnvelopeValue)

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- For a power-torsion-valued functor, the original-ring and completed-ring
duals into the same hull agree, including their precomposition maps. -/
private def completedMatlisDualIso (E : residueFieldEnvelopeValue (Completion R))
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) (h : ∀ X, IsPowerTorsion R (F.obj X)) :
    F.op ⋙ restrictedHullDual E ≅ (completedAction F h).op ⋙ matlisDualValue E := by
  refine NatIso.ofComponents (fun X =>
    (MatlisHullUnderCompletion.completedMatlisDualEquiv E (h X.unop)).toModuleIso) ?_
  intro X Y f
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

/-- The adic completion functor restricted to finite modules on both sides. -/
private def completeFiniteModules (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    (finiteModules R).FullSubcategory ⥤ (finiteModules (Completion R)).FullSubcategory :=
  (finiteModules (Completion R)).lift ((finiteModules R).ι ⋙ adicCompletionFunctor R) fun X => by
    let : Module.Finite R X.obj := X.property
    exact Module.Finite.equiv
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) X.obj)

/-- The Matlis dual of local cohomology over the original ring is naturally
the opposite-degree cohomology of derived Hom over its completion. -/
theorem localDualityAfterCompletion : LocalDualityAfterCompletionType.{u} := by
  intro R S _ _ _ _ _ _ f _ hf n hn J E i
  let A := Completion R
  let : IsNoetherianRing A := P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let F := localCohomology (maximalIdeal R) i
  let H := localCohomology (maximalIdeal A) i
  let ι := (finiteModules R).ι
  let K := ι ⋙ adicCompletionFunctor R
  let G := completeFiniteModules R
  let D := dualizingComplex f J.complex
  let Q := homologyFunctor (ModuleCat.{u} A) (.up ℤ) (-i)
  obtain ⟨h, ⟨comparison⟩⟩ := localCohomologyFiniteCompletion (R := R) i
  obtain ⟨duality⟩ := (completeLocalDuality (R := A) f hf hn J E).2 i
  refine ⟨?_⟩
  calc
    (ι ⋙ F).op ⋙ restrictedHullDual E ≅ (ι ⋙ completedAction F h).op ⋙ matlisDualValue E :=
      Functor.isoWhiskerRight (Functor.opComp ι F) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ι.op (completedMatlisDualIso E F h) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp ι (completedAction F h)).symm _
    _ ≅ (K ⋙ H).op ⋙ matlisDualValue E :=
      Functor.isoWhiskerRight (NatIso.op comparison.symm ≪≫
        (NatIso.op (Functor.associator ι (adicCompletionFunctor R) H)).symm) _
    _ ≅ K.op ⋙ (homFromModule D ⋙ Q) :=
      Functor.isoWhiskerRight (Functor.opComp K H) _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.op duality

end CommutativeAlgebraNotes
