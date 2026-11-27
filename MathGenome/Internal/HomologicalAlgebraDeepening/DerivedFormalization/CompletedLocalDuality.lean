import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CompletedLocalDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisHullUnderCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CompleteLocalDuality
namespace DerivedFormalization.CompletedLocalDuality

open CategoryTheory
open IsLocalRing (maximalIdeal)
open Specs.DerivedFormalization.CompletedLocalDuality (CompletedLocalDualityType)
open Specs.DerivedFormalization.CompleteLocalDuality (CompleteLocalDualityType)
open Specs.DerivedFormalization.Cochains (derivedCohomologyValue)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion)
open Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
  (adicCompletionFunctor completedAction finiteModules)
open Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion (restrictedHullDual)
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs (matlisDualValue residueFieldEnvelopeValue)

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Scalar restriction on maps out of a power-torsion module agrees with
precomposition and is linear over the completion. -/
private def completedMatlisDualIso (E : residueFieldEnvelopeValue (Completion R))
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) (h : ∀ M, IsPowerTorsion R (F.obj M)) :
    F.op ⋙ restrictedHullDual E ≅ (completedAction F h).op ⋙ matlisDualValue E :=
  NatIso.ofComponents
    (fun M => (CommutativeAlgebraNotes.MatlisHullUnderCompletion.completedMatlisDualEquiv
      E (h M.unop)).toModuleIso)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

/-- The adic completion of a finite module is finite over the completed ring. -/
private def completeFiniteModules (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    (finiteModules R).FullSubcategory ⥤ (finiteModules (Completion R)).FullSubcategory :=
  (finiteModules (Completion R)).lift ((finiteModules R).ι ⋙ adicCompletionFunctor R) fun M => by
    let : Module.Finite R M.obj := M.property
    exact Module.Finite.equiv
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) M.obj)

/-- The completion comparison follows from complete local duality via the
canonical completion of local cohomology and restriction of the residue hull. -/
theorem completedLocalDuality_conditional (completeLocalDuality : CompleteLocalDualityType.{u}) :
    CompletedLocalDualityType.{u} := by
  intro R S _ _ _ _ _ _ f _ hf d hd G H E
  refine ⟨CommutativeAlgebraNotes.MatlisHullUnderCompletion.restrictedHull_isEnvelope E, ?_⟩
  intro q
  let A := Completion R
  let : IsNoetherianRing A :=
    P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)
  obtain ⟨J, _, _⟩ :=
    CommutativeAlgebraNotes.RegularCoverDualizingModel.shiftedRingResolution_exists S d hd
  obtain ⟨_, _, _, _, _, _, _, hDual, _, _⟩ :=
    completeLocalDuality f hf d hd G (DerivedFormalization.DerivedHomModels.models.{u,u} S) H J E
  obtain ⟨duality⟩ := hDual q
  obtain ⟨h, ⟨comparison⟩⟩ := CommutativeAlgebraNotes.localCohomologyFiniteCompletion (R := R) q
  let ι := (finiteModules R).ι
  let F := localCohomology (maximalIdeal R) q
  let L := localCohomology (maximalIdeal A) q
  let K := ι ⋙ adicCompletionFunctor R
  refine ⟨?_⟩
  calc
    (ι ⋙ F).op ⋙ restrictedHullDual E ≅ (ι ⋙ completedAction F h).op ⋙ matlisDualValue E :=
      Functor.isoWhiskerRight (Functor.opComp ι F) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ι.op (completedMatlisDualIso E F h) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp ι (completedAction F h)).symm _
    _ ≅ (K ⋙ L).op ⋙ matlisDualValue E :=
      Functor.isoWhiskerRight (NatIso.op comparison.symm ≪≫
        (NatIso.op (Functor.associator ι (adicCompletionFunctor R) L)).symm) _
    _ ≅ _ :=
      Functor.isoWhiskerRight (Functor.opComp K L) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (completeFiniteModules R).op duality.symm

end

end DerivedFormalization.CompletedLocalDuality

universe v8_closure_8973d826aa23c8d5_u0
theorem _root_.«DerivedFormalization».«CompletedLocalDuality».«completedLocalDuality» : _root_.«Specs».«DerivedFormalization».«CompletedLocalDuality».«CompletedLocalDualityType».{v8_closure_8973d826aa23c8d5_u0} :=
  @_root_.«DerivedFormalization».«CompletedLocalDuality».«completedLocalDuality_conditional».{v8_closure_8973d826aa23c8d5_u0} (@_root_.«DerivedFormalization».«CompleteLocalDuality».«completeLocalDuality».{v8_closure_8973d826aa23c8d5_u0})
