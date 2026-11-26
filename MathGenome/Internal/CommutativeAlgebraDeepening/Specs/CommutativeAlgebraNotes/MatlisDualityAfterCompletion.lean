import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteMatlisDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Matlis duality and completion for Noetherian local rings (M06). -/

noncomputable section

open CategoryTheory Opposite IsLocalRing

namespace CommutativeAlgebraNotes.MatlisDualityAfterCompletionSpecs

open MatlisDualFunctorSpecs CompleteMatlisDualitySpecs
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)
open Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion (restrictedHullModule restrictedHullScalarTower)

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R

attribute [local instance] restrictedHullModule restrictedHullScalarTower

/-- The original-ring dual with the completed action on the codomain hull. -/
def originalDual (E : residueFieldEnvelopeValue S) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} S where
  obj X := ModuleCat.of S (X.unop →ₗ[R] E.carrier)
  map f := ModuleCat.ofHom (LinearMap.lcomp S E.carrier f.unop.hom)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

/-- The completed-ring dual followed by restriction of scalars. -/
def completedDual (E : residueFieldEnvelopeValue S) :
    (ModuleCat.{u} S)ᵒᵖ ⥤ ModuleCat.{u} R :=
  matlisDualValue E ⋙ ModuleCat.restrictScalars (algebraMap R S)

/-- The two Matlis dual functors restrict to an anti-equivalence between Artinian
original-ring modules and finite completed-ring modules. -/
def matlisDualityAfterCompletion : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)),
    ∃ (hA : ∀ X : (artinianModules R).FullSubcategoryᵒᵖ,
          finiteModules (Completion R) ((originalDual E).obj (op X.unop.obj)))
      (hF : ∀ X : (finiteModules (Completion R)).FullSubcategoryᵒᵖ,
          artinianModules R ((completedDual E).obj (op X.unop.obj)))
      (e : (artinianModules R).FullSubcategoryᵒᵖ ≌ (finiteModules (Completion R)).FullSubcategory),
      e.functor = (finiteModules (Completion R)).lift
          ((artinianModules R).ι.op ⋙ originalDual E) hA ∧
      e.inverse = ((artinianModules R).lift
          ((finiteModules (Completion R)).ι.op ⋙ completedDual E) hF).rightOp

/-- For any residue-field hull, the actual original-ring bidual of a finite module
is naturally the maximal-ideal-adic completion, with evaluation the completion map. -/
def matlisBidualCompletion : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R),
    ∃ e : ∀ (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X],
        matlisDualModuleValue E (matlisDualModuleValue E X) ≃ₗ[R]
          AdicCompletion (maximalIdeal R) X,
      (∀ (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X] (x : X),
        e X (matlisEvaluationValue E X x) = AdicCompletion.of (maximalIdeal R) X x) ∧
      (∀ (X Y : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X]
        [AddCommGroup Y] [Module R Y] [Module.Finite R Y] (f : X →ₗ[R] Y)
        (z : matlisDualModuleValue E (matlisDualModuleValue E X)),
        e Y (matlisDualMapValue E (matlisDualMapValue E f) z) =
          AdicCompletion.map (maximalIdeal R) f (e X z))

end CommutativeAlgebraNotes.MatlisDualityAfterCompletionSpecs
