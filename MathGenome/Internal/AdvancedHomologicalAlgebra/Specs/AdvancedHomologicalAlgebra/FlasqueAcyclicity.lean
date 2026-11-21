import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

/-! HA-H01, source lines 3579–3596. All opens and all ringed spaces are
allowed. Derived sections are the HA-R09 values, with their R(U)-module
structures, for every choice of derived-category models. -/
noncomputable section
universe u w w'
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

namespace Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity

instance sectionsAdditive {X : TopCat.{u}} (R : RingSheaf X) (U : Opens X) :
    (SheafOfModules.evaluation.{u} R (op U)).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

def sectionsSurjectiveType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (S : ShortComplex (Modules R)),
    S.ShortExact → IsFlasque R S.X₁ → ∀ U : Opens X,
      Function.Surjective (S.g.val.app (op U))

def quotientFlasqueType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) (S : ShortComplex (Modules R)),
    S.ShortExact → IsFlasque R S.X₁ → IsFlasque R S.X₂ → IsFlasque R S.X₃

def flasqueAcyclicType : Prop :=
  ∀ {X : TopCat.{u}} (R : RingSheaf X) [EnoughInjectives (Modules R)]
    [HasDerivedCategory.{w} (Modules R)] (U : Opens X)
    [HasDerivedCategory.{w'} (ModuleCat.{u} (sectionRing R U))]
    (M : Modules R), IsFlasque R M → ∀ n : ℕ,
      IsZero ((rightValue (SheafOfModules.evaluation R (op U)) (n + 1)).obj M)

end Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity
