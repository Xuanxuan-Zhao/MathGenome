import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeModules
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DecompositionMatrix

/-! The ordered modular simple family and decomposition matrix for (S_3) at (p=2). -/

namespace RepTheorySurvey.Modular.SymmetricThree.DecompositionTwoSpec

universe u v

open IsLocalRing (ResidueField)

abbrev modularFamilyType (F : Type u) [Field F] :=
  Fin 2 → ModuleCat.{u} (MonoidAlgebra F Spec.GroupValue)

noncomputable def modularFamilyValue (F : Type u) [Field F] : modularFamilyType F :=
  ![MR01Spec.representationModuleValue (Spec.trivialValue F),
    MR01Spec.representationModuleValue (Spec.standardValue F)]

abbrev familyType := type_of% (@modularFamilyValue)

/-- The classes represented by the identity and a three-cycle are the two regular classes. -/
def regularClasses : Prop :=
  (∀ g : MR01Spec.pRegularValue Spec.GroupValue 2,
    IsConj g.val 1 ∨ IsConj g.val Spec.threeCycleValue) ∧
  Nat.card (MR03Spec.pRegularConjClassesValue Spec.GroupValue 2) = 2

def ordinaryRegularRestrictions : Prop :=
  ∀ (K : Type v) [Field K] (g : MR01Spec.pRegularValue Spec.GroupValue 2),
    (Spec.signValue K).character g.val = (Spec.trivialValue K).character g.val

def modularSimpleFamily : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData Spec.GroupValue 2 O K → MR01Spec.SimpleRepresentativeFamily (modularFamilyValue (ResidueField O))

def standardReductionDimension : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData Spec.GroupValue 2 O K →
    let k := ResidueField O
    Module.finrank k (RestrictScalars k (MonoidAlgebra k Spec.GroupValue)
      (modularFamilyValue k 1)) = 2

def decompositionMatrix : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K] (system : MR01Spec.SplittingSystemData Spec.GroupValue 2 O K),
    MR06Spec.decompositionMatrixValue system (Spec.ordinaryFamilyValue K)
      (modularFamilyValue (ResidueField O)) =
      (!![1, 0; 1, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℕ)

end RepTheorySurvey.Modular.SymmetricThree.DecompositionTwoSpec
