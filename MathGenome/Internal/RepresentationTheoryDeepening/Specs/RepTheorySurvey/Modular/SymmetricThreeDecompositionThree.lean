import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DecompositionMatrix
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SymmetricThreeModules
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The ordered modular simple family and decomposition matrix for (S_3) at three. -/

namespace RepTheorySurvey.Modular.SymmetricThree.DecompositionThreeSpec

universe u v

open IsLocalRing (ResidueField)

set_option backward.isDefEq.respectTransparency false

/-- The first column is trivial and the second is sign. -/
noncomputable def modularFamilyValue (F : Type u) [Field F] :
    Fin 2 → ModuleCat.{u} (MonoidAlgebra F Spec.GroupValue) :=
  ![MR01Spec.representationModuleValue (Spec.trivialValue F),
    MR01Spec.representationModuleValue (Spec.signValue F)]

abbrev modularFamilyType := type_of% (@modularFamilyValue)

/-- At three, the regular conjugacy classes are those of the identity and a transposition. -/
def regularClassesType : Prop :=
  ∀ g : Spec.GroupValue,
    MR01Spec.isPRegularValue 3 g ↔ IsConj g 1 ∨ IsConj g Spec.transpositionValue

section System

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type v} [Field K] [Algebra O K]

local notation "G" => Spec.GroupValue
local notation "k" => ResidueField O

/-- These two columns are a complete list of the simple modules over the residue field. -/
def simpleFamilyType : Prop :=
  ∀ _ : MR01Spec.SplittingSystemData G 3 O K,
    MR01Spec.SimpleRepresentativeFamily (modularFamilyValue k)

private theorem modularGroundFinite (F : Type u) [Field F] (i : Fin 2) :
    Module.Finite F (RestrictScalars F (MonoidAlgebra F G) (modularFamilyValue F i)) := by
  fin_cases i
  · exact Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (Spec.trivialValue F)).symm
  · exact Module.Finite.equiv (MR04Spec.asModuleScalarEquiv (Spec.signValue F)).symm

/-- The lifted Brauer values on the two regular classes, in the fixed column order. -/
def brauerValuesType : Prop :=
  ∀ (system : MR01Spec.SplittingSystemData G 3 O K) (i : Fin 2)
    (g : MR01Spec.pRegularValue G 3),
    letI := modularGroundFinite k i
    (IsConj g.val 1 → MR03Spec.brauerCharacterValue system (modularFamilyValue k i) g = 1) ∧
    (IsConj g.val Spec.transpositionValue →
      MR03Spec.brauerCharacterValue system (modularFamilyValue k i) g =
        (![1, -1] : Fin 2 → O) i)

/-- The canonical decomposition matrix with the specified ordinary rows and modular columns. -/
def decompositionMatrixType : Prop :=
  ∀ system : MR01Spec.SplittingSystemData G 3 O K,
    MR06Spec.decompositionMatrixValue system (Spec.ordinaryFamilyValue K) (modularFamilyValue k) =
      !![1, 0; 0, 1; 1, 1]

end System

/-- Completeness of the modular family over every splitting system at three. -/
def simpleFamilyStatement : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K], simpleFamilyType (O := O) (K := K)

/-- The Brauer values over every splitting system at three. -/
def brauerValuesStatement : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K], brauerValuesType (O := O) (K := K)

/-- The decomposition matrix over every splitting system at three. -/
def decompositionMatrixStatement : Prop :=
  ∀ {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type v} [Field K] [Algebra O K], decompositionMatrixType (O := O) (K := K)

end RepTheorySurvey.Modular.SymmetricThree.DecompositionThreeSpec
