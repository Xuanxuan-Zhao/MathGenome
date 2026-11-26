import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellentBasicRings
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellentFiniteAlgebrasAndLocalizations

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

/-- The examples and both permanence assertions of Theorem 5.9. -/
def excellentRingsAndPermanenceType : Prop :=
  completeLocal_excellentType.{u} ∧
  field_excellentType.{u} ∧
  int_excellentType ∧
  finiteTypeField_excellentType.{u,v} ∧
  finiteTypeInt_excellentType.{v} ∧
  LocalizedExcellent.{u,v} ∧
  FiniteAlgebraExcellent.{u,v}

end CommutativeAlgebraNotes.Excellence.Specs
