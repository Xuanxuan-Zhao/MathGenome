import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellentRingsAndPermanence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellentBasicRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellentFiniteAlgebrasAndLocalizations

namespace CommutativeAlgebraNotes.Excellence

universe u v

/-- The basic examples of excellent rings and permanence under localization
and passage to finite algebras. -/
theorem excellentRingsAndPermanence : Specs.excellentRingsAndPermanenceType.{u,v} :=
  ⟨completeLocal_excellent, field_excellent, int_excellent, finiteTypeField_excellent,
    finiteTypeInt_excellent, @Excellent.of_isLocalization, @Excellent.of_finite⟩

end CommutativeAlgebraNotes.Excellence
