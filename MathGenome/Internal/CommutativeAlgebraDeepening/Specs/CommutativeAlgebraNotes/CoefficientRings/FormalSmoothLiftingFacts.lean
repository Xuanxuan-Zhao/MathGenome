import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.FlatSquareZeroFormalSmoothness

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u v w

/-- The two formal smoothness assertions of Lemma A.1. -/
def formalSmoothLiftingFacts : Prop :=
  FieldFormalSmoothness.primeSubfieldFormallySmooth.{u} ∧
    flatSquareZeroFormalSmoothness.{v, w}

end Specs.CommutativeAlgebraNotes.CoefficientRings
