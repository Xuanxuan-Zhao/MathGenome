import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.UnramifiedRegularPresentation

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u

/-- The regular cover and the two power-series presentations of a complete local ring. -/
def CompleteRegularPresentations : Prop :=
  CompleteRegularCover.{u} ∧
    EqualCharacteristicRegularPresentation.Presentation.{u} ∧
    _root_.CommutativeAlgebraNotes.CoefficientRings.Specs.unramifiedRegularPresentationType.{u}

end Specs.CommutativeAlgebraNotes.CoefficientRings
