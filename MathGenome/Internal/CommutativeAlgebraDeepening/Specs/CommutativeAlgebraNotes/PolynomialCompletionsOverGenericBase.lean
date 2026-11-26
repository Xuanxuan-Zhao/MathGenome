import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants

namespace Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase

open IsLocalRing
open _root_.CommutativeAlgebraNotes.Excellence.Specs (GeometricallyRegularValue)
open PolynomialCompletionsOverRegularConstants (GenericConstantsFibre)

universe u

/-- For every polynomial prime over a complete local domain, invert the
nonzero constants in its completed local ring. -/
def OverCompleteLocalDomain : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (P : Ideal (Polynomial A)) [P.IsPrime],
    GeometricallyRegularValue (FractionRing A) (GenericConstantsFibre P)

end Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase
