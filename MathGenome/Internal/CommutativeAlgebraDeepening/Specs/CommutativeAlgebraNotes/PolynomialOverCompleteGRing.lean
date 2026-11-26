import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Polynomial.Basic

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u

/-- Lemma 5.13. The polynomial ring in one variable over a Noetherian
local ring complete for its maximal ideal is a G-ring. -/
def polynomial_isGRing_of_completeLocalType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A], IsGRingValue (Polynomial A)

end CommutativeAlgebraNotes.Excellence.Specs
