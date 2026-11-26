import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization

namespace Specs.CommutativeAlgebraNotes.CoefficientRings.FiniteRegularNormalization

open IsLocalRing
open FinitePowerSeriesNormalization (IsFiniteNormalization)

universe u

/-- A complete Noetherian local domain contains a complete regular local subring of
the same dimension. Its inclusion induces an isomorphism on residue fields, makes
the ambient ring a finite module, and extends the maximal ideal to an ideal
with radical equal to the ambient maximal ideal. -/
def Normalization : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B],
    ∃ d : ℕ, ringKrullDim B = (d : WithBot ℕ∞) ∧
      ∃ (S : Subring B) (hS : IsLocalRing S),
        letI : IsLocalRing S := hS
        IsFiniteNormalization d S.subtype

end Specs.CommutativeAlgebraNotes.CoefficientRings.FiniteRegularNormalization
