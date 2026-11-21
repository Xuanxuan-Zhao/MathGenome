import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions

/-! Independent specifications for SN-10, paper.tex:4282–4292.
Both statements concern arbitrary Noetherian rings. In particular no
locality, domain, or nonzero assumption is imposed on the ambient ring. -/
universe u
namespace AdvCommAlg.Normality.Specs

def isNormal_of_regular_at_every_primeType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    (∀ p : PrimeSpectrum A, IsRegularLocalRing (Localization.AtPrime p.asIdeal)) →
      IsNormalValue A

def cohenMacaulay_isNormal_iff_regularInCodimension_oneType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    CohenMacaulay.Specs.CohenMacaulayRingValue A →
      (IsNormalValue A ↔ RegularInCodimensionValue A 1)

end AdvCommAlg.Normality.Specs
