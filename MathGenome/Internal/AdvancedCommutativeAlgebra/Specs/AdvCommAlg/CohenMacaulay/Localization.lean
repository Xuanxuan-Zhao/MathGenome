import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions

/-! CM-06, paper.tex:3358–3389. Zero localizations are admitted in the
maximal-ideal test and arbitrary-localization statement. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def localCohenMacaulay_atPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsLocalRing R] [Nontrivial M], LocalCohenMacaulayValue R M →
    ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
      LocalCohenMacaulayValue (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)

def dimension_eq_localized_add_dimType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsLocalRing R] [Nontrivial M], LocalCohenMacaulayValue R M →
    ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
      dimensionValue R M =
        dimensionValue (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) +
          ringKrullDim (R ⧸ p.asIdeal)

def isCohenMacaulay_iff_maximalType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsCohenMacaulayValue R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        LocalCohenMacaulayValue (Localization.AtPrime m) (LocalizedModule.AtPrime m M)

def isCohenMacaulay_localizedModuleType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsCohenMacaulayValue R M → ∀ S : Submonoid R,
      IsCohenMacaulayValue (Localization S) (LocalizedModule S M)

end AdvCommAlg.CohenMacaulay.Specs
