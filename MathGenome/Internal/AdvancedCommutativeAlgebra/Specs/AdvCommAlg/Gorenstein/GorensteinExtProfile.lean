import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-! Independent specification of the forward Gorenstein consequences in GC-06,
paper.tex:4557–4593, with the chapter's nonzero Noetherian local conventions.
The Gorenstein hypothesis is finite self-injective dimension. -/

universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.ExtProfileSpecs

def cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R → CohenMacaulay.Specs.LocalCohenMacaulayValue R R

def injectiveDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R →
      injectiveDimension (ModuleCat.of R R) = ringKrullDim R

def extVanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R → ∀ (d : ℕ), ringKrullDim R = (d : WithBot ℕ∞) →
      ∀ i : ℕ, i ≠ d → Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i)

def extEquivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R → ∀ (d : ℕ), ringKrullDim R = (d : WithBot ℕ∞) →
      Nonempty (Depth.ResidueExt (ModuleCat.of R R) d ≃ₗ[IsLocalRing.ResidueField R]
        IsLocalRing.ResidueField R)

def typeOneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R → Specs.ringTypeValue R = 1

end AdvCommAlg.Gorenstein.ExtProfileSpecs
