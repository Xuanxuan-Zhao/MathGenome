import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-! GC-06, paper.tex:4557–4593: the three equivalent local conditions.
`IsLocalRing` includes nonzeroness. Vanishing of an Ext group is expressed
by its underlying additive group being a subsingleton. -/

universe u
namespace AdvCommAlg.Gorenstein.TypeOneCriterionSpecs

noncomputable def cohenMacaulayTypeOneType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R ↔
      CohenMacaulay.Specs.LocalCohenMacaulayValue R R ∧ Specs.ringTypeValue R = 1

noncomputable def eventuallyExtVanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R ↔
      ∃ n : ℕ, ∀ i : ℕ, n < i →
        Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i)

noncomputable def cohenMacaulayTypeOneEventuallyExtType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    (CohenMacaulay.Specs.LocalCohenMacaulayValue R R ∧ Specs.ringTypeValue R = 1) ↔
      ∃ n : ℕ, ∀ i : ℕ, n < i →
        Subsingleton (Depth.ResidueExt (ModuleCat.of R R) i)

end AdvCommAlg.Gorenstein.TypeOneCriterionSpecs
