import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-! Independent GC-09 concentration specification (paper.tex:4653–4700).
The first argument is any nonzero finite CM module, with dimension measured
by the support. Local rings are nonzero by `IsLocalRing`.
-/
universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Gorenstein.CMExtConcentrationSpecs

def dimensionLeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R →
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.Specs.LocalCohenMacaulayValue R M →
      ∀ s e : ℕ, ringKrullDim R = (s : WithBot ℕ∞) →
        Module.supportDim R M = (e : WithBot ℕ∞) → e ≤ s

def vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Specs.LocalGorensteinValue R →
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.Specs.LocalCohenMacaulayValue R M →
      ∀ s e : ℕ, ringKrullDim R = (s : WithBot ℕ∞) →
        Module.supportDim R M = (e : WithBot ℕ∞) →
        ∀ i : ℕ, i ≠ s - e → Subsingleton (Ext M (ModuleCat.of R R) i)

end AdvCommAlg.Gorenstein.CMExtConcentrationSpecs
