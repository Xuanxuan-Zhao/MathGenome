import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

/-! GC-10, paper.tex:4701–4739. The coefficient is actual Ext over the
source, with the first-argument action of the target ring. The comparison
is an isomorphism of functors on all target modules, including infinite ones.
An algebra structure records an arbitrary ring homomorphism S → R. -/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.CanonicalQuotient
open ConcentratedChangeOfRings

/-- The prescribed canonical-module candidate, with its natural R-action. -/
abbrev omega (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]
    (s d : ℕ) : ModuleCat.{u} R :=
  coefficient (algebraMap S R) (ModuleCat.of S S) (s - d)

end AdvCommAlg.Gorenstein.CanonicalQuotient

namespace AdvCommAlg.Gorenstein.CanonicalQuotientSpecs
open CanonicalQuotient ConcentratedChangeOfRings

def dimensionLeType : Prop :=
  ∀ (S R : Type u) [CommRing S] [CommRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalRing S] [IsLocalRing R]
    [Algebra S R], Function.Surjective (algebraMap S R) →
    Specs.LocalGorensteinValue S → CohenMacaulay.Specs.LocalCohenMacaulayValue R R →
    ∀ s d : ℕ, ringKrullDim S = (s : WithBot ℕ∞) →
      ringKrullDim R = (d : WithBot ℕ∞) → d ≤ s

def comparisonType : Prop :=
  ∀ (S R : Type u) [CommRing S] [CommRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalRing S] [IsLocalRing R]
    [Algebra S R], Function.Surjective (algebraMap S R) →
    Specs.LocalGorensteinValue S → CohenMacaulay.Specs.LocalCohenMacaulayValue R R →
    ∀ s d : ℕ, ringKrullDim S = (s : WithBot ℕ∞) →
      ringKrullDim R = (d : WithBot ℕ∞) → ∀ i : ℕ,
      Nonempty (coefficientExtFunctor (algebraMap S R) (ModuleCat.of S S) (s - d) i ≅
        shiftedExtFunctor (algebraMap S R) (ModuleCat.of S S) (s - d) i)

def propertiesType : Prop :=
  ∀ (S R : Type u) [CommRing S] [CommRing R]
    [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalRing S] [IsLocalRing R]
    [Algebra S R], Function.Surjective (algebraMap S R) →
    Specs.LocalGorensteinValue S → CohenMacaulay.Specs.LocalCohenMacaulayValue R R →
    ∀ s d : ℕ, ringKrullDim S = (s : WithBot ℕ∞) →
      ringKrullDim R = (d : WithBot ℕ∞) →
      ∃ hfin : Module.Finite R (omega S R s d),
        letI := hfin
        Specs.IsCanonicalModuleValue R (omega S R s d) ∧
        injectiveDimension (omega S R s d) = (d : WithBot ℕ∞) ∧
        (∀ i : ℕ, i ≠ d → Subsingleton (Depth.ResidueExt (omega S R s d) i)) ∧
        Nonempty (Depth.ResidueExt (omega S R s d) d ≃ₗ[IsLocalRing.ResidueField R]
          IsLocalRing.ResidueField R)

end AdvCommAlg.Gorenstein.CanonicalQuotientSpecs
