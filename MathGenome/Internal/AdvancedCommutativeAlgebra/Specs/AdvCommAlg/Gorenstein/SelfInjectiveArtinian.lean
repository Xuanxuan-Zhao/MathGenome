import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.HopkinsLevitzki

/-! Independent specification for the first assertion of GC-05.
`IsLocalRing` includes nontriviality. Self-injectivity means injectivity of the
regular module, with no hypothesis about dimension, depth, or its socle. -/

universe u

namespace AdvCommAlg.Gorenstein.Specs

def isArtinianRing_of_selfInjectiveType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    CategoryTheory.Injective (ModuleCat.of R R) → IsArtinianRing R

end AdvCommAlg.Gorenstein.Specs
