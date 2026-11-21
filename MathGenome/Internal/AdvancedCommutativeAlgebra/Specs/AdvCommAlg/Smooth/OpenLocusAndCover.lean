import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocusDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! SM-07: openness and the global equivalences for arbitrary A-algebras.
No finite-presentation or nonzero-ring hypothesis is imposed. The finite
principal cover can be empty, as needed when the spectrum is empty. -/
namespace Specs.AdvCommAlg.Smooth.OpenLocusAndCover

universe u v

def locusOpen : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  IsOpen (smoothLocusValue A B)

def smoothIffEveryPrime : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B ↔ ∀ q : PrimeSpectrum B, isSmoothAtValue A B q

def smoothIffFiniteStandardCover : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  smoothValue A B ↔ ∃ s : Finset B,
    Ideal.span (s : Set B) = ⊤ ∧
      ∀ g ∈ s, standardSmoothValue A (Localization.Away g)

/-- In particular, neighborhood smoothness everywhere forces finite presentation. -/
def finitePresentationOfEveryPrime : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  (∀ q : PrimeSpectrum B, isSmoothAtValue A B q) → Algebra.FinitePresentation A B

end Specs.AdvCommAlg.Smooth.OpenLocusAndCover
