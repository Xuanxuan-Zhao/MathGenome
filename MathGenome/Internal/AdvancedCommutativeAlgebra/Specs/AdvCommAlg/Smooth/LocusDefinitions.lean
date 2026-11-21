import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Definitions
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-! Independent specifications for the neighborhood definition in SM-07
(paper.tex:1101–1106). The base and algebra are arbitrary commutative unital
rings, including the zero ring. No finite-presentation hypothesis is imposed.
-/

namespace Specs.AdvCommAlg.Smooth

universe u v

def isSmoothAtType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], PrimeSpectrum B → Prop

/-- A prime has a principal neighborhood smooth over the specified base.
The localization carries the algebra structure induced by A → B. -/
def isSmoothAtValue : isSmoothAtType.{u,v} :=
  fun A B _ _ _ q =>
    ∃ g : B, g ∉ q.asIdeal ∧ smoothValue A (Localization.Away g)

def smoothLocusType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], Set (PrimeSpectrum B)

/-- The smooth locus consists exactly of the primes with such a neighborhood. -/
def smoothLocusValue : smoothLocusType.{u,v} :=
  fun A B _ _ _ => {q | isSmoothAtValue A B q}

def isSmoothAtIff : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
  isSmoothAtValue A B q ↔
    ∃ g : B, g ∉ q.asIdeal ∧ smoothValue A (Localization.Away g)

def memSmoothLocus : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B),
  q ∈ smoothLocusValue A B ↔ isSmoothAtValue A B q

end Specs.AdvCommAlg.Smooth
