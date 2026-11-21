import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocusDefinitions

/-! The neighborhood definition of smoothness at a prime and the smooth locus
from SM-07. These definitions apply to every commutative A-algebra B, without
requiring B to be finitely presented over A.
-/

namespace AdvCommAlg.Smooth

universe u v

/-- B is smooth over A at q if some principal neighborhood of q is smooth.
Here B_g is the canonical localization at the powers of g, with its induced
A-algebra structure. -/
def IsSmoothAt (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B) : Prop :=
  ∃ g : B, g ∉ q.asIdeal ∧ Smooth A (Localization.Away g)

/-- The set of primes at which B is smooth over A. -/
def smoothLocus (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : Set (PrimeSpectrum B) :=
  {q | IsSmoothAt A B q}

theorem isSmoothAt_iff (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B) :
    IsSmoothAt A B q ↔
      ∃ g : B, g ∉ q.asIdeal ∧ Smooth A (Localization.Away g) := Iff.rfl

theorem mem_smoothLocus (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B) :
    q ∈ smoothLocus A B ↔ IsSmoothAt A B q := Iff.rfl

end AdvCommAlg.Smooth
