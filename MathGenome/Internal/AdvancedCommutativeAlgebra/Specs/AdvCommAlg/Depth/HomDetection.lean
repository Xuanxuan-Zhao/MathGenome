import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! Independent statement of the Hom-detection assertion of DP-03.
`Module.support` uses nonzero localizations; over a Noetherian ring,
`associatedPrimes` consists exactly of prime annihilators of elements.
No nonzero hypothesis is imposed on either module or on the ring. -/
namespace Specs.AdvCommAlg.Depth

universe u v w

def HomDetection : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M],
    (∃ f : N →ₗ[R] M, f ≠ 0) ↔
      (Module.support R N ∩ {p : PrimeSpectrum R | p.asIdeal ∈ associatedPrimes R M}).Nonempty

end Specs.AdvCommAlg.Depth
