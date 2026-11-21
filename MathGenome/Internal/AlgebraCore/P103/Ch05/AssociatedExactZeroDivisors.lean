import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedExactZeroDivisors
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedPrimesInterface
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Support

namespace P103.Ch05.AssociatedExactZeroDivisors

open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch05.AssociatedExactZeroDivisors
universe u v w x

/-- Over a Noetherian ring Mathlib's radical-annihilator definition agrees
with the source's exact-annihilator definition. No module finiteness is needed. -/
theorem associatedPrimes_eq_mathlib (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    associatedPrimesValue R M = _root_.associatedPrimes R M := by
  ext p
  exact (_root_.isAssociatedPrime_iff (I := p) (M := M)).symm

theorem zero_divisors : zero_divisorsType.{u,v} := by
  intro R _ _ M _ _ _
  rw [associatedPrimes_eq_mathlib]
  exact (biUnion_associatedPrimes_eq_zero_divisors R M).symm

theorem associatedPrimes_exact : associatedPrimes_exactType.{u,v,w,x} := by
  intro R _ _ L M N _ _ _ _ _ _ _ _ _ i q hi he _
  rw [associatedPrimes_eq_mathlib R L, associatedPrimes_eq_mathlib R M,
    associatedPrimes_eq_mathlib R N]
  exact ⟨_root_.associatedPrimes.subset_of_injective hi,
    _root_.associatedPrimes.subset_union_of_exact hi he⟩

/-- Mathlib's support is defined by precisely the same localized module.
Its exact-sequence result uses the fraction-zero criterion, so this equality
is an equality of the localization supports of the specified maps. -/
theorem support_exact : support_exactType.{u,v,w,x} := by
  intro R _ _ L M N _ _ _ _ _ _ _ _ _ i q hi he hq
  exact Module.support_of_exact he hi hq

theorem associatedPrimes_prod : associatedPrimes_prodType.{u,v,w} := by
  intro R _ _ L N _ _ _ _ _ _
  rw [associatedPrimes_eq_mathlib R (L × N), associatedPrimes_eq_mathlib R L,
    associatedPrimes_eq_mathlib R N]
  exact _root_.associatedPrimes.prod R L N

end P103.Ch05.AssociatedExactZeroDivisors
