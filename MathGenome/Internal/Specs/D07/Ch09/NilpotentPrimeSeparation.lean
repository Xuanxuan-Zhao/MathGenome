import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Nilpotent.Defs

/-!
Independent statement of `lem:nilpotent-prime-separation`, paper.tex:1783–1800.

The coefficient ring is commutative, associative and unital, and may be the
zero ring. `Ideal.IsPrime` includes properness. Over a commutative ring every
`Ideal` is two-sided. `IsNilpotent x` means that some natural power of `x`
equals zero; it does not impose a uniform exponent on the ring.
-/

universe u

namespace Specs.D07.Ch09.NilpotentPrimeSeparation

/-- An element lies in every prime ideal exactly when it is nilpotent.
There is no nontriviality, domain, finiteness or Noetherian hypothesis. -/
def MemEveryPrimeIffNilpotent : Prop :=
  ∀ (R : Type u) [CommRing R] (x : R),
    (∀ P : Ideal R, P.IsPrime → x ∈ P) ↔ IsNilpotent x

end Specs.D07.Ch09.NilpotentPrimeSeparation
