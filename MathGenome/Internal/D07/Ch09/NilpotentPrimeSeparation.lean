import MathGenome.Internal.Specs.D07.Ch09.NilpotentPrimeSeparation
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! Prime-ideal separation of elements that are not nilpotent. -/

universe u

namespace D07.Ch09.NilpotentPrimeSeparation

/-- The intersection of all prime ideals consists of the nilpotent elements,
including when the ring is trivial. Mathlib proves the radical-intersection
theorem using Zorn's lemma on ideals avoiding powers of the element. -/
theorem memEveryPrimeIffNilpotent :
    Specs.D07.Ch09.NilpotentPrimeSeparation.MemEveryPrimeIffNilpotent.{u} := by
  intro R _ x
  exact (nilpotent_iff_mem_prime (x := x)).symm

end D07.Ch09.NilpotentPrimeSeparation
