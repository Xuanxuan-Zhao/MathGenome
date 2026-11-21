import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.AssociatedFiniteness
import MathGenome.Internal.AlgebraCore.P103.Ch05.AssociatedExactZeroDivisors
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
Finiteness and nonemptiness of the source's associated-prime set.
Mathlib proves finiteness by constructing a finite filtration with prime
cyclic factors and applying the associated-prime exact-sequence bound.
The upstream equality with Mathlib's set uses the Noetherian hypothesis,
so its radical-annihilator definition is correctly translated back to the
source's exact element annihilators. Nonemptiness uses the upstream maximal
annihilator argument, and the converse follows from a nonzero witness.
-/
namespace P103.Ch05.AssociatedFiniteness

open P103.Specs.Ch05.AssociatedFiniteness
universe u v

theorem associatedPrimes_finite : associatedPrimes_finiteType.{u,v} := by
  intro R _ _ M _ _ _
  rw [AssociatedExactZeroDivisors.associatedPrimes_eq_mathlib R M]
  exact _root_.associatedPrimes.finite R M

theorem associatedPrimes_nonempty_iff : associatedPrimes_nonempty_iffType.{u,v} := by
  intro R _ _ M _ _ _
  constructor
  · rintro ⟨p, hp, x, hx⟩
    exact ⟨⟨x, 0, AssociatedPrimesInterface.annihilator_witness_ne_zero R M p x hp hx⟩⟩
  · intro hM
    exact @AssociatedPrimesInterface.associatedPrimes_nonempty R _ _ M _ _ hM

theorem associatedPrimes_eq_empty : associatedPrimes_eq_emptyType.{u,v} := by
  intro R _ M _ _ _
  exact AssociatedPrimesInterface.associatedPrimes_eq_empty R M

end P103.Ch05.AssociatedFiniteness
