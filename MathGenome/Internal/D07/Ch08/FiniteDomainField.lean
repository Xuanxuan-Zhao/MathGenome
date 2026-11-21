import MathGenome.Internal.Specs.D07.Ch08.FiniteDomainField
import MathGenome.Internal.D07.Ch08.ZeroDivisorCancellation
import Mathlib.Data.Fintype.Card

/-!
Finite domains are fields (K07.08.finite_domain_field).
Cancellation makes multiplication by a nonzero element injective. On the
finite underlying set it is surjective, so 1 has a preimage. Commutativity
makes this a two-sided inverse. The integer example witnesses the need
for finiteness.
-/

universe u

namespace D07.Ch08.FiniteDomainField

open Specs.D07.Ch08.FiniteDomainField

theorem nonzeroMultiplicationBijective : NonzeroMultiplicationBijective.{u} := by
  intro R _ _ _ a ha
  have hinj : Function.Injective (fun x : R => a * x) := by
    intro b c hbc
    exact (ZeroDivisorCancellation.domainCancellation R a b c ha).1.mp hbc
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem finiteDomainInverse : FiniteDomainInverse.{u} := by
  intro R _ _ _ a ha
  obtain ⟨b, hab⟩ := (nonzeroMultiplicationBijective R a ha).2 1
  exact ⟨b, hab, (mul_comm b a).trans hab⟩

theorem finiteDomainIsField : FiniteDomainIsField.{u} := by
  intro R _ _ _
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hab, _⟩ := finiteDomainInverse R a ha
  exact ⟨b, hab⟩

theorem fieldStructure : FieldStructure.{u} := by
  intro R s _ _
  exact ⟨(finiteDomainIsField R).toField, rfl⟩

theorem integerCounterexample : IntegerCounterexample := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro hfield
  obtain ⟨b, hab⟩ := hfield.mul_inv_cancel (by decide : (2 : ℤ) ≠ 0)
  apply Units.integerTwoNotIsUnit
  exact (Units.unitCharacterization ℤ 2).mpr
    ⟨b, hab, (mul_comm b 2).trans hab⟩

end D07.Ch08.FiniteDomainField
