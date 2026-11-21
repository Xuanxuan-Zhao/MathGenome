import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.FiniteFields
import MathGenome.Internal.D07.Ch13.Existence
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.GaloisField

/-! The finite-field classification in Theorem nt:B02 (paper.tex:447–487). -/

universe u v

namespace P203.Ch02.FiniteFields

theorem characteristic_and_cardinality :
    P203Specs.Ch02.FiniteFields.CharacteristicAndCardinality.{u} := by
  intro F _ _
  let p := ringChar F
  have hp : p.Prime := CharP.prime_ringChar F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := ringChar.charP F
  let := ZMod.algebra F p
  refine ⟨p, Module.finrank (ZMod p) F, hp, inferInstance,
    rfl, inferInstance, Module.finrank_pos, rfl, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem existence : P203Specs.Ch02.FiniteFields.Existence := by
  exact D07.Ch13.Existence.prime_power_existence

theorem uniqueness : P203Specs.Ch02.FiniteFields.Uniqueness.{u, v} := by
  intro p f hp _hf E L _ _ _ _ hE hL
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite E
  let := Fintype.ofFinite L
  have hcE : CharP E p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hE)
  have hcL : CharP L p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hL)
  refine ⟨hcE, hcL, ?_⟩
  let : CharP E p := hcE
  let : CharP L p := hcL
  let := ZMod.algebra E p
  let := ZMod.algebra L p
  exact ⟨FiniteField.algEquivOfCardEq p (by
    simp only [← Nat.card_eq_fintype_card, hE, hL])⟩

end P203.Ch02.FiniteFields
