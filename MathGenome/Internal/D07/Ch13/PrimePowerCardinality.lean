import MathGenome.Internal.Specs.D07.Ch13.PrimePowerCardinality
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.Algebra.CharP.Lemmas

/-! Prime characteristic and cardinality of finite fields and finite extensions.
The coordinate-count theorem is used with the specified scalar action. -/

universe u v

namespace D07.Ch13.PrimePowerCardinality

theorem characteristic_prime :
    Specs.D07.Ch13.PrimePowerCardinality.CharacteristicPrime.{u} := by
  intro F _ _
  exact CharP.prime_ringChar F

theorem prime_power_cardinality :
    Specs.D07.Ch13.PrimePowerCardinality.FiniteFieldCardinality.{u} := by
  intro F _ _
  let p := ringChar F
  have hp : p.Prime := characteristic_prime F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := ringChar.charP F
  let := ZMod.algebra F p
  refine ⟨p, Module.finrank (ZMod p) F, hp, inferInstance,
    inferInstance, Module.finrank_pos, ?_, ?_⟩
  · exact D07.Ch12.DegreeDefinition.degree_eq_finrank (ZMod p) F
  · rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem extension_cardinality :
    Specs.D07.Ch13.PrimePowerCardinality.ExtensionCardinality.{u, v} := by
  intro K L _ _ _ _ _
  have hfinite : Finite L :=
    Finite.of_injective (Module.finBasis K L).equivFun
      (Module.finBasis K L).equivFun.injective
  exact ⟨hfinite, Module.finrank_pos, Module.natCard_eq_pow_finrank⟩

theorem extension_cardinality_of_degree
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite K]
    (q n : ℕ) (hcard : Nat.card K = q)
    (hdegree : D07.Ch12.DegreeDefinition.degree K L = (n : Cardinal.{v})) :
    Finite L ∧ 1 ≤ n ∧ Nat.card L = q ^ n := by
  obtain ⟨hfiniteDimensional, hfinrank⟩ :=
    (D07.Ch12.DegreeDefinition.degree_eq_nat_iff K L n).mp hdegree
  let := hfiniteDimensional
  simpa only [hcard, hfinrank] using extension_cardinality K L

end D07.Ch13.PrimePowerCardinality
