import MathGenome.Internal.Specs.D07.Ch20.SeparableInseparableDegrees
import MathGenome.Internal.D07.Ch12.EmbeddingCount
import MathGenome.Internal.D07.Ch20.PurelyInseparable
import MathGenome.Internal.D07.Ch20.SeparablePart
import MathGenome.Internal.D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres

/-!
Separable and inseparable degrees of finite extensions.
Restriction to the separable part is bijective because the upper step is
purely inseparable. Its degree over K therefore counts the embeddings.
The ordinary tower law gives the degree factorization. The positive
characteristic assertion applies the purely inseparable degree theorem to
the upper step. For arbitrary finite towers, the accepted restriction-fibre
argument gives the separable-degree identity; cancellation of its positive
value in the ordinary degree identity gives the inseparable-degree identity.
-/

universe u v w

namespace D07.Ch20.SeparableInseparableDegrees

open Specs.D07.Ch20.SeparableInseparableDegrees

noncomputable section

theorem embedding_count : EmbeddingCount.{u, v, w} := by
  intro K L Ω _ _ _ _ _ _ _
  exact ⟨D07.Ch12.EmbeddingCount.finite_embeddings K L Ω,
    (Field.finSepDegree_eq_of_isAlgClosed K L Ω).symm⟩

theorem restriction_bijection : RestrictionBijection.{u, v, w} := by
  intro K L Ω _ _ _ _ _ _ _
  exact IsPurelyInseparable.bijective_restrictDomain (separableClosure K L) L K Ω

theorem separable_degree_part : SeparableDegreePart.{u, v} := by
  intro K L _ _ _ _
  have h := D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres.finSepDegree_tower
    K (separableClosure K L) L
  simpa only [IsPurelyInseparable.finSepDegree_eq_one,
    Field.finSepDegree_eq_finrank_of_isSeparable, one_mul] using h

theorem inseparable_degree_part : InseparableDegreePart.{u, v} := by
  intro K L _ _ _ _
  rfl

theorem degree_factorization : DegreeFactorization.{u, v} := by
  intro K L _ _ _ _
  exact ⟨(Field.finSepDegree_mul_finInsepDegree K L).symm,
    Nat.pos_of_ne_zero (NeZero.ne _), Nat.pos_of_ne_zero (NeZero.ne _)⟩

theorem positive_characteristic : PositiveCharacteristic.{u, v} := by
  intro K L _ _ _ _ p _ hp
  let : ExpChar K p := ExpChar.prime hp
  let : CharP (separableClosure K L) p :=
    charP_of_injective_algebraMap
      (algebraMap K (separableClosure K L)).injective p
  exact D07.Ch20.PurelyInseparable.finite_degree
    (separableClosure K L) L p hp inferInstance

theorem characteristic_zero : CharacteristicZero.{u, v} := by
  intro K L _ _ _ _ _
  exact Algebra.IsSeparable.finInsepDegree_eq K L

theorem separable_degree_tower : SeparableDegreeTower.{u, v, w} := by
  exact D07.Ch20.SeparableInseparableDegreesRestrictionEmbeddingFibres.finSepDegree_tower

theorem inseparable_degree_tower : InseparableDegreeTower.{u, v, w} := by
  intro K M L _ _ _ _ _ _ _ _ _
  let : FiniteDimensional K L := FiniteDimensional.trans K M L
  apply Nat.eq_of_mul_eq_mul_left (degree_factorization K L).2.1
  calc
    Field.finSepDegree K L * Field.finInsepDegree K L = Module.finrank K L :=
      Field.finSepDegree_mul_finInsepDegree K L
    _ = Module.finrank K M * Module.finrank M L :=
      (Module.finrank_mul_finrank K M L).symm
    _ = (Field.finSepDegree K M * Field.finInsepDegree K M) *
        (Field.finSepDegree M L * Field.finInsepDegree M L) := by
      rw [Field.finSepDegree_mul_finInsepDegree, Field.finSepDegree_mul_finInsepDegree]
    _ = Field.finSepDegree K L *
        (Field.finInsepDegree M L * Field.finInsepDegree K M) := by
      rw [separable_degree_tower K M L]
      ac_rfl

end

end D07.Ch20.SeparableInseparableDegrees
