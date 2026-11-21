import MathGenome.Internal.Specs.D07.Ch14.DegreeIndex
import MathGenome.Internal.D07.Ch03.Lagrange
import MathGenome.Internal.D07.Ch12.TowerLaw
import MathGenome.Internal.D07.Ch14.ArtinFixedField
import MathGenome.Internal.D07.Ch14.AutomorphismBound

/-!
Degrees, orders and indices, K07.14.degree_index.

Artin gives [L:L^H] = |H|, and the automorphism-count criterion gives
[L:K] = |Aut_K(L)|. The finite tower law and Lagrange's formula then
give equal products with the positive factor |H|, which can be cancelled.
The upstream quotient/coset equivalence identifies the index with the
source's number of distinct left cosets, without any normality assumption.
-/

universe u v

namespace D07.Ch14.DegreeIndex

theorem degree_index : Specs.D07.Ch14.DegreeIndex.DegreeIndexIdentities.{u, v} := by
  intro K L _ _ _ _ _ H
  let E := Specs.D07.Ch14.FixedField.fixedFieldValue K L H
  have hupper : Module.finrank E L = Nat.card H :=
    (ArtinFixedField.subgroup_artin K L H).2.2.1
  have htotal : Module.finrank K L = Nat.card (L ≃ₐ[K] L) :=
    ((AutomorphismBound.equality_iff_galois K L).mpr inferInstance).symm
  have hlagrange : Nat.card (L ≃ₐ[K] L) = Nat.card H * H.index := by
    rw [← Ch03.Lagrange.coset_count_eq_index]
    exact Ch03.Lagrange.cardinality_formula (L ≃ₐ[K] L) H
  have hpositive : 0 < Nat.card H :=
    (Ch03.Lagrange.positive_cardinalities (L ≃ₐ[K] L) H).1
  have hindex : Module.finrank K E = H.index := by
    apply Nat.eq_of_mul_eq_mul_left hpositive
    calc
      Nat.card H * Module.finrank K E =
          Module.finrank E L * Module.finrank K E := by rw [hupper]
      _ = Module.finrank K L := by
        rw [Nat.mul_comm, Module.finrank_mul_finrank K E L]
      _ = Nat.card (L ≃ₐ[K] L) := htotal
      _ = Nat.card H * H.index := hlagrange
  exact ⟨hupper, hindex, htotal⟩

end D07.Ch14.DegreeIndex
