import MathGenome.Internal.D07.Ch03.CosetBijections
import MathGenome.Internal.Specs.D07.Ch03.Lagrange
import Mathlib.GroupTheory.Index

/-!
# Lagrange's theorem

K07.03.lagrange, paper.tex:591–598. We first identify Mathlib's quotient
set with the space of distinct left-coset subsets used upstream. Thus the
library cardinality formula counts exactly the source's cosets. Finiteness
is retained in all statements of the source's natural-number conclusions.
-/

namespace D07.Ch03.Lagrange

open Specs.D07.Ch03.CosetsPartition

universe u

/-- Equality of the shared set-valued left cosets is the left-coset relation. -/
theorem left_coset_eq_iff (G : Type u) [Group G] (H : Subgroup G) (x y : G) :
    leftCoset H x = leftCoset H y ↔ x⁻¹ * y ∈ H := by
  have hy : y ∈ leftCoset H y := ⟨1, H.one_mem, mul_one y⟩
  constructor
  · intro heq
    have hxy : y ∈ leftCoset H x := heq.symm ▸ hy
    rwa [← CosetsPartition.left_class_eq_coset G H x] at hxy
  · intro hxy
    have hmem : y ∈ leftCoset H x := by
      rw [← CosetsPartition.left_class_eq_coset G H x]
      exact hxy
    rcases CosetsPartition.left_cosets_eq_or_disjoint G H x y with heq | hd
    · exact heq
    · exact False.elim (Set.disjoint_left.mp hd hmem hy)

/-- A quotient class represents precisely one distinct left-coset subset.
This is an equivalence of sets for every subgroup, without normality. -/
noncomputable def quotientEquivLeftCosets (G : Type u) [Group G] (H : Subgroup G) :
    G ⧸ H ≃ ↥(Set.range (leftCoset H)) :=
  (Quotient.congrRight (fun x y =>
    (QuotientGroup.leftRel_apply (s := H)).trans (left_coset_eq_iff G H x y).symm)).trans
    (Setoid.quotientKerEquivRange (leftCoset H))

theorem coset_count_eq_index (G : Type u) [Group G] (H : Subgroup G) :
    Nat.card ↥(Set.range (leftCoset H)) = H.index :=
  (Nat.card_congr (quotientEquivLeftCosets G H)).symm

theorem cardinality_formula (G : Type u) [Group G] [Finite G] (H : Subgroup G) :
    Nat.card G = Nat.card H * Nat.card ↥(Set.range (leftCoset H)) := by
  rw [coset_count_eq_index]
  exact H.card_mul_index.symm

theorem subgroup_card_divides (G : Type u) [Group G] [Finite G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  ⟨Nat.card ↥(Set.range (leftCoset H)), cardinality_formula G H⟩

theorem coset_count_divides (G : Type u) [Group G] [Finite G] (H : Subgroup G) :
    Nat.card ↥(Set.range (leftCoset H)) ∣ Nat.card G := by
  rw [coset_count_eq_index]
  exact H.index_dvd_card

theorem positive_cardinalities (G : Type u) [Group G] [Finite G] (H : Subgroup G) :
    0 < Nat.card H ∧ 0 < Nat.card ↥(Set.range (leftCoset H)) := by
  have hprod := Nat.card_pos (α := G)
  rw [cardinality_formula G H] at hprod
  exact ⟨Nat.pos_of_mul_pos_right hprod, Nat.pos_of_mul_pos_left hprod⟩

end D07.Ch03.Lagrange
