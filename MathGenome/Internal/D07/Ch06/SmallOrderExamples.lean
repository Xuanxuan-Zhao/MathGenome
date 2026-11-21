import MathGenome.Internal.Specs.D07.Ch06.SmallOrderExamples
import MathGenome.Internal.D07.Ch06.SmallOrderExamplesOrderSix
import MathGenome.Internal.D07.Ch06.SmallOrderExamplesOrderEight
import MathGenome.Internal.D07.Ch04.NormalityNotTransitive
import MathGenome.Internal.D07.Ch06.SylowCounting

namespace D07.Ch06.SmallOrderExamples

open Specs.D07.Ch06.SmallOrderExamples
open Specs.D07.Ch04.NormalityNotTransitive

universe u

theorem order_six_classification :
    Specs.D07.Ch06.SmallOrderExamples.OrderSixClassification.{u} :=
  SmallOrderExamplesOrderSix.classification

theorem order_six_models : OrderSixModels := SmallOrderExamplesOrderSix.models

theorem order_eight_classification :
    Specs.D07.Ch06.SmallOrderExamples.OrderEightClassification.{u} :=
  SmallOrderExamplesOrderEight.classification

theorem order_eight_models : OrderEightModels :=
  ⟨SmallOrderExamplesOrderEight.model_cardinalities,
    SmallOrderExamplesOrderEight.pairwise_nonisomorphic⟩

lemma alternating_four_card : Nat.card A4 = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem alternating_four_sylow_two : AlternatingFourSylowTwo := by
  obtain ⟨V, H, hV, _, _, _, _, hn, _⟩ :=
    D07.Ch04.NormalityNotTransitive.normality_not_transitive
  have hle : V ≤ alternatingGroup (Fin 4) := by
    intro x hx
    rw [← SetLike.mem_coe, hV] at hx
    simp only [vCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      rw [Equiv.Perm.mem_alternatingGroup] <;> decide
  have hcard : Nat.card V = 4 := by
    change Nat.card ↥(V : Set S4) = 4
    rw [hV]
    let : DecidablePred (· ∈ vCarrier) := fun g =>
      inferInstanceAs (Decidable (g = 1 ∨ g = double12_34 ∨
        g = double13_24 ∨ g = double14_23))
    rw [Nat.card_eq_fintype_card]
    decide
  let W : Subgroup A4 := V.subgroupOf (alternatingGroup (Fin 4))
  have hW : Nat.card W = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans hcard
  have hnW : W.Normal := hn.subgroupOf _
  obtain ⟨P, hP⟩ := (SylowDefinition.sylow_iff_card A4 2 2 3 (by decide)
    (by rw [alternating_four_card]; decide) (by decide) W).mpr (by simpa using hW)
  have hnP : P.Normal := by rw [hP]; exact hnW
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Unique (Sylow 2 A4) := Sylow.unique_of_normal P hnP
  refine ⟨W, ?_, hnW, hW, ?_, ⟨P, hP⟩, ?_⟩
  · intro g
    change (g : S4) ∈ V ↔ _
    rw [← SetLike.mem_coe, hV]
  · intro x
    have hx : ((x : A4) : S4) ∈ vCarrier := by
      rw [← hV]
      exact x.property
    apply Subtype.ext
    apply Subtype.ext
    change (((x : A4) : S4) ^ 2) = 1
    simp only [vCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> decide
  · intro Q
    rw [Subsingleton.elim Q P, hP]

/- The three-cycle subgroup fixing the fourth letter is self-normalizing in A₄.
The finite checks below evaluate the displayed permutations on the four letters. -/
private def threeCycleSubgroup : Subgroup A4 where
  carrier := {g | (g : S4) = 1 ∨ (g : S4) = cycle123 ∨
    (g : S4) = cycle123 ^ 2}
  one_mem' := Or.inl rfl
  mul_mem' := by decide
  inv_mem' := by decide

private instance : DecidablePred (· ∈ threeCycleSubgroup) := fun g =>
  inferInstanceAs (Decidable ((g : S4) = 1 ∨ (g : S4) = cycle123 ∨
    (g : S4) = cycle123 ^ 2))

private lemma threeCycleSubgroup_card : Nat.card threeCycleSubgroup = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option maxRecDepth 10000 in
private lemma threeCycleSubgroup_normalizer :
    Subgroup.normalizer (threeCycleSubgroup : Set A4) = threeCycleSubgroup := by
  ext g
  change (∀ h : A4, h ∈ threeCycleSubgroup ↔
    g * h * g⁻¹ ∈ threeCycleSubgroup) ↔ g ∈ threeCycleSubgroup
  revert g
  decide

theorem alternating_four_sylow_three_count : AlternatingFourSylowThreeCount := by
  have hi : (Subgroup.normalizer (threeCycleSubgroup : Set A4)).index = 4 := by
    have h := threeCycleSubgroup.card_mul_index
    rw [threeCycleSubgroup_card, alternating_four_card] at h
    rw [threeCycleSubgroup_normalizer]
    omega
  have hcount := SylowCounting.count_eq_index_normalizer A4 3 1 4 (by decide)
    (by rw [alternating_four_card]; decide) (by decide) threeCycleSubgroup
    (by simpa using threeCycleSubgroup_card)
  rw [SylowCounting.card_subgroups_eq_card_sylow A4 3 1 4 (by decide)
    (by rw [alternating_four_card]; decide) (by decide), hi] at hcount
  exact hcount

end D07.Ch06.SmallOrderExamples
