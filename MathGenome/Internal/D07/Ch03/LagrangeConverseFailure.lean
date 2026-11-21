import MathGenome.Internal.D07.Ch01.HomOnGenerators
import MathGenome.Internal.D07.Ch01.GroupNormalQuotient
import MathGenome.Internal.D07.Ch02.AlternatingGroups
import MathGenome.Internal.D07.Ch03.FiniteElementOrders
import MathGenome.Internal.D07.Ch03.IndexTwoPreliminary
import MathGenome.Internal.Specs.D07.Ch03.LagrangeConverseFailure

/-! The counterexample to the converse of Lagrange's theorem: A₄ has
order twelve and has no subgroup of order six (paper.tex:648–656). -/

namespace D07.Ch03.LagrangeConverseFailure

/-- The standard alternating-group cardinality formula specializes to twelve. -/
theorem alternating_four_order :
    Specs.D07.Ch03.LagrangeConverseFailure.AlternatingFourOrder := by
  unfold Specs.D07.Ch03.LagrangeConverseFailure.AlternatingFourOrder
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- An index-two quotient kills three-cycles, which generate A₄. -/
theorem no_subgroup_order_six :
    Specs.D07.Ch03.LagrangeConverseFailure.NoSubgroupOrderSix := by
  classical
  intro H hcard
  have hA : Nat.card (alternatingGroup (Fin 4)) = 12 := alternating_four_order
  have hindex : H.index = 2 := by
    have hcount := H.card_mul_index
    rw [hcard, hA] at hcount
    omega
  have : H.Normal :=
    D07.Ch03.IndexTwoPreliminary.normal_of_index_two _ H hindex
  let f := QuotientGroup.mk' H
  have hQ : Nat.card ((alternatingGroup (Fin 4)) ⧸ H) = 2 := hindex
  let S : Set (alternatingGroup (Fin 4)) :=
    {c | Equiv.Perm.IsThreeCycle (c : Equiv.Perm (Fin 4))}
  have hgenerators : ∀ c ∈ S, f c = 1 := by
    intro c hc
    have hc3 : c ^ 3 = 1 := by
      apply Subtype.val_injective
      change (c : Equiv.Perm (Fin 4)) ^ 3 = 1
      rw [← hc.orderOf]
      exact pow_orderOf_eq_one _
    have hf2 : f c ^ 2 = 1 := by
      simpa only [hQ] using
        D07.Ch03.FiniteElementOrders.power_card_eq_one _ (f c)
    have hf3 : f c ^ 3 = 1 := by
      rw [← map_pow, hc3, map_one]
    simpa only [pow_succ, hf2, one_mul] using hf3
  have hall : ∀ c, f c = 1 := by
    intro c
    have hmem : c ∈ Subgroup.closure S := by
      rw [show Subgroup.closure S = ⊤ from alternatingGroup.closure_isThreeCycles_eq_top]
      exact Subgroup.mem_top c
    exact D07.Ch01.HomOnGenerators.agree_on_generated _ _ f 1 S
      hgenerators c hmem
  have htop : H = ⊤ := by
    apply top_unique
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (hall c)
  have hfull : Nat.card H = Nat.card (alternatingGroup (Fin 4)) := by
    rw [htop]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  omega

end D07.Ch03.LagrangeConverseFailure
