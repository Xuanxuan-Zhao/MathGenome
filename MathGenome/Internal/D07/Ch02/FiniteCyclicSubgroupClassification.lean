import MathGenome.Internal.D07.Ch02.CyclicAbelianAndSubgroups
import MathGenome.Internal.D07.Ch02.CyclicModelsIsomorphism
import MathGenome.Internal.D07.Ch02.OrderOfPower
import MathGenome.Internal.D07.Ch02.SubgroupsOfIntegerGroup
import MathGenome.Internal.Specs.D07.Ch02.FiniteCyclicSubgroupClassification
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Subgroups and generators of a finite cyclic group (paper.tex:481–488).

The order-of-power formula gives size d to the indicated subgroup.
In a cyclic group finite subgroups of equal cardinality coincide, proving
uniqueness. Equality of power-generated subgroups is characterized by gcds,
including negative and zero exponents. Finally generators are exactly the
elements of full order, to which the cyclic-group totient count applies.
-/

namespace D07.Ch02.FiniteCyclicSubgroupClassification

universe u

theorem unique_subgroup_of_order (G : Type u) [Group G] (x : G) (n : ℕ)
    (hx : Subgroup.zpowers x = ⊤) (hn : 0 < n) (hcard : Nat.card G = n)
    (d : ℕ) (_hd : 0 < d) (hdvd : d ∣ n) :
    Nat.card (Subgroup.zpowers (x ^ (n / d))) = d ∧
      ∀ H : Subgroup G,
        Nat.card H = d ↔ H = Subgroup.zpowers (x ^ (n / d)) := by
  let : Finite G := Nat.finite_of_card_ne_zero (hcard.trans_ne hn.ne')
  let : IsCyclic G :=
    (D07.Ch02.CyclicDefinition.cyclic_iff_cyclic_subgroup_eq_top G).mpr ⟨x, hx⟩
  have horder : orderOf x = n := (orderOf_eq_card_of_zpowers_eq_top hx).trans hcard
  have hsize : Nat.card (Subgroup.zpowers (x ^ (n / d))) = d := by
    rw [Nat.card_zpowers, ← zpow_natCast]
    rw [D07.Ch02.OrderOfPower.finite_order_of_power G x n hn horder]
    rw [Int.natAbs_natCast, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
      Nat.div_div_self hdvd hn.ne']
  refine ⟨hsize, fun H => ?_⟩
  rw [IsCyclic.subgroup_eq_iff_card_eq, hsize]

theorem power_generates_iff (G : Type u) [Group G] (x : G) (n : ℕ)
    (hx : Subgroup.zpowers x = ⊤) (_hn : 0 < n) (hcard : Nat.card G = n)
    (k : ℤ) :
    Subgroup.zpowers (x ^ k) = ⊤ ↔ Nat.gcd k.natAbs n = 1 := by
  have horder : orderOf x = n := (orderOf_eq_card_of_zpowers_eq_top hx).trans hcard
  simpa only [zpow_one, hx, horder, Int.gcd, Int.natAbs_natCast, Int.natAbs_one,
    Nat.gcd_one_left] using (Subgroup.zpowers_eq_zpowers_iff' x k 1)

theorem generator_count (G : Type u) [Group G] (x : G) (n : ℕ)
    (hx : Subgroup.zpowers x = ⊤) (hn : 0 < n) (hcard : Nat.card G = n) :
    Nat.card {y : G // Subgroup.zpowers y = ⊤} = Nat.totient n := by
  classical
  let : Finite G := Nat.finite_of_card_ne_zero (hcard.trans_ne hn.ne')
  let : Fintype G := Fintype.ofFinite G
  let : IsCyclic G :=
    (D07.Ch02.CyclicDefinition.cyclic_iff_cyclic_subgroup_eq_top G).mpr ⟨x, hx⟩
  have hgen : ∀ y : G, Subgroup.zpowers y = ⊤ ↔ orderOf y = n := by
    intro y
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hcard]
  have hcount := IsCyclic.card_orderOf_eq_totient (α := G)
    (d := n) (show n ∣ Fintype.card G by rw [← Nat.card_eq_fintype_card, hcard])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hgen] using hcount

end D07.Ch02.FiniteCyclicSubgroupClassification
