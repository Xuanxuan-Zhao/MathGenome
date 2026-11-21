import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.MultiplicativeCyclicity
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.TotientClassicalCongruences
import MathGenome.Internal.D07.Ch13.MultiplicativeCyclic

/-! Cyclicity and generator counts in Theorem 2.3, paper.tex:447–508.
MathGenome's results use the actual units and inherited subgroup operations.
Its generator predicate is equality of the integer-power subgroup with top,
exactly as in our independent statements. The totient bridge is Theorem 2.1.
-/

namespace P203.Ch02

open P203Specs.Ch02
universe u

theorem finiteMultiplicativeSubgroupCyclic : FiniteMultiplicativeSubgroupCyclic.{u} :=
  D07.Ch13.MultiplicativeCyclic.finite_multiplicative_subgroup_is_cyclic

theorem cyclicGeneratorCount : CyclicGeneratorCount.{u} := by
  intro G _ _ _ d hd hcard
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  rw [totient_eq_natTotient d hd]
  exact D07.Ch02.FiniteCyclicSubgroupClassification.generator_count G g d hg hd hcard

theorem orderOfNaturalPower : OrderOfNaturalPower.{u} := by
  intro G _ g d hd horder j
  have hg : IsOfFinOrder g := orderOf_pos_iff.mp (horder.symm ▸ hd)
  simpa only [horder] using hg.orderOf_pow g j

theorem orderOfIntegerPower : OrderOfIntegerPower.{u} := by
  intro G _ g d hd horder j
  exact D07.Ch02.OrderOfPower.finite_order_of_power G g d hd horder j

theorem powerGeneratorCriterion : PowerGeneratorCriterion.{u} := by
  intro G _ _ g d hg hd hcard j
  simpa only [Nat.gcd_comm] using
    D07.Ch02.FiniteCyclicSubgroupClassification.power_generates_iff G g d hg hd hcard j

theorem finiteFieldMultiplicativeGroup : FiniteFieldMultiplicativeGroup.{u} := by
  intro K _ _ q hq
  obtain ⟨hcyclic, hcard, hcount⟩ :=
    D07.Ch13.MultiplicativeCyclic.finite_field_units K q hq
  refine ⟨hcyclic, hcard, ?_⟩
  have hd : 0 < q - 1 := hcard ▸ (Nat.card_pos (α := Kˣ))
  rw [totient_eq_natTotient (q - 1) hd]
  exact hcount

end P203.Ch02
