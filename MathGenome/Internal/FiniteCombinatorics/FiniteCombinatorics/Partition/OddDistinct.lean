import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.OddDistinct
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.Foundations
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.Fintype.EquivFin

noncomputable section

namespace FiniteCombinatorics.Partition

/-- Restrict the shared representation equivalence to odd parts. -/
def oddMathlibEquiv (n : ℕ) :
    Specs.OddPartitions n ≃ ↥(Nat.Partition.odds n) := by
  apply Equiv.subtypeEquiv (mathlibEquiv n)
  intro p
  change (∀ i ∈ p.val, Odd i) ↔ toMathlib p ∈ Nat.Partition.odds n
  simp [Nat.Partition.odds, Nat.Partition.restricted, toMathlib,
    Nat.not_even_iff_odd]

/-- Restrict the shared representation equivalence to distinct parts. -/
def distinctMathlibEquiv (n : ℕ) :
    Specs.DistinctPartitions n ≃ ↥(Nat.Partition.distincts n) := by
  apply Equiv.subtypeEquiv (mathlibEquiv n)
  intro p
  change p.val.Nodup ↔ toMathlib p ∈ Nat.Partition.distincts n
  simp [Nat.Partition.distincts, toMathlib]

/-- W26: odd-part and distinct-part partitions of every natural weight are
equinumerous. Glaisher's theorem supplies the cardinality equality, transported
through the actual restricted list partition subtypes. -/
theorem odd_distinct : Specs.OddDistinct := by
  intro n
  exact ⟨(oddMathlibEquiv n).trans
    ((Finset.equivOfCardEq (Nat.Partition.card_odds_eq_card_distincts n)).trans
      (distinctMathlibEquiv n).symm)⟩

end FiniteCombinatorics.Partition
