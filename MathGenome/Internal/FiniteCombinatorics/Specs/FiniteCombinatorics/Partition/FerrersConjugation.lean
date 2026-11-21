import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Foundations
import Mathlib.Combinatorics.Young.YoungDiagram

/-! Independent specification of W27. The public cells use the source's
one-based coordinates; Mathlib's auxiliary Young diagrams use zero-based ones. -/
namespace FiniteCombinatorics.Partition.Specs

abbrev FerrersDiagramType := {n : ℕ} → PartitionValue n → Set (ℕ × ℕ)

def FerrersDiagramValue : FerrersDiagramType := fun p =>
  {c | 1 ≤ c.1 ∧ c.1 ≤ p.val.length ∧
    1 ≤ c.2 ∧ c.2 ≤ p.val[c.1 - 1]?.getD 0}

abbrev PartitionStatisticType := {n : ℕ} → PartitionValue n → ℕ

def NumberOfPartsValue : PartitionStatisticType := fun p => p.val.length

def LargestPartValue : PartitionStatisticType := fun p => p.val.headD 0

def youngDiagram {n : ℕ} (p : PartitionValue n) : YoungDiagram :=
  YoungDiagram.ofRowLens p.val p.property.1.sortedGE

abbrev ConjugateType := {n : ℕ} → PartitionValue n → PartitionValue n

def ConjugateValue : ConjugateType := fun p =>
  ⟨(youngDiagram p).transpose.rowLens,
    (youngDiagram p).transpose.rowLens_sorted.pairwise,
    (youngDiagram p).transpose.pos_of_mem_rowLens,
    by
      rw [YoungDiagram.sum_rowLens_eq_card, YoungDiagram.card_transpose,
        ← YoungDiagram.sum_rowLens_eq_card]
      rw [youngDiagram, YoungDiagram.rowLens_ofRowLens_eq_self p.property.2.1]
      exact p.property.2.2⟩

def FerrersTranspose : Prop :=
  ∀ n (p : PartitionValue n) i j,
    (i, j) ∈ FerrersDiagramValue (ConjugateValue p) ↔
      (j, i) ∈ FerrersDiagramValue p

def ConjugateInvolution : Prop :=
  ∀ n, Function.Involutive (@ConjugateValue n)

def ConjugateWeight : Prop :=
  ∀ n (p : PartitionValue n), (ConjugateValue p).val.sum = p.val.sum

def ConjugateStatistics : Prop :=
  ∀ n (p : PartitionValue n),
    NumberOfPartsValue (ConjugateValue p) = LargestPartValue p ∧
    LargestPartValue (ConjugateValue p) = NumberOfPartsValue p

def EmptyStatistics : Prop :=
  ∀ p : PartitionValue 0, NumberOfPartsValue p = 0 ∧ LargestPartValue p = 0

def ConjugateBounds : Prop :=
  ∀ n (p : PartitionValue n) a b,
    (NumberOfPartsValue p ≤ a ∧ LargestPartValue p ≤ b) ↔
    (NumberOfPartsValue (ConjugateValue p) ≤ b ∧
      LargestPartValue (ConjugateValue p) ≤ a)

end FiniteCombinatorics.Partition.Specs
