import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.FerrersConjugation

namespace FiniteCombinatorics.Partition

/-- The Ferrers cells in the one-based coordinates of W27. -/
abbrev ferrersDiagram : Specs.FerrersDiagramType := Specs.FerrersDiagramValue

/-- Number of positive parts, with value zero on the empty list. -/
abbrev numberOfParts : Specs.PartitionStatisticType := Specs.NumberOfPartsValue

/-- The largest part, with value zero on the empty list. -/
abbrev largestPart : Specs.PartitionStatisticType := Specs.LargestPartValue

/-- Read the rows after transposing the Ferrers diagram. Its type preserves weight. -/
abbrev conjugate : Specs.ConjugateType := Specs.ConjugateValue

private theorem rowLens_youngDiagram {n : ℕ} (p : Partition n) :
    (Specs.youngDiagram p).rowLens = p.val :=
  YoungDiagram.rowLens_ofRowLens_eq_self p.property.2.1

private theorem youngDiagram_conjugate {n : ℕ} (p : Partition n) :
    Specs.youngDiagram (conjugate p) = (Specs.youngDiagram p).transpose :=
  YoungDiagram.ofRowLens_to_rowLens_eq_self

private theorem ferrers_succ {n : ℕ} (p : Partition n) (i j : ℕ) :
    (i + 1, j + 1) ∈ ferrersDiagram p ↔ (i, j) ∈ Specs.youngDiagram p := by
  simp only [ferrersDiagram, Specs.FerrersDiagramValue, Set.mem_ofPred_eq,
    Nat.add_sub_cancel, Specs.youngDiagram, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨_, hi, _, hj⟩
    have h : i < p.val.length := by omega
    refine ⟨h, ?_⟩
    simpa only [List.getElem?_eq_getElem h, Option.getD_some, Nat.add_one_le_iff] using hj
  · rintro ⟨hi, hj⟩
    refine ⟨by omega, by omega, by omega, ?_⟩
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some, Nat.add_one_le_iff] using hj

theorem ferrers_transpose : Specs.FerrersTranspose := by
  intro n p i j
  cases i with
  | zero => simp [Specs.FerrersDiagramValue]
  | succ i =>
    cases j with
    | zero => simp [Specs.FerrersDiagramValue]
    | succ j =>
      rw [ferrers_succ, ferrers_succ, youngDiagram_conjugate,
        YoungDiagram.mem_transpose]
      rfl

theorem conjugate_involution : Specs.ConjugateInvolution := by
  intro n p
  apply Subtype.ext
  change (Specs.youngDiagram (conjugate p)).transpose.rowLens = p.val
  rw [youngDiagram_conjugate, YoungDiagram.transpose_transpose, rowLens_youngDiagram]

theorem conjugate_weight : Specs.ConjugateWeight := by
  intro n p
  exact (conjugate p).property.2.2.trans p.property.2.2.symm

private theorem numberOfParts_eq_colLen {n : ℕ} (p : Partition n) :
    numberOfParts p = (Specs.youngDiagram p).colLen 0 := by
  rw [← YoungDiagram.length_rowLens, rowLens_youngDiagram]
  rfl

private theorem rowLen_zero_eq_largestPart {n : ℕ} (p : Partition n) :
    (Specs.youngDiagram p).rowLen 0 = largestPart p := by
  cases h : p.val with
  | nil =>
    have hz : largestPart p = 0 := by simp [largestPart, Specs.LargestPartValue, h]
    rw [hz]
    apply Nat.eq_zero_of_not_pos
    intro hr
    have hm : (0, 0) ∈ Specs.youngDiagram p := YoungDiagram.mem_iff_lt_rowLen.mpr hr
    rw [Specs.youngDiagram, YoungDiagram.mem_ofRowLens] at hm
    simp [h] at hm
  | cons a l =>
    have hh : 0 < p.val.length := by simp [h]
    simpa [Specs.youngDiagram, largestPart, Specs.LargestPartValue, h] using
      (YoungDiagram.rowLen_ofRowLens (hw := p.property.1.sortedGE) ⟨0, hh⟩)

theorem conjugate_statistics : Specs.ConjugateStatistics := by
  intro n p
  constructor
  · change numberOfParts (conjugate p) = largestPart p
    rw [numberOfParts_eq_colLen, youngDiagram_conjugate,
      YoungDiagram.colLen_transpose, rowLen_zero_eq_largestPart]
  · change largestPart (conjugate p) = numberOfParts p
    rw [← rowLen_zero_eq_largestPart, youngDiagram_conjugate,
      YoungDiagram.rowLen_transpose, ← numberOfParts_eq_colLen]

theorem empty_statistics : Specs.EmptyStatistics := by
  intro p
  have hp := zero_partition.2.1 p
  simp [Specs.NumberOfPartsValue, Specs.LargestPartValue, hp]

theorem conjugate_bounds : Specs.ConjugateBounds := by
  intro n p a b
  rw [(conjugate_statistics n p).1, (conjugate_statistics n p).2]
  exact and_comm

end FiniteCombinatorics.Partition
