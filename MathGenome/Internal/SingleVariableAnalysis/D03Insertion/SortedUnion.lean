import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.SortedUnion
import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.FinitePartitionData
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega

/-! Construction of the sorted union from a finite ordered set. -/

noncomputable section

namespace D03Insertion

/-- Every node of a valid partition lies between its two endpoints. -/
theorem partition_node_mem_Icc {a b : ℝ} {s : ℕ}
    {p : Fin (s + 1) → ℝ} (hp : ValidPartition a b p) (i : Fin (s + 1)) :
    p i ∈ Set.Icc a b := by
  constructor
  · rw [← hp.2.2.1]
    exact hp.2.1.monotone (Fin.zero_le i)
  · rw [← hp.2.2.2]
    exact hp.2.1.monotone (Fin.le_last i)

/-- Enumerate the finite union in increasing order. Shared nodes are included
once because the enumeration is an order embedding of a finite set. -/
theorem sorted_union_partition {a b : ℝ} (_hab : a < b) {s n : ℕ}
    (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ)
    (hp : ValidPartition a b p) (hq : ValidPartition a b q) :
    ∃ (t : ℕ) (r : Fin (t + 1) → ℝ),
      ValidPartition a b r ∧ nodes r = nodes p ∪ nodes q := by
  classical
  let U := nodes p ∪ nodes q
  have hcardp : (nodes p).card = s + 1 := by
    simp [nodes, Finset.card_image_of_injective _ hp.2.1.injective]
  have hcard : 2 ≤ U.card := by
    have hle : (nodes p).card ≤ U.card :=
      Finset.card_le_card Finset.subset_union_left
    rw [hcardp] at hle
    have := hp.1
    omega
  let t := U.card - 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hsize : U.card = t + 1 := by dsimp [t]; omega
  let r : Fin (t + 1) → ℝ := U.orderEmbOfFin hsize
  have hmono : StrictMono r := (U.orderEmbOfFin hsize).strictMono
  have hnodes : nodes r = U := Finset.image_orderEmbOfFin_univ U hsize
  have hbound : ∀ x ∈ U, x ∈ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact partition_node_mem_Icc hp i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact partition_node_mem_Icc hq i
  have ha : a ∈ U := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hp.2.2.1⟩
  have hb : b ∈ U := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨Fin.last s, Finset.mem_univ _, hp.2.2.2⟩
  have hfirst : r 0 = a := by
    apply le_antisymm
    · rw [← hnodes] at ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      rw [← hi]
      exact hmono.monotone (Fin.zero_le i)
    · exact (hbound _ (Finset.orderEmbOfFin_mem U hsize 0)).1
  have hlast : r (Fin.last t) = b := by
    apply le_antisymm
    · exact (hbound _ (Finset.orderEmbOfFin_mem U hsize (Fin.last t))).2
    · rw [← hnodes] at hb
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      rw [← hi]
      exact hmono.monotone (Fin.le_last i)
  exact ⟨t, r, ⟨ht, hmono, hfirst, hlast⟩, hnodes⟩

end D03Insertion
