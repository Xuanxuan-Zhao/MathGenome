import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GreedyBasis
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Models
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyBasis

/-! Greedy bases for finite canonical matroids, with arbitrary real weights.
The arbitrary-list interface is related to MathGenome's total-tie-order interface
by ordering elements according to their positions in the supplied list. -/
namespace P205.Matroids
noncomputable section
universe u

/-- Add the scanned element exactly when its insertion preserves independence. -/
def greedyStep : Specs.P205.Matroids.greedyStepType.{u} :=
  @Specs.P205.Matroids.greedyStepValue.{u}

/-- Scan the first `i` elements, starting with the empty set. -/
def greedyState : Specs.P205.Matroids.greedyStateType.{u} :=
  @Specs.P205.Matroids.greedyStateValue.{u}

/-- Scan every element, including those of negative weight. -/
def greedyOutput : Specs.P205.Matroids.greedyOutputType.{u} :=
  @Specs.P205.Matroids.greedyOutputValue.{u}

/-- The set of elements appearing in the first `i` positions. -/
def greedyPrefix : Specs.P205.Matroids.greedyPrefixType.{u} :=
  @Specs.P205.Matroids.greedyPrefixValue.{u}

/-- An exhaustive nonincreasing ordering, with arbitrary ordering of tied weights. -/
def GreedyOrdering : Specs.P205.Matroids.GreedyOrderingType.{u} :=
  @Specs.P205.Matroids.GreedyOrderingValue.{u}

/-- Every supplied exhaustive nonincreasing list is exactly a MathGenome greedy
 enumeration for a suitable total tie order. This also handles empty ground. -/
theorem exists_greedy_tie {α : Type u} (M : Matroid α) [M.Finite]
    (w : Coordinates M) (l : List M.E) (hl : GreedyOrdering M w l) :
    ∃ tie : LinearOrder M.E,
      FiniteCombinatorics.Matroid.greedyEnumeration
        (FiniteCombinatorics.Matroid.fromMatroid M) w tie = l := by
  classical
  let := M.ground_finite.fintype
  rcases hl with ⟨hn, hall, hs⟩
  let tie : LinearOrder M.E := LinearOrder.lift' (fun e => l.idxOf e)
    (fun a b h => (List.idxOf_inj (hall a)).1 h)
  refine ⟨tie, ?_⟩
  have hpair : l.Pairwise (FiniteCombinatorics.Matroid.WeightTieBefore w tie) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hw := (List.pairwise_iff_getElem.mp hs) i j hi hj hij
    rcases hw.lt_or_eq with hw | hw
    · exact Or.inl hw
    · apply Or.inr
      refine ⟨hw.symm, ?_⟩
      change l.idxOf l[i] ≤ l.idxOf l[j]
      simpa only [hn.idxOf_getElem] using hij.le
  unfold FiniteCombinatorics.Matroid.greedyEnumeration
  have huniv : l.toFinset = Finset.univ := by
    ext e
    simp [hall e]
  rw [← huniv]
  exact (List.toFinset_sort _ hn).2 hpair

/-- The selected elements after a prefix form a basis of that prefix. -/
theorem greedy_prefix_basis : Specs.P205.Matroids.GreedyPrefixBasis := by
  intro α M _ w l hl i
  obtain ⟨tie, ht⟩ := exists_greedy_tie M w l hl
  have h := FiniteCombinatorics.Matroid.greedyPrefix_isBasis M w tie i
  change M.IsBasis
    (greedyState M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie) i)
    (greedyPrefix M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie) i) at h
  rw [ht] at h
  exact h

/-- Intersecting the final output with a prefix recovers its selected state. -/
theorem greedy_output_inter_prefix : Specs.P205.Matroids.GreedyOutputInterPrefix := by
  intro α M _ w l hl i
  obtain ⟨tie, ht⟩ := exists_greedy_tie M w l hl
  have h := FiniteCombinatorics.Matroid.greedyOutput_inter_prefix
    (FiniteCombinatorics.Matroid.fromMatroid M) w tie i
  change greedyOutput M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie) ∩
    greedyPrefix M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie) i =
    greedyState M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie) i at h
  rw [ht] at h
  exact h

/-- The output simultaneously attains the project's natural rank on every prefix. -/
theorem greedy_prefix_rank : Specs.P205.Matroids.GreedyPrefixRank := by
  intro α M _ w l hl i
  rw [greedy_output_inter_prefix M w l hl i]
  have hP : greedyPrefix M l i ⊆ M.E := by
    rintro x ⟨e, _, rfl⟩
    exact e.property
  exact ((basis_rank M _ _ hP).1 (greedy_prefix_basis M w l hl i)).2.2

/-- Maximum-weight basis for every exhaustive nonincreasing order and real weights. -/
theorem greedy_basis_optimal : Specs.P205.Matroids.GreedyBasisOptimal := by
  intro α M _ w l hl
  obtain ⟨tie, ht⟩ := exists_greedy_tie M w l hl
  have h := FiniteCombinatorics.Matroid.greedyBasisOptimal M w tie
  change M.IsBase (greedyOutput M (FiniteCombinatorics.Matroid.greedyEnumeration
      (FiniteCombinatorics.Matroid.fromMatroid M) w tie)) ∧
    ∀ B : Set α, M.IsBase B → subsetSum M w B ≤
      subsetSum M w (greedyOutput M (FiniteCombinatorics.Matroid.greedyEnumeration
        (FiniteCombinatorics.Matroid.fromMatroid M) w tie)) at h
  rw [ht] at h
  exact h

end
end P205.Matroids
