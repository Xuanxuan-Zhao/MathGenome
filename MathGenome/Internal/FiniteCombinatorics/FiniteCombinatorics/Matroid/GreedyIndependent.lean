import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyBasis
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyIndependent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Independent-set optimization in paper.tex W79. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α}

/-- Enlarging a set cannot decrease its weight when all weights are nonnegative. -/
theorem subsetWeight_mono (S : IndependenceSystem E) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) {I J : Set α} (hIJ : I ⊆ J) :
    subsetWeight S w I ≤ subsetWeight S w J := by
  classical
  let := S.finite_ground.fintype
  unfold subsetWeight
  apply Finset.sum_le_sum
  intro e _
  by_cases he : (e : α) ∈ I
  · simp [he, hIJ he]
  · simp only [ite_eq_right he]
    split_ifs <;> simp [hw]

/-- Nonnegative weights allow extension to a basis without loss. -/
theorem greedyIndependentOptimal (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) (hw : ∀ e, 0 ≤ w e) :
    IndependentOptimal (fromMatroid M) w (greedyOutput (fromMatroid M) w tie) := by
  obtain ⟨hG, hopt⟩ := greedyBasisOptimal M w tie
  refine ⟨hG.indep, ?_⟩
  intro I hI
  obtain ⟨B, hB, hIB⟩ := basisExtension M I M.E hI hI.subset_ground Subset.rfl
  exact (subsetWeight_mono (fromMatroid M) w hw hIB).trans
    (hopt B (_root_.Matroid.isBasis_ground_iff.mp hB))

/-- The retained ground is a subset of the original ground. -/
theorem nonnegativeGround_subset (w : E → ℝ) : nonnegativeGround w ⊆ E :=
  fun _ h => h.choose

/-- Restricting a matroid to its nonnegative elements preserves augmentation. -/
theorem nonnegativeRestriction_augmentation (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) : Augmentation (nonnegativeRestriction (fromMatroid M) w) := by
  intro I J hI hJ hcard
  have hlt : I.encard < J.encard := by
    rw [← (M.ground_finite.subset hI.1.subset_ground).cast_ncard_eq,
      ← (M.ground_finite.subset hJ.1.subset_ground).cast_ncard_eq]
    exact_mod_cast hcard
  obtain ⟨e, he, hIe⟩ := hI.1.augment hJ.1 hlt
  exact ⟨e, he, hIe, insert_subset (hJ.2 he.1) hI.2⟩

/-- Summing unchanged weights on a retained set gives the same number on either
side of the restriction. -/
theorem subsetWeight_nonnegativeRestriction (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) (hI : I ⊆ nonnegativeGround w) :
    subsetWeight (nonnegativeRestriction S w) (nonnegativeWeight w) I =
      subsetWeight S w I := by
  classical
  let := S.finite_ground.fintype
  let := (nonnegativeRestriction S w).finite_ground.fintype
  let f : nonnegativeGround w → E := fun e => ⟨e.val, e.property.choose⟩
  unfold subsetWeight
  apply Fintype.sum_of_injective f
    (fun a b h => Subtype.ext (congrArg (fun x : E => (x : α)) h))
  · intro e he
    have hn : (e : α) ∉ I := by
      intro hi
      exact he ⟨⟨e.val, hI hi⟩, rfl⟩
    simp [hn]
  · intro e
    rfl

/-- Removing negative-weight elements improves the weight of every subset. -/
theorem subsetWeight_inter_nonnegative (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) : subsetWeight S w I ≤ subsetWeight S w (I ∩ nonnegativeGround w) := by
  classical
  let := S.finite_ground.fintype
  unfold subsetWeight
  apply Finset.sum_le_sum
  intro e _
  by_cases he : (e : α) ∈ I
  · by_cases hn : (e : α) ∈ nonnegativeGround w
    · simp [he, hn]
    · have hw : w e ≤ 0 := le_of_lt (lt_of_not_ge (fun hw => hn ⟨e.property, hw⟩))
      simpa [he, hn] using hw
  · simp [he]

/-- Arbitrary real weights: delete all negative elements, then run the original
greedy algorithm with the inherited tie order. -/
theorem nonnegativeGreedyIndependentOptimal (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) :
    IndependentOptimal (fromMatroid M) w
      (nonnegativeGreedyOutput (fromMatroid M) w tie) := by
  let S := nonnegativeRestriction (fromMatroid M) w
  let h := nonnegativeRestriction_augmentation M w
  let N := ofAugmentation S h
  have hw : ∀ e, 0 ≤ nonnegativeWeight w e := fun e => e.property.choose_spec
  have hopt : IndependentOptimal S (nonnegativeWeight w)
      (greedyOutput S (nonnegativeWeight w) (nonnegativeTie w tie)) :=
    greedyIndependentOptimal N (nonnegativeWeight w) (nonnegativeTie w tie) hw
  obtain ⟨hG, hbest⟩ := hopt
  refine ⟨hG.1, ?_⟩
  intro I hI
  have hret : S.Indep (I ∩ nonnegativeGround w) :=
    ⟨hI.subset inter_subset_left, inter_subset_right⟩
  have hc := hbest _ hret
  dsimp only [S] at hc
  rw [subsetWeight_nonnegativeRestriction (fromMatroid M) w
      (I ∩ nonnegativeGround w) inter_subset_right,
    subsetWeight_nonnegativeRestriction (fromMatroid M) w _ hG.2] at hc
  exact (subsetWeight_inter_nonnegative (fromMatroid M) w I).trans hc

/-- A single coloop of weight -1 distinguishes basis optimization from
optimization over all independent sets. -/
theorem negativeColoopExample :
    let M : _root_.Matroid Unit := _root_.Matroid.freeOn univ
    let w : M.E → ℝ := fun _ => -1
    M.IsColoop () ∧
      (∀ B, M.IsBase B ↔ B = univ) ∧
      (∀ B, M.IsBase B → subsetWeight (fromMatroid M) w B = -1) ∧
      IndependentOptimal (fromMatroid M) w ∅ ∧
      subsetWeight (fromMatroid M) w ∅ = 0 ∧
      ∀ tie : LinearOrder M.E,
        greedyOutput (fromMatroid M) w tie = univ ∧
        nonnegativeGreedyOutput (fromMatroid M) w tie = ∅ := by
  classical
  let M : _root_.Matroid Unit := _root_.Matroid.freeOn univ
  let w : M.E → ℝ := fun _ => -1
  change M.IsColoop () ∧ _
  have hb : ∀ B, M.IsBase B ↔ B = univ := fun _ => _root_.Matroid.freeOn_isBase_iff
  have hweight (I : Set Unit) :
      subsetWeight (fromMatroid M) w I = if () ∈ I then -1 else 0 := by
    let := M.ground_finite.fintype
    have hf : Finset.univ (α := M.E) = {⟨(), mem_univ _⟩} := by
      ext e
      simp only [Finset.mem_univ, Finset.mem_singleton]
    unfold subsetWeight
    rw [hf, Finset.sum_singleton]
  have hnonnegative : nonnegativeGround w = ∅ := by
    ext x
    simp [nonnegativeGround, w]
  refine ⟨?_, hb, ?_, ?_, subsetWeight_empty _ _, ?_⟩
  · apply _root_.Matroid.isColoop_iff_forall_mem_isBase.mpr
    intro B hB
    simp [(hb B).mp hB]
  · intro B hB
    rw [(hb B).mp hB, hweight]
    simp
  · refine ⟨M.empty_indep, ?_⟩
    intro I _
    rw [hweight, subsetWeight_empty]
    split_ifs <;> norm_num
  · intro tie
    refine ⟨(hb _).mp (greedyBasisOptimal M w tie).1, ?_⟩
    have hsub : nonnegativeGreedyOutput (fromMatroid M) w tie ⊆ nonnegativeGround w :=
      (greedyOutput_maximal (nonnegativeRestriction (fromMatroid M) w)
        (nonnegativeWeight w) (nonnegativeTie w tie)).1
    exact subset_empty_iff.mp (hnonnegative ▸ hsub)

end FiniteCombinatorics.Matroid
