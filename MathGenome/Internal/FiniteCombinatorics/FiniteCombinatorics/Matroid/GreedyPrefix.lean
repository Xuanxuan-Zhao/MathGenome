import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyDefinition
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyPrefix

/-! Prefix invariants for weighted greedy selection (paper.tex:3313–3331).
Heredity alone gives maximality. Independence of the final output then forces
its intersection with a prefix to be the state at that prefix. Augmentation
is used only to identify the resulting cardinalities with matroid rank. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α}

/-- A greedy step preserves maximality in the enlarged scanned set. -/
theorem greedyStep_basisIn (S : IndependenceSystem E) {A I : Set α}
    (hI : BasisIn S A I) (e : E) :
    BasisIn S (insert (e : α) A) (greedyStep S I e) := by
  classical
  have hmax : ∀ J, J ⊆ insert (e : α) A → S.Indep J → I ⊆ J → J ∩ A = I := by
    intro J _ hJ hIJ
    exact hI.2.2 (J ∩ A) inter_subset_right
      (S.hereditary hJ inter_subset_left) (subset_inter hIJ hI.1)
  by_cases h : S.Indep (insert (e : α) I)
  · rw [greedyStep_accept S I e h]
    refine ⟨insert_subset_insert hI.1, h, ?_⟩
    intro J hJA hJ hIJ
    have heq := hmax J hJA hJ ((subset_insert _ _).trans hIJ)
    apply Subset.antisymm ?_ hIJ
    intro x hx
    rcases hJA hx with he | hxA
    · exact Or.inl he
    · exact Or.inr (heq ▸ (show x ∈ J ∩ A from ⟨hx, hxA⟩))
  · rw [greedyStep_reject S I e h]
    refine ⟨hI.1.trans (subset_insert _ _), hI.2.1, ?_⟩
    intro J hJA hJ hIJ
    have heJ : (e : α) ∉ J := fun he =>
      h (S.hereditary hJ (insert_subset he hIJ))
    apply hI.2.2 J ?_ hJ hIJ
    intro x hx
    rcases hJA hx with he | hxA
    · exact (heJ (he ▸ hx)).elim
    · exact hxA

private def scannedSet (l : List E) : Set α :=
  {x | ∃ e ∈ l, (e : α) = x}

private theorem scannedSet_append (l k : List E) :
    scannedSet (l ++ k) = scannedSet l ∪ scannedSet k := by
  ext x
  simp only [scannedSet, mem_ofPred_eq, List.mem_append, mem_union]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

private theorem greedyFold_basisIn (S : IndependenceSystem E) (l : List E) :
    BasisIn S (scannedSet l) (l.foldl (greedyStep S) ∅) := by
  induction l using List.reverseRecOn with
  | nil =>
    have h : scannedSet ([] : List E) = ∅ := by ext x; simp [scannedSet]
    rw [h, List.foldl_nil]
    exact ⟨Subset.rfl, S.empty_indep,
      fun J hJ _ _ => Set.subset_empty_iff.mp hJ⟩
  | append_singleton l e ih =>
    have h : scannedSet (l ++ [e]) = insert (e : α) (scannedSet l) := by
      rw [scannedSet_append]
      ext x
      simp [scannedSet, eq_comm, or_comm]
    rw [h, List.foldl_append]
    exact greedyStep_basisIn S ih e

/-- Greedy never removes a selected element. -/
theorem greedyStep_extensive (S : IndependenceSystem E) (I : Set α) (e : E) :
    I ⊆ greedyStep S I e := by
  classical
  unfold greedyStep
  split_ifs
  · exact subset_insert _ _
  · exact Subset.rfl

private theorem greedyFold_extensive (S : IndependenceSystem E) (l : List E)
    (I : Set α) : I ⊆ l.foldl (greedyStep S) I := by
  induction l generalizing I with
  | nil => exact Subset.rfl
  | cons e l ih =>
    exact (greedyStep_extensive S I e).trans (ih (greedyStep S I e))

theorem greedyPrefix_basisIn (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) :
    BasisIn S (greedyPrefix S w tie i) (greedyState S w tie i) :=
  greedyFold_basisIn S ((greedyEnumeration S w tie).take i)

theorem greedyState_subset_output (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) :
    greedyState S w tie i ⊆ greedyOutput S w tie := by
  have h := greedyFold_extensive S ((greedyEnumeration S w tie).drop i)
    (greedyState S w tie i)
  simpa only [greedyOutput, greedyState, List.take_length, ← List.foldl_append,
    List.take_append_drop] using h

theorem greedyOutput_maximal (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) : MaximalIndependent S (greedyOutput S w tie) := by
  have h := greedyPrefix_basisIn S w tie (greedyEnumeration S w tie).length
  rw [greedyPrefix_full] at h
  exact h

theorem greedyOutput_inter_prefix (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) :
    greedyOutput S w tie ∩ greedyPrefix S w tie i = greedyState S w tie i := by
  have h := greedyPrefix_basisIn S w tie i
  exact h.2.2 _ inter_subset_right
    (S.hereditary (greedyOutput_maximal S w tie).2.1 inter_subset_left)
    (subset_inter (greedyState_subset_output S w tie i) h.1)

private theorem greedyPrefix_subset_ground (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (i : ℕ) : greedyPrefix S w tie i ⊆ E := by
  rintro x ⟨e, _, rfl⟩
  exact e.property

private theorem basisIn_fromMatroid {M : _root_.Matroid α} [M.Finite]
    {A I : Set α} (hA : A ⊆ M.E) (h : BasisIn (fromMatroid M) A I) :
    M.IsBasis I A := by
  rw [_root_.Matroid.isBasis_iff hA]
  exact ⟨h.2.1, h.1, fun J hJ hIJ hJA => (h.2.2 J hJA hJ hIJ).symm⟩

theorem greedyPrefix_isBasis (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) (i : ℕ) :
    M.IsBasis (greedyState (fromMatroid M) w tie i)
      (greedyPrefix (fromMatroid M) w tie i) :=
  basisIn_fromMatroid (greedyPrefix_subset_ground _ _ _ _)
    (greedyPrefix_basisIn _ _ _ _)

theorem greedyPrefix_cardinality (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) (i : ℕ) :
    (greedyOutput (fromMatroid M) w tie ∩
      greedyPrefix (fromMatroid M) w tie i).ncard =
      (greedyState (fromMatroid M) w tie i).ncard ∧
    ((greedyState (fromMatroid M) w tie i).ncard : ℤ) =
      rank M (greedyPrefix (fromMatroid M) w tie i) := by
  exact ⟨congrArg Set.ncard (greedyOutput_inter_prefix _ _ _ _),
    basisCardinality M _ _ (greedyPrefix_isBasis M w tie i)⟩

theorem greedyOutput_isBase (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) :
    M.IsBase (greedyOutput (fromMatroid M) w tie) := by
  rw [← _root_.Matroid.isBasis_ground_iff]
  exact basisIn_fromMatroid Subset.rfl (greedyOutput_maximal _ _ _)

theorem greedyPrefix_augmented_cardinality (S : IndependenceSystem E) (h : Augmentation S)
    (w : E → ℝ) (tie : LinearOrder E) (i : ℕ) :
    (greedyOutput S w tie ∩ greedyPrefix S w tie i).ncard =
      (greedyState S w tie i).ncard ∧
    ((greedyState S w tie i).ncard : ℤ) =
      rank (ofAugmentation S h) (greedyPrefix S w tie i) := by
  refine ⟨congrArg Set.ncard (greedyOutput_inter_prefix _ _ _ _), ?_⟩
  apply basisCardinality
  exact (basisPreserved E S h _ _ (greedyPrefix_subset_ground _ _ _ _)).mpr
    (greedyPrefix_basisIn S w tie i)

theorem greedyOutput_augmented_isBase (S : IndependenceSystem E) (h : Augmentation S)
    (w : E → ℝ) (tie : LinearOrder E) :
    (ofAugmentation S h).IsBase (greedyOutput S w tie) :=
  (basePreserved E S h _).mpr (greedyOutput_maximal S w tie)

end FiniteCombinatorics.Matroid
