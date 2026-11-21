import MathGenome.Internal.ExtremalOptimization.P205.Matroids.MaximumAssignableSize
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Union
import Mathlib.Combinatorics.Matroid.IndepAxioms

namespace P205.Matroids
open Set
open scoped BigOperators
noncomputable section
universe u

/-- Deleting elements from each part preserves assignability. -/
theorem assignable_subset {α : Type u} {k : ℕ} (F : Family α k)
    {I J : Set α} (hJ : Assignable F J) (hIJ : I ⊆ J) : Assignable F I := by
  obtain ⟨parts, hind, hparts⟩ := hJ
  refine ⟨fun i => I ∩ parts i, fun i => (hind i).subset inter_subset_right, ?_⟩
  rw [← inter_iUnion, ← hparts, inter_eq_self_of_subset_left hIJ]

/-- Monotonicity follows from the independently defined finite maximum. -/
theorem q_mono {α : Type u} {k : ℕ} (F : Family α k)
    {S T : Set α} (h : S ⊆ T) : q F S ≤ q F T := by
  obtain ⟨I, hIS, ha, hcard⟩ := (q_maximum F S).1
  change I.ncard = q F S at hcard
  rw [← hcard]
  exact (q_maximum F T).2 I (hIS.trans h) ha

theorem q_le_ncard {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (hS : S ⊆ F.ground) : q F S ≤ S.ncard := by
  obtain ⟨I, hIS, _, hcard⟩ := (q_maximum F S).1
  change I.ncard = q F S at hcard
  rw [← hcard]
  exact ncard_le_ncard hIS (F.ground_finite.subset hS)

/-- Equality in the maximum-size bound characterizes assignability. -/
theorem assignable_iff_q_eq {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (hS : S ⊆ F.ground) : Assignable F S ↔ q F S = S.ncard := by
  constructor
  · intro ha
    exact Nat.le_antisymm (q_le_ncard F S hS) ((q_maximum F S).2 S Subset.rfl ha)
  · intro hq
    obtain ⟨I, hIS, ha, hcard⟩ := (q_maximum F S).1
    change I.ncard = q F S at hcard
    have heq : I = S := eq_of_subset_of_ncard_le hIS (by omega) (F.ground_finite.subset hS)
    rwa [← heq]

/-- Finite canonical rank submodularity, transported from ENat without truncation. -/
theorem rank_submodular {α : Type u} (M : Matroid α) [M.Finite]
    (S T : Set α) : rank M (S ∪ T) + rank M (S ∩ T) ≤ rank M S + rank M T := by
  have h := M.eRk_submod S T
  rw [← rank_natCast M (S ∩ T), ← rank_natCast M (S ∪ T),
    ← rank_natCast M S, ← rank_natCast M T, ← Nat.cast_add, ← Nat.cast_add] at h
  exact_mod_cast (show (rank M (S ∪ T) : ℕ∞) + rank M (S ∩ T) ≤
    rank M S + rank M T by simpa [add_comm] using h)

/-- The four difference-cardinalities satisfy the uncrossing identity. -/
private theorem difference_card_identity {α : Type u} {S₁ S₂ T₁ T₂ : Set α}
    (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) (hT₁ : T₁ ⊆ S₁) (hT₂ : T₂ ⊆ S₂) :
    (S₁ \ T₁).ncard + (S₂ \ T₂).ncard =
      ((S₁ ∪ S₂) \ (T₁ ∪ T₂)).ncard + ((S₁ ∩ S₂) \ (T₁ ∩ T₂)).ncard := by
  have h₁ := ncard_sdiff_add_ncard_of_subset hT₁ hS₁
  have h₂ := ncard_sdiff_add_ncard_of_subset hT₂ hS₂
  have hu := ncard_sdiff_add_ncard_of_subset (union_subset_union hT₁ hT₂) (hS₁.union hS₂)
  have hi := ncard_sdiff_add_ncard_of_subset (inter_subset_inter hT₁ hT₂) (hS₁.subset inter_subset_left)
  have hs := ncard_union_add_ncard_inter S₁ S₂ hS₁ hS₂
  have ht := ncard_union_add_ncard_inter T₁ T₂ (hS₁.subset hT₁) (hS₂.subset hT₂)
  omega

/-- Uncrossing minimizing sets gives submodularity before the matroid exists. -/
theorem q_submodular : Specs.P205.Matroids.QSubmodular := by
  intro α k F S₁ S₂ hS₁ hS₂
  obtain ⟨T₁, hT₁, heq₁⟩ := (maximum_assignable_min F S₁ hS₁).1
  obtain ⟨T₂, hT₂, heq₂⟩ := (maximum_assignable_min F S₂ hS₂).1
  have hu := (maximum_assignable_min F (S₁ ∪ S₂) (union_subset hS₁ hS₂)).2
    (T₁ ∪ T₂) (union_subset_union hT₁ hT₂)
  have hi := (maximum_assignable_min F (S₁ ∩ S₂) (inter_subset_left.trans hS₁)).2
    (T₁ ∩ T₂) (inter_subset_inter hT₁ hT₂)
  have hc := difference_card_identity (F.ground_finite.subset hS₁)
    (F.ground_finite.subset hS₂) hT₁ hT₂
  have hr : (∑ i, rank (F.matroid i) (T₁ ∪ T₂)) +
      (∑ i, rank (F.matroid i) (T₁ ∩ T₂)) ≤
      (∑ i, rank (F.matroid i) T₁) + (∑ i, rank (F.matroid i) T₂) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => rank_submodular (F.matroid i) T₁ T₂
  change q F (S₁ ∪ S₂) + q F (S₁ ∩ S₂) ≤ q F S₁ + q F S₂
  change q F S₁ = (S₁ \ T₁).ncard + ∑ i, rank (F.matroid i) T₁ at heq₁
  change q F S₂ = (S₂ \ T₂).ncard + ∑ i, rank (F.matroid i) T₂ at heq₂
  change q F (S₁ ∪ S₂) ≤ ((S₁ ∪ S₂) \ (T₁ ∪ T₂)).ncard +
    ∑ i, rank (F.matroid i) (T₁ ∪ T₂) at hu
  change q F (S₁ ∩ S₂) ≤ ((S₁ ∩ S₂) \ (T₁ ∩ T₂)).ncard +
    ∑ i, rank (F.matroid i) (T₁ ∩ T₂) at hi
  omega

/-- Failure to add an element to an assignable set makes its q increment zero. -/
private theorem q_insert_eq_of_not_assignable {α : Type u} {k : ℕ} (F : Family α k)
    {I : Set α} (hI : Assignable F I) {e : α} (he : e ∈ F.ground) (heI : e ∉ I)
    (hn : ¬ Assignable F (insert e I)) : q F (insert e I) = q F I := by
  have hIg := assignable_ground F I hI
  have hIf := F.ground_finite.subset hIg
  have hcard := (assignable_iff_q_eq F I hIg).mp hI
  have hinsg : insert e I ⊆ F.ground := insert_subset he hIg
  have hle := q_le_ncard F (insert e I) hinsg
  have hlower := q_mono F (subset_insert e I)
  have hne : q F (insert e I) ≠ (insert e I).ncard :=
    fun h => hn ((assignable_iff_q_eq F (insert e I) hinsg).mpr h)
  rw [ncard_insert_of_notMem heI hIf] at hle hne
  omega

/-- Zero single-element increments over I remain zero after taking their union. -/
private theorem q_union_eq_of_insert_eq {α : Type u} {k : ℕ} (F : Family α k)
    (I : Set α) (hI : I ⊆ F.ground) (K : Set α) (hK : K.Finite)
    (hKg : K ⊆ F.ground) (hzero : ∀ e ∈ K, q F (insert e I) = q F I) :
    q F (I ∪ K) = q F I := by
  classical
  induction K, hK using Set.Finite.induction_on with
  | empty => simp
  | @insert e K heK hK ih =>
    have hKg' : K ⊆ F.ground := (subset_insert e K).trans hKg
    have hzero' : ∀ f ∈ K, q F (insert f I) = q F I :=
      fun f hf => hzero f (mem_insert_of_mem e hf)
    have hprev := ih hKg' hzero'
    have hsingle := hzero e (mem_insert e K)
    by_cases he : e ∈ I ∪ K
    · rw [union_insert, insert_eq_of_mem he]
      exact hprev
    · have hunion : (I ∪ K) ∪ insert e I = insert e (I ∪ K) := by
        ext x; simp only [mem_union, mem_insert_iff]; tauto
      have hinter : (I ∪ K) ∩ insert e I = I := by
        ext x
        constructor
        · rintro ⟨hx, hxe | hxI⟩
          · subst x
            exact False.elim (he hx)
          · exact hxI
        · intro hx
          exact ⟨Or.inl hx, mem_insert_of_mem e hx⟩
      have hs := q_submodular F (I ∪ K) (insert e I) (union_subset hI hKg')
        (insert_subset (hKg (mem_insert e K)) hI)
      change q F ((I ∪ K) ∪ insert e I) + q F ((I ∪ K) ∩ insert e I) ≤
        q F (I ∪ K) + q F (insert e I) at hs
      rw [hunion, hinter, hsingle, hprev] at hs
      have hl := q_mono F (show I ⊆ insert e (I ∪ K) from
        subset_union_left.trans (subset_insert _ _))
      rw [union_insert]
      omega

/-- Submodularity and the maximum-size characterization give augmentation. -/
theorem assignable_augmentation : Specs.P205.Matroids.AssignableAugmentation := by
  intro α k F I J hI hJ hlt
  classical
  by_contra! hn
  have hIg := assignable_ground F I hI
  have hJg := assignable_ground F J hJ
  have hzero : ∀ e ∈ J, q F (insert e I) = q F I := by
    intro e he
    by_cases heI : e ∈ I
    · rw [insert_eq_of_mem heI]
    · exact q_insert_eq_of_not_assignable F hI (hJg he) heI (hn e he heI)
  have heq := q_union_eq_of_insert_eq F I hIg J (F.ground_finite.subset hJg) hJg hzero
  have hle := q_mono F (show J ⊆ I ∪ J from subset_union_right)
  have hcI := (assignable_iff_q_eq F I hIg).mp hI
  have hcJ := (assignable_iff_q_eq F J hJg).mp hJ
  omega

/-- The actual finite union matroid, built only after augmentation has been proved. -/
private def unionMatroid {α : Type u} {k : ℕ} (F : Family α k) : Matroid α :=
  (IndepMatroid.ofFinite F.ground_finite (Assignable F)
    (assignable_empty F)
    (fun {_I _J} hJ hIJ => assignable_subset F hJ hIJ)
    (fun {I J} hI hJ hlt => assignable_augmentation F I J hI hJ hlt)
    (fun {I} hI => assignable_ground F I hI)).matroid

private theorem unionMatroid_ground {α : Type u} {k : ℕ} (F : Family α k) :
    (unionMatroid F).E = F.ground := rfl

private theorem unionMatroid_indep {α : Type u} {k : ℕ} (F : Family α k)
    (I : Set α) : (unionMatroid F).Indep I ↔ Assignable F I := Iff.rfl

private instance unionMatroid_finite {α : Type u} {k : ℕ} (F : Family α k) :
    (unionMatroid F).Finite := ⟨F.ground_finite⟩

/-- Canonical rank equals the independently computed maximum, by the two maxima. -/
private theorem unionMatroid_rank {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (hS : S ⊆ F.ground) : rank (unionMatroid F) S = q F S := by
  have hS' : S ⊆ (unionMatroid F).E := hS
  obtain ⟨I, hIS, hI, hcard⟩ := (rank_maximum (unionMatroid F) S hS').1
  obtain ⟨J, hJS, hJ, hcard'⟩ := (q_maximum F S).1
  change I.ncard = rank (unionMatroid F) S at hcard
  change J.ncard = q F S at hcard'
  have hl := (q_maximum F S).2 I hIS ((unionMatroid_indep F I).mp hI)
  have hr := (rank_maximum (unionMatroid F) S hS').2 J hJS
    ((unionMatroid_indep F J).mpr hJ)
  change I.ncard ≤ q F S at hl
  change J.ncard ≤ rank (unionMatroid F) S at hr
  omega

/-- Matroid union, with independence and both forms of the actual rank formula. -/
theorem union_exists : Specs.P205.Matroids.UnionExistence := by
  intro α k F
  refine ⟨unionMatroid F, unionMatroid_ground F, inferInstance, unionMatroid_indep F,
    unionMatroid_rank F, ?_⟩
  intro S hS
  have h := maximum_assignable_min F S hS
  change (∃ T, T ⊆ S ∧ rank (unionMatroid F) S =
    (S \ T).ncard + ∑ i, rank (F.matroid i) T) ∧
    (∀ T, T ⊆ S → rank (unionMatroid F) S ≤
    (S \ T).ncard + ∑ i, rank (F.matroid i) T)
  rw [unionMatroid_rank F S hS]
  exact h

/-- Full partition criterion, including empty parts and the empty family. -/
theorem partition_criterion : Specs.P205.Matroids.PartitionCriterion := by
  intro α k F S hS
  change (∃ parts : Fin k → Set α, DisjointAssignment F S S parts) ↔
    ∀ T : Set α, T ⊆ S → T.ncard ≤ ∑ i, rank (F.matroid i) T
  rw [← assignable_disjointization F S S Subset.rfl]
  constructor
  · intro ha T hT
    have haT := assignable_subset F ha hT
    have hqT := (assignable_iff_q_eq F T (hT.trans hS)).mp haT
    have hb := (maximum_assignable_min F T (hT.trans hS)).2 T Subset.rfl
    change q F T ≤ (T \ T).ncard + ∑ i, rank (F.matroid i) T at hb
    simpa only [hqT, sdiff_self, ncard_empty, zero_add] using hb
  · intro h
    apply (assignable_iff_q_eq F S hS).mpr
    obtain ⟨T, hT, hmin⟩ := (maximum_assignable_min F S hS).1
    have hb := h T hT
    have hc := ncard_sdiff_add_ncard_of_subset hT (F.ground_finite.subset hS)
    have hupper := q_le_ncard F S hS
    change q F S = (S \ T).ncard + ∑ i, rank (F.matroid i) T at hmin
    omega

/-- For zero factors the ground stays E, independence is emptiness, and rank is zero. -/
theorem union_zero : Specs.P205.Matroids.UnionZero := by
  intro α F
  obtain ⟨M, hE, hfinite, hind, hrank, _⟩ := union_exists F
  refine ⟨M, hE, hfinite, fun I => (hind I).trans (assignable_zero F I), ?_⟩
  intro S hS
  exact (hrank S hS).trans (q_zero F S)

/-- Both forms of the empty-family partition condition hold precisely at ∅. -/
theorem partition_zero : Specs.P205.Matroids.PartitionZero := by
  intro α F S hS
  have hp : (∃ parts : Fin 0 → Set α, DisjointAssignment F S S parts) ↔ S = ∅ :=
    (assignable_disjointization F S S Subset.rfl).symm.trans (assignable_zero F S)
  exact ⟨hp, (partition_criterion F S hS).symm.trans hp⟩

end
end P205.Matroids
