import MathGenome.Internal.ExtremalOptimization.P205.Matroids.UnionCopies
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Intersection
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.MaximumAssignableSize

namespace P205.Matroids
open Set
open scoped BigOperators
noncomputable section
universe u

/-- Choose one original occurrence of each element and delete all others. -/
theorem assignment_refinement : Specs.P205.Matroids.AssignmentRefinement := by
  classical
  intro α k F parts hind
  let I : Set α := ⋃ i, parts i
  have hex : ∀ e : I, ∃ i, (e : α) ∈ parts i := by
    intro e
    exact mem_iUnion.mp e.property
  let pick : I → Fin k := fun e => Classical.choose (hex e)
  have hpick : ∀ e : I, (e : α) ∈ parts (pick e) :=
    fun e => Classical.choose_spec (hex e)
  let refined : Fin k → Set α := fun i => {e | ∃ h : e ∈ I, pick ⟨e, h⟩ = i}
  have hsub : ∀ i, refined i ⊆ parts i := by
    intro i e he
    obtain ⟨he, hp⟩ := he
    simpa only [hp] using hpick ⟨e, he⟩
  refine ⟨refined, hsub, Subset.rfl, fun i => (hind i).subset (hsub i), ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro e ⟨he, hi⟩ ⟨he', hj⟩
    exact hij (hi.symm.trans hj)
  · ext e
    constructor
    · intro he
      exact mem_iUnion.mpr ⟨pick ⟨e, he⟩, he, rfl⟩
    · intro he
      obtain ⟨i, hi⟩ := mem_iUnion.mp he
      exact hi.choose

/-- Assignability is equivalent to the existence of a disjoint assignment. -/
theorem assignable_disjointization : Specs.P205.Matroids.AssignableDisjointization := by
  intro α k F S I hIS
  constructor
  · rintro ⟨parts, hind, hunion⟩
    obtain ⟨refined, _, hr⟩ := assignment_refinement F parts hind
    rw [← hunion] at hr
    exact ⟨refined, hIS, hr.2⟩
  · rintro ⟨parts, _, hind, _, hunion⟩
    exact ⟨parts, hind, hunion⟩

/-- The elements with all their copies in U. This also makes sense at k = 0. -/
private def allCopies {α : Type u} {S : Set α} {k : ℕ}
    (U : Set (CopyGround S k)) : Set α := S \ copyLabels (univ \ U)

private theorem allCopies_subset_slice {α : Type u} {S : Set α} {k : ℕ}
    (U : Set (CopyGround S k)) (i : Fin k) : allCopies U ⊆ copySlice U i := by
  classical
  rintro e ⟨heS, he⟩
  refine ⟨⟨e, heS⟩, ?_, rfl⟩
  change (⟨e, heS⟩, i) ∈ U
  by_contra hn
  exact he ⟨(⟨e, heS⟩, i), ⟨mem_univ _, hn⟩, rfl⟩

private theorem complement_labels {α : Type u} {S : Set α} {k : ℕ}
    (U : Set (CopyGround S k)) : copyLabels (univ \ U) = S \ allCopies U := by
  ext e
  have h := @copy_labels_subset α S k (univ \ U) e
  simp only [allCopies, mem_sdiff]
  tauto

/-- Compressing any copy split gives a no larger original rank expression. -/
theorem copy_split_compression {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (hS : S ⊆ F.ground) (U : Set (CopyGround S k)) :
    ∃ T : Set α, T ⊆ S ∧
      (S \ T).ncard + ∑ i, rank (F.matroid i) T ≤
        rank (sliceMatroid F S) U + rank (labelMatroid S k) (univ \ U) := by
  refine ⟨allCopies U, sdiff_subset, ?_⟩
  rw [show rank (sliceMatroid F S) U = ∑ i, rank (F.matroid i) (copySlice U i)
      from slice_rank F S hS U,
    show rank (labelMatroid S k) (univ \ U) = (copyLabels (univ \ U)).ncard
      from label_rank S k (univ \ U), complement_labels]
  have hle : (∑ i, rank (F.matroid i) (allCopies U)) ≤
      ∑ i, rank (F.matroid i) (copySlice U i) :=
    Finset.sum_le_sum fun i _ => rank_mono (F.matroid i) (allCopies_subset_slice U i)
  omega

/-- For a positive number of matroids, a full-copy split realizes each expression. -/
theorem full_copy_split {α : Type u} {k : ℕ} (F : Family α k) (hk : 0 < k)
    (S T : Set α) (hS : S ⊆ F.ground) (hT : T ⊆ S) :
    rank (sliceMatroid F S) (labelledParts S (fun _ : Fin k => T)) +
      rank (labelMatroid S k) (univ \ labelledParts S (fun _ : Fin k => T)) =
    (S \ T).ncard + ∑ i, rank (F.matroid i) T := by
  have hslices := labelled_parts_slice (fun _ : Fin k => T) (fun _ => hT)
  have hlabels : copyLabels (univ \ labelledParts S (fun _ : Fin k => T)) = S \ T := by
    ext e
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1.property, hp.2⟩
    · rintro ⟨heS, heT⟩
      exact ⟨(⟨e, heS⟩, ⟨0, hk⟩), ⟨mem_univ _, heT⟩, rfl⟩
  rw [show rank (sliceMatroid F S) (labelledParts S (fun _ : Fin k => T)) =
      ∑ i, rank (F.matroid i) (copySlice (labelledParts S (fun _ : Fin k => T)) i)
      from slice_rank F S hS _,
    show rank (labelMatroid S k) (univ \ labelledParts S (fun _ : Fin k => T)) =
      (copyLabels (univ \ labelledParts S (fun _ : Fin k => T))).ncard
      from label_rank S k _, hlabels]
  simp only [hslices]
  exact Nat.add_comm _ _

/-- The common independent optimum is exactly the separately defined maximum q. -/
theorem common_maximum_eq_q {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (J : Set (CopyGround S k))
    (hJ₁ : (sliceMatroid F S).Indep J) (hJ₂ : (labelMatroid S k).Indep J)
    (hmax : ∀ K : Set (CopyGround S k), (sliceMatroid F S).Indep K →
      (labelMatroid S k).Indep K → K.ncard ≤ J.ncard) : J.ncard = q F S := by
  apply Nat.le_antisymm
  · have ha := (common_assignment F S J).mp ⟨hJ₁, hJ₂⟩
    have hass : Assignable F (copyLabels J) := ⟨copySlice J, ha.2.1, ha.2.2.2⟩
    rw [← common_cardinality F S J hJ₁ hJ₂]
    exact (q_maximum F S).2 _ ha.1 hass
  · obtain ⟨I, hIS, ha, hq⟩ := (q_maximum F S).1
    obtain ⟨parts, hparts⟩ := (assignable_disjointization F S I hIS).mp ha
    have hc := assignment_copies F S I parts hparts
    have hq' : I.ncard = q F S := hq
    rw [← hq', ← hc.2.2.2.2]
    exact hmax _ hc.1 hc.2.1

/-- Empty-family verification uses no positive-copy argument. -/
theorem maximum_assignable_zero : Specs.P205.Matroids.MaximumAssignableZero := by
  intro α F S hS
  refine ⟨assignable_zero F, q_zero F S, ?_, ?_⟩
  · simp [q_zero F S]
  · intro T hT
    simp [q_zero F S]

private theorem maximum_assignable_min_pos {α : Type u} {k : ℕ}
    (F : Family α k) (hk : 0 < k) (S : Set α) (hS : S ⊆ F.ground) :
    (∃ T : Set α, T ⊆ S ∧
      q F S = (S \ T).ncard + ∑ i, rank (F.matroid i) T) ∧
    (∀ T : Set α, T ⊆ S →
      q F S ≤ (S \ T).ncard + ∑ i, rank (F.matroid i) T) := by
  let : (sliceMatroid F S).Finite := (copy_finite F S hS).1
  let : (labelMatroid S k).Finite := (copy_finite F S hS).2
  have hg : (sliceMatroid F S).E = univ := slice_ground F S
  have hE : (sliceMatroid F S).E = (labelMatroid S k).E :=
    (slice_ground F S).trans (label_ground S k).symm
  obtain ⟨J, U, hJ₁, hJ₂, hU, heq, hmax, _⟩ :=
    intersection_attainment (sliceMatroid F S) (labelMatroid S k) hE
  have hq := common_maximum_eq_q F S J hJ₁ hJ₂ hmax
  have hbound : ∀ T : Set α, T ⊆ S →
      q F S ≤ (S \ T).ncard + ∑ i, rank (F.matroid i) T := by
    intro T hT
    have hb := intersection_upper_bound (sliceMatroid F S) (labelMatroid S k) hE
      J (labelledParts S (fun _ : Fin k => T)) hJ₁ hJ₂
      (by rw [hg]; exact subset_univ _)
    change J.ncard ≤ rank (sliceMatroid F S) (labelledParts S (fun _ : Fin k => T)) +
      rank (labelMatroid S k) ((sliceMatroid F S).E \ labelledParts S (fun _ : Fin k => T)) at hb
    rw [hg, full_copy_split F hk S T hS hT, hq] at hb
    exact hb
  obtain ⟨T, hT, hcomp⟩ := copy_split_compression F S hS U
  change J.ncard = rank (sliceMatroid F S) U +
    rank (labelMatroid S k) ((sliceMatroid F S).E \ U) at heq
  rw [hg, hq] at heq
  refine ⟨⟨T, hT, Nat.le_antisymm (hbound T hT) ?_⟩, hbound⟩
  exact hcomp.trans heq.ge

/-- Maximum assignable subset size equals the attained minimum over all T ⊆ S. -/
theorem maximum_assignable_min : Specs.P205.Matroids.MaximumAssignableMin := by
  intro α k F S hS
  cases k with
  | zero =>
    have hz := maximum_assignable_zero F S hS
    exact ⟨⟨S, Subset.rfl, hz.2.2.1⟩, hz.2.2.2⟩
  | succ k =>
    exact maximum_assignable_min_pos F (Nat.succ_pos k) S hS

end
end P205.Matroids
