import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Minors
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Intersection
import Mathlib.Tactic.Tauto

namespace P205.Matroids
open Set
open scoped Matroid
universe u

private theorem rank_empty_eq {α : Type u} (M : Matroid α) : rank M ∅ = 0 :=
  rank_empty M

private theorem rank_restrict_eq {α : Type u} (M : Matroid α) [M.Finite]
    (U : Set α) (hU : U ⊆ M.E) (S : Set α) (hS : S ⊆ U) :
    rank (M ↾ U) S = rank M S := restriction_rank M U hU S hS

private theorem rank_contract_eq {α : Type u} (M : Matroid α) [M.Finite]
    (C : Set α) (hC : C ⊆ M.E) (S : Set α) (hS : S ⊆ M.E \ C) :
    rank (M ／ C) S = rank M (S ∪ C) - rank M C := contraction_rank M C hC S hS

theorem intersection_upper_bound : Specs.P205.Matroids.IntersectionUpperBound := by
  intro α M N _ _ hE I U hIM hIN hU
  have h₁ := (rank_maximum M U hU).2 (I ∩ U) inter_subset_right
    (hIM.subset inter_subset_left)
  have h₂ := (rank_maximum N (M.E \ U) (hE ▸ sdiff_subset)).2 (I \ U)
    (sdiff_subset_sdiff_left hIM.subset_ground) (hIN.subset sdiff_subset)
  have hc := ncard_inter_add_ncard_sdiff_eq_ncard I U hIM.finite
  change I.ncard ≤ rank M U + rank N (M.E \ U)
  simp only [rank] at *
  omega

/-- Finite rank is monotone, with no ambient finiteness assumption. -/
theorem rank_mono {α : Type u} (M : Matroid α) [M.Finite]
    {S T : Set α} (h : S ⊆ T) : rank M S ≤ rank M T :=
  ENat.toNat_le_toNat (M.eRk_mono h)
    ((Matroid.eRk_ne_top_iff).2 (Matroid.isRkFinite_set M T))

/-- Adding one element increases finite rank by at most one. -/
theorem rank_insert_le {α : Type u} (M : Matroid α) [M.Finite]
    (e : α) (S : Set α) : rank M (insert e S) ≤ rank M S + 1 := by
  have h := ENat.toNat_le_toNat (M.eRk_insert_le_add_one e S)
    (by simp [(Matroid.eRk_ne_top_iff).2 (Matroid.isRkFinite_set M S)])
  simpa [rank, Specs.P205.Matroids.rankValue, ENat.toNat_add,
    (Matroid.eRk_ne_top_iff).2 (Matroid.isRkFinite_set M S)] using h

/-- A singleton with positive rank is independent. -/
theorem singleton_indep_of_rank_pos {α : Type u} (M : Matroid α) [M.Finite]
    {e : α} (he : e ∈ M.E) (h : 0 < rank M {e}) : M.Indep {e} := by
  apply (independent_rank M {e} (singleton_subset_iff.mpr he)).2
  have hle := (rank_insert_le M e ∅)
  simp only [insert_empty_eq, rank_empty_eq] at hle
  simp only [ncard_singleton]
  simp only [rank] at *
  omega

/-- The lower-bound form of intersection, proved by strong induction on the
actual finite ground cardinality. A tight proper split is assembled using
contraction; in its absence deleting one element preserves the lower bound. -/
private theorem common_independent_of_lower_bound_aux {α : Type u} (c : ℕ) :
    ∀ (M N : Matroid α) [M.Finite] [N.Finite], M.E = N.E → M.E.ncard = c →
    ∀ n : ℕ, (∀ U : Set α, U ⊆ M.E → n ≤ rank M U + rank N (M.E \ U)) →
    ∃ I : Set α, M.Indep I ∧ N.Indep I ∧ n ≤ I.ncard := by
  classical
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro M N _ _ hE hc n hbound
    by_cases hn : n = 0
    · exact ⟨∅, M.empty_indep, N.empty_indep, by simp [hn]⟩
    by_cases hEmpty : M.E = ∅
    · have hb := hbound ∅ (empty_subset _)
      simp only [hEmpty, Set.sdiff_self, rank_empty_eq, add_zero] at hb
      simp only [rank] at *
      omega
    obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
    by_cases hSingle : M.E = {e}
    · have h₁ := hbound M.E Subset.rfl
      have h₂ := hbound ∅ (empty_subset _)
      simp only [Set.sdiff_self, rank_empty_eq, add_zero, sdiff_empty, zero_add, hSingle] at h₁ h₂
      have hle := rank_insert_le M e ∅
      simp only [insert_empty_eq, rank_empty_eq] at hle
      refine ⟨{e}, singleton_indep_of_rank_pos M he (by simp only [rank] at *; omega),
        singleton_indep_of_rank_pos N (hE ▸ he) (by simp only [rank] at *; omega), ?_⟩
      simp only [ncard_singleton]
      simp only [rank] at *
      omega
    by_cases htight : ∃ U : Set α, U ⊆ M.E ∧ U.Nonempty ∧ U ≠ M.E ∧
        rank M U + rank N (M.E \ U) = n
    · obtain ⟨U, hU, hUne, hUneE, hsum⟩ := htight
      let V := M.E \ U
      have hV : V ⊆ M.E := sdiff_subset
      have hVN : V ⊆ N.E := hV.trans hE.subset
      have hNV : N.E \ V = U := by
        rw [← hE]
        dsimp [V]
        ext x
        simp only [mem_sdiff]
        have := @hU x
        tauto
      have hUV : U ⊆ N.E \ V := hNV ▸ Subset.rfl
      have hU' : U.ncard < c := by
        rw [← hc]
        exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hU, hUneE⟩) M.ground_finite
      have hVne : V ≠ M.E := by
        intro hv
        obtain ⟨x, hx⟩ := hUne
        have : x ∈ V := hv ▸ hU hx
        exact this.2 hx
      have hV' : V.ncard < c := by
        rw [← hc]
        exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hV, hVne⟩) M.ground_finite
      have : (M ↾ U).Finite := restriction_finite M U hU
      have : (N ↾ V).Finite := restriction_finite N V hVN
      have hleftGround : (M ↾ U).E = (N ／ V).E := by
        rw [Matroid.restrict_ground_eq, Matroid.contract_ground, hNV]
      have hleft : ∀ A : Set α, A ⊆ (M ↾ U).E →
          rank M U ≤ rank (M ↾ U) A + rank (N ／ V) ((M ↾ U).E \ A) := by
        intro A hA
        change A ⊆ U at hA
        have hdiff : U \ A ⊆ N.E \ V := (sdiff_subset.trans hUV)
        have hsets : (U \ A) ∪ V = M.E \ A := by
          dsimp [V]
          ext x
          simp only [mem_union, mem_sdiff]
          have := @hA x
          have := @hU x
          tauto
        have hb := hbound A (hA.trans hU)
        have hm := rank_mono N (show V ⊆ M.E \ A by
          intro x hx
          exact ⟨hx.1, fun ha => hx.2 (hA ha)⟩)
        rw [Matroid.restrict_ground_eq, rank_restrict_eq M U hU A hA,
          rank_contract_eq N V hVN (U \ A) hdiff, hsets]
        dsimp [V] at *
        simp only [rank] at *
        omega
      obtain ⟨IU, hIUM', hIUN, hIUcard⟩ :=
        ih U.ncard hU' (M ↾ U) (N ／ V) hleftGround rfl (rank M U) hleft
      obtain ⟨hIUM, hIUU⟩ := (restriction_indep M U hU IU).1 hIUM'
      have hIUeq : IU.ncard = rank M U :=
        Nat.le_antisymm ((rank_maximum M U hU).2 IU hIUU hIUM) hIUcard
      have hIUbasis : M.IsBasis IU U :=
        (basis_rank M IU U hU).2 ⟨hIUU, hIUM, hIUeq⟩
      have hrightGround : (M ／ U).E = (N ↾ V).E := by
        rw [Matroid.contract_ground, Matroid.restrict_ground_eq]
      have hright : ∀ A : Set α, A ⊆ (M ／ U).E →
          rank N V ≤ rank (M ／ U) A + rank (N ↾ V) ((M ／ U).E \ A) := by
        intro A hA
        change A ⊆ V at hA
        have hsets : M.E \ (A ∪ U) = V \ A := by
          dsimp [V]
          ext x
          simp only [mem_union, mem_sdiff]
          tauto
        have hb := hbound (A ∪ U) (union_subset (hA.trans hV) hU)
        have hm := rank_mono M (subset_union_right : U ⊆ A ∪ U)
        rw [Matroid.contract_ground, rank_contract_eq M U hU A hA,
          rank_restrict_eq N V hVN (V \ A) sdiff_subset]
        rw [hsets] at hb
        change rank M U + rank N V = n at hsum
        simp only [rank] at *
        omega
      obtain ⟨IV, hIVM, hIVN', hIVcard⟩ :=
        ih V.ncard hV' (M ／ U) (N ↾ V) hrightGround rfl (rank N V) hright
      obtain ⟨hIVN, hIVV⟩ := (restriction_indep N V hVN IV).1 hIVN'
      have hIVeq : IV.ncard = rank N V :=
        Nat.le_antisymm ((rank_maximum N V hVN).2 IV hIVV hIVN) hIVcard
      have hIVbasis : N.IsBasis IV V :=
        (basis_rank N IV V hVN).2 ⟨hIVV, hIVN, hIVeq⟩
      have hdisj : Disjoint IU IV := by
        apply disjoint_left.mpr
        intro x hx hy
        exact (hIVV hy).2 (hIUU hx)
      refine ⟨IU ∪ IV, (contraction_indep M U hU IU hIUbasis IV hIVV).1 hIVM, ?_, ?_⟩
      · simpa only [union_comm] using
          (contraction_indep N V hVN IV hIVbasis IU (hIUU.trans hUV)).1 hIUN
      · rw [ncard_union_eq hdisj hIUM.finite hIVN.finite, hIUeq, hIVeq]
        exact hsum.ge
    · have hstrict : ∀ A : Set α, A ⊆ M.E → A.Nonempty → A ≠ M.E →
          rank M A + rank N (M.E \ A) ≠ n := by
        intro A hA hne hneE heq
        exact htight ⟨A, hA, hne, hneE, heq⟩
      let D := M.E \ {e}
      have hD : D ⊆ M.E := sdiff_subset
      have hDN : D ⊆ N.E := hD.trans hE.subset
      have : (M ↾ D).Finite := restriction_finite M D hD
      have : (N ↾ D).Finite := restriction_finite N D hDN
      have hDcard : D.ncard < c := by
        rw [← hc]
        exact ncard_sdiff_singleton_lt_of_mem he M.ground_finite
      have hDG : (M ↾ D).E = (N ↾ D).E := by
        simp only [Matroid.restrict_ground_eq]
      have hdelete : ∀ A : Set α, A ⊆ (M ↾ D).E →
          n ≤ rank (M ↾ D) A + rank (N ↾ D) ((M ↾ D).E \ A) := by
        intro A hA
        change A ⊆ D at hA
        rw [Matroid.restrict_ground_eq, rank_restrict_eq M D hD A hA,
          rank_restrict_eq N D hDN (D \ A) sdiff_subset]
        by_contra hbad
        have hAE : A ⊆ M.E := hA.trans hD
        have heA : e ∉ A := fun ha => (hA ha).2 (mem_singleton e)
        have hcomp : M.E \ A = insert e (D \ A) := by
          dsimp [D]
          ext x
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          have hx := @hAE x
          have heE := he
          constructor
          · rintro ⟨hxE, hxA⟩
            by_cases hxe : x = e
            · exact Or.inl hxe
            · exact Or.inr ⟨⟨hxE, hxe⟩, hxA⟩
          · rintro (rfl | ⟨⟨hxE, hxe⟩, hxA⟩)
            · exact ⟨heE, heA⟩
            · exact ⟨hxE, hxA⟩
        have hcomp' : M.E \ insert e A = D \ A := by
          dsimp [D]
          ext x
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
          tauto
        have hb₁ := hbound A hAE
        have hb₂ := hbound (insert e A) (insert_subset he hAE)
        have hi₁ := rank_insert_le N e (D \ A)
        have hi₂ := rank_insert_le M e A
        rw [hcomp] at hb₁
        rw [hcomp'] at hb₂
        have heq₁ : rank M A + rank N (M.E \ A) = n := by
          rw [hcomp]
          simp only [rank] at *
          omega
        have heq₂ : rank M (insert e A) + rank N (M.E \ insert e A) = n := by
          rw [hcomp']
          simp only [rank] at *
          omega
        have hAempty : A = ∅ := by
          by_contra hne
          apply hstrict A hAE (nonempty_iff_ne_empty.mpr hne) _ heq₁
          intro hEq
          exact heA (hEq ▸ he)
        apply hstrict (insert e A) (insert_subset he hAE) (insert_nonempty _ _) _ heq₂
        simpa [hAempty, eq_comm] using hSingle
      obtain ⟨I, hIM, hIN, hcard⟩ :=
        ih D.ncard hDcard (M ↾ D) (N ↾ D) hDG rfl n hdelete
      exact ⟨I, ((restriction_indep M D hD I).1 hIM).1,
        ((restriction_indep N D hDN I).1 hIN).1, hcard⟩

/-- Every lower bound on all split rank sums is reached by a common
independent set. This includes bounds below the optimum. -/
theorem exists_common_independent_of_rank_bounds {α : Type u} (M N : Matroid α)
    [M.Finite] [N.Finite] (hE : M.E = N.E) (n : ℕ)
    (hbound : ∀ U : Set α, U ⊆ M.E → n ≤ rank M U + rank N (M.E \ U)) :
    ∃ I : Set α, M.Indep I ∧ N.Indep I ∧ n ≤ I.ncard :=
  common_independent_of_lower_bound_aux M.E.ncard M N hE rfl n hbound

/-- Edmonds' unweighted intersection theorem, with witnesses for both extrema. -/
theorem intersection_attainment : Specs.P205.Matroids.IntersectionAttainment := by
  intro α M N _ _ hE
  classical
  have hex : ∃ n : ℕ, ∃ U : Set α, U ⊆ M.E ∧
      rank M U + rank N (M.E \ U) = n :=
    ⟨_, ∅, empty_subset _, rfl⟩
  obtain ⟨U, hU, hsum⟩ := Nat.find_spec hex
  have hbound : ∀ V : Set α, V ⊆ M.E →
      Nat.find hex ≤ rank M V + rank N (M.E \ V) := by
    intro V hV
    exact Nat.find_min' hex ⟨V, hV, rfl⟩
  obtain ⟨I, hIM, hIN, hcard⟩ :=
    exists_common_independent_of_rank_bounds M N hE (Nat.find hex) hbound
  have heq : I.ncard = rank M U + rank N (M.E \ U) := by
    exact Nat.le_antisymm (intersection_upper_bound M N hE I U hIM hIN hU)
      (hsum.symm ▸ hcard)
  refine ⟨I, U, hIM, hIN, hU, heq, ?_, ?_⟩
  · intro J hJM hJN
    exact (intersection_upper_bound M N hE J U hJM hJN hU).trans heq.ge
  · intro V hV
    change rank M U + rank N (M.E \ U) ≤ rank M V + rank N (M.E \ V)
    rw [hsum]
    exact hbound V hV

end P205.Matroids
