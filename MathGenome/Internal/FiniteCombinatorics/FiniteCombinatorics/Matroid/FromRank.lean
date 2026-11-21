import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FromRank
import Mathlib.Tactic.Linarith

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α} {r : Set α → ℤ}

/-- Adding a finite collection increases rank by between zero and its size. -/
lemma rank_union_bounds (hr : RankPresentation E r) {A D : Set α}
    (hA : A ⊆ E) (hD : D ⊆ E) (hf : D.Finite) :
    r A ≤ r (A ∪ D) ∧ r (A ∪ D) ≤ r A + (D.ncard : ℤ) := by
  induction D, hf using Set.Finite.induction_on with
  | empty => simp
  | @insert e D he hf ih =>
    have heE := hD (mem_insert e D)
    have hDE : D ⊆ E := (subset_insert e D).trans hD
    have hi := ih hDE
    have hb := hr.2.1 (A ∪ D) (union_subset hA hDE) e heE
    rw [union_insert]
    rw [ncard_insert_of_notMem he hf, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith [hi.1, hi.2, hb.1, hb.2]

lemma rank_mono_of_presentation (hr : RankPresentation E r)
    {A B : Set α} (hAB : A ⊆ B) (hB : B ⊆ E) (hf : B.Finite) : r A ≤ r B := by
  have h := (rank_union_bounds hr (hAB.trans hB) hB hf).1
  simpa [union_eq_self_of_subset_left hAB] using h

theorem rankPresentationBounds (E : Set α) (hE : E.Finite) (r : Set α → ℤ)
    (hr : RankPresentation E r) (A : Set α) (hA : A ⊆ E) :
    0 ≤ r A ∧ r A ≤ (A.ncard : ℤ) := by
  simpa [hr.1] using rank_union_bounds hr (empty_subset E) hA (hE.subset hA)

/-- The deficit of a subset cannot exceed that of the larger set. -/
lemma rankIndependent_subset (hE : E.Finite) (hr : RankPresentation E r)
    {I J : Set α} (hI : RankIndependent E r I) (hJI : J ⊆ I) :
    RankIndependent E r J := by
  have hJ := hJI.trans hI.1
  have hb := (rank_union_bounds hr hJ
    ((sdiff_subset : I \ J ⊆ I).trans hI.1) ((hE.subset hI.1).sdiff)).2
  have hu : J ∪ I \ J = I := by
    classical
    ext x
    constructor
    · rintro (hx | hx)
      · exact hJI hx
      · exact hx.1
    · intro hx
      by_cases hxJ : x ∈ J
      · exact Or.inl hxJ
      · exact Or.inr ⟨hx, hxJ⟩
  rw [hu, cast_ncard_sdiff hJI (hE.subset hI.1)] at hb
  have hjb := (rankPresentationBounds E hE r hr J hJ).2
  exact ⟨hJ, by linarith [hI.2]⟩

/-- Submodularity gives diminishing increments, including when `e ∈ B`. -/
lemma rank_diminishing (hr : RankPresentation E r) {A B : Set α}
    (hAB : A ⊆ B) (hB : B ⊆ E) {e : α} (he : e ∈ E) :
    r (insert e B) - r B ≤ r (insert e A) - r A := by
  by_cases heB : e ∈ B
  · rw [insert_eq_of_mem heB, sub_self]
    exact (hr.2.1 A (hAB.trans hB) e he).1
  · have hu : insert e A ∪ B = insert e B := by
      ext x
      simp only [mem_union, mem_insert_iff]
      constructor
      · rintro ((rfl | hx) | hx)
        · exact Or.inl rfl
        · exact Or.inr (hAB hx)
        · exact Or.inr hx
      · rintro (rfl | hx)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hx
    have hi : insert e A ∩ B = A := by
      ext x
      simp only [mem_inter_iff, mem_insert_iff]
      constructor
      · rintro ⟨rfl | hx, hxB⟩
        · exact False.elim (heB hxB)
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, hAB hx⟩
    have hs := hr.2.2 (insert e A) (insert_subset he (hAB.trans hB)) B hB
    rw [hu, hi] at hs
    linarith

/-- If all single additions have zero increment, their finite union does too. -/
lemma rank_union_eq_of_insert_eq (hr : RankPresentation E r) {A D : Set α}
    (hA : A ⊆ E) (hD : D ⊆ E) (hf : D.Finite)
    (hz : ∀ e ∈ D, r (insert e A) = r A) : r (A ∪ D) = r A := by
  induction D, hf using Set.Finite.induction_on with
  | empty => simp
  | @insert e D he hf ih =>
    have heE := hD (mem_insert e D)
    have hDE : D ⊆ E := (subset_insert e D).trans hD
    have hi := ih hDE (fun x hx => hz x (mem_insert_of_mem e hx))
    have hd := rank_diminishing hr (subset_union_left : A ⊆ A ∪ D)
      (union_subset hA hDE) heE
    have hb := (hr.2.1 (A ∪ D) (union_subset hA hDE) e heE).1
    rw [union_insert]
    have hz' := hz e (mem_insert e D)
    linarith

/-- An independent set can fail a single extension only at zero increment. -/
lemma rank_insert_eq_of_not_independent (hE : E.Finite) (hr : RankPresentation E r)
    {I : Set α} (hI : RankIndependent E r I) {e : α} (he : e ∈ E)
    (hn : ¬ RankIndependent E r (insert e I)) : r (insert e I) = r I := by
  by_cases heI : e ∈ I
  · rw [insert_eq_of_mem heI]
  have hb := hr.2.1 I hI.1 e he
  have hc := ncard_insert_of_notMem heI (hE.subset hI.1)
  have hne : r (insert e I) ≠ r I + 1 := by
    intro h
    apply hn
    refine ⟨insert_subset he hI.1, ?_⟩
    rw [hc, Nat.cast_add, Nat.cast_one, h, hI.2]
  omega

/-- The rank-equals-size predicate satisfies augmentation. -/
lemma rankIndependent_augmentation (hE : E.Finite) (hr : RankPresentation E r)
    {I J : Set α} (hI : RankIndependent E r I) (hJ : RankIndependent E r J)
    (hc : I.ncard < J.ncard) : ∃ e ∈ J \ I, RankIndependent E r (insert e I) := by
  classical
  by_contra hn
  have hz : ∀ e ∈ J, r (insert e I) = r I := by
    intro e heJ
    by_cases heI : e ∈ I
    · rw [insert_eq_of_mem heI]
    · exact rank_insert_eq_of_not_independent hE hr hI (hJ.1 heJ)
        (fun hi => hn ⟨e, ⟨heJ, heI⟩, hi⟩)
  have hu := rank_union_eq_of_insert_eq hr hI.1 hJ.1 (hE.subset hJ.1) hz
  have hm := rank_mono_of_presentation hr (subset_union_right : J ⊆ I ∪ J)
    (union_subset hI.1 hJ.1) ((hE.subset hI.1).union (hE.subset hJ.1))
  have hc' : (I.ncard : ℤ) < (J.ncard : ℤ) := by exact_mod_cast hc
  linarith [hI.2, hJ.2]

/-- Integer rank axioms construct a finite matroid and recover precisely the
supplied rank on all subsets of its ground, including the empty ground. -/
theorem existsMatroidFromRank (E : Set α) (hE : E.Finite) (r : Set α → ℤ)
    (hr : RankPresentation E r) : ∃ M : _root_.Matroid α,
      M.E = E ∧ ∃ hM : M.Finite,
        (∀ I, M.Indep I ↔ RankIndependent E r I) ∧
        (∀ A, A ⊆ E → @rank α M hM A = r A) := by
  let S : IndependenceSystem E := {
    finite_ground := hE
    Indep := RankIndependent E r
    empty_indep := ⟨empty_subset E, by simpa using hr.1⟩
    hereditary := fun {_ _} hI hJI => rankIndependent_subset hE hr hI hJI
    subset_ground := fun {_} hI => hI.1 }
  have ha : Augmentation S := fun {_ _} hI hJ hc =>
    rankIndependent_augmentation hE hr hI hJ hc
  let M := ofAugmentation S ha
  have hME : M.E = E := groundPreserved E S ha
  refine ⟨M, hME, inferInstance, ?_, ?_⟩
  · intro I
    exact indepPreserved E S ha I
  · intro A hA
    obtain ⟨I, hI⟩ := M.exists_isBasis A (by simpa only [hME] using hA)
    have hi : RankIndependent E r I := (indepPreserved E S ha I).mp hI.indep
    have hz : ∀ e ∈ A, r (insert e I) = r I := by
      intro e heA
      by_cases heI : e ∈ I
      · rw [insert_eq_of_mem heI]
      · apply rank_insert_eq_of_not_independent hE hr hi (hA heA)
        intro h
        exact heI (hI.mem_of_insert_indep heA ((indepPreserved E S ha _).mpr h))
    have hu := rank_union_eq_of_insert_eq hr hi.1 hA (hE.subset hA) hz
    rw [union_eq_self_of_subset_left hI.subset] at hu
    change ((M.eRk A).toNat : ℤ) = r A
    rw [hI.eRk_eq_encard]
    change (I.ncard : ℤ) = r A
    exact hi.2.symm.trans hu.symm

end FiniteCombinatorics.Matroid
