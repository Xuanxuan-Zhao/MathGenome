import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.DualRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.MinorRank

/-! The rank formulas and basis extension criterion of paper.tex, W69.
Contraction rank follows by applying dual rank on the retained ground,
then deletion rank, and finally dual rank on the original ground.
All cancellation takes place in ℤ, without any positive-rank assumptions. -/

namespace FiniteCombinatorics.Matroid

open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

theorem deletionRank (M : _root_.Matroid α) [M.Finite] (C A : Set α)
    (_hC : C ⊆ M.E) (hA : A ⊆ relativeCompl M.E C) :
    rank (M ＼ C) A = rank M A := by
  change A ⊆ M.E \ C at hA
  unfold rank
  rw [_root_.Matroid.delete_eq_restrict, M.restrict_eRk_eq hA]

theorem contractionRank (M : _root_.Matroid α) [M.Finite] (C A : Set α)
    (hC : C ⊆ M.E) (hA : A ⊆ relativeCompl M.E C) :
    rank (M ／ C) A = rank M (A ∪ C) - rank M C := by
  have hAE : A ⊆ M.E := hA.trans sdiff_subset
  have hcomp : relativeCompl M.E (M.E \ C) = C :=
    sdiff_sdiff_cancel_left hC
  have hcompA : relativeCompl M.E ((M.E \ C) \ A) = A ∪ C := by
    ext x
    constructor
    · intro hx
      by_cases hxC : x ∈ C
      · exact Or.inr hxC
      · exact Or.inl (by
          by_contra hxA
          exact hx.2 ⟨⟨hx.1, hxC⟩, hxA⟩)
    · rintro (hxA | hxC)
      · exact ⟨hAE hxA, fun hx => hx.2 hxA⟩
      · exact ⟨hC hxC, fun hx => hx.1.2 hxC⟩
  have hcard : ((((M.E \ C) \ A).ncard : ℤ) + (A.ncard : ℤ)) =
      ((M.E \ C).ncard : ℤ) := by
    exact_mod_cast ncard_sdiff_add_ncard_of_subset hA M.ground_finite.sdiff
  have hd := dualRank (M✶ ＼ C) A hA
  have h₁ := deletionRank M✶ C ((M.E \ C) \ A) hC sdiff_subset
  have h₂ := deletionRank M✶ C (M.E \ C) hC Subset.rfl
  have h₃ := dualRank M ((M.E \ C) \ A) (sdiff_subset.trans sdiff_subset)
  have h₄ := dualRank M (M.E \ C) sdiff_subset
  change rank (M ／ C) A = (A.ncard : ℤ) +
    rank (M✶ ＼ C) ((M.E \ C) \ A) - rank (M✶ ＼ C) (M.E \ C) at hd
  rw [h₁, h₂, h₃, h₄, hcomp, hcompA] at hd
  linarith

theorem contractionIndependentBasis (M : _root_.Matroid α) [M.Finite]
    (C I J : Set α) (_hC : C ⊆ M.E) (hI : M.IsBasis I C)
    (hJ : J ⊆ relativeCompl M.E C) :
    (M ／ C).Indep J ↔ M.Indep (I ∪ J) := by
  have hd : Disjoint C J := disjoint_left.mpr fun _ hxC hxJ => (hJ hxJ).2 hxC
  simpa only [union_comm] using hI.contract_indep_iff_of_disjoint hd

end FiniteCombinatorics.Matroid
