import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Duality

/-! The canonical Mathlib dual, deletion and contraction realize W67.
The minor assertions hold for all ambient sets `C`, in particular for all
`C ⊆ M.E` as in the source, including the empty and full ground sets. -/

namespace FiniteCombinatorics.Matroid

open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

theorem dualGround (M : _root_.Matroid α) [M.Finite] : M✶.E = M.E :=
  _root_.Matroid.dual_ground

theorem dualFinite (M : _root_.Matroid α) [M.Finite] : M✶.Finite :=
  inferInstance

theorem dualBases (M : _root_.Matroid α) [M.Finite] (D : Set α) :
    M✶.IsBase D ↔ ∃ B, M.IsBase B ∧ D = relativeCompl M.E B := by
  constructor
  · intro hD
    exact ⟨M.E \ D, hD.compl_isBase_of_dual,
      (sdiff_sdiff_cancel_left hD.subset_ground).symm⟩
  · rintro ⟨B, hB, rfl⟩
    exact hB.compl_isBase_dual

theorem dualBaseComplement (M : _root_.Matroid α) [M.Finite] (D : Set α) :
    M✶.IsBase D ↔ D ⊆ M.E ∧ M.IsBase (relativeCompl M.E D) := by
  exact _root_.Matroid.dual_isBase_iff'.trans and_comm

theorem dualInvolution (M : _root_.Matroid α) [M.Finite] : M✶✶ = M :=
  _root_.Matroid.dual_dual M

theorem deletionGround (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ＼ C).E = relativeCompl M.E C := rfl

theorem deletionIndependent (M : _root_.Matroid α) [M.Finite] (C I : Set α) :
    (M ＼ C).Indep I ↔ M.Indep I ∧ I ⊆ relativeCompl M.E C := by
  rw [_root_.Matroid.delete_indep_iff]
  constructor
  · rintro ⟨hI, hIC⟩
    exact ⟨hI, subset_sdiff.mpr ⟨hI.subset_ground, hIC⟩⟩
  · rintro ⟨hI, hIC⟩
    exact ⟨hI, (subset_sdiff.mp hIC).2⟩

theorem deletionFinite (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ＼ C).Finite := inferInstance

theorem contractionDefinition (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    M ／ C = (M✶ ＼ C)✶ := rfl

theorem contractionGround (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ／ C).E = relativeCompl M.E C := rfl

theorem contractionFinite (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ／ C).Finite := inferInstance

theorem contractionDual (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ／ C)✶ = M✶ ＼ C := _root_.Matroid.dual_contract M C

theorem deletionDual (M : _root_.Matroid α) [M.Finite] (C : Set α) :
    (M ＼ C)✶ = M✶ ／ C := _root_.Matroid.dual_delete M C

end FiniteCombinatorics.Matroid
