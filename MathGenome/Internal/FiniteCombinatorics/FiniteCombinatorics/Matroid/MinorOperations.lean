import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Duality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.MinorOperations

/-! The operation assertions of paper.tex, W69, for the same canonical
set-ground matroids as Foundation and Duality. These are equalities of matroids,
including when the remaining ground is empty. The current-ground lemmas make
explicit why overlapping successive operation sets are allowed. -/

namespace FiniteCombinatorics.Matroid

open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

theorem successiveDeletions (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    (M ＼ C) ＼ D = M ＼ (C ∪ D) :=
  _root_.Matroid.delete_delete M C D

theorem successiveContractions (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    (M ／ C) ／ D = M ／ (C ∪ D) :=
  _root_.Matroid.contract_contract M C D

theorem disjointDeletionContraction (M : _root_.Matroid α) [M.Finite]
    (C D : Set α) (hCD : Disjoint C D) : (M ／ C) ＼ D = (M ＼ D) ／ C :=
  _root_.Matroid.contract_delete_comm M hCD

theorem emptyDeletion (M : _root_.Matroid α) [M.Finite] : M ＼ ∅ = M :=
  _root_.Matroid.delete_empty M

theorem emptyContraction (M : _root_.Matroid α) [M.Finite] : M ／ ∅ = M :=
  _root_.Matroid.contract_empty M

theorem deletionCurrentGround (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    (M ＼ C) ＼ (D ∩ (M ＼ C).E) = (M ＼ C) ＼ D :=
  _root_.Matroid.delete_inter_ground_eq (M ＼ C) D

theorem contractionCurrentGround (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    (M ／ C) ／ (D ∩ (M ／ C).E) = (M ／ C) ／ D :=
  _root_.Matroid.contract_inter_ground_eq (M ／ C) D

theorem successiveDeletionsGround (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    ((M ＼ C) ＼ D).E = M.E \ (C ∪ D) := by
  rw [successiveDeletions, _root_.Matroid.delete_ground]

theorem successiveContractionsGround (M : _root_.Matroid α) [M.Finite]
    (C D : Set α) : ((M ／ C) ／ D).E = M.E \ (C ∪ D) := by
  rw [successiveContractions, _root_.Matroid.contract_ground]

theorem mixedMinorGround (M : _root_.Matroid α) [M.Finite] (C D : Set α) :
    ((M ／ C) ＼ D).E = M.E \ (C ∪ D) ∧
      ((M ＼ D) ／ C).E = M.E \ (C ∪ D) := by
  constructor <;>
    simp only [_root_.Matroid.delete_ground, _root_.Matroid.contract_ground,
      sdiff_sdiff, union_comm]

end FiniteCombinatorics.Matroid
