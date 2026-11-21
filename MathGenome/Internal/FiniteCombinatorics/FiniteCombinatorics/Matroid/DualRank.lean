import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Duality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.DualRank

/-! The dual rank formula of W67, with the canonical finite integer rank.
We convert Mathlib's subtraction-free extended-rank identity to finite
natural ranks, then to integers, before performing any subtraction. -/

namespace FiniteCombinatorics.Matroid

open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

/-- Dual rank on a subset of the finite ground, with subtraction in ℤ. -/
theorem dualRank (M : _root_.Matroid α) [M.Finite] (A : Set α) (hA : A ⊆ M.E) :
    rank M✶ A = (A.ncard : ℤ) + rank M (relativeCompl M.E A) - rank M M.E := by
  have h := M.eRk_dual_add_eRank A hA
  rw [M.eRank_def, ← finiteRankBridge M✶ A, ← finiteRankBridge M M.E,
    ← finiteRankBridge M (M.E \ A),
    ← (M.ground_finite.subset hA).cast_ncard_eq] at h
  norm_cast at h
  have hz : rank M✶ A + rank M M.E = rank M (relativeCompl M.E A) + (A.ncard : ℤ) := by
    unfold rank relativeCompl
    exact_mod_cast h
  apply (eq_sub_iff_add_eq).2
  exact hz.trans (add_comm _ _)

end FiniteCombinatorics.Matroid
