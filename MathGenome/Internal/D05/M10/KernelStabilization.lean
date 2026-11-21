import MathGenome.Internal.Specs.D05.M10.KernelStabilization
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M02.SubspaceDimension
import MathGenome.Internal.D05.M08.Evaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! K05.10.kernel_stabilization: ascending kernels and descending images. -/

namespace D05.M10.KernelStabilization

theorem initial_terms : Specs.D05.M10.KernelStabilization.initial_terms := by
  intro K V _ _ _ T
  change LinearMap.ker (LinearMap.id : Module.End K V) = ⊥ ∧
    LinearMap.range (LinearMap.id : Module.End K V) = ⊤
  exact ⟨LinearMap.ker_id, LinearMap.range_id⟩

theorem kernel_inclusion : Specs.D05.M10.KernelStabilization.kernel_inclusion := by
  intro K V _ _ _ T k
  rw [pow_succ', Module.End.mul_eq_comp]
  exact LinearMap.ker_le_ker_comp (T ^ k) T

theorem image_inclusion : Specs.D05.M10.KernelStabilization.image_inclusion := by
  intro K V _ _ _ T k
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range T (T ^ k)

theorem kernel_eq_of_consecutive :
    Specs.D05.M10.KernelStabilization.kernel_eq_of_consecutive := by
  intro K V _ _ _ T k h j
  exact Module.End.ker_pow_constant h j

theorem kernel_stabilization :
    Specs.D05.M10.KernelStabilization.kernel_stabilization := by
  intro K V _ _ _ _ T n hn j
  subst n
  exact (Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T)
    (Nat.le_add_right (Module.finrank K V) j)).symm

theorem image_stabilization :
    Specs.D05.M10.KernelStabilization.image_stabilization := by
  intro K V _ _ _ _ T n hn j
  have hker := kernel_stabilization T n hn j
  have hle : LinearMap.range (T ^ (n + j)) ≤ LinearMap.range (T ^ n) := by
    rw [pow_add, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range (T ^ j) (T ^ n)
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hn_rank := D05.M03.RankNullity.rank_nullity (T ^ n)
  have hj_rank := D05.M03.RankNullity.rank_nullity (T ^ (n + j))
  rw [← hker] at hj_rank
  exact Nat.add_left_cancel (hj_rank.symm.trans hn_rank)

end D05.M10.KernelStabilization
