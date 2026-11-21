import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.HoffmanWielandtSorted
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.HoffmanWielandtNormal
import Mathlib.Algebra.Order.Rearrangement

noncomputable section
open scoped BigOperators

namespace NumAnalysis206.HoffmanWielandtSorted

theorem sorted_squared_cost_le :
    Specs.NumAnalysis206.HoffmanWielandtSorted.sorted_squared_cost_le := by
  intro n a b ha hb p
  have hprod := (ha.monovary hb).sum_mul_comp_perm_le_sum_mul (σ := p)
  have hsq : (∑ i, b (p i) ^ 2) = ∑ i, b i ^ 2 :=
    Equiv.sum_comp p (fun i => b i ^ 2)
  have expand (c : Fin n → ℝ) :
      (∑ i, (a i - c i) ^ 2) =
        (∑ i, a i ^ 2) + (∑ i, c i ^ 2) - 2 * ∑ i, a i * c i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand b, expand (fun i => b (p i)), hsq]
  linarith

/-- The real-eigenvalue version of the mixed spectral-basis cost identity.
Symmetry moves A to the left side of the inner product; its eigenvalues are
real, so conjugation leaves them unchanged. -/
lemma hermitian_spectral_cost {K : Type*} [RCLike K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    MatrixData.frobeniusNorm (A - B) ^ 2 =
      ∑ i, ∑ j, (MatrixData.eigenvalue A hA i - MatrixData.eigenvalue B hB j) ^ 2 *
        ‖inner K (MatrixData.eigenbasis A hA i) (MatrixData.eigenbasis B hB j)‖ ^ 2 := by
  let u := MatrixData.eigenbasis A hA
  let v := MatrixData.eigenbasis B hB
  rw [MatrixData.frobeniusNorm_sq_basis (A - B) v]
  calc
    (∑ j, ‖(A - B).toEuclideanLin (v j)‖ ^ 2) =
        ∑ i, ∑ j, ‖inner K (u i) ((A - B).toEuclideanLin (v j))‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (u.sum_sq_norm_inner_right _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have he : inner K (u i) ((A - B).toEuclideanLin (v j)) =
          ((MatrixData.eigenvalue A hA i - MatrixData.eigenvalue B hB j : ℝ) : K) *
            inner K (u i) (v j) := by
        rw [map_sub, LinearMap.sub_apply, inner_sub_right,
          ← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (u i) (v j)]
        dsimp only [u, v]
        rw [MatrixData.eigenbasis_action, MatrixData.eigenbasis_action,
          inner_smul_left, inner_smul_right, RCLike.conj_ofReal, RCLike.ofReal_sub,
          sub_mul]
      rw [he, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

theorem hoffman_wielandt_sorted :
    Specs.NumAnalysis206.HoffmanWielandtSorted.hoffman_wielandt_sorted := by
  intro K _ n A B hA hB
  let u := MatrixData.eigenbasis A hA
  let v := MatrixData.eigenbasis B hB
  have hP : (fun i j => ‖inner K (u i) (v j)‖ ^ 2) ∈ doublyStochastic ℝ (Fin n) := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
    · intro i
      rw [v.sum_sq_norm_inner_left, u.norm_eq_one, one_pow]
    · intro j
      rw [u.sum_sq_norm_inner_right, v.norm_eq_one, one_pow]
  obtain ⟨p, hp⟩ := HoffmanWielandtNormal.exists_perm_cost_le
    (fun i j => ‖inner K (u i) (v j)‖ ^ 2)
    (fun i j => (MatrixData.eigenvalue A hA i - MatrixData.eigenvalue B hB j) ^ 2) hP
  exact (sorted_squared_cost_le _ _ (MatrixData.eigenvalue_monotone A hA)
    (MatrixData.eigenvalue_monotone B hB) p).trans
      (hp.trans_eq (hermitian_spectral_cost A B hA hB).symm)

end NumAnalysis206.HoffmanWielandtSorted
