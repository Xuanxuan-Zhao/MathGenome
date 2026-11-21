import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.HoffmanWielandtNormal
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Analysis.Convex.Birkhoff

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HoffmanWielandtNormal

theorem overlap_doublyStochastic :
    Specs.NumAnalysis206.HoffmanWielandtNormal.overlap_doublyStochastic := by
  intro n u v
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
  · intro i
    rw [v.sum_sq_norm_inner_left, u.norm_eq_one, one_pow]
  · intro j
    rw [u.sum_sq_norm_inner_right, v.norm_eq_one, one_pow]

/-- In a complete eigenbasis the coordinate of the image is multiplied by
its eigenvalue. No reality assumption on that eigenvalue is used. -/
lemma inner_apply_of_eigenbasis {n : ℕ}
    (T : Module.End ℂ (EuclideanSpace ℂ (Fin n)))
    (u : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (lam : Fin n → ℂ) (hT : ∀ i, T (u i) = lam i • u i)
    (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (u i) (T x) = lam i * inner ℂ (u i) x := by
  have hx : T x = ∑ k, (inner ℂ (u k) x * lam k) • u k := by
    calc
      T x = T (∑ k, inner ℂ (u k) x • u k) := congrArg T (u.sum_repr' x).symm
      _ = _ := by simp only [map_sum, map_smul, hT, smul_smul]
  rw [hx, u.orthonormal.inner_right_fintype]
  exact mul_comm _ _

theorem spectral_frobenius_cost :
    Specs.NumAnalysis206.HoffmanWielandtNormal.spectral_frobenius_cost := by
  intro n A B u v lam mu hA hB
  rw [MatrixData.frobeniusNorm_sq_basis (A - B) v]
  calc
    (∑ j, ‖(A - B).toEuclideanLin (v j)‖ ^ 2) =
        ∑ j, ∑ i, ‖inner ℂ (u i) ((A - B).toEuclideanLin (v j))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (u.sum_sq_norm_inner_right _).symm
    _ = ∑ i, ∑ j, ‖lam i - mu j‖ ^ 2 * ‖inner ℂ (u i) (v j)‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hentry : inner ℂ (u i) ((A - B).toEuclideanLin (v j)) =
          (lam i - mu j) * inner ℂ (u i) (v j) := by
        rw [map_sub, LinearMap.sub_apply, inner_sub_right,
          inner_apply_of_eigenbasis A.toEuclideanLin u lam hA, hB,
          inner_smul_right, sub_mul]
      rw [hentry, norm_mul, mul_pow]

/-- A linear cost on a doubly stochastic matrix is at least the cost
of some permutation. This uses Mathlib's Birkhoff decomposition. -/
lemma exists_perm_cost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P C : Matrix ι ι ℝ) (hP : P ∈ doublyStochastic ℝ ι) :
    ∃ p : Equiv.Perm ι, (∑ i, C i (p i)) ≤ ∑ i, ∑ j, C i j * P i j := by
  classical
  obtain ⟨w, hw, hwSum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have hentry (i j : ι) : P i j = ∑ p, w p * p.permMatrix ℝ i j := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hwP
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h.symm
  have hperm (p : Equiv.Perm ι) :
      (∑ i, ∑ j, C i j * p.permMatrix ℝ i j) = ∑ i, C i (p i) := by
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hcost : (∑ p, w p * ∑ i, C i (p i)) = ∑ i, ∑ j, C i j * P i j := by
    simp_rw [← hperm, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hentry, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ
    (fun p : Equiv.Perm ι => ∑ i, C i (p i)) Finset.univ_nonempty
  refine ⟨p, ?_⟩
  calc
    (∑ i, C i (p i)) = ∑ q, w q * (∑ i, C i (p i)) := by
      rw [← Finset.sum_mul, hwSum, one_mul]
    _ ≤ ∑ q, w q * (∑ i, C i (q i)) :=
      Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hp q (Finset.mem_univ _)) (hw q)
    _ = _ := hcost

theorem hoffman_wielandt_normal :
    Specs.NumAnalysis206.HoffmanWielandtNormal.hoffman_wielandt_normal := by
  intro n A B _ _ lam mu u v hA hB
  obtain ⟨p, hp⟩ := exists_perm_cost_le
    (fun i j => ‖inner ℂ (u i) (v j)‖ ^ 2)
    (fun i j => ‖lam i - mu j‖ ^ 2) (overlap_doublyStochastic u v)
  exact ⟨p, hp.trans_eq (spectral_frobenius_cost A B u v lam mu hA hB).symm⟩

end NumAnalysis206.HoffmanWielandtNormal
