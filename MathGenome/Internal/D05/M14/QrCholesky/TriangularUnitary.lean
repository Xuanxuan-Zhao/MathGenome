import MathGenome.Internal.Specs.D05.M14.QrCholesky.TriangularUnitary
import Mathlib.Tactic.Linarith

/-! Upper triangular inverses and unitary matrices, K05.14.qr_cholesky. -/

noncomputable section

namespace D05.M14.QrCholesky.TriangularUnitary

theorem unitary_criterion :
    Specs.D05.M14.QrCholesky.TriangularUnitary.unitary_criterion := by
  intro F _ n C
  exact Matrix.mem_unitaryGroup_iff'

theorem upper_triangular_inverse :
    Specs.D05.M14.QrCholesky.TriangularUnitary.upper_triangular_inverse := by
  intro K _ n A hA hunit
  let := hunit.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

theorem nonzero_diagonal_inverse :
    Specs.D05.M14.QrCholesky.TriangularUnitary.nonzero_diagonal_inverse := by
  intro K _ n A hA hd
  have hdet : A.det ≠ 0 := hA.det_ne_zero_iff.mpr hd
  have hunitdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hunitdet
  exact ⟨hunit, upper_triangular_inverse A hA hunit,
    Matrix.nonsing_inv_mul A hunitdet, Matrix.mul_nonsing_inv A hunitdet⟩

/-- The conjugate transpose is the inverse, hence upper triangular too.
Together with triangularity of C this eliminates both off-diagonal halves. -/
theorem upper_triangular_unitary :
    Specs.D05.M14.QrCholesky.TriangularUnitary.upper_triangular_unitary := by
  intro F _ n C hC hu
  have hinv : C⁻¹ = C.conjTranspose := Matrix.inv_eq_left_inv hu
  let := invertibleOfLeftInverse C C.conjTranspose hu
  have hstar : C.conjTranspose.IsUpperTriangular := by
    rw [← hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hC
  have hoff (i j : Fin n) (hij : i ≠ j) : C i j = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hs := hstar hlt
      simpa using hs
    · exact hC hgt
  have hdiag : C = Matrix.diagonal (fun i => C i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij, hoff i j hij]
  refine ⟨hdiag, ?_⟩
  intro i
  have hi := congrArg (fun A : Matrix (Fin n) (Fin n) F => A i i) hu
  rw [hdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at hi
  have hprod : star (C i i) * C i i = 1 := by simpa using hi
  have hn : ‖C i i‖ * ‖C i i‖ = 1 := by
    simpa only [norm_mul, norm_star, norm_one] using congrArg norm hprod
  have hp := norm_nonneg (C i i)
  nlinarith

theorem positive_diagonal_unitary :
    Specs.D05.M14.QrCholesky.TriangularUnitary.positive_diagonal_unitary := by
  intro F _ n C hC hu hpos
  obtain ⟨hdiag, hnorm⟩ := upper_triangular_unitary C hC hu
  have hd (i : Fin n) : C i i = 1 := by
    obtain ⟨r, hr, heq⟩ := hpos i
    have hn := hnorm i
    rw [heq, RCLike.norm_ofReal, abs_of_pos hr] at hn
    rw [heq, hn]
    simp
  rw [hdiag]
  simpa only [hd] using (Matrix.diagonal_one : Matrix.diagonal (fun _ : Fin n => (1 : F)) = 1)

theorem empty_matrix :
    Specs.D05.M14.QrCholesky.TriangularUnitary.empty_matrix := by
  intro F _ C
  refine ⟨Subsingleton.elim _ _, ?_, Subsingleton.elim _ _, ?_⟩ <;>
    intro i j h <;> exact Fin.elim0 i

end D05.M14.QrCholesky.TriangularUnitary
