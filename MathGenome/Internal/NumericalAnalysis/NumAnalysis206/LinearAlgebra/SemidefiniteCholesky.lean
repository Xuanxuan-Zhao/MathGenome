import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.SemidefiniteCholesky
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace NumAnalysis206.SemidefiniteCholesky
open MatrixData

variable {K : Type*} [RCLike K] {n : ℕ}

/-- Comparison of successive rows uses only their Gram matrices, and so does
not require nonsingularity of either triangular factor. -/
theorem normalized_gram_injective (R S : Mat K n n)
    (hR : SemidefiniteCholeskyNormalization R)
    (hS : SemidefiniteCholeskyNormalization S)
    (hgram : R.conjTranspose * R = S.conjTranspose * S) : R = S := by
  classical
  have hrow : ∀ i : Fin n, ∀ j, R i j = S i j := by
    intro i
    induction i using WellFoundedLT.induction with | ind i ih
    have hpivot (j : Fin n) : star (R i i) * R i j = star (S i i) * S i j := by
      have he := congrArg (fun M : Mat K n n => M i j) hgram
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at he
      have hrest : ∑ k ∈ Finset.univ.erase i, star (R k i) * R k j =
          ∑ k ∈ Finset.univ.erase i, star (S k i) * S k j := by
        apply Finset.sum_congr rfl
        intro k hk
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        rcases lt_or_gt_of_ne hki with hki | hik
        · rw [ih k hki i, ih k hki j]
        · simp only [hR.1 k i hik, hS.1 k i hik, star_zero, zero_mul]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hrest] at he
      exact add_left_cancel he
    have hd : R i i = S i i := by
      obtain ⟨r, hr, her⟩ := hR.2.1 i
      obtain ⟨s, hs, hes⟩ := hS.2.1 i
      have he := hpivot i
      rw [her, hes] at he
      simp only [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul] at he
      have he' : r * r = s * s := RCLike.ofReal_injective he
      have hrs : r = s := by nlinarith
      rw [her, hes, hrs]
    intro j
    by_cases hzero : R i i = 0
    · rw [hR.2.2 i hzero j, hS.2.2 i (hd ▸ hzero) j]
    · have he := hpivot j
      rw [← hd] at he
      exact mul_left_cancel₀ (star_ne_zero.mpr hzero) he
  exact Matrix.ext hrow

section GramSchmidt
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The unnormalized residual has squared norm as its diagonal coefficient. -/
theorem gramSchmidt_inner_diagonal (f : Fin n → E) (i : Fin n) :
    inner K (gramSchmidt K f i) (f i) = (‖gramSchmidt K f i‖ : K) ^ 2 := by
  calc
    _ = inner K (gramSchmidt K f i)
        (gramSchmidt K f i + ∑ k ∈ Finset.Iio i,
          (inner K (gramSchmidt K f k) (f i) / (‖gramSchmidt K f k‖ : K) ^ 2) •
            gramSchmidt K f k) := congrArg _ (gramSchmidt_def'' K f i)
    _ = _ := by
      rw [inner_add_right, inner_sum]
      have hz : ∑ k ∈ Finset.Iio i,
          inner K (gramSchmidt K f i)
            ((inner K (gramSchmidt K f k) (f i) / (‖gramSchmidt K f k‖ : K) ^ 2) •
              gramSchmidt K f k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [inner_smul_right, gramSchmidt_orthogonal K f
          (ne_of_gt (Finset.mem_Iio.mp hk)), mul_zero]
      rw [hz, add_zero, inner_self_eq_norm_sq_to_K]

/-- Extending the nonzero residuals to a basis leaves zero residuals orthogonal
to every original vector; the diagonal remains the nonnegative residual norm. -/
theorem gramSchmidt_basis_diagonal [FiniteDimensional K E]
    (h : Module.finrank K E = Fintype.card (Fin n)) (f : Fin n → E) (i : Fin n) :
    inner K (gramSchmidtOrthonormalBasis h f i) (f i) =
      (‖gramSchmidt K f i‖ : K) := by
  by_cases hn : gramSchmidtNormed K f i = 0
  · have hgs : gramSchmidt K f i = 0 := by
      simpa [gramSchmidtNormed, smul_eq_zero] using hn
    rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hn, hgs, norm_zero,
      RCLike.ofReal_zero]
  · rw [gramSchmidtOrthonormalBasis_apply h hn, gramSchmidtNormed,
      inner_smul_left, RCLike.conj_inv, RCLike.conj_ofReal,
      gramSchmidt_inner_diagonal]
    have hgs : gramSchmidt K f i ≠ 0 := by
      intro hz
      exact hn (by simp [gramSchmidtNormed, hz])
    have hnorm : (‖gramSchmidt K f i‖ : K) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hgs
    field_simp

end GramSchmidt

/-- QR of an arbitrary square matrix, with the zero residual rows retained as
zero rows, supplies a normalized triangular factor of its Gram matrix. -/
theorem exists_normalized_gram_factor (B : Mat K n n) :
    ∃ R : Mat K n n, B.conjTranspose * B = R.conjTranspose * R ∧
      SemidefiniteCholeskyNormalization R := by
  let f := columns B
  have hdim : Module.finrank K (Vec K n) = Fintype.card (Fin n) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  let R : Mat K n n := fun i j => inner K (b i) (f j)
  have hdiag (i : Fin n) : R i i = (‖InnerProductSpace.gramSchmidt K f i‖ : K) :=
    gramSchmidt_basis_diagonal hdim f i
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · ext i j
    change (B.conjTranspose * B) i j = ∑ k, star (inner K (b k) (f i)) *
      inner K (b k) (f j)
    rw [show (B.conjTranspose * B) i j = inner K (f i) (f j) from ?_]
    · symm
      simpa only [RCLike.star_def, inner_conj_symm] using b.sum_inner_mul_inner (f i) (f j)
    · simp only [f, Specs.NumAnalysis206.MatrixData.columns_value,
        NumAnalysis206.MatrixDefinitions.columns,
        D05.QrCholesky.columns, PiLp.inner_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, RCLike.inner_apply, RCLike.star_def, mul_comm]
  · intro i j hji
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hdim f hji
  · intro i
    exact ⟨_, norm_nonneg _, hdiag i⟩
  · intro i hi j
    have hgs : InnerProductSpace.gramSchmidt K f i = 0 := by
      have hz := (hdiag i).symm.trans hi
      exact norm_eq_zero.mp (RCLike.ofReal_eq_zero.mp hz)
    exact InnerProductSpace.inner_gramSchmidtOrthonormalBasis_eq_zero hdim
      (by simp [InnerProductSpace.gramSchmidtNormed, hgs]) j

/-- Canonical semidefinite Cholesky, including the empty matrix. -/
theorem exists_unique_cholesky : Specs.NumAnalysis206.SemidefiniteCholesky.exists_unique_cholesky := by
  intro K _ n A hA
  let B := CFC.sqrt A
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : B.conjTranspose * B = A := by
    rw [hB.isHermitian.eq, ← pow_two]
    exact CFC.sq_sqrt A hA.nonneg
  obtain ⟨R, hR, hnorm⟩ := exists_normalized_gram_factor B
  refine ⟨R, ⟨hsq.symm.trans hR, hnorm⟩, ?_⟩
  intro S hS
  exact normalized_gram_injective S R hS.2 hnorm (hS.1.symm.trans (hsq.symm.trans hR))

/-- Without the zero-row convention, the source's two upper triangular
nonnegative-diagonal factors of diag(0,1) are different. -/
theorem unnormalized_nonunique : Specs.NumAnalysis206.SemidefiniteCholesky.unnormalized_nonunique := by
  intro K _
  let A : Mat K 2 2 := !![0, 0; 0, 1]
  let S : Mat K 2 2 := !![0, 1; 0, 0]
  change A.PosSemidef ∧ A = adjoint A * A ∧ A = adjoint S * S ∧
    IsUpperTriangular A ∧ NonnegativeRealDiagonal A ∧
    IsUpperTriangular S ∧ NonnegativeRealDiagonal S ∧
    A ≠ S ∧ ¬ SemidefiniteCholeskyNormalization S
  have hAA : A = adjoint A * A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, adjoint, MatrixDefinitions.adjoint, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
  have hSS : A = adjoint S * S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, S, adjoint, MatrixDefinitions.adjoint, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
  refine ⟨?_, hAA, hSS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAA]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  · intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num [A] at *
  · intro i
    fin_cases i
    · exact ⟨0, le_rfl, by simp [A]⟩
    · exact ⟨1, zero_le_one, by simp [A]⟩
  · intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num [S] at *
  · intro i
    refine ⟨0, le_rfl, ?_⟩
    fin_cases i <;> simp [S]
  · intro he
    have hz := congrArg (fun M : Mat K 2 2 => M 0 1) he
    simp [A, S] at hz
  · intro hnorm
    have hz := hnorm.2.2 0 (by rfl) 1
    simp [S] at hz

end NumAnalysis206.SemidefiniteCholesky
