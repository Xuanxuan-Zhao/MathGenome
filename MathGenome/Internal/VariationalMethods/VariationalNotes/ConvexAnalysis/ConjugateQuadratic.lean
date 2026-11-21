import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ConjugateQuadratic
import MathGenome.Internal.D05.M14.Pseudoinverse
import Mathlib.Tactic.Ring

noncomputable section
open scoped InnerProductSpace
universe u
namespace VariationalNotes.ConvexAnalysis

def quadraticPseudoinverse {n : Type u} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) : Matrix n n ℝ := Specs.quadraticPseudoinverse Q

def matrixQuadratic {n : Type u} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (x : EuclideanSpace ℝ n) : WithTop ℝ := Specs.matrixQuadratic Q x

theorem matrixQuadratic_coordinates : Specs.matrixQuadratic_coordinates.{u} := by
  intro n _ _ Q x
  simp [Specs.matrixQuadratic, PiLp.inner_apply, Matrix.toLpLin_apply,
    dotProduct, RCLike.inner_apply, mul_comm]

theorem quadratic_range_kernel : Specs.quadratic_range_kernel.{u} := by
  intro n _ _ Q hQ
  have h := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  rw [LinearMap.orthogonal_ker, h.adjoint_eq]

theorem quadratic_pseudoinverse_conventions :
    Specs.quadratic_pseudoinverse_conventions.{u} := by
  intro n _ _ Q hQ
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  have hrange := quadratic_range_kernel Q hQ
  have hp : (Specs.quadraticPseudoinverse Q).toEuclideanLin =
      D05.pseudoinverse Q.toEuclideanLin :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [hp]
  refine ⟨D05.M14.Pseudoinverse.mem_kernel_orthogonal _, ?_, ?_, ?_⟩
  · intro y hy
    rw [D05.M14.Pseudoinverse.map_pseudoinverse]
    exact D05.M12.Projection.fixes_subspace _ _ hy
  · intro x hx
    apply Eq.symm
    apply (D05.M14.Pseudoinverse.characterization _ _ _).mpr
    refine ⟨hx, ?_⟩
    exact (D05.M12.Projection.fixes_subspace _ _ (LinearMap.mem_range_self _ _)).symm
  · intro y hy
    apply Eq.symm
    apply (D05.M14.Pseudoinverse.characterization _ _ _).mpr
    refine ⟨Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    apply Eq.symm
    apply (D05.M12.Projection.component_characterization _ _ _).mpr
    refine ⟨Submodule.zero_mem _, ?_⟩
    simpa only [sub_zero, hsym.orthogonal_range] using hy

/-- Completing the square requires positivity, but no nonsingularity. -/
lemma quadratic_objective_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsPositive)
    (y z : E) (hz : T z = y) (x : E) :
    inner ℝ y x - inner ℝ x (T x) / 2 ≤ inner ℝ y z / 2 := by
  have hn := hT.inner_nonneg_right (x - z)
  simp only [map_sub, inner_sub_left, inner_sub_right] at hn
  rw [← hT.isSymmetric z x, hz, real_inner_comm y x, real_inner_comm y z] at hn
  linarith

theorem conjugate_matrixQuadratic : Specs.conjugate_matrixQuadratic.{u} := by
  classical
  intro n _ _ Q hQ y
  have hT := Matrix.isPositive_toEuclideanLin_iff.mpr hQ
  have hc := quadratic_pseudoinverse_conventions Q hQ.isHermitian
  split_ifs with hy
  · let z := (Specs.quadraticPseudoinverse Q).toEuclideanLin y
    have hz : Q.toEuclideanLin z = y := hc.2.1 y hy
    apply le_antisymm
    · apply iSup₂_le
      intro x hx
      apply EReal.coe_le_coe_iff.mpr
      change inner ℝ y x - inner ℝ x (Q.toEuclideanLin x) / 2 ≤ inner ℝ y z / 2
      exact quadratic_objective_le _ hT y z hz x
    · have hb := conjugate_finite_lower_bound (Specs.matrixQuadratic Q) z
        (inner ℝ z (Q.toEuclideanLin z) / 2) rfl (innerSL ℝ y)
      change ((inner ℝ y z - inner ℝ z (Q.toEuclideanLin z) / 2 : ℝ) : EReal) ≤ _ at hb
      rw [hz, real_inner_comm y z] at hb
      change ((inner ℝ y z / 2 : ℝ) : EReal) ≤ _
      convert hb using 1
      congr 1
      ring
  · have hy' : y ∉ Q.toEuclideanLin.ker.orthogonal := by
      rwa [← quadratic_range_kernel Q hQ.isHermitian]
    rw [Submodule.mem_orthogonal] at hy'
    push Not at hy'
    obtain ⟨k, hk, hky⟩ := hy'
    have hcy : inner ℝ y k ≠ 0 := by rwa [real_inner_comm]
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro r
    let t : ℝ := (r + 1) / inner ℝ y k
    have hval : Specs.matrixQuadratic Q (t • k) = (0 : WithTop ℝ) := by
      have hk' : Q.toEuclideanLin k = 0 := hk
      simp [Specs.matrixQuadratic, map_smul, hk']
    have hb := conjugate_finite_lower_bound (Specs.matrixQuadratic Q) (t • k)
      0 hval (innerSL ℝ y)
    have heval : innerSL ℝ y (t • k) - 0 = r + 1 := by
      change inner ℝ y (t • k) - 0 = r + 1
      simp only [inner_smul_right, sub_zero]
      exact div_mul_cancel₀ (r + 1) hcy
    rw [heval] at hb
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith : r < r + 1)) hb

end VariationalNotes.ConvexAnalysis
