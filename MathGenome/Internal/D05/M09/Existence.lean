import MathGenome.Internal.Specs.D05.M09.Existence
import MathGenome.Internal.D05.M09.Existence.IrreducibleDegree
import MathGenome.Internal.D05.M08.EigenRoots
import MathGenome.Internal.D05.Foundations.Fta
import MathGenome.Internal.D05.Foundations.OddRealRoot
import MathGenome.Internal.D05.M05.TriangularBlock
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! K05.09.existence: existence over ℂ and in odd real dimension, and
rotation-block counterexamples in even real dimension, and the
degree-divisibility obstruction for polynomial kernels. -/

noncomputable section

namespace D05.M09.Existence

open Polynomial

theorem complex_exists : Specs.D05.M09.Existence.complex_exists := by
  intro V _ _ _ _ T
  obtain ⟨μ, hμ⟩ := Foundations.Fta.existsRoot
    (Specs.D05.M08.Charpoly.charpoly_value T)
    (by rw [M08.Charpoly.natDegree]; exact Module.finrank_pos)
  refine ⟨μ, ?_⟩
  rw [Module.End.hasEigenvalue_iff, M09.Eigenspace.eigenspace_eq_kernel]
  exact (M08.EigenRoots.kernel_iff_charpoly_root T μ).mpr hμ

theorem real_odd_exists : Specs.D05.M09.Existence.real_odd_exists := by
  intro V _ _ _ T hodd
  obtain ⟨μ, hμ⟩ := Foundations.OddRealRoot.existsRealRoot
    (Specs.D05.M08.Charpoly.charpoly_value T)
    (by rw [M08.Charpoly.natDegree]; exact hodd.pos)
    (by rw [M08.Charpoly.natDegree]; exact hodd)
  refine ⟨μ, ?_⟩
  rw [Module.End.hasEigenvalue_iff, M09.Eigenspace.eigenspace_eq_kernel]
  exact (M08.EigenRoots.kernel_iff_charpoly_root T μ).mpr hμ

theorem rotation_charpoly : Specs.D05.M09.Existence.rotation_charpoly := by
  change (Specs.D05.M09.Existence.rotation).charmatrix.det = _
  rw [Matrix.det_fin_two]
  simp [Specs.D05.M09.Existence.rotation]
  ring

/-- Taking `xI - A` preserves this direct-sum decomposition. -/
theorem charmatrix_blockDiagonal {ι n : Type*} [DecidableEq ι] [DecidableEq n]
    [Fintype ι] [Fintype n]
    (A : ι → Matrix n n ℝ) :
    (Matrix.blockDiagonal A).charmatrix =
      Matrix.blockDiagonal (fun i => (A i).charmatrix) := by
  ext ⟨i, k⟩ ⟨j, l⟩ : 1
  by_cases hkl : k = l
  · subst l
    simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply]
  · simp [Matrix.blockDiagonal_apply, hkl]

theorem rotation_blocks_charpoly : Specs.D05.M09.Existence.rotation_blocks_charpoly := by
  intro m
  change (Matrix.blockDiagonal (fun _ : Fin m =>
    Specs.D05.M09.Existence.rotation)).charmatrix.det = _
  rw [charmatrix_blockDiagonal, Matrix.det_blockDiagonal]
  change (∏ _ : Fin m, Specs.D05.M09.Existence.rotation.charpoly) = _
  rw [rotation_charpoly]
  simp

theorem rotation_blocks_no_roots : Specs.D05.M09.Existence.rotation_blocks_no_roots := by
  intro m x
  rw [rotation_blocks_charpoly]
  simp only [eval_pow, eval_add, eval_X, eval_one]
  exact pow_ne_zero m (ne_of_gt (by positivity : 0 < x ^ 2 + 1))

theorem real_even_counterexample : Specs.D05.M09.Existence.real_even_counterexample := by
  intro V _ _ _ heven
  obtain ⟨m, hm⟩ := heven
  let W := (Fin 2 × Fin m) → ℝ
  have hdim : Module.finrank ℝ W = Module.finrank ℝ V := by
    simp only [W, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    omega
  let e : W ≃ₗ[ℝ] V := LinearEquiv.ofFinrankEq W V hdim
  let T := e.conj (Specs.D05.M09.Existence.rotationBlocks m).toLin'
  have hc : Specs.D05.M08.Charpoly.charpoly_value T =
      ((X : Polynomial ℝ) ^ 2 + 1) ^ m := by
    change (e.conj _).charpoly = _
    rw [e.charpoly_conj, Matrix.charpoly_toLin', rotation_blocks_charpoly]
  refine ⟨T, ?_, ?_⟩
  · rw [hc]
    congr 1
    omega
  · intro μ hμ
    have hroot := (M08.EigenRoots.kernel_iff_charpoly_root T μ).mp
      (by
        change T.eigenspace μ ≠ ⊥ at hμ
        rwa [Module.End.eigenspace_def] at hμ)
    rw [hc] at hroot
    exact pow_ne_zero m (ne_of_gt (by positivity : 0 < μ ^ 2 + 1))
      (by simpa only [eval_pow, eval_add, eval_X, eval_one] using hroot)

theorem real_universal_iff_odd : Specs.D05.M09.Existence.real_universal_iff_odd := by
  intro V _ _ _
  constructor
  · intro hall
    by_contra hodd
    obtain ⟨T, _, hT⟩ := real_even_counterexample (V := V) (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨μ, hμ⟩ := hall T
    exact hT μ hμ
  · intro hodd T
    exact real_odd_exists T hodd

theorem complex_exists_iff_nonzero : Specs.D05.M09.Existence.complex_exists_iff_nonzero := by
  intro V _ _ _ T
  constructor
  · rintro ⟨μ, hμ⟩
    by_contra hdim
    have hz : Module.finrank ℂ V = 0 := Nat.eq_zero_of_not_pos hdim
    have hc := M08.Charpoly.zero_dimensional T hz
    have hr := (M08.EigenRoots.kernel_iff_charpoly_root T μ).mp
      (by
        change T.eigenspace μ ≠ ⊥ at hμ
        rwa [Module.End.eigenspace_def] at hμ)
    rw [hc, eval_one] at hr
    exact one_ne_zero hr
  · intro hdim
    have : Nontrivial V := Module.finrank_pos_iff.mp hdim
    exact complex_exists T

/-- The quotient-field dimension theorem applies to the actual kernel of p(T),
with the shared polynomial evaluation definition. -/
theorem degree_dvd_kernel : Specs.D05.M09.Existence.degree_dvd_kernel := by
  intro K V _ _ _ _ T p hp
  exact IrreducibleDegree.degree_dvd_kernel T p hp

/-- The real quadratic consequence applies without a nonzero-kernel condition. -/
theorem quadratic_kernel_even : Specs.D05.M09.Existence.quadratic_kernel_even := by
  intro V _ _ _ T b c h
  exact IrreducibleDegree.quadratic_kernel_even T b c h

end D05.M09.Existence
