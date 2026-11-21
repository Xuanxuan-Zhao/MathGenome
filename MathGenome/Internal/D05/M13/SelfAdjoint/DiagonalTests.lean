import MathGenome.Internal.Specs.D05.M13.SelfAdjoint.DiagonalTests
import MathGenome.Internal.D05.M13.SelfAdjoint

/-! Diagonal tests, with the paper's first-slot-linear inner product. -/

namespace D05.M13.SelfAdjoint.DiagonalTests

theorem selfAdjoint_zero_of_diagonal_zero :
    Specs.D05.M13.SelfAdjoint.DiagonalTests.selfAdjoint_zero_of_diagonal_zero := by
  intro F V _ _ _ _ D hD h
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric D).mp hD
  apply hs.inner_map_self_eq_zero.mp
  intro v
  exact inner_eq_zero_symm.mpr (h v)

theorem complex_diagonal_zero_iff :
    Specs.D05.M13.SelfAdjoint.DiagonalTests.complex_diagonal_zero_iff := by
  intro V _ _ _ T
  constructor
  · intro h
    apply (_root_.inner_map_self_eq_zero T).mp
    intro v
    exact inner_eq_zero_symm.mpr (h v)
  · rintro rfl v
    simp [D05.firstInner]

theorem complex_diagonal_real_iff :
    Specs.D05.M13.SelfAdjoint.DiagonalTests.complex_diagonal_real_iff := by
  intro V _ _ _ T
  rw [D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  constructor
  · intro h v
    obtain ⟨r, hr⟩ := h v
    have hv : inner ℂ (T v) v = (r : ℂ) := by
      rw [← inner_conj_symm (T v) v]
      change starRingEnd ℂ (D05.firstInner (F := ℂ) (T v) v) = (r : ℂ)
      rw [hr]
      simp
    rw [hv]
    simp
  · intro h v
    refine ⟨(inner ℂ (T v) v).re, ?_⟩
    change inner ℂ v (T v) = _
    rw [← inner_conj_symm v (T v), h v]
    exact (RCLike.conj_eq_iff_re.mp (h v)).symm

theorem rotation_diagonal_zero :
    Specs.D05.M13.SelfAdjoint.DiagonalTests.rotation_diagonal_zero := by
  intro v
  have ha := LinearMap.adjoint_inner_right D05.planeRotation v v
  rw [D05.M13.SelfAdjoint.rotation_adjoint] at ha
  have hr : inner ℝ v (D05.planeRotation v) = 0 := by
    simp only [LinearMap.neg_apply, inner_neg_right, real_inner_comm] at ha
    linarith
  exact hr

theorem real_zero_diagonal_counterexample :
    Specs.D05.M13.SelfAdjoint.DiagonalTests.real_zero_diagonal_counterexample := by
  refine ⟨D05.planeRotation, ?_, rotation_diagonal_zero⟩
  intro hz
  apply D05.M13.SelfAdjoint.rotation_not_selfAdjoint
  change D05.planeRotation = LinearMap.adjoint D05.planeRotation
  simp [hz]

end D05.M13.SelfAdjoint.DiagonalTests
