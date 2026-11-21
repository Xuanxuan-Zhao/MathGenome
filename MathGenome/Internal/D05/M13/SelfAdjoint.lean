import MathGenome.Internal.Specs.D05.M13.SelfAdjoint
import MathGenome.Internal.D05.M13.AdjointLaws
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! K05.13.self_adjoint: definitions and the real-plane rotation counterexample. -/

noncomputable section

namespace D05.M13.SelfAdjoint

def selfAdjoint {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  _root_.D05.selfAdjoint T

def normalOperator {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  _root_.D05.normalOperator T

def planeRotationMatrix : Matrix (Fin 2) (Fin 2) ℝ := _root_.D05.planeRotationMatrix

def planeRotation : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  _root_.D05.planeRotation

theorem selfAdjoint_iff_mathlib : Specs.D05.M13.SelfAdjoint.selfAdjoint_iff_mathlib := by
  intro F V _ _ _ _ T
  exact eq_comm

theorem selfAdjoint_iff_isSymmetric :
    Specs.D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric := by
  intro F V _ _ _ _ T
  exact (selfAdjoint_iff_mathlib T).trans (LinearMap.isSymmetric_iff_isSelfAdjoint T).symm

theorem normalOperator_iff_mathlib :
    Specs.D05.M13.SelfAdjoint.normalOperator_iff_mathlib := by
  intro F V _ _ _ _ T
  change T.comp T.adjoint = T.adjoint.comp T ↔ IsStarNormal T
  rw [isStarNormal_iff, commute_iff_eq]
  exact eq_comm

theorem selfAdjoint_implies_normal :
    Specs.D05.M13.SelfAdjoint.selfAdjoint_implies_normal := by
  intro F V _ _ _ _ T hT
  change T = T.adjoint at hT
  change T.comp T.adjoint = T.adjoint.comp T
  rw [← hT]

theorem rotation_matrix : Specs.D05.M13.SelfAdjoint.rotation_matrix := by
  exact LinearMap.toMatrix_toLin _ _ _

private theorem rotation_conjTranspose :
    _root_.D05.planeRotationMatrix.conjTranspose = -_root_.D05.planeRotationMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.D05.planeRotationMatrix, Matrix.conjTranspose_apply]

theorem rotation_adjoint : Specs.D05.M13.SelfAdjoint.rotation_adjoint := by
  change (Matrix.toEuclideanLin _root_.D05.planeRotationMatrix).adjoint =
    -(Matrix.toEuclideanLin _root_.D05.planeRotationMatrix)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, rotation_conjTranspose, map_neg]

private theorem rotation_apply_zero (v : EuclideanSpace ℝ (Fin 2)) :
    _root_.D05.planeRotation v 0 = -v 1 := by
  simp [_root_.D05.planeRotation, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, _root_.D05.planeRotationMatrix]

private theorem rotation_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    _root_.D05.planeRotation v 1 = v 0 := by
  simp [_root_.D05.planeRotation, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, _root_.D05.planeRotationMatrix]

theorem rotation_products : Specs.D05.M13.SelfAdjoint.rotation_products := by
  change _root_.D05.planeRotation.comp _ = LinearMap.id ∧
    (LinearMap.adjoint _root_.D05.planeRotation).comp _ = LinearMap.id
  rw [rotation_adjoint]
  constructor <;> ext v i <;> fin_cases i <;>
    simp [rotation_apply_zero, rotation_apply_one]

theorem rotation_normal : Specs.D05.M13.SelfAdjoint.rotation_normal := by
  exact rotation_products.1.trans rotation_products.2.symm

theorem rotation_not_selfAdjoint : Specs.D05.M13.SelfAdjoint.rotation_not_selfAdjoint := by
  intro h
  change _root_.D05.planeRotation = LinearMap.adjoint _root_.D05.planeRotation at h
  rw [rotation_adjoint] at h
  have h' := congrArg (fun T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) =>
    T (WithLp.toLp 2 ![1, 0]) 1) h
  norm_num [rotation_apply_one] at h'

theorem rotation_charpoly : Specs.D05.M13.SelfAdjoint.rotation_charpoly := by
  rw [Specs.D05.M13.SelfAdjoint.rotation_charpoly, Matrix.charpoly_fin_two]
  norm_num [_root_.D05.planeRotationMatrix, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.det_fin_two]

theorem rotation_det_sub : Specs.D05.M13.SelfAdjoint.rotation_det_sub := by
  intro t
  norm_num [Matrix.det_fin_two, _root_.D05.planeRotationMatrix, pow_two]

theorem rotation_no_real_root : Specs.D05.M13.SelfAdjoint.rotation_no_real_root := by
  intro t ht
  rw [rotation_charpoly] at ht
  have hz : t ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using ht
  nlinarith [sq_nonneg t]

theorem rotation_no_real_eigenvector :
    Specs.D05.M13.SelfAdjoint.rotation_no_real_eigenvector := by
  intro t v hv
  have h₀ := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hv
  have h₁ := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hv
  have h₀' : -v 1 = t * v 0 := by simpa [rotation_apply_zero] using h₀
  have h₁' : v 0 = t * v 1 := by simpa [rotation_apply_one] using h₁
  have hn : t ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg t]
  have he : (t ^ 2 + 1) * v 1 = 0 := by
    nlinarith [congrArg (fun r : ℝ => t * r) h₁']
  have hz : v 1 = 0 := (mul_eq_zero.mp he).resolve_left hn
  ext i
  fin_cases i <;> simp_all

theorem rotation_no_real_eigenbasis :
    Specs.D05.M13.SelfAdjoint.rotation_no_real_eigenbasis := by
  intro ι ⟨b, hb⟩
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨t, ht⟩ := hb i
  exact b.ne_zero i (rotation_no_real_eigenvector t (b i) ht)

theorem real_normal_counterexample :
    Specs.D05.M13.SelfAdjoint.real_normal_counterexample := by
  exact ⟨_root_.D05.planeRotation, rotation_normal, rotation_not_selfAdjoint,
    rotation_no_real_eigenbasis⟩

end D05.M13.SelfAdjoint
