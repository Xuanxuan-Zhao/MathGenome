import MathGenome.Internal.Specs.D05.M14.Positive
import MathGenome.Internal.D05.M13.SelfAdjoint
import MathGenome.Internal.D05.M12.InnerProduct
import Mathlib.Tactic.Linarith

/-! K05.14.positive: definitions, reality of diagonal values, and the real
counterexample showing why self-adjointness is a separate requirement. -/

noncomputable section

namespace D05.M14.Positive

def positiveSemidefinite {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  _root_.D05.positiveSemidefinite T

def positiveDefinite {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  _root_.D05.positiveDefinite T

def identityPlusRotation : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  _root_.D05.identityPlusRotation

theorem selfAdjoint_diagonal_conjugate :
    Specs.D05.M14.Positive.selfAdjoint_diagonal_conjugate := by
  intro F V _ _ _ _ T hT v
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mp hT
  have he : _root_.D05.firstInner (F := F) (T v) v = _root_.D05.firstInner (F := F) v (T v) :=
    (hs v v).symm
  exact ⟨he, he.trans (D05.M12.InnerProduct.firstInner_conjugate (T v) v)⟩

theorem selfAdjoint_diagonal_real :
    Specs.D05.M14.Positive.selfAdjoint_diagonal_real := by
  intro F V _ _ _ _ T hT v
  have he := (selfAdjoint_diagonal_conjugate T hT v).2.symm
  exact ⟨RCLike.conj_eq_iff_im.mp he, RCLike.conj_eq_iff_re.mp he⟩

theorem positiveSemidefinite_iff_mathlib :
    Specs.D05.M14.Positive.positiveSemidefinite_iff_mathlib := by
  intro F V _ _ _ _ T
  change (_root_.D05.selfAdjoint T ∧ ∀ v, 0 ≤ RCLike.re (inner F v (T v))) ↔
    (T.IsSymmetric ∧ ∀ v, 0 ≤ RCLike.re (inner F (T v) v))
  rw [D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric]
  simp only [inner_re_symm (𝕜 := F) (T _) _]

theorem positiveDefinite_implies_semidefinite :
    Specs.D05.M14.Positive.positiveDefinite_implies_semidefinite := by
  intro F V _ _ _ _ T hT
  refine ⟨hT.1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, _root_.D05.firstInner]
  · exact (hT.2 v hv).le

theorem zero_space : Specs.D05.M14.Positive.zero_space := by
  intro F V _ _ _ _ _ T
  have hs : _root_.D05.selfAdjoint T := Subsingleton.elim _ _
  constructor
  · refine ⟨hs, fun v => ?_⟩
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv, _root_.D05.firstInner]
  · exact ⟨hs, fun v hv => (hv (Subsingleton.elim _ _)).elim⟩

theorem rotation_quadratic_zero : Specs.D05.M14.Positive.rotation_quadratic_zero := by
  intro v
  have he := D05.M13.Adjoint.adjoint_identity _root_.D05.planeRotation v v
  rw [D05.M13.SelfAdjoint.rotation_adjoint] at he
  have hs : _root_.D05.firstInner (F := ℝ) v (_root_.D05.planeRotation v) =
      _root_.D05.firstInner (F := ℝ) (_root_.D05.planeRotation v) v := by
    exact real_inner_comm _ _
  simp only [LinearMap.neg_apply, _root_.D05.firstInner, inner_neg_left] at he
  change inner ℝ v (_root_.D05.planeRotation v) = 0
  change inner ℝ (_root_.D05.planeRotation v) v = inner ℝ v (_root_.D05.planeRotation v) at hs
  linarith

theorem identityPlusRotation_quadratic :
    Specs.D05.M14.Positive.identityPlusRotation_quadratic := by
  intro v
  change inner ℝ v (v + _root_.D05.planeRotation v) = ‖v‖ ^ 2
  rw [inner_add_right]
  change inner ℝ v v + _root_.D05.firstInner (F := ℝ) (_root_.D05.planeRotation v) v = _
  rw [rotation_quadratic_zero, add_zero, real_inner_self_eq_norm_sq]

theorem identityPlusRotation_strict_quadratic :
    Specs.D05.M14.Positive.identityPlusRotation_strict_quadratic := by
  intro v hv
  rw [identityPlusRotation_quadratic]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

theorem identityPlusRotation_adjoint :
    Specs.D05.M14.Positive.identityPlusRotation_adjoint := by
  change LinearMap.adjoint (LinearMap.id + _root_.D05.planeRotation) = _
  rw [map_add, LinearMap.adjoint_id, D05.M13.SelfAdjoint.rotation_adjoint, sub_eq_add_neg]

theorem identityPlusRotation_not_selfAdjoint :
    Specs.D05.M14.Positive.identityPlusRotation_not_selfAdjoint := by
  intro h
  change _root_.D05.identityPlusRotation = LinearMap.adjoint _root_.D05.identityPlusRotation at h
  rw [identityPlusRotation_adjoint] at h
  have hj : _root_.D05.planeRotation = -_root_.D05.planeRotation :=
    add_left_cancel (show LinearMap.id + _root_.D05.planeRotation =
      LinearMap.id + -_root_.D05.planeRotation from h)
  apply D05.M13.SelfAdjoint.rotation_not_selfAdjoint
  change _root_.D05.planeRotation = LinearMap.adjoint _root_.D05.planeRotation
  rw [D05.M13.SelfAdjoint.rotation_adjoint]
  exact hj

theorem identityPlusRotation_not_positive :
    Specs.D05.M14.Positive.identityPlusRotation_not_positive := by
  exact ⟨fun h => identityPlusRotation_not_selfAdjoint h.1,
    fun h => identityPlusRotation_not_selfAdjoint h.1⟩

theorem real_quadratic_counterexample :
    Specs.D05.M14.Positive.real_quadratic_counterexample := by
  refine ⟨_root_.D05.identityPlusRotation, identityPlusRotation_quadratic, ?_,
    identityPlusRotation_strict_quadratic, identityPlusRotation_not_selfAdjoint,
    identityPlusRotation_not_positive⟩
  intro v
  rw [identityPlusRotation_quadratic]
  exact sq_nonneg _

end D05.M14.Positive
