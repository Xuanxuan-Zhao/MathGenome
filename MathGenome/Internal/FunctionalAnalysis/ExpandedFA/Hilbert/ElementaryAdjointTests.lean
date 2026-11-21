import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ElementaryAdjointTests
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Elementary adjoint tests (`paper.tex` 7878–7889).

The complex converse uses polarization through the library's symmetric-operator
criterion; normality is never assumed. The real rotation is verified directly
in orthonormal coordinates, including its skew-adjoint identity. Composition
reversal proves the product criterion, and continuity of the adjoint makes its
fixed set closed in operator norm.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.ElementaryAdjointTests
universe u v

theorem complex_quadratic_criterion : Spec.ComplexQuadraticCriterion.{v} := by
  intro H _ _ _ T
  constructor
  · intro h x
    have hs : IsSelfAdjoint T := h.symm
    exact hs.isSymmetric.im_inner_self_apply x
  · intro h
    have hs : T.toLinearMap.IsSymmetric :=
      (LinearMap.isSymmetric_iff_inner_map_self_real T.toLinearMap).mpr (by
        intro x
        change conj ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ
        simpa only [inner_conj_symm] using
          (Complex.conj_eq_iff_im.mpr (h x)).symm)
    exact hs.isSelfAdjoint.adjoint_eq.symm

/-- The bounded ninety-degree rotation on the real Euclidean plane. -/
def realPlaneRotation : Spec.RotationType := Spec.RotationValue

theorem real_rotation_counterexample : Spec.RealRotationCounterexample := by
  let J := Spec.RotationValue
  have hcoords (x : EuclideanSpace ℝ (Fin 2)) : J x 0 = -x 1 ∧ J x 1 = x 0 := by
    constructor <;>
      simp [J, Spec.RotationValue, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        dotProduct, Fin.sum_univ_two]
  have hne : J ≠ 0 := by
    intro h
    have hc := (hcoords (WithLp.toLp 2 ![(1 : ℝ), 0])).2
    rw [h] at hc
    norm_num at hc
  have hq (x : EuclideanSpace ℝ (Fin 2)) : ⟪x, J x⟫_ℝ = 0 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      RCLike.conj_to_real, (hcoords x).1, (hcoords x).2]
    ring
  have hadj : ContinuousLinearMap.adjoint J = -J := by
    apply Eq.symm
    apply (ContinuousLinearMap.eq_adjoint_iff (-J) J).mpr
    intro x y
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      RCLike.conj_to_real, neg_apply, PiLp.neg_apply,
      (hcoords x).1, (hcoords x).2, (hcoords y).1, (hcoords y).2]
    ring
  have hnot : J ≠ ContinuousLinearMap.adjoint J := by
    intro h
    have hc := congrArg
      (fun T : Spec.RotationType => T (WithLp.toLp 2 ![(1 : ℝ), 0]) 1) (h.trans hadj)
    simp only [neg_apply, PiLp.neg_apply, (hcoords _).2] at hc
    norm_num at hc
  exact ⟨hcoords, hne, hq, hadj, hnot⟩

theorem product_selfAdjoint_iff_commute : Spec.ProductCriterion.{u, v} := by
  intro 𝕜 H _ _ _ _ S T hS hT
  change S = S.adjoint at hS
  change T = T.adjoint at hT
  change S.comp T = (S.comp T).adjoint ↔ S.comp T = T.comp S
  rw [ContinuousLinearMap.adjoint_comp, ← hS, ← hT]

theorem selfAdjoint_isClosed : Spec.SelfAdjointClosed.{u, v} := by
  intro 𝕜 H _ _ _ _
  exact isClosed_eq continuous_id ContinuousLinearMap.adjoint.continuous

end ExpandedFA.Hilbert.ElementaryAdjointTests
