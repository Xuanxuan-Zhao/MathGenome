import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.LatticeBall
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.LinearAlgebra.Countable
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace P203.Ch04

open MeasureTheory Module

private def matrixEquiv (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :=
  B.toLinearEquiv (Pi.basisFun ℝ (Fin 3)) (isUnit_iff_ne_zero.mpr hB)

private theorem matrixEquiv_apply (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0)
    (v : Fin 3 → ℝ) : matrixEquiv B hB v = B.mulVec v := by
  simp [matrixEquiv, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

private def matrixBasis (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :=
  (Pi.basisFun ℝ (Fin 3)).map (matrixEquiv B hB)

private theorem matrixBasis_volume (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.det ≠ 0) :
    volume (ZSpan.fundamentalDomain (matrixBasis B hB)) = ENNReal.ofReal |B.det| := by
  rw [ZSpan.volume_fundamentalDomain]
  have heq : Matrix.of (matrixBasis B hB) = B.transpose := by
    ext i j
    simp [matrixBasis, matrixEquiv_apply, Pi.basisFun_apply, Matrix.mulVec_single]
  rw [heq, Matrix.det_transpose]

/-- Lemma 4.9: the strict Minkowski bound for the lattice given by B. -/
theorem minkowski_ball : P203Specs.Ch04.latticeBall := by
  classical
  intro B hB r hvol
  let b := matrixBasis B hB
  let L := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  let : Countable L := inferInstanceAs
    (Countable (Submodule.span ℤ (Set.range b)))
  let s : Set (Fin 3 → ℝ) := WithLp.toLp 2 ⁻¹'
    Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r
  have hsvol : volume s = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) :=
    (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
      Metric.isOpen_ball.measurableSet.nullMeasurableSet
  have hpos : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) :=
    lt_of_le_of_lt (by positivity) hvol
  have hmeasure : volume (ZSpan.fundamentalDomain b) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume s := by
    rw [show b = matrixBasis B hB from rfl, matrixBasis_volume, Module.finrank_pi]
    norm_num only [Fintype.card_fin, pow_succ, pow_zero, mul_one]
    calc
      ENNReal.ofReal |B.det| * 8 =
          ENNReal.ofReal (8 * |B.det|) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num
        ring
      _ < ENNReal.ofReal (volume.real
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)) :=
        (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hvol
      _ ≤ volume s := by
        rw [hsvol]
        exact ENNReal.ofReal_toReal_le
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simpa [s, Metric.mem_ball, dist_zero_right] using hx
  have hconv : Convex ℝ s :=
    (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) r).linear_preimage
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  obtain ⟨x, hxzero, hxball⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L) (ZSpan.isAddFundamentalDomain' b volume) hsymm hconv hmeasure
  have hxcoords := (b.mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)).mp x.property
  choose z hz using hxcoords
  have hcoords : (fun i ↦ (z i : ℝ)) = (matrixEquiv B hB).symm (x : Fin 3 → ℝ) := by
    funext i
    simpa [b, matrixBasis, Basis.map_repr] using hz i
  have hximage : B.mulVec (fun i ↦ (z i : ℝ)) = (x : Fin 3 → ℝ) := by
    rw [hcoords, ← matrixEquiv_apply B hB, LinearEquiv.apply_symm_apply]
  refine ⟨z, ?_, ?_⟩
  · rw [hximage]
    intro h
    apply hxzero
    apply Subtype.ext
    simpa using congrArg WithLp.ofLp h
  · simpa only [hximage] using (show WithLp.toLp 2 (x : Fin 3 → ℝ) ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r from hxball)

end P203.Ch04
