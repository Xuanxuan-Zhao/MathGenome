import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Lemma 4.9 (paper.tex, `lem:nt-minkowski`). The norm and volume here are
those of Euclidean three-space, and the witness uses the given matrix B. -/
namespace P203Specs.Ch04

open MeasureTheory

/-- Every origin-centred open Euclidean ball of volume greater than eight
 times the covolume of Bℤ³ contains a nonzero image of an integer vector. -/
def latticeBall : Prop :=
  ∀ (B : Matrix (Fin 3) (Fin 3) ℝ), B.det ≠ 0 → ∀ r : ℝ,
    8 * |B.det| < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) →
    ∃ z : Fin 3 → ℤ,
      WithLp.toLp 2 (B.mulVec (fun i ↦ (z i : ℝ))) ≠ 0 ∧
      WithLp.toLp 2 (B.mulVec (fun i ↦ (z i : ℝ))) ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r

end P203Specs.Ch04
