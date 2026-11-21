import MathGenome.Internal.Specs.D05.Foundations.VolumeElementary
import MathGenome.Internal.Specs.D05.M01.Elimination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The invertible Borel part of paper.tex:430. Coordinates are columns;
`volume.completion` denotes complete Lebesgue measure, valued in `ℝ≥0∞`.
The measurable space on the finite real product is its Borel measurable space.
No finite-measure or positive-dimension restriction is imposed. -/
noncomputable section
open MeasureTheory

namespace D05.VolumeBorelInvertible.Spec
open D05.VolumeElementary D05.M01.RowOps D05.M01.Elimination

/-- A finite elementary factorization, in chronological row-operation order.
Each factor is the elementary matrix of a permitted operation. -/
def elementaryFactorization : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∃ ops : List (RowOperation ℝ n), applyOps ops 1 = A

/-- Borel images and the complete Lebesgue measure formula, also for sets of
infinite measure and for the unique zero-dimensional coordinate tuple. -/
def invertibleBorelVolume : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∀ (E : Set (CoordinateSpace n)), MeasurableSet E →
    MeasurableSet (A.mulVec '' E) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) =
        ENNReal.ofReal |A.det| * (volume : Measure (CoordinateSpace n)).completion E

end D05.VolumeBorelInvertible.Spec
