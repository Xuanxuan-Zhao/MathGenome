import MathGenome.Internal.Specs.D05.Foundations.VolumeBorelInvertible
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Independent obligations for paper.tex:432. Coordinates and complete Lebesgue
measure are exactly those of the elementary and invertible-volume interfaces.
Measurability in the completion is stated explicitly, rather than Borel
measurability, which need not hold for an arbitrary subset of a null subspace. -/
noncomputable section
open MeasureTheory Set
namespace D05.VolumeSingular.Spec
open D05.VolumeElementary

def coordinateHyperplaneNull : Prop := ∀ (n : ℕ) (i : Fin n),
  (volume : Measure (CoordinateSpace n)).completion {x | x i = 0} = 0

def subspaceTransport : Prop := ∀ (n : ℕ) (U : Submodule ℝ (CoordinateSpace n)),
  U ≠ ⊤ → ∃ (e : CoordinateSpace n ≃ₗ[ℝ] CoordinateSpace n) (i : Fin n),
    ∀ x ∈ U, e x i = 0

def properSubspaceNull : Prop := ∀ (n : ℕ) (U : Submodule ℝ (CoordinateSpace n)),
  U ≠ ⊤ → (volume : Measure (CoordinateSpace n)).completion (U : Set (CoordinateSpace n)) = 0

def subsetProperSubspace : Prop := ∀ (n : ℕ) (U : Submodule ℝ (CoordinateSpace n)),
  U ≠ ⊤ → ∀ S : Set (CoordinateSpace n), S ⊆ U →
    @MeasurableSet (NullMeasurableSpace _ (volume : Measure (CoordinateSpace n))) inferInstance S ∧
    (volume : Measure (CoordinateSpace n)).completion S = 0

def singularRangeProper : Prop := ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
  A.det = 0 → LinearMap.range A.mulVecLin ≠ ⊤

def singularSubsets : Prop := ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
  A.det = 0 → ∀ S : Set (CoordinateSpace n), S ⊆ Set.range A.mulVec →
    @MeasurableSet (NullMeasurableSpace _ (volume : Measure (CoordinateSpace n))) inferInstance S ∧
    (volume : Measure (CoordinateSpace n)).completion S = 0

/-- No measurability assumption on the original set is required. -/
def singularImages : Prop := ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
  A.det = 0 → ∀ E : Set (CoordinateSpace n),
    @MeasurableSet (NullMeasurableSpace _ (volume : Measure (CoordinateSpace n))) inferInstance
      (A.mulVec '' E) ∧
    (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) = 0

def zeroDimensionalNonsingular : Prop := ∀ (A : Matrix (Fin 0) (Fin 0) ℝ),
  A.det = 1 ∧ IsUnit A
end D05.VolumeSingular.Spec
