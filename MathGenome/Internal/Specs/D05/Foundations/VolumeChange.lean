import MathGenome.Internal.Specs.D05.Foundations.VolumeInvertibleMeasurable
import MathGenome.Internal.Specs.D05.Foundations.VolumeSingular

/-! Independent statements for the linear change of volume theorem,
`paper.tex:420–433`. The canonical coordinates are `Fin n → ℝ`.

`volume` on these coordinates is Borel product Lebesgue measure;
`NullMeasurableSet E volume` means that `E` is measurable in its completion.
All displayed measures below are explicitly completed and take values in
`ℝ≥0∞`. No finite-measure or positive-dimension hypothesis is imposed.
-/

noncomputable section
open MeasureTheory Set

namespace D05.VolumeChange.Spec
open D05.VolumeElementary

/-- The Borel-null-cover mechanism for the passage to complete measure.
The image of a complete-measurable set differs from a Borel image only
inside the image of a containing Borel null set. -/
def borelNullCoverImages : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∀ E : Set (CoordinateSpace n),
    NullMeasurableSet E (volume : Measure (CoordinateSpace n)) →
    ∃ B N : Set (CoordinateSpace n),
      MeasurableSet B ∧ B ⊆ E ∧ MeasurableSet N ∧
      (volume : Measure (CoordinateSpace n)).completion N = 0 ∧ E \ B ⊆ N ∧
      MeasurableSet (A.mulVec '' B) ∧ MeasurableSet (A.mulVec '' N) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' N) = 0 ∧
      A.mulVec '' (E \ B) ⊆ A.mulVec '' N ∧
      (A.mulVec '' E =ᵐ[volume] A.mulVec '' B)

/-- The invertible case, with the real determinant multiplier embedded in
extended nonnegative reals. -/
def invertibleVolume : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∀ E : Set (CoordinateSpace n),
    NullMeasurableSet E (volume : Measure (CoordinateSpace n)) →
    NullMeasurableSet (A.mulVec '' E) (volume : Measure (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) =
        ENNReal.ofReal |A.det| * (volume : Measure (CoordinateSpace n)).completion E

/-- Singular images lie in a proper null linear subspace and are measurable
and null themselves. This is a separate assertion, with no assumption on `E`.
In particular it covers measurable sets of infinite measure. -/
def singularVolume : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), A.det = 0 →
    ∀ E : Set (CoordinateSpace n),
    ∃ U : Submodule ℝ (CoordinateSpace n),
      U ≠ ⊤ ∧ A.mulVec '' E ⊆ (U : Set (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (U : Set (CoordinateSpace n)) = 0 ∧
      NullMeasurableSet (A.mulVec '' E) (volume : Measure (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) = 0

/-- In dimension zero the sole point, and hence the whole space, has mass one. -/
def zeroDimensionalVolume : Prop :=
  (∀ x : CoordinateSpace 0,
    (volume : Measure (CoordinateSpace 0)).completion ({x} : Set (CoordinateSpace 0)) = 1) ∧
  (volume : Measure (CoordinateSpace 0)).completion (univ : Set (CoordinateSpace 0)) = 1

end D05.VolumeChange.Spec
