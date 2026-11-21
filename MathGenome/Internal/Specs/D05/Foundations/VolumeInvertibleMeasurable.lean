import MathGenome.Internal.Specs.D05.Foundations.VolumeBorelInvertible

/-! The completion step of the linear volume theorem, paper.tex:430.
The underlying measurable space of `CoordinateSpace n` is Borel.
`NullMeasurableSet E volume` is, by definition, measurability in the
sigma-algebra of `volume.completion`, i.e. complete Lebesgue measurability.
Measures take values in `ℝ≥0∞`, with no finite-measure restriction.
Natural dimensions include zero. -/
noncomputable section
open MeasureTheory

namespace D05.VolumeInvertibleMeasurable.Spec
open D05.VolumeElementary

/-- Every invertible real matrix sends complete-Lebesgue-measurable sets to
complete-Lebesgue-measurable sets and scales their measure by its absolute
determinant. No Borel hypothesis is imposed on `E`. -/
def invertibleMeasurableVolume : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∀ (E : Set (CoordinateSpace n)),
    NullMeasurableSet E (volume : Measure (CoordinateSpace n)) →
    NullMeasurableSet (A.mulVec '' E) (volume : Measure (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) =
        ENNReal.ofReal |A.det| * (volume : Measure (CoordinateSpace n)).completion E

end D05.VolumeInvertibleMeasurable.Spec
