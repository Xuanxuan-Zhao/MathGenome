import MathGenome.Internal.Specs.D05.Foundations.VolumeInvertibleMeasurable
import MathGenome.Internal.D05.Foundations.VolumeBorelInvertible

/-! Extend the proved Borel rule by a Borel null cover and completeness.
No general linear change-of-variables theorem is used. -/
noncomputable section
open MeasureTheory Set

namespace D05.VolumeInvertibleMeasurable
open D05.VolumeElementary

/-- A Lebesgue-measurable set consists of a Borel core together with a
subset of a Borel null set. The construction also works at infinite measure. -/
theorem borelNullDecomposition (n : ℕ) (E : Set (CoordinateSpace n))
    (hE : NullMeasurableSet E (volume : Measure (CoordinateSpace n))) :
    ∃ B N : Set (CoordinateSpace n), MeasurableSet B ∧ MeasurableSet N ∧
      (volume : Measure (CoordinateSpace n)) N = 0 ∧ B ⊆ E ∧ E \ B ⊆ N := by
  obtain ⟨B, hBE, hB, hEq⟩ := hE.exists_measurable_subset_ae_eq
  have hnull : (volume : Measure (CoordinateSpace n)) (E \ B) = 0 :=
    ae_le_set.mp hEq.symm.le
  refine ⟨B, toMeasurable volume (E \ B), hB,
    measurableSet_toMeasurable _ _, ?_, hBE, subset_toMeasurable _ _⟩
  rw [measure_toMeasurable, hnull]

/-- The Borel formula sends the null cover to a Borel null set, so arbitrary
subsets of its image are measurable in the completed measure. -/
theorem invertibleMeasurableVolume : Spec.invertibleMeasurableVolume := by
  intro n A hA E hE
  obtain ⟨B, N, hB, hN, hNzero, hBE, hcover⟩ := borelNullDecomposition n E hE
  obtain ⟨hAB, hvolB⟩ := D05.VolumeBorelInvertible.invertibleBorelVolume n A hA B hB
  obtain ⟨hAN, hvolN⟩ := D05.VolumeBorelInvertible.invertibleBorelVolume n A hA N hN
  have hANzero : (volume : Measure (CoordinateSpace n)) (A.mulVec '' N) = 0 := by
    change volume (A.mulVec '' N) = ENNReal.ofReal |A.det| * volume N at hvolN
    simpa only [hNzero, mul_zero] using hvolN
  have hrestzero : (volume : Measure (CoordinateSpace n)) (A.mulVec '' (E \ B)) = 0 :=
    measure_mono_null (image_mono hcover) hANzero
  have hsplit : E = B ∪ (E \ B) := by
    rw [union_sdiff_self, union_eq_right.mpr hBE]
  have himageEq : A.mulVec '' E =ᵐ[volume] A.mulVec '' B := by
    rw [hsplit, image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hrestzero)
  refine ⟨hAB.nullMeasurableSet.congr himageEq.symm, ?_⟩
  have hEvol : (volume : Measure (CoordinateSpace n)) E = volume B := by
    exact (measure_eq_measure_of_null_sdiff hBE (measure_mono_null hcover hNzero)).symm
  change volume (A.mulVec '' E) = ENNReal.ofReal |A.det| * volume E
  change volume (A.mulVec '' B) = ENNReal.ofReal |A.det| * volume B at hvolB
  rw [measure_congr himageEq, hEvol]
  exact hvolB

end D05.VolumeInvertibleMeasurable
