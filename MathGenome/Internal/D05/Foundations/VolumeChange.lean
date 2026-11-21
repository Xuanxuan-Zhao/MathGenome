import MathGenome.Internal.Specs.D05.Foundations.VolumeChange
import MathGenome.Internal.D05.Foundations.VolumeInvertibleMeasurable
import MathGenome.Internal.D05.Foundations.VolumeSingular

/-! Assembly of the linear change of volume theorem (`paper.tex:420–433`).
The invertible rule was proved by elementary factorization and completion;
the singular rule by transport of a proper subspace to a null hyperplane.
The completion mechanism is also recorded explicitly below.
-/

noncomputable section
open MeasureTheory Set

namespace D05.VolumeChange
open D05.VolumeElementary

theorem borelNullCoverImages : Spec.borelNullCoverImages := by
  intro n A hA E hE
  obtain ⟨B, N, hB, hN, hNzero, hBE, hcover⟩ :=
    D05.VolumeInvertibleMeasurable.borelNullDecomposition n E hE
  obtain ⟨hAB, _⟩ :=
    D05.VolumeBorelInvertible.invertibleBorelVolume n A hA B hB
  obtain ⟨hAN, hvolN⟩ :=
    D05.VolumeBorelInvertible.invertibleBorelVolume n A hA N hN
  have hANzero : (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' N) = 0 := by
    simpa only [show (volume : Measure (CoordinateSpace n)).completion N = 0 from hNzero,
      mul_zero] using hvolN
  have hsub : A.mulVec '' (E \ B) ⊆ A.mulVec '' N := image_mono hcover
  have hrestzero : (volume : Measure (CoordinateSpace n)) (A.mulVec '' (E \ B)) = 0 :=
    measure_mono_null hsub hANzero
  have hsplit : E = B ∪ (E \ B) := by
    rw [union_sdiff_self, union_eq_right.mpr hBE]
  refine ⟨B, N, hB, hBE, hN, hNzero, hcover, hAB, hAN, hANzero, hsub, ?_⟩
  rw [hsplit, image_union]
  exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hrestzero)

/-- Complete Lebesgue measurability and absolute determinant scaling,
including infinite measure and dimension zero. -/
theorem invertibleVolume : Spec.invertibleVolume :=
  D05.VolumeInvertibleMeasurable.invertibleMeasurableVolume

/-- Singular maps have null images, separately from the invertible formula. -/
theorem singularVolume : Spec.singularVolume := by
  intro n A hA E
  have hU := D05.VolumeSingular.singularRangeProper n A hA
  obtain ⟨himage, hzero⟩ := D05.VolumeSingular.singularImages n A hA E
  exact ⟨LinearMap.range A.mulVecLin, hU, Set.image_subset_range _ _,
    D05.VolumeSingular.properSubspaceNull n _ hU, himage, hzero⟩

theorem zeroDimensionalVolume : Spec.zeroDimensionalVolume := by
  obtain ⟨_, _, huniv⟩ := D05.VolumeElementary.zeroDimensionalVolume
  refine ⟨fun x => ?_, huniv⟩
  have hs : ({x} : Set (CoordinateSpace 0)) = univ := by
    ext y
    simp only [mem_singleton_iff, mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hs]
  exact huniv

end D05.VolumeChange
