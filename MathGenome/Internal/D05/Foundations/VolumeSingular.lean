import MathGenome.Internal.Specs.D05.Foundations.VolumeSingular
import MathGenome.Internal.D05.Foundations.VolumeBorelInvertible
import MathGenome.Internal.D05.M02.BasisExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open MeasureTheory Set Module
namespace D05.VolumeSingular
open D05.VolumeElementary

/-- A bounded slice is contained in a product box with one singleton factor. -/
theorem boundedHyperplaneNull (n : ℕ) (i : Fin n) (m : ℕ) :
    (volume : Measure (CoordinateSpace n))
      ({x | x i = 0} ∩ Set.pi Set.univ (fun _ => Set.Icc (-(m : ℝ)) m)) = 0 := by
  classical
  let s : Fin n → Set ℝ := fun j => if j = i then {0} else Set.Icc (-(m : ℝ)) m
  have hsub : {x : CoordinateSpace n | x i = 0} ∩
      Set.pi Set.univ (fun _ => Set.Icc (-(m : ℝ)) m) ⊆ Set.pi Set.univ s := by
    intro x hx j _
    by_cases hj : j = i
    · simpa [s, hj] using hx.1
    · simpa [s, hj] using hx.2 j (Set.mem_univ j)
  apply measure_mono_null hsub
  change Measure.pi (fun _ : Fin n => (volume : Measure ℝ)) (Set.pi Set.univ s) = 0
  rw [Measure.pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [s]

theorem coordinateHyperplaneNull : Spec.coordinateHyperplaneNull := by
  intro n i
  change (volume : Measure (CoordinateSpace n)) {x | x i = 0} = 0
  have hcover : {x : CoordinateSpace n | x i = 0} =
      ⋃ m : ℕ, {x | x i = 0} ∩ Set.pi Set.univ
        (fun _ : Fin n => Set.Icc (-(m : ℝ)) m) := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
      refine Set.mem_iUnion.mpr ⟨m, hx, ?_⟩
      intro j _
      exact abs_le.mp ((norm_le_pi_norm x j).trans hm.le)
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      exact hm.1
  rw [hcover]
  exact measure_iUnion_null (fun m => boundedHyperplaneNull n i m)

theorem subspaceTransport : Spec.subspaceTransport := by
  intro n U hU
  classical
  obtain ⟨f, hf, hUf⟩ := U.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hU)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    apply hf
    apply LinearMap.ext
    intro x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨I, b, i, _, hcoord⟩ := exists_basis_of_pairing_ne_zero hv
  haveI : Finite I := b.linearIndependent.finite
  letI : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = n := by
    rw [← Module.finrank_eq_card_basis b]
    simp [CoordinateSpace]
  let q : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let c : Module.Basis (Fin n) ℝ (CoordinateSpace n) := b.reindex q
  refine ⟨c.equivFun, q i, ?_⟩
  intro x hx
  have hz : f x = 0 := hUf hx
  rw [hcoord] at hz
  have hz' : b.coord i x = 0 := (mul_eq_zero.mp hz).resolve_left hv
  simpa [c, Module.Basis.equivFun_apply, Module.Basis.coord_apply] using hz'

/-- Transport nullity back using only the previously proved invertible Borel rule. -/
theorem properSubspaceNull : Spec.properSubspaceNull := by
  intro n U hU
  classical
  obtain ⟨e, i, he⟩ := subspaceTransport n U hU
  let H : Set (CoordinateSpace n) := e '' (U : Set (CoordinateSpace n))
  have hH : MeasurableSet H :=
    e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      U.closed_of_finiteDimensional.measurableSet
  have hH0 : (volume : Measure (CoordinateSpace n)).completion H = 0 := by
    apply measure_mono_null (t := {x | x i = 0})
    · rintro y ⟨x, hx, rfl⟩
      exact he x hx
    · exact coordinateHyperplaneNull n i
  let A : Matrix (Fin n) (Fin n) ℝ := e.symm.toLinearMap.toMatrix'
  have hAfun : A.mulVec = e.symm := by
    funext x
    exact LinearMap.toMatrix'_mulVec _ x
  have hA : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.mp (by
    rw [hAfun]
    exact e.symm.surjective)
  have himage : A.mulVec '' H = (U : Set (CoordinateSpace n)) := by
    rw [hAfun]
    exact e.toEquiv.symm_image_image _
  have hv := (D05.VolumeBorelInvertible.invertibleBorelVolume n A hA H hH).2
  change volume (A.mulVec '' H) = ENNReal.ofReal |A.det| * volume H at hv
  change volume H = 0 at hH0
  rw [himage, hH0, mul_zero] at hv
  exact hv

/-- Completeness supplies measurability for every subset, including non-Borel ones. -/
theorem subsetProperSubspace : Spec.subsetProperSubspace := by
  intro n U hU S hS
  have hz : (volume : Measure (CoordinateSpace n)).completion S = 0 :=
    measure_mono_null hS (properSubspaceNull n U hU)
  exact ⟨measurableSet_of_null hz, hz⟩

theorem singularRangeProper : Spec.singularRangeProper := by
  intro n A hA htop
  have hs : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp htop
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero hA

theorem singularSubsets : Spec.singularSubsets := by
  intro n A hA S hS
  exact subsetProperSubspace n (LinearMap.range A.mulVecLin)
    (singularRangeProper n A hA) S hS

theorem singularImages : Spec.singularImages := by
  intro n A hA E
  exact singularSubsets n A hA (A.mulVec '' E) (Set.image_subset_range _ _)

theorem zeroDimensionalNonsingular : Spec.zeroDimensionalNonsingular := by
  intro A
  have hd : A.det = 1 := Matrix.det_isEmpty
  exact ⟨hd, (Matrix.isUnit_iff_isUnit_det A).mpr (hd ▸ isUnit_one)⟩

end D05.VolumeSingular
