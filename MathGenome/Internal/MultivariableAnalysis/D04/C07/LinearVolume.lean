import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.LinearVolume
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SlicingAndMoments
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set Function Topology
namespace D04.LinearVolume
open JordanRegions NullCovers

variable {n : ℕ}

lemma region_one_integrable {S : Set (E n)} (hS : Jordan S) :
    RegionIntegrable (fun _ : S => (1 : ℝ)) := by
  obtain ⟨Q, hQ, hi⟩ := hS
  refine ⟨⟨1, fun _ => by simp⟩, Q, hQ, ?_⟩
  have he : zeroExtension (fun _ : S => (1 : ℝ)) = indicator S := by
    funext x
    by_cases hx : x ∈ S <;>
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx]
  exact (congrArg (fun F => Darboux.Integrable F Q) he).mpr hi

lemma linear_equiv_regular (A : E n ≃ₗ[ℝ] E n) :
    ContDiff ℝ 1 A := A.toContinuousLinearEquiv.contDiff

lemma linear_equiv_jacobian (A : E n ≃ₗ[ℝ] E n) (x : E n) :
    (fderiv ℝ A x).det = (A : E n →ₗ[ℝ] E n).det := by
  have hd : HasFDerivAt A A.toContinuousLinearEquiv.toContinuousLinearMap x :=
    A.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  rw [hd.fderiv]
  rfl

lemma invertible_volume (A : E n ≃ₗ[ℝ] E n) (S : Set (E n)) (hS : Jordan S) :
    Jordan (A '' S) ∧ volume (A '' S) = |(A : E n →ₗ[ℝ] E n).det| * volume S := by
  let e := A.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph
  have he : ContDiffOn ℝ 1 e e.source := (linear_equiv_regular A).contDiffOn
  have hei : ContDiffOn ℝ 1 e.symm e.target := (linear_equiv_regular A.symm).contDiffOn
  have hK : IsCompact (closure S) := (jordan_bounded hS).isCompact_closure
  have hU : closure S ⊆ e.source := subset_univ _
  have hj := (RegionSubstitution.jordan_image e he hei S hS hK hU).2
  have hv := (RegionSubstitution.volume_substitution e he hei S hS hK hU).2
  have hc := SlicingAndMoments.region_smul (jordan_bounded hS)
    (fun _ : S => (1 : ℝ)) (region_one_integrable hS) |(A : E n →ₗ[ℝ] E n).det|
  refine ⟨hj, ?_⟩
  change volume (A '' S) = regionIntegral (fun x : S => |(fderiv ℝ A x).det|) at hv
  simp_rw [linear_equiv_jacobian] at hv
  exact hv.trans (by simpa only [mul_one, regionIntegral_one] using hc.2)

/-- A bounded set of content zero is Jordan, and its Riemann volume is zero. -/
lemma contentZero_jordan_volume (hn : 0 < n) (S : Set (E n))
    (hb : Bornology.IsBounded S) (hz : ContentZero S) : Jordan S ∧ volume S = 0 := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded S).mpr hb
  obtain ⟨hi, hv⟩ := ExceptionalSets.zero_off_contentZero hn (indicator_bounded S Q) hz
    (fun x _ hx => by
      simp [JordanRegions.indicator, Specs.D04.C06.JordanRegions.Model.indicator, hx])
  have hj : Jordan S := ⟨Q, hQ, hi⟩
  exact ⟨hj, (volume_eq_on_enclosing_box hj hQ hi).trans hv⟩

/-- Proper subspaces are null for coordinate Lebesgue measure. The upstream
box-cover bridge and compactness then give *finite* covers of the image
closure. No volume-transformation or inverse-substitution theorem is used. -/
theorem singular_image : Specs.D04.C07.LinearVolume.singular_imageType := by
  intro n A hA S hS
  have hp : LinearMap.range A ≠ ⊤ := (LinearMap.range_lt_top_of_det_eq_zero hA).ne
  have hsub : closure (A '' S) ⊆ (LinearMap.range A : Set (E n)) :=
    closure_minimal (image_subset_range A S) (Submodule.closed_of_finiteDimensional _)
  have hcimage := hS.isCompact_closure.image A.continuous_of_finiteDimensional
  have hc : IsCompact (closure (A '' S)) := hcimage.of_isClosed_subset isClosed_closure
    (closure_minimal (image_mono subset_closure) hcimage.isClosed)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have he : A = LinearMap.id := Subsingleton.elim _ _
    simp [he] at hA
  let c := coordinates n
  let P : Submodule ℝ (Fin n → ℝ) := (LinearMap.range A).map c.toLinearMap
  have hP : P ≠ ⊤ := Submodule.map_ne_top_iff.mpr hp
  have hzP : MeasureTheory.volume (P : Set (Fin n → ℝ)) = 0 :=
    MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume P hP
  have hz : ContentZero (closure (A '' S)) := by
    apply compact_null_contentZero _ hc
    apply NullPreservation.null_of_coordinate_volume_zero hn
    apply MeasureTheory.measure_mono_null _ hzP
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hsub hx, rfl⟩
  have hzS := contentZero_mono subset_closure hz
  have hjv := contentZero_jordan_volume hn (A '' S) (hc.isBounded.subset subset_closure) hzS
  exact ⟨hc.isBounded, hsub, hp, hz, contentZero_jordan_volume hn _ hc.isBounded hz, hjv⟩

theorem linear_volume : Specs.D04.C07.LinearVolume.linear_volumeType := by
  intro n A S hS
  by_cases hA : A.det = 0
  · obtain ⟨_, _, _, _, _, hj, hv⟩ := singular_image A hA S (jordan_bounded hS)
    exact ⟨hj, by simp [hv, hA]⟩
  · simpa using invertible_volume (A.equivOfDetNeZero hA) S hS

lemma region_smul_integrable_iff {S : Set (E n)} (hb : Bornology.IsBounded S)
    (g : S → ℝ) {c : ℝ} (hc : c ≠ 0) :
    RegionIntegrable (fun x => c * g x) ↔ RegionIntegrable g := by
  constructor
  · intro h
    have hi := (SlicingAndMoments.region_smul hb _ h c⁻¹).1
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi
  · intro h
    exact (SlicingAndMoments.region_smul hb g h c).1

theorem linear_substitution : Specs.D04.C07.LinearVolume.linear_substitutionType := by
  intro n A S hS f hb
  let e := A.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph
  have he : ContDiffOn ℝ 1 e e.source := (linear_equiv_regular A).contDiffOn
  have hei : ContDiffOn ℝ 1 e.symm e.target := (linear_equiv_regular A.symm).contDiffOn
  have hK : IsCompact (closure S) := (jordan_bounded hS).isCompact_closure
  have hU : closure S ⊆ e.source := subset_univ _
  let g : S → ℝ := fun x => f ⟨A x, mem_image_of_mem A x.property⟩
  let c : ℝ := |(A : E n →ₗ[ℝ] E n).det|
  have hc : c ≠ 0 := abs_ne_zero.mpr A.isUnit_det'.ne_zero
  have hs := RegionSubstitution.region_substitution e he hei S hS hK hU f hb
  have hw : (fun x : S =>
      f ⟨e x, mem_image_of_mem e x.property⟩ * |(fderiv ℝ e x).det|) =
      fun x => c * g x := by
    funext x
    change f ⟨A x, _⟩ * |(fderiv ℝ A x).det| = c * g x
    rw [linear_equiv_jacobian]
    exact mul_comm _ _
  have hs' := (congrArg (fun G : S → ℝ => RegionBounded G ∧
    (RegionIntegrable f ↔ RegionIntegrable G) ∧
    ((RegionIntegrable f ∨ RegionIntegrable G) → regionIntegral f = regionIntegral G)) hw).mp hs
  have hi : RegionIntegrable f ↔ RegionIntegrable g :=
    hs'.2.1.trans (region_smul_integrable_iff (jordan_bounded hS) g hc)
  refine ⟨?_, hi, ?_⟩
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun x => hM _⟩
  · intro hh
    have hgi : RegionIntegrable g := hh.elim hi.mp id
    have heq := hs'.2.2 (Or.inl (hi.mpr hgi))
    exact heq.trans (SlicingAndMoments.region_smul (jordan_bounded hS) g hgi c).2

/-- The abstract linear determinant is the determinant of the actual
basis columns in the paper's Euclidean coordinates. -/
theorem basis_determinant : Specs.D04.C07.LinearVolume.basis_determinantType := by
  intro n b
  let A : E n ≃ₗ[ℝ] E n := (coordinates n).trans b.equivFun.symm
  have hcol (j : Fin n) : A (standardBasis n j) = b j := by
    change b.equivFun.symm (coordinates n (standardBasis n j)) = b j
    simp [Module.Basis.equivFun_symm_apply, standardBasis_apply, coordinates_apply]
  have hM : matrixOfLinearMap A.toLinearMap = (fun i j => b j i) := by
    ext i j
    rw [matrixOfLinearMap_apply]
    exact congrArg (fun v : E n => v i) (hcol j)
  calc
    A.toLinearMap.det = (matrixLinearEquiv n n (matrixOfLinearMap A.toLinearMap)).det :=
      congrArg LinearMap.det (matrix_linear_roundtrip A.toLinearMap).symm
    _ = (matrixOfLinearMap A.toLinearMap).det := by
      change LinearMap.det (Matrix.toLin (standardBasis n) (standardBasis n)
        (matrixOfLinearMap A.toLinearMap)) = _
      exact LinearMap.det_toLin (standardBasis n) _
    _ = _ := congrArg Matrix.det hM

theorem basis_substitution : Specs.D04.C07.LinearVolume.basis_substitutionType := by
  intro n b S hS
  let A : E n ≃ₗ[ℝ] E n := (coordinates n).trans b.equivFun.symm
  refine ⟨?_, (invertible_volume A S hS).1, (invertible_volume A S hS).2, ?_⟩
  · intro u
    exact b.equivFun_symm_apply (coordinates n u)
  · intro f hb
    exact (linear_substitution A S hS f hb).2

theorem zero_dimension : Specs.D04.C07.LinearVolume.zero_dimensionType := by
  refine ⟨?_, ?_⟩
  · intro A
    have he : A = LinearMap.id := Subsingleton.elim _ _
    refine ⟨by simp [he], ?_⟩
    intro S
    simp only [he, LinearMap.id_coe, id_eq, image_id']
  · simpa using (JordanRegions.zero_dimension (univ : Set (E 0))).2.1

end D04.LinearVolume
