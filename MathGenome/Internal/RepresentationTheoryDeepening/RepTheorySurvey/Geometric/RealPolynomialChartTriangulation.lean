import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.RealPolynomialChartTriangulation
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GeometricBarycentricSubdivision
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RealPolynomialRootProjection
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RealPolynomialRootSections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialSectionBandTriangulation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Order.Compact

namespace RepTheorySurvey.Geometric.RealPolynomialChartTriangulation

open Set Geometry RealPolynomialChartTriangulationSpecs

theorem isClosed_zeroLocus {σ : Type*} (equations : Finset (MvPolynomial σ ℝ)) :
    IsClosed (zeroLocus equations) := by
  have heq : zeroLocus equations = ⋂ p : equations, {x | MvPolynomial.eval x p.val = 0} := by
    ext x
    simp only [zeroLocus, mem_ofPred_eq, mem_iInter, MvPolynomial.aeval_eq_eval]
    exact ⟨fun h p => h p.val p.property, fun h p hp => h ⟨p, hp⟩⟩
  rw [heq]
  exact isClosed_iInter fun p => isClosed_eq (MvPolynomial.continuous_eval p.val) continuous_const

theorem isOpen_strictBox {σ : Type*} [Finite σ] (a b : σ → ℝ) :
    IsOpen (strictBox a b) := by
  have heq : strictBox a b = ⋂ i, (fun x : σ → ℝ => x i) ⁻¹' Ioo (a i) (b i) := by
    ext x
    simp [strictBox]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

theorem isCompact_boxZeroLocus {σ : Type*} (equations : Finset (MvPolynomial σ ℝ))
    (a b : σ → ℝ) : IsCompact (zeroLocus equations ∩ Icc a b) :=
  isCompact_Icc.inter_left (isClosed_zeroLocus equations)

/-- The complex whose only faces are the points of a set. -/
private noncomputable def pointComplex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E) : SimplicialComplex ℝ E where
  faces := (fun x : E => ({x} : Finset E)) '' X
  indep := by
    rintro _ ⟨x, _, rfl⟩
    exact affineIndependent_of_subsingleton ℝ _
  isRelLowerSet_faces := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Finset.singleton_nonempty _, fun s hs hne => ⟨x, hx, ?_⟩⟩
    obtain ⟨y, hy⟩ := hne
    have he := Finset.mem_singleton.mp (hs hy)
    exact (Finset.Subset.antisymm hs (Finset.singleton_subset_iff.mpr (he ▸ hy))).symm
  inter_subset_convexHull := by
    classical
    rintro _ _ ⟨x, _, rfl⟩ ⟨y, _, rfl⟩ z hz
    have hxy : z = x ∧ z = y := by simpa using hz
    have he : x = y := hxy.1.symm.trans hxy.2
    exact subset_convexHull ℝ _ (by simp [hxy.2, he])

private theorem pointComplex_space {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E) :
    (pointComplex X).space = X := by
  ext x
  simp only [SimplicialComplex.mem_space_iff, pointComplex, mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    simpa [show x = y by simpa using hxy] using hy
  · exact fun hx => ⟨{x}, ⟨x, hx, rfl⟩, by simp⟩

private theorem isUnionOfFaceInteriors_of_vertices {σ : Type*}
    (K : SimplicialComplex ℝ (σ → ℝ)) (A : Set K.space)
    (hA : ∀ x ∈ A, x.val ∈ K.vertices) : IsUnionOfFaceInteriors K A := by
  let faces : Set (Finset (σ → ℝ)) := (fun x : K.space => ({x.val} : Finset (σ → ℝ))) '' A
  refine ⟨faces, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hA x hx
  · ext x
    simp only [mem_iUnion, faces, mem_image]
    constructor
    · exact fun hx => ⟨{x.val}, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      have h : x.val = y.val := by simpa using hxy
      exact (Subtype.ext h : x = y) ▸ hy

/-- A finite subset of a real coordinate space is triangulated by its points, compatibly
with every subset. This includes the empty set. -/
theorem finiteLocusTriangulation {σ : Type*} (X : Set (σ → ℝ)) (hX : X.Finite) :
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ X),
      K.faces.Finite ∧ ∀ A : Set (σ → ℝ),
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' A) := by
  refine ⟨pointComplex X, Homeomorph.setCongr (pointComplex_space X), hX.image _, ?_⟩
  intro A
  apply isUnionOfFaceInteriors_of_vertices
  exact fun x _ => ⟨x.val, (pointComplex_space X).subset x.property, rfl⟩

theorem emptyCoordinateChartTriangulation {σ : Type*} [IsEmpty σ] {ι : Type*}
    (equations : ι → Finset (MvPolynomial σ ℝ)) (base : ι) (a b : σ → ℝ) :
    let X := zeroLocus (equations base) ∩ Icc a b
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ X),
      K.faces.Finite ∧
        (∀ j, IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' zeroLocus (equations j))) ∧
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' (Icc a b \ strictBox a b)) := by
  dsimp only
  obtain ⟨K, e, hK, h⟩ := finiteLocusTriangulation (zeroLocus (equations base) ∩ Icc a b)
    (Set.toFinite _)
  exact ⟨K, e, hK, fun j => h _, h _⟩

/-- Transport a geometric complex by an affine change of coordinates. -/
private def affineImageComplex {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [DecidableEq F]
    (φ : E ≃ᵃ[ℝ] F) (K : SimplicialComplex ℝ E) : SimplicialComplex ℝ F where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map φ
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    change AffineIndependent ℝ (Subtype.val : ↥((s.image φ : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact (φ.affineIndependent_set_of_eq_iff).mpr (K.indep hs)
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have h (A : Set E) : convexHull ℝ (φ '' A) = φ '' convexHull ℝ A :=
      (φ.toAffineMap.image_convexHull A).symm
    simp only [Finset.coe_image, ← image_inter φ.injective, h]
    exact image_mono (K.inter_subset_convexHull hs ht)

private theorem affineImageComplex_space {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [DecidableEq F]
    (φ : E ≃ᵃ[ℝ] F) (K : SimplicialComplex ℝ E) :
    (affineImageComplex φ K).space = φ '' K.space := by
  suffices he : ∀ s : Finset E,
      convexHull ℝ (s.image φ : Set F) = φ '' convexHull ℝ (s : Set E) by
    ext x
    constructor
    · intro hx
      obtain ⟨_, ⟨s, hs, rfl⟩, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      rw [he] at hxs
      exact image_mono (K.convexHull_subset_space hs) hxs
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
      exact SimplicialComplex.mem_space_iff.mpr ⟨s.image φ, ⟨s, hs, rfl⟩, by rw [he]; exact ⟨y, hys, rfl⟩⟩
  intro s
  rw [Finset.coe_image]
  exact (φ.toAffineMap.image_convexHull (s : Set E)).symm

private theorem closure_intrinsicInterior_convexHull_finset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Finset E} (hs : s.Nonempty) :
    closure (intrinsicInterior ℝ (convexHull ℝ (s : Set E))) = convexHull ℝ (s : Set E) := by
  apply le_antisymm (closure_minimal intrinsicInterior_subset (s.finite_toSet.isClosed_convexHull ℝ))
  let C := convexHull ℝ (s : Set E)
  have hc : Convex ℝ C := convex_convexHull ℝ _
  obtain ⟨y, hy⟩ := (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)).intrinsicInterior hc
  intro x hx
  have hseg := hc.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hy
    (subset_intrinsicClosure (𝕜 := ℝ) hx)
  exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ y x))

private theorem convex_intrinsicInterior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) : Convex ℝ (intrinsicInterior ℝ C) := by
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with ha₀ | ha
  · have hb₁ : b = 1 := by simpa [← ha₀] using hab
    simpa [← ha₀, hb₁] using hy
  rcases hb.eq_or_lt with hb₀ | hb
  · have ha₁ : a = 1 := by simpa [← hb₀] using hab
    simpa [← hb₀, ha₁] using hx
  exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hx
    (subset_intrinsicClosure (intrinsicInterior_subset hy)) ⟨a, b, ha, hb, hab, rfl⟩

private theorem mem_intrinsicInterior_of_positive_weights {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Finset E} (hs : s.Nonempty)
    {w : E → ℝ} (hw : ∀ i ∈ s, 0 < w i) (hw₁ : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • i) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  let C := convexHull ℝ (s : Set E)
  have hC : Convex ℝ C := convex_convexHull ℝ _
  have hne : C.Nonempty := convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
  obtain ⟨y, hy⟩ := hne.intrinsicInterior hC
  obtain ⟨v, hv₀, hv₁, hvy⟩ := Finset.mem_convexHull'.mp (intrinsicInterior_subset hy)
  have hv (i : E) (hi : i ∈ s) : v i ≤ 1 := by
    rw [← hv₁]
    exact Finset.single_le_sum (fun j hj => hv₀ j hj) hi
  let m := min 1 (s.inf' hs w)
  have hm : 0 < m := lt_min zero_lt_one ((Finset.lt_inf'_iff _).mpr hw)
  let e := m / 2
  have he : 0 < e := half_pos hm
  have hem : e ≤ m := (half_lt_self hm).le
  have he₁ : e < 1 := (half_lt_self hm).trans_le (min_le_left _ _)
  have ht : 0 < 1 - e := sub_pos.mpr he₁
  let r := fun i => (1 - e)⁻¹ * (w i - e * v i)
  have hr₀ (i : E) (hi : i ∈ s) : 0 ≤ r i := by
    have hew : e ≤ w i := (hem.trans (min_le_right _ _)).trans (Finset.inf'_le w hi)
    have hev : e * v i ≤ e := mul_le_of_le_one_right he.le (hv i hi)
    exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hev.trans hew))
  have hr₁ : ∑ i ∈ s, r i = 1 := by
    simp only [r, ← Finset.mul_sum, Finset.sum_sub_distrib, hv₁, hw₁, mul_one]
    exact inv_mul_cancel₀ ht.ne'
  let z := ∑ i ∈ s, r i • i
  have hz : z ∈ C := Finset.mem_convexHull'.mpr ⟨r, hr₀, hr₁, rfl⟩
  have hseg : (∑ i ∈ s, w i • i) ∈ openSegment ℝ y z := by
    refine ⟨e, 1 - e, he, ht, by rw [← add_sub_assoc, add_sub_cancel_left], ?_⟩
    rw [← hvy]
    change e • (∑ i ∈ s, v i • i) + (1 - e) • (∑ i ∈ s, r i • i) = _
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
    apply Finset.sum_congr rfl
    intro i _
    have hri : (1 - e) * r i = w i - e * v i := by
      dsimp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    rw [hri, ← add_sub_assoc, add_sub_cancel_left]
  exact hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hy
    (subset_intrinsicClosure hz) hseg

/-- Every point of a geometric complex is in the intrinsic interior of a face. -/
theorem exists_faceInterior_of_mem_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) {x : E} (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.mp hxs
  let t := s.filter (fun i => 0 < w i)
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hpositive (i : E) (hi : i ∈ t) : 0 < w i := (Finset.mem_filter.mp hi).2
  have hzero (i : E) (hi : i ∈ s) (hit : i ∉ t) : w i = 0 :=
    le_antisymm (le_of_not_gt fun h => hit (Finset.mem_filter.mpr ⟨hi, h⟩)) (hw₀ i hi)
  have hsum : ∑ i ∈ t, w i = 1 := (Finset.sum_subset hts hzero).trans hw₁
  have hcomb : ∑ i ∈ t, w i • i = x := (Finset.sum_subset hts fun i hi hit => by
    rw [hzero i hi hit, zero_smul]).trans hwx
  have ht : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hsum
  exact ⟨t, K.down_closed hs hts ht, hcomb ▸ mem_intrinsicInterior_of_positive_weights ht hpositive hsum⟩

/-- An open face of a finite complex is a nonempty preconnected subset of the realization.
Its closure, also in the realization, is the closed face. -/
theorem faceInteriorInSpace_properties {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) :
    let A := (Subtype.val : K.space → E) ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s : Set E))
    A.Nonempty ∧ IsPreconnected A ∧ closure A = Subtype.val ⁻¹' convexHull ℝ (s : Set E) := by
  let V : Set E := convexHull ℝ (s : Set E)
  let R := intrinsicInterior ℝ V
  let f : K.space → E := Subtype.val
  have hV : V ⊆ K.space := K.convexHull_subset_space hs
  have hR : R ⊆ K.space := intrinsicInterior_subset.trans hV
  have he : Topology.IsClosedEmbedding f :=
    (hK.isClosed_biUnion fun t _ => t.finite_toSet.isClosed_convexHull ℝ).isClosedEmbedding_subtypeVal
  have hVr : V ⊆ range f := fun x hx => ⟨⟨x, hV hx⟩, rfl⟩
  have hRr : R ⊆ range f := fun x hx => ⟨⟨x, hR hx⟩, rfl⟩
  have hne : V.Nonempty := convexHull_nonempty_iff.mpr
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs))
  have hcv : Convex ℝ V := convex_convexHull ℝ _
  change (f ⁻¹' R).Nonempty ∧ IsPreconnected (f ⁻¹' R) ∧ closure (f ⁻¹' R) = f ⁻¹' V
  refine ⟨(hne.intrinsicInterior hcv).preimage' hRr,
    (convex_intrinsicInterior hcv).isPreconnected.preimage_of_isClosedMap
      he.injective he.isClosedMap hRr, ?_⟩
  apply he.injective.image_injective
  rw [← he.closure_image_eq, image_preimage_eq_of_subset hRr,
    image_preimage_eq_of_subset hVr]
  exact closure_intrinsicInterior_convexHull_finset (K.nonempty_of_mem_faces hs)

/-- Restrict a complex to the faces whose convex hulls belong to a closed union of pieces. -/
private def restrictComplex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : SimplicialComplex ℝ E) (S : Set E) : SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ S}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := fun {_} hs => ⟨K.nonempty_of_mem_faces hs.1, fun {_} hts ht =>
    ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

private theorem exists_restrictComplex_face {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) {S : Set E} (hS : IsClosed S)
    (hSK : S ⊆ K.space)
    (hcover : ∀ x ∈ K.space, ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hconst : ∀ s ∈ K.faces, ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)),
      ∀ y ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)), x ∈ S → y ∈ S)
    {x : E} (hx : x ∈ S) : ∃ s ∈ (restrictComplex K S).faces,
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  obtain ⟨s, hs, hxs⟩ := hcover x (hSK hx)
  refine ⟨s, ⟨hs, ?_⟩, hxs⟩
  rw [← closure_intrinsicInterior_convexHull_finset (K.nonempty_of_mem_faces hs)]
  exact closure_minimal (fun y hy => hconst s hs x hxs y hy hx) hS

private theorem restrictComplex_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) {S : Set E} (hS : IsClosed S)
    (hSK : S ⊆ K.space)
    (hcover : ∀ x ∈ K.space, ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hconst : ∀ s ∈ K.faces, ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)),
      ∀ y ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)), x ∈ S → y ∈ S) :
    (restrictComplex K S).space = S := by
  ext x
  rw [SimplicialComplex.mem_space_iff]
  refine ⟨fun ⟨s, hs, hx⟩ => hs.2 hx, fun hx => ?_⟩
  obtain ⟨s, hs, hxs⟩ := exists_restrictComplex_face K hS hSK hcover hconst hx
  exact ⟨s, hs, intrinsicInterior_subset hxs⟩

/-- Membership in `A` is constant on the image of each relative simplex interior. -/
def FaceInteriorCompatible {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (K : SimplicialComplex ℝ E) (g : K.space → F) (A : Set F) : Prop :=
  ∀ s ∈ K.faces, ∀ x y : K.space,
    x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) →
    y.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) → (g x ∈ A ↔ g y ∈ A)

private noncomputable def affineImageComplexHomeomorph {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [DecidableEq F] (φ : E ≃ᴬ[ℝ] F) (K : SimplicialComplex ℝ E) :
    K.space ≃ₜ (affineImageComplex φ.toAffineEquiv K).space :=
  (φ.toHomeomorph.image K.space).trans
    (Homeomorph.setCongr (affineImageComplex_space φ.toAffineEquiv K).symm)

private theorem affineImageComplex_faceInteriorCompatible {E F Y : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [DecidableEq F] (φ : E ≃ᴬ[ℝ] F) (K : SimplicialComplex ℝ E)
    {g : K.space → Y} {A : Set Y} (h : FaceInteriorCompatible K g A) :
    FaceInteriorCompatible (affineImageComplex φ.toAffineEquiv K)
      (g ∘ (affineImageComplexHomeomorph φ K).symm) A := by
  let e := affineImageComplexHomeomorph φ K
  intro t ht x y hx hy
  change t ∈ (fun s : Finset E => s.image φ.toAffineEquiv) '' K.faces at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hh : convexHull ℝ (φ '' (s : Set E)) = φ '' convexHull ℝ (s : Set E) :=
    (φ.toAffineEquiv.toAffineMap.image_convexHull (s : Set E)).symm
  have hface : intrinsicInterior ℝ (convexHull ℝ (s.image φ.toAffineEquiv : Set F)) =
      φ '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rw [Finset.coe_image]
    change intrinsicInterior ℝ (convexHull ℝ (φ '' (s : Set E))) = _
    rw [hh, φ.intrinsicInterior_image]
  have hp (z : (affineImageComplex φ.toAffineEquiv K).space)
      (hz : z.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.image φ.toAffineEquiv : Set F))) :
      (e.symm z).val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rw [hface] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    have he : φ (e.symm z).val = z.val := congrArg Subtype.val (e.apply_symm_apply z)
    exact (φ.injective (hzw.trans he.symm)) ▸ hw
  exact h s hs (e.symm x) (e.symm y) (hp x hx) (hp y hy)

/-- A closed compatible subset of the image of a finite triangulation inherits a finite
triangulation, preserving every other compatible subset. -/
theorem restrictFiniteTriangulation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace F] (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {g : K.space → F} (hg : Topology.IsEmbedding g) {S : Set F}
    (hS : IsClosed S) (hSg : S ⊆ range g) (hc : FaceInteriorCompatible K g S) :
    ∃ (L : SimplicialComplex ℝ E) (e : L.space ≃ₜ S), L.faces.Finite ∧
      ∀ (A : Set F), FaceInteriorCompatible K g A →
        ∃ faces : Set (Finset E), faces ⊆ L.faces ∧
          (fun x => (e x).val) ⁻¹' A = ⋃ s ∈ faces,
            (Subtype.val : L.space → E) ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  let D := (Subtype.val : K.space → E) '' (g ⁻¹' S)
  have hKclosed : IsClosed K.space :=
    hK.isClosed_biUnion fun s _ => s.finite_toSet.isClosed_convexHull ℝ
  have hD : IsClosed D :=
    hKclosed.isClosedEmbedding_subtypeVal.isClosedMap _ (hS.preimage hg.continuous)
  have hDK : D ⊆ K.space := fun _ ⟨x, _, he⟩ => he ▸ x.property
  have hmem (x : K.space) : x.val ∈ D ↔ g x ∈ S := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hcover (x : E) (hx : x ∈ K.space) := exists_faceInterior_of_mem_space K hx
  have hconst (s : Finset E) (hs : s ∈ K.faces) (x : E)
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) (y : E)
      (hy : y ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) (hxD : x ∈ D) : y ∈ D := by
    let x' : K.space := ⟨x, K.convexHull_subset_space hs (intrinsicInterior_subset hx)⟩
    let y' : K.space := ⟨y, K.convexHull_subset_space hs (intrinsicInterior_subset hy)⟩
    exact (hmem y').mpr ((hc s hs x' y' hx hy).mp ((hmem x').mp hxD))
  let L := restrictComplex K D
  have hL : L.space = D := restrictComplex_space K hD hDK hcover hconst
  let j := Topology.IsEmbedding.subtypeVal.homeomorphImage (g ⁻¹' S)
  let f : L.space ≃ₜ (g ⁻¹' S) := (Homeomorph.setCongr hL).trans j.symm
  have hf (x : L.space) : (f x).val.val = x.val :=
    congrArg Subtype.val (j.apply_symm_apply (Homeomorph.setCongr hL x))
  let e := f.trans (hg.homeomorphOfSubsetRange hSg)
  refine ⟨L, e, hK.subset (fun _ hs => hs.1), ?_⟩
  intro A hA
  have he (x : L.space) : (e x).val = g (f x).val := rfl
  let selected := {s ∈ L.faces | ∀ x : L.space,
    x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) → (e x).val ∈ A}
  refine ⟨selected, fun _ hs => hs.1, ?_⟩
  ext x
  simp only [mem_iUnion, mem_preimage]
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := exists_restrictComplex_face K hD hDK hcover hconst (hL.subset x.property)
    have hsel : s ∈ selected := by
      refine ⟨hs, fun y hy => ?_⟩
      have hx' : (f x).val.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by rwa [hf]
      have hy' : (f y).val.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by rwa [hf]
      rw [he] at hx ⊢
      exact (hA s hs.1 (f x).val (f y).val hx' hy').mp hx
    exact ⟨s, hsel, hxs⟩
  · rintro ⟨s, hs, hx⟩
    exact hs.2 x hx

section LineSpecialization

open _root_.Polynomial

private theorem coeff_prod_at_sum_of_degree_bounds {ι A : Type*} [CommSemiring A]
    (s : Finset ι) (q : ι → A[X]) (d : ι → ℕ)
    (hd : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hds (j : ι) (hj : j ∈ s) := hd j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))
        ((natDegree_prod_le _ _).trans (Finset.sum_le_sum hds)), ih hds]

/-- Substitute the affine line with offset `x` and direction `v`. The coefficients of the
offset can themselves be polynomials in the remaining coordinates. -/
noncomputable def polynomialAlongLine {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (x : σ → A) (v : σ → R) (p : MvPolynomial σ R) : A[X] :=
  p.eval₂ (Polynomial.C.comp f) (fun i => Polynomial.C (x i) + Polynomial.C (f (v i)) * X)

theorem eval_polynomialAlongLine {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (x : σ → A) (v : σ → R) (p : MvPolynomial σ R) (t : A) :
    (polynomialAlongLine f x v p).eval t = p.eval₂ f (fun i => x i + f (v i) * t) := by
  simp only [polynomialAlongLine, MvPolynomial.eval₂_eq, eval_finsetSum, eval_mul, eval_prod,
    eval_C, RingHom.comp_apply, eval_pow, eval_add, eval_X]

theorem map_polynomialAlongLine {σ R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    (f : R →+* A) (g : A →+* B) (x : σ → A) (v : σ → R) (p : MvPolynomial σ R) :
    (polynomialAlongLine f x v p).map g = polynomialAlongLine (g.comp f) (g ∘ x) v p := by
  simp only [polynomialAlongLine, MvPolynomial.eval₂_eq, Polynomial.map_sum, Polynomial.map_mul,
    RingHom.comp_apply, Polynomial.map_C, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_X, Function.comp_apply]

private theorem natDegree_lineFactor_le {A : Type*} [CommSemiring A] (x v : A) :
    (Polynomial.C x + Polynomial.C v * X).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

private theorem natDegree_lineMonomial_le {σ A : Type*} [CommSemiring A]
    (x v : σ → A) (d : σ →₀ ℕ) (c : A) :
    (Polynomial.C c * ∏ i ∈ d.support, (Polynomial.C (x i) + Polynomial.C (v i) * X) ^ d i).natDegree ≤
      ∑ i ∈ d.support, d i := by
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  simpa using natDegree_pow_le_of_le (d i) (natDegree_lineFactor_le (x i) (v i))

theorem natDegree_polynomialAlongLine_le {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (x : σ → A) (v : σ → R) (p : MvPolynomial σ R) :
    (polynomialAlongLine f x v p).natDegree ≤ p.totalDegree := by
  rw [polynomialAlongLine, MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro d hd
  exact (natDegree_lineMonomial_le x (f ∘ v) d _).trans (MvPolynomial.le_totalDegree hd)

/-- The coefficient in total degree after line substitution is the value of the highest
homogeneous component in the chosen direction. In particular it is independent of the offset. -/
theorem coeff_polynomialAlongLine_totalDegree {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (x : σ → A) (v : σ → R) (p : MvPolynomial σ R) :
    (polynomialAlongLine f x v p).coeff p.totalDegree =
      f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) := by
  classical
  rw [polynomialAlongLine, MvPolynomial.eval₂_eq, finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  simp only [map_sum, Finset.sum_filter, RingHom.comp_apply]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases he : d.degree = p.totalDegree
  · have hs : (∑ i ∈ d.support, d i) = p.totalDegree := he
    simp only [he, reduceIte, MvPolynomial.eval_monomial, map_mul, Finsupp.prod, map_prod, map_pow]
    rw [coeff_C_mul, ← hs, coeff_prod_at_sum_of_degree_bounds]
    · congr 1
      apply Finset.prod_congr rfl
      intro i _
      have hpow := coeff_pow_of_natDegree_le (m := d i) (natDegree_lineFactor_le (x i) (f (v i)))
      simpa [coeff_add, coeff_C_mul_X] using hpow
    · intro i _
      simpa using natDegree_pow_le_of_le (d i) (natDegree_lineFactor_le (x i) (f (v i)))
  · simp only [he, ite_false, map_zero]
    exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_lineMonomial_le x (f ∘ v) d _).trans_lt
        ((MvPolynomial.le_totalDegree hd).lt_of_ne he))

theorem degree_and_leadingCoeff_polynomialAlongLine {σ R A : Type*}
    [CommSemiring R] [CommSemiring A] (f : R →+* A) (x : σ → A) (v : σ → R)
    (p : MvPolynomial σ R)
    (h : f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) ≠ 0) :
    (polynomialAlongLine f x v p).natDegree = p.totalDegree ∧
      (polynomialAlongLine f x v p).leadingCoeff =
        f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) := by
  have hcoeff := coeff_polynomialAlongLine_totalDegree f x v p
  have hd := le_antisymm (natDegree_polynomialAlongLine_le f x v p)
    (le_natDegree_of_ne_zero (hcoeff ▸ h))
  exact ⟨hd, by rw [leadingCoeff, hd, hcoeff]⟩

private theorem topHomogeneousComponent_ne_zero {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : p ≠ 0) : MvPolynomial.homogeneousComponent p.totalDegree p ≠ 0 := by
  obtain ⟨d, hd, he⟩ := p.support.exists_mem_eq_sup (MvPolynomial.support_nonempty.mpr hp)
    (fun d => d.sum fun _ k => k)
  have hddeg : d.degree = p.totalDegree := he.symm
  intro h
  have hcoeff := congrArg (fun q : MvPolynomial σ ℝ => q.coeff d) h
  simp only [MvPolynomial.coeff_homogeneousComponent, hddeg, reduceIte,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

/-- A direction can be chosen simultaneously for finitely many nonzero polynomials, with a
nonzero component in the coordinate used for the cylinder projection. -/
theorem exists_genericLineDirection {σ : Type*} (P : Finset (MvPolynomial σ ℝ)) (i : σ) :
    ∃ v : σ → ℝ, v i ≠ 0 ∧ ∀ p ∈ P, p ≠ 0 →
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) ≠ 0 := by
  classical
  let Q := P.filter (· ≠ 0)
  let top := fun p : MvPolynomial σ ℝ => MvPolynomial.homogeneousComponent p.totalDegree p
  let H := ∏ p ∈ Q, top p
  have hH : H ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp =>
    topHomogeneousComponent_ne_zero (Finset.mem_filter.mp hp).2
  have hprod : (MvPolynomial.X i * H).IsHomogeneous (1 + ∑ p ∈ Q, p.totalDegree) :=
    (MvPolynomial.isHomogeneous_X _ _).mul
      (MvPolynomial.IsHomogeneous.prod _ _ _ fun p _ =>
        MvPolynomial.homogeneousComponent_isHomogeneous p.totalDegree p)
  have hne : MvPolynomial.X i * H ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero _) hH
  obtain ⟨v, hv⟩ : ∃ v : σ → ℝ, MvPolynomial.eval v (MvPolynomial.X i * H) ≠ 0 := by
    by_contra! h
    exact hne (hprod.eq_zero_of_forall_eval_eq_zero h)
  simp only [map_mul, MvPolynomial.eval_X, H, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hv
  exact ⟨v, hv.1, fun p hp hp₀ => hv.2 p (Finset.mem_filter.mpr ⟨hp, hp₀⟩)⟩

/-- Offsets in the coordinate hyperplane form a cylinder in direction `v`. -/
noncomputable def lineCoordinates {σ : Type*} [DecidableEq σ] (i : σ) (v : σ → ℝ)
    (hv : v i ≠ 0) : (({j : σ // j ≠ i} → ℝ) × ℝ) ≃L[ℝ] (σ → ℝ) where
  toFun z j := (if h : j = i then 0 else z.1 ⟨j, h⟩) + v j * z.2
  invFun x := (fun j => x j.val - v j.val * (x i / v i), x i / v i)
  left_inv := by
    intro z
    have hz : (0 + v i * z.2) / v i = z.2 := by rw [zero_add, mul_comm, mul_div_cancel_right₀ _ hv]
    apply Prod.ext
    · funext j
      dsimp only
      rw [dite_eq_left rfl, hz, dite_eq_right j.property, add_sub_cancel_right]
    · change ((if h : i = i then 0 else z.1 ⟨i, h⟩) + v i * z.2) / v i = z.2
      rwa [dite_eq_left rfl]
  right_inv := by
    intro x
    funext j
    dsimp only
    by_cases h : j = i
    · subst j
      rw [dite_eq_left rfl, zero_add, mul_comm, div_mul_cancel₀ _ hv]
    · rw [dite_eq_right h, sub_add_cancel]
  map_add' := by
    intro x y
    funext j
    by_cases h : j = i <;> simp [h, mul_add, add_add_add_comm]
  map_smul' := by
    intro c x
    funext j
    by_cases h : j = i <;> simp [h, mul_add, mul_left_comm]
  continuous_toFun := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · simp only [dite_eq_left h, zero_add]
      exact continuous_snd.const_mul _
    · simp only [dite_eq_right h]
      exact ((continuous_apply _).comp continuous_fst).add (continuous_snd.const_mul _)
  continuous_invFun := by
    have hi : Continuous fun x : σ → ℝ => x i / v i :=
      (continuous_apply i : Continuous fun x : σ → ℝ => x i).div_const _
    exact (continuous_pi fun j : {j : σ // j ≠ i} =>
      (continuous_apply j.val).sub (hi.const_mul (v j.val))).prodMk hi

/-- Regard a polynomial as univariate along the cylinder fibres, with polynomial coefficients
in the offset coordinates. -/
noncomputable def polynomialInLineCoordinates {σ : Type*} [DecidableEq σ]
    (i : σ) (v : σ → ℝ) (p : MvPolynomial σ ℝ) : (MvPolynomial {j : σ // j ≠ i} ℝ)[X] :=
  polynomialAlongLine MvPolynomial.C
    (fun j => if h : j = i then 0 else MvPolynomial.X ⟨j, h⟩) v p

theorem eval_polynomialInLineCoordinates {σ : Type*} [DecidableEq σ]
    (i : σ) (v : σ → ℝ) (hv : v i ≠ 0) (p : MvPolynomial σ ℝ)
    (z : ({j : σ // j ≠ i} → ℝ) × ℝ) :
    ((polynomialInLineCoordinates i v p).map (MvPolynomial.eval z.1)).eval z.2 =
      MvPolynomial.eval (lineCoordinates i v hv z) p := by
  rw [polynomialInLineCoordinates, map_polynomialAlongLine, eval_polynomialAlongLine]
  have hcoeff : (MvPolynomial.eval z.1).comp MvPolynomial.C = RingHom.id ℝ := by
    ext c
    exact MvPolynomial.eval_C _
  rw [hcoeff]
  change p.eval₂ (RingHom.id ℝ) _ = p.eval₂ (RingHom.id ℝ) (lineCoordinates i v hv z)
  congr 1
  funext j
  by_cases h : j = i <;> simp [lineCoordinates, h]

theorem leadingCoeff_polynomialInLineCoordinates {σ : Type*} [DecidableEq σ]
    (i : σ) (v : σ → ℝ) (p : MvPolynomial σ ℝ)
    (h : MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p) ≠ 0) :
    (polynomialInLineCoordinates i v p).leadingCoeff =
      MvPolynomial.C (MvPolynomial.eval v (MvPolynomial.homogeneousComponent p.totalDegree p)) :=
  (degree_and_leadingCoeff_polynomialAlongLine MvPolynomial.C _ _ _
    (fun hz => h (MvPolynomial.C_injective _ ℝ (hz.trans MvPolynomial.C.map_zero.symm)))).2

end LineSpecialization

/-- In one real coordinate the locus of a finite system is finite unless every equation
is the zero polynomial. -/
theorem finite_zeroLocus_of_unique {σ : Type*} [Unique σ] (equations : Finset (MvPolynomial σ ℝ))
    {p : MvPolynomial σ ℝ} (hp : p ∈ equations) (hp₀ : p ≠ 0) :
    (zeroLocus equations).Finite := by
  let q := MvPolynomial.uniqueAlgEquiv ℝ σ p
  have hq : q ≠ 0 := fun h => hp₀ ((MvPolynomial.uniqueAlgEquiv ℝ σ).injective
    (h.trans (map_zero (MvPolynomial.uniqueAlgEquiv ℝ σ)).symm))
  let ev : (σ → ℝ) ↪ ℝ := (Equiv.funUnique σ ℝ).toEmbedding
  apply ((_root_.Polynomial.finite_setOfPred_isRoot hq).preimage_embedding ev).subset
  intro z hz
  have he : q.eval (z default) = MvPolynomial.eval z p := by
    exact MvPolynomial.eval₂_uniqueAlgEquiv (a := z) (φ := RingHom.id ℝ) (f := p)
  change q.eval (z default) = 0
  rw [he, ← MvPolynomial.aeval_eq_eval]
  exact hz p hp

section LineSubdivision

private def Consecutive (V : Finset ℝ) (l r : ℝ) : Prop :=
  l ∈ V ∧ r ∈ V ∧ l < r ∧ ∀ t ∈ V, t ∉ Ioo l r

private theorem eq_endpoint_of_consecutive {V : Finset ℝ} {l r x : ℝ}
    (h : Consecutive V l r) (hx : x ∈ V) (hm : x ∈ Icc l r) : x = l ∨ x = r := by
  rcases hm.1.eq_or_lt with he | hl
  · exact Or.inl he.symm
  · rcases hm.2.eq_or_lt with he | hr
    · exact Or.inr he
    · exact (h.2.2.2 x hx ⟨hl, hr⟩).elim

private theorem convexHull_pair_real {l r : ℝ} (h : l ≤ r) :
    convexHull ℝ (({l, r} : Finset ℝ) : Set ℝ) = Icc l r := by
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_Icc h]

private theorem consecutive_edges_intersect {V : Finset ℝ} {l r u v : ℝ}
    (h : Consecutive V l r) (h' : Consecutive V u v) :
    Icc l r ∩ Icc u v ⊆ convexHull ℝ (({l, r} : Set ℝ) ∩ {u, v}) := by
  intro x hx
  rcases lt_trichotomy l u with hlu | rfl | hul
  · have hru : r ≤ u := le_of_not_gt fun hur => h.2.2.2 u h'.1 ⟨hlu, hur⟩
    have hxr := le_antisymm hx.1.2 (hru.trans hx.2.1)
    have hxu := le_antisymm (hx.1.2.trans hru) hx.2.1
    exact subset_convexHull ℝ _ ⟨mem_insert_of_mem _ (mem_singleton_iff.mpr hxr),
      mem_insert_iff.mpr (Or.inl hxu)⟩
  · have hrv : r = v := le_antisymm
      (le_of_not_gt fun hvr => h.2.2.2 v h'.2.1 ⟨h'.2.2.1, hvr⟩)
      (le_of_not_gt fun hrv => h'.2.2.2 r h.2.1 ⟨h.2.2.1, hrv⟩)
    subst v
    rw [inter_self]
    simpa only [convexHull_pair, segment_eq_Icc h.2.2.1.le] using hx.1
  · have hvl : v ≤ l := le_of_not_gt fun hlv => h'.2.2.2 l h.1 ⟨hul, hlv⟩
    have hxl := le_antisymm (hx.2.2.trans hvl) hx.1.1
    have hxv := le_antisymm hx.2.2 (hvl.trans hx.1.1)
    exact subset_convexHull ℝ _ ⟨mem_insert_iff.mpr (Or.inl hxl),
      mem_insert_of_mem _ (mem_singleton_iff.mpr hxv)⟩

/-- The vertices are the given points, and the edges join successive points. -/
private noncomputable def lineSubdivision (V : Finset ℝ) : SimplicialComplex ℝ ℝ where
  faces := {s | (∃ x ∈ V, s = {x}) ∨ ∃ l r, Consecutive V l r ∧ s = {l, r}}
  indep := by
    rintro _ (⟨x, _, rfl⟩ | ⟨l, r, h, rfl⟩)
    · exact affineIndependent_of_subsingleton ℝ _
    · change AffineIndepOn ℝ id (({l, r} : Finset ℝ) : Set ℝ)
      simpa only [Finset.coe_insert, Finset.coe_singleton] using affineIndepOn_of_ne ℝ h.2.2.1.ne
  isRelLowerSet_faces := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨l, r, h, rfl⟩)
    · refine ⟨Finset.singleton_nonempty x, fun s hs hne => Or.inl ⟨x, hx, ?_⟩⟩
      obtain ⟨y, hy⟩ := hne
      exact Finset.Subset.antisymm hs (Finset.singleton_subset_iff.mpr
        ((Finset.mem_singleton.mp (hs hy)) ▸ hy))
    · refine ⟨⟨l, Finset.mem_insert_self _ _⟩, fun s hs hne => ?_⟩
      by_cases hl : l ∈ s
      · by_cases hr : r ∈ s
        · exact Or.inr ⟨l, r, h, Finset.Subset.antisymm hs
            (Finset.insert_subset_iff.mpr ⟨hl, Finset.singleton_subset_iff.mpr hr⟩)⟩
        · refine Or.inl ⟨l, h.1, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hl)⟩
          intro x hx
          rcases Finset.mem_insert.mp (hs hx) with rfl | hx'
          · exact Finset.mem_singleton_self _
          · exact (hr ((Finset.mem_singleton.mp hx') ▸ hx)).elim
      · obtain ⟨x, hx⟩ := hne
        have hr : r ∈ s := by
          rcases Finset.mem_insert.mp (hs hx) with rfl | hxr
          · exact (hl hx).elim
          · exact (Finset.mem_singleton.mp hxr) ▸ hx
        refine Or.inl ⟨r, h.2.1, Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hr)⟩
        intro y hy
        rcases Finset.mem_insert.mp (hs hy) with rfl | hys
        · exact (hl hy).elim
        · exact hys
  inter_subset_convexHull := by
    classical
    rintro _ _ (⟨x, hx, rfl⟩ | ⟨l, r, h, rfl⟩) (⟨y, hy, rfl⟩ | ⟨u, v, h', rfl⟩)
    · intro z hz
      have hz' : z = x ∧ z = y := by simpa using hz
      apply subset_convexHull ℝ _
      simpa only [mem_inter_iff, Finset.coe_singleton, mem_singleton_iff] using hz'
    · rw [convexHull_pair_real h'.2.2.1.le, Finset.coe_singleton, convexHull_singleton]
      rintro z ⟨hz, he⟩
      have hzx := mem_singleton_iff.mp hz
      subst z
      exact subset_convexHull ℝ _ ⟨mem_singleton _, by
        simpa using eq_endpoint_of_consecutive h' hx he⟩
    · rw [convexHull_pair_real h.2.2.1.le, Finset.coe_singleton, convexHull_singleton]
      rintro z ⟨he, hz⟩
      have hzy := mem_singleton_iff.mp hz
      subst z
      exact subset_convexHull ℝ _ ⟨by simpa using eq_endpoint_of_consecutive h hy he,
        mem_singleton _⟩
    · rw [convexHull_pair_real h.2.2.1.le, convexHull_pair_real h'.2.2.1.le]
      simpa only [Finset.coe_insert, Finset.coe_singleton] using consecutive_edges_intersect h h'

private theorem lineSubdivision_finite (V : Finset ℝ) : (lineSubdivision V).faces.Finite := by
  apply V.powerset.finite_toSet.subset
  rintro _ (⟨x, hx, rfl⟩ | ⟨l, r, h, rfl⟩)
  · exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hx)
  · exact Finset.mem_powerset.mpr
      (Finset.insert_subset_iff.mpr ⟨h.1, Finset.singleton_subset_iff.mpr h.2.1⟩)

private theorem point_or_consecutive {V : Finset ℝ} {a b : ℝ} (ha : a ∈ V) (hb : b ∈ V)
    {x : ℝ} (hx : x ∈ Icc a b) : x ∈ V ∨ ∃ l r, Consecutive V l r ∧ x ∈ Ioo l r := by
  classical
  by_cases hm : x ∈ V
  · exact Or.inl hm
  · let L := V.filter (fun t => t ≤ x)
    let R := V.filter (fun t => x ≤ t)
    have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hx.1⟩⟩
    have hR : R.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hx.2⟩⟩
    let l := L.max' hL
    let r := R.min' hR
    have hl := Finset.mem_filter.mp (L.max'_mem hL)
    have hr := Finset.mem_filter.mp (R.min'_mem hR)
    have hlx : l < x := hl.2.lt_of_ne fun h => hm (h ▸ hl.1)
    have hxr : x < r := hr.2.lt_of_ne fun h => hm (h.symm ▸ hr.1)
    refine Or.inr ⟨l, r, ⟨hl.1, hr.1, hlx.trans hxr, ?_⟩, ⟨hlx, hxr⟩⟩
    intro t ht htr
    rcases le_total t x with htx | hxt
    · exact (not_lt_of_ge (L.le_max' t (Finset.mem_filter.mpr ⟨ht, htx⟩))) htr.1
    · exact (not_lt_of_ge (R.min'_le t (Finset.mem_filter.mpr ⟨ht, hxt⟩))) htr.2

private theorem lineSubdivision_space {V : Finset ℝ} {a b : ℝ}
    (ha : a ∈ V) (hb : b ∈ V) (hV : (V : Set ℝ) ⊆ Icc a b) :
    (lineSubdivision V).space = Icc a b := by
  ext x
  rw [SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_, (⟨t, ht, rfl⟩ | ⟨l, r, h, rfl⟩), hx⟩
    · have hxt : x = t := by simpa using hx
      exact hxt.symm ▸ hV ht
    · rw [convexHull_pair_real h.2.2.1.le] at hx
      exact ⟨(hV h.1).1.trans hx.1, hx.2.trans (hV h.2.1).2⟩
  · intro hx
    rcases point_or_consecutive ha hb hx with hm | ⟨l, r, h, hlr⟩
    · exact ⟨{x}, Or.inl ⟨x, hm, rfl⟩, by simp⟩
    · exact ⟨{l, r}, Or.inr ⟨l, r, h, rfl⟩,
        convexHull_pair_real h.2.2.1.le ▸ Ioo_subset_Icc_self hlr⟩

private theorem intrinsicInterior_Icc {l r : ℝ} (h : l < r) :
    intrinsicInterior ℝ (Icc l r) = Ioo l r := by
  have hspan := (convex_Icc l r).interior_nonempty_iff_affineSpan_eq_top.mp
    (by rw [interior_Icc]; exact nonempty_Ioo.mpr h)
  have htop : (affineSpan ℝ (Icc l r) : Set ℝ) = univ := by simp [hspan]
  have hop : IsOpen (affineSpan ℝ (Icc l r) : Set ℝ) := htop.symm ▸ isOpen_univ
  let f : ↥(affineSpan ℝ (Icc l r) : Set ℝ) → ℝ := Subtype.val
  have hf : IsOpenMap f := hop.isOpenEmbedding_subtypeVal.isOpenMap
  have hpre : f ⁻¹' interior (Icc l r) = interior (f ⁻¹' Icc l r) :=
    hf.preimage_interior_eq_interior_preimage continuous_subtype_val _
  change f '' interior (f ⁻¹' Icc l r) = Ioo l r
  rw [← hpre, image_preimage_eq_inter_range]
  simp only [f, Subtype.range_val, htop, inter_univ, interior_Icc]

end LineSubdivision

section SignConditions

universe u v

/-- Membership is determined by the signs of the polynomials in the finite list. -/
def IsUnionOfSignCells {σ : Type*} (P : Finset (MvPolynomial σ ℝ)) (S : Set (σ → ℝ)) : Prop :=
  ∀ ⦃x y⦄, (∀ p ∈ P, (0 ≤ MvPolynomial.eval x p ↔ 0 ≤ MvPolynomial.eval y p) ∧
    (MvPolynomial.eval x p ≤ 0 ↔ MvPolynomial.eval y p ≤ 0)) → (x ∈ S ↔ y ∈ S)

/-- The induction statement with the coordinate type fixed. -/
def HasCompactSignTriangulation (σ : Type u) : Prop :=
  ∀ (P : Finset (MvPolynomial σ ℝ)) (S : Set (σ → ℝ)),
    IsCompact S → IsUnionOfSignCells P S →
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ S),
      K.faces.Finite ∧ ∀ A : Set (σ → ℝ), IsUnionOfSignCells P A →
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' A)

/-- Simultaneous triangulation of a compact union of polynomial sign cells. The projected
sets in a cylindrical decomposition can be arbitrary unions of sign cells. -/
def CompactSignTriangulation : Prop :=
  ∀ (σ : Type u) [Finite σ], HasCompactSignTriangulation σ

private noncomputable def boxPolynomials {σ : Type*} [Fintype σ] (a b : σ → ℝ) :
    Finset (MvPolynomial σ ℝ) := by
  classical
  exact (Finset.univ.image fun i => MvPolynomial.X i - MvPolynomial.C (a i)) ∪
    (Finset.univ.image fun i => MvPolynomial.X i - MvPolynomial.C (b i))

private theorem isUnionOfSignCells_box {σ : Type*} [Fintype σ] {a b : σ → ℝ}
    {P : Finset (MvPolynomial σ ℝ)} (h : boxPolynomials a b ⊆ P) :
    IsUnionOfSignCells P (Icc a b) ∧ IsUnionOfSignCells P (strictBox a b) := by
  classical
  have hLower (i : σ) : MvPolynomial.X i - MvPolynomial.C (a i) ∈ P :=
    h (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hUpper (i : σ) : MvPolynomial.X i - MvPolynomial.C (b i) ∈ P :=
    h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  constructor
  · intro x y hs
    have hl (i : σ) : a i ≤ x i ↔ a i ≤ y i := by
      simpa [sub_nonneg] using (hs _ (hLower i)).1
    have hu (i : σ) : x i ≤ b i ↔ y i ≤ b i := by
      simpa [sub_nonpos] using (hs _ (hUpper i)).2
    exact and_congr (forall_congr' hl) (forall_congr' hu)
  · intro x y hs
    have hl (i : σ) : a i < x i ↔ a i < y i := by
      simpa [sub_nonpos, not_le] using not_congr (hs _ (hLower i)).2
    have hu (i : σ) : x i < b i ↔ y i < b i := by
      simpa [sub_nonneg, not_le] using not_congr (hs _ (hUpper i)).1
    exact forall_congr' fun i => and_congr (hl i) (hu i)

private theorem mem_iff_of_unionOfFaceInteriors {σ : Type*} [Finite σ]
    {K : SimplicialComplex ℝ (σ → ℝ)} {A : Set K.space} (hA : IsUnionOfFaceInteriors K A)
    (s : K.faces) {x y : K.space}
    (hx : x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))))
    (hy : y.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ)))) : x ∈ A ↔ y ∈ A := by
  obtain ⟨faces, hfaces, rfl⟩ := hA
  have hm {z w : K.space}
      (hz : z.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))))
      (hw : w.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))))
      (h : z ∈ ⋃ t ∈ faces, (Subtype.val : K.space → σ → ℝ) ⁻¹'
        intrinsicInterior ℝ (convexHull ℝ (t : Set (σ → ℝ)))) :
      w ∈ ⋃ t ∈ faces, (Subtype.val : K.space → σ → ℝ) ⁻¹'
        intrinsicInterior ℝ (convexHull ℝ (t : Set (σ → ℝ))) := by
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp h
    have he : s.val = t := by
      by_contra hn
      exact Set.disjoint_left.mp (GeometricBarycentricSubdivision.disjoint_face_intrinsicInteriors
        σ K s.val t s.property (hfaces ht) hn) hz hzt
    exact mem_iUnion₂.mpr ⟨s.val, he.symm ▸ ht, hw⟩
  exact ⟨hm hx hy, hm hy hx⟩

private theorem compact_subset_box_product {σ : Type*}
    {S : Set ((σ → ℝ) × ℝ)} (hS : IsCompact S) :
    ∃ (l u : σ → ℝ) (a b : ℝ), a < b ∧ S ⊆ Icc l u ×ˢ Icc a b := by
  classical
  have hproj (i : σ) : IsCompact ((fun z : (σ → ℝ) × ℝ => z.1 i) '' S) :=
    hS.image ((continuous_apply i).comp continuous_fst)
  choose l hl using fun i => (hproj i).bddBelow
  choose u hu using fun i => (hproj i).bddAbove
  obtain ⟨a, ha⟩ := (hS.image continuous_snd).bddBelow
  obtain ⟨b, hb⟩ := (hS.image continuous_snd).bddAbove
  refine ⟨l, u, min a b - 1, max a b + 1, ?_, ?_⟩
  · exact (sub_lt_self _ zero_lt_one).trans_le
      ((min_le_left a b).trans ((le_max_left a b).trans (le_add_of_nonneg_right zero_le_one)))
  · intro z hz
    exact ⟨⟨fun i => hl i (mem_image_of_mem _ hz), fun i => hu i (mem_image_of_mem _ hz)⟩,
      ⟨(sub_le_self _ zero_le_one).trans ((min_le_left _ _).trans (ha (mem_image_of_mem _ hz))),
        (hb (mem_image_of_mem _ hz)).trans ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))⟩⟩

private def mappedFaceInterior {σ : Type*} {K : SimplicialComplex ℝ (σ → ℝ)}
    {B : Set (σ → ℝ)} (e : K.space ≃ₜ B) (s : K.faces) : Set (σ → ℝ) :=
  (fun x : K.space => (e x).val) '' ((Subtype.val : K.space → σ → ℝ) ⁻¹'
    intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))))

private lemma mappedFaceInterior_properties {σ : Type*} [Fintype σ]
    {K : SimplicialComplex ℝ (σ → ℝ)} (hK : K.faces.Finite)
    {B : Set (σ → ℝ)} (hB : IsClosed B) (e : K.space ≃ₜ B) (s : K.faces) :
    (mappedFaceInterior e s).Nonempty ∧ IsPreconnected (mappedFaceInterior e s) ∧
      closure (mappedFaceInterior e s) = (fun x : K.space => (e x).val) ''
        ((Subtype.val : K.space → σ → ℝ) ⁻¹' convexHull ℝ (s.val : Set (σ → ℝ))) := by
  let f : K.space → σ → ℝ := fun x => (e x).val
  have hf : Topology.IsClosedEmbedding f :=
    hB.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  obtain ⟨hne, hpre, hclosure⟩ := faceInteriorInSpace_properties K hK s.property
  refine ⟨hne.image f, hpre.image f hf.continuous.continuousOn, ?_⟩
  change closure (f '' _) = f '' _
  rw [hf.closure_image_eq, hclosure]

private def cylinderHomeomorph {E : Type*} [TopologicalSpace E] {B C : Set E}
    (e : B ≃ₜ C) (I : Set ℝ) : ↥(B ×ˢ I) ≃ₜ ↥(C ×ˢ I) where
  toFun x := ⟨((e ⟨x.val.1, x.property.1⟩).val, x.val.2), (e _).property, x.property.2⟩
  invFun x := ⟨((e.symm ⟨x.val.1, x.property.1⟩).val, x.val.2), (e.symm _).property, x.property.2⟩
  left_inv x := Subtype.ext (Prod.ext (congrArg Subtype.val (e.symm_apply_apply _)) rfl)
  right_inv x := Subtype.ext (Prod.ext (congrArg Subtype.val (e.apply_symm_apply _)) rfl)
  continuous_toFun := by
    have hf : Continuous (fun x : ↥(B ×ˢ I) => (⟨x.val.1, x.property.1⟩ : B)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    exact ((continuous_subtype_val.comp (e.continuous.comp hf)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    have hf : Continuous (fun x : ↥(C ×ˢ I) => (⟨x.val.1, x.property.1⟩ : C)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    exact ((continuous_subtype_val.comp (e.symm.continuous.comp hf)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

open SimplicialSectionBandTriangulationSpecs RealPolynomialRootSectionsSpecs in
/-- Lift a triangulated base by the compatible root sections on its faces. -/
private theorem triangulateCylinder {σ : Type u} [Finite σ]
    (P : Finset (Polynomial (MvPolynomial σ ℝ))) {a b : ℝ} (hab : a < b)
    (hP : ∀ p ∈ P, ∃ c : ℝ, c ≠ 0 ∧ p.leadingCoeff = MvPolynomial.C c)
    (K : SimplicialComplex ℝ (σ → ℝ)) (hK : K.faces.Finite)
    {B : Set (σ → ℝ)} (hB : IsClosed B) (e : K.space ≃ₜ B)
    (hcount : ∀ s : K.faces, ∀ x y : mappedFaceInterior e s,
      (((derivativeProduct P a b).map (MvPolynomial.eval x.val)).rootSet ℂ).ncard =
        (((derivativeProduct P a b).map (MvPolynomial.eval y.val)).rootSet ℂ).ncard) :
    ∃ (T : SimplicialComplex ℝ ((σ → ℝ) × ℝ)) (g : T.space ≃ₜ ↥(B ×ˢ Icc a b)),
      T.faces.Finite ∧ ∀ t ∈ T.faces, ∀ x y : T.space,
        x.val ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ))) →
        y.val ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ))) →
        ∀ p ∈ P,
          let r := (p.map (MvPolynomial.eval (g x).val.1)).eval (g x).val.2
          let s := (p.map (MvPolynomial.eval (g y).val.1)).eval (g y).val.2
          (0 ≤ r ↔ 0 ≤ s) ∧ (r ≤ 0 ↔ s ≤ 0) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Finite K.faces := hK.to_subtype
  let C := mappedFaceInterior e
  have hC := mappedFaceInterior_properties hK hB e
  obtain ⟨m, h, hcont, hmono, hstrict, hends, _, hgraph, hband, hcompat⟩ :=
    RealPolynomialRootSections.realPolynomialRootSections σ K.faces P a b C hab hP
      (fun s => (hC s).1) (fun s => (hC s).2.1) hcount
  obtain ⟨L, carrier, hL, hspace, hcarrier, hfaces⟩ :=
    GeometricBarycentricSubdivision.exists_barycentric_subdivision σ K hK
  let point (s : Face L) (x : faceHull s) : K.space :=
    ⟨x.val, K.convexHull_subset_space (carrier s).property ((hfaces s).1 x.property)⟩
  let rootPoint (s : Face L) (x : faceHull s) : closure (C (carrier s)) :=
    ⟨(e (point s x)).val, by
      rw [(hC (carrier s)).2.2]
      exact ⟨point s x, (hfaces s).1 x.property, rfl⟩⟩
  have hpoint (s : Face L) : Continuous (point s) := continuous_subtype_val.subtype_mk _
  have hrootPoint (s : Face L) : Continuous (rootPoint s) :=
    (continuous_subtype_val.comp (e.continuous.comp (hpoint s))).subtype_mk _
  have hopen (s : Face L) (x : faceHull s)
      (hx : x.val ∈ intrinsicInterior ℝ (faceHull (carrier s))) :
      (rootPoint s x).val ∈ C (carrier s) := ⟨point s x, hx, rfl⟩
  let D : LevelFamily L a b :=
    { count := fun s => m (carrier s)
      level := fun s i x => h (carrier s) i (rootPoint s x)
      continuous_level := fun s i => (hcont (carrier s) i).comp (hrootPoint s)
      first_level := fun s x => (hends (carrier s) (rootPoint s x)).1
      last_level := fun s x => (hends (carrier s) (rootPoint s x)).2
      monotone_level := fun s x => hmono (carrier s) (rootPoint s x)
      strictMono_level := fun s x hx =>
        hstrict (carrier s) ⟨_, hopen s x ((hfaces s).2.1 hx)⟩
      separates_at_vertex := by
        intro s i j hij
        obtain ⟨v, hv, hvi⟩ := (hfaces s).2.2
        let x : faceHull s := ⟨v, subset_convexHull ℝ _ hv⟩
        exact ⟨v, hv, (hstrict (carrier s) ⟨_, hopen s x hvi⟩).injective.ne hij⟩
      restrict_levels := by
        intro r s hrs
        have hsub : C (carrier r) ⊆ closure (C (carrier s)) := by
          intro z hz
          obtain ⟨x, hx, rfl⟩ := hz
          rw [(hC (carrier s)).2.2]
          refine ⟨x, ?_, rfl⟩
          exact convexHull_mono (Finset.coe_subset.mpr (hcarrier hrs))
            (intrinsicInterior_subset hx)
        obtain ⟨q, hq, hsurj, hval⟩ := hcompat (carrier s) (carrier r) hsub
        exact ⟨q, hq, hsurj, fun i x => hval i (rootPoint r x)⟩ }
  obtain ⟨T, f, hT, _, hpieces⟩ :=
    SimplicialSectionBandTriangulation.simplicialSectionBandTriangulation σ L hL a b hab D
  let eL := (Homeomorph.setCongr hspace).trans e
  let g := f.trans (cylinderHomeomorph eL (Icc a b))
  refine ⟨T, g, hT, ?_⟩
  intro t ht x y hx hy p hp
  obtain ⟨s, hpiece | hpiece⟩ := hpieces t ht
  · obtain ⟨i, hi⟩ := hpiece
    have hmem (z : T.space)
        (hz : z.val ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ)))) :
        (g z).val ∈ range (fun w : C (carrier s) =>
          (w.val, (h (carrier s) i ⟨w.val, subset_closure w.property⟩).val)) := by
      obtain ⟨hzf, hheight⟩ := hi ⟨z, hz, rfl⟩
      let w : faceHull s := ⟨(f z).val.1, intrinsicInterior_subset hzf⟩
      exact ⟨⟨_, hopen s w ((hfaces s).2.1 hzf)⟩, Prod.ext rfl hheight.symm⟩
    exact hgraph (carrier s) i p hp _ (hmem x hx) _ (hmem y hy)
  · obtain ⟨i, hi⟩ := hpiece
    have hmem (z : T.space)
        (hz : z.val ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ)))) :
        ∃ w : C (carrier s), w.val = (g z).val.1 ∧
          (h (carrier s) i.castSucc ⟨w.val, subset_closure w.property⟩).val < (g z).val.2 ∧
            (g z).val.2 < (h (carrier s) i.succ ⟨w.val, subset_closure w.property⟩).val := by
      obtain ⟨hzf, hlo, hhi⟩ := hi ⟨z, hz, rfl⟩
      let w : faceHull s := ⟨(f z).val.1, intrinsicInterior_subset hzf⟩
      exact ⟨⟨_, hopen s w ((hfaces s).2.1 hzf)⟩, rfl, hlo, hhi⟩
    exact hband (carrier s) i p hp _ (hmem x hx) _ (hmem y hy)

private theorem same_sign_on_preconnected_of_ne_zero {S : Set ℝ} {f : ℝ → ℝ}
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (h₀ : ∀ t ∈ S, f t ≠ 0)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : (0 ≤ f x ↔ 0 ≤ f y) ∧ (f x ≤ 0 ↔ f y ≤ 0) := by
  have hnonneg {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (h : 0 ≤ f a) : 0 ≤ f b := by
    by_contra! hn
    obtain ⟨t, ht, ht₀⟩ := hS.intermediate_value hb ha hf (show 0 ∈ Icc (f b) (f a) from ⟨hn.le, h⟩)
    exact h₀ t ht ht₀
  have hn : 0 ≤ f x ↔ 0 ≤ f y := ⟨hnonneg hx hy, hnonneg hy hx⟩
  have hneg (t : ℝ) (ht : t ∈ S) : f t ≤ 0 ↔ ¬0 ≤ f t :=
    ⟨fun h h' => h₀ t ht (le_antisymm h h'), fun h => (lt_of_not_ge h).le⟩
  exact ⟨hn, (hneg x hx).trans ((not_congr hn).trans (hneg y hy).symm)⟩

/-- The compact sign-cell induction statement in one real coordinate. -/
theorem uniqueCoordinateSignTriangulation {σ : Type*} [Unique σ]
    (P : Finset (MvPolynomial σ ℝ)) (S : Set (σ → ℝ))
    (hS : IsCompact S) (hSat : IsUnionOfSignCells P S) :
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ S),
      K.faces.Finite ∧ ∀ A : Set (σ → ℝ), IsUnionOfSignCells P A →
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' A) := by
  classical
  let φ : ℝ ≃ᴬ[ℝ] (σ → ℝ) := (ContinuousLinearEquiv.funUnique σ ℝ ℝ).symm.toContinuousAffineEquiv
  have hW := hS.image φ.symm.continuous
  obtain ⟨a, ha⟩ := hW.bddBelow
  obtain ⟨b, hb⟩ := hW.bddAbove
  let l := min a b
  let r := max a b
  have hlr : l ≤ r := (min_le_left a b).trans (le_max_left a b)
  have hSbox : S ⊆ φ '' Icc l r := by
    intro x hx
    have hm := mem_image_of_mem φ.symm hx
    exact ⟨φ.symm x, ⟨(min_le_left _ _).trans (ha hm), (hb hm).trans (le_max_right _ _)⟩,
      φ.apply_symm_apply x⟩
  let I := {p : P // (p.val : MvPolynomial σ ℝ) ≠ 0}
  let R : I → Set ℝ := fun p => {t | MvPolynomial.eval (φ t) p.val.val = 0} ∩ Icc l r
  let M : Set ℝ := ⋃ p : I, R p
  have hM : M.Finite := finite_iUnion fun p => by
    let f := ({p.val.val} : Finset (MvPolynomial σ ℝ))
    have hf := finite_zeroLocus_of_unique f (Finset.mem_singleton_self _) p.property
    apply ((hf.preimage φ.injective.injOn).inter_of_left (Icc l r)).subset
    intro t ht
    refine ⟨?_, ht.2⟩
    change φ t ∈ zeroLocus f
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact ht.1
  let V := insert l (insert r hM.toFinset)
  have hl : l ∈ V := Finset.mem_insert_self _ _
  have hr : r ∈ V := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hV : (V : Set ℝ) ⊆ Icc l r := by
    intro t ht
    change t ∈ V at ht
    simp only [V, Finset.mem_insert, Finite.mem_toFinset] at ht
    rcases ht with rfl | rfl | ht
    · exact left_mem_Icc.mpr hlr
    · exact right_mem_Icc.mpr hlr
    · obtain ⟨p, hp⟩ := mem_iUnion.mp ht
      exact hp.2
  let T := affineImageComplex φ.toAffineEquiv (lineSubdivision V)
  have hTspace : T.space = φ '' Icc l r := by
    change (affineImageComplex φ.toAffineEquiv _).space = _
    rw [affineImageComplex_space, lineSubdivision_space hl hr hV]
    rfl
  have himage (s : Finset ℝ) : intrinsicInterior ℝ (convexHull ℝ (s.image φ : Set (σ → ℝ))) =
      φ '' intrinsicInterior ℝ (convexHull ℝ (s : Set ℝ)) := by
    have he : convexHull ℝ (φ '' (s : Set ℝ)) = φ '' convexHull ℝ (s : Set ℝ) :=
      (φ.toAffineEquiv.toAffineMap.image_convexHull (s : Set ℝ)).symm
    rw [Finset.coe_image, he, φ.intrinsicInterior_image]
  have hcompatible (A : Set (σ → ℝ)) (hA : IsUnionOfSignCells P A) {s : Finset (σ → ℝ)}
      (hs : s ∈ T.faces) {x y : σ → ℝ}
      (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ))))
      (hy : y ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ)))) : x ∈ A ↔ y ∈ A := by
    obtain ⟨t, ht, rfl⟩ : ∃ t ∈ (lineSubdivision V).faces, t.image φ = s := hs
    rw [himage] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rcases ht with ⟨w, hw, rfl⟩ | ⟨a', b', hgap, rfl⟩
    · have hu' : u = w := by simpa using hu
      have hv' : v = w := by simpa using hv
      rw [hu', hv']
    · rw [convexHull_pair_real hgap.2.2.1.le, intrinsicInterior_Icc hgap.2.2.1] at hu hv
      apply hA
      intro p hp
      by_cases hpn : p = 0
      · simp [hpn]
      · let f := fun t : ℝ => MvPolynomial.eval (φ t) p
        have hf := (MvPolynomial.continuous_eval p).comp φ.continuous
        have hfree (w : ℝ) (hw : w ∈ Ioo a' b') : f w ≠ 0 := by
          intro hw₀
          have hbox : w ∈ Icc l r :=
            ⟨(hV hgap.1).1.trans hw.1.le, hw.2.le.trans (hV hgap.2.1).2⟩
          have hmem : w ∈ M := mem_iUnion.mpr ⟨⟨⟨p, hp⟩, hpn⟩, hw₀, hbox⟩
          exact hgap.2.2.2 w
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hM.mem_toFinset.mpr hmem))) hw
        exact same_sign_on_preconnected_of_ne_zero isPreconnected_Ioo hf.continuousOn hfree hu hv
  have hST : S ⊆ T.space := hSbox.trans hTspace.symm.subset
  have hT : T.faces.Finite := (lineSubdivision_finite V).image _
  have hC (A : Set (σ → ℝ)) (hA : IsUnionOfSignCells P A) :
      FaceInteriorCompatible T Subtype.val A :=
    fun _ hs _ _ hx hy => hcompatible A hA hs hx hy
  obtain ⟨K, e, hK, h⟩ := restrictFiniteTriangulation T hT Topology.IsEmbedding.subtypeVal
    hS.isClosed (fun x hx => ⟨⟨x, hST hx⟩, rfl⟩) (hC S hSat)
  exact ⟨K, e, hK, fun A hA => h A (hC A hA)⟩

/-- The sign-cell triangulation in dimensions zero and one. -/
theorem subsingletonCoordinateSignTriangulation (σ : Type*) [Subsingleton σ] :
    HasCompactSignTriangulation σ := by
  intro P S hS hSat
  rcases isEmpty_or_nonempty σ with h | h
  · obtain ⟨K, e, hK, h⟩ := finiteLocusTriangulation S (Set.toFinite _)
    exact ⟨K, e, hK, fun A _ => h A⟩
  · let : Unique σ := { default := Classical.choice h, uniq := fun _ => Subsingleton.elim _ _ }
    exact uniqueCoordinateSignTriangulation P S hS hSat

open RealPolynomialRootSectionsSpecs in
private theorem compactSignTriangulation_of_complement {σ : Type u} [Finite σ] (i : σ)
    (ih : HasCompactSignTriangulation {j : σ // j ≠ i}) : HasCompactSignTriangulation σ := by
  classical
  intro P S hS hSat
  let β := {j : σ // j ≠ i}
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype β := Fintype.ofFinite β
  obtain ⟨v, hv, hDir⟩ := exists_genericLineDirection P i
  let φ := lineCoordinates i v hv
  let vertical := polynomialInLineCoordinates i v
  let V := (P.filter (· ≠ 0)).image vertical
  have hV : ∀ p ∈ V, ∃ c : ℝ, c ≠ 0 ∧ p.leadingCoeff = MvPolynomial.C c := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq, hn⟩ := Finset.mem_filter.mp hq
    exact ⟨_, hDir q hq hn, leadingCoeff_polynomialInLineCoordinates i v q (hDir q hq hn)⟩
  obtain ⟨l, r, a, b, hab, hbox⟩ := compact_subset_box_product (hS.image φ.symm.continuous)
  let F := derivativeProduct V a b
  obtain ⟨Q, hQ⟩ := exists_rootCountProjection β F
    (RealPolynomialRootSections.derivativeProduct_leadingCoeff β V a b hab hV)
  let Q' := Q ∪ boxPolynomials l r
  let B := Icc l r
  have hB : IsUnionOfSignCells Q' B := (isUnionOfSignCells_box Finset.subset_union_right).1
  obtain ⟨K, e, hK, hmark⟩ := ih Q' B isCompact_Icc hB
  have hcount (s : K.faces) (x y : mappedFaceInterior e s) :
      ((F.map (MvPolynomial.eval x.val)).rootSet ℂ).ncard =
        ((F.map (MvPolynomial.eval y.val)).rootSet ℂ).ncard := by
    obtain ⟨x', hx', hx⟩ := x.property
    obtain ⟨y', hy', hy⟩ := y.property
    apply hQ
    intro q hq
    let A := {z : β → ℝ | MvPolynomial.eval z q = 0}
    have hA : IsUnionOfSignCells Q' A := by
      intro z w hs
      obtain ⟨h₁, h₂⟩ := hs q (Finset.mem_union_left _ hq)
      change MvPolynomial.eval z q = 0 ↔ MvPolynomial.eval w q = 0
      simp only [le_antisymm_iff]
      exact and_congr h₂ h₁
    have he := mem_iff_of_unionOfFaceInteriors (hmark A hA) s hx' hy'
    change MvPolynomial.eval (e x').val q = 0 ↔ MvPolynomial.eval (e y').val q = 0 at he
    change (e x').val = x.val at hx
    change (e y').val = y.val at hy
    rwa [hx, hy] at he
  obtain ⟨T, g, hT, hSigns⟩ := triangulateCylinder V hab hV K hK isClosed_Icc e hcount
  let g₀ : T.space → σ → ℝ := fun x => φ (g x).val
  have hg₀ : Topology.IsEmbedding g₀ :=
    φ.toHomeomorph.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.comp g.isEmbedding)
  let ψ := affineImageComplexHomeomorph φ.toContinuousAffineEquiv T
  let T' := affineImageComplex φ.toContinuousAffineEquiv.toAffineEquiv T
  let f : T'.space → σ → ℝ := g₀ ∘ ψ.symm
  have hf : Topology.IsEmbedding f := hg₀.comp ψ.symm.isEmbedding
  have hfS : S ⊆ range f := by
    intro x hx
    have hφ : φ.symm x ∈ B ×ˢ Icc a b := hbox ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := g.surjective ⟨φ.symm x, hφ⟩
    refine ⟨ψ z, ?_⟩
    change φ (g (ψ.symm (ψ z))).val = x
    rw [ψ.symm_apply_apply, hz]
    exact φ.apply_symm_apply x
  have hfCompatible (A : Set (σ → ℝ)) (hA : IsUnionOfSignCells P A) :
      FaceInteriorCompatible T' f A := by
    apply affineImageComplex_faceInteriorCompatible
    intro s hs x y hx hy
    apply hA
    intro p hp
    by_cases hn : p = 0
    · simp [hn]
    have hpV : vertical p ∈ V := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp, hn⟩)
    have he := hSigns s hs x y hx hy (vertical p) hpV
    dsimp only [vertical] at he
    rw [eval_polynomialInLineCoordinates i v hv p (g x).val,
      eval_polynomialInLineCoordinates i v hv p (g y).val] at he
    exact he
  have hT' : T'.faces.Finite := hT.image _
  obtain ⟨R, j, hR, hj⟩ := restrictFiniteTriangulation T' hT' hf hS.isClosed hfS
    (hfCompatible S hSat)
  exact ⟨R, j, hR, fun A hA => hj A (hfCompatible A hA)⟩

/-- A finite compact sign-cell triangulation by induction on the number of coordinates. -/
theorem compactSignTriangulation : CompactSignTriangulation.{u} := by
  have aux (n : ℕ) : ∀ (σ : Type u) [Finite σ], Nat.card σ = n → HasCompactSignTriangulation σ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro σ _ hσ
      rcases isEmpty_or_nonempty σ with h | h
      · exact subsingletonCoordinateSignTriangulation σ
      · classical
        obtain ⟨i⟩ := h
        let β := {j : σ // j ≠ i}
        let : Fintype σ := Fintype.ofFinite σ
        let : Fintype β := Fintype.ofFinite β
        have hn : Nat.card β < n := by
          rw [← hσ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          refine Fintype.card_lt_of_injective_not_surjective (Subtype.val : β → σ) Subtype.val_injective ?_
          intro hs
          obtain ⟨j, hj⟩ := hs i
          exact j.property hj
        exact compactSignTriangulation_of_complement i (ih _ hn β rfl)
  intro σ _
  exact aux (Nat.card σ) σ rfl

/-- The polynomial systems and both box conditions can be encoded in a single finite sign
list, so a compact sign-cell triangulation supplies the full chart interface. -/
private theorem chartTriangulation_of_signCells {σ : Type*} [Finite σ] {ι : Type*} [Finite ι]
    (h : HasCompactSignTriangulation σ)
    (equations : ι → Finset (MvPolynomial σ ℝ)) (base : ι) (a b : σ → ℝ) :
    let X := zeroLocus (equations base) ∩ Icc a b
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ X),
      K.faces.Finite ∧
        (∀ j, IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' zeroLocus (equations j))) ∧
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' (Icc a b \ strictBox a b)) := by
  classical
  let _ := Fintype.ofFinite σ
  let _ := Fintype.ofFinite ι
  let P := Finset.univ.biUnion equations ∪ boxPolynomials a b
  have hEq (j : ι) : IsUnionOfSignCells P (zeroLocus (equations j)) := by
    intro x y hsign
    have heq (p : MvPolynomial σ ℝ) (hp : p ∈ equations j) :
        MvPolynomial.aeval x p = 0 ↔ MvPolynomial.aeval y p = 0 := by
      have hm : p ∈ P := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩)
      obtain ⟨h₁, h₂⟩ := hsign p hm
      simp only [MvPolynomial.aeval_eq_eval, le_antisymm_iff]
      exact and_congr h₂ h₁
    exact ⟨fun hx p hp => (heq p hp).mp (hx p hp), fun hy p hp => (heq p hp).mpr (hy p hp)⟩
  have ⟨hBox, hStrict⟩ := isUnionOfSignCells_box (P := P) (a := a) (b := b) Finset.subset_union_right
  obtain ⟨K, e, hK, hA⟩ := h P (zeroLocus (equations base) ∩ Icc a b)
    (isCompact_boxZeroLocus (equations base) a b)
    (fun {_ _} hs => and_congr (hEq base hs) (hBox hs))
  exact ⟨K, e, hK, fun j => hA _ (hEq j), hA _ (fun {_ _} hs =>
    and_congr (hBox hs) (not_congr (hStrict hs)))⟩

theorem realPolynomialChartTriangulation_of_signCells (h : CompactSignTriangulation.{u}) :
    RealPolynomialChartTriangulationSpecs.RealPolynomialChartTriangulation.{u, v} := by
  intro σ _ ι _ equations base a b _
  exact chartTriangulation_of_signCells (h σ) equations base a b

/-- Compatible finite triangulation of a real polynomial zero locus in a coordinate box. -/
theorem realPolynomialChartTriangulation :
    RealPolynomialChartTriangulationSpecs.RealPolynomialChartTriangulation.{u, v} :=
  realPolynomialChartTriangulation_of_signCells compactSignTriangulation

/-- In one coordinate, the endpoint and root subdivision is compatible with every system
and with the box boundary. -/
theorem uniqueCoordinateChartTriangulation {σ : Type*} [Unique σ] {ι : Type*} [Finite ι]
    (equations : ι → Finset (MvPolynomial σ ℝ)) (base : ι) (a b : σ → ℝ) :
    let X := zeroLocus (equations base) ∩ Icc a b
    ∃ (K : SimplicialComplex ℝ (σ → ℝ)) (e : K.space ≃ₜ X),
      K.faces.Finite ∧
        (∀ j, IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' zeroLocus (equations j))) ∧
        IsUnionOfFaceInteriors K ((fun x => (e x).val) ⁻¹' (Icc a b \ strictBox a b)) :=
  chartTriangulation_of_signCells (subsingletonCoordinateSignTriangulation σ) equations base a b

end SignConditions

end RepTheorySurvey.Geometric.RealPolynomialChartTriangulation
