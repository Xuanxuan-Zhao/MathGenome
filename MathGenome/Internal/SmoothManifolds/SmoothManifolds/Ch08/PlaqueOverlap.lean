import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.PlaqueOverlap
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.Frobenius
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SmoothManifolds.PlaqueOverlap
open ModelData AtlasData MapData TangentData TangentBundleData
  BundleOperationsData CovectorData DistributionData FrobeniusData Frobenius Set Filter
open scoped Topology
universe u

/-- The genuine ambient chart transition, expressed in Euclidean coordinates. -/
def transitionDomain {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n .euclidean M) : Set (Euclidean n) :=
  modelPoint ⁻¹' (e.symm.trans d).source

def transitionMap {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n .euclidean M) (x : Euclidean n) : Euclidean n :=
  (d (e.symm (modelPoint x))).val

theorem transitionDomain_isOpen {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n .euclidean M) : IsOpen (transitionDomain e d) :=
  (e.symm.trans d).open_source.preimage (continuous_modelPoint n)

theorem transitionMap_contDiffOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    ContDiffOn ℝ (⊤ : ℕ∞) (transitionMap e d) (transitionDomain e d) := by
  intro x hx
  obtain ⟨U, hU, hxU, F, hF, hrep⟩ :=
    (S.smoothStructure.property.1.2 e he d hd).1 (modelPoint x) hx
  have hEq : transitionMap e d =ᶠ[𝓝 x] F := by
    filter_upwards [(transitionDomain_isOpen e d).mem_nhds hx, hU.mem_nhds hxU] with y hy hyU
    exact (hrep (modelPoint y) hy hyU).symm
  exact ((hF.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq hEq).contDiffWithinAt

/-- Transverse projection as a continuous linear map. -/
def transverseProjection {n : ℕ} (k : ℕ) : Euclidean n →L[ℝ] Euclidean (n-k) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj ⟨k+j.val, by omega⟩

@[simp] theorem transverseProjection_apply {n : ℕ} (k : ℕ) (x : Euclidean n) :
    transverseProjection k x = transverseCoordinates k x := rfl

/-- The actual transition derivative preserves the distribution's coordinate plane. -/
theorem transitionMap_derivative_plane {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (ha : IsAdaptedChart D e he) (hb : IsAdaptedChart D d hd)
    (x : Euclidean n) (hx : x ∈ transitionDomain e d)
    (v : Euclidean n) (hv : v ∈ CoordinatePlane k) :
    fderiv ℝ (transitionMap e d) x v ∈ CoordinatePlane k := by
  let q := e.symm (modelPoint x)
  have hqe : q ∈ e.source := e.map_target hx.1
  have hqd : q ∈ d.source := hx.2
  have heq : (e q).val = x := congrArg Subtype.val (e.right_inv hx.1)
  let E := C.tangent.fiberCoordinates.equiv e he q hqe
  let F := C.tangent.fiberCoordinates.equiv d hd q hqd
  have hrep : (fun y => transitionMap e d (e y).val) =ᶠ[𝓝 q] (fun y => (d y).val) := by
    filter_upwards [e.open_source.mem_nhds hqe] with y hy
    change (d (e.symm (modelPoint (e y).val))).val = (d y).val
    have hpoint : modelPoint (e y).val = e y := Subtype.ext rfl
    rw [hpoint, e.left_inv hy]
  have hj := TangentBundle.transition_jacobian S C.tangent.fiberCoordinates e d he hd q hqe hqd
    (transitionDomain e d) (transitionMap e d) (transitionDomain_isOpen e d)
    (by rwa [heq]) (transitionMap_contDiffOn e d he hd) hrep (E.symm v)
  have hmem : E.symm v ∈ D.fiber q := (ha q hqe _).mpr (by simpa [E] using hv)
  have hmem' := (hb q hqd _).mp hmem
  rw [hj, heq] at hmem'
  simpa only [E, LinearEquiv.apply_symm_apply] using hmem'

/-- In longitudinal coordinates, every transverse component has zero derivative. -/
theorem transverse_transition_zero {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (ha : IsAdaptedChart D e he) (hb : IsAdaptedChart D d hd)
    (hk : k ≤ n) (z : Euclidean (n-k)) :
    let V := sliceInsertion hk z ⁻¹' transitionDomain e d
    let H := fun x => transverseProjection k (transitionMap e d (sliceInsertion hk z x))
    DifferentiableOn ℝ H V ∧ V.EqOn (fderiv ℝ H) 0 := by
  dsimp only
  have hG := transitionMap_contDiffOn e d he hd
  have hV : IsOpen (sliceInsertion hk z ⁻¹' transitionDomain e d) :=
    (transitionDomain_isOpen e d).preimage (contDiff_sliceInsertion hk z).continuous
  constructor
  · exact ((transverseProjection k).contDiff.comp_contDiffOn
      (hG.comp (contDiff_sliceInsertion hk z).contDiffOn (fun _ hx => hx))).differentiableOn
      (by norm_num)
  · intro x hx
    have hder := (transverseProjection k).hasFDerivAt.comp x
      (((hG.contDiffAt ((transitionDomain_isOpen e d).mem_nhds hx)).differentiableAt
        (by norm_num)).hasFDerivAt.comp x (hasFDerivAt_sliceInsertion hk z x))
    change fderiv ℝ (⇑(transverseProjection k) ∘ transitionMap e d ∘ sliceInsertion hk z) x = 0
    rw [hder.fderiv]
    ext v j
    change transverseCoordinates k
      (fderiv ℝ (transitionMap e d) (sliceInsertion hk z x) (longitudinalInclusion hk v)) j = 0
    have hplane : longitudinalInclusion hk v ∈ CoordinatePlane k := by
      rw [← range_longitudinalInclusion hk]
      exact ⟨v, rfl⟩
    exact congrFun ((transverseCoordinates_eq_zero_iff _).mpr
      (transitionMap_derivative_plane D e d he hd ha hb _ hx _ hplane)) j

/-- Local constancy is proved with the original ambient subspace topology. -/
theorem local_constancy : Specs.SmoothManifolds.Ch08.PlaqueOverlap.local_constancyType.{u} := by
  intro n k M _ S C D e d he hd ha hb z
  classical
  let A := coordinateSlice e k z ∩ d.source
  cases isEmpty_or_nonempty A with
  | inl h =>
    letI := h
    exact fun t => isOpen_discrete _
  | inr h =>
    obtain ⟨p₀⟩ := h
    have hk : k ≤ n := (D.smooth p₀.val).1
    let V := sliceInsertion hk z ⁻¹' transitionDomain e d
    let H := fun x => transverseProjection k (transitionMap e d (sliceInsertion hk z x))
    let u : A → Euclidean k := fun q => longitudinalProjection hk (e q.val).val
    have hu : Continuous u := by
      exact (longitudinalProjection hk).continuous.comp (continuous_subtype_val.comp
        (e.continuousOn.comp_continuous continuous_subtype_val (fun q => q.property.1.1)))
    have hucoord (q : A) : sliceInsertion hk z (u q) = (e q.val).val :=
      sliceInsertion_projection hk z _ q.property.1.2
    have huV (q : A) : u q ∈ V := by
      change modelPoint (sliceInsertion hk z (u q)) ∈ (e.symm.trans d).source
      rw [hucoord]
      have hpoint : modelPoint (e q.val).val = e q.val := Subtype.ext rfl
      rw [hpoint]
      refine ⟨e.map_source q.property.1.1, ?_⟩
      change e.symm (e q.val) ∈ d.source
      rw [e.left_inv q.property.1.1]
      exact q.property.2
    have hH (q : A) : H (u q) = transverseCoordinates k (d q.val).val := by
      change transverseCoordinates k (d (e.symm (modelPoint (sliceInsertion hk z (u q))))).val = _
      rw [hucoord]
      have hpoint : modelPoint (e q.val).val = e q.val := Subtype.ext rfl
      rw [hpoint, e.left_inv q.property.1.1]
    obtain ⟨hHd, hHz⟩ := transverse_transition_zero D e d he hd ha hb hk z
    intro t
    have hopen := ((transitionDomain_isOpen e d).preimage
      (contDiff_sliceInsertion hk z).continuous).isOpen_inter_preimage_of_fderiv_eq_zero hHd hHz t
    have hset : (fun q : A => transverseCoordinates k (d q.val).val) ⁻¹' t =
        u ⁻¹' (V ∩ H ⁻¹' t) := by
      ext q
      simp only [mem_preimage, mem_inter_iff, huV, true_and, hH]
    rw [hset]
    exact hopen.preimage hu

/-- A transverse level set is open in the complete source slice. -/
theorem overlap_isOpen {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (D : SmoothDistribution C k) (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (ha : IsAdaptedChart D e he) (hb : IsAdaptedChart D d hd)
    (z w : Euclidean (n-k)) :
    IsOpen ((Subtype.val : coordinateSlice e k z → M) ⁻¹' coordinateSlice d k w) := by
  have hc := (local_constancy D e d he hd ha hb z).isOpen_fiber w
  obtain ⟨U, hU, hEq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hc
  have hset : (Subtype.val : coordinateSlice e k z → M) ⁻¹' coordinateSlice d k w =
      Subtype.val ⁻¹' (d.source ∩ U) := by
    ext q
    constructor
    · intro hq
      refine ⟨hq.1, ?_⟩
      exact (Set.ext_iff.mp hEq ⟨q.val, q.property, hq.1⟩).mpr hq.2
    · rintro ⟨hqd, hqU⟩
      exact ⟨hqd, (Set.ext_iff.mp hEq ⟨q.val, q.property, hqd⟩).mp hqU⟩
  rw [hset]
  exact (d.open_source.inter hU).preimage continuous_subtype_val

theorem open_overlaps : Specs.SmoothManifolds.Ch08.PlaqueOverlap.open_overlapsType.{u} := by
  intro n k M _ S C D e d he hd ha hb z w
  exact ⟨overlap_isOpen D e d he hd ha hb z w, overlap_isOpen D d e hd he hb ha w z⟩

theorem local_agreement : Specs.SmoothManifolds.Ch08.PlaqueOverlap.local_agreementType.{u} := by
  intro n k M _ S C D e d he hd ha hb z w p hp hq
  obtain ⟨U, hU, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
    (overlap_isOpen D e d he hd ha hb z w)
  obtain ⟨V, hV, hVeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
    (overlap_isOpen D d e hd he hb ha w z)
  have hpU : p ∈ U := (Set.ext_iff.mp hUeq ⟨p, hp⟩).mpr hq
  have hpV : p ∈ V := (Set.ext_iff.mp hVeq ⟨p, hq⟩).mpr hp
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxU, hxV⟩
    exact ⟨(Set.ext_iff.mp hUeq ⟨x, hx⟩).mp hxU, hxU, hxV⟩
  · rintro ⟨hx, hxU, hxV⟩
    exact ⟨(Set.ext_iff.mp hVeq ⟨x, hx⟩).mp hxV, hxU, hxV⟩

/-- Smooth ambient transitions restrict to smooth longitudinal transitions,
with actual extensions on open Euclidean neighborhoods. -/
theorem longitudinal_extension {n k : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hk : k ≤ n) (z : Euclidean (n-k)) (A : Set M)
    (hAe : A ⊆ coordinateSlice e k z) (hAd : A ⊆ d.source) (p : A) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun q : A => longitudinalProjection hk (e q.val).val)
      (fun q : A => longitudinalProjection hk (d q.val).val) p := by
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 e he d hd) (hAe p.property).1 (hAd p.property)
  let V := sliceInsertion hk z ⁻¹' U
  have hcoord (q : A) : sliceInsertion hk z (longitudinalProjection hk (e q.val).val) =
      (e q.val).val := sliceInsertion_projection hk z _ (hAe q.property).2
  refine ⟨V, hU.preimage (contDiff_sliceInsertion hk z).continuous, ?_,
    fun x => longitudinalProjection hk (F (sliceInsertion hk z x)), ?_, ?_⟩
  · change sliceInsertion hk z (longitudinalProjection hk (e p.val).val) ∈ U
    rwa [hcoord]
  · exact (longitudinalProjection hk).contDiff.comp_contDiffOn
      (hF.comp (contDiff_sliceInsertion hk z).contDiffOn (fun _ hx => hx))
  · have hh := hrep.comp_tendsto (continuous_subtype_val.continuousAt (x := p))
    filter_upwards [hh] with q hq
    change F (e q.val).val = (d q.val).val at hq
    rw [hcoord, hq]

theorem smooth_transitions : Specs.SmoothManifolds.Ch08.PlaqueOverlap.smooth_transitionsType.{u} := by
  intro n k M _ S C D e d he hd _ha _hb hk z w p
  constructor
  · exact longitudinal_extension e d he hd hk z _ inter_subset_left
      (fun q hq => hq.2.1) p
  · exact longitudinal_extension d e hd he hk w _ inter_subset_right
      (fun q hq => hq.1.1) p

end SmoothManifolds.PlaqueOverlap
