import Mathlib.Analysis.Convex.Basic
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.ExcisionMayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EilenbergZilber
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.AbstractTubular
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The unique Thom class for the actual oriented quotient normal bundle.

The construction works over every commutative coefficient ring. It proves
normalized tubular existence, the local relative fiber computation, finite
Mayer--Vietoris gluing, ambient excision, and independence of all normalized
tubular choices. Empty submanifolds and rank zero are included.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

universe u v w
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- Original fiber charts identify the punctured pairs, so their induced
cohomology pullbacks really are isomorphisms. -/
def fiberCoordinatesIso (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    fiberPair N p ≅ modelPair.{u} (n-m) where
  hom := fiberCoordinates N a p hp
  inv := {
    map := TopCat.ofHom ⟨(P202Specs.ThomClass.fiberChart N a p hp).symm,
      (P202Specs.ThomClass.fiberChart N a p hp).symm.continuous⟩
    mapsTo := by
      intro z hz heq
      apply hz
      have h := congrArg (fun q =>
        (P202Specs.ThomClass.fiberChart N a p hp q).down) heq
      change ((P202Specs.ThomClass.fiberChart N a p hp)
        ((P202Specs.ThomClass.fiberChart N a p hp).symm z)).down =
        ((P202Specs.ThomClass.fiberChart N a p hp) (fiberOrigin N p)).down at h
      simpa only [Homeomorph.apply_symm_apply, fiberChart_origin] using h }
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (P202Specs.ThomClass.fiberChart N a p hp).symm_apply_apply
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (P202Specs.ThomClass.fiberChart N a p hp).apply_symm_apply

/-- P104's local geometry and globalization also work for a prescribed normal
bundle, rather than only the existential bundle in `abstract_tubular`. This
adapter asserts no normal differential normalization. -/
theorem tubular_exists (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) :
    Nonempty (TubularNeighborhood N) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  obtain ⟨O, F, hO, hzO, hzero, hF, hlocal⟩ :=
    SmoothManifolds.TubularLocalGeometry.tubular_local_geometry T S i hi N
  have hemb : Topology.IsEmbedding i := by
    obtain ⟨h, hh⟩ := hi.2.2.2
    have heq : i = (Subtype.val : Set.range i → M) ∘ h := by
      funext p
      exact (hh p).symm
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  obtain ⟨V, W, hV, hW, h, _, hzV, hiW, hval, hs, hinv, hstar⟩ :=
    SmoothManifolds.BundleTubularGlobalization.bundle_tubular_globalization T S
      N.quotient.bundle i O F hemb hO hzO hzero hF hlocal
  exact ⟨{
    domain := V
    target := W
    isOpen_domain := hV
    isOpen_target := hW
    zero_mem := hzV
    star := hstar
    inclusion_mem := hiW
    homeomorph := h
    zero_eq := fun p => (hval ⟨normalZero N p, hzV p⟩).trans (hzero p)
    smooth := hs
    inverse_smooth := hinv }⟩

/-- The first-order normalization for a total representative of a tubular germ.
This is construction data produced below, rather than an additional assumption
on the embedded submanifold. -/
def NormalDerivative (N : NormalBundle T S i) (F : NormalTotal N → M) : Prop :=
  ∀ p : P, ∃ (a : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (hpc : i p ∈ c.source) (L : Euclidean (n-m) →L[ℝ] Euclidean n),
      HasFDerivAt (fun v => (c (F ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩)).val) L 0 ∧
      ∀ v : Euclidean (n-m),
        (LinearMap.range (N.differential p)).mkQ
          ((N.ambientTangent.fiberCoordinates.equiv c hc (i p) hpc).symm (L v)) =
            (fiberLinearCoordinates N a p hp).symm v

/-- Retain the vertical derivative through the local inverse construction.
The smooth quotient splitting is a right inverse, so the resulting normal
map is the identity, including in rank zero. -/
theorem normalized_tubularGerm_exists (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) :
    ∃ G : TubularGerm N, NormalDerivative N G.map := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  let B := N.quotient.bundle
  obtain ⟨t, ht⟩ := SmoothManifolds.TubularLocalGeometry.normal_lift_exists N
  obtain ⟨j, R, W, hW, r, hj, hR, hjW, hr, hrzero⟩ :=
    SmoothManifolds.TubularLocalGeometry.exists_euclidean_retraction S
  obtain ⟨D, hD, hDcoords⟩ :=
    SmoothManifolds.TubularLocalGeometry.exists_smooth_euclidean_differential
      S N.ambientTangent j hj.1
  let A := fun z : NormalTotal N => j (i z.proj) + D (i z.proj) (t.linearMap z.proj z.snd)
  obtain ⟨F, hU, hzero, hFzero, hF, heq⟩ :=
    SmoothManifolds.TubularLocalGeometry.normal_retraction_candidate N hi.1
      j hj.1 D hD R hR W hW r hjW hr hrzero t
  have hv : ∀ p : P, ∃ (a : P) (hp : p ∈ B.baseSet a)
      (c : ModelChart m .euclidean P) (d : ModelChart n .euclidean M)
      (hc : c ∈ T.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
      (hpc : p ∈ c.source) (hip : i p ∈ d.source)
      (L : Euclidean (n-m) →L[ℝ] Euclidean n),
      HasFDerivAt (fun v => (d (F ⟨p, (B.fiberCoordinates a p hp).symm v⟩)).val) L 0 ∧
      Function.Bijective ((SmoothManifolds.FiniteRegularityData.chartDerivative c d i p).coprod L) ∧
      ∀ v, (N.differential p).range.mkQ
        ((N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip).symm (L v)) =
          (B.fiberCoordinates a p hp).symm v := by
    intro p
    obtain ⟨a, hp⟩ := B.covers p
    obtain ⟨c, hc, hpc⟩ := T.smoothStructure.property.1.1 p
    obtain ⟨d, hd, hip⟩ := S.smoothStructure.property.1.1 (i p)
    let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
    have hDcoord : ∀ v, D (i p) v =
        SmoothManifolds.FiniteRegularityData.coordinateDerivative d j (i p) (E v) :=
      hDcoords (i p) d hd hip E
        (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip)
    obtain ⟨L, hL, heL⟩ :=
      SmoothManifolds.TubularLocalGeometry.retraction_vertical_derivative
        S j hj.1 R hR W hW r hjW hr hrzero (i p) d hd hip E (D (i p)) hDcoord
        (B.fiberCoordinates a p hp) (t.linearMap p) A F heq
        (fun v => ⟨p, (B.fiberCoordinates a p hp).symm v⟩) (fun _ => rfl)
    refine ⟨a, hp, c, d, hc, hd, hpc, hip, L, hL, ?_, ?_⟩
    · exact SmoothManifolds.TubularLocalGeometry.normal_coprod_bijective_coordinates
        N hi.1 t ht p c d hc hd hpc hip a hp L heL
    · intro v
      rw [heL v]
      change (N.differential p).range.mkQ (E.symm (E _)) = _
      rw [E.symm_apply_apply]
      exact ht p _
  have hloc : ∀ z ∈ Set.range (normalZero N),
      ∃ e : OpenPartialHomeomorph (NormalTotal N) M,
        z ∈ e.source ∧ e.source ⊆ A ⁻¹' W ∧ Set.EqOn e F e.source ∧
        ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
          e.symm e.target := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨a, hp, c, d, hc, hd, hpc, hip, L, hL, hbij, _⟩ := hv p
    let b := SmoothManifolds.BundleData.bundleChart B.coordinates (B.trivialization a) c
    have hzb : normalZero N p ∈ b.source :=
      (SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mpr
        ⟨(B.trivialization_baseSet a).symm ▸ hp, hpc⟩
    have hFpd : F (normalZero N p) ∈ d.source := by
      change F ⟨p, 0⟩ ∈ d.source
      rwa [hFzero p]
    have hg := SmoothManifolds.TubularLocalGeometry.smoothAt_target_chart
      _ _ F (normalZero N p) (hF _ (hzero p)) d hd hFpd
    obtain ⟨J, hJ, hblocks⟩ :=
      SmoothManifolds.TubularLocalGeometry.bundle_derivative_at_zero B
        (fun z => (d (F z)).val) (fun x => (d (i x)).val) p a hp c hc hpc hg
        (fun x => congrArg (fun y => (d y).val) (hFzero x)) L hL
    have hder : SmoothManifolds.FiniteRegularityData.chartDerivative b d F (normalZero N p) = J :=
      SmoothManifolds.FiniteRegularity.coordinateDerivative_eq b _ _ hzb J hJ
    apply SmoothManifolds.TubularLocalGeometry.local_inverse_on_open_of_bijective_chartDerivative
      B.totalManifold S F (A ⁻¹' W) hU hF (normalZero N p) (hzero p)
      b d (B.chart_mem a c hc) hd hzb hFpd
    rw [hder]
    apply (Function.Bijective.of_comp_iff J B.coordinates.linearEquiv.bijective).mp
    change Function.Bijective (J.comp B.coordinates.linearEquiv.toContinuousLinearMap)
    rw [hblocks]
    exact hbij
  obtain ⟨O, hO, hzO, _, hFO, hinv⟩ :=
    SmoothManifolds.TubularLocalGeometry.local_inverse_locus
      B.totalManifold.smoothStructure.val S.smoothStructure.val F (A ⁻¹' W)
      (Set.range (normalZero N)) hF hloc
  refine ⟨⟨O, hO, fun p => hzO ⟨p, rfl⟩, F, hFzero, hFO, hinv⟩, ?_⟩
  intro p
  obtain ⟨a, hp, c, d, hc, hd, hpc, hip, L, hL, _, hn⟩ := hv p
  exact ⟨a, hp, d, hd, hip, L, hL, hn⟩

/-- Fixed-fiber linear coordinates are continuous into the original normal
bundle topology, as witnessed by the original bundle chart homeomorphism. -/
theorem continuous_fiberLinearCoordinates_symm (N : NormalBundle T S i)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    Continuous (fun v : Euclidean (n-m) =>
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N)) := by
  have heq : (fun v : Euclidean (n-m) =>
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N)) =
      (fun v => ((P202Specs.ThomClass.fiberChart N a p hp).symm (ULift.up v)).val) := by
    funext v
    have hmap : P202Specs.ThomClass.fiberChart N a p hp
        ⟨⟨p, (fiberLinearCoordinates N a p hp).symm v⟩, rfl⟩ = ULift.up v := by
      apply ULift.ext
      change fiberLinearCoordinates N a p hp ((fiberLinearCoordinates N a p hp).symm v) = v
      exact LinearEquiv.apply_symm_apply _ v
    exact (congrArg Subtype.val
      ((P202Specs.ThomClass.fiberChart N a p hp).symm_apply_apply
        (⟨⟨p, (fiberLinearCoordinates N a p hp).symm v⟩, rfl⟩ : Fiber N p))).symm.trans
          (congrArg (fun z => ((P202Specs.ThomClass.fiberChart N a p hp).symm z).val) hmap)
  rw [heq]
  exact continuous_subtype_val.comp
    ((P202Specs.ThomClass.fiberChart N a p hp).symm.continuous.comp continuous_uliftUp)

/-- Globalization shrinks the domain while retaining its map. Thus every
first derivative at the zero section, including its quotient normalization,
survives globalization. -/
theorem normalized_tubular_exists (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) :
    ∃ K : TubularNeighborhood N, NormalCompatible N K := by
  classical
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  obtain ⟨G, hG⟩ := normalized_tubularGerm_exists hi N
  have hemb : Topology.IsEmbedding i := by
    obtain ⟨h, hh⟩ := hi.2.2.2
    have heq : i = (Subtype.val : Set.range i → M) ∘ h := by
      funext p
      exact (hh p).symm
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  obtain ⟨V, W, hV, hW, h, _, hzV, hiW, hval, hs, hinv, hstar⟩ :=
    SmoothManifolds.BundleTubularGlobalization.bundle_tubular_globalization T S
      N.quotient.bundle i G.domain G.map hemb G.isOpen_domain G.zero_mem
        G.zero_eq G.smooth G.local_inverse
  let K : TubularNeighborhood N := {
    domain := V
    target := W
    isOpen_domain := hV
    isOpen_target := hW
    zero_mem := hzV
    star := hstar
    inclusion_mem := hiW
    homeomorph := h
    zero_eq := fun p => (hval ⟨normalZero N p, hzV p⟩).trans (G.zero_eq p)
    smooth := hs
    inverse_smooth := hinv }
  refine ⟨K, ?_⟩
  intro p
  obtain ⟨a, hp, c, hc, hpc, L, hL, hn⟩ := hG p
  refine ⟨a, hp, c, hc, hpc, L, ?_, hn⟩
  have hnear : ∀ᶠ v in nhds (0 : Euclidean (n-m)),
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ V := by
    have htend := (continuous_fiberLinearCoordinates_symm N a p hp).continuousAt (x := 0)
    have h0 : (⟨p, (fiberLinearCoordinates N a p hp).symm 0⟩ : NormalTotal N) ∈ V := by
      simpa only [map_zero] using hzV p
    exact htend (hV.mem_nhds h0)
  apply hL.congr_of_eventuallyEq
  filter_upwards [hnear] with v hv
  change (c (fiberImage N K a p hp v)).val =
    (c (G.map ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩)).val
  unfold fiberImage
  rw [dite_eq_left hv]
  exact congrArg (fun y => (c y).val) (hval _)

/-- Compactness and Hausdorffness supply the closed image needed for ambient
excision. No ambient compactness is used. -/
theorem image_isClosed [CompactSpace P] (hi : IsSmoothEmbedding T S i) :
    IsClosed (Set.range i) := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨h, hh⟩ := hi.2.2.2
  have hc : Continuous i := by
    have heq : i = (Subtype.val : Set.range i → M) ∘ h := by
      funext p
      exact (hh p).symm
    rw [heq]
    exact continuous_subtype_val.comp h.continuous
  exact (isCompact_range hc).isClosed

/-- Removing the closed complement of the tubular target satisfies the exact
hypotheses of the supplied cohomological excision statement. -/
def tubularExcisionData [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N) : P202Specs.Excision.Data.{u} where
  pair := ambientPair i
  removed := K.targetᶜ
  subset := by
    intro x hx hxi
    exact hx (K.inclusion_mem hxi)
  closure_subset := by
    rw [K.isOpen_target.isClosed_compl.closure_eq]
    change K.targetᶜ ⊆ interior (Set.range i)ᶜ
    rw [(image_isClosed hi).isOpen_compl.interior_eq]
    intro x hx hxi
    exact hx (K.inclusion_mem hxi)

/-- This is the exact excision inclusion, before identifying the tubular target
with its normal-bundle domain. The current usable cohomological excision theorem supplies its isomorphism. -/
theorem tubular_excision_isIso
    [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map
      (tubularExcisionData hi N K).inclusion.op) :=
  P202.CohomologyExcisionMV.excision R R (tubularExcisionData hi N K) q

/-- A homeomorphism carrying exactly one specified subspace onto the other
is an isomorphism of the original category of pairs. -/
def pairIsoOfHomeomorph (A B : Pair.{u}) (h : A.space ≃ₜ B.space)
    (hh : ∀ x : A.space, x ∈ A.subspace ↔ h x ∈ B.subspace) : A ≅ B where
  hom := ⟨TopCat.ofHom ⟨h, h.continuous⟩, fun x hx => (hh x).mp hx⟩
  inv := ⟨TopCat.ofHom ⟨h.symm, h.symm.continuous⟩, fun y hy =>
    (hh (h.symm y)).mpr (by simpa only [h.apply_symm_apply] using hy)⟩
  hom_inv_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext h.symm_apply_apply))
  inv_hom_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext h.apply_symm_apply))

/-- An open subpair carries the induced topology and the original second term. -/
def openPair (A : Pair.{u}) (U : Set A.space) : Pair.{u} :=
  ⟨TopCat.of U, {x | x.val ∈ A.subspace}⟩

def openPairInclusion (A : Pair.{u}) (U : Set A.space) : openPair A U ⟶ A :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hx => hx⟩

/-- Any open neighborhood of the closed support computes the same relative
cohomology, via its literal inclusion. -/
theorem openPairInclusion_isIso (A : Pair.{u}) (hA : IsOpen A.subspace)
    (U : Set A.space) (hU : IsOpen U) (hSupport : A.subspaceᶜ ⊆ U)
    (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (openPairInclusion A U).op) := by
  classical
  have hsub : Uᶜ ⊆ A.subspace := by
    intro x hx
    by_contra hxA
    exact hx (hSupport hxA)
  let D : P202Specs.Excision.Data.{u} := {
    pair := A
    removed := Uᶜ
    subset := hsub
    closure_subset := by
      rw [hU.isClosed_compl.closure_eq, hA.interior_eq]
      exact hsub }
  let h : D.excised.space ≃ₜ (openPair A U).space := {
    toFun := fun x => ⟨x.val, of_not_not x.property⟩
    invFun := fun x => ⟨x.val, not_not_intro x.property⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }
  let e : D.excised ≅ openPair A U := pairIsoOfHomeomorph _ _ h (fun _ => Iff.rfl)
  let F := relativeCohomologyFunctor R R q
  have hs : e.hom ≫ openPairInclusion A U = D.inclusion := PairMap.ext _ _ rfl
  have hc : F.map (openPairInclusion A U).op ≫ F.map e.hom.op = F.map D.inclusion.op := by
    rw [← F.map_comp, ← op_comp, hs]
  haveI : IsIso (F.map D.inclusion.op) := P202.CohomologyExcisionMV.excision R R D q
  haveI : IsIso (F.map (openPairInclusion A U).op ≫ F.map e.hom.op) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map e.hom.op)

/-- The reassociation of the two subspace conditions in a normal slice is an
actual homeomorphism of pairs, with the original normal vectors unchanged. -/
def sliceOpenPairIso (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    slicePair N K p ≅ openPair (fiberPair N p) {z | z.val ∈ K.domain} := by
  let h : (slicePair N K p).space ≃ₜ
      (openPair (fiberPair N p) {z | z.val ∈ K.domain}).space := {
    toFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
    invFun := fun z => ⟨z.val.val, z.val.property, z.property⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    continuous_toFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  apply pairIsoOfHomeomorph _ _ h
  intro z
  constructor
  · intro hz heq
    exact hz (congrArg Subtype.val heq)
  · intro hz heq
    exact hz (Subtype.ext heq)

/-- Restricting a punctured normal fiber to any tubular slice preserves its
relative cohomology. This uses only openness and containment of the origin;
no positive-rank or radial retraction hypothesis is needed. -/
theorem sliceToFiber_isIso (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (p : P) (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (sliceToFiber N K p).op) := by
  letI := (normalBundle N).totalManifold.topologicalManifold.hausdorff
  have hA : IsOpen (fiberPair N p).subspace := by
    change IsOpen ({fiberOrigin N p}ᶜ : Set (Fiber N p))
    exact isClosed_singleton.isOpen_compl
  have hU : IsOpen {z : Fiber N p | z.val ∈ K.domain} :=
    K.isOpen_domain.preimage continuous_subtype_val
  have hSupport : (fiberPair N p).subspaceᶜ ⊆ {z : Fiber N p | z.val ∈ K.domain} := by
    intro z hz
    have heq : z = fiberOrigin N p := Classical.not_not.mp hz
    change z.val ∈ K.domain
    rw [heq]
    exact K.zero_mem p
  let F := relativeCohomologyFunctor R R q
  haveI : IsIso (F.map (openPairInclusion (fiberPair N p)
      {z | z.val ∈ K.domain}).op) :=
    openPairInclusion_isIso (fiberPair N p) hA _ hU hSupport R q
  have hs : (sliceOpenPairIso N K p).hom ≫
      openPairInclusion (fiberPair N p) {z | z.val ∈ K.domain} = sliceToFiber N K p :=
    PairMap.ext _ _ rfl
  rw [← hs, op_comp, F.map_comp]
  infer_instance

/-- The open target pair with the complement of the embedded image. -/
def tubularTargetPair (N : NormalBundle T S i) (K : TubularNeighborhood N) : Pair.{u} :=
  ⟨TopCat.of K.target, {x | x.val ∉ Set.range i}⟩

def tubularTargetInclusion (N : NormalBundle T S i) (K : TubularNeighborhood N) :
    tubularTargetPair N K ⟶ ambientPair i :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ h => h⟩

/-- Resolve the double complement in the literal excision construction by an
actual isomorphism of pairs, preserving the underlying inclusion into M. -/
def excisedTargetIso [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N) :
    (tubularExcisionData hi N K).excised ≅ tubularTargetPair N K := by
  classical
  let h : (tubularExcisionData hi N K).excised.space ≃ₜ
      (tubularTargetPair N K).space := {
    toFun := fun x => ⟨x.val, of_not_not x.property⟩
    invFun := fun x => ⟨x.val, not_not_intro x.property⟩
    left_inv := fun x => Subtype.ext rfl
    right_inv := fun x => Subtype.ext rfl
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }
  exact pairIsoOfHomeomorph _ _ h (fun _ => Iff.rfl)

/-- Cohomological excision for the literal open tubular target, with exactly
its canonical inclusion map. -/
theorem tubularTargetInclusion_isIso
    [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (tubularTargetInclusion N K).op) := by
  let F := relativeCohomologyFunctor R R q
  let e := excisedTargetIso hi N K
  have hs : e.hom ≫ tubularTargetInclusion N K = (tubularExcisionData hi N K).inclusion :=
    PairMap.ext _ _ rfl
  have hc : F.map (tubularTargetInclusion N K).op ≫ F.map e.hom.op =
      F.map (tubularExcisionData hi N K).inclusion.op := by
    rw [← F.map_comp, ← op_comp, hs]
  haveI : IsIso (F.map (tubularExcisionData hi N K).inclusion.op) :=
    tubular_excision_isIso hi N K R q
  haveI : IsIso (F.map (tubularTargetInclusion N K).op ≫ F.map e.hom.op) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map e.hom.op)

/-- The actual open domain in the quotient normal bundle, punctured at its
entire zero section, not just at one point of that section. -/
def tubularDomainPair (N : NormalBundle T S i) (K : TubularNeighborhood N) : Pair.{u} :=
  ⟨TopCat.of K.domain, {z | z.val ≠ normalZero N z.val.proj}⟩

/-- The tubular diffeomorphism is an isomorphism of the relevant relative pairs. -/
def tubularPairIso (N : NormalBundle T S i) (K : TubularNeighborhood N) :
    tubularDomainPair N K ≅ tubularTargetPair N K := by
  apply pairIsoOfHomeomorph _ _ K.homeomorph
  intro z
  exact not_congr (tubular_mem_range_iff N K z.val.proj
    ⟨z.val, rfl, z.property⟩).symm

/-- The complete tubular-domain/excision comparison, before imposing fiber
orientation values. This is the actual map to H^q(domain,domain minus zero). -/
theorem tubularDomainInclusion_isIso
    [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map
      ((tubularPairIso N K).hom ≫ tubularTargetInclusion N K).op) := by
  haveI := tubularTargetInclusion_isIso hi N K R q
  rw [op_comp, Functor.map_comp]
  infer_instance

/-- The inclusion of one normal slice in the punctured tubular domain. -/
def sliceToDomain (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    slicePair N K p ⟶ tubularDomainPair N K where
  map := TopCat.ofHom ⟨fun z => ⟨z.val, z.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  mapsTo := by
    intro z hz heq
    exact hz (heq.trans (congrArg (normalZero N) z.property.1))

/-- The inclusion of the punctured tubular domain into the ambient pair,
using the actual tubular homeomorphism. -/
def domainToAmbient (N : NormalBundle T S i) (K : TubularNeighborhood N) :
    tubularDomainPair N K ⟶ ambientPair i :=
  (tubularPairIso N K).hom ≫ tubularTargetInclusion N K

lemma sliceToDomain_comp (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    sliceToDomain N K p ≫ domainToAmbient N K = sliceToAmbient N K p :=
  PairMap.ext _ _ rfl

/-- Excision gives an actual linear equivalence with the original tubular
pullback as its forward map. -/
def tubularCohomologyEquiv [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) :
    relativeCohomology R R (ambientPair i) q ≃ₗ[R]
      relativeCohomology R R (tubularDomainPair N K) q := by
  letI : IsIso ((relativeCohomologyFunctor R R q).map (domainToAmbient N K).op) :=
    tubularDomainInclusion_isIso hi N K R q
  exact (asIso ((relativeCohomologyFunctor R R q).map (domainToAmbient N K).op)).toLinearEquiv

/-- The excision equivalence respects the exact fiber maps used in the Thom
statement. This is equality of induced restrictions, without choosing cocycles. -/
lemma tubularCohomologyEquiv_restrict [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) (p : P)
    (c : relativeCohomology R R (ambientPair i) q) :
    (relativeCohomologyFunctor R R q).map (sliceToDomain N K p).op
        (tubularCohomologyEquiv hi N K R q c) =
      (relativeCohomologyFunctor R R q).map (sliceToAmbient N K p).op c := by
  let F := relativeCohomologyFunctor R R q
  change (F.map (domainToAmbient N K).op ≫ F.map (sliceToDomain N K p).op) c = _
  rw [← F.map_comp, ← op_comp, sliceToDomain_comp]

/-- The ambient pair is (M,M) for an empty embedded submanifold, regardless of
its declared dimension and of the intended rank. -/
lemma ambientPair_subspace_of_isEmpty [IsEmpty P] :
    (ambientPair i).subspace = Set.univ := by
  ext x
  simp [ambientPair, Set.mem_range]

/-- At the empty submanifold the pair inclusion is a genuine isomorphism. -/
theorem ambientPair_inclusion_isIso_of_isEmpty [IsEmpty P] :
    IsIso (ambientPair i).inclusion := by
  let j : (ambientPair i).space ⟶ (ambientPair i).sub :=
    TopCat.ofHom ⟨fun x => ⟨x, fun h => isEmptyElim (Classical.choose h)⟩,
      continuous_id.subtype_mk _⟩
  refine ⟨⟨j, ?_, ?_⟩⟩
  · exact TopCat.hom_ext (ContinuousMap.ext (fun x => Subtype.ext rfl))
  · exact TopCat.hom_ext (ContinuousMap.ext (fun x => rfl))

/-- Every relative cohomology group of the empty-support ambient pair is zero,
for the shared unrestricted cochains and in every integer degree. -/
theorem ambientCohomology_isZero_of_isEmpty [IsEmpty P]
    (R : Type v) [CommRing R] (q : ℤ) :
    IsZero (relativeCohomology R R (ambientPair i) q) := by
  letI := ambientPair_inclusion_isIso_of_isEmpty (i := i)
  have hc : IsZero (ordinary R R (ambientPair i)) :=
    isZero_cokernel_of_epi (inclusion (P202Specs.SingularChains.ordinaryFunctor R R) (ambientPair i))
  have hd : IsZero ((ordinary R R (ambientPair i)).X q) :=
    (HomologicalComplex.eval _ _ q).map_isZero hc
  have hdual : IsZero ((relativeCochains R R (ambientPair i)).X q) :=
    P202.CohomologyPairs.dual_isZero R R _ hd
  exact ((relativeCochains R R (ambientPair i)).sc q).isZero_homology_of_isZero_X₂ hdual

/-- The full empty-submanifold conclusion, including arbitrary declared rank
and the normalized tubular existence clause. It uses no conditional theorem. -/
theorem exists_unique_of_isEmpty [IsEmpty P]
    (R : Type v) [CommRing R] (d : ℕ)
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i)
    (o : Orientation R N d) :
    (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
      ∃! c : relativeCohomology R R (ambientPair i) (d : ℤ), HasFiberValues R o c := by
  obtain ⟨K⟩ := tubular_exists hi N
  refine ⟨⟨K, fun p => isEmptyElim p⟩, 0, ?_, ?_⟩
  · intro K hK p
    exact isEmptyElim p
  · intro c hc
    haveI := ModuleCat.subsingleton_of_isZero
      (ambientCohomology_isZero_of_isEmpty (i := i) R (d : ℤ))
    exact Subsingleton.elim _ _

/-- Over the zero ring every relative cohomology module has one element.
The full Thom conclusion still includes a normalized tubular neighborhood,
which is supplied by the geometric construction rather than by a premise. -/
theorem exists_unique_of_subsingleton_ring
    (R : Type v) [CommRing R] [Subsingleton R] (d : ℕ)
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i)
    (o : Orientation R N d) :
    (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
      ∃! c : relativeCohomology R R (ambientPair i) (d : ℤ), HasFiberValues R o c := by
  refine ⟨normalized_tubular_exists hi N, 0, ?_, ?_⟩
  · intro K hK p
    exact @Subsingleton.elim (relativeCohomology R R (slicePair N K p) (d : ℤ))
      (Module.subsingleton R _) _ _
  · intro c hc
    letI := Module.subsingleton R (relativeCohomology R R (ambientPair i) (d : ℤ))
    exact Subsingleton.elim _ _

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped Simplicial
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.MayerVietoris

variable (R : Type u) [CommRing R]

/-- For a map reflecting membership in the designated subspace, outside
simplices are exactly carried to outside simplices. -/
lemma inSubspace_map_iff {P Q : Pair.{v}} (f : P ⟶ Q)
    (hf : ∀ x : P.space, f.map x ∈ Q.subspace ↔ x ∈ P.subspace)
    (k : ℕ) (s : Simplex P.space k) :
    InSubspace Q k ((TopCat.toSSet.map f.map).app (op ⦋k⦌) s) ↔ InSubspace P k s := by
  simp only [InSubspace, P202.SingularChains.simplexEquiv_postcomp]
  exact forall_congr' (fun x => hf _)

/-- An injective map reflecting the second term of a pair has an injection
on the actual relative simplex basis. -/
def outsideMap {P Q : Pair.{v}} (f : P ⟶ Q)
    (hf : ∀ x : P.space, f.map x ∈ Q.subspace ↔ x ∈ P.subspace)
    (k : ℕ) : Outside P k → Outside Q k :=
  fun s => ⟨(TopCat.toSSet.map f.map).app (op ⦋k⦌) s.val,
    (inSubspace_map_iff f hf k s.val).not.mpr s.property⟩

lemma outsideMap_injective {P Q : Pair.{v}} (f : P ⟶ Q)
    (hinj : Function.Injective f.map)
    (hf : ∀ x : P.space, f.map x ∈ Q.subspace ↔ x ∈ P.subspace)
    (k : ℕ) : Function.Injective (outsideMap f hf k) := by
  intro s t h
  apply Subtype.ext
  apply (simplexEquiv P.space k).injective
  ext x
  apply hinj
  have he := congrArg (fun a : Outside Q k => simplexEquiv Q.space k a.val x) h
  simpa only [outsideMap, P202.SingularChains.simplexEquiv_postcomp, ContinuousMap.comp_apply] using he

/-- In every nonnegative degree, an injective map of pairs reflecting the
second term is split on relative chains. Its retraction only selects simplex
coordinates and is not asserted to commute with the boundary. -/
lemma relative_map_nonnegative_split {P Q : Pair.{v}} (f : P ⟶ Q)
    (hinj : Function.Injective f.map)
    (hf : ∀ x : P.space, f.map x ∈ Q.subspace ↔ x ∈ P.subspace)
    (k : ℕ) :
    ∃ r : (nonnegative R R Q).X k ⟶ (nonnegative R R P).X k,
      (relativeMap (chainFunctor R R) f).f k ≫ r = 𝟙 _ := by
  obtain ⟨bP, hbP⟩ := P202.RelativeSingularChains.quotient_basis R P k
  obtain ⟨bQ, hbQ⟩ := P202.RelativeSingularChains.quotient_basis R Q k
  let j := outsideMap f hf k
  have hj : Function.Injective j := outsideMap_injective f hinj hf k
  have hmap (s : Outside P k) :
      (relativeMap (chainFunctor R R) f).f k (bP s) = bQ (j s) := by
    rw [hbP, hbQ]
    have hπ := congrArg (fun a => a.f k) (projection_map (chainFunctor R R) f)
    have he := congrArg (fun a : (complex R R P.space).X k ⟶ _ => a (Finsupp.single s.val 1)) hπ
    change (relativeMap (chainFunctor R R) f).f k
      ((projection (chainFunctor R R) P).f k (Finsupp.single s.val 1)) =
        (projection (chainFunctor R R) Q).f k (Finsupp.single (j s).val 1)
    change (relativeMap (chainFunctor R R) f).f k
      ((projection (chainFunctor R R) P).f k (Finsupp.single s.val 1)) =
      (projection (chainFunctor R R) Q).f k
        ((chainMap R R f.map).f k (Finsupp.single s.val 1)) at he
    rw [he]
    congr 1
    exact Finsupp.mapDomain_single
  let r : (nonnegative R R Q).X k →ₗ[R] (nonnegative R R P).X k :=
    bP.repr.symm.toLinearMap.comp ((Finsupp.lcomapDomain j hj).comp bQ.repr.toLinearMap)
  refine ⟨ModuleCat.ofHom r, ?_⟩
  apply ModuleCat.hom_ext
  apply bP.ext
  intro s
  change r ((relativeMap (chainFunctor R R) f).f k (bP s)) = bP s
  rw [hmap]
  dsimp only [r, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [bQ.repr_self]
  have hs : Finsupp.lcomapDomain (R := R) j hj (Finsupp.single (j s) (1 : R)) = Finsupp.single s 1 := by
    rw [← Finsupp.mapDomain_single (f := j) (a := s)]
    exact Finsupp.leftInverse_lcomapDomain_mapDomain j hj _
  rw [hs]
  simpa using bP.repr_symm_single s (1 : R)


/-- The same degreewise splitting for the chapter's integer-graded complex. -/
lemma relative_map_ordinary_split {P Q : Pair.{v}} (f : P ⟶ Q)
    (hinj : Function.Injective f.map)
    (hf : ∀ x : P.space, f.map x ∈ Q.subspace ↔ x ∈ P.subspace)
    (q : ℤ) :
    ∃ r : (ordinary R R Q).X q ⟶ (ordinary R R P).X q,
      (relativeMap (ordinaryFunctor R R) f).f q ≫ r = 𝟙 _ := by
  by_cases hq : 0 ≤ q
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain ⟨r, hr⟩ := relative_map_nonnegative_split R f hinj hf k
    let eP := (eval _ _ (k : ℤ)).mapIso
      (P202.CohomologyExcisionMV.relativeExtensionIso R P)
    let eQ := (eval _ _ (k : ℤ)).mapIso
      (P202.CohomologyExcisionMV.relativeExtensionIso R Q)
    have hk : (degreeEmbedding 0).f k = (k : ℤ) := by
      change (0 : ℤ) + k = k
      omega
    let aP := (nonnegative R R P).extendXIso (degreeEmbedding 0) hk
    let aQ := (nonnegative R R Q).extendXIso (degreeEmbedding 0) hk
    have he : eP.hom ≫ (relativeMap (ordinaryFunctor R R) f).f (k : ℤ) =
        aP.hom ≫ (relativeMap (chainFunctor R R) f).f k ≫ aQ.inv ≫ eQ.hom := by
      have h := congrArg (fun α => α.f (k : ℤ))
        (P202.CohomologyExcisionMV.relativeExtensionIso_natural R f)
      change eP.hom ≫ (relativeMap (ordinaryFunctor R R) f).f (k : ℤ) = _ at h
      rw [comp_f, extendMap_f _ _ hk] at h
      exact h
    refine ⟨eQ.inv ≫ aQ.hom ≫ r ≫ aP.inv ≫ eP.hom, ?_⟩
    apply (cancel_epi eP.hom).mp
    rw [← Category.assoc, he]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc ((relativeMap (chainFunctor R R) f).f k), hr]
    simp
  · exact ⟨0, (P202.RelativeSingularChains.ordinary_negative R R P q (by omega)).1.eq_of_src _ _⟩

/-- The first relative Mayer--Vietoris chain map is split in every degree. -/
lemma relative_cover_first_split (C : CoverPair.{v,w}) (q : ℤ) :
    ∃ r : (middle (theoryFunctor R .relative) C).X q ⟶
        ((theoryFunctor R .relative).obj C.intersectionPair).X q,
      (chainFirst (theoryFunctor R .relative) C).f q ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := relative_map_ordinary_split R C.toLeft
    (by intro a b h; exact Subtype.ext (congrArg (fun x : C.leftPair.space => x.val) h))
    (by intro a; exact Iff.rfl) q
  refine ⟨(biprod.fst : middle (theoryFunctor R .relative) C ⟶
    (theoryFunctor R .relative).obj C.leftPair).f q ≫ r, ?_⟩
  rw [← Category.assoc, ← comp_f]
  simp only [chainFirst, biprod.lift_fst]
  exact hr


abbrev relativeCoverChains := theoryFunctor.{u,v} R .relative
abbrev relativeCoverQuotient (C : CoverPair.{v,w}) :=
  (P202.MayerVietoris.presentation (relativeCoverChains R) C).X₃
abbrev relativeCoverComparison (C : CoverPair.{v,w}) :=
  P202.MayerVietoris.comparison (relativeCoverChains R) C

lemma relative_cover_chain_shortExact (C : CoverPair.{v,w}) :
    P202Specs.ChainLES.DegreewiseShortExact
      (P202.MayerVietoris.presentation (relativeCoverChains R) C) := by
  letI := (P202.MayerVietoris.relative_presentation_properties R C).1
  exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (P202.MayerVietoris.presentation_shortExact (relativeCoverChains R) C)

/-- The small relative-chain presentation remains projective in every degree;
the chosen relative-simplex retraction is the reason unrestricted duality is
valid here. -/
lemma relative_cover_quotient_projective (C : CoverPair.{v,w}) (q : ℤ) :
    Projective ((relativeCoverQuotient R C).X q) := by
  have hproj (A : Pair.{v}) : Projective ((ordinary R R A).X q) := by
    haveI := P202.CohomologyExcisionMV.relative_ordinary_free R A q
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  haveI : Projective (((relativeCoverChains R).obj C.leftPair).X q) := hproj _
  haveI : Projective (((relativeCoverChains R).obj C.rightPair).X q) := hproj _
  haveI : Projective ((middle (relativeCoverChains R) C).X q) :=
    Projective.of_iso (biprodXIso _ _ q).symm inferInstance
  obtain ⟨r, hr⟩ := relative_cover_first_split R C q
  let S := (P202.MayerVietoris.presentation (relativeCoverChains R) C).map (eval _ _ q)
  let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S
    (relative_cover_chain_shortExact R C q).exact r hr
      (relative_cover_chain_shortExact R C q).epi_g
  exact @Retract.projective _ _ S.X₃ S.X₂ ⟨σ.s, S.g, σ.s_g⟩
    (by change Projective ((middle (relativeCoverChains R) C).X q); infer_instance)

lemma relative_cover_quotient_negative (C : CoverPair.{v,w}) (q : ℤ) (hq : q < 0) :
    IsZero ((relativeCoverQuotient R C).X q) := by
  have hz : IsZero ((middle (relativeCoverChains R) C).X q) := by
    apply IsZero.of_iso _ (biprodXIso _ _ q)
    exact (biprod_isZero_iff _ _).mpr
      ⟨(P202.RelativeSingularChains.ordinary_negative R R C.leftPair q hq).1,
        (P202.RelativeSingularChains.ordinary_negative R R C.rightPair q hq).1⟩
  exact IsZero.of_epi ((cokernel.π (chainFirst (relativeCoverChains R) C)).f q) hz

/-- The actual relative cover comparison is a chain homotopy equivalence,
so its unrestricted algebraic dual computes relative cohomology. -/
lemma relative_cover_comparison_homotopy (C : CoverPair.{v,w}) :
    ∃ e : HomotopyEquiv (relativeCoverQuotient R C)
        ((relativeCoverChains R).obj C.pair), e.hom = relativeCoverComparison R C := by
  haveI : ∀ q, Projective ((relativeCoverQuotient R C).X q) :=
    relative_cover_quotient_projective R C
  haveI : ∀ q, Projective (((relativeCoverChains R).obj C.pair).X q) := by
    intro q
    change Projective ((ordinary R R C.pair).X q)
    haveI := P202.CohomologyExcisionMV.relative_ordinary_free R C.pair q
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  haveI : QuasiIso (relativeCoverComparison R C) := by
    rw [quasiIso_iff]
    intro q
    exact (quasiIsoAt_iff_isIso_homologyMap _ q).mpr
      ((P202.MayerVietoris.relative_presentation_properties R C).2.2 q)
  exact P202.CohomologyExcisionMV.projective_comparison_homotopy R
    (K := relativeCoverQuotient R C) (L := (relativeCoverChains R).obj C.pair)
    ⟨0, relative_cover_quotient_negative R C⟩
    ⟨0, fun q hq => (P202.RelativeSingularChains.ordinary_negative R R C.pair q hq).1⟩
    (relativeCoverComparison R C)

variable (A : Type w) [AddCommGroup A] [Module R A]
open P202Specs.CohomologyPairs
abbrev relativeCoverCochains (C : CoverPair.{v,w}) :=
  (dualComplexFunctor R A (.down ℤ)).obj (op (relativeCoverQuotient R C))
abbrev relativeCoverDualComparison (C : CoverPair.{v,w}) :
    relativeCochains R A C.pair ⟶ relativeCoverCochains R A C :=
  (dualComplexFunctor R A (.down ℤ)).map (relativeCoverComparison R C).op

def relativeCoverCochainSequence (C : CoverPair.{v,w}) :
    ShortComplex (CochainComplex (ModuleCat.{max u v w} R) ℤ) :=
  ShortComplex.mk
    ((dualComplexFunctor R A (.down ℤ)).map
      (cokernel.π (chainFirst (relativeCoverChains R) C)).op)
    ((dualComplexFunctor R A (.down ℤ)).map
      (chainFirst (relativeCoverChains R) C).op)
    (by rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero, Functor.map_zero])

/-- Relative cover cochains form a genuinely short exact sequence for every
coefficient module, with no injectivity or finite generation requirement. -/
lemma relative_cover_cochain_shortExact (C : CoverPair.{v,w}) :
    P202Specs.ChainLES.DegreewiseShortExact (relativeCoverCochainSequence R A C) := by
  intro q
  exact P202.CohomologyPairs.dual_shortExact R A
    ((P202.MayerVietoris.presentation (relativeCoverChains R) C).map (eval _ _ q))
    (relative_cover_chain_shortExact R C q) (relative_cover_first_split R C q)

lemma relative_cover_dual_comparison_quasiIso (C : CoverPair.{v,w}) :
    QuasiIso (relativeCoverDualComparison R A C) := by
  obtain ⟨e, he⟩ := relative_cover_comparison_homotopy R C
  have h := (P202.CohomologyExcisionMV.dualHomotopyEquiv R A e).quasiIso_hom
  change QuasiIso ((dualComplexFunctor R A (.down ℤ)).map e.hom.op) at h
  rw [he] at h
  exact h


abbrev relativeCoverMiddle (C : CoverPair.{v,w}) (q : ℤ) :=
  relativeCohomology R A C.leftPair q ⊞ relativeCohomology R A C.rightPair q

def relativeCoverRestrictions (C : CoverPair.{v,w}) (q : ℤ) :
    relativeCohomology R A C.pair q ⟶ relativeCoverMiddle R A C q :=
  biprod.lift ((relativeCohomologyFunctor R A q).map C.leftInclusion.op)
    ((relativeCohomologyFunctor R A q).map C.rightInclusion.op)

def relativeCoverDifference (C : CoverPair.{v,w}) (q : ℤ) :
    relativeCoverMiddle R A C q ⟶ relativeCohomology R A C.intersectionPair q :=
  biprod.desc ((relativeCohomologyFunctor R A q).map C.toLeft.op)
    (- (relativeCohomologyFunctor R A q).map C.toRight.op)

abbrev relativeCoverMiddleIso (C : CoverPair.{v,w}) (q : ℤ) :
    ((relativeCoverCochainSequence R A C).X₂).homology q ≅ relativeCoverMiddle R A C q :=
  P202.CohomologyExcisionMV.contravariantBiprodIso
    (P202.CohomologyExcisionMV.dualHomologyFunctor R A q)
    ((relativeCoverChains R).obj C.leftPair) ((relativeCoverChains R).obj C.rightPair)

lemma relative_cover_restrictions_formula (C : CoverPair.{v,w}) (q : ℤ) :
    homologyMap (relativeCoverDualComparison R A C) q ≫
      homologyMap (relativeCoverCochainSequence R A C).f q ≫
        (relativeCoverMiddleIso R A C q).hom = relativeCoverRestrictions R A C q := by
  change (P202.CohomologyExcisionMV.dualHomologyFunctor R A q).map
      (relativeCoverComparison R C).op ≫
    (P202.CohomologyExcisionMV.dualHomologyFunctor R A q).map (cokernel.π _).op ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  simp only [relativeCoverComparison, P202.MayerVietoris.comparison, cokernel.π_desc]
  exact P202.CohomologyExcisionMV.contravariantBiprodIso_desc _ _ _
    ((relativeCoverChains R).map C.leftInclusion) ((relativeCoverChains R).map C.rightInclusion)

lemma relative_cover_difference_formula (C : CoverPair.{v,w}) (q : ℤ) :
    (relativeCoverMiddleIso R A C q).hom ≫ relativeCoverDifference R A C q =
      homologyMap (relativeCoverCochainSequence R A C).g q := by
  have h := P202.CohomologyExcisionMV.contravariantBiprodIso_lift
    (P202.CohomologyExcisionMV.dualHomologyFunctor R A q)
    ((relativeCoverChains R).obj C.leftPair) ((relativeCoverChains R).obj C.rightPair)
    ((relativeCoverChains R).map C.toLeft) (- (relativeCoverChains R).map C.toRight)
  simp only [op_neg, Functor.map_neg] at h
  exact h

/-- Relative Mayer--Vietoris gluing in a fixed degree: compatible classes
have a unique extension when the preceding cohomology of the overlap vanishes.
The arrows are the actual restrictions of the shared relative cohomology. -/
theorem relative_cover_glue_unique (C : CoverPair.{v,w}) (q : ℤ)
    (hvan : IsZero (relativeCohomology R A C.intersectionPair (q-1)))
    (x : relativeCoverMiddle R A C q)
    (hx : relativeCoverDifference R A C q x = 0) :
    ∃! c : relativeCohomology R A C.pair q,
      relativeCoverRestrictions R A C q c = x := by
  let S := relativeCoverCochainSequence R A C
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (relative_cover_cochain_shortExact R A C)
  let e := relativeCoverMiddleIso R A C q
  let f := homologyMap (relativeCoverDualComparison R A C) q
  haveI : IsIso f := by
    haveI := relative_cover_dual_comparison_quasiIso R A C
    exact inferInstanceAs (IsIso (homologyMap (relativeCoverDualComparison R A C) q))
  have hφ : f ≫ homologyMap S.f q ≫ e.hom = relativeCoverRestrictions R A C q :=
    relative_cover_restrictions_formula R A C q
  have hψ : e.hom ≫ relativeCoverDifference R A C q = homologyMap S.g q :=
    relative_cover_difference_formula R A C q
  have hx' : homologyMap S.g q (e.inv x) = 0 := by
    rw [← hψ]
    change relativeCoverDifference R A C q (e.hom (e.inv x)) = 0
    rw [Iso.inv_hom_id_apply]
    exact hx
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hs.homology_exact₂ q)
    (e.inv x) hx'
  have hzero : hs.δ (q-1) q (by simp) = 0 := hvan.eq_of_src _ _
  haveI : Mono (homologyMap S.f q) := (hs.homology_exact₁ (q-1) q (by simp)).mono_g hzero
  haveI : Mono (relativeCoverRestrictions R A C q) := by
    rw [← hφ]
    infer_instance
  refine ⟨inv f y, ?_, ?_⟩
  · rw [← hφ]
    change e.hom (homologyMap S.f q (f (inv f y))) = x
    rw [IsIso.inv_hom_id_apply, hy, Iso.inv_hom_id_apply]
  · intro c hc
    apply (ModuleCat.mono_iff_injective (relativeCoverRestrictions R A C q)).mp inferInstance
    rw [hc]
    change x = relativeCoverRestrictions R A C q (inv f y)
    rw [← hφ]
    change x = e.hom (homologyMap S.f q (f (inv f y)))
    rw [IsIso.inv_hom_id_apply, hy, Iso.inv_hom_id_apply]


/-- The low-degree vanishing needed for the Thom induction propagates across
a two-set cover by the same relative Mayer--Vietoris argument. -/
theorem relative_cover_isZero (C : CoverPair.{v,w}) (q : ℤ)
    (hleft : IsZero (relativeCohomology R A C.leftPair q))
    (hright : IsZero (relativeCohomology R A C.rightPair q))
    (hoverlap : IsZero (relativeCohomology R A C.intersectionPair (q-1))) :
    IsZero (relativeCohomology R A C.pair q) := by
  have hm : IsZero (relativeCoverMiddle R A C q) :=
    (biprod_isZero_iff _ _).mpr ⟨hleft, hright⟩
  haveI := ModuleCat.subsingleton_of_isZero hm
  obtain ⟨c, hc, hu⟩ := relative_cover_glue_unique R A C q hoverlap 0 (map_zero _)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b =>
    (hu a (Subsingleton.elim _ _)).trans (hu b (Subsingleton.elim _ _)).symm⟩

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped Simplicial
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.SingularChains
variable (R : Type v) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]

/-- Degree-zero cohomology has a unique cocycle representative, because
ordinary relative cochains vanish in degree -1. -/
def relativeZeroCochain (B : Pair.{u}) :
    relativeCohomology R A B 0 ⟶ (relativeCochains R A B).X 0 := by
  let K := relativeCochains R A B
  have hd : K.d (-1) 0 = 0 :=
    ((P202.CohomologyPairs.negative R A).2 B (-1) (by decide)).1.eq_of_src _ _
  exact (K.isoHomologyπ (-1) 0 (by simp) hd).inv ≫ K.iCycles 0

instance relativeZeroCochain_mono (B : Pair.{u}) : Mono (relativeZeroCochain R A B) := by
  unfold relativeZeroCochain
  infer_instance

lemma relativeZeroCochain_natural {B C : Pair.{u}} (f : B ⟶ C) :
    (relativeCohomologyFunctor R A 0).map f.op ≫ relativeZeroCochain R A B =
      relativeZeroCochain R A C ≫ ((relativeCochainFunctor R A).map f.op).f 0 := by
  let K := relativeCochains R A C
  let L := relativeCochains R A B
  let φ := (relativeCochainFunctor R A).map f.op
  rw [← cancel_epi (K.homologyπ 0)]
  change K.homologyπ 0 ≫ homologyMap φ 0 ≫ _ = K.homologyπ 0 ≫ _
  rw [homologyπ_naturality_assoc]
  dsimp only [K]
  simp only [relativeZeroCochain, Category.assoc, isoHomologyπ_hom_inv_id_assoc]
  exact cyclesMap_i φ 0

/-- A point with the empty relative subspace. -/
def pointPair : Pair.{u} := ⟨TopCat.of PUnit.{u+1}, ∅⟩

def pointToPair (B : Pair.{u}) (x : B.space) : pointPair.{u} ⟶ B where
  map := TopCat.ofHom ⟨fun _ => x, continuous_const⟩
  mapsTo := fun _ h => False.elim h

def constantSimplex (X : TopCat.{u}) (x : X) (n : ℕ) : Simplex X n :=
  (simplexEquiv X n).symm (ContinuousMap.const _ x)

lemma simplex_zero_constant (X : TopCat.{u}) (s : Simplex X 0) :
    s = constantSimplex X (simplexEquiv X 0 s (Convexity.StdSimplex.single 0)) 0 := by
  apply (simplexEquiv X 0).injective
  ext y
  change simplexEquiv X 0 s y = simplexEquiv X 0 s (Convexity.StdSimplex.single 0)
  rw [Subsingleton.elim y (Convexity.StdSimplex.single 0)]

lemma pointMap_constantSimplex (B : Pair.{u}) (x : B.space) (n : ℕ) :
    (TopCat.toSSet.map (pointToPair B x).map).app (op ⦋n⦌)
      (constantSimplex pointPair.space PUnit.unit n) = constantSimplex B.space x n := by
  apply (simplexEquiv B.space n).injective
  ext y
  rfl

/-- The unique representative as an actual linear functional. -/
def relativeZeroCocycle (B : Pair.{u}) (c : relativeCohomology R A B 0) :
    (ordinary R R B).X 0 →ₗ[R] A := relativeZeroCochain R A B c

/-- Value of the unique degree-zero cocycle on the relative point cycle at x. -/
def relativeZeroValue (B : Pair.{u}) (c : relativeCohomology R A B 0) (x : B.space) : A :=
  (relativeZeroCocycle R A B c)
    ((projection (ordinaryFunctor R R) B).f 0
      ((ordinaryNonnegativeIso R R B.space 0).inv
        (Finsupp.single (constantSimplex B.space x 0) 1)))

lemma relativeZeroValue_ext (B : Pair.{u}) (c e : relativeCohomology R A B 0)
    (h : ∀ x, relativeZeroValue R A B c x = relativeZeroValue R A B e x) : c = e := by
  apply (ModuleCat.mono_iff_injective (relativeZeroCochain R A B)).mp inferInstance
  have hmono : Mono ((relativeToAbsolute R A B).f 0) :=
    (P202.CohomologyPairs.short_exact R A B 0).mono_f
  apply (ModuleCat.mono_iff_injective ((relativeToAbsolute R A B).f 0)).mp hmono
  apply (ordinaryCochainsEquiv R A B.space 0).injective
  apply Finsupp.lhom_ext
  intro s r
  let x := simplexEquiv B.space 0 s (Convexity.StdSimplex.single 0)
  have hs : s = constantSimplex B.space x 0 := simplex_zero_constant B.space s
  rw [hs]
  change (relativeZeroCocycle R A B c)
      ((projection (ordinaryFunctor R R) B).f 0
        ((ordinaryNonnegativeIso R R B.space 0).inv
          (Finsupp.single (constantSimplex B.space x 0) r))) =
    (relativeZeroCocycle R A B e)
      ((projection (ordinaryFunctor R R) B).f 0
        ((ordinaryNonnegativeIso R R B.space 0).inv
          (Finsupp.single (constantSimplex B.space x 0) r)))
  have hr : Finsupp.single (constantSimplex B.space x 0) r =
      r • Finsupp.single (constantSimplex B.space x 0) (1 : R) := by simp
  rw [hr]
  simpa only [relativeZeroValue, map_smul] using congrArg (fun a : A => r • a) (h x)

lemma ordinaryNonnegativeIso_inv_natural {X Y : TopCat.{u}} (f : X ⟶ Y) (k : ℕ) :
    (ordinaryNonnegativeIso R R X k).inv ≫ ((ordinaryFunctor R R).map f).f (k : ℤ) =
      (chainMap R R f).f k ≫ (ordinaryNonnegativeIso R R Y k).inv := by
  change (ordinaryNonnegativeIso R R X k).inv ≫
    (extendMap (chainMap R R f) (degreeEmbedding 0)).f _ = _
  rw [extendMap_f _ _ (show (degreeEmbedding 0).f k = (k : ℤ) by
    change (0 : ℤ) + k = k; omega)]
  simp [ordinaryNonnegativeIso]

lemma map_constantSimplex {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (k : ℕ) :
    (TopCat.toSSet.map f).app (op ⦋k⦌) (constantSimplex X x k) =
      constantSimplex Y (f x) k := by
  apply (simplexEquiv Y k).injective
  ext y
  rfl

lemma relativeZeroValue_natural {B C : Pair.{u}} (f : B ⟶ C)
    (c : relativeCohomology R A C 0) (x : B.space) :
    relativeZeroValue R A B ((relativeCohomologyFunctor R A 0).map f.op c) x =
      relativeZeroValue R A C c (f.map x) := by
  have hn := congrArg (fun a : relativeCohomology R A C 0 ⟶ _ => a c)
    (relativeZeroCochain_natural R A f)
  change relativeZeroCochain R A B ((relativeCohomologyFunctor R A 0).map f.op c) =
    ((relativeCochainFunctor R A).map f.op).f 0 (relativeZeroCochain R A C c) at hn
  have hn' : relativeZeroCocycle R A B ((relativeCohomologyFunctor R A 0).map f.op c) =
      (relativeZeroCocycle R A C c).comp ((relativeMap (ordinaryFunctor R R) f).f 0).hom := hn
  unfold relativeZeroValue
  rw [hn']
  change (relativeZeroCocycle R A C c)
      ((relativeMap (ordinaryFunctor R R) f).f 0
        ((projection (ordinaryFunctor R R) B).f 0
          ((ordinaryNonnegativeIso R R B.space 0).inv
            (Finsupp.single (constantSimplex B.space x 0) 1)))) = _
  have hp := congrArg (fun a => a.f 0) (projection_map (ordinaryFunctor R R) f)
  have hpe := congrArg (fun a : (ordinaryComplex R R B.space).X 0 ⟶ _ =>
    a ((ordinaryNonnegativeIso R R B.space 0).inv
      (Finsupp.single (constantSimplex B.space x 0) 1))) hp
  change (relativeMap (ordinaryFunctor R R) f).f 0
      ((projection (ordinaryFunctor R R) B).f 0 _) = _ at hpe
  rw [hpe]
  change (relativeZeroCocycle R A C c)
    ((projection (ordinaryFunctor R R) C).f 0
      (((ordinaryFunctor R R).map f.map).f 0
        ((ordinaryNonnegativeIso R R B.space 0).inv
          (Finsupp.single (constantSimplex B.space x 0) 1)))) = _
  apply congrArg (relativeZeroCocycle R A C c)
  apply congrArg ((projection (ordinaryFunctor R R) C).f 0)
  have hm := congrArg (fun a : (complex R R B.space).X 0 ⟶ _ =>
      a (Finsupp.single (constantSimplex B.space x 0) 1))
    (ordinaryNonnegativeIso_inv_natural R f.map 0)
  change ((ordinaryFunctor R R).map f.map).f 0
    ((ordinaryNonnegativeIso R R B.space 0).inv _) = _ at hm
  rw [hm]
  change (ordinaryNonnegativeIso R R C.space 0).inv
    ((chainMap R R f.map).f 0 (Finsupp.single (constantSimplex B.space x 0) 1)) = _
  apply congrArg (ordinaryNonnegativeIso R R C.space 0).inv
  change Finsupp.mapDomain ((TopCat.toSSet.map f.map).app (op ⦋0⦌))
    (Finsupp.single (constantSimplex B.space x 0) (1 : R)) = _
  rw [Finsupp.mapDomain_single, map_constantSimplex]

/-- Relative H^0 classes are determined by their pullbacks to points. -/
lemma relativeCohomology_zero_ext (B : Pair.{u}) (c e : relativeCohomology R A B 0)
    (h : ∀ x : B.space,
      (relativeCohomologyFunctor R A 0).map (pointToPair B x).op c =
        (relativeCohomologyFunctor R A 0).map (pointToPair B x).op e) : c = e := by
  apply relativeZeroValue_ext R A B c e
  intro x
  have hx := congrArg (fun z => relativeZeroValue R A pointPair z PUnit.unit) (h x)
  simpa only [relativeZeroValue_natural, pointToPair, TopCat.hom_ofHom, ContinuousMap.coe_mk] using hx

/-- Relative zero-cocycles vanish at every point of the designated subspace. -/
lemma relativeZeroValue_of_mem (B : Pair.{u}) (c : relativeCohomology R A B 0)
    (x : B.space) (hx : x ∈ B.subspace) : relativeZeroValue R A B c x = 0 := by
  let a := quotientCochainsEquiv R A B 0 (relativeZeroCochain R A B c)
  obtain ⟨e, he⟩ := P202.CohomologyPairs.quotient_vanishing R A B 0
  have hz := (P202.CohomologyPairs.vanishing_on_simplices R A B 0 (e a).val).mp
    (e a).property (constantSimplex B.space x 0) (fun _ => hx)
  rw [he] at hz
  have hi := P202.CohomologyPairs.quotient_identification R A B 0
    (relativeZeroCochain R A B c) (Finsupp.single (constantSimplex B.space x 0) 1)
  change relativeZeroValue R A B c x = 0
  change a (Submodule.Quotient.mk (Finsupp.single (constantSimplex B.space x 0) 1)) = _ at hi
  exact hi.symm.trans hz

/-- To detect a relative H^0 class, only points outside the second term are
needed: values on the second term already vanish by the relative definition. -/
lemma relativeCohomology_zero_ext_support (B : Pair.{u}) (c e : relativeCohomology R A B 0)
    (h : ∀ x : B.space, x ∉ B.subspace →
      (relativeCohomologyFunctor R A 0).map (pointToPair B x).op c =
        (relativeCohomologyFunctor R A 0).map (pointToPair B x).op e) : c = e := by
  apply relativeZeroValue_ext R A B c e
  intro x
  by_cases hx : x ∈ B.subspace
  · rw [relativeZeroValue_of_mem R A B c x hx, relativeZeroValue_of_mem R A B e x hx]
  · have hh := congrArg (fun z => relativeZeroValue R A pointPair z PUnit.unit) (h x hx)
    simpa only [relativeZeroValue_natural, pointToPair, TopCat.hom_ofHom, ContinuousMap.coe_mk] using hh

end P202.ThomClass


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

theorem normal_eq_zero_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (z : NormalTotal N) : z = normalZero N z.proj := by
  let p := z.proj
  obtain ⟨a, ha⟩ := (normalBundle N).covers p
  let e := fiberLinearCoordinates N a p ha
  haveI : Subsingleton (Euclidean (n-m)) := by rw [h]; infer_instance
  have hz : z.snd = 0 := e.injective (Subsingleton.elim _ _)
  cases z
  simp_all [normalZero]


theorem tubular_domain_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) : K.domain = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rw [normal_eq_zero_of_rank_zero N h z]
  exact K.zero_mem _

theorem tubular_target_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) : K.target = Set.range i := by
  apply Set.Subset.antisymm _ K.inclusion_mem
  intro x hx
  let z := K.homeomorph.symm ⟨x, hx⟩
  refine ⟨z.val.proj, ?_⟩
  have hz : z = ⟨normalZero N z.val.proj, K.zero_mem _⟩ :=
    Subtype.ext (normal_eq_zero_of_rank_zero N h z.val)
  have he := congrArg Subtype.val (K.homeomorph.apply_symm_apply ⟨x, hx⟩)
  change (K.homeomorph z).val = x at he
  rw [hz, K.zero_eq] at he
  exact he

theorem image_isOpen_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) : IsOpen (Set.range i) := by
  rw [← tubular_target_of_rank_zero N h K]
  exact K.isOpen_target

theorem normalCompatible_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) : NormalCompatible N K := by
  intro p
  obtain ⟨a, hp⟩ := (normalBundle N).covers p
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 (i p)
  haveI : Subsingleton (Euclidean (n-m)) := by rw [h]; infer_instance
  refine ⟨a, hp, c, hc, hpc, 0, ?_, ?_⟩
  · have he : (fun v => (c (fiberImage N K a p hp v)).val) =
        fun _ : Euclidean (n-m) => (c (fiberImage N K a p hp 0)).val := by
      funext v
      rw [Subsingleton.elim v 0]
    rw [he]
    exact hasFDerivAt_const _ _
  · intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]


lemma fiber_eq_origin_of_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (p : P) (z : Fiber N p) : z = fiberOrigin N p := by
  apply Subtype.ext
  exact (normal_eq_zero_of_rank_zero N h z.val).trans
    (congrArg (normalZero N) z.property)

/-- At rank zero, a whole fiber maps canonically into M without choosing a tube. -/
def fiberToAmbientRankZero (N : NormalBundle T S i) (h : n - m = 0) (p : P) :
    fiberPair N p ⟶ ambientPair i where
  map := TopCat.ofHom ⟨fun _ => i p, continuous_const⟩
  mapsTo := by
    intro z hz
    exact (hz (fiber_eq_origin_of_rank_zero N h p z)).elim

/-- At rank zero the slice is the entire normal fiber as an actual pair. -/
def sliceToFiberRankZeroIso (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) (p : P) : slicePair N K p ≅ fiberPair N p where
  hom := sliceToFiber N K p
  inv := {
    map := TopCat.ofHom ⟨fun z => ⟨z.val, z.property, by
      have he := congrArg Subtype.val (fiber_eq_origin_of_rank_zero N h p z)
      change z.val = normalZero N p at he
      rw [he]
      exact K.zero_mem p⟩,
      continuous_subtype_val.subtype_mk _⟩
    mapsTo := by
      intro z hz
      exact (hz (fiber_eq_origin_of_rank_zero N h p z)).elim }
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

lemma sliceToAmbient_factor_rank_zero (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) (p : P) :
    sliceToFiber N K p ≫ fiberToAmbientRankZero N h p = sliceToAmbient N K p := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  have hz : (⟨z.val, z.property.2⟩ : K.domain) =
      ⟨normalZero N p, K.zero_mem p⟩ := by
    apply Subtype.ext
    exact (normal_eq_zero_of_rank_zero N h z.val).trans
      (congrArg (normalZero N) z.property.1)
  change i p = (K.homeomorph ⟨z.val, z.property.2⟩).val
  rw [hz, K.zero_eq]

lemma hasFiberValues_iff_rank_zero (R : Type v) [CommRing R]
    (N : NormalBundle T S i) (h : n - m = 0) (d : ℕ)
    (o : Orientation R N d) (K : TubularNeighborhood N)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) :
    HasFiberValues R o c ↔ ∀ p : P,
      (relativeCohomologyFunctor R R (d : ℤ)).map
        (fiberToAmbientRankZero N h p).op c = o.generator p := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  have he (L : TubularNeighborhood N) (p : P) :
      F.map (sliceToAmbient N L p).op =
        F.map (fiberToAmbientRankZero N h p).op ≫ F.map (sliceToFiber N L p).op := by
    rw [← F.map_comp, ← op_comp, sliceToAmbient_factor_rank_zero]
  constructor
  · intro hc p
    haveI : IsIso (F.map (sliceToFiber N K p).op) := by
      change IsIso (F.map (sliceToFiberRankZeroIso N h K p).hom.op)
      infer_instance
    apply (ConcreteCategory.bijective_of_isIso (F.map (sliceToFiber N K p).op)).injective
    have hp := hc K (normalCompatible_of_rank_zero N h K) p
    rw [he K p] at hp
    exact hp
  · intro hc L hL p
    change F.map (sliceToAmbient N L p).op c = _
    rw [he L p]
    change F.map (sliceToFiber N L p).op
      (F.map (fiberToAmbientRankZero N h p).op c) = _
    rw [hc p]


/-- A rank-zero normal fiber is canonically the one-point pair. -/
def fiberPointIso (N : NormalBundle T S i) (p : P) (h : n - m = 0) :
    fiberPair N p ≅ pointPair.{u} where
  hom := {
    map := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    mapsTo := by
      intro z hz
      exact (hz (fiber_eq_origin_of_rank_zero N h p z)).elim }
  inv := pointToPair (fiberPair N p) (fiberOrigin N p)
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (fun z => (fiber_eq_origin_of_rank_zero N h p z).symm)
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (fun x => by
      change PUnit.unit = x
      exact Subsingleton.elim _ _)

lemma fiberPointIso_inv_comp (N : NormalBundle T S i) (p : P) (h : n - m = 0) :
    (fiberPointIso N p h).inv ≫ fiberToAmbientRankZero N h p =
      pointToPair (ambientPair i) (i p) := PairMap.ext _ _ rfl

lemma hasFiberValues_iff_point_rank_zero (R : Type v) [CommRing R]
    (N : NormalBundle T S i) (h : n - m = 0) (d : ℕ)
    (o : Orientation R N d) (K : TubularNeighborhood N)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) :
    HasFiberValues R o c ↔ ∀ p : P,
      (relativeCohomologyFunctor R R (d : ℤ)).map
        (pointToPair (ambientPair i) (i p)).op c =
      (relativeCohomologyFunctor R R (d : ℤ)).map
        (fiberPointIso N p h).inv.op (o.generator p) := by
  rw [hasFiberValues_iff_rank_zero R N h d o K c]
  let F := relativeCohomologyFunctor R R (d : ℤ)
  have he (p : P) : F.map (pointToPair (ambientPair i) (i p)).op =
      F.map (fiberToAmbientRankZero N h p).op ≫ F.map (fiberPointIso N p h).inv.op := by
    rw [← F.map_comp, ← op_comp, fiberPointIso_inv_comp]
  constructor
  · intro hc p
    rw [he p]
    change F.map (fiberPointIso N p h).inv.op
      (F.map (fiberToAmbientRankZero N h p).op c) = _
    rw [hc p]
  · intro hc p
    haveI : IsIso (F.map (fiberPointIso N p h).inv.op) := by infer_instance
    apply (ConcreteCategory.bijective_of_isIso (F.map (fiberPointIso N p h).inv.op)).injective
    have hp := hc p
    rw [he p] at hp
    exact hp


lemma fiberPointIso_inv_comp_coordinates (N : NormalBundle T S i) (p : P)
    (h : n - m = 0) (a : P) (hp : p ∈ (normalBundle N).baseSet a) :
    (fiberPointIso N p h).inv ≫ fiberCoordinates N a p hp =
      pointToPair (modelPair.{u} (n-m)) (ULift.up 0) := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  exact fiberChart_origin N a p hp

/-- Rank-zero orientation values, transported to a common point group, vary
locally constantly; this follows directly from the actual orientation field. -/
theorem orientation_point_values_locally_constant (R : Type v) [CommRing R]
    (N : NormalBundle T S i) (h : n - m = 0) (d : ℕ) (o : Orientation R N d) :
    IsLocallyConstant (fun p : P =>
      (relativeCohomologyFunctor R R (d : ℤ)).map
        (fiberPointIso N p h).inv.op (o.generator p)) := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨a, U, hU, hpU, hUa, c, hc⟩ := o.locally_constant p
  have he (q : P) (hq : q ∈ U) :
      F.map (fiberPointIso N q h).inv.op (o.generator q) =
        F.map (pointToPair (modelPair.{u} (n-m)) (ULift.up 0)).op c := by
    rw [← hc q hq]
    change (F.map (fiberCoordinates N a q (hUa hq)).op ≫
      F.map (fiberPointIso N q h).inv.op) c = _
    rw [← F.map_comp, ← op_comp, fiberPointIso_inv_comp_coordinates]
  refine ⟨U, hU, hpU, ?_⟩
  intro q hq
  exact (he q hq).trans (he p hpU).symm


/-- A locally constant function on a compact codimension-zero submanifold
extends by zero across its clopen image. No topology on its values is needed. -/
theorem exists_locallyConstant_extension_rank_zero [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (h : n - m = 0)
    (K : TubularNeighborhood N) {V : Type w} [Zero V] (f : LocallyConstant P V) :
    ∃ g : LocallyConstant M V,
      (∀ p : P, g (i p) = f p) ∧ ∀ x : M, x ∉ Set.range i → g x = 0 := by
  classical
  obtain ⟨e, he⟩ := hi.2.2.2
  let fi : LocallyConstant (Set.range i) V :=
    ⟨fun x => f (e.symm x), f.isLocallyConstant.comp_continuous e.symm.continuous⟩
  let fo : LocallyConstant ((Set.range i)ᶜ : Set M) V := LocallyConstant.const _ 0
  have hc : IsClosed (Set.range i) := image_isClosed hi
  have ho : IsClosed ((Set.range i)ᶜ : Set M) :=
    (image_isOpen_of_rank_zero N h K).isClosed_compl
  have hcover : Set.range i ∪ (Set.range i)ᶜ = Set.univ := Set.union_compl_self _
  have hagree : ∀ (x : M) (hx : x ∈ Set.range i ∩ (Set.range i)ᶜ),
      fi ⟨x, hx.1⟩ = fo ⟨x, hx.2⟩ := fun x hx => (hx.2 hx.1).elim
  let g := LocallyConstant.piecewise hc ho hcover fi fo hagree
  refine ⟨g, ?_, ?_⟩
  · intro p
    rw [LocallyConstant.piecewise_apply_left hc ho hcover fi fo hagree (i p) ⟨p, rfl⟩]
    change f (e.symm ⟨i p, ⟨p, rfl⟩⟩) = f p
    have hep : (⟨i p, ⟨p, rfl⟩⟩ : Set.range i) = e p := Subtype.ext (he p).symm
    rw [hep, e.symm_apply_apply]
  · intro x hx
    exact LocallyConstant.piecewise_apply_right hc ho hcover fi fo hagree x hx

end P202.ThomClass



open CategoryTheory Opposite Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

/-- A map tangent to the identity at the origin admits the elementary relative
straight-line homotopy to the identity on a sufficiently small punctured ball. -/
theorem exists_pos_nonvanishing_linear_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} (hf0 : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, (norm x) < ε → x ≠ 0 →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (f x - x) ≠ 0 := by
  have hbound : ∀ᶠ x in 𝓝 (0 : E), (norm (f x - x)) ≤ (1 / 2 : ℝ) * (norm x) := by
    simpa only [hf0, sub_zero, ContinuousLinearMap.id_apply] using
      hf.isLittleO.def (by norm_num : 0 < (1 / 2 : ℝ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨ε, hε, ?_⟩
  intro x hx hx0 t ht heq
  have herr : (norm (f x - x)) ≤ (1 / 2 : ℝ) * (norm x) :=
    hball (by simpa only [dist_zero_right] using hx)
  have hneg : t • (f x - x) = -x := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_comm] using heq
  have hnorm : (norm x) = t * (norm (f x - x)) := by
    calc
      (norm x) = (norm (-x)) := (norm_neg x).symm
      _ = (norm (t • (f x - x))) := congrArg norm hneg.symm
      _ = t * (norm (f x - x)) := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have htbound := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (f x - x))
  have hxpos : 0 < (norm x) := norm_pos_iff.mpr hx0
  nlinarith


/-- The relative pair supported at the origin of an actual real normed space. -/
abbrev puncturedVectorPair (E : Type u) [TopologicalSpace E] [Zero E] : Pair.{u} :=
  ⟨TopCat.of E, {x | x ≠ 0}⟩

/-- The same actual pair homotopy requires continuity only on an open
neighborhood of the origin, as needed for total representatives of smooth germs. -/
theorem exists_pairHomotopyOn_of_hasFDerivAt_id
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0U : 0 ∈ U)
    (hfc : ContinuousOn f U) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (puncturedVectorPair E) {x : E | (norm x) < ε} ⟶ puncturedVectorPair E),
      {x : E | (norm x) < ε} ⊆ U ∧ (∀ x, g.map x = f x.val) ∧
      Nonempty (P202Specs.PrismHomotopy.PairHomotopy
        (openPairInclusion (puncturedVectorPair E) {x : E | (norm x) < ε}) g) := by
  obtain ⟨ε₁, hε₁, hnonzero⟩ := exists_pos_nonvanishing_linear_homotopy hf0 hf
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsmall : {x : E | (norm x) < ε} ⊆ U := by
    intro x hx
    apply hball
    change dist x 0 < ε₂
    simpa only [dist_zero_right] using lt_of_lt_of_le hx (min_le_right ε₁ ε₂)
  have hcont : Continuous (fun x : {x : E // (norm x) < ε} => f x.val) :=
    hfc.comp_continuous continuous_subtype_val (fun x => hsmall x.property)
  have hn : ∀ x : E, (norm x) < ε → x ≠ 0 →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (f x - x) ≠ 0 := by
    intro x hx
    exact hnonzero x (lt_of_lt_of_le hx (min_le_left ε₁ ε₂))
  let g : openPair (puncturedVectorPair E) {x : E | (norm x) < ε} ⟶ puncturedVectorPair E := {
    map := TopCat.ofHom ⟨fun x => f x.val, hcont⟩
    mapsTo := by
      intro x hx
      have hh := hn x.val x.property hx 1 (by simp)
      change f x.val ≠ 0
      simpa only [one_smul, add_sub_cancel] using hh }
  let H : unitInterval × {x : E // (norm x) < ε} → E :=
    fun tx => tx.2.val + tx.1.val • (f tx.2.val - tx.2.val)
  have hH : Continuous H := by
    exact (continuous_subtype_val.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((hcont.comp continuous_snd).sub (continuous_subtype_val.comp continuous_snd)))
  refine ⟨ε, hε, g, hsmall, fun _ => rfl, ⟨?_⟩⟩
  refine {
    homotopy := {
      toFun := H
      continuous_toFun := hH
      map_zero_left := by intro x; simp [H, openPairInclusion]
      map_one_left := by
        intro x
        change x.val + (1 : ℝ) • (f x.val - x.val) = f x.val
        simp }
    preserves := ?_ }
  intro t x
  exact hn x.val.val x.val.property x.property t.val t.property


/-- The local pullback associated to a map tangent to the identity is the
literal excision inclusion pullback, hence an isomorphism in every degree. -/
theorem exists_cohomology_isIsoOn_of_hasFDerivAt_id
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0U : 0 ∈ U)
    (hfc : ContinuousOn f U) (hf0 : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (puncturedVectorPair E) {x : E | (norm x) < ε} ⟶ puncturedVectorPair E),
      {x : E | (norm x) < ε} ⊆ U ∧ (∀ x, g.map x = f x.val) ∧
      ∀ (R : Type v) [CommRing R] (q : ℤ),
        (relativeCohomologyFunctor R R q).map g.op =
          (relativeCohomologyFunctor R R q).map
            (openPairInclusion (puncturedVectorPair E) {x : E | (norm x) < ε}).op ∧
        IsIso ((relativeCohomologyFunctor R R q).map g.op) := by
  obtain ⟨ε, hε, g, hsmall, hg, ⟨H⟩⟩ :=
    exists_pairHomotopyOn_of_hasFDerivAt_id hU h0U hfc hf0 hf
  refine ⟨ε, hε, g, hsmall, hg, ?_⟩
  intro R _ q
  have heq := (P202.CohomologyPairs.homotopy_invariant R R).2 H q
  refine ⟨heq.symm, ?_⟩
  rw [← heq]
  apply openPairInclusion_isIso
  · change IsOpen ({(0 : E)}ᶜ : Set E)
    exact isClosed_singleton.isOpen_compl
  · change IsOpen {x : E | (norm x) < ε}
    exact isOpen_lt continuous_norm continuous_const
  · intro x hx
    change ¬x ≠ 0 at hx
    have hx0 : x = 0 := Classical.not_not.mp hx
    change (norm x) < ε
    simpa only [hx0, norm_zero] using hε

end P202.ThomClass


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- In codimension zero the actual fiber restrictions uniquely determine the
ambient relative class; no connectedness assumption is needed. -/
theorem fiber_values_unique_rank_zero (R : Type v) [CommRing R]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (h : n - m = 0)
    (o : Orientation R N 0) (c e : relativeCohomology R R (ambientPair i) 0)
    (hc : HasFiberValues R o c) (he : HasFiberValues R o e) : c = e := by
  obtain ⟨K⟩ := tubular_exists hi N
  apply relativeCohomology_zero_ext_support R R (ambientPair i) c e
  intro x hx
  have hx' : x ∈ Set.range i := Classical.not_not.mp hx
  obtain ⟨p, rfl⟩ := hx'
  exact ((hasFiberValues_iff_point_rank_zero R N h 0 o K c).mp hc p).trans
    ((hasFiberValues_iff_point_rank_zero R N h 0 o K e).mp he p).symm

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped Simplicial
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.SingularChains
variable (R : Type v) [CommRing R] (A : Type w) [AddCommGroup A] [Module R A]

/-- A degree-zero cochain evaluating locally constant values at vertices. -/
def scalarZeroCochain (X : TopCat.{u}) (f : X → A) : Chains R X 0 →ₗ[R] A :=
  Finsupp.linearCombination R (fun s => f (simplexEquiv X 0 s (Convexity.StdSimplex.single 0)))

lemma scalarZeroCochain_single (X : TopCat.{u}) (f : X → A) (s : Simplex X 0) (r : R) :
    scalarZeroCochain R A X f (Finsupp.single s r) =
      r • f (simplexEquiv X 0 s (Convexity.StdSimplex.single 0)) := by
  exact Finsupp.linearCombination_single _ _ _

lemma scalarZeroCochain_boundary (X : TopCat.{u}) (f : LocallyConstant X A) :
    (scalarZeroCochain R A X f).comp (boundary R R X 0) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  change scalarZeroCochain R A X f (boundary R R X 0 (Finsupp.single s r)) = 0
  rw [P202.SingularChains.boundary_single]
  change scalarZeroCochain R A X f
    (∑ i : Fin 2, (-1 : ℤ)^i.val • Finsupp.single (face i s) r) = 0
  have hb : (∑ i : Fin 2, (-1 : ℤ)^i.val • Finsupp.single (face i s) r) =
      Finsupp.single (face 0 s) r - Finsupp.single (face 1 s) r := by
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [hb, map_sub, scalarZeroCochain_single, scalarZeroCochain_single]
  have hc : IsLocallyConstant (f ∘ simplexEquiv X 1 s) :=
    f.isLocallyConstant.comp_continuous (simplexEquiv X 1 s).continuous
  have he := hc.apply_eq_of_preconnectedSpace
    (faceInclusion (0 : Fin 2) (Convexity.StdSimplex.single 0))
    (faceInclusion (1 : Fin 2) (Convexity.StdSimplex.single 0))
  change f ((simplexEquiv X 1 s) _) = f ((simplexEquiv X 1 s) _) at he
  rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_face]
  change r • f ((simplexEquiv X 1 s) _) - (r • f ((simplexEquiv X 1 s) _)) = 0
  rw [he, sub_self]


lemma scalarZeroCochain_restriction (B : Pair.{u}) (f : B.space → A)
    (hf : ∀ x ∈ B.subspace, f x = 0) :
    (restriction R A B).f 0 ((ordinaryCochainsEquiv R A B.space 0).symm
      (scalarZeroCochain R A B.space f)) = 0 := by
  apply (ordinaryCochainsEquiv R A B.sub 0).injective
  apply Finsupp.lhom_ext
  intro s r
  change (scalarZeroCochain R A B.space f)
    ((ordinaryNonnegativeIso R R B.space 0).hom
      (((ordinaryFunctor R R).map B.inclusion).f 0
        ((ordinaryNonnegativeIso R R B.sub 0).inv (Finsupp.single s r)))) = 0
  have hn := congrArg (fun a : (complex R R B.sub).X 0 ⟶ _ => a (Finsupp.single s r))
    (ordinaryNonnegativeIso_inv_natural R B.inclusion 0)
  change ((ordinaryFunctor R R).map B.inclusion).f 0
    ((ordinaryNonnegativeIso R R B.sub 0).inv _) = _ at hn
  rw [hn]
  change (scalarZeroCochain R A B.space f)
    ((ordinaryNonnegativeIso R R B.space 0).hom
      ((ordinaryNonnegativeIso R R B.space 0).inv
        ((chainMap R R B.inclusion).f 0 (Finsupp.single s r)))) = 0
  rw [Iso.inv_hom_id_apply]
  rw [P202.SingularChains.chainMap_single, scalarZeroCochain_single]
  have hv := hf ((simplexEquiv B.sub 0 s (Convexity.StdSimplex.single 0)).val)
    (simplexEquiv B.sub 0 s (Convexity.StdSimplex.single 0)).property
  change r • f ((simplexEquiv B.sub 0 s (Convexity.StdSimplex.single 0)).val) = 0
  rw [hv, smul_zero]

/-- Every scalar zero-cochain vanishing on the relative subspace lifts to the
actual relative cochain object. -/
lemma scalarZeroCochain_relative_lift (B : Pair.{u}) (f : B.space → A)
    (hf : ∀ x ∈ B.subspace, f x = 0) :
    ∃ a : (relativeCochains R A B).X 0,
      (relativeToAbsolute R A B).f 0 a =
        (ordinaryCochainsEquiv R A B.space 0).symm (scalarZeroCochain R A B.space f) := by
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (P202.CohomologyPairs.short_exact R A B 0).exact _
      (scalarZeroCochain_restriction R A B f hf)


lemma scalarZeroCochain_cocycle (X : TopCat.{u}) (f : LocallyConstant X A) :
    (ordinaryCochains R A X).d 0 1
      ((ordinaryCochainsEquiv R A X 0).symm (scalarZeroCochain R A X f)) = 0 := by
  apply (ordinaryCochainsEquiv R A X 1).injective
  apply LinearMap.ext
  intro c
  change (ordinaryCochainsEquiv R A X 1
    ((ordinaryCochains R A X).d 0 1
      ((ordinaryCochainsEquiv R A X 0).symm (scalarZeroCochain R A X f)))) c = 0
  exact (P202.CohomologyPairs.natural_coboundary R A X 0
    (scalarZeroCochain R A X f) c).trans
      (congrArg (fun l : Chains R X 1 →ₗ[R] A => l c)
        (scalarZeroCochain_boundary R A X f))

/-- A locally constant function vanishing on the relative subspace determines
an actual degree-zero relative cohomology class, with exactly those values. -/
theorem exists_relativeH0_of_locallyConstant (B : Pair.{u}) (f : LocallyConstant B.space A)
    (hf : ∀ x ∈ B.subspace, f x = 0) :
    ∃ c : relativeCohomology R A B 0, ∀ x,
      relativeZeroValue R A B c x = f x := by
  obtain ⟨a, ha⟩ := scalarZeroCochain_relative_lift R A B f hf
  let K := relativeCochains R A B
  have hca : K.d 0 1 a = 0 := by
    have hmono : Mono ((relativeToAbsolute R A B).f 1) :=
      (P202.CohomologyPairs.short_exact R A B 1).mono_f
    apply (ModuleCat.mono_iff_injective ((relativeToAbsolute R A B).f 1)).mp hmono
    have hh := congrArg (fun k : (relativeCochains R A B).X 0 ⟶ _ => k a)
      ((relativeToAbsolute R A B).comm 0 1)
    change (ordinaryCochains R A B.space).d 0 1 ((relativeToAbsolute R A B).f 0 a) =
      (relativeToAbsolute R A B).f 1 (K.d 0 1 a) at hh
    rw [ha, scalarZeroCochain_cocycle R A B.space f] at hh
    simpa only [map_zero] using hh.symm
  let cy := K.cyclesMk a 1 (by simp) hca
  let c := K.homologyπ 0 cy
  have hrep : relativeZeroCochain R A B c = a := by
    change K.iCycles 0 ((K.isoHomologyπ (-1) 0 (by simp) _).inv (K.homologyπ 0 cy)) = a
    have he := congrArg (fun k : K.cycles 0 ⟶ K.cycles 0 => k cy)
      (K.isoHomologyπ_hom_inv_id (-1) 0 (by simp)
        (((P202.CohomologyPairs.negative R A).2 B (-1) (by decide)).1.eq_of_src _ _))
    change (K.isoHomologyπ (-1) 0 (by simp) _).inv (K.homologyπ 0 cy) = cy at he
    rw [he]
    exact K.i_cyclesMk a 1 (by simp) hca
  refine ⟨c, ?_⟩
  intro x
  unfold relativeZeroValue relativeZeroCocycle
  rw [hrep]
  have he := congrArg (fun b =>
      ordinaryCochainsEquiv R A B.space 0 b
        (Finsupp.single (constantSimplex B.space x 0) (1 : R))) ha
  change (show (ordinary R R B).X 0 →ₗ[R] A from a)
    ((projection (ordinaryFunctor R R) B).f 0
      ((ordinaryNonnegativeIso R R B.space 0).inv
        (Finsupp.single (constantSimplex B.space x 0) 1))) = _ at he
  rw [he]
  simp [constantSimplex, scalarZeroCochain]

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
variable (R : Type u) [CommRing R]

/-- A bounded-below projective chain complex with one projective homology
module is actually chain homotopy equivalent to that module in its degree.
The chain map is constructed by lifting a homology generator to cycles. -/
theorem homotopyEquiv_single_of_homology_concentrated
    (K : ChainComplex (ModuleCat.{v} R) ℤ) [∀ q, Projective (K.X q)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K)
    (d : ℤ) (A : ModuleCat.{v} R) [Projective A]
    (e : K.homology d ≅ A)
    (hzero : ∀ q : ℤ, q ≠ d → IsZero (K.homology q)) :
    Nonempty (HomotopyEquiv ((single (ModuleCat.{v} R) (.down ℤ) d).obj A) K) := by
  let C := (single (ModuleCat.{v} R) (.down ℤ) d).obj A
  let l : A ⟶ K.cycles d := Projective.factorThru e.inv (K.homologyπ d)
  have hl : l ≫ K.homologyπ d = e.inv := Projective.factorThru_comp _ _
  let f : C ⟶ K := mkHomFromSingle (l ≫ K.iCycles d) (by
    intro q hq
    rw [Category.assoc, K.iCycles_d, comp_zero])
  have hf : homologyMap f d = (singleObjHomologySelfIso (.down ℤ) d A).hom ≫ e.inv := by
    have hcycles : cyclesMap f d = (singleObjCyclesSelfIso (.down ℤ) d A).hom ≫ l := by
      apply (cancel_mono (K.iCycles d)).mp
      rw [cyclesMap_i]
      change C.iCycles d ≫ f.f d = _
      simp only [f, mkHomFromSingle_f, Category.assoc]
      rfl
    apply (cancel_epi (C.homologyπ d)).mp
    rw [homologyπ_naturality, hcycles, Category.assoc, hl,
      ← Category.assoc, homologyπ_singleObjHomologySelfIso_hom]
  haveI : QuasiIso f := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hq : q = d
    · subst q
      rw [hf]
      infer_instance
    · have hC : IsZero (C.homology q) := isZero_single_obj_homology (.down ℤ) d A q hq
      have hL := hzero q hq
      haveI : Mono (homologyMap f q) := hC.mono _
      haveI : Epi (homologyMap f q) := hL.epi _
      exact isIso_of_mono_of_epi _
  haveI : ∀ q, Projective (C.X q) := by
    intro q
    by_cases hq : q = d
    · subst q
      exact Projective.of_iso (singleObjXSelf (.down ℤ) d A).symm inferInstance
    · exact (isZero_single_obj_X (.down ℤ) d A q hq).projective
  have hC : P202Specs.FreeChainDual.BoundedBelow C :=
    ⟨d, fun q hq => isZero_single_obj_X (.down ℤ) d A q (by omega)⟩
  obtain ⟨h, _⟩ := P202.CohomologyExcisionMV.projective_comparison_homotopy R hC hK f
  exact ⟨h⟩

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped Simplicial TensorProduct
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.AlexanderWhitney
variable (R : Type u) [CommRing R]

lemma chain_map_nonnegative_split {X Y : TopCat.{v}} (g : X ⟶ Y)
    (hg : Function.Injective g) (n : ℕ) :
    ∃ r : (complex R R Y).X n ⟶ (complex R R X).X n,
      (chainMap R R g).f n ≫ r = 𝟙 _ := by
  have hs : Function.Injective ((TopCat.toSSet.map g).app (op ⦋n⦌)) := by
    intro s t h
    apply (simplexEquiv X n).injective
    ext x
    apply hg
    have he := congrArg (fun z => simplexEquiv Y n z x) h
    simpa only [P202.SingularChains.simplexEquiv_postcomp, ContinuousMap.comp_apply] using he
  refine ⟨ModuleCat.ofHom (Finsupp.lcomapDomain (R := R) _ hs), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := R) _ hs

/-- Tensoring the second-factor subspace inclusion with the first singular
complex preserves its degreewise split injection in the actual total complex. -/
lemma tensor_second_map_split {X Y Z : TopCat.{v}} (g : Y ⟶ Z)
    (hg : Function.Injective g) (n : ℕ) :
    ∃ r : (tensorComplex R X Z).X n ⟶ (tensorComplex R X Y).X n,
      (P202.AlexanderWhitney.tensorChainMap R (𝟙 X) g).f n ≫ r = 𝟙 _ := by
  choose r hr using fun k => chain_map_nonnegative_split R g hg k
  let s : Total R X Z n →ₗ[R] Total R X Y n := {
    toFun := fun z i => TensorProduct.map LinearMap.id (r i.val.2).hom (z i)
    map_add' := by intro x y; ext i; exact map_add _ _ _
    map_smul' := by
      intro a x
      ext i
      change TensorProduct.map _ _ (a • x i) = a • _
      exact map_smul _ _ _ }
  refine ⟨ModuleCat.ofHom s, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map LinearMap.id (r i.val.2).hom
      (TensorProduct.map ((chainMap R R (𝟙 X)).f i.val.1).hom
        ((chainMap R R g).f i.val.2).hom (z i)) = z i
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  have hri : (r i.val.2).hom.comp ((chainMap R R g).f i.val.2).hom = LinearMap.id :=
    congrArg ModuleCat.Hom.hom (hr i.val.2)
  simp only [hri, P202.SingularChains.chainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]


/-- Cokernels of the literal second-factor maps, before the homeomorphic
identification with the standard relative product pair. -/
abbrev productSecondInclusion (X : TopCat.{v}) (B : Pair.{v}) :=
  chainMap R R (productMap (𝟙 X) B.inclusion)
abbrev tensorSecondInclusion (X : TopCat.{v}) (B : Pair.{v}) :=
  P202.AlexanderWhitney.tensorChainMap R (𝟙 X) B.inclusion
abbrev relativeProductComplex (X : TopCat.{v}) (B : Pair.{v}) :=
  cokernel (productSecondInclusion R X B)
abbrev relativeTensorComplex (X : TopCat.{v}) (B : Pair.{v}) :=
  cokernel (tensorSecondInclusion R X B)

def relativeAW (X : TopCat.{v}) (B : Pair.{v}) :
    relativeProductComplex R X B ⟶ relativeTensorComplex R X B :=
  cokernel.map _ _ (P202.EilenbergZilber.comparison R X B.sub).toTensor
    (P202.EilenbergZilber.comparison R X B.space).toTensor
    (P202.EilenbergZilber.comparison_toTensor_natural R (𝟙 X) B.inclusion)

lemma productSecondInclusion_mono (X : TopCat.{v}) (B : Pair.{v}) :
    Mono (productSecondInclusion R X B) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  obtain ⟨r, hr⟩ := chain_map_nonnegative_split R
    (productMap (𝟙 X) B.inclusion) (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z : productSpace X B.space => z.1) h
      · exact Subtype.ext (congrArg (fun z : productSpace X B.space => z.2) h)) n
  exact SplitMono.mono ⟨r, hr⟩

lemma tensorSecondInclusion_mono (X : TopCat.{v}) (B : Pair.{v}) :
    Mono (tensorSecondInclusion R X B) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  obtain ⟨r, hr⟩ := tensor_second_map_split R (X := X) B.inclusion
    Subtype.val_injective n
  exact SplitMono.mono ⟨r, hr⟩

lemma comparison_toTensor_quasiIso (X Y : TopCat.{v}) :
    QuasiIso (P202.EilenbergZilber.comparison R X Y).toTensor := by
  obtain ⟨h, k, _, _⟩ := P202.EilenbergZilber.naturalHomotopies R
  exact (P202.EilenbergZilber.equivalenceOfHomotopies R h k X Y).quasiIso_hom

/-- Relative AW is a quasi-isomorphism for an arbitrary second-factor pair.
This follows from the actual absolute equivalences and exact cokernel rows,
without assuming an unconstructed relative chain equivalence. -/
lemma relativeAW_quasiIso (X : TopCat.{v}) (B : Pair.{v}) :
    QuasiIso (relativeAW R X B) := by
  let S := ShortComplex.cokernelSequence (productSecondInclusion R X B)
  let T := ShortComplex.cokernelSequence (tensorSecondInclusion R X B)
  let φ : S ⟶ T := ShortComplex.Hom.mk
    (P202.EilenbergZilber.comparison R X B.sub).toTensor
    (P202.EilenbergZilber.comparison R X B.space).toTensor
    (relativeAW R X B)
    (P202.EilenbergZilber.comparison_toTensor_natural R (𝟙 X) B.inclusion).symm
    (cokernel.π_desc _ _ _).symm
  haveI := productSecondInclusion_mono R X B
  haveI := tensorSecondInclusion_mono R X B
  have hS : S.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := by change Mono (productSecondInclusion R X B); infer_instance
    epi_g := inferInstance }
  have hT : T.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := by change Mono (tensorSecondInclusion R X B); infer_instance
    epi_g := inferInstance }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT
    (comparison_toTensor_quasiIso R X B.sub) (comparison_toTensor_quasiIso R X B.space)


/-- A degreewise split quotient of a projective complex has projective terms. -/
lemma projective_cokernel_X_of_degreewise_split
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{v} R) c} (f : K ⟶ L)
    [∀ q, Projective (L.X q)]
    (h : ∀ q, ∃ r : L.X q ⟶ K.X q, f.f q ≫ r = 𝟙 _) (q : ι) :
    Projective ((cokernel f).X q) := by
  haveI : Mono f := HomologicalComplex.mono_of_mono_f f (fun q => by
    obtain ⟨r, hr⟩ := h q
    exact SplitMono.mono ⟨r, hr⟩)
  have hs : (ShortComplex.cokernelSequence f).ShortExact := {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := inferInstanceAs (Mono f)
    epi_g := inferInstance }
  have hsq := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hs q
  obtain ⟨r, hr⟩ := h q
  let S := (ShortComplex.cokernelSequence f).map (eval _ _ q)
  let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hsq.exact r hr hsq.epi_g
  exact @Retract.projective _ _ S.X₃ S.X₂ ⟨σ.s, S.g, σ.s_g⟩
    (by change Projective (L.X q); infer_instance)

lemma relativeProductComplex_projective (X : TopCat.{v}) (B : Pair.{v}) (n : ℕ) :
    Projective ((relativeProductComplex R X B).X n) := by
  haveI : ∀ n, Projective ((complex R R (productSpace X B.space)).X n) := by
    intro n
    exact ModuleCat.projective_of_free (Finsupp.basisSingleOne)
  exact projective_cokernel_X_of_degreewise_split R (productSecondInclusion R X B)
    (fun n => chain_map_nonnegative_split R (productMap (𝟙 X) B.inclusion)
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg (fun z : productSpace X B.space => z.1) h
        · exact Subtype.ext (congrArg (fun z : productSpace X B.space => z.2) h)) n) n

lemma relativeTensorComplex_projective (X : TopCat.{v}) (B : Pair.{v}) (n : ℕ) :
    Projective ((relativeTensorComplex R X B).X n) := by
  haveI : ∀ n, Projective ((P202.AlexanderWhitney.tensorComplex R X B.space).X n) := by
    intro n
    change Projective (ModuleCat.of R (Total R X B.space n))
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (Total R X B.space n))
  exact projective_cokernel_X_of_degreewise_split R (tensorSecondInclusion R X B)
    (fun n => tensor_second_map_split R B.inclusion Subtype.val_injective n) n

/-- Integer extension of a nonnegative projective complex is still degreewise
projective and bounded below, with its original nonnegative terms preserved. -/
lemma nonnegative_extend_projective
    (K : ChainComplex (ModuleCat.{v} R) ℕ) [∀ n, Projective (K.X n)] (q : ℤ) :
    Projective ((K.extend (degreeEmbedding 0)).X q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact Projective.of_iso (K.extendXIso (degreeEmbedding 0)
      (show (degreeEmbedding 0).f n = (n : ℤ) by change (0 : ℤ) + n = n; omega)).symm inferInstance
  · exact (isZero_extend_X K (degreeEmbedding 0) q (by
      intro n hn
      change (0 : ℤ) + n = q at hn
      omega)).projective

lemma nonnegative_extend_boundedBelow (K : ChainComplex (ModuleCat.{v} R) ℕ) :
    P202Specs.FreeChainDual.BoundedBelow (K.extend (degreeEmbedding 0)) := by
  refine ⟨0, fun q hq => isZero_extend_X K (degreeEmbedding 0) q ?_⟩
  intro n hn
  change (0 : ℤ) + n = q at hn
  omega

/-- Actual relative Eilenberg--Zilber over an arbitrary second-factor pair,
in the shared integer grading. The homotopy inverse is obtained from the
proved relative quasi-isomorphism between projective complexes. -/
theorem relativeAW_integer_homotopy (X : TopCat.{v}) (B : Pair.{v}) :
    ∃ e : HomotopyEquiv
      ((relativeProductComplex R X B).extend (degreeEmbedding 0))
      ((relativeTensorComplex R X B).extend (degreeEmbedding 0)),
      e.hom = extendMap (relativeAW R X B) (degreeEmbedding 0) := by
  haveI : ∀ n, Projective ((relativeProductComplex R X B).X n) :=
    relativeProductComplex_projective R X B
  haveI : ∀ n, Projective ((relativeTensorComplex R X B).X n) :=
    relativeTensorComplex_projective R X B
  haveI : ∀ q, Projective (((relativeProductComplex R X B).extend (degreeEmbedding 0)).X q) :=
    nonnegative_extend_projective R _
  haveI : ∀ q, Projective (((relativeTensorComplex R X B).extend (degreeEmbedding 0)).X q) :=
    nonnegative_extend_projective R _
  haveI := relativeAW_quasiIso R X B
  exact P202.CohomologyExcisionMV.projective_comparison_homotopy R
    (nonnegative_extend_boundedBelow R _) (nonnegative_extend_boundedBelow R _)
    (extendMap (relativeAW R X B) (degreeEmbedding 0))


/-- The literal relative product pair with only the second factor punctured. -/
def secondProductPair (X : TopCat.{v}) (B : Pair.{v}) : Pair.{v} :=
  ⟨productSpace X B.space, {z | z.2 ∈ B.subspace}⟩

/-- The second-factor product subspace has exactly its induced product topology. -/
def secondProductSubspaceIso (X : TopCat.{v}) (B : Pair.{v}) :
    productSpace X B.sub ≅ (secondProductPair X B).sub :=
  TopCat.isoOfHomeo {
    toFun := fun z => ⟨(z.1, z.2.val), z.2.property⟩
    invFun := fun z => (z.val.1, ⟨z.val.2, z.property⟩)
    left_inv := fun z => rfl
    right_inv := fun z => rfl
    continuous_toFun := (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

/-- The relative-product cokernel used above is the actual shared relative
singular complex of the product pair, with its original quotient map. -/
def relativeProductComplexIso (X : TopCat.{v}) (B : Pair.{v}) :
    relativeProductComplex R X B ≅ nonnegative R R (secondProductPair X B) :=
  cokernel.mapIso (productSecondInclusion R X B)
    (inclusion (chainFunctor R R) (secondProductPair X B))
    ((chainFunctor R R).mapIso (secondProductSubspaceIso X B))
    (Iso.refl _) (by
      change chainMap R R (productMap (𝟙 X) B.inclusion) ≫ 𝟙 _ =
        (chainFunctor R R).map (secondProductSubspaceIso X B).hom ≫
          (chainFunctor R R).map (secondProductPair X B).inclusion
      rw [Category.comp_id, ← Functor.map_comp]
      rfl)

/-- Relative EZ for the actual product pair in the chapter's integer grading,
with its true induced subspace and arbitrary ring coefficients. -/
theorem secondProduct_relative_eilenbergZilber (X : TopCat.{v}) (B : Pair.{v}) :
    Nonempty (HomotopyEquiv (ordinary R R (secondProductPair X B))
      ((relativeTensorComplex R X B).extend (degreeEmbedding 0))) := by
  obtain ⟨e, _⟩ := relativeAW_integer_homotopy R X B
  let a := ((degreeEmbedding 0).extendFunctor _).mapIso (relativeProductComplexIso R X B)
  let b := P202.CohomologyExcisionMV.relativeExtensionIso R (secondProductPair X B)
  exact ⟨(HomotopyEquiv.ofIso (a ≪≫ b).symm).trans e⟩

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- The complete Thom existence and uniqueness conclusion in codimension zero.
The class is constructed from the actual locally compatible fiber values and
extended by zero across the compact embedding's clopen image. -/
theorem exists_unique_of_rank_zero [CompactSpace P]
    (R : Type v) [CommRing R]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (h : n - m = 0)
    (o : Orientation R N 0) :
    (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
      ∃! c : relativeCohomology R R (ambientPair i) 0, HasFiberValues R o c := by
  obtain ⟨K, hK⟩ := normalized_tubular_exists hi N
  let b := fun p : P => (relativeCohomologyFunctor R R 0).map
    (fiberPointIso N p h).inv.op (o.generator p)
  have hb : IsLocallyConstant b := orientation_point_values_locally_constant R N h 0 o
  let f : LocallyConstant P R :=
    ⟨fun p => relativeZeroValue R R pointPair (b p) PUnit.unit,
      hb.comp (fun z => relativeZeroValue R R pointPair z PUnit.unit)⟩
  obtain ⟨g, hgp, hgzero⟩ := exists_locallyConstant_extension_rank_zero hi N h K f
  obtain ⟨c, hc⟩ := exists_relativeH0_of_locallyConstant R R (ambientPair i) g
    (fun x hx => hgzero x hx)
  have hcv : HasFiberValues R o c := by
    apply (hasFiberValues_iff_point_rank_zero R N h 0 o K c).mpr
    intro p
    apply relativeZeroValue_ext R R pointPair
    intro x
    have hx : x = PUnit.unit := by cases x; rfl
    rw [hx]
    calc
      _ = relativeZeroValue R R (ambientPair i) c (i p) :=
        relativeZeroValue_natural R R (pointToPair (ambientPair i) (i p)) c PUnit.unit
      _ = g (i p) := hc (i p)
      _ = f p := hgp p
      _ = relativeZeroValue R R pointPair (b p) PUnit.unit := rfl
  refine ⟨⟨K, hK⟩, c, hcv, ?_⟩
  intro e he
  exact fiber_values_unique_rank_zero R hi N h o e c he hcv

/-- The original degree-zero boundary case, retaining the pointwise rank law
so the empty submanifold is also covered when its declared dimensions differ. -/
theorem exists_unique_of_degree_zero [CompactSpace P]
    (R : Type v) [CommRing R]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i)
    (hrank : ∀ _ : P, 0 = n - m) (o : Orientation R N 0) :
    (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
      ∃! c : relativeCohomology R R (ambientPair i) 0, HasFiberValues R o c := by
  cases isEmpty_or_nonempty P with
  | inl hP =>
    letI := hP
    exact exists_unique_of_isEmpty R 0 hi N o
  | inr hP =>
    exact exists_unique_of_rank_zero R hi N (hrank (Classical.choice hP)).symm o

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.ThomClass
open P202Specs.AlexanderWhitney
variable (R : Type u) [CommRing R]
abbrev Chain := ChainComplex (ModuleCat.{max u v} R) ℕ
abbrev TensorTotal (K L : Chain.{u,v} R) (n : ℕ) :=
  (i : Diagonal n) → K.X i.val.1 ⊗[R] L.X i.val.2

def tensorLeftBoundary (K L : Chain.{u,v} R) (p q : ℕ) :
    K.X (p+1) ⊗[R] L.X q →ₗ[R] K.X p ⊗[R] L.X q :=
  (K.d (p+1) p).hom.rTensor (L.X q)
def tensorRightBoundary (K L : Chain.{u,v} R) (p q : ℕ) :
    K.X p ⊗[R] L.X (q+1) →ₗ[R] K.X p ⊗[R] L.X q :=
  (L.d (q+1) q).hom.lTensor (K.X p)
def tensorTotalBoundary (K L : Chain.{u,v} R) (n : ℕ) :
    TensorTotal.{u,v} R K L (n+1) →ₗ[R] TensorTotal.{u,v} R K L n where
  toFun z i := tensorLeftBoundary R K L i.val.1 i.val.2
      (z ⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩) +
    (-1 : ℤ)^i.val.1 • tensorRightBoundary R K L i.val.1 i.val.2
      (z ⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩)
  map_add' z z' := by ext i; simp [map_add, smul_add]; abel
  map_smul' r z := by
    ext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add]
    rw [smul_comm r]
lemma tensorLeftBoundary_squared (K L : Chain.{u,v} R) (p q : ℕ)
    (z : K.X (p+1+1) ⊗[R] L.X q) :
    tensorLeftBoundary R K L p q (tensorLeftBoundary R K L (p+1) q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change (K.d (p+1) p (K.d (p+2) (p+1) a)) ⊗ₜ[R] b = 0
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.d_comp_d (p+2) (p+1) p)) a
    change K.d (p+1) p (K.d (p+2) (p+1) a) = 0 at h
    rw [h, TensorProduct.zero_tmul]
lemma tensorRightBoundary_squared (K L : Chain.{u,v} R) (p q : ℕ)
    (z : K.X p ⊗[R] L.X (q+1+1)) :
    tensorRightBoundary R K L p q (tensorRightBoundary R K L p (q+1) z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change a ⊗ₜ[R] (L.d (q+1) q (L.d (q+2) (q+1) b)) = 0
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (L.d_comp_d (q+2) (q+1) q)) b
    change L.d (q+1) q (L.d (q+2) (q+1) b) = 0 at h
    rw [h, TensorProduct.tmul_zero]
lemma tensorBoundaries_commute (K L : Chain.{u,v} R) (p q : ℕ)
    (z : K.X (p+1) ⊗[R] L.X (q+1)) :
    tensorLeftBoundary R K L p q (tensorRightBoundary R K L (p+1) q z) =
      tensorRightBoundary R K L p q (tensorLeftBoundary R K L p (q+1) z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b => rfl
lemma tensorTotalBoundary_square (K L : Chain.{u,v} R) (n : ℕ) :
    (tensorTotalBoundary R K L n).comp (tensorTotalBoundary R K L (n+1)) = 0 := by
  apply LinearMap.ext
  intro z
  funext i
  simp only [LinearMap.comp_apply, tensorTotalBoundary, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, map_zsmul, tensorLeftBoundary_squared, tensorRightBoundary_squared,
    tensorBoundaries_commute, smul_zero, zero_add, add_zero, pow_succ, mul_smul,
    neg_one_zsmul, smul_neg, map_neg, neg_add_cancel, LinearMap.zero_apply, Pi.zero_apply]
def totalTensorComplex (K L : Chain.{u,v} R) : Chain.{u,v} R :=
  ChainComplex.of (fun n => ModuleCat.of R (TensorTotal.{u,v} R K L n))
    (fun n => ModuleCat.ofHom (tensorTotalBoundary R K L n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact tensorTotalBoundary_square R K L n)

def tensorTotalMap {K K' L L' : Chain.{u,v} R}
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    TensorTotal.{u,v} R K L n →ₗ[R] TensorTotal.{u,v} R K' L' n where
  toFun z i := TensorProduct.map (f.f i.val.1).hom (g.f i.val.2).hom (z i)
  map_add' := by intros; ext i; apply map_add
  map_smul' r z := by
    ext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _
lemma tensorTotalMap_left {K K' L L' : Chain.{u,v} R}
    (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) (z : K.X (p+1) ⊗[R] L.X q) :
    tensorLeftBoundary R K' L' p q
      (TensorProduct.map (f.f (p+1)).hom (g.f q).hom z) =
    TensorProduct.map (f.f p).hom (g.f q).hom
      (tensorLeftBoundary R K L p q z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change (K'.d (p+1) p (f.f (p+1) a)) ⊗ₜ[R] (g.f q b) =
      (f.f p (K.d (p+1) p a)) ⊗ₜ[R] (g.f q b)
    exact congrArg (fun t => t ⊗ₜ[R] (g.f q b))
      (congrArg (fun k : K.X (p+1) ⟶ K'.X p => k a) (f.comm (p+1) p))
lemma tensorTotalMap_right {K K' L L' : Chain.{u,v} R}
    (f : K ⟶ K') (g : L ⟶ L') (p q : ℕ) (z : K.X p ⊗[R] L.X (q+1)) :
    tensorRightBoundary R K' L' p q
      (TensorProduct.map (f.f p).hom (g.f (q+1)).hom z) =
    TensorProduct.map (f.f p).hom (g.f q).hom
      (tensorRightBoundary R K L p q z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change (f.f p a) ⊗ₜ[R] (L'.d (q+1) q (g.f (q+1) b)) =
      (f.f p a) ⊗ₜ[R] (g.f q (L.d (q+1) q b))
    exact congrArg (fun t => (f.f p a) ⊗ₜ[R] t)
      (congrArg (fun k : L.X (q+1) ⟶ L'.X q => k b) (g.comm (q+1) q))
lemma tensorTotalMap_boundary {K K' L L' : Chain.{u,v} R}
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    (tensorTotalBoundary R K' L' n).comp (tensorTotalMap R f g (n+1)) =
    (tensorTotalMap R f g n).comp (tensorTotalBoundary R K L n) := by
  ext z i
  simp [tensorTotalBoundary, tensorTotalMap, map_add, map_zsmul,
    tensorTotalMap_left, tensorTotalMap_right]
def totalTensorMap {K K' L L' : Chain.{u,v} R} (f : K ⟶ K') (g : L ⟶ L') :
    totalTensorComplex R K L ⟶ totalTensorComplex R K' L' :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (tensorTotalMap R f g n)) (by
    intro n
    simp only [totalTensorComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    exact tensorTotalMap_boundary R f g n)

lemma totalTensorMap_second_zero {K L M N : Chain.{u,v} R}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : f ≫ g = 0) :
    totalTensorMap R (𝟙 K) f ≫ totalTensorMap R (𝟙 K) g = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map LinearMap.id (g.f i.val.2).hom
    (TensorProduct.map LinearMap.id (f.f i.val.2).hom (z i)) = 0
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  have hz : (g.f i.val.2).hom.comp (f.f i.val.2).hom = 0 := by
    exact congrArg (fun k : L ⟶ N => (k.f i.val.2).hom) hfg
  simp [hz]
lemma tensorTotalMap_cokernel_exact (K : Chain.{u,v} R)
    {L M : Chain.{u,v} R} (f : L ⟶ M) (n : ℕ) :
    Function.Exact (tensorTotalMap R (𝟙 K) f n)
      (tensorTotalMap R (𝟙 K) (cokernel.π f) n) := by
  have hc : ∀ i : Diagonal n,
      Function.Exact ((f.f i.val.2).hom.lTensor (K.X i.val.1))
        (((cokernel.π f).f i.val.2).hom.lTensor (K.X i.val.1)) := by
    intro i
    apply lTensor_exact
    · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        ((ShortComplex.cokernelSequence f).map (eval _ _ i.val.2))).mp
          ((ShortComplex.cokernelSequence_exact f).map (eval _ _ i.val.2))
    · exact (ModuleCat.epi_iff_surjective ((cokernel.π f).f i.val.2)).mp inferInstance
  intro y
  constructor
  · intro hy
    have he : ∀ i : Diagonal n, ∃ z,
        TensorProduct.map LinearMap.id (f.f i.val.2).hom z = y i := by
      intro i
      apply (hc i (y i)).mp
      exact congrFun hy i
    choose z hz using he
    exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩
    funext i
    exact (hc i _).mpr ⟨z i, rfl⟩
lemma tensorTotalMap_cokernel_surjective (K : Chain.{u,v} R)
    {L M : Chain.{u,v} R} (f : L ⟶ M) (n : ℕ) :
    Function.Surjective (tensorTotalMap R (𝟙 K) (cokernel.π f) n) := by
  intro z
  have he : ∀ i : Diagonal n, ∃ y,
      TensorProduct.map LinearMap.id ((cokernel.π f).f i.val.2).hom y = z i := by
    intro i
    exact LinearMap.lTensor_surjective (K.X i.val.1)
      ((ModuleCat.epi_iff_surjective ((cokernel.π f).f i.val.2)).mp inferInstance) (z i)
  choose y hy using he
  exact ⟨y, funext hy⟩

/-- Tensor on the left is right exact even over arbitrary commutative rings.
The complex and its differential are the literal finite diagonal total. -/
def totalTensorCokernelIso (K : Chain.{u,v} R) {L M : Chain.{u,v} R} (f : L ⟶ M) :
    cokernel (totalTensorMap R (𝟙 K) f) ≅ totalTensorComplex R K (cokernel f) := by
  let S := ShortComplex.mk (totalTensorMap R (𝟙 K) f)
    (totalTensorMap R (𝟙 K) (cokernel.π f))
    (totalTensorMap_second_zero R f (cokernel.π f) (cokernel.condition f))
  have hS : S.Exact := by
    apply HomologicalComplex.exact_of_degreewise_exact
    intro n
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (eval _ _ n))).mpr (tensorTotalMap_cokernel_exact R K f n)
  haveI : Epi S.g := HomologicalComplex.epi_of_epi_f S.g (fun n => by
    exact (ModuleCat.epi_iff_surjective (S.g.f n)).mpr
      (tensorTotalMap_cokernel_surjective R K f n))
  exact (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel


open P202Specs.SingularChains P202Specs.RelativeSingularChains
lemma totalTensorComplex_singular (X Y : TopCat.{v}) :
    totalTensorComplex R (complex R R X) (complex R R Y) =
      P202.AlexanderWhitney.tensorComplex R X Y := rfl
lemma totalTensorMap_singular_second (X : TopCat.{v}) (B : Pair.{v}) :
    tensorSecondInclusion R X B =
      totalTensorMap R (𝟙 (complex R R X)) (chainMap R R B.inclusion) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map ((chainMap R R (𝟙 X)).f i.val.1).hom
      ((chainMap R R B.inclusion).f i.val.2).hom (z i) =
    TensorProduct.map LinearMap.id ((chainMap R R B.inclusion).f i.val.2).hom (z i)
  rw [P202.SingularChains.chainMap_id]
  rfl

/-- The relative tensor cokernel is the actual tensor with relative fiber
chains. The right factor is the shared relative complex, with its induced
differential, and the total has the Koszul sign in the original AW grading. -/
def relativeTensorComplexIso (X : TopCat.{v}) (B : Pair.{v}) :
    relativeTensorComplex R X B ≅
      totalTensorComplex R (complex R R X) (nonnegative R R B) :=
  cokernelIsoOfEq (totalTensorMap_singular_second R X B) ≪≫
    totalTensorCokernelIso R (complex R R X) (chainMap R R B.inclusion)

/-- Integer extension reflects genuine chain homotopy equivalences. -/
def homotopyEquivOfNonnegativeExtend {K L : Chain.{u,v} R}
    (e : HomotopyEquiv (K.extend (degreeEmbedding 0)) (L.extend (degreeEmbedding 0))) :
    HomotopyEquiv K L := by
  let F := (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R)
  let f : K ⟶ L := F.preimage e.hom
  let g : L ⟶ K := F.preimage e.inv
  have hf : extendMap f (degreeEmbedding 0) = e.hom := F.map_preimage e.hom
  have hg : extendMap g (degreeEmbedding 0) = e.inv := F.map_preimage e.inv
  exact {
    hom := f
    inv := g
    homotopyHomInvId := Homotopy.ofExtend (e := degreeEmbedding 0) (by
      simpa only [extendMap_comp, extendMap_id, hf, hg] using e.homotopyHomInvId)
    homotopyInvHomId := Homotopy.ofExtend (e := degreeEmbedding 0) (by
      simpa only [extendMap_comp, extendMap_id, hf, hg] using e.homotopyInvHomId) }
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped Simplicial
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.ThomClass
variable (R : Type v) [CommRing R]

def crossUniverseSimplexEquiv {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) (n : ℕ) : Simplex X n ≃ Simplex Y n :=
  (simplexEquiv X n).trans
    (((Homeomorph.refl _).continuousMapCongr h).trans (simplexEquiv Y n).symm)

lemma crossUniverseSimplexEquiv_face {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) {n : ℕ} (i : Fin (n+2)) (s : Simplex X (n+1)) :
    crossUniverseSimplexEquiv h n (face i s) =
      face i (crossUniverseSimplexEquiv h (n+1) s) := by
  apply (simplexEquiv Y n).injective
  ext x
  rfl

def crossUniverseChainsEquiv {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) (n : ℕ) : Chains R X n ≃ₗ[R] Chains (ULift.{u} R) Y n :=
  Finsupp.lcongr (crossUniverseSimplexEquiv h n) ULift.moduleEquiv.symm

@[simp] lemma crossUniverseChainsEquiv_single {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) (n : ℕ) (s : Simplex X n) (r : R) :
    crossUniverseChainsEquiv R h n (Finsupp.single s r) =
      Finsupp.single (crossUniverseSimplexEquiv h n s) (ULift.up r) := by
  exact Finsupp.lcongr_single _ _ _ _

def crossUniverseComplexIso {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) : complex R R X ≅ complex R (ULift.{u} R) Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (crossUniverseChainsEquiv R h n).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j+1 := by simpa using hij.symm
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro s r
      symm
      change crossUniverseChainsEquiv R h j (boundary R R X j (Finsupp.single s r)) =
        boundary R (ULift.{u} R) Y j (crossUniverseChainsEquiv R h (j+1) (Finsupp.single s r))
      rw [P202.SingularChains.boundary_single, map_sum]
      simp only [map_zsmul, crossUniverseChainsEquiv_single,
        P202.SingularChains.boundary_single, crossUniverseSimplexEquiv_face])


def crossUniverseAugmentedIso {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) : augmentedShifted R R X ≅ augmentedShifted R (ULift.{u} R) Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => match n with
      | 0 => (ULift.moduleEquiv (R := R) (M := ULift.{u} R)).symm.toModuleIso
      | n+1 => (HomologicalComplex.eval _ _ n).mapIso (crossUniverseComplexIso R h)) (by
      intro i j hij
      obtain rfl : i = j+1 := by simpa using hij.symm
      cases j with
      | zero =>
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro s r
        change augmentation R (ULift.{u} R) Y
          (crossUniverseChainsEquiv R h 0 (Finsupp.single s r)) =
          ULift.up (augmentation R R X (Finsupp.single s r))
        rw [crossUniverseChainsEquiv_single]
        change ULift.up (sumCoefficients R (ULift.{u} R) _
            (Finsupp.single (crossUniverseSimplexEquiv h 0 s) (ULift.up r))) =
          ULift.up (ULift.up (sumCoefficients R R _ (Finsupp.single s r)))
        congr 1
        simp only [sumCoefficients, Finsupp.lsum_single, LinearMap.id_apply]
      | succ j =>
        exact (crossUniverseComplexIso R h).hom.comm (j+1) j)


def crossUniverseReducedIso {X : TopCat.{u}} {Y : TopCat.{0}}
    (h : X ≃ₜ Y) : reducedComplex R R X ≅ reducedComplex R (ULift.{u} R) Y :=
  ((P202Specs.SingularChains.degreeEmbedding (-1)).extendFunctor
    (ModuleCat.{max u v} R)).mapIso (crossUniverseAugmentedIso R h)


/-- Removing the origin commutes with the actual universe lift and P104's
sup-norm coordinates versus Mathlib's Euclidean L2 coordinates. -/
def modelPuncturedHomeomorph (k : ℕ) :
    (modelPair.{u} k).sub ≃ₜ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) := by
  let h : ULift.{u} (SmoothManifolds.ModelData.Euclidean k) ≃ₜ
      EuclideanSpace ℝ (Fin k) :=
    Homeomorph.ulift.trans (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm
  exact h.subtype (by
    intro x
    change x.down ≠ 0 ↔ h x ≠ 0
    constructor
    · intro hx he
      apply hx
      have hh : h (ULift.up 0) = 0 := rfl
      have heq := h.injective (he.trans hh.symm)
      exact congrArg ULift.down heq
    · intro hx he
      apply hx
      change WithLp.toLp 2 x.down = 0
      rw [he]
      rfl)

/-- The punctured Euclidean space retracts to its actual unit sphere. -/
def smallPuncturedHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n+1))))
      (P202Specs.SpheresDisks.sphere n) :=
  (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n+1)))).toHomotopyEquiv.trans
    (((Homeomorph.refl _).prodCongr
      SmoothManifolds.SphereCohomology.PoleTopology.positiveRadialHomeomorph).toHomotopyEquiv.trans
        (SmoothManifolds.SphereCohomology.prodRealHomotopyEquiv _))

/-- Exact homology comparison from the genuine model fiber to the geometric
sphere, with coefficient lifts only where required by categorical universes. -/
def modelHomologySphereIso (n : ℕ) (q : ℤ) :
    relativeHomology R R (modelPair.{u} (n+1)) q ≅
      reducedHomology R (ULift.{u} R) (P202Specs.SpheresDisks.sphere n) (q-1) := by
  letI : Nonempty (modelPair.{u} (n+1)).space := ⟨ULift.up 0⟩
  letI : ContractibleSpace (modelPair.{u} (n+1)).space :=
    (Homeomorph.ulift : ULift.{u} (SmoothManifolds.ModelData.Euclidean (n+1)) ≃ₜ
      SmoothManifolds.ModelData.Euclidean (n+1)).contractibleSpace
  exact P202.SpheresDisks.contractiblePairIso R R (modelPair.{u} (n+1)) q ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q-1)).mapIso
      (crossUniverseReducedIso R (modelPuncturedHomeomorph (n+1))) ≪≫
        P202.SpheresDisks.reducedHomologyIsoOfHomotopyEquiv R (ULift.{u} R)
          (X := TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n+1)))))
          (smallPuncturedHomotopyEquiv n) (q-1)


def modelHomologySelfIso (n : ℕ) :
    relativeHomology R R (modelPair.{u} (n+1)) ((n+1 : ℕ) : ℤ) ≅
      ModuleCat.of R (ULift.{u} R) := by
  let e := modelHomologySphereIso R n ((n+1 : ℕ) : ℤ)
  have ht : (((n+1 : ℕ) : ℤ)-1) = (n : ℤ) := by omega
  rw [ht] at e
  let f := Classical.choice ((P202.SpheresDisks.sphereHomology R (ULift.{u} R) n n).1 rfl)
  exact e ≪≫ f.toModuleIso

theorem modelHomology_isZero (n : ℕ) (q : ℤ) (hq : q ≠ ((n+1 : ℕ) : ℤ)) :
    IsZero (relativeHomology R R (modelPair.{u} (n+1)) q) := by
  by_cases hneg : q < 0
  · exact (P202.RelativeSingularChains.ordinary_negative R R (modelPair.{u} (n+1)) q hneg).2
  lift q to ℕ using le_of_not_gt hneg
  cases q with
  | zero =>
    haveI : Nonempty (P202Specs.SpheresDisks.sphere n) :=
      (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).to_subtype
    exact (modelHomologySphereIso R n 0).isZero_iff.mpr
      (P202.SingularDegreeZero.nonemptyReducedMinusOne R (ULift.{u} R)
        (P202Specs.SpheresDisks.sphere n))
  | succ j =>
    let e := modelHomologySphereIso R n ((j+1 : ℕ) : ℤ)
    have ht : (((j+1 : ℕ) : ℤ)-1) = (j : ℤ) := by omega
    rw [ht] at e
    exact e.isZero_iff.mpr ((P202.SpheresDisks.sphereHomology R (ULift.{u} R) n j).2 (by omega))


/-- The actual positive-rank fiber singular complex has a single free module
in its rank, through a constructed chain homotopy equivalence. -/
theorem modelRelativeHomotopyEquiv (n : ℕ) :
    Nonempty (HomotopyEquiv
      ((single (ModuleCat.{max u v} R) (.down ℤ) ((n+1 : ℕ) : ℤ)).obj
        (ModuleCat.of R (ULift.{u} R)))
      (ordinary R R (modelPair.{u} (n+1)))) := by
  haveI : ∀ q, Projective ((ordinary R R (modelPair.{u} (n+1))).X q) := by
    intro q
    haveI := P202.CohomologyExcisionMV.relative_ordinary_free R (modelPair.{u} (n+1)) q
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  haveI : Projective (ModuleCat.of R (ULift.{u} R)) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  apply homotopyEquiv_single_of_homology_concentrated R
    (ordinary R R (modelPair.{u} (n+1)))
    ⟨0, fun q hq => (P202.RelativeSingularChains.ordinary_negative R R
      (modelPair.{u} (n+1)) q hq).1⟩
    ((n+1 : ℕ) : ℤ) (ModuleCat.of R (ULift.{u} R))
    (modelHomologySelfIso R n)
  exact modelHomology_isZero R n

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.MayerVietoris
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The two-component form of relative Mayer--Vietoris gluing. -/
theorem relative_cover_glue_unique_components (C : CoverPair.{w,v}) (q : ℤ)
    (hvan : IsZero (relativeCohomology R A C.intersectionPair (q-1)))
    (a : relativeCohomology R A C.leftPair q)
    (b : relativeCohomology R A C.rightPair q)
    (hab : (relativeCohomologyFunctor R A q).map C.toLeft.op a =
      (relativeCohomologyFunctor R A q).map C.toRight.op b) :
    ∃! c : relativeCohomology R A C.pair q,
      (relativeCohomologyFunctor R A q).map C.leftInclusion.op c = a ∧
      (relativeCohomologyFunctor R A q).map C.rightInclusion.op c = b := by
  let x : relativeCoverMiddle R A C q :=
    (biprod.inl : relativeCohomology R A C.leftPair q ⟶ _) a +
    (biprod.inr : relativeCohomology R A C.rightPair q ⟶ _) b
  have hx : relativeCoverDifference R A C q x = 0 := by
    dsimp only [x]
    rw [map_add]
    change ((biprod.inl : relativeCohomology R A C.leftPair q ⟶ _) ≫
        relativeCoverDifference R A C q) a +
      ((biprod.inr : relativeCohomology R A C.rightPair q ⟶ _) ≫
        relativeCoverDifference R A C q) b = 0
    rw [relativeCoverDifference, biprod.inl_desc, biprod.inr_desc]
    change (relativeCohomologyFunctor R A q).map C.toLeft.op a +
      - (relativeCohomologyFunctor R A q).map C.toRight.op b = 0
    rw [hab, add_neg_cancel]
  have hxfst : (biprod.fst : relativeCoverMiddle R A C q ⟶ _) x = a := by
    dsimp only [x]
    rw [map_add]
    change ((biprod.inl : relativeCohomology R A C.leftPair q ⟶ _) ≫ biprod.fst) a +
      ((biprod.inr : relativeCohomology R A C.rightPair q ⟶ _) ≫ biprod.fst) b = a
    rw [biprod.inl_fst, biprod.inr_fst]
    change a + 0 = a
    exact add_zero a
  have hxsnd : (biprod.snd : relativeCoverMiddle R A C q ⟶ _) x = b := by
    dsimp only [x]
    rw [map_add]
    change ((biprod.inl : relativeCohomology R A C.leftPair q ⟶ _) ≫ biprod.snd) a +
      ((biprod.inr : relativeCohomology R A C.rightPair q ⟶ _) ≫ biprod.snd) b = b
    rw [biprod.inl_snd, biprod.inr_snd]
    change 0 + b = b
    exact zero_add b
  have hcomponents (c : relativeCohomology R A C.pair q) :
      relativeCoverRestrictions R A C q c = x ↔
      (relativeCohomologyFunctor R A q).map C.leftInclusion.op c = a ∧
      (relativeCohomologyFunctor R A q).map C.rightInclusion.op c = b := by
    have hfst : (biprod.fst : relativeCoverMiddle R A C q ⟶ _)
        (relativeCoverRestrictions R A C q c) =
        (relativeCohomologyFunctor R A q).map C.leftInclusion.op c := by
      change (relativeCoverRestrictions R A C q ≫ biprod.fst) c = _
      rw [relativeCoverRestrictions, biprod.lift_fst]
      rfl
    have hsnd : (biprod.snd : relativeCoverMiddle R A C q ⟶ _)
        (relativeCoverRestrictions R A C q c) =
        (relativeCohomologyFunctor R A q).map C.rightInclusion.op c := by
      change (relativeCoverRestrictions R A C q ≫ biprod.snd) c = _
      rw [relativeCoverRestrictions, biprod.lift_snd]
      rfl
    constructor
    · intro hc
      exact ⟨hfst.symm.trans ((congrArg (biprod.fst : relativeCoverMiddle R A C q ⟶ _) hc).trans hxfst),
        hsnd.symm.trans ((congrArg (biprod.snd : relativeCoverMiddle R A C q ⟶ _) hc).trans hxsnd)⟩
    · rintro ⟨ha, hb⟩
      have ht (y : relativeCoverMiddle R A C q) :
          (biprod.inl : relativeCohomology R A C.leftPair q ⟶ _) ((biprod.fst : relativeCoverMiddle R A C q ⟶ relativeCohomology R A C.leftPair q) y) +
          (biprod.inr : relativeCohomology R A C.rightPair q ⟶ _) ((biprod.snd : relativeCoverMiddle R A C q ⟶ relativeCohomology R A C.rightPair q) y) = y := by
        have hh := congrArg (fun f : relativeCoverMiddle R A C q ⟶ relativeCoverMiddle R A C q => f y)
          (biprod.total (X := relativeCohomology R A C.leftPair q)
            (Y := relativeCohomology R A C.rightPair q))
        exact hh
      rw [← ht (relativeCoverRestrictions R A C q c), hfst, hsnd, ha, hb]
  obtain ⟨c, hc, hu⟩ := relative_cover_glue_unique R A C q hvan x hx
  exact ⟨c, (hcomponents c).mp hc, fun e he => hu e ((hcomponents e).mpr he)⟩

/-- Reassociate nested induced subpairs without changing any point. -/
def piecePreimageIso (B : Pair.{w}) {U V : Set B.space} (h : V ⊆ U) :
    piece (piece B U) (Subtype.val ⁻¹' V) ≅ piece B V :=
  pairIsoOfHomeomorph _ _ {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, h x.property⟩, x.property⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
    (fun _ => Iff.rfl)

/-- The actual relative pair on U union V has its cover by the original sets. -/
def openUnionCover (B : Pair.{w}) (U V : Set B.space)
    (hU : IsOpen U) (hV : IsOpen V) : CoverPair.{w,z} :=
  CoverPair.ofSets (piece B (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (by ext x; exact ⟨fun _ => trivial, fun _ => x.property⟩)

def openUnionLeftIso (B : Pair.{w}) {U V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) :
    (openUnionCover.{w,z} B U V hU hV).leftPair ≅ piece B U :=
  piecePreimageIso B Set.subset_union_left

def openUnionRightIso (B : Pair.{w}) {U V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) :
    (openUnionCover.{w,z} B U V hU hV).rightPair ≅ piece B V :=
  piecePreimageIso B Set.subset_union_right

def openUnionIntersectionIso (B : Pair.{w}) {U V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) :
    (openUnionCover.{w,z} B U V hU hV).intersectionPair ≅ piece B (U ∩ V) :=
  piecePreimageIso B (U := U ∪ V) (V := U ∩ V) (fun _ hx => Or.inl hx.1)

/-- Relative cohomology vanishing propagates over a literal open union. -/
theorem relative_openUnion_isZero (B : Pair.{w}) {U V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) (q : ℤ)
    (hleft : IsZero (relativeCohomology R A (piece B U) q))
    (hright : IsZero (relativeCohomology R A (piece B V) q))
    (hoverlap : IsZero (relativeCohomology R A (piece B (U ∩ V)) (q-1))) :
    IsZero (relativeCohomology R A (piece B (U ∪ V)) q) := by
  apply relative_cover_isZero R A (openUnionCover.{w,v} B U V hU hV) q
  · exact hleft.of_iso ((relativeCohomologyFunctor R A q).mapIso
      (openUnionLeftIso.{w,v} B hU hV).op).symm
  · exact hright.of_iso ((relativeCohomologyFunctor R A q).mapIso
      (openUnionRightIso.{w,v} B hU hV).op).symm
  · exact hoverlap.of_iso ((relativeCohomologyFunctor R A (q-1)).mapIso
      (openUnionIntersectionIso.{w,v} B hU hV).op).symm

/-- Compatible classes on two open subpairs glue by their literal inclusions.
No restriction is placed on the coefficient module. -/
theorem relative_openUnion_glue_unique (B : Pair.{w}) {U V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) (q : ℤ)
    (hvan : IsZero (relativeCohomology R A (piece B (U ∩ V)) (q-1)))
    (a : relativeCohomology R A (piece B U) q)
    (b : relativeCohomology R A (piece B V) q)
    (hab : (relativeCohomologyFunctor R A q).map
        (pieceMono B (show U ∩ V ⊆ U from Set.inter_subset_left)).op a =
      (relativeCohomologyFunctor R A q).map
        (pieceMono B (show U ∩ V ⊆ V from Set.inter_subset_right)).op b) :
    ∃! c : relativeCohomology R A (piece B (U ∪ V)) q,
      (relativeCohomologyFunctor R A q).map
        (pieceMono B (show U ⊆ U ∪ V from Set.subset_union_left)).op c = a ∧
      (relativeCohomologyFunctor R A q).map
        (pieceMono B (show V ⊆ U ∪ V from Set.subset_union_right)).op c = b := by
  let F := relativeCohomologyFunctor R A q
  let C := openUnionCover.{w,v} B U V hU hV
  let eU := openUnionLeftIso.{w,v} B hU hV
  let eV := openUnionRightIso.{w,v} B hU hV
  let eI := openUnionIntersectionIso.{w,v} B hU hV
  let a' := F.map eU.hom.op a
  let b' := F.map eV.hom.op b
  have hcU : C.toLeft ≫ eU.hom =
      eI.hom ≫ pieceMono B (show U ∩ V ⊆ U from Set.inter_subset_left) :=
    PairMap.ext _ _ rfl
  have hcV : C.toRight ≫ eV.hom =
      eI.hom ≫ pieceMono B (show U ∩ V ⊆ V from Set.inter_subset_right) :=
    PairMap.ext _ _ rfl
  have hab' : F.map C.toLeft.op a' = F.map C.toRight.op b' := by
    change (F.map eU.hom.op ≫ F.map C.toLeft.op) a =
      (F.map eV.hom.op ≫ F.map C.toRight.op) b
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hcU, hcV,
      op_comp, op_comp, F.map_comp, F.map_comp]
    exact congrArg (F.map eI.hom.op) hab
  have hCvan : IsZero (relativeCohomology R A C.intersectionPair (q-1)) :=
    hvan.of_iso ((relativeCohomologyFunctor R A (q-1)).mapIso eI.op).symm
  have hl (c : relativeCohomology R A (piece B (U ∪ V)) q) :
      F.map C.leftInclusion.op c = F.map eU.hom.op
        (F.map (pieceMono B (show U ⊆ U ∪ V from Set.subset_union_left)).op c) := by
    change _ = (F.map (pieceMono B Set.subset_union_left).op ≫ F.map eU.hom.op) c
    rw [← F.map_comp, ← op_comp]
    rfl
  have hr (c : relativeCohomology R A (piece B (U ∪ V)) q) :
      F.map C.rightInclusion.op c = F.map eV.hom.op
        (F.map (pieceMono B (show V ⊆ U ∪ V from Set.subset_union_right)).op c) := by
    change _ = (F.map (pieceMono B Set.subset_union_right).op ≫ F.map eV.hom.op) c
    rw [← F.map_comp, ← op_comp]
    rfl
  have hpred (c : relativeCohomology R A (piece B (U ∪ V)) q) :
      (F.map C.leftInclusion.op c = a' ∧ F.map C.rightInclusion.op c = b') ↔
      (F.map (pieceMono B (show U ⊆ U ∪ V from Set.subset_union_left)).op c = a ∧
      F.map (pieceMono B (show V ⊆ U ∪ V from Set.subset_union_right)).op c = b) := by
    rw [hl, hr]
    exact and_congr
      ((ModuleCat.mono_iff_injective (F.map eU.hom.op)).mp inferInstance).eq_iff
      ((ModuleCat.mono_iff_injective (F.map eV.hom.op)).mp inferInstance).eq_iff
  obtain ⟨c, hc, hu⟩ := relative_cover_glue_unique_components R A C q hCvan a' b' hab'
  exact ⟨c, (hpred c).mp hc, fun e he => hu e ((hpred e).mpr he)⟩

/-- No cohomology remains when the specified second term is the whole space. -/
theorem relativeCohomology_isZero_of_subspace_eq_univ (B : Pair.{w})
    (hB : B.subspace = Set.univ) (q : ℤ) :
    IsZero (relativeCohomology R A B q) := by
  let hj : ∀ x : B.space, x ∈ B.subspace := fun x => by rw [hB]; trivial
  let j : B.space ⟶ B.sub := TopCat.ofHom
    ⟨fun x => ⟨x, hj x⟩, continuous_id.subtype_mk hj⟩
  haveI : IsIso B.inclusion := ⟨⟨j,
    TopCat.hom_ext (ContinuousMap.ext (fun _ => Subtype.ext rfl)),
    TopCat.hom_ext (ContinuousMap.ext (fun _ => rfl))⟩⟩
  have hc : IsZero (ordinary R R B) :=
    isZero_cokernel_of_epi (inclusion (P202Specs.SingularChains.ordinaryFunctor R R) B)
  have hd : IsZero ((ordinary R R B).X q) :=
    (HomologicalComplex.eval _ _ q).map_isZero hc
  have hdual : IsZero ((relativeCochains R A B).X q) :=
    P202.CohomologyPairs.dual_isZero R A _ hd
  exact ((relativeCochains R A B).sc q).isZero_homology_of_isZero_X₂ hdual

/-- Vanishing below d on every open part of each cover member propagates
across any finite union, including arbitrary open subsets of that union. -/
theorem relative_finite_open_vanishing (B : Pair.{w}) {ι : Type z}
    (s : Finset ι) (U : ι → Set B.space) (hU : ∀ j ∈ s, IsOpen (U j)) (d : ℤ)
    (hlocal : ∀ j ∈ s, ∀ V : Set B.space, IsOpen V → V ⊆ U j →
      ∀ q : ℤ, q < d → IsZero (relativeCohomology R A (piece B V) q)) :
    ∀ V : Set B.space, IsOpen V → V ⊆ ⋃ j ∈ s, U j →
      ∀ q : ℤ, q < d → IsZero (relativeCohomology R A (piece B V) q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V hV hVs q hq
    have hVe : V = ∅ := by simpa using hVs
    apply relativeCohomology_isZero_of_subspace_eq_univ R A
    ext x
    exact (False.elim (by simpa [hVe] using x.property))
  | @insert j s hj ih =>
    intro V hV hVs q hq
    have hjopen := hU j (Finset.mem_insert_self j s)
    have hsopen (k) (hk : k ∈ s) : IsOpen (U k) := hU k (Finset.mem_insert_of_mem hk)
    have hJ : IsOpen (⋃ k ∈ s, U k) := isOpen_biUnion hsopen
    let L := V ∩ U j
    let W := V ∩ ⋃ k ∈ s, U k
    have hL : IsOpen L := hV.inter hjopen
    have hW : IsOpen W := hV.inter hJ
    have hLW : L ∪ W = V := by
      ext x
      constructor
      · rintro (hx | hx); exact hx.1; exact hx.1
      · intro hx
        have hxcover := hVs hx
        rcases Set.mem_iUnion.mp hxcover with ⟨k, hk⟩
        rcases Set.mem_iUnion.mp hk with ⟨hk, hxk⟩
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inl ⟨hx, hxk⟩
        · exact Or.inr ⟨hx, Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hxk⟩⟩⟩
    rw [← hLW]
    apply relative_openUnion_isZero R A B hL hW q
    · exact hlocal j (Finset.mem_insert_self j s) L hL Set.inter_subset_right q hq
    · exact ih hsopen (fun k hk => hlocal k (Finset.mem_insert_of_mem hk))
        W hW Set.inter_subset_right q hq
    · exact hlocal j (Finset.mem_insert_self j s) (L ∩ W) (hL.inter hW)
        (fun x hx => hx.1.2) (q-1) (by omega)

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.ThomClass
open P202Specs.AlexanderWhitney
variable (R : Type u) [CommRing R]

def tensorSecondHomotopyComponent (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    (h : ∀ q, L.X q ⟶ M.X (q+1)) (n : ℕ) :
    TensorTotal R K L n →ₗ[R] TensorTotal R K M (n+1) where
  toFun z i := match i with
    | ⟨(p,0), _⟩ => 0
    | ⟨(p,q+1), hi⟩ => (-1 : ℤ)^p • TensorProduct.map LinearMap.id (h q).hom
        (z ⟨(p,q), by omega⟩)
  map_add' z z' := by
    ext ⟨⟨p,q⟩,hi⟩
    cases q <;> simp [map_add, smul_add]
  map_smul' a z := by
    ext ⟨⟨p,q⟩,hi⟩
    cases q <;> simp [map_smul, smul_comm a]

lemma tensorSecondHomotopyComponent_zero (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    (h : ∀ q, L.X q ⟶ M.X (q+1)) (n p : ℕ) (hi : p+0=n+1)
    (z : TensorTotal R K L n) :
    tensorSecondHomotopyComponent R K h n z ⟨(p,0),hi⟩ = 0 := rfl
lemma tensorSecondHomotopyComponent_succ (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    (h : ∀ q, L.X q ⟶ M.X (q+1)) (n p q : ℕ) (hi : p+(q+1)=n+1)
    (z : TensorTotal R K L n) :
    tensorSecondHomotopyComponent R K h n z ⟨(p,q+1),hi⟩ =
      (-1 : ℤ)^p • TensorProduct.map LinearMap.id (h q).hom
        (z ⟨(p,q), by omega⟩) := rfl

lemma tensor_homotopy_zero {L M : Chain.{u,v} R} {f g : L ⟶ M}
    (h : Homotopy f g) (A : ModuleCat.{max u v} R) (z : A ⊗[R] L.X 0) :
    TensorProduct.map LinearMap.id (f.f 0).hom z =
      TensorProduct.map LinearMap.id (M.d 1 0).hom
        (TensorProduct.map LinearMap.id (h.hom 0 1).hom z) +
      TensorProduct.map LinearMap.id (g.f 0).hom z := by
  have he : f.f 0 = h.hom 0 1 ≫ M.d 1 0 + g.f 0 := by
    simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add]
      using h.comm 0
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']; abel
  | tmul a b =>
    change a ⊗ₜ[R] (f.f 0 b) = _
    rw [he]
    simp [TensorProduct.tmul_add]
lemma tensor_homotopy_succ {L M : Chain.{u,v} R} {f g : L ⟶ M}
    (h : Homotopy f g) (A : ModuleCat.{max u v} R) (q : ℕ) (z : A ⊗[R] L.X (q+1)) :
    TensorProduct.map LinearMap.id (f.f (q+1)).hom z =
      TensorProduct.map LinearMap.id (h.hom q (q+1)).hom
        (TensorProduct.map LinearMap.id (L.d (q+1) q).hom z) +
      TensorProduct.map LinearMap.id (M.d (q+2) (q+1)).hom
        (TensorProduct.map LinearMap.id (h.hom (q+1) (q+2)).hom z) +
      TensorProduct.map LinearMap.id (g.f (q+1)).hom z := by
  have he : f.f (q+1) = L.d (q+1) q ≫ h.hom q (q+1) +
      h.hom (q+1) (q+2) ≫ M.d (q+2) (q+1) + g.f (q+1) := by
    simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      using h.comm (q+1)
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']; abel
  | tmul a b =>
    change a ⊗ₜ[R] (f.f (q+1) b) = _
    rw [he]
    simp [TensorProduct.tmul_add]

lemma sign_smul_sign_smul {A : Type*} [AddCommGroup A] (p : ℕ) (a : A) :
    (-1 : ℤ)^p • ((-1 : ℤ)^p • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp
lemma tensorLeftBoundary_homotopy (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    (h : ∀ q, L.X q ⟶ M.X (q+1)) (p q : ℕ)
    (z : K.X (p+1) ⊗[R] L.X q) :
    tensorLeftBoundary R K M p (q+1)
      (TensorProduct.map LinearMap.id (h q).hom z) =
    TensorProduct.map LinearMap.id (h q).hom (tensorLeftBoundary R K L p q z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b => rfl

lemma tensorSecondHomotopy_zero (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    {f g : L ⟶ M} (h : Homotopy f g) :
    tensorTotalMap R (𝟙 K) f 0 =
      (tensorTotalBoundary R K M 0).comp
        (tensorSecondHomotopyComponent R K (fun q => h.hom q (q+1)) 0) +
      tensorTotalMap R (𝟙 K) g 0 := by
  apply LinearMap.ext
  intro z
  funext i
  rcases i with ⟨⟨p,q⟩,hi⟩
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst p
  subst q
  simpa [tensorTotalMap, tensorTotalBoundary, tensorSecondHomotopyComponent,
    tensorLeftBoundary, tensorRightBoundary, TensorProduct.map_map, LinearMap.id_comp] using
      tensor_homotopy_zero R h (K.X 0) (z ⟨(0,0), rfl⟩)

lemma tensorSecondHomotopy_succ (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    {f g : L ⟶ M} (h : Homotopy f g) (n : ℕ) :
    tensorTotalMap R (𝟙 K) f (n+1) =
      (tensorSecondHomotopyComponent R K (fun q => h.hom q (q+1)) n).comp
        (tensorTotalBoundary R K L n) +
      (tensorTotalBoundary R K M (n+1)).comp
        (tensorSecondHomotopyComponent R K (fun q => h.hom q (q+1)) (n+1)) +
      tensorTotalMap R (𝟙 K) g (n+1) := by
  apply LinearMap.ext
  intro z
  funext i
  rcases i with ⟨⟨p,q⟩,hi⟩
  cases q with
  | zero =>
    simpa [tensorTotalMap, tensorTotalBoundary, tensorSecondHomotopyComponent,
      tensorLeftBoundary, tensorRightBoundary, TensorProduct.map_map, LinearMap.id_comp,
      sign_smul_sign_smul] using tensor_homotopy_zero R h (K.X p) (z ⟨(p,0),hi⟩)
  | succ q =>
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
      tensorTotalMap, tensorTotalBoundary, tensorSecondHomotopyComponent,
      LinearMap.coe_mk, AddHom.coe_mk, map_add, map_zsmul,
      HomologicalComplex.id_f, ModuleCat.hom_id, sign_smul_sign_smul,
      pow_succ, mul_smul, neg_one_zsmul, smul_neg, map_neg]
    rw [tensorLeftBoundary_homotopy R K (fun q => h.hom q (q+1))]
    simp only [smul_add, sign_smul_sign_smul]
    change TensorProduct.map LinearMap.id (f.f (q+1)).hom _ =
      (-1 : ℤ)^p • TensorProduct.map LinearMap.id (h.hom q (q+1)).hom _ +
        TensorProduct.map LinearMap.id (h.hom q (q+1)).hom
          (TensorProduct.map LinearMap.id (L.d (q+1) q).hom _) +
      (-((-1 : ℤ)^p • TensorProduct.map LinearMap.id (h.hom q (q+1)).hom _) +
        TensorProduct.map LinearMap.id (M.d (q+2) (q+1)).hom
          (TensorProduct.map LinearMap.id (h.hom (q+1) (q+2)).hom _)) + _
    rw [tensor_homotopy_succ R h (K.X p) q (z ⟨(p,q+1),hi⟩)]
    abel

/-- Tensoring a homotopy in the second factor uses its Koszul sign. -/
def totalTensorHomotopy (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    {f g : L ⟶ M} (h : Homotopy f g) :
    Homotopy (totalTensorMap R (𝟙 K) f) (totalTensorMap R (𝟙 K) g) :=
  P202.EilenbergZilber.homotopyOfComponents R _ _
    (fun n => ModuleCat.ofHom
      (tensorSecondHomotopyComponent R K (fun q => h.hom q (q+1)) n))
    (by
      apply ModuleCat.hom_ext
      exact tensorSecondHomotopy_zero R K h)
    (by
      intro n
      simp only [totalTensorComplex, ChainComplex.of.d, dite_true, eqToHom_refl,
        Category.id_comp]
      rw [dite_eq_left (show n+2 = n+1+1 from rfl)]
      apply ModuleCat.hom_ext
      exact tensorSecondHomotopy_succ R K h n)
lemma totalTensorMap_second_comp (K : Chain.{u,v} R) {L M N : Chain.{u,v} R}
    (f : L ⟶ M) (g : M ⟶ N) :
    totalTensorMap R (𝟙 K) (f ≫ g) =
      totalTensorMap R (𝟙 K) f ≫ totalTensorMap R (𝟙 K) g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map LinearMap.id
      ((g.f i.val.2).hom.comp (f.f i.val.2).hom) (z i) =
    TensorProduct.map LinearMap.id (g.f i.val.2).hom
      (TensorProduct.map LinearMap.id (f.f i.val.2).hom (z i))
  simp only [TensorProduct.map_map, LinearMap.id_comp]
lemma totalTensorMap_id (K L : Chain.{u,v} R) :
    totalTensorMap R (𝟙 K) (𝟙 L) = 𝟙 (totalTensorComplex R K L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map LinearMap.id LinearMap.id (z i) = z i
  exact congrFun (congrArg DFunLike.coe (TensorProduct.map_id (R := R))) (z i)

/-- Chain homotopy equivalence of the second factor gives a constructed
chain homotopy equivalence of the total tensors over every commutative ring. -/
def totalTensorHomotopyEquiv (K : Chain.{u,v} R) {L M : Chain.{u,v} R}
    (e : HomotopyEquiv L M) :
    HomotopyEquiv (totalTensorComplex R K L) (totalTensorComplex R K M) where
  hom := totalTensorMap R (𝟙 K) e.hom
  inv := totalTensorMap R (𝟙 K) e.inv
  homotopyHomInvId := by
    have h := totalTensorHomotopy R K e.homotopyHomInvId
    rw [totalTensorMap_second_comp, totalTensorMap_id] at h
    exact h
  homotopyInvHomId := by
    have h := totalTensorHomotopy R K e.homotopyInvHomId
    rw [totalTensorMap_second_comp, totalTensorMap_id] at h
    exact h

/-- Extend a constructed nonnegative homotopy equivalence to the shared
integer grading. -/
def nonnegativeExtendHomotopyEquiv {K L : Chain.{u,v} R}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend (P202Specs.SingularChains.degreeEmbedding 0))
      (L.extend (P202Specs.SingularChains.degreeEmbedding 0)) where
  hom := extendMap e.hom (P202Specs.SingularChains.degreeEmbedding 0)
  inv := extendMap e.inv (P202Specs.SingularChains.degreeEmbedding 0)
  homotopyHomInvId := by
    simpa only [extendMap_comp, extendMap_id] using
      e.homotopyHomInvId.extend (P202Specs.SingularChains.degreeEmbedding 0)
  homotopyInvHomId := by
    simpa only [extendMap_comp, extendMap_id] using
      e.homotopyInvHomId.extend (P202Specs.SingularChains.degreeEmbedding 0)

/-- Relative EZ, right exactness and signed tensoring assembled on the actual
second-product pair in the chapter's integer chain grading. -/
theorem secondProduct_tensor_homotopy (X : TopCat.{v})
    (B : P202Specs.RelativeSingularChains.Pair.{v}) (L : Chain.{u,v} R)
    (e : HomotopyEquiv (P202Specs.RelativeSingularChains.nonnegative R R B) L) :
    Nonempty (HomotopyEquiv
      (P202Specs.RelativeSingularChains.ordinary R R (secondProductPair X B))
      ((totalTensorComplex R (P202Specs.SingularChains.complex R R X) L).extend
        (P202Specs.SingularChains.degreeEmbedding 0))) := by
  obtain ⟨a⟩ := secondProduct_relative_eilenbergZilber R X B
  let b := ((P202Specs.SingularChains.degreeEmbedding 0).extendFunctor _).mapIso
    (relativeTensorComplexIso R X B)
  exact ⟨(a.trans (HomotopyEquiv.ofIso b)).trans
    (nonnegativeExtendHomotopyEquiv R (totalTensorHomotopyEquiv R _ e))⟩
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.ThomClass
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.ThomClass
variable (R : Type u) [CommRing R]
theorem modelNonnegativeHomotopyEquiv (n : ℕ) :
    Nonempty (HomotopyEquiv
      ((single (ModuleCat.{max u v} R) (.down ℕ) (n+1)).obj
        (ModuleCat.of R (ULift.{v} R)))
      (nonnegative R R (modelPair.{v} (n+1)))) := by
  obtain ⟨e⟩ := modelRelativeHomotopyEquiv R n
  let a := HomotopyEquiv.ofIso
    (extendSingleIso (degreeEmbedding 0) (ModuleCat.of R (ULift.{v} R))
      (n+1) ((n+1 : ℕ) : ℤ) (by simp [degreeEmbedding]))
  let b := HomotopyEquiv.ofIso
    (P202.CohomologyExcisionMV.relativeExtensionIso R (modelPair.{v} (n+1))).symm
  exact ⟨homotopyEquivOfNonnegativeExtend R ((a.trans e).trans b)⟩
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.ThomClass
open P202Specs.AlexanderWhitney P202Specs.SingularChains
variable (R : Type u) [CommRing R]
abbrev rankSingle (d : ℕ) : Chain.{u,v} R :=
  (single (ModuleCat.{max u v} R) (.down ℕ) d).obj (ModuleCat.of R (ULift.{v} R))

lemma tensorSingle_component_subsingleton (K : Chain.{u,v} R) (d p q : ℕ) (hq : q ≠ d) :
    Subsingleton (K.X p ⊗[R] (rankSingle.{u,v} R d).X q) := by
  haveI : Subsingleton ((rankSingle.{u,v} R d).X q) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.down ℕ) d (ModuleCat.of R (ULift.{v} R)) q hq)
  infer_instance

theorem totalTensorSingle_below_isZero (K : Chain.{u,v} R) (d n : ℕ) (hn : n < d) :
    IsZero ((totalTensorComplex R K (rankSingle R d)).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  haveI : ∀ i : Diagonal n, Subsingleton (K.X i.val.1 ⊗[R] (rankSingle R d).X i.val.2) := by
    intro i
    apply tensorSingle_component_subsingleton R K d
    have := i.property
    omega
  change Subsingleton (TensorTotal R K (rankSingle R d) n)
  infer_instance

/-- Only the component with right degree d survives in total degree d+p. -/
def totalTensorSingleDegreeEquiv (K : Chain.{u,v} R) (d p : ℕ) :
    TensorTotal R K (rankSingle R d) (d+p) ≃ₗ[R] K.X p := by
  let i0 : Diagonal (d+p) := ⟨(p,d), by omega⟩
  let P : TensorTotal R K (rankSingle R d) (d+p) →ₗ[R]
      K.X p ⊗[R] (rankSingle R d).X d := LinearMap.proj i0
  have hP : Function.Bijective P := by
    constructor
    · intro z z' hz
      funext i
      by_cases hi : i = i0
      · subst i
        exact hz
      · have hq : i.val.2 ≠ d := by
          intro he
          apply hi
          apply Subtype.ext
          apply Prod.ext
          · have := i.property
            dsimp [i0]
            omega
          · exact he
        haveI := tensorSingle_component_subsingleton R K d i.val.1 i.val.2 hq
        exact Subsingleton.elim _ _
    · intro z
      refine ⟨Pi.single i0 z, ?_⟩
      change Pi.single (M := fun i : Diagonal (d+p) =>
        K.X i.val.1 ⊗[R] (rankSingle R d).X i.val.2) i0 z i0 = z
      exact Pi.single_eq_same _ _
  exact (LinearEquiv.ofBijective P hP).trans
    ((TensorProduct.congr (LinearEquiv.refl R (K.X p))
      ((singleObjXSelf (.down ℕ) d (ModuleCat.of R (ULift.{v} R))).toLinearEquiv.trans
        ULift.moduleEquiv)).trans (TensorProduct.rid R (K.X p)))


lemma totalTensorSingleDegreeEquiv_apply (K : Chain.{u,v} R) (d p : ℕ)
    (z : TensorTotal R K (rankSingle R d) (d+p)) :
    totalTensorSingleDegreeEquiv R K d p z =
      (TensorProduct.rid R (K.X p))
        ((TensorProduct.congr (LinearEquiv.refl R (K.X p))
          ((singleObjXSelf (.down ℕ) d (ModuleCat.of R (ULift.{v} R))).toLinearEquiv.trans
            ULift.moduleEquiv)) (z ⟨(p,d), by omega⟩)) := rfl

lemma tensorSingleRightBoundary_zero (K : Chain.{u,v} R) (d p q : ℕ)
    (z : K.X p ⊗[R] (rankSingle R d).X (q+1)) :
    tensorRightBoundary R K (rankSingle R d) p q z = 0 := by
  simp [tensorRightBoundary, rankSingle]

lemma totalTensorSingleDegreeEquiv_boundary (K : Chain.{u,v} R) (d p : ℕ)
    (z : TensorTotal R K (rankSingle R d) (d+(p+1))) :
    totalTensorSingleDegreeEquiv R K d p (tensorTotalBoundary R K (rankSingle R d) (d+p) z) =
      K.d (p+1) p (totalTensorSingleDegreeEquiv R K d (p+1) z) := by
  simp only [totalTensorSingleDegreeEquiv_apply]
  change (TensorProduct.rid R (K.X p))
    ((TensorProduct.congr (LinearEquiv.refl R (K.X p))
      ((singleObjXSelf (.down ℕ) d (ModuleCat.of R (ULift.{v} R))).toLinearEquiv.trans
        ULift.moduleEquiv))
          (tensorLeftBoundary R K (rankSingle R d) p d (z ⟨(p+1,d), by omega⟩) +
            (-1 : ℤ)^p • tensorRightBoundary R K (rankSingle R d) p d
              (z ⟨(p,d+1), by omega⟩))) = _
  rw [tensorSingleRightBoundary_zero, smul_zero, add_zero]
  generalize z ⟨(p+1,d), by omega⟩ = x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul a b =>
    simp [tensorLeftBoundary, TensorProduct.rid_tmul]


/-- Tensor-single identification is natural in the entire first chain factor. -/
lemma totalTensorSingleDegreeEquiv_naturality {K K' : Chain.{u,v} R}
    (f : K ⟶ K') (d p : ℕ)
    (z : TensorTotal R K (rankSingle R d) (d+p)) :
    totalTensorSingleDegreeEquiv R K' d p
      (tensorTotalMap R f (𝟙 (rankSingle R d)) (d+p) z) =
        f.f p (totalTensorSingleDegreeEquiv R K d p z) := by
  simp only [totalTensorSingleDegreeEquiv_apply]
  change (TensorProduct.rid R (K'.X p))
    ((TensorProduct.congr (LinearEquiv.refl R (K'.X p))
      ((singleObjXSelf (.down ℕ) d (ModuleCat.of R (ULift.{v} R))).toLinearEquiv.trans
        ULift.moduleEquiv))
          (TensorProduct.map (f.f p).hom LinearMap.id (z ⟨(p,d), by omega⟩))) = _
  generalize z ⟨(p,d), by omega⟩ = x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp [map_add, ha, hb]
  | tmul a b => simp [TensorProduct.rid_tmul]

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R]

/-- At the first possibly nonzero cochain degree, cohomology has a unique
cocycle representative in the original cochain module. -/
def bottomCochain (C : CochainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hC : IsZero (C.X (d-1))) : C.homology d ⟶ C.X d :=
  (C.isoHomologyπ (d-1) d (by simp) (hC.eq_of_src _ _)).inv ≫ C.iCycles d
instance bottomCochain_mono (C : CochainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hC : IsZero (C.X (d-1))) : Mono (bottomCochain R C d hC) := by
  unfold bottomCochain
  infer_instance
lemma bottomCochain_cocycle (C : CochainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hC : IsZero (C.X (d-1))) : bottomCochain R C d hC ≫ C.d d (d+1) = 0 := by
  simp [bottomCochain, Category.assoc]
lemma bottomCochain_natural {C D : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : C ⟶ D) (d : ℤ) (hC : IsZero (C.X (d-1))) (hD : IsZero (D.X (d-1))) :
    homologyMap f d ≫ bottomCochain R D d hD = bottomCochain R C d hC ≫ f.f d := by
  rw [← cancel_epi (C.homologyπ d)]
  rw [homologyπ_naturality_assoc]
  simp only [bottomCochain, Category.assoc, isoHomologyπ_hom_inv_id_assoc]
  exact cyclesMap_i f d
lemma dual_term_isZero (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) (hK : IsZero (K.X q)) :
    IsZero (((dualComplexFunctor R A (.down ℤ)).obj (op K)).X q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  haveI := ModuleCat.subsingleton_of_isZero hK
  change Subsingleton (K.X q →ₗ[R] A)
  infer_instance
lemma dual_cohomology_below_isZero (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hK : ∀ q : ℤ, q < d → IsZero (K.X q)) (q : ℤ) (hq : q < d) :
    IsZero (((dualComplexFunctor R A (.down ℤ)).obj (op K)).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (dual_term_isZero R A K q (hK q hq))

/-- Bottom-degree dual cohomology injects into the literal unrestricted
module of linear functionals. No projectivity assumption is needed here. -/
def dualBottomCochain (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hK : IsZero (K.X (d-1))) :
    ((dualComplexFunctor R A (.down ℤ)).obj (op K)).homology d ⟶
      ModuleCat.of R (K.X d →ₗ[R] A) :=
  bottomCochain R _ d (dual_term_isZero R A K (d-1) hK)
instance dualBottomCochain_mono (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (d : ℤ)
    (hK : IsZero (K.X (d-1))) : Mono (dualBottomCochain R A K d hK) :=
  inferInstanceAs (Mono (bottomCochain R _ d _))


open P202Specs.SingularChains
lemma nonnegative_extend_below_isZero
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (d : ℕ)
    (hK : ∀ n : ℕ, n < d → IsZero (K.X n)) (q : ℤ) (hq : q < (d : ℤ)) :
    IsZero ((K.extend (degreeEmbedding 0)).X q) := by
  by_cases hneg : q < 0
  · exact isZero_extend_X K (degreeEmbedding 0) q (by
      intro n hn
      change (0 : ℤ) + n = q at hn
      omega)
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    exact (hK n (by omega)).of_iso
      (K.extendXIso (degreeEmbedding 0) (show (degreeEmbedding 0).f n = (n : ℤ) by
        change (0 : ℤ) + n = n; omega))

lemma nonnegative_dual_cohomology_below_isZero (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (d : ℕ)
    (hK : ∀ n : ℕ, n < d → IsZero (K.X n)) (q : ℤ) (hq : q < (d : ℤ)) :
    IsZero (((dualComplexFunctor R A (.down ℤ)).obj
      (op (K.extend (degreeEmbedding 0)))).homology q) :=
  dual_cohomology_below_isZero R A _ (d : ℤ)
    (nonnegative_extend_below_isZero R K d hK) q hq

/-- The bottom cohomology class is recorded as a functional on the original
nonnegative chain term, retaining the literal extension coordinate map. -/
def nonnegativeDualBottomCochain (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (d : ℕ)
    (hK : ∀ n : ℕ, n < d → IsZero (K.X n)) :
    ((dualComplexFunctor R A (.down ℤ)).obj
      (op (K.extend (degreeEmbedding 0)))).homology (d : ℤ) ⟶
      ModuleCat.of R (K.X d →ₗ[R] A) :=
  dualBottomCochain R A (K.extend (degreeEmbedding 0)) d
      (nonnegative_extend_below_isZero R K d hK (d-1) (by omega)) ≫
    (LinearEquiv.arrowCongr
      (K.extendXIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f d = (d : ℤ) by
          change (0 : ℤ) + d = d; omega)).toLinearEquiv
      (LinearEquiv.refl R A)).toModuleIso.hom

instance nonnegativeDualBottomCochain_mono (A : Type w) [AddCommGroup A] [Module R A]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (d : ℕ)
    (hK : ∀ n : ℕ, n < d → IsZero (K.X n)) :
    Mono (nonnegativeDualBottomCochain R A K d hK) := by
  unfold nonnegativeDualBottomCochain
  infer_instance


lemma nonnegativeDualBottomCochain_natural (A : Type w) [AddCommGroup A] [Module R A]
    {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (d : ℕ)
    (hK : ∀ n : ℕ, n < d → IsZero (K.X n))
    (hL : ∀ n : ℕ, n < d → IsZero (L.X n)) :
    homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (extendMap f (degreeEmbedding 0)).op) (d : ℤ) ≫
        nonnegativeDualBottomCochain R A K d hK =
      nonnegativeDualBottomCochain R A L d hL ≫
        ModuleCat.ofHom (LinearMap.lcomp R A (f.f d).hom) := by
  let C := (dualComplexFunctor R A (.down ℤ)).obj (op (L.extend (degreeEmbedding 0)))
  let D := (dualComplexFunctor R A (.down ℤ)).obj (op (K.extend (degreeEmbedding 0)))
  let φ : C ⟶ D := (dualComplexFunctor R A (.down ℤ)).map
    (extendMap f (degreeEmbedding 0)).op
  let hC := dual_term_isZero R A (L.extend (degreeEmbedding 0)) (d-1)
    (nonnegative_extend_below_isZero R L d hL (d-1) (by omega))
  let hD := dual_term_isZero R A (K.extend (degreeEmbedding 0)) (d-1)
    (nonnegative_extend_below_isZero R K d hK (d-1) (by omega))
  let eK := K.extendXIso (degreeEmbedding 0)
    (show (degreeEmbedding 0).f d = (d : ℤ) by change (0 : ℤ) + d = d; omega)
  let eL := L.extendXIso (degreeEmbedding 0)
    (show (degreeEmbedding 0).f d = (d : ℤ) by change (0 : ℤ) + d = d; omega)
  let cK : D.X (d : ℤ) ⟶ ModuleCat.of R (K.X d →ₗ[R] A) := (LinearEquiv.arrowCongr eK.toLinearEquiv (LinearEquiv.refl R A)).toModuleIso.hom
  let cL : C.X (d : ℤ) ⟶ ModuleCat.of R (L.X d →ₗ[R] A) := (LinearEquiv.arrowCongr eL.toLinearEquiv (LinearEquiv.refl R A)).toModuleIso.hom
  change homologyMap φ (d : ℤ) ≫ (bottomCochain R D d hD ≫ cK) =
    (bottomCochain R C d hC ≫ cL) ≫ _
  rw [← Category.assoc, bottomCochain_natural R φ (d : ℤ) hC hD, Category.assoc, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (L.extend (degreeEmbedding 0)).X (d : ℤ) →ₗ[R] A at a
  apply LinearMap.ext
  intro x
  change a ((extendMap f (degreeEmbedding 0)).f (d : ℤ) (eK.inv x)) =
    a (eL.inv (f.f d x))
  have he := extendMap_f f (degreeEmbedding 0)
    (show (degreeEmbedding 0).f d = (d : ℤ) by change (0 : ℤ) + d = d; omega)
  rw [he]
  change a (eL.inv (f.f d (eK.hom (eK.inv x)))) = _
  have hx : eK.hom (eK.inv x) = x :=
    congrArg (fun k : K.X d ⟶ K.X d => k x) eK.inv_hom_id
  rw [hx]
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.ThomClass
open scoped TensorProduct Simplicial
open P202Specs.AlexanderWhitney P202Specs.SingularChains
variable (R : Type u) [CommRing R]
open P202Specs.ThomClass P202Specs.RelativeSingularChains

def pointMapToSpace (X : TopCat.{v}) (x : X) : pointPair.{v}.space ⟶ X :=
  TopCat.ofHom ⟨fun _ => x, continuous_const⟩

/-- A linear form in the bottom total degree is detected by restrictions
along all actual point maps in the first factor. -/
theorem totalTensorSingle_linearForm_zero_of_points
    (X : TopCat.{v}) (d : ℕ) (A : Type w) [AddCommGroup A] [Module R A]
    (a : TensorTotal R (complex R R X) (rankSingle R d) d →ₗ[R] A)
    (ha : ∀ x : X, a.comp (tensorTotalMap R (chainMap R R (pointMapToSpace X x))
      (𝟙 (rankSingle R d)) d) = 0) : a = 0 := by
  let e := totalTensorSingleDegreeEquiv R (complex R R X) d 0
  let b := a.comp e.symm.toLinearMap
  have hb : b = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    let x := simplexEquiv X 0 s (Convexity.StdSimplex.single 0)
    have hs : s = constantSimplex X x 0 := simplex_zero_constant X s
    let P0 := pointPair.{v}.space
    let e0 := totalTensorSingleDegreeEquiv R (complex R R P0) d 0
    let z0 : Chains R P0 0 := Finsupp.single (constantSimplex P0 PUnit.unit 0) r
    let z := e0.symm z0
    let f := chainMap R R (pointMapToSpace X x)
    have hz : e (tensorTotalMap R f (𝟙 (rankSingle R d)) d z) = Finsupp.single s r := by
      have hh := totalTensorSingleDegreeEquiv_naturality R f d 0 z
      change e (tensorTotalMap R f (𝟙 (rankSingle R d)) d z) = f.f 0 (e0 z) at hh
      rw [hh]
      change (chainMap R R (pointMapToSpace X x)).f 0 (e0 (e0.symm z0)) = _
      rw [e0.apply_symm_apply]
      change Finsupp.mapDomain ((TopCat.toSSet.map (pointMapToSpace X x)).app (Opposite.op ⦋0⦌)) z0 = _
      rw [Finsupp.mapDomain_single, map_constantSimplex]
      change Finsupp.single (constantSimplex X x 0) r = Finsupp.single s r
      rw [← hs]
    have hpre : e.symm (Finsupp.single s r) =
        tensorTotalMap R f (𝟙 (rankSingle R d)) d z := by
      apply e.injective
      rw [e.apply_symm_apply, hz]
    change a (e.symm (Finsupp.single s r)) = 0
    rw [hpre]
    exact LinearMap.congr_fun (ha x) z
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun hb (e z)
  change a (e.symm (e z)) = 0 at hz
  simpa only [e.symm_apply_apply, LinearMap.zero_apply] using hz

end P202.ThomClass




noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open P202Specs.SingularChains P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R]

lemma totalTensorSingle_dual_cohomology_below_isZero
    (K : Chain.{u,v} R) (d : ℕ) (A : Type w) [AddCommGroup A] [Module R A]
    (q : ℤ) (hq : q < (d : ℤ)) :
    IsZero (((dualComplexFunctor R A (.down ℤ)).obj
      (op ((totalTensorComplex R K (rankSingle R d)).extend (degreeEmbedding 0)))).homology q) :=
  nonnegative_dual_cohomology_below_isZero R A
    (totalTensorComplex R K (rankSingle R d)) d
    (totalTensorSingle_below_isZero R K d) q hq

theorem totalTensorSingle_cohomology_zero_of_points
    (X : TopCat.{v}) (d : ℕ) (A : Type w) [AddCommGroup A] [Module R A]
    (c : ((dualComplexFunctor R A (.down ℤ)).obj
      (op ((totalTensorComplex R (complex R R X) (rankSingle R d)).extend
        (degreeEmbedding 0)))).homology (d : ℤ))
    (hc : ∀ x : X, homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (extendMap (totalTensorMap R (chainMap R R (pointMapToSpace X x))
        (𝟙 (rankSingle R d))) (degreeEmbedding 0)).op) (d : ℤ) c = 0) : c = 0 := by
  let K := totalTensorComplex R (complex R R X) (rankSingle R d)
  let hK := totalTensorSingle_below_isZero R (complex R R X) d
  let b := nonnegativeDualBottomCochain R A K d hK
  have hbmono : Function.Injective b := (ModuleCat.mono_iff_injective b).mp inferInstance
  apply hbmono
  rw [map_zero]
  apply totalTensorSingle_linearForm_zero_of_points R X d A
  intro x
  let P0 := pointPair.{v}.space
  let L := totalTensorComplex R (complex R R P0) (rankSingle R d)
  let hL := totalTensorSingle_below_isZero R (complex R R P0) d
  let f : L ⟶ K := totalTensorMap R (chainMap R R (pointMapToSpace X x)) (𝟙 (rankSingle R d))
  have hn := nonnegativeDualBottomCochain_natural R A f d hL hK
  have he := congrArg (fun k => k c) hn
  change nonnegativeDualBottomCochain R A L d hL
      (homologyMap ((dualComplexFunctor R A (.down ℤ)).map
        (extendMap f (degreeEmbedding 0)).op) (d : ℤ) c) =
    (b c).comp (f.f d).hom at he
  rw [hc x, map_zero] at he
  exact he.symm
end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace P202.ThomClass
variable (R : Type u) [CommRing R]
@[reassoc]
lemma totalTensorCokernelIso_π (K : Chain.{u,v} R) {L M : Chain.{u,v} R} (f : L ⟶ M) :
    cokernel.π (totalTensorMap R (𝟙 K) f) ≫ (totalTensorCokernelIso R K f).hom =
      totalTensorMap R (𝟙 K) (cokernel.π f) := by
  unfold totalTensorCokernelIso
  apply Cofork.IsColimit.π_desc

lemma totalTensorMap_interchange {K K' L M : Chain.{u,v} R}
    (a : K ⟶ K') (b : L ⟶ M) :
    totalTensorMap R (𝟙 K) b ≫ totalTensorMap R a (𝟙 M) =
      totalTensorMap R a (𝟙 L) ≫ totalTensorMap R (𝟙 K') b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map (a.f i.val.1).hom LinearMap.id
      (TensorProduct.map LinearMap.id (b.f i.val.2).hom (z i)) =
    TensorProduct.map LinearMap.id (b.f i.val.2).hom
      (TensorProduct.map (a.f i.val.1).hom LinearMap.id (z i))
  simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

def tensorCokernelFirstMap {K K' L M : Chain.{u,v} R}
    (a : K ⟶ K') (b : L ⟶ M) :
    cokernel (totalTensorMap R (𝟙 K) b) ⟶ cokernel (totalTensorMap R (𝟙 K') b) :=
  cokernel.map _ _ (totalTensorMap R a (𝟙 L)) (totalTensorMap R a (𝟙 M))
    (totalTensorMap_interchange R a b)

lemma totalTensorCokernelIso_natural {K K' L M : Chain.{u,v} R}
    (a : K ⟶ K') (b : L ⟶ M) :
    tensorCokernelFirstMap R a b ≫ (totalTensorCokernelIso R K' b).hom =
      (totalTensorCokernelIso R K b).hom ≫ totalTensorMap R a (𝟙 (cokernel b)) := by
  apply (cancel_epi (cokernel.π (totalTensorMap R (𝟙 K) b))).mp
  simp only [tensorCokernelFirstMap, cokernel.map, cokernel.π_desc_assoc,
    Category.assoc, totalTensorCokernelIso_π, totalTensorCokernelIso_π_assoc]
  exact (totalTensorMap_interchange R a (cokernel.π b)).symm

open P202Specs.SingularChains P202Specs.RelativeSingularChains
@[reassoc]
lemma relativeTensorComplexIso_π (X : TopCat.{v}) (B : Pair.{v}) :
    cokernel.π (tensorSecondInclusion R X B) ≫ (relativeTensorComplexIso R X B).hom =
      totalTensorMap R (𝟙 (complex R R X)) (projection (chainFunctor R R) B) := by
  simp only [relativeTensorComplexIso, Iso.trans_hom, ← Category.assoc,
    π_comp_cokernelIsoOfEq_hom, totalTensorCokernelIso_π]

lemma totalTensorMap_singular_first {X X' Y : TopCat.{v}} (a : X ⟶ X') :
    P202.AlexanderWhitney.tensorChainMap R a (𝟙 Y) =
      totalTensorMap R (chainMap R R a) (𝟙 (complex R R Y)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map ((chainMap R R a).f i.val.1).hom
      ((chainMap R R (𝟙 Y)).f i.val.2).hom (z i) =
    TensorProduct.map ((chainMap R R a).f i.val.1).hom LinearMap.id (z i)
  rw [P202.SingularChains.chainMap_id]
  rfl

lemma tensorSecondInclusion_first_natural {X X' : TopCat.{v}} (a : X ⟶ X') (B : Pair.{v}) :
    tensorSecondInclusion R X B ≫ P202.AlexanderWhitney.tensorChainMap R a (𝟙 B.space) =
      P202.AlexanderWhitney.tensorChainMap R a (𝟙 B.sub) ≫ tensorSecondInclusion R X' B := by
  rw [totalTensorMap_singular_first, totalTensorMap_singular_first,
    totalTensorMap_singular_second, totalTensorMap_singular_second]
  exact totalTensorMap_interchange R (chainMap R R a) (chainMap R R B.inclusion)

def relativeTensorFirstMap {X X' : TopCat.{v}} (a : X ⟶ X') (B : Pair.{v}) :
    relativeTensorComplex R X B ⟶ relativeTensorComplex R X' B :=
  cokernel.map _ _ (P202.AlexanderWhitney.tensorChainMap R a (𝟙 B.sub))
    (P202.AlexanderWhitney.tensorChainMap R a (𝟙 B.space))
    (tensorSecondInclusion_first_natural R a B)

lemma relativeTensorComplexIso_natural {X X' : TopCat.{v}} (a : X ⟶ X') (B : Pair.{v}) :
    relativeTensorFirstMap R a B ≫ (relativeTensorComplexIso R X' B).hom =
      (relativeTensorComplexIso R X B).hom ≫
        totalTensorMap R (chainMap R R a) (𝟙 (nonnegative R R B)) := by
  apply (cancel_epi (cokernel.π (tensorSecondInclusion R X B))).mp
  simp only [relativeTensorFirstMap, cokernel.map, cokernel.π_desc_assoc,
    Category.assoc, relativeTensorComplexIso_π, relativeTensorComplexIso_π_assoc,
    totalTensorMap_singular_first]
  exact (totalTensorMap_interchange R (chainMap R R a)
    (projection (chainFunctor R R) B)).symm
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.ThomClass
open scoped TensorProduct Simplicial
open P202Specs.AlexanderWhitney P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R]

lemma productSecondFirst_square {X Y : TopCat.{v}} (f : X ⟶ Y) (B : Pair.{v}) :
    productSecondInclusion R X B ≫ chainMap R R (productMap f (𝟙 B.space)) =
      chainMap R R (productMap f (𝟙 B.sub)) ≫ productSecondInclusion R Y B := by
  change (chainFunctor R R).map _ ≫ (chainFunctor R R).map _ =
    (chainFunctor R R).map _ ≫ (chainFunctor R R).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

def relativeProductFirstMap {X Y : TopCat.{v}} (f : X ⟶ Y) (B : Pair.{v}) :
    relativeProductComplex R X B ⟶ relativeProductComplex R Y B :=
  cokernel.map _ _ (chainMap R R (productMap f (𝟙 B.sub)))
    (chainMap R R (productMap f (𝟙 B.space))) (productSecondFirst_square R f B)

lemma relativeAW_first_natural {X Y : TopCat.{v}} (f : X ⟶ Y) (B : Pair.{v}) :
    relativeAW R X B ≫ relativeTensorFirstMap R f B =
      relativeProductFirstMap R f B ≫ relativeAW R Y B := by
  apply (cancel_epi (cokernel.π (productSecondInclusion R X B))).mp
  simp only [relativeAW, relativeTensorFirstMap, relativeProductFirstMap,
    cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, ← P202.EilenbergZilber.comparison_toTensor_natural, Category.assoc]


def secondProductFirstMap {X Y : TopCat.{v}} (f : X ⟶ Y) (B : Pair.{v}) :
    secondProductPair X B ⟶ secondProductPair Y B where
  map := productMap f (𝟙 B.space)
  mapsTo := fun _ hz => hz

lemma relativeProductComplexIso_π (X : TopCat.{v}) (B : Pair.{v}) :
    cokernel.π (productSecondInclusion R X B) ≫ (relativeProductComplexIso R X B).hom =
      projection (chainFunctor R R) (secondProductPair X B) := by
  simp [relativeProductComplexIso, cokernel.mapIso, cokernel.map]

lemma relativeProductComplexIso_first_natural {X Y : TopCat.{v}}
    (f : X ⟶ Y) (B : Pair.{v}) :
    relativeProductFirstMap R f B ≫ (relativeProductComplexIso R Y B).hom =
      (relativeProductComplexIso R X B).hom ≫
        relativeMap (chainFunctor R R) (secondProductFirstMap f B) := by
  apply (cancel_epi (cokernel.π (productSecondInclusion R X B))).mp
  rw [← Category.assoc]
  rw [relativeProductFirstMap, cokernel.π_desc, Category.assoc, relativeProductComplexIso_π,
    ← Category.assoc, relativeProductComplexIso_π, projection_map]
  rfl

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.ThomClass
open scoped TensorProduct Simplicial
open P202Specs.AlexanderWhitney P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R]

lemma relativeProductComplexIso_inv_first_natural {X Y : TopCat.{v}}
    (f : X ⟶ Y) (B : Pair.{v}) :
    relativeMap (chainFunctor R R) (secondProductFirstMap f B) ≫
      (relativeProductComplexIso R Y B).inv =
        (relativeProductComplexIso R X B).inv ≫ relativeProductFirstMap R f B := by
  rw [← cancel_mono (relativeProductComplexIso R Y B).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [relativeProductComplexIso_first_natural, Iso.inv_hom_id_assoc]

def secondProductTensorMap (X : TopCat.{v}) (B : Pair.{v})
    {L : Chain.{u,v} R} (g : nonnegative R R B ⟶ L) :
    nonnegative R R (secondProductPair X B) ⟶ totalTensorComplex R (complex R R X) L :=
  (relativeProductComplexIso R X B).inv ≫ relativeAW R X B ≫
    (relativeTensorComplexIso R X B).hom ≫ totalTensorMap R (𝟙 _) g

lemma secondProductTensorMap_natural {X Y : TopCat.{v}}
    (f : X ⟶ Y) (B : Pair.{v}) {L : Chain.{u,v} R} (g : nonnegative R R B ⟶ L) :
    relativeMap (chainFunctor R R) (secondProductFirstMap f B) ≫ secondProductTensorMap R Y B g =
      secondProductTensorMap R X B g ≫ totalTensorMap R (chainMap R R f) (𝟙 L) := by
  simp only [secondProductTensorMap]
  rw [← Category.assoc, relativeProductComplexIso_inv_first_natural,
    Category.assoc, ← Category.assoc (relativeProductFirstMap R f B),
    ← relativeAW_first_natural]
  simp only [Category.assoc]
  rw [← Category.assoc (relativeTensorFirstMap R f B), relativeTensorComplexIso_natural]
  simp only [Category.assoc]
  rw [totalTensorMap_interchange]

/-- The canonical natural comparison is a true equivalence; its hom is kept
explicit so every literal fiber restriction can be transported. -/
theorem secondProductTensorMap_homotopy (X : TopCat.{v}) (B : Pair.{v})
    {L : Chain.{u,v} R} (e : HomotopyEquiv (nonnegative R R B) L) :
    ∃ h : HomotopyEquiv (ordinary R R (secondProductPair X B))
      ((totalTensorComplex R (complex R R X) L).extend (degreeEmbedding 0)),
      h.hom = (P202.CohomologyExcisionMV.relativeExtensionIso R (secondProductPair X B)).inv ≫
        extendMap (secondProductTensorMap R X B e.hom) (degreeEmbedding 0) := by
  obtain ⟨a, ha⟩ := relativeAW_integer_homotopy R X B
  let F := (degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R)
  let i := F.mapIso (relativeProductComplexIso R X B) ≪≫
    P202.CohomologyExcisionMV.relativeExtensionIso R (secondProductPair X B)
  let j := F.mapIso (relativeTensorComplexIso R X B)
  let z := (((HomotopyEquiv.ofIso i.symm).trans a).trans (HomotopyEquiv.ofIso j)).trans
    (nonnegativeExtendHomotopyEquiv R (totalTensorHomotopyEquiv R (complex R R X) e))
  refine ⟨z, ?_⟩
  simp only [z, HomotopyEquiv.trans_hom, HomotopyEquiv.ofIso, ha,
    nonnegativeExtendHomotopyEquiv, totalTensorHomotopyEquiv, i, j,
    Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Functor.mapIso_hom,
    secondProductTensorMap, extendMap_comp, Category.assoc]
  rfl
end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.MayerVietoris
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- The full quotient normal bundle, relative to the complement of its zero section. -/
def normalPair (N : NormalBundle T S i) : Pair.{u} :=
  ⟨TopCat.of (NormalTotal N), {z | z ≠ normalZero N z.proj}⟩

lemma normalPair_subspace_eq (N : NormalBundle T S i) :
    (normalPair N).subspace = (Set.range (normalZero N))ᶜ := by
  ext z
  change z ≠ normalZero N z.proj ↔ z ∉ Set.range (normalZero N)
  constructor
  · rintro hz ⟨p, hp⟩
    apply hz
    have he : p = z.proj := congrArg Bundle.TotalSpace.proj hp
    exact hp.symm.trans (congrArg (normalZero N) he)
  · intro hz he
    exact hz ⟨z.proj, he.symm⟩

lemma normalPair_subspace_isOpen [CompactSpace P] (N : NormalBundle T S i) :
    IsOpen (normalPair N).subspace := by
  letI := (normalBundle N).totalManifold.topologicalManifold.hausdorff
  have hc : Continuous (normalZero N) :=
    continuous_iff_continuousAt.mpr (fun p => ((normalBundle N).zero_smooth p).1)
  rw [normalPair_subspace_eq]
  exact (isCompact_range hc).isClosed.isOpen_compl

/-- The original full normal fiber includes in the full normal relative pair. -/
def fiberToNormal (N : NormalBundle T S i) (p : P) : fiberPair N p ⟶ normalPair N where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := by
    intro z hz he
    apply hz
    apply Subtype.ext
    exact he.trans (congrArg (normalZero N) z.property)

/-- The tubular domain includes in the full quotient normal pair. -/
def domainToNormal (N : NormalBundle T S i) (K : TubularNeighborhood N) :
    tubularDomainPair N K ⟶ normalPair N :=
  openPairInclusion (normalPair N) K.domain

lemma sliceToNormal_comp (N : NormalBundle T S i) (K : TubularNeighborhood N) (p : P) :
    sliceToDomain N K p ≫ domainToNormal N K = sliceToFiber N K p ≫ fiberToNormal N p :=
  PairMap.ext _ _ rfl

lemma domainToNormal_isIso [CompactSpace P] (N : NormalBundle T S i)
    (K : TubularNeighborhood N) (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (domainToNormal N K).op) := by
  apply openPairInclusion_isIso (normalPair N) (normalPair_subspace_isOpen N)
    K.domain K.isOpen_domain
  intro z hz
  have he : z = normalZero N z.proj := Classical.not_not.mp hz
  rw [he]
  exact K.zero_mem z.proj

def normalDomainCohomologyEquiv [CompactSpace P] (N : NormalBundle T S i)
    (K : TubularNeighborhood N) (R : Type v) [CommRing R] (q : ℤ) :
    relativeCohomology R R (normalPair N) q ≃ₗ[R]
      relativeCohomology R R (tubularDomainPair N K) q := by
  haveI := domainToNormal_isIso N K R q
  exact (asIso ((relativeCohomologyFunctor R R q).map (domainToNormal N K).op)).toLinearEquiv

/-- Excision on both sides of the actual tube identifies ambient and normal
bundle cohomology, before any orientation or rank hypothesis. -/
def ambientNormalCohomologyEquiv [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) :
    relativeCohomology R R (ambientPair i) q ≃ₗ[R]
      relativeCohomology R R (normalPair N) q :=
  (tubularCohomologyEquiv hi N K R q).trans (normalDomainCohomologyEquiv N K R q).symm

lemma ambientNormalCohomologyEquiv_restrict [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (q : ℤ) (p : P)
    (c : relativeCohomology R R (ambientPair i) q) :
    (relativeCohomologyFunctor R R q).map (sliceToAmbient N K p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K p).op
        ((relativeCohomologyFunctor R R q).map (fiberToNormal N p).op
          (ambientNormalCohomologyEquiv hi N K R q c)) := by
  let F := relativeCohomologyFunctor R R q
  rw [← tubularCohomologyEquiv_restrict hi N K R q p]
  change F.map (sliceToDomain N K p).op (tubularCohomologyEquiv hi N K R q c) =
    (F.map (fiberToNormal N p).op ≫ F.map (sliceToFiber N K p).op)
      (ambientNormalCohomologyEquiv hi N K R q c)
  rw [← F.map_comp, ← op_comp, ← sliceToNormal_comp, op_comp, F.map_comp]
  change _ = F.map (sliceToDomain N K p).op
    (normalDomainCohomologyEquiv N K R q
      ((normalDomainCohomologyEquiv N K R q).symm (tubularCohomologyEquiv hi N K R q c)))
  rw [LinearEquiv.apply_symm_apply]

lemma normal_fiber_values_iff_slice [CompactSpace P] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (R : Type v) [CommRing R] (d : ℕ) (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ)) :
    (∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToAmbient N K p).op c =
      (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToFiber N K p).op (o.generator p)) ↔
    (∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op
      (ambientNormalCohomologyEquiv hi N K R (d : ℤ) c) = o.generator p) := by
  constructor
  · intro hc p
    haveI := sliceToFiber_isIso N K p R (d : ℤ)
    apply (ModuleCat.mono_iff_injective
      ((relativeCohomologyFunctor R R (d : ℤ)).map (sliceToFiber N K p).op)).mp inferInstance
    rw [← ambientNormalCohomologyEquiv_restrict hi N K R (d : ℤ) p]
    exact hc p
  · intro hc p
    rw [ambientNormalCohomologyEquiv_restrict hi N K R (d : ℤ) p, hc p]

/-- Restriction of the full normal pair over an arbitrary subset of the base. -/
def normalOverPair (N : NormalBundle T S i) (U : Set P) : Pair.{u} :=
  piece (normalPair N) (Bundle.TotalSpace.proj ⁻¹' U)

/-- A genuine original bundle trivialization gives the normal relative product
on every subset of its base set, with the original quotient normal vectors. -/
def normalChartPairIso (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) :
    normalOverPair N U ≅ secondProductPair (TopCat.of U) (modelPair.{u} (n-m)) := by
  classical
  let e := (normalBundle N).trivialization a
  letI : e.IsLinear ℝ := (normalBundle N).linear a
  have hU' : U ⊆ e.baseSet := by
    change U ⊆ ((normalBundle N).trivialization a).baseSet
    rwa [(normalBundle N).trivialization_baseSet a]
  let h : (normalOverPair N U).space ≃ₜ
      (secondProductPair (TopCat.of U) (modelPair.{u} (n-m))).space :=
    (e.preimageHomeomorph hU').trans ((Homeomorph.refl U).prodCongr Homeomorph.ulift.symm)
  apply pairIsoOfHomeomorph _ _ h
  intro z
  have hp : z.val.proj ∈ e.baseSet := hU' z.property
  have hh : (h z).2.down = e.linearEquivAt ℝ z.val.proj hp z.val.snd := by
    change (e.preimageHomeomorph hU' z).2 = _
    rw [Bundle.Trivialization.preimageHomeomorph_apply]
    rfl
  change z.val ≠ normalZero N z.val.proj ↔ (h z).2.down ≠ 0
  rw [hh]
  have hzero : (e.linearEquivAt ℝ z.val.proj hp z.val.snd ≠ 0) ↔ z.val.snd ≠ 0 :=
    not_congr (e.linearEquivAt ℝ z.val.proj hp).map_eq_zero_iff
  apply Iff.trans ?_ hzero.symm
  constructor
  · intro hz hv
    apply hz
    cases z with
    | mk z hz =>
      cases z with
      | mk p v =>
        change (⟨p, v⟩ : NormalTotal N) = ⟨p, 0⟩
        exact congrArg (fun v : NormalFiber N p => (⟨p, v⟩ : NormalTotal N)) hv
  · intro hv hz
    apply hv
    let hs : NormalTotal N → NormalFiber N z.val.proj := fun w =>
      if hpw : w.proj = z.val.proj then hpw ▸ w.snd else 0
    have hs1 : hs z.val = z.val.snd := by simp [hs]
    have hs0 : hs (normalZero N z.val.proj) = 0 := by simp [hs, normalZero]
    exact hs1.symm.trans ((congrArg hs hz).trans hs0)

end P202.ThomClass

namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.MayerVietoris
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

lemma normalProjection_continuous (N : NormalBundle T S i) :
    Continuous (Bundle.TotalSpace.proj : NormalTotal N → P) :=
  continuous_iff_continuousAt.mpr (fun z => ((normalBundle N).projection_smooth z).1)

def normalOverMono (N : NormalBundle T S i) {U V : Set P} (h : U ⊆ V) :
    normalOverPair N U ⟶ normalOverPair N V :=
  pieceMono (normalPair N) (Set.preimage_mono h)

def fiberToNormalOver (N : NormalBundle T S i) (U : Set P) (p : P) (hp : p ∈ U) :
    fiberPair N p ⟶ normalOverPair N U := by
  let hmem : ∀ z : Fiber N p, z.val.proj ∈ U := fun z => z.property.symm ▸ hp
  exact {
    map := TopCat.ofHom ⟨fun z : Fiber N p => ⟨z.val, hmem z⟩,
      (continuous_subtype_val : Continuous (Subtype.val : Fiber N p → NormalTotal N)).subtype_mk hmem⟩
    mapsTo := (fiberToNormal N p).mapsTo }

lemma fiberToNormalOver_comp (N : NormalBundle T S i) {U V : Set P}
    (h : U ⊆ V) (p : P) (hp : p ∈ U) :
    fiberToNormalOver N U p hp ≫ normalOverMono N h = fiberToNormalOver N V p (h hp) :=
  PairMap.ext _ _ rfl

variable (R : Type v) [CommRing R]

def NormalHasValues (N : NormalBundle T S i) (U : Set P) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (c : relativeCohomology R R (normalOverPair N U) (d : ℤ)) : Prop :=
  ∀ (p : P) (hp : p ∈ U),
    (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormalOver N U p hp).op c = g p

lemma normalFiberRestriction_mono (N : NormalBundle T S i) {U V : Set P}
    (h : U ⊆ V) (q : ℤ) (c : relativeCohomology R R (normalOverPair N V) q)
    (p : P) (hp : p ∈ U) :
    (relativeCohomologyFunctor R R q).map (fiberToNormalOver N U p hp).op
      ((relativeCohomologyFunctor R R q).map (normalOverMono N h).op c) =
    (relativeCohomologyFunctor R R q).map (fiberToNormalOver N V p (h hp)).op c := by
  change ((relativeCohomologyFunctor R R q).map (normalOverMono N h).op ≫
    (relativeCohomologyFunctor R R q).map (fiberToNormalOver N U p hp).op) c = _
  rw [← Functor.map_comp, ← op_comp, fiberToNormalOver_comp]

lemma normalHasValues_mono (N : NormalBundle T S i) {U V : Set P}
    (h : U ⊆ V) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (c : relativeCohomology R R (normalOverPair N V) (d : ℤ))
    (hc : NormalHasValues R N V d g c) :
    NormalHasValues R N U d g
      ((relativeCohomologyFunctor R R (d : ℤ)).map (normalOverMono N h).op c) := by
  intro p hp
  rw [normalFiberRestriction_mono R N h]
  exact hc p (h hp)

lemma normalHasValues_union (N : NormalBundle T S i) (U V : Set P) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (c : relativeCohomology R R (normalOverPair N (U ∪ V)) (d : ℤ)) :
    NormalHasValues R N (U ∪ V) d g c ↔
      NormalHasValues R N U d g ((relativeCohomologyFunctor R R (d : ℤ)).map
        (normalOverMono N Set.subset_union_left).op c) ∧
      NormalHasValues R N V d g ((relativeCohomologyFunctor R R (d : ℤ)).map
        (normalOverMono N Set.subset_union_right).op c) := by
  constructor
  · intro hc
    exact ⟨normalHasValues_mono R N Set.subset_union_left d g c hc,
      normalHasValues_mono R N Set.subset_union_right d g c hc⟩
  · rintro ⟨hU,hV⟩ p (hp | hp)
    · exact (normalFiberRestriction_mono R N Set.subset_union_left _ c p hp).symm.trans (hU p hp)
    · exact (normalFiberRestriction_mono R N Set.subset_union_right _ c p hp).symm.trans (hV p hp)

/-- The local Thom assertion is required on every open subregion, precisely
so it may be used on overlaps in a finite cover. -/
def NormalThomOn (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ)) (U : Set P) : Prop :=
  ∀ W : Set P, IsOpen W → W ⊆ U →
    (∀ q : ℤ, q < (d : ℤ) → IsZero (relativeCohomology R R (normalOverPair N W) q)) ∧
    ∃! c : relativeCohomology R R (normalOverPair N W) (d : ℤ),
      NormalHasValues R N W d g c

/-- The local Thom assertion glues across any two open subsets of the base.
Compatibility on the overlap follows from local uniqueness there. -/
theorem normalThomOn_union (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    {U V : Set P} (hU : IsOpen U) (hV : IsOpen V)
    (hTU : NormalThomOn R N d g U) (hTV : NormalThomOn R N d g V) :
    NormalThomOn R N d g (U ∪ V) := by
  intro W hW hWU
  let L := W ∩ U
  let D := W ∩ V
  have hL : IsOpen L := hW.inter hU
  have hD : IsOpen D := hW.inter hV
  have hLD : L ∪ D = W := by
    ext p
    constructor
    · rintro (hp | hp); exact hp.1; exact hp.1
    · intro hp
      rcases hWU hp with hpU | hpV
      · exact Or.inl ⟨hp,hpU⟩
      · exact Or.inr ⟨hp,hpV⟩
  obtain ⟨hvL,a,ha,hau⟩ := hTU L hL Set.inter_subset_right
  obtain ⟨hvD,b,hb,hbu⟩ := hTV D hD Set.inter_subset_right
  obtain ⟨hvI,e,he,heu⟩ := hTU (L ∩ D) (hL.inter hD) (fun p hp => hp.1.2)
  let F := relativeCohomologyFunctor R R (d : ℤ)
  have hab : F.map (normalOverMono N (show L ∩ D ⊆ L from Set.inter_subset_left)).op a =
      F.map (normalOverMono N (show L ∩ D ⊆ D from Set.inter_subset_right)).op b :=
    (heu _ (normalHasValues_mono R N Set.inter_subset_left d g a ha)).trans
      (heu _ (normalHasValues_mono R N Set.inter_subset_right d g b hb)).symm
  obtain ⟨c,hc,hcu⟩ := relative_openUnion_glue_unique R R (normalPair N)
    (hL.preimage (normalProjection_continuous N))
    (hD.preimage (normalProjection_continuous N)) (d : ℤ)
    (hvI (d-1) (by omega)) a b hab
  change F.map (normalOverMono N (show L ⊆ L ∪ D from Set.subset_union_left)).op c = a ∧
    F.map (normalOverMono N (show D ⊆ L ∪ D from Set.subset_union_right)).op c = b at hc
  change ∀ e : relativeCohomology R R (normalOverPair N (L ∪ D)) (d : ℤ),
    (F.map (normalOverMono N (show L ⊆ L ∪ D from Set.subset_union_left)).op e = a ∧
      F.map (normalOverMono N (show D ⊆ L ∪ D from Set.subset_union_right)).op e = b) → e = c at hcu
  have hcc : NormalHasValues R N (L ∪ D) d g c := by
    apply (normalHasValues_union R N L D d g c).mpr
    constructor
    · rw [hc.1]
      exact ha
    · rw [hc.2]
      exact hb
  have hcu' : ∀ e, NormalHasValues R N (L ∪ D) d g e → e = c := by
    intro e he
    obtain ⟨heL,heD⟩ := (normalHasValues_union R N L D d g e).mp he
    exact hcu e ⟨hau _ heL, hbu _ heD⟩
  rw [← hLD]
  refine ⟨?_, c, hcc, hcu'⟩
  intro q hq
  exact relative_openUnion_isZero R R (normalPair N)
    (hL.preimage (normalProjection_continuous N))
    (hD.preimage (normalProjection_continuous N)) q
    (hvL q hq) (hvD q hq) (hvI (q-1) (by omega))

end P202.ThomClass

namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology
variable (R : Type v) [CommRing R]

lemma normalThomOn_empty (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ)) :
    NormalThomOn R N d g ∅ := by
  intro W hW hWe
  have hno (p : P) (hp : p ∈ W) : False := hWe hp
  have hzero (q : ℤ) : IsZero (relativeCohomology R R (normalOverPair N W) q) := by
    apply relativeCohomology_isZero_of_subspace_eq_univ R R
    ext z
    exact (hno z.val.proj z.property).elim
  refine ⟨fun q _ => hzero q, 0, ?_, ?_⟩
  · intro p hp
    exact (hno p hp).elim
  · intro c hc
    haveI := ModuleCat.subsingleton_of_isZero (hzero (d : ℤ))
    exact Subsingleton.elim _ _

theorem normalThomOn_finite_union (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    {ι : Type*} (s : Finset ι) (U : ι → Set P)
    (hU : ∀ j ∈ s, IsOpen (U j)) (hTU : ∀ j ∈ s, NormalThomOn R N d g (U j)) :
    NormalThomOn R N d g (⋃ j ∈ s, U j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] using
      normalThomOn_empty R N d g
  | @insert j s hj ih =>
    have hset : (⋃ k ∈ insert j s, U k) = U j ∪ ⋃ k ∈ s, U k := by
      change (⋃ k ∈ (↑(insert j s) : Set ι), U k) = _
      rw [Finset.coe_insert, Set.biUnion_insert]
      rfl
    rw [hset]
    apply normalThomOn_union R N d g (hU j (Finset.mem_insert_self j s))
      (isOpen_biUnion (fun k hk => hU k (Finset.mem_insert_of_mem hk)))
      (hTU j (Finset.mem_insert_self j s))
    exact ih (fun k hk => hU k (Finset.mem_insert_of_mem hk))
      (fun k hk => hTU k (Finset.mem_insert_of_mem hk))

/-- Compactness is used only to pass from local orientation charts to a
finite cover; the relative gluing itself required no compactness. -/
theorem normalThomOn_univ_of_locally [CompactSpace P] (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (hlocal : ∀ p : P, ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ NormalThomOn R N d g U) :
    NormalThomOn R N d g Set.univ := by
  classical
  choose U hU hp hTU using hlocal
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p,hp p⟩)
  have heq : (⋃ j ∈ s, U j) = Set.univ := Set.eq_univ_of_univ_subset hs
  rw [← heq]
  exact normalThomOn_finite_union R N d g s U (fun j _ => hU j) (fun j _ => hTU j)

def normalOverUnivIso (N : NormalBundle T S i) :
    normalOverPair N Set.univ ≅ normalPair N :=
  pairIsoOfHomeomorph _ _ (Homeomorph.Set.univ (NormalTotal N)) (fun _ => Iff.rfl)

/-- The finite-cover construction yields an actual unique class on the full
normal bundle, with the specified values on every original normal fiber. -/
theorem normalClass_exists_unique_of_locally [CompactSpace P]
    (N : NormalBundle T S i) (d : ℕ)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (hlocal : ∀ p : P, ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ NormalThomOn R N d g U) :
    ∃! c : relativeCohomology R R (normalPair N) (d : ℤ),
      ∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c = g p := by
  let F := relativeCohomologyFunctor R R (d : ℤ)
  let e := normalOverUnivIso N
  obtain ⟨_,c,hc,hu⟩ := normalThomOn_univ_of_locally R N d g hlocal
    Set.univ isOpen_univ Set.Subset.rfl
  have hvalues (a : relativeCohomology R R (normalPair N) (d : ℤ)) :
      NormalHasValues R N Set.univ d g (F.map e.hom.op a) ↔
      (∀ p, F.map (fiberToNormal N p).op a = g p) := by
    have he (p : P) : fiberToNormalOver N Set.univ p (Set.mem_univ p) ≫ e.hom = fiberToNormal N p :=
      PairMap.ext _ _ rfl
    change (∀ p hp, F.map (fiberToNormalOver N Set.univ p hp).op (F.map e.hom.op a) = g p) ↔ _
    constructor
    · intro ha p
      have hh := ha p (Set.mem_univ p)
      change (F.map e.hom.op ≫ F.map (fiberToNormalOver N Set.univ p (Set.mem_univ p)).op) a = _ at hh
      rwa [← F.map_comp, ← op_comp, he] at hh
    · intro ha p hp
      change (F.map e.hom.op ≫ F.map (fiberToNormalOver N Set.univ p hp).op) a = _
      rw [← F.map_comp, ← op_comp, he]
      exact ha p
  refine ⟨F.map e.inv.op c, ?_, ?_⟩
  · apply (hvalues _).mp
    have hmap : F.map e.hom.op (F.map e.inv.op c) = c := by
      change (F.map e.inv.op ≫ F.map e.hom.op) c = c
      rw [← F.map_comp, ← op_comp, e.hom_inv_id, op_id, F.map_id]
      rfl
    rw [hmap]
    exact hc
  · intro a ha
    apply (ModuleCat.mono_iff_injective (F.map e.hom.op)).mp inferInstance
    have hmap : F.map e.hom.op (F.map e.inv.op c) = c := by
      change (F.map e.inv.op ≫ F.map e.hom.op) c = c
      rw [← F.map_comp, ← op_comp, e.hom_inv_id, op_id, F.map_id]
      rfl
    rw [hmap]
    exact hu _ ((hvalues a).mpr ha)

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

/-- A product neighborhood with only the normal zero section removed. -/
def secondPuncturedPair (B E : Type u) [TopologicalSpace B] [TopologicalSpace E]
    [Zero E] : Pair.{u} := ⟨TopCat.of (B × E), {z | z.2 ≠ 0}⟩

def verticalPairMap {B E : Type u} [TopologicalSpace B] [TopologicalSpace E]
    [Zero E] (b : B) : puncturedVectorPair E ⟶ secondPuncturedPair B E where
  map := TopCat.ofHom ⟨fun x => (b, x), continuous_const.prodMk continuous_id⟩
  mapsTo := fun _ h => h

/-- A smooth local transition may move its base point. If its normal component
is tangent to the identity, it is nevertheless homotopic on a small punctured
normal ball to the vertical inclusion. The base homotopy remains in the chosen
convex chart neighborhood. -/
theorem exists_pairHomotopy_moving_base
    {B E : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → B × E} {U : Set E} {V : Set B} {b : B}
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U)
    (hV : IsOpen V) (hb : b ∈ V) (hcV : Convex ℝ V)
    (hbase : (f 0).1 = b) (hnormal : (f 0).2 = 0)
    (hf : HasFDerivAt (fun x => (f x).2) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
        secondPuncturedPair V E),
      {x : E | norm x < ε} ⊆ U ∧
      (∀ x, ((g.map x).1.val, (g.map x).2) = f x.val) ∧
      Nonempty (P202Specs.PrismHomotopy.PairHomotopy
        (openPairInclusion (puncturedVectorPair E) {x : E | norm x < ε} ≫
          verticalPairMap (E := E) (⟨b, hb⟩ : V)) g) := by
  obtain ⟨ε₁, hε₁, hnonzero⟩ := exists_pos_nonvanishing_linear_homotopy hnormal hf
  have hbaseNear : ∀ᶠ x in 𝓝 (0 : E), x ∈ U ∧ (f x).1 ∈ V := by
    have hcont := (hfc.continuousAt (hU.mem_nhds h0U)).fst
    have h0V : (f 0).1 ∈ V := by rwa [hbase]
    filter_upwards [hU.mem_nhds h0U, hcont (hV.mem_nhds h0V)] with x hx hfx
    exact ⟨hx, hfx⟩
  obtain ⟨ε₂, hε₂, hsmall₂⟩ := Metric.eventually_nhds_iff.mp hbaseNear
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsmall : ∀ x : E, norm x < ε → x ∈ U ∧ (f x).1 ∈ V := by
    intro x hx
    apply hsmall₂
    simpa only [dist_zero_right] using lt_of_lt_of_le hx (min_le_right ε₁ ε₂)
  have hcont : Continuous (fun x : {x : E // norm x < ε} => f x.val) :=
    hfc.comp_continuous continuous_subtype_val (fun x => (hsmall x x.property).1)
  have hn : ∀ x : E, norm x < ε → x ≠ 0 →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • ((f x).2 - x) ≠ 0 := by
    intro x hx
    exact hnonzero x (lt_of_lt_of_le hx (min_le_left ε₁ ε₂))
  let g : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
      secondPuncturedPair V E := {
    map := TopCat.ofHom ⟨fun x => (⟨(f x.val).1, (hsmall x x.property).2⟩, (f x.val).2),
      (hcont.fst.subtype_mk _).prodMk hcont.snd⟩
    mapsTo := by
      intro x hx
      have hh := hn x.val x.property hx 1 (by simp)
      change (f x.val).2 ≠ 0
      simpa only [one_smul, add_sub_cancel] using hh }
  let H : unitInterval × {x : E // norm x < ε} → V × E := fun tx =>
    (⟨b + tx.1.val • ((f tx.2.val).1 - b),
      hcV.add_smul_sub_mem hb (hsmall tx.2 tx.2.property).2 tx.1.property⟩,
      tx.2.val + tx.1.val • ((f tx.2.val).2 - tx.2.val))
  have hH : Continuous H := by
    have hbaseH : Continuous (fun tx : unitInterval × {x : E // norm x < ε} =>
        b + tx.1.val • ((f tx.2.val).1 - b)) :=
      continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
        ((hcont.fst.comp continuous_snd).sub continuous_const))
    exact (hbaseH.subtype_mk _).prodMk
      ((continuous_subtype_val.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).smul
          ((hcont.snd.comp continuous_snd).sub (continuous_subtype_val.comp continuous_snd))))
  refine ⟨ε, hε, g, fun x hx => (hsmall x hx).1, fun _ => rfl, ⟨?_⟩⟩
  refine {
    homotopy := {
      toFun := H
      continuous_toFun := hH
      map_zero_left := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          change b + (0 : ℝ) • ((f x.val).1 - b) = b
          simp
        · change x.val + (0 : ℝ) • ((f x.val).2 - x.val) = x.val
          simp
      map_one_left := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          change b + (1 : ℝ) • ((f x.val).1 - b) = (f x.val).1
          simp
        · change x.val + (1 : ℝ) • ((f x.val).2 - x.val) = (f x.val).2
          simp }
    preserves := ?_ }
  intro t x
  exact hn x.val.val x.val.property x.property t.val t.property

/-- The moving-base transition induces the same pullback as the vertical
inclusion after restricting to an excisive normal ball, in every degree. -/
theorem exists_cohomology_pullback_moving_base
    {B E : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → B × E} {U : Set E} {V : Set B} {b : B}
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U)
    (hV : IsOpen V) (hb : b ∈ V) (hcV : Convex ℝ V)
    (hbase : (f 0).1 = b) (hnormal : (f 0).2 = 0)
    (hf : HasFDerivAt (fun x => (f x).2) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (g : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
        secondPuncturedPair V E),
      {x : E | norm x < ε} ⊆ U ∧
      (∀ x, ((g.map x).1.val, (g.map x).2) = f x.val) ∧
      ∀ (R : Type v) [CommRing R] (q : ℤ),
        (relativeCohomologyFunctor R R q).map g.op =
          (relativeCohomologyFunctor R R q).map
            (verticalPairMap (E := E) (⟨b, hb⟩ : V)).op ≫
          (relativeCohomologyFunctor R R q).map
            (openPairInclusion (puncturedVectorPair E) {x : E | norm x < ε}).op ∧
        IsIso ((relativeCohomologyFunctor R R q).map
          (openPairInclusion (puncturedVectorPair E) {x : E | norm x < ε}).op) := by
  obtain ⟨ε, hε, g, hsmall, hg, ⟨H⟩⟩ :=
    exists_pairHomotopy_moving_base hU h0U hfc hV hb hcV hbase hnormal hf
  refine ⟨ε, hε, g, hsmall, hg, ?_⟩
  intro R _ q
  have he := ((P202.CohomologyPairs.homotopy_invariant R R).2 H q).symm
  rw [op_comp, Functor.map_comp] at he
  refine ⟨he, ?_⟩
  apply openPairInclusion_isIso
  · change IsOpen ({(0 : E)}ᶜ : Set E)
    exact isClosed_singleton.isOpen_compl
  · exact isOpen_lt continuous_norm continuous_const
  · intro x hx
    change ¬x ≠ 0 at hx
    change norm x < ε
    simpa only [Classical.not_not.mp hx, norm_zero] using hε

end P202.ThomClass

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- Both directions of the actual tubular homeomorphism have smooth total
representatives on their original open domains. The fallback is used only away
from the domains. -/
theorem tubular_smoothRepresentatives (N : NormalBundle T S i)
    (K : TubularNeighborhood N) (p : P) :
    ∃ (F : NormalTotal N → M) (G : M → NormalTotal N),
      ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
        S.smoothStructure.val F K.domain ∧
      ManifoldSmoothOn S.smoothStructure.val
        (normalBundle N).totalManifold.smoothStructure.val G K.target ∧
      (∀ z (hz : z ∈ K.domain), F z = (K.homeomorph ⟨z, hz⟩).val) ∧
      (∀ x (hx : x ∈ K.target), G x = (K.homeomorph.symm ⟨x, hx⟩).val) := by
  let B := normalBundle N
  have hincM : ManifoldSmooth
      (openSubsetAtlas S.smoothStructure.val K.target K.isOpen_target)
      S.smoothStructure.val (Subtype.val : K.target → M) :=
    (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ id K.target K.isOpen_target).mp
      (fun x _ => SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 x)
  have hincB : ManifoldSmooth
      (openSubsetAtlas B.totalManifold.smoothStructure.val K.domain K.isOpen_domain)
      B.totalManifold.smoothStructure.val (Subtype.val : K.domain → NormalTotal N) :=
    (SmoothManifolds.manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ id K.domain K.isOpen_domain).mp
      (fun z _ => SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ B.totalManifold.smoothStructure.property.1 z)
  have hforward : ManifoldSmooth
      (openSubsetAtlas B.totalManifold.smoothStructure.val K.domain K.isOpen_domain)
      S.smoothStructure.val (fun z : K.domain => (K.homeomorph z).val) :=
    fun z => SmoothManifolds.manifoldContDiffAt_comp
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
        S.smoothStructure.property.1 K.target K.isOpen_target).1
      (K.smooth z) (hincM _)
  have hinverse : ManifoldSmooth
      (openSubsetAtlas S.smoothStructure.val K.target K.isOpen_target)
      B.totalManifold.smoothStructure.val (fun x : K.target => (K.homeomorph.symm x).val) :=
    fun x => SmoothManifolds.manifoldContDiffAt_comp
      (SmoothManifolds.openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
        B.totalManifold.smoothStructure.property.1 K.domain K.isOpen_domain).1
      (K.inverse_smooth x) (hincB _)
  obtain ⟨F, heF, hF⟩ := SmoothManifolds.TubularLocalGeometry.totalize_smooth_on
    B.totalManifold.smoothStructure.val S.smoothStructure.val
    K.domain K.isOpen_domain (fun z => (K.homeomorph z).val) (fun z => i z.proj) hforward
  obtain ⟨G, heG, hG⟩ := SmoothManifolds.TubularLocalGeometry.totalize_smooth_on
    S.smoothStructure.val B.totalManifold.smoothStructure.val
    K.target K.isOpen_target (fun x => (K.homeomorph.symm x).val)
    (fun _ => normalZero N p) hinverse
  exact ⟨F, G, hF, hG, fun z hz => heF ⟨z, hz⟩, fun x hx => heG ⟨x, hx⟩⟩

/-- The full derivative of a normalized tubular map, in an original bundle
chart, induces the identity on the quotient normal fiber. Horizontal motion
lies in the image of the inclusion differential and disappears in the quotient. -/
theorem normalCompatible_full_derivative (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (F : NormalTotal N → M)
    (hF : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F K.domain)
    (heF : ∀ z (hz : z ∈ K.domain), F z = (K.homeomorph ⟨z, hz⟩).val)
    (p : P) :
    ∃ (a : P) (hp : p ∈ (normalBundle N).baseSet a)
      (c : ModelChart m .euclidean P) (hc : c ∈ T.smoothStructure.val)
      (hpc : p ∈ c.source)
      (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
      (hip : i p ∈ d.source)
      (J : Euclidean (m + (n-m)) →L[ℝ] Euclidean n),
      SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative
        (bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c)
        (fun z => (d (F z)).val) (normalZero N p) J ∧
      ∀ (x : Euclidean m) (v : Euclidean (n-m)),
        (LinearMap.range (N.differential p)).mkQ
          ((N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip).symm
            (J ((normalBundle N).coordinates.linearEquiv (x, v)))) =
              (fiberLinearCoordinates N a p hp).symm v := by
  let B := normalBundle N
  obtain ⟨a, hp, d, hd, hip, L, hL, hn⟩ := hK p
  obtain ⟨c, hc, hpc⟩ := T.smoothStructure.property.1.1 p
  have hzero : ∀ q : P, F (normalZero N q) = i q := by
    intro q
    exact (heF _ (K.zero_mem q)).trans (K.zero_eq q)
  have hFp : F (normalZero N p) ∈ d.source := by rw [hzero p]; exact hip
  have hAt := SmoothManifolds.TubularLocalGeometry.smoothAt_target_chart _ _ F (normalZero N p)
    (hF _ (K.zero_mem p)) d hd hFp
  have hnear : ∀ᶠ v in 𝓝 (0 : Euclidean (n-m)),
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K.domain := by
    have ht := (continuous_fiberLinearCoordinates_symm N a p hp).continuousAt (x := 0)
    have hz : (⟨p, (fiberLinearCoordinates N a p hp).symm 0⟩ : NormalTotal N) ∈ K.domain := by
      simpa only [map_zero, normalZero] using K.zero_mem p
    exact ht (K.isOpen_domain.mem_nhds hz)
  have hvert : HasFDerivAt
      (fun v => (d (F ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩)).val) L 0 := by
    apply hL.congr_of_eventuallyEq
    filter_upwards [hnear] with v hv
    unfold fiberImage
    rw [dite_eq_left hv]
    exact congrArg (fun y => (d y).val) (heF _ hv)
  obtain ⟨J, hJ, hblocks⟩ := SmoothManifolds.TubularLocalGeometry.bundle_derivative_at_zero B
    (fun z => (d (F z)).val) (fun q => (d (i q)).val) p a hp c hc hpc
    hAt (fun q => congrArg (fun y => (d y).val) (hzero q)) L hvert
  refine ⟨a, hp, c, hc, hpc, d, hd, hip, J, hJ, ?_⟩
  let C := N.sourceTangent.fiberCoordinates.equiv c hc p hpc
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
  have hhorizontal (x : Euclidean m) :
      E.symm (SmoothManifolds.FiniteRegularityData.chartDerivative c d i p x) = N.differential p (C.symm x) := by
    have hj := SmoothManifolds.FiniteRegularity.smooth_jacobian_coordinateDerivative T S i hi.1 p
      (N.differential p) (N.isDifferential p) c d hc hd hpc hip C E
      (N.sourceTangent.fiberCoordinates.isCoordinates c hc p hpc)
      (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip) (C.symm x)
    apply E.injective
    simpa only [LinearEquiv.apply_symm_apply] using hj.symm
  intro x v
  have hj := congrArg (fun A => A (x, v)) hblocks
  change J (B.coordinates.linearEquiv (x, v)) =
    SmoothManifolds.FiniteRegularityData.chartDerivative c d i p x + L v at hj
  rw [hj, map_add, map_add, hhorizontal]
  have hqzero : (LinearMap.range (N.differential p)).mkQ (N.differential p (C.symm x)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
  rw [hqzero, zero_add]
  exact hn v

/-- First-order normalization is independent of the ambient and normal bundle
charts. This keeps the original quotient normal vector fixed while changing
both coordinate systems. -/
theorem normalCompatible_fiber_derivative_in_charts
    (N : NormalBundle T S i) (K : TubularNeighborhood N) (hK : NormalCompatible N K)
    (F : NormalTotal N → M)
    (hF : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F K.domain)
    (heF : ∀ z (hz : z ∈ K.domain), F z = (K.homeomorph ⟨z, hz⟩).val)
    (p a : P) (hp : p ∈ (normalBundle N).baseSet a)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hip : i p ∈ d.source) :
    ∃ L : Euclidean (n-m) →L[ℝ] Euclidean n,
      HasFDerivAt (fun v => (d (F ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩)).val) L 0 ∧
      ∀ v, (LinearMap.range (N.differential p)).mkQ
        ((N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip).symm (L v)) =
          (fiberLinearCoordinates N a p hp).symm v := by
  obtain ⟨a₀, hp₀, d₀, hd₀, hip₀, L₀, hL₀, hn₀⟩ := hK p
  have hzero : F (normalZero N p) = i p :=
    (heF _ (K.zero_mem p)).trans (K.zero_eq p)
  let z : Euclidean (n-m) → NormalTotal N :=
    fun v => ⟨p, (fiberLinearCoordinates N a₀ p hp₀).symm v⟩
  have hzcont : Continuous z := continuous_fiberLinearCoordinates_symm N a₀ p hp₀
  have hz0 : z 0 = normalZero N p := by simp [z, normalZero]
  have hnear : ∀ᶠ v in 𝓝 (0 : Euclidean (n-m)), z v ∈ K.domain := by
    have ht := hzcont.tendsto 0
    rw [hz0] at ht
    exact ht (K.isOpen_domain.mem_nhds (K.zero_mem p))
  have hL₀F : HasFDerivAt (fun v => (d₀ (F (z v))).val) L₀ 0 := by
    apply hL₀.congr_of_eventuallyEq
    filter_upwards [hnear] with v hv
    unfold fiberImage
    rw [dite_eq_left hv]
    exact congrArg (fun y => (d₀ y).val) (heF _ hv)
  have hid : IsSmoothMap S S id :=
    SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1
  let D := SmoothManifolds.FiniteRegularityData.chartDerivative d₀ d id (i p)
  obtain ⟨H, hH, heH⟩ := SmoothManifolds.FiniteRegularity.chartDerivative_exists
    (⊤ : ℕ∞) (by simp) d₀ d id (i p) ((hid (i p)).2 d₀ hd₀ d hd hip₀ hip)
  have hFz : ContinuousAt (fun v => F (z v)) 0 := by
    have ht : ContinuousAt F (z 0) := hz0.symm ▸ (hF _ (K.zero_mem p)).1
    exact ht.comp hzcont.continuousAt
  have hFz0 : F (z 0) = i p := by rw [hz0, hzero]
  have hrep : (fun v => H (d₀ (F (z v))).val) =ᶠ[𝓝 (0 : Euclidean (n-m))]
      (fun v => (d (F (z v))).val) := by
    have ht := hFz.tendsto
    rw [hFz0] at ht
    exact heH.comp_tendsto ht
  have hH' : HasFDerivAt H D (d₀ (F (z 0))).val := by rwa [hFz0]
  have htarget : HasFDerivAt (fun v => (d (F (z v))).val) (D.comp L₀) 0 :=
    (hH'.comp 0 hL₀F).congr_of_eventuallyEq hrep.symm
  let A : Euclidean (n-m) ≃ₗ[ℝ] Euclidean (n-m) :=
    (fiberLinearCoordinates N a p hp).symm.trans (fiberLinearCoordinates N a₀ p hp₀)
  let A' : Euclidean (n-m) ≃L[ℝ] Euclidean (n-m) := A.toContinuousLinearEquiv
  have hzA (v : Euclidean (n-m)) :
      z (A' v) = ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ := by
    change (⟨p, (fiberLinearCoordinates N a₀ p hp₀).symm
      ((fiberLinearCoordinates N a₀ p hp₀) ((fiberLinearCoordinates N a p hp).symm v))⟩ :
      NormalTotal N) = _
    rw [LinearEquiv.symm_apply_apply]
  let L := (D.comp L₀).comp A'.toContinuousLinearMap
  refine ⟨L, ?_, ?_⟩
  · have htargetA : HasFDerivAt (fun v => (d (F (z v))).val) (D.comp L₀) (A' 0) := by
      simpa only [map_zero] using htarget
    have hcomp := htargetA.comp 0 A'.hasFDerivAt
    have heq : (fun v => (d (F (z (A' v)))).val) =
        (fun v => (d (F ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩)).val) :=
      funext (fun v => congrArg (fun w => (d (F w)).val) (hzA v))
    exact heq ▸ hcomp
  · intro v
    let E₀ := N.ambientTangent.fiberCoordinates.equiv d₀ hd₀ (i p) hip₀
    let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
    have hD (w : Euclidean n) : E.symm (D w) = E₀.symm w := by
      have hj := SmoothManifolds.FiniteRegularity.smooth_jacobian_coordinateDerivative S S id hid
        (i p) LinearMap.id (SmoothManifolds.differential_id S (i p))
        d₀ d hd₀ hd hip₀ hip E₀ E
        (N.ambientTangent.fiberCoordinates.isCoordinates d₀ hd₀ (i p) hip₀)
        (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip) (E₀.symm w)
      apply E.injective
      simpa [D, LinearMap.id] using hj.symm
    change (LinearMap.range (N.differential p)).mkQ (E.symm (D (L₀ (A' v)))) = _
    rw [hD, hn₀]
    change (fiberLinearCoordinates N a₀ p hp₀).symm
      ((fiberLinearCoordinates N a₀ p hp₀) ((fiberLinearCoordinates N a p hp).symm v)) = _
    exact LinearEquiv.symm_apply_apply _ _

/-- Coordinate derivatives of actual local inverse germs are inverse linear
maps. The inverse identity is proved from equality of the maps on a neighborhood. -/
theorem coordinate_inverse_derivative
    {k l : ℕ} {a b : SmoothManifolds.ModelKind}
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ModelChart k a X) (d : ModelChart l b Y)
    (F : X → Y) (G : Y → X) (p : X) (q : Y)
    (hq : q ∈ d.source) (hGq : G q = p) (hGc : ContinuousAt G q)
    (hFG : ∀ᶠ y in 𝓝 q, F (G y) = y)
    (J : Euclidean k →L[ℝ] Euclidean l) (I : Euclidean l →L[ℝ] Euclidean k)
    (hJ : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative e
      (fun x => (d (F x)).val) p J)
    (hI : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative d
      (fun y => (e (G y)).val) q I) :
    J.comp I = ContinuousLinearMap.id ℝ (Euclidean l) := by
  obtain ⟨A, hA, heA⟩ := hJ
  obtain ⟨B, hB, heB⟩ := hI
  have hbase : B (d q).val = (e p).val := by
    simpa only [hGq] using heB.eq_of_nhds
  have hGc' : Tendsto G (𝓝 q) (𝓝 p) := by
    simpa only [hGq] using hGc.tendsto
  have hcomp : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative d
      (fun y => (d y).val) q (J.comp I) := by
    refine ⟨A ∘ B, (hbase.symm ▸ hA).comp (d q).val hB, ?_⟩
    filter_upwards [heB, heA.comp_tendsto hGc', hFG] with y hyB hyA hyFG
    change A (e (G y)).val = (d (F (G y))).val at hyA
    change A (B (d y).val) = (d y).val
    rw [hyB, hyA, hyFG]
  exact SmoothManifolds.FiniteRegularity.extension_independence d _ q hq _ _ hcomp
    ⟨id, hasFDerivAt_id _, Eventually.of_forall (fun _ => rfl)⟩

/-- A normalized full derivative and its actual inverse leave the normal
component of any other normalized vertical derivative unchanged. The base
component can be arbitrary. -/
theorem normal_transition_linear_identity
    {B E A C Q : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [AddCommGroup Q] [Module ℝ Q]
    (coord : (B × E) ≃L[ℝ] A) (quot : C →ₗ[ℝ] Q) (fiber : Q ≃ₗ[ℝ] E)
    (J : A →L[ℝ] C) (I : C →L[ℝ] A) (L : E →L[ℝ] C)
    (hJI : J.comp I = ContinuousLinearMap.id ℝ C)
    (hJ : ∀ x v, quot (J (coord (x, v))) = fiber.symm v)
    (hL : ∀ v, quot (L v) = fiber.symm v) :
    (ContinuousLinearMap.snd ℝ B E).comp
      (coord.symm.toContinuousLinearMap.comp (I.comp L)) = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  change (coord.symm (I (L v))).2 = v
  apply fiber.symm.injective
  have hh := hJ (coord.symm (I (L v))).1 (coord.symm (I (L v))).2
  rw [Prod.eta, coord.apply_symm_apply] at hh
  have hi : J (I (L v)) = L v := by
    have he := congrArg (fun A => A (L v)) hJI
    exact he
  rw [hi, hL] at hh
  exact hh.symm
/-- The moving-base transition homotopy stays in any prescribed open target
neighborhood after shrinking its source. Compactness of the interval supplies
a single radius valid for the entire homotopy. -/
theorem exists_pairHomotopy_moving_base_in_open
    {B E : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → B × E} {U : Set E} {W : Set (B × E)} {b : B}
    (hU : IsOpen U) (h0U : 0 ∈ U) (hfc : ContinuousOn f U)
    (hW : IsOpen W) (hbW : (b, 0) ∈ W)
    (hbase : (f 0).1 = b) (hnormal : (f 0).2 = 0)
    (hf : HasFDerivAt (fun x => (f x).2) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (ε : ℝ) (_ : 0 < ε)
      (j g : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
        openPair (secondPuncturedPair B E) W),
      {x : E | norm x < ε} ⊆ U ∧
      (∀ x, (j.map x).val = (b, x.val)) ∧
      (∀ x, (g.map x).val = f x.val) ∧
      Nonempty (P202Specs.PrismHomotopy.PairHomotopy j g) := by
  obtain ⟨ε₁, hε₁, hnonzero⟩ := exists_pos_nonvanishing_linear_homotopy hnormal hf
  let H : unitInterval × U → B × E := fun tx =>
    (b + tx.1.val • ((f tx.2.val).1 - b), tx.2.val + tx.1.val • ((f tx.2.val).2 - tx.2.val))
  have hfU : Continuous (fun x : U => f x.val) :=
    hfc.comp_continuous continuous_subtype_val (fun x => x.property)
  have hH : Continuous H := by
    exact (continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
      ((hfU.fst.comp continuous_snd).sub continuous_const))).prodMk
      ((continuous_subtype_val.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).smul
          ((hfU.snd.comp continuous_snd).sub (continuous_subtype_val.comp continuous_snd))))
  let Good : Set U := {x | ∀ t : unitInterval, H (t, x) ∈ W}
  have hGood : IsOpen Good := by
    have hbad : IsClosed (Prod.snd '' (H ⁻¹' Wᶜ)) :=
      isClosedMap_snd_of_compactSpace _ (hW.isClosed_compl.preimage hH)
    have he : Good = (Prod.snd '' (H ⁻¹' Wᶜ))ᶜ := by
      ext x
      constructor
      · intro hx hb
        obtain ⟨⟨t, y⟩, hy, hyx⟩ := hb
        change y = x at hyx
        subst y
        exact hy (hx t)
      · intro hx t
        by_contra ht
        exact hx ⟨(t, x), ht, rfl⟩
    rw [he]
    exact hbad.isOpen_compl
  have h0Good : (⟨0, h0U⟩ : U) ∈ Good := by
    intro t
    simpa only [H, hbase, hnormal, sub_self, smul_zero, add_zero] using hbW
  have hGoodE : IsOpen (Subtype.val '' Good : Set E) :=
    hU.isOpenMap_subtype_val Good hGood
  have h0GoodE : (0 : E) ∈ Subtype.val '' Good := ⟨⟨0, h0U⟩, h0Good, rfl⟩
  obtain ⟨ε₂, hε₂, hsmall₂⟩ := Metric.mem_nhds_iff.mp (hGoodE.mem_nhds h0GoodE)
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsmall : ∀ x : E, norm x < ε → x ∈ U ∧
      ∀ t : unitInterval,
        (b + t.val • ((f x).1 - b), x + t.val • ((f x).2 - x)) ∈ W := by
    intro x hx
    have hxE : x ∈ Subtype.val '' Good := hsmall₂ (by
      change dist x 0 < ε₂
      simpa only [dist_zero_right] using lt_of_lt_of_le hx (min_le_right ε₁ ε₂))
    obtain ⟨y, hy, hyx⟩ := hxE
    subst x
    exact ⟨y.property, hy⟩
  have hn : ∀ x : E, norm x < ε → x ≠ 0 →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • ((f x).2 - x) ≠ 0 := by
    intro x hx
    exact hnonzero x (lt_of_lt_of_le hx (min_le_left ε₁ ε₂))
  have hcont : Continuous (fun x : {x : E // norm x < ε} => f x.val) :=
    hfc.comp_continuous continuous_subtype_val (fun x => (hsmall x x.property).1)
  have hjW (x : {x : E // norm x < ε}) : (b, x.val) ∈ W := by
    simpa using (hsmall x x.property).2 0
  have hgW (x : {x : E // norm x < ε}) : f x.val ∈ W := by
    simpa using (hsmall x x.property).2 1
  let j : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
      openPair (secondPuncturedPair B E) W := {
    map := TopCat.ofHom ⟨fun x => ⟨(b, x.val), hjW x⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
    mapsTo := by intro x hx; exact hx }
  let g : openPair (puncturedVectorPair E) {x : E | norm x < ε} ⟶
      openPair (secondPuncturedPair B E) W := {
    map := TopCat.ofHom ⟨fun x => ⟨f x.val, hgW x⟩, hcont.subtype_mk _⟩
    mapsTo := by
      intro x hx
      have hh := hn x.val x.property hx 1 (by simp)
      change (f x.val).2 ≠ 0
      simpa only [one_smul, add_sub_cancel] using hh }
  let Hsmall : unitInterval × {x : E // norm x < ε} → W := fun tx =>
    ⟨(b + tx.1.val • ((f tx.2.val).1 - b),
      tx.2.val + tx.1.val • ((f tx.2.val).2 - tx.2.val)), (hsmall tx.2 tx.2.property).2 tx.1⟩
  have hHsmall : Continuous Hsmall := by
    exact ((continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
      ((hcont.fst.comp continuous_snd).sub continuous_const))).prodMk
      ((continuous_subtype_val.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).smul
          ((hcont.snd.comp continuous_snd).sub (continuous_subtype_val.comp continuous_snd))))).subtype_mk _
  refine ⟨ε, hε, j, g, fun x hx => (hsmall x hx).1, fun _ => rfl, fun _ => rfl, ⟨?_⟩⟩
  refine {
    homotopy := {
      toFun := Hsmall
      continuous_toFun := hHsmall
      map_zero_left := by
        intro x
        apply Subtype.ext
        change (b + (0 : ℝ) • ((f x.val).1 - b),
          x.val + (0 : ℝ) • ((f x.val).2 - x.val)) = (b, x.val)
        simp
      map_one_left := by
        intro x
        apply Subtype.ext
        change (b + (1 : ℝ) • ((f x.val).1 - b),
          x.val + (1 : ℝ) • ((f x.val).2 - x.val)) = f x.val
        simp }
    preserves := ?_ }
  intro t x
  exact hn x.val.val x.val.property x.property t.val t.property

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped TensorProduct Simplicial
open P202Specs.AlexanderWhitney P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.ThomClass P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R]

theorem secondProduct_model_cohomology_below (X : TopCat.{v}) (n : ℕ)
    (A : Type w) [AddCommGroup A] [Module R A] (q : ℤ) (hq : q < ((n+1 : ℕ) : ℤ)) :
    IsZero (relativeCohomology R A (secondProductPair X (modelPair.{v} (n+1))) q) := by
  obtain ⟨eF⟩ := modelNonnegativeHomotopyEquiv R n
  obtain ⟨eX⟩ := secondProduct_tensor_homotopy R X (modelPair.{v} (n+1))
    (rankSingle R (n+1)) eF.symm
  let d := P202.CohomologyExcisionMV.dualHomotopyEquiv R A eX
  haveI := d.quasiIso_hom
  haveI : IsIso (homologyMap d.hom q) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  apply (asIso (homologyMap d.hom q)).isZero_iff.mp
  exact nonnegative_dual_cohomology_below_isZero R A
    (totalTensorComplex R (complex R R X) (rankSingle R (n+1))) (n+1)
    (totalTensorSingle_below_isZero R (complex R R X) (n+1)) q hq


def secondProductFiberInclusion (X : TopCat.{v}) (B : Pair.{v}) (x : X) :
    B ⟶ secondProductPair X B where
  map := TopCat.ofHom ⟨fun b => (x,b), continuous_const.prodMk continuous_id⟩
  mapsTo := fun _ hb => hb

def secondProductProjection (X : TopCat.{v}) (B : Pair.{v}) :
    secondProductPair X B ⟶ B where
  map := secondProjection X B.space
  mapsTo := fun _ hb => hb

lemma secondProductFiberInclusion_projection (X : TopCat.{v}) (B : Pair.{v}) (x : X) :
    secondProductFiberInclusion X B x ≫ secondProductProjection X B = 𝟙 B := by
  apply PairMap.ext
  apply TopCat.ext
  intro b
  rfl

def secondProductPointIso (B : Pair.{v}) : B ≅ secondProductPair pointPair.{v}.space B where
  hom := secondProductFiberInclusion pointPair.space B PUnit.unit
  inv := { map := secondProjection pointPair.space B.space, mapsTo := fun _ hb => hb }
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.ext
    intro x
    rfl
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.ext
    intro x
    apply Prod.ext
    · change (PUnit.unit : PUnit.{v+1}) = x.1
      exact Subsingleton.elim _ _
    · rfl

lemma secondProductFiberInclusion_factor (X : TopCat.{v}) (B : Pair.{v}) (x : X) :
    (secondProductPointIso B).hom ≫ secondProductFirstMap (pointMapToSpace X x) B =
      secondProductFiberInclusion X B x := rfl

lemma secondProduct_point_pullback_zero_of_fiber
    (X : TopCat.{v}) (B : Pair.{v}) (q : ℤ) (A : Type w) [AddCommGroup A] [Module R A]
    (c : relativeCohomology R A (secondProductPair X B) q) (x : X)
    (hc : (relativeCohomologyFunctor R A q).map (secondProductFiberInclusion X B x).op c = 0) :
    (relativeCohomologyFunctor R A q).map
      (secondProductFirstMap (pointMapToSpace X x) B).op c = 0 := by
  let F := relativeCohomologyFunctor R A q
  haveI : IsIso (F.map (secondProductPointIso B).hom.op) := by infer_instance
  apply (ConcreteCategory.bijective_of_isIso (F.map (secondProductPointIso B).hom.op)).injective
  change (F.map (secondProductFirstMap (pointMapToSpace X x) B).op ≫
    F.map (secondProductPointIso B).hom.op) c = _
  rw [← F.map_comp, ← op_comp, secondProductFiberInclusion_factor]
  change F.map (secondProductFiberInclusion X B x).op c = 0 at hc
  simpa only [map_zero] using hc

def secondProductTensorIntegerMap (X : TopCat.{v}) (B : Pair.{v})
    {L : Chain.{u,v} R} (g : nonnegative R R B ⟶ L) :
    ordinary R R (secondProductPair X B) ⟶
      (totalTensorComplex R (complex R R X) L).extend (degreeEmbedding 0) :=
  (P202.CohomologyExcisionMV.relativeExtensionIso R (secondProductPair X B)).inv ≫
    extendMap (secondProductTensorMap R X B g) (degreeEmbedding 0)

lemma relativeExtensionIso_inv_natural {B C : Pair.{v}} (f : B ⟶ C) :
    relativeMap (ordinaryFunctor R R) f ≫ (P202.CohomologyExcisionMV.relativeExtensionIso R C).inv =
      (P202.CohomologyExcisionMV.relativeExtensionIso R B).inv ≫
        extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0) := by
  rw [← cancel_mono (P202.CohomologyExcisionMV.relativeExtensionIso R C).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← P202.CohomologyExcisionMV.relativeExtensionIso_natural, Iso.inv_hom_id_assoc]

lemma secondProductTensorIntegerMap_natural {X Y : TopCat.{v}}
    (f : X ⟶ Y) (B : Pair.{v}) {L : Chain.{u,v} R} (g : nonnegative R R B ⟶ L) :
    relativeMap (ordinaryFunctor R R) (secondProductFirstMap f B) ≫
      secondProductTensorIntegerMap R Y B g =
        secondProductTensorIntegerMap R X B g ≫
          extendMap (totalTensorMap R (chainMap R R f) (𝟙 L)) (degreeEmbedding 0) := by
  simp only [secondProductTensorIntegerMap]
  rw [← Category.assoc, relativeExtensionIso_inv_natural, Category.assoc,
    ← extendMap_comp, secondProductTensorMap_natural, extendMap_comp, Category.assoc]


lemma secondProductTensorIntegerMap_dual_isIso (X : TopCat.{v}) (B : Pair.{v})
    {L : Chain.{u,v} R} (e : HomotopyEquiv (nonnegative R R B) L)
    (A : Type w) [AddCommGroup A] [Module R A] (q : ℤ) :
    IsIso (homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (secondProductTensorIntegerMap R X B e.hom).op) q) := by
  obtain ⟨h, hh⟩ := secondProductTensorMap_homotopy R X B e
  let dh := P202.CohomologyExcisionMV.dualHomotopyEquiv R A h
  have hd : dh.hom = (dualComplexFunctor R A (.down ℤ)).map
      (secondProductTensorIntegerMap R X B e.hom).op := by
    change (dualComplexFunctor R A (.down ℤ)).map h.hom.op = _
    rw [hh]
    rfl
  haveI : QuasiIso ((dualComplexFunctor R A (.down ℤ)).map
      (secondProductTensorIntegerMap R X B e.hom).op) := by
    rw [← hd]
    exact dh.quasiIso_hom
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance

lemma secondProductTensorIntegerMap_dual_natural {X Y : TopCat.{v}}
    (f : X ⟶ Y) (B : Pair.{v}) {L : Chain.{u,v} R} (g : nonnegative R R B ⟶ L)
    (A : Type w) [AddCommGroup A] [Module R A] (q : ℤ) :
    homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (secondProductTensorIntegerMap R Y B g).op) q ≫
      (relativeCohomologyFunctor R A q).map (secondProductFirstMap f B).op =
    homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (extendMap (totalTensorMap R (chainMap R R f) (𝟙 L)) (degreeEmbedding 0)).op) q ≫
      homologyMap ((dualComplexFunctor R A (.down ℤ)).map
        (secondProductTensorIntegerMap R X B g).op) q := by
  change homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (secondProductTensorIntegerMap R Y B g).op) q ≫
    homologyMap ((dualComplexFunctor R A (.down ℤ)).map
      (relativeMap (ordinaryFunctor R R) (secondProductFirstMap f B)).op) q = _
  rw [← homologyMap_comp, ← homologyMap_comp]
  change homologyMap ((dualComplexFunctor R A (.down ℤ)).map _ ≫
    (dualComplexFunctor R A (.down ℤ)).map _) q =
      homologyMap ((dualComplexFunctor R A (.down ℤ)).map _ ≫
        (dualComplexFunctor R A (.down ℤ)).map _) q
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    secondProductTensorIntegerMap_natural]

/-- In the actual product pair, all fiber pullbacks detect the complete
bottom relative cohomology class. The base is arbitrary and may be empty. -/
theorem secondProduct_model_cohomology_zero_of_fibers
    (X : TopCat.{v}) (n : ℕ) (A : Type w) [AddCommGroup A] [Module R A]
    (c : relativeCohomology R A (secondProductPair X (modelPair.{v} (n+1))) ((n+1 : ℕ) : ℤ))
    (hc : ∀ x : X, (relativeCohomologyFunctor R A ((n+1 : ℕ) : ℤ)).map
      (secondProductFiberInclusion X (modelPair.{v} (n+1)) x).op c = 0) : c = 0 := by
  obtain ⟨eF⟩ := modelNonnegativeHomotopyEquiv R n
  let B := modelPair.{v} (n+1)
  let e : HomotopyEquiv (nonnegative R R B) (rankSingle R (n+1)) := eF.symm
  let T := fun Y : TopCat.{v} => homologyMap ((dualComplexFunctor R A (.down ℤ)).map
    (secondProductTensorIntegerMap R Y B e.hom).op) ((n+1 : ℕ) : ℤ)
  haveI : IsIso (T X) := secondProductTensorIntegerMap_dual_isIso R X B e A _
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (T X)).surjective c
  have ha : a = 0 := by
    apply totalTensorSingle_cohomology_zero_of_points R X (n+1) A
    intro x
    have hn := secondProductTensorIntegerMap_dual_natural R (pointMapToSpace X x) B e.hom A ((n+1 : ℕ) : ℤ)
    have he := congrArg (fun k => k a) hn
    change (relativeCohomologyFunctor R A ((n+1 : ℕ) : ℤ)).map
        (secondProductFirstMap (pointMapToSpace X x) B).op (T X a) =
      T pointPair.{v}.space
        (homologyMap ((dualComplexFunctor R A (.down ℤ)).map
          (extendMap (totalTensorMap R (chainMap R R (pointMapToSpace X x))
            (𝟙 (rankSingle R (n+1)))) (degreeEmbedding 0)).op) ((n+1 : ℕ) : ℤ) a) at he
    have hx := secondProduct_point_pullback_zero_of_fiber R X B ((n+1 : ℕ) : ℤ) A (T X a) x (hc x)
    rw [hx] at he
    haveI : IsIso (T pointPair.{v}.space) :=
      secondProductTensorIntegerMap_dual_isIso R pointPair.space B e A _
    apply (ConcreteCategory.bijective_of_isIso (T pointPair.{v}.space)).injective
    rw [map_zero]
    exact he.symm
  rw [ha, map_zero]

theorem secondProduct_model_cohomology_ext
    (X : TopCat.{v}) (n : ℕ) (A : Type w) [AddCommGroup A] [Module R A]
    (c e : relativeCohomology R A (secondProductPair X (modelPair.{v} (n+1))) ((n+1 : ℕ) : ℤ))
    (h : ∀ x : X, (relativeCohomologyFunctor R A ((n+1 : ℕ) : ℤ)).map
      (secondProductFiberInclusion X (modelPair.{v} (n+1)) x).op c =
      (relativeCohomologyFunctor R A ((n+1 : ℕ) : ℤ)).map
        (secondProductFiberInclusion X (modelPair.{v} (n+1)) x).op e) : c = e := by
  apply sub_eq_zero.mp
  apply secondProduct_model_cohomology_zero_of_fibers R X n A (c-e)
  intro x
  rw [map_sub, h x, sub_self]

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.ThomClass
open scoped TensorProduct Simplicial
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
open P202Specs.AlexanderWhitney
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

lemma normalChart_projection_fiber (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) (p : P) (hp : p ∈ U) :
    fiberToNormalOver N U p hp ≫ (normalChartPairIso N a U hU).hom ≫
        secondProductProjection (TopCat.of U) (modelPair.{u} (n-m)) =
      fiberCoordinates N a p (hU hp) := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

lemma normalChart_fiber_factor (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) (p : P) (hp : p ∈ U) :
    fiberToNormalOver N U p hp ≫ (normalChartPairIso N a U hU).hom =
      fiberCoordinates N a p (hU hp) ≫
        secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩ := by
  apply PairMap.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change (((normalBundle N).trivialization a) z.val).1 = p
    exact (((normalBundle N).trivialization a).proj_toFun z.val (by
      rw [Bundle.Trivialization.mem_source, (normalBundle N).trivialization_baseSet]
      exact z.property.symm ▸ hU hp)).trans z.property
  · rfl

lemma normalChart_inv_fiber_factor (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) (p : P) (hp : p ∈ U) :
    fiberCoordinates N a p (hU hp) ≫
        secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩ ≫
          (normalChartPairIso N a U hU).inv = fiberToNormalOver N U p hp := by
  rw [← Category.assoc, ← normalChart_fiber_factor N a U hU p hp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end P202.ThomClass
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology
variable (R : Type v) [CommRing R]

lemma normalChart_fiberRestriction (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) (p : P) (hp : p ∈ U) (q : ℤ)
    (c : relativeCohomology R R (normalOverPair N U) q) :
    (relativeCohomologyFunctor R R q).map (fiberCoordinates N a p (hU hp)).op
      ((relativeCohomologyFunctor R R q).map
        (secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩).op
        ((relativeCohomologyFunctor R R q).map (normalChartPairIso N a U hU).inv.op c)) =
      (relativeCohomologyFunctor R R q).map (fiberToNormalOver N U p hp).op c := by
  let F := relativeCohomologyFunctor R R q
  change (F.map (normalChartPairIso N a U hU).inv.op ≫
    F.map (secondProductFiberInclusion (TopCat.of U) (modelPair.{u} (n-m)) ⟨p,hp⟩).op ≫
      F.map (fiberCoordinates N a p (hU hp)).op) c = _
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  rw [Category.assoc, normalChart_inv_fiber_factor]

/-- On every open subregion of one original normal chart, a fixed model
class gives the unique Thom class with its prescribed fiber values. -/
theorem normalThomOn_of_chart (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m = d) (hpos : 0 < d)
    (g : ∀ p : P, relativeCohomology R R (fiberPair N p) (d : ℤ))
    (a : P) (U : Set P) (hU : U ⊆ (normalBundle N).baseSet a)
    (cModel : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ))
    (hg : ∀ (p : P) (hp : p ∈ U),
      (relativeCohomologyFunctor R R (d : ℤ)).map (fiberCoordinates N a p (hU hp)).op cModel = g p) :
    NormalThomOn R N d g U := by
  cases d with
  | zero => omega
  | succ k =>
    intro W hW hWU
    let hWa : W ⊆ (normalBundle N).baseSet a := hWU.trans hU
    let E := normalChartPairIso N a W hWa
    let F := relativeCohomologyFunctor R R ((k+1 : ℕ) : ℤ)
    have hv (q : ℤ) (hq : q < ((k+1 : ℕ) : ℤ)) :
        IsZero (relativeCohomology R R (normalOverPair N W) q) := by
      have hp : IsZero (relativeCohomology R R
          (secondProductPair (TopCat.of W) (modelPair.{u} (n-m))) q) := by
        rw [hd]
        exact secondProduct_model_cohomology_below R (TopCat.of W) k R q hq
      exact hp.of_iso (asIso ((relativeCohomologyFunctor R R q).map E.hom.op)).symm
    let c : relativeCohomology R R (normalOverPair N W) ((k+1 : ℕ) : ℤ) :=
      F.map (E.hom ≫ secondProductProjection (TopCat.of W) (modelPair.{u} (n-m))).op cModel
    have hc : NormalHasValues R N W (k+1) g c := by
      intro p hp
      change (F.map (E.hom ≫ secondProductProjection (TopCat.of W) (modelPair.{u} (n-m))).op ≫
        F.map (fiberToNormalOver N W p hp).op) cModel = g p
      rw [← F.map_comp, ← op_comp, normalChart_projection_fiber]
      exact hg p (hWU hp)
    refine ⟨hv, c, hc, ?_⟩
    intro b hb
    apply (ModuleCat.mono_iff_injective (F.map E.inv.op)).mp inferInstance
    have hprodext : ∀ b e : relativeCohomology R R
        (secondProductPair (TopCat.of W) (modelPair.{u} (n-m))) ((k+1 : ℕ) : ℤ),
        (∀ x : W, F.map (secondProductFiberInclusion (TopCat.of W)
          (modelPair.{u} (n-m)) x).op b =
          F.map (secondProductFiberInclusion (TopCat.of W) (modelPair.{u} (n-m)) x).op e) → b = e := by
      rw [hd]
      exact secondProduct_model_cohomology_ext R (TopCat.of W) k R
    apply hprodext
    intro x
    haveI : IsIso (F.map (fiberCoordinates N a x.val (hWa x.property)).op) := by
      change IsIso (F.map (fiberCoordinatesIso N a x.val (hWa x.property)).hom.op)
      infer_instance
    apply (ModuleCat.mono_iff_injective
      (F.map (fiberCoordinates N a x.val (hWa x.property)).op)).mp inferInstance
    rw [normalChart_fiberRestriction, normalChart_fiberRestriction]
    exact (hb x.val x.property).trans (hc x.val x.property).symm

theorem orientation_normalThomOn_locally (N : NormalBundle T S i) (d : ℕ)
    (hd : n-m = d) (hpos : 0 < d) (o : Orientation R N d) :
    ∀ p : P, ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ NormalThomOn R N d o.generator U := by
  intro p
  obtain ⟨a,U,hU,hp,hUa,c,hc⟩ := o.locally_constant p
  exact ⟨U,hU,hp,normalThomOn_of_chart R N d hd hpos o.generator a U hUa c hc⟩

/-- The specified orientation determines an actual unique class on the full
normal bundle. Compactness is used only by the proved finite-cover gluing. -/
theorem normalClass_exists_unique_of_orientation [CompactSpace P]
    (N : NormalBundle T S i) (d : ℕ) (hd : n-m = d) (hpos : 0 < d)
    (o : Orientation R N d) :
    ∃! c : relativeCohomology R R (normalPair N) (d : ℤ),
      ∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op c = o.generator p :=
  normalClass_exists_unique_of_locally R N d o.generator
    (orientation_normalThomOn_locally R N d hd hpos o)

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology
variable (R : Type v) [CommRing R]

/-- The positive-rank Thom class is uniquely specified on any one prescribed
tubular normal slice system, through the actual normal-bundle/excision map. -/
theorem exists_unique_on_fixed_tube_positive [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i)
    (d : ℕ) (hd : n-m = d) (hpos : 0 < d) (o : Orientation R N d)
    (K : TubularNeighborhood N) :
    ∃! c : relativeCohomology R R (ambientPair i) (d : ℤ),
      ∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToAmbient N K p).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToFiber N K p).op (o.generator p) := by
  obtain ⟨a,ha,hu⟩ := normalClass_exists_unique_of_orientation R N d hd hpos o
  let e := ambientNormalCohomologyEquiv hi N K R (d : ℤ)
  refine ⟨e.symm a, ?_, ?_⟩
  · apply (normal_fiber_values_iff_slice hi N K R d o (e.symm a)).mpr
    change ∀ p, (relativeCohomologyFunctor R R (d : ℤ)).map (fiberToNormal N p).op
      (e (e.symm a)) = o.generator p
    rw [e.apply_symm_apply]
    exact ha
  · intro b hb
    apply e.injective
    rw [e.apply_symm_apply]
    apply hu
    exact (normal_fiber_values_iff_slice hi N K R d o b).mp hb

/-- Intrinsic fiber values determine at most one ambient relative class.
The rank condition is required only at existing points of the submanifold. -/
theorem fiber_values_unique [CompactSpace P]
    (hi : IsSmoothEmbedding T S i) (N : NormalBundle T S i) (d : ℕ)
    (hrank : ∀ _ : P, d = n-m) (o : Orientation R N d)
    (c e : relativeCohomology R R (ambientPair i) (d : ℤ))
    (hc : HasFiberValues R o c) (he : HasFiberValues R o e) : c = e := by
  cases isEmpty_or_nonempty P with
  | inl hP =>
    letI := hP
    obtain ⟨_,a,ha,hu⟩ := exists_unique_of_isEmpty R d hi N o
    exact (hu c hc).trans (hu e he).symm
  | inr hP =>
    have hd : n-m = d := (hrank (Classical.choice hP)).symm
    cases d with
    | zero => exact fiber_values_unique_rank_zero R hi N hd o c e hc he
    | succ k =>
      obtain ⟨K,hK⟩ := normalized_tubular_exists hi N
      obtain ⟨a,ha,hu⟩ := exists_unique_on_fixed_tube_positive R hi N (k+1) hd (by omega) o K
      exact (hu c (hc K hK)).trans (hu e (he K hK)).symm

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology
/-- Product coordinates of a tubular transition, including its moving base. -/
def tubularTransitionCoordinates (N : NormalBundle T S i)
    (F : NormalTotal N → M) (G : M → NormalTotal N)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart m .euclidean P) (v : Euclidean (n-m)) :
    Euclidean m × Euclidean (n-m) :=
  (normalBundle N).coordinates.linearEquiv.symm
    ((bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c)
      (G (F ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩))).val

set_option maxHeartbeats 400000 in
/-- The normal component of the actual transition from one normalized tubular
map to another is tangent to the identity. The full transition is permitted to
move its base point. -/
theorem normalCompatible_transition_derivative
    (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N)
    (hK₁ : NormalCompatible N K₁) (hK₂ : NormalCompatible N K₂)
    (F₁ F₂ : NormalTotal N → M) (G₁ : M → NormalTotal N)
    (hF₁ : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F₁ K₁.domain)
    (hF₂ : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F₂ K₂.domain)
    (hG₁ : ManifoldSmoothOn S.smoothStructure.val
      (normalBundle N).totalManifold.smoothStructure.val G₁ K₁.target)
    (heF₁ : ∀ z (hz : z ∈ K₁.domain), F₁ z = (K₁.homeomorph ⟨z, hz⟩).val)
    (heF₂ : ∀ z (hz : z ∈ K₂.domain), F₂ z = (K₂.homeomorph ⟨z, hz⟩).val)
    (heG₁ : ∀ x (hx : x ∈ K₁.target), G₁ x = (K₁.homeomorph.symm ⟨x, hx⟩).val)
    (p : P) :
    ∃ (a : P) (hp : p ∈ (normalBundle N).baseSet a)
      (c : ModelChart m .euclidean P) (hc : c ∈ T.smoothStructure.val)
      (hpc : p ∈ c.source),
      HasFDerivAt (fun v : Euclidean (n-m) =>
        (tubularTransitionCoordinates N F₂ G₁ a p hp c v).2)
          (ContinuousLinearMap.id ℝ (Euclidean (n-m))) 0 := by
  let B := normalBundle N
  obtain ⟨a, hp, c, hc, hpc, d, hd, hip, J, hJ, hnormJ⟩ :=
    normalCompatible_full_derivative (T := T) (S := S) (i := i) hi N K₁ hK₁ F₁ hF₁ heF₁ p
  let b := bundleChart B.coordinates (B.trivialization a) c
  have hb : b ∈ B.totalManifold.smoothStructure.val := B.chart_mem a c hc
  have hpbase : p ∈ (B.trivialization a).baseSet :=
    (B.trivialization_baseSet a).symm ▸ hp
  have hzb : normalZero N p ∈ b.source :=
    (SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mpr ⟨hpbase, hpc⟩
  have hiK : i p ∈ K₁.target := K₁.inclusion_mem ⟨p, rfl⟩
  have hGzero : G₁ (i p) = normalZero N p := by
    rw [heG₁ _ hiK]
    have he : (⟨i p, hiK⟩ : K₁.target) =
        K₁.homeomorph ⟨normalZero N p, K₁.zero_mem p⟩ :=
      Subtype.ext (K₁.zero_eq p).symm
    rw [he, K₁.homeomorph.symm_apply_apply]
  have hGc := (hG₁ _ hiK).1
  have hbG : G₁ (i p) ∈ b.source := hGzero.symm ▸ hzb
  let I := SmoothManifolds.FiniteRegularityData.chartDerivative d b G₁ (i p)
  have hI : SmoothManifolds.FiniteRegularityData.HasCoordinateDerivative d
      (fun x => (b (G₁ x)).val) (i p) I :=
    SmoothManifolds.FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp)
      d b G₁ (i p) ((hG₁ _ hiK).2 d hd b hb hip hbG)
  have hFG : ∀ᶠ x in 𝓝 (i p), F₁ (G₁ x) = x := by
    filter_upwards [K₁.isOpen_target.mem_nhds hiK] with x hx
    rw [heG₁ x hx, heF₁ _ (K₁.homeomorph.symm ⟨x, hx⟩).property]
    exact congrArg Subtype.val (K₁.homeomorph.apply_symm_apply ⟨x, hx⟩)
  have hJI : J.comp I = ContinuousLinearMap.id ℝ (Euclidean n) :=
    coordinate_inverse_derivative b d F₁ G₁ (normalZero N p) (i p)
      hip hGzero hGc hFG J I hJ hI
  obtain ⟨L, hL, hnormL⟩ := normalCompatible_fiber_derivative_in_charts
    N K₂ hK₂ F₂ hF₂ heF₂ p a hp d hd hip
  let z : Euclidean (n-m) → NormalTotal N :=
    fun v => ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩
  have hz0 : z 0 = normalZero N p := by simp [z, normalZero]
  have hF₂zero : F₂ (z 0) = i p := by
    rw [hz0, heF₂ _ (K₂.zero_mem p), K₂.zero_eq]
  have hF₂c : ContinuousAt (fun v => F₂ (z v)) 0 := by
    have ht : ContinuousAt F₂ (z 0) := hz0.symm ▸ (hF₂ _ (K₂.zero_mem p)).1
    exact ht.comp (continuous_fiberLinearCoordinates_symm N a p hp).continuousAt
  obtain ⟨A, hA, heA⟩ := hI
  have hA' : HasFDerivAt A I (d (F₂ (z 0))).val := by rwa [hF₂zero]
  have hcompose : HasFDerivAt (fun v => (b (G₁ (F₂ (z v)))).val) (I.comp L) 0 := by
    apply (hA'.comp 0 hL).congr_of_eventuallyEq
    have ht := hF₂c.tendsto
    rw [hF₂zero] at ht
    exact (heA.comp_tendsto ht).symm
  have hprod : HasFDerivAt
      (fun v => B.coordinates.linearEquiv.symm (b (G₁ (F₂ (z v)))).val)
      (B.coordinates.linearEquiv.symm.toContinuousLinearMap.comp (I.comp L)) 0 :=
    B.coordinates.linearEquiv.symm.hasFDerivAt.comp 0 hcompose
  have hnormal : (ContinuousLinearMap.snd ℝ (Euclidean m) (Euclidean (n-m))).comp
      (B.coordinates.linearEquiv.symm.toContinuousLinearMap.comp (I.comp L)) =
        ContinuousLinearMap.id ℝ (Euclidean (n-m)) := by
    apply ContinuousLinearMap.ext
    intro v
    change (B.coordinates.linearEquiv.symm (I (L v))).2 = v
    apply (fiberLinearCoordinates N a p hp).symm.injective
    have hh := hnormJ (B.coordinates.linearEquiv.symm (I (L v))).1
      (B.coordinates.linearEquiv.symm (I (L v))).2
    rw [Prod.eta, B.coordinates.linearEquiv.apply_symm_apply] at hh
    have hi : J (I (L v)) = L v := by
      exact congrArg (fun A => A (L v)) hJI
    rw [hi, hnormL] at hh
    exact hh.symm
  refine ⟨a, hp, c, hc, hpc, ?_⟩
  have hh := hprod.snd
  rw [hnormal] at hh
  exact hh


end P202.ThomClass



noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

def fiberBallPair (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) : Pair.{u} :=
  openPair (fiberPair N p) {z | norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε}

def fiberBallInclusion (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) :
    fiberBallPair N a p hp ε ⟶ fiberPair N p :=
  openPairInclusion _ _

theorem fiberBallInclusion_isIso (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) (hε : 0 < ε)
    (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (fiberBallInclusion N a p hp ε).op) := by
  letI := (normalBundle N).totalManifold.topologicalManifold.hausdorff
  apply openPairInclusion_isIso
  · change IsOpen ({fiberOrigin N p}ᶜ : Set (Fiber N p))
    exact isClosed_singleton.isOpen_compl
  · apply isOpen_lt _ continuous_const
    exact (continuous_uliftDown.comp (P202Specs.ThomClass.fiberChart N a p hp).continuous).norm
  · intro z hz
    have he : z = fiberOrigin N p := Classical.not_not.mp hz
    change norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε
    rw [he, fiberChart_origin, norm_zero]
    exact hε

def fiberBallToSlice (N : NormalBundle T S i) (K : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ)
    (hball : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K.domain) : fiberBallPair N a p hp ε ⟶ slicePair N K p where
  map := TopCat.ofHom ⟨fun z => ⟨z.val.val, z.val.property, hball z.val z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  mapsTo := by
    intro z hz he
    exact hz (Subtype.ext he)

lemma fiberBallToSlice_comp (N : NormalBundle T S i) (K : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ)
    (hball : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K.domain) :
    fiberBallToSlice N K a p hp ε hball ≫ sliceToFiber N K p = fiberBallInclusion N a p hp ε := by
  apply PairMap.ext
  apply TopCat.ext
  intro z
  rfl

theorem fiberBallToSlice_isIso (N : NormalBundle T S i) (K : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) (hε : 0 < ε)
    (hball : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K.domain) (R : Type v) [CommRing R] (q : ℤ) :
    IsIso ((relativeCohomologyFunctor R R q).map (fiberBallToSlice N K a p hp ε hball).op) := by
  let F := relativeCohomologyFunctor R R q
  haveI : IsIso (F.map (sliceToFiber N K p).op) := sliceToFiber_isIso N K p R q
  haveI : IsIso (F.map (sliceToFiber N K p).op ≫
      F.map (fiberBallToSlice N K a p hp ε hball).op) := by
    rw [← F.map_comp, ← op_comp, fiberBallToSlice_comp]
    exact fiberBallInclusion_isIso N a p hp ε hε R q
  exact IsIso.of_isIso_comp_left (F.map (sliceToFiber N K p).op)
    (F.map (fiberBallToSlice N K a p hp ε hball).op)


theorem exists_fiberBall_in_tubularDomain (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fiber N p,
      norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε → z.val ∈ K.domain := by
  let h := P202Specs.ThomClass.fiberChart N a p hp
  let f : Euclidean (n-m) → NormalTotal N := fun v => (h.symm (ULift.up v)).val
  have hcont : Continuous f :=
    continuous_subtype_val.comp (h.symm.continuous.comp continuous_uliftUp)
  have h0 : f 0 = normalZero N p := by
    have he : h.symm (ULift.up 0) = fiberOrigin N p := by
      apply h.injective
      rw [h.apply_symm_apply]
      apply ULift.ext
      exact (fiberChart_origin N a p hp).symm
    exact congrArg Subtype.val he
  have hmem : {v : Euclidean (n-m) | f v ∈ K.domain} ∈ 𝓝 0 :=
    hcont.continuousAt.preimage_mem_nhds
      (K.isOpen_domain.mem_nhds (h0.symm ▸ K.zero_mem p))
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hv : f ((h z).down) ∈ K.domain := hsmall (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he : f ((h z).down) = z.val := by
    change (h.symm (ULift.up (h z).down)).val = z.val
    exact congrArg Subtype.val (h.symm_apply_apply z)
  rwa [he] at hv


def fiberBallCoordinateMap (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) :
    C((fiberBallPair N a p hp ε).space,
      (openPair (puncturedVectorPair (Euclidean (n-m))) {v | norm v < ε}).space) where
  toFun z := ⟨(P202Specs.ThomClass.fiberChart N a p hp z.val).down, z.property⟩
  continuous_toFun := (continuous_uliftDown.comp
    ((P202Specs.ThomClass.fiberChart N a p hp).continuous.comp continuous_subtype_val)).subtype_mk _

lemma fiberBallCoordinateMap_mapsTo (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) :
    Set.MapsTo (fiberBallCoordinateMap N a p hp ε)
      (fiberBallPair N a p hp ε).subspace
      (openPair (puncturedVectorPair (Euclidean (n-m))) {v | norm v < ε}).subspace := by
  intro z hz
  change (P202Specs.ThomClass.fiberChart N a p hp z.val).down ≠ 0
  exact (fiberCoordinates N a p hp).mapsTo hz

/-- Transfer an actual coordinate pair homotopy across arbitrary topological
universes. The pre- and postmaps are ordinary continuous maps, with their
relative-subspace preservation checked explicitly. -/
def pairHomotopyOfCoordinates
    {A B : Pair.{u}} {S₀ T₀ : Pair.{w}} {f₀ g₀ : S₀ ⟶ T₀}
    (H : P202Specs.PrismHomotopy.PairHomotopy f₀ g₀)
    (pre : C(A.space, S₀.space)) (hpre : Set.MapsTo pre A.subspace S₀.subspace)
    (post : C(T₀.space, B.space)) (hpost : Set.MapsTo post T₀.subspace B.subspace)
    (f g : A ⟶ B)
    (hf : ∀ x, f.map x = post (f₀.map (pre x)))
    (hg : ∀ x, g.map x = post (g₀.map (pre x))) :
    P202Specs.PrismHomotopy.PairHomotopy f g where
  homotopy := {
    toFun := fun tx => post (H.homotopy (tx.1, pre tx.2))
    continuous_toFun := post.continuous.comp (H.homotopy.continuous.comp
      (continuous_fst.prodMk (pre.continuous.comp continuous_snd)))
    map_zero_left := by
      intro x
      change post (H.homotopy (0, pre x)) = f.map x
      exact (congrArg post (H.homotopy.map_zero_left (pre x))).trans (hf x).symm
    map_one_left := by
      intro x
      change post (H.homotopy (1, pre x)) = g.map x
      exact (congrArg post (H.homotopy.map_one_left (pre x))).trans (hg x).symm }
  preserves := by
    intro t x
    exact hpost (H.preserves t ⟨pre x.val, hpre x.property⟩)


/-- A local ambient pair homotopy transfers the exact prescribed fiber value
from one normalized tubular slice to another, by excision on its actual
universe-u source ball. No coordinate cohomology object is introduced. -/
theorem fiber_value_transport_of_ball_homotopy
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) (hε : 0 < ε)
    (hball₁ : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K₁.domain)
    (hball₂ : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K₂.domain)
    (H : P202Specs.PrismHomotopy.PairHomotopy
      (fiberBallToSlice N K₁ a p hp ε hball₁ ≫ sliceToAmbient N K₁ p)
      (fiberBallToSlice N K₂ a p hp ε hball₂ ≫ sliceToAmbient N K₂ p))
    (R : Type v) [CommRing R] (q : ℤ)
    (c : relativeCohomology R R (ambientPair i) q)
    (v₀ : relativeCohomology R R (fiberPair N p) q)
    (hc : (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₁ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₁ p).op v₀) :
    (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₂ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₂ p).op v₀ := by
  let F := relativeCohomologyFunctor R R q
  let b₁ := fiberBallToSlice N K₁ a p hp ε hball₁
  let b₂ := fiberBallToSlice N K₂ a p hp ε hball₂
  haveI : IsIso (F.map b₂.op) := fiberBallToSlice_isIso N K₂ a p hp ε hε hball₂ R q
  apply (ConcreteCategory.bijective_of_isIso (F.map b₂.op)).injective
  have hh := (P202.CohomologyPairs.homotopy_invariant R R).2 H q
  have hh' : F.map (sliceToAmbient N K₁ p).op ≫ F.map b₁.op =
      F.map (sliceToAmbient N K₂ p).op ≫ F.map b₂.op := by
    simpa only [op_comp, Functor.map_comp] using hh
  have hb : F.map (sliceToFiber N K₁ p).op ≫ F.map b₁.op =
      F.map (sliceToFiber N K₂ p).op ≫ F.map b₂.op := by
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
      fiberBallToSlice_comp, fiberBallToSlice_comp]
  calc
    F.map b₂.op (F.map (sliceToAmbient N K₂ p).op c) =
      F.map b₁.op (F.map (sliceToAmbient N K₁ p).op c) :=
        congrArg (fun f => f c) hh'.symm
    _ = F.map b₁.op (F.map (sliceToFiber N K₁ p).op v₀) := by rw [hc]
    _ = F.map b₂.op (F.map (sliceToFiber N K₂ p).op v₀) :=
      congrArg (fun f => f v₀) hb

end P202.ThomClass


noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.MapData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- The original bundle chart, with its product coordinates exposed. -/
def normalProductChart (N : NormalBundle T S i) (a : P)
    (c : ModelChart m .euclidean P) :
    OpenPartialHomeomorph (NormalTotal N) (Euclidean m × Euclidean (n-m)) :=
  (bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c).trans
    ((normalBundle N).coordinates.homeomorph.symm.trans
      ((Homeomorph.Set.univ (Euclidean m)).prodCongr
        (Homeomorph.Set.univ (Euclidean (n-m))))).toOpenPartialHomeomorph

lemma normalProductChart_apply (N : NormalBundle T S i) (a : P)
    (c : ModelChart m .euclidean P) (z : NormalTotal N) :
    normalProductChart N a c z = (normalBundle N).coordinates.linearEquiv.symm
      ((bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c) z).val := by
  rfl

lemma normalProductChart_source (N : NormalBundle T S i) (a : P)
    (c : ModelChart m .euclidean P) :
    (normalProductChart N a c).source =
      (bundleChart (normalBundle N).coordinates ((normalBundle N).trivialization a) c).source := by
  simp [normalProductChart, OpenPartialHomeomorph.trans_source]

lemma normalProductChart_zero (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (c : ModelChart m .euclidean P) :
    normalProductChart N a c (normalZero N p) = ((c p).val, 0) := by
  rw [normalProductChart_apply,
    SmoothManifolds.BundleData.bundleChart_val _ _ _ _
      ((normalBundle N).trivialization_baseSet a |>.symm ▸ hp)]
  change (normalBundle N).coordinates.linearEquiv.symm
    ((normalBundle N).coordinates.linearEquiv ((c p).val,
      (normalBundle N).fiberCoordinates a p hp 0)) = _
  rw [map_zero, ContinuousLinearEquiv.symm_apply_apply]

lemma normalProductChart_snd_eq_zero_iff (N : NormalBundle T S i) (a : P)
    (c : ModelChart m .euclidean P) (z : NormalTotal N)
    (hz : z ∈ (normalProductChart N a c).source) :
    (normalProductChart N a c z).2 = 0 ↔ z = normalZero N z.proj := by
  let B := normalBundle N
  have hzb : z ∈ (bundleChart B.coordinates (B.trivialization a) c).source := by
    rwa [normalProductChart_source] at hz
  have hp : z.proj ∈ (B.trivialization a).baseSet :=
    ((SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mp hzb).1
  have hpB : z.proj ∈ B.baseSet a := (B.trivialization_baseSet a) ▸ hp
  rw [normalProductChart_apply,
    SmoothManifolds.BundleData.bundleChart_val _ _ _ _ hp,
    ContinuousLinearEquiv.symm_apply_apply]
  change B.fiberCoordinates a z.proj hpB z.snd = 0 ↔ z = normalZero N z.proj
  constructor
  · intro hv
    have hv0 : z.snd = 0 := (B.fiberCoordinates a z.proj hpB).injective
      (hv.trans (map_zero (B.fiberCoordinates a z.proj hpB)).symm)
    cases z with
    | mk p v =>
      change v = 0 at hv0
      subst v
      rfl
  · intro hz
    have hv := congrArg (fun y => (B.trivialization a y).2) hz
    change B.fiberCoordinates a z.proj hpB z.snd =
      B.fiberCoordinates a z.proj hpB 0 at hv
    exact hv.trans (map_zero (B.fiberCoordinates a z.proj hpB))

/-- A genuine open product-coordinate neighborhood in the first tubular
chart, with its actual ambient map and support-preservation statement. -/
theorem exists_tubular_product_target
    (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (F : NormalTotal N → M)
    (hF : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F K.domain)
    (heF : ∀ z (hz : z ∈ K.domain), F z = (K.homeomorph ⟨z, hz⟩).val)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart m .euclidean P) (hpc : p ∈ c.source) :
    ∃ (W : Set (Euclidean m × Euclidean (n-m))) (Φ : W → M),
      IsOpen W ∧ ((c p).val, 0) ∈ W ∧ Continuous Φ ∧
      (∀ w : W, w.val.2 ≠ 0 → Φ w ∉ Set.range i) ∧
      (∀ w : W, Φ w = F ((normalProductChart N a c).symm w.val)) ∧
      (∀ w : W, w.val ∈ (normalProductChart N a c).target ∧
        (normalProductChart N a c).symm w.val ∈ K.domain) := by
  let e := normalProductChart N a c
  let W := e.target ∩ e.symm ⁻¹' K.domain
  have hW : IsOpen W := e.symm.isOpen_inter_preimage K.isOpen_domain
  have hz : normalZero N p ∈ e.source := by
    rw [normalProductChart_source]
    apply (SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mpr
    exact ⟨(normalBundle N).trivialization_baseSet a |>.symm ▸ hp, hpc⟩
  have hezero : e (normalZero N p) = ((c p).val, 0) := normalProductChart_zero N a p hp c
  have hbW : ((c p).val, 0) ∈ W := by
    rw [← hezero]
    refine ⟨e.map_source hz, ?_⟩
    change e.symm (e (normalZero N p)) ∈ K.domain
    rw [e.left_inv hz]
    exact K.zero_mem p
  let Φ : W → M := fun w => F (e.symm w.val)
  have hec : Continuous (fun w : W => e.symm w.val) :=
    e.symm.continuousOn.comp_continuous continuous_subtype_val (fun w => w.property.1)
  have hFc : ContinuousOn F K.domain := fun z hz => (hF z hz).1.continuousWithinAt
  have hΦ : Continuous Φ := hFc.comp_continuous hec (fun w => w.property.2)
  refine ⟨W, Φ, hW, hbW, hΦ, ?_, fun _ => rfl, fun w => w.property⟩
  intro w hw hrange
  let z := e.symm w.val
  have hzd : z ∈ K.domain := w.property.2
  have hzsource : z ∈ e.source := e.symm.map_source w.property.1
  have hr : (K.homeomorph ⟨z, hzd⟩).val ∈ Set.range i := by
    rwa [← heF z hzd]
  have hz0 : z = normalZero N z.proj :=
    (tubular_mem_range_iff N K z.proj ⟨z, rfl, hzd⟩).mp hr
  have he0 : (e z).2 = 0 :=
    (normalProductChart_snd_eq_zero_iff N a c z hzsource).mpr hz0
  exact hw (by simpa only [z, e.right_inv w.property.1] using he0)

lemma normalProductChart_fiber (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (c : ModelChart m .euclidean P)
    (v : Euclidean (n-m)) :
    normalProductChart N a c ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ =
      ((c p).val, v) := by
  rw [normalProductChart_apply,
    SmoothManifolds.BundleData.bundleChart_val _ _ _ _
      ((normalBundle N).trivialization_baseSet a |>.symm ▸ hp)]
  change (normalBundle N).coordinates.linearEquiv.symm
    ((normalBundle N).coordinates.linearEquiv ((c p).val,
      (fiberLinearCoordinates N a p hp) ((fiberLinearCoordinates N a p hp).symm v))) = _
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

lemma normalProductChart_inverse_fiber (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (c : ModelChart m .euclidean P)
    (hpc : p ∈ c.source) (v : Euclidean (n-m)) :
    (normalProductChart N a c).symm ((c p).val, v) =
      ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ := by
  have hz : (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈
      (normalProductChart N a c).source := by
    rw [normalProductChart_source]
    apply (SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mpr
    exact ⟨(normalBundle N).trivialization_baseSet a |>.symm ▸ hp, hpc⟩
  rw [← normalProductChart_fiber N a p hp c v]
  exact (normalProductChart N a c).left_inv hz

/-- A transition has a continuous representative on an actual open normal
coordinate neighborhood, with all three domain conditions retained. -/
theorem tubular_transition_continuity
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N)
    (F₂ : NormalTotal N → M) (G₁ : M → NormalTotal N)
    (hF₂ : ManifoldSmoothOn (normalBundle N).totalManifold.smoothStructure.val
      S.smoothStructure.val F₂ K₂.domain)
    (hG₁ : ManifoldSmoothOn S.smoothStructure.val
      (normalBundle N).totalManifold.smoothStructure.val G₁ K₁.target)
    (heF₂ : ∀ z (hz : z ∈ K₂.domain), F₂ z = (K₂.homeomorph ⟨z, hz⟩).val)
    (heG₁ : ∀ x (hx : x ∈ K₁.target), G₁ x = (K₁.homeomorph.symm ⟨x, hx⟩).val)
    (a p : P) (hp : p ∈ (normalBundle N).baseSet a)
    (c : ModelChart m .euclidean P) (hpc : p ∈ c.source) :
    ∃ U : Set (Euclidean (n-m)), IsOpen U ∧ 0 ∈ U ∧
      ContinuousOn (fun v => normalProductChart N a c
        (G₁ (F₂ ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩))) U ∧
      (∀ v ∈ U, (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K₂.domain ∧
        F₂ ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ ∈ K₁.target ∧
        G₁ (F₂ ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩) ∈
          (normalProductChart N a c).source) ∧
      normalProductChart N a c
        (G₁ (F₂ ⟨p, (fiberLinearCoordinates N a p hp).symm 0⟩)) = ((c p).val, 0) := by
  let z : Euclidean (n-m) → NormalTotal N :=
    fun v => ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩
  let e := normalProductChart N a c
  have hz0 : z 0 = normalZero N p := by simp [z, normalZero]
  have hFzero : F₂ (z 0) = i p := by
    rw [hz0, heF₂ _ (K₂.zero_mem p), K₂.zero_eq]
  have hiK : i p ∈ K₁.target := K₁.inclusion_mem ⟨p, rfl⟩
  have hGzero : G₁ (i p) = normalZero N p := by
    rw [heG₁ _ hiK]
    have he : (⟨i p, hiK⟩ : K₁.target) =
        K₁.homeomorph ⟨normalZero N p, K₁.zero_mem p⟩ :=
      Subtype.ext (K₁.zero_eq p).symm
    rw [he, K₁.homeomorph.symm_apply_apply]
  have hezero : normalZero N p ∈ e.source := by
    rw [normalProductChart_source]
    apply (SmoothManifolds.BundleData.mem_bundleChart_source _ _ _ _).mpr
    exact ⟨(normalBundle N).trivialization_baseSet a |>.symm ▸ hp, hpc⟩
  have hzc : Continuous z := continuous_fiberLinearCoordinates_symm N a p hp
  have hFc : ContinuousOn F₂ K₂.domain := fun z hz => (hF₂ z hz).1.continuousWithinAt
  have hGc : ContinuousOn G₁ K₁.target := fun x hx => (hG₁ x hx).1.continuousWithinAt
  let U₂ := z ⁻¹' K₂.domain
  have hU₂ : IsOpen U₂ := K₂.isOpen_domain.preimage hzc
  have hFzc : ContinuousOn (fun v => F₂ (z v)) U₂ :=
    hFc.comp hzc.continuousOn (fun _ hv => hv)
  let U₁ := U₂ ∩ (fun v => F₂ (z v)) ⁻¹' K₁.target
  have hU₁ : IsOpen U₁ := hFzc.isOpen_inter_preimage hU₂ K₁.isOpen_target
  have hGcomp : ContinuousOn (fun v => G₁ (F₂ (z v))) U₁ :=
    hGc.comp (hFzc.mono Set.inter_subset_left) (fun _ hv => hv.2)
  let U := U₁ ∩ (fun v => G₁ (F₂ (z v))) ⁻¹' e.source
  have hU : IsOpen U := hGcomp.isOpen_inter_preimage hU₁ e.open_source
  have h0U : (0 : Euclidean (n-m)) ∈ U := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change z 0 ∈ K₂.domain
      rw [hz0]
      exact K₂.zero_mem p
    · change F₂ (z 0) ∈ K₁.target
      rwa [hFzero]
    · change G₁ (F₂ (z 0)) ∈ e.source
      rwa [hFzero, hGzero]
  refine ⟨U, hU, h0U, ?_, ?_, ?_⟩
  · exact e.continuousOn.comp (hGcomp.mono Set.inter_subset_left) (fun _ hv => hv.2)
  · intro v hv
    exact ⟨hv.1.1, hv.1.2, hv.2⟩
  · change e (G₁ (F₂ (z 0))) = _
    rw [hFzero, hGzero]
    exact normalProductChart_zero N a p hp c

theorem exists_normalized_tubular_local_homotopy
    (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N)
    (hK₁ : NormalCompatible N K₁) (hK₂ : NormalCompatible N K₂) (p : P) :
    ∃ (a : P) (hp : p ∈ (normalBundle N).baseSet a)
      (ε : ℝ) (hε : 0 < ε)
      (W : Set (Euclidean m × Euclidean (n-m))) (Φ : W → M)
      (j g : openPair (puncturedVectorPair (Euclidean (n-m)))
          {v : Euclidean (n-m) | norm v < ε} ⟶
        openPair (secondPuncturedPair (Euclidean m) (Euclidean (n-m))) W),
      IsOpen W ∧ Continuous Φ ∧
      (∀ w : W, w.val.2 ≠ 0 → Φ w ∉ Set.range i) ∧
      (∀ v : Euclidean (n-m), norm v < ε →
        (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K₁.domain) ∧
      (∀ v : Euclidean (n-m), norm v < ε →
        (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K₂.domain) ∧
      (∀ x, Φ (j.map x) = fiberImage N K₁ a p hp x.val) ∧
      (∀ x, Φ (g.map x) = fiberImage N K₂ a p hp x.val) ∧
      Nonempty (P202Specs.PrismHomotopy.PairHomotopy j g)
 := by
  obtain ⟨F₁, G₁, hF₁, hG₁, heF₁, heG₁⟩ := tubular_smoothRepresentatives N K₁ p
  obtain ⟨F₂, G₂, hF₂, hG₂, heF₂, heG₂⟩ := tubular_smoothRepresentatives N K₂ p
  obtain ⟨a, hp, c, hc, hpc, hder⟩ := normalCompatible_transition_derivative
    hi N K₁ K₂ hK₁ hK₂ F₁ F₂ G₁ hF₁ hF₂ hG₁ heF₁ heF₂ heG₁ p
  let e := normalProductChart N a c
  let z : Euclidean (n-m) → NormalTotal N :=
    fun v => ⟨p, (fiberLinearCoordinates N a p hp).symm v⟩
  let f : Euclidean (n-m) → Euclidean m × Euclidean (n-m) :=
    fun v => e (G₁ (F₂ (z v)))
  obtain ⟨U, hU, h0U, hcont, hdom, hf0⟩ := tubular_transition_continuity
    N K₁ K₂ F₂ G₁ hF₂ hG₁ heF₂ heG₁ a p hp c hpc
  have hdf : HasFDerivAt (fun v => (f v).2)
      (ContinuousLinearMap.id ℝ (Euclidean (n-m))) 0 := by
    simpa only [f, e, z, normalProductChart_apply, tubularTransitionCoordinates] using hder
  obtain ⟨W, Φ, hW, hbW, hΦ, hsupport, hΦformula, hWprops⟩ :=
    exists_tubular_product_target N K₁ F₁ hF₁ heF₁ a p hp c hpc
  obtain ⟨ε, hε, j, g, hsmall, hj, hg, H⟩ :=
    exists_pairHomotopy_moving_base_in_open hU h0U hcont hW hbW
      (congrArg Prod.fst hf0) (congrArg Prod.snd hf0) hdf
  have hball₂ (v : Euclidean (n-m)) (hv : norm v < ε) : z v ∈ K₂.domain :=
    (hdom v (hsmall hv)).1
  have hball₁ (v : Euclidean (n-m)) (hv : norm v < ε) : z v ∈ K₁.domain := by
    have hh := (hWprops (j.map ⟨v, hv⟩)).2
    rw [hj ⟨v, hv⟩, normalProductChart_inverse_fiber N a p hp c hpc v] at hh
    exact hh
  refine ⟨a, hp, ε, hε, W, Φ, j, g, hW, hΦ, hsupport, hball₁, hball₂, ?_, ?_, H⟩
  · intro x
    rw [hΦformula, hj x, normalProductChart_inverse_fiber N a p hp c hpc x.val]
    unfold fiberImage
    rw [dite_eq_left (hball₁ x.val x.property)]
    exact heF₁ _ (hball₁ x.val x.property)
  · intro x
    rw [hΦformula, hg x]
    change F₁ (e.symm (e (G₁ (F₂ (z x.val))))) = _
    rw [e.left_inv (hdom x.val (hsmall x.property)).2.2]
    have hxT : F₂ (z x.val) ∈ K₁.target := (hdom x.val (hsmall x.property)).2.1
    have hFG : F₁ (G₁ (F₂ (z x.val))) = F₂ (z x.val) := by
      rw [heG₁ _ hxT, heF₁ _ (K₁.homeomorph.symm ⟨F₂ (z x.val), hxT⟩).property]
      exact congrArg Subtype.val (K₁.homeomorph.apply_symm_apply ⟨F₂ (z x.val), hxT⟩)
    rw [hFG]
    unfold fiberImage
    rw [dite_eq_left (hball₂ x.val x.property)]
    exact heF₂ _ (hball₂ x.val x.property)

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

lemma fiberChart_reconstruct (N : NormalBundle T S i) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (z : Fiber N p) :
    (⟨p, (fiberLinearCoordinates N a p hp).symm
      ((P202Specs.ThomClass.fiberChart N a p hp z).down)⟩ : NormalTotal N) = z.val := by
  let h := P202Specs.ThomClass.fiberChart N a p hp
  have he : h ⟨⟨p, (fiberLinearCoordinates N a p hp).symm (h z).down⟩, rfl⟩ = h z := by
    apply ULift.ext
    change fiberLinearCoordinates N a p hp ((fiberLinearCoordinates N a p hp).symm (h z).down) = _
    exact (fiberLinearCoordinates N a p hp).apply_symm_apply _
  exact congrArg Subtype.val (h.injective he)


lemma fiberImage_fiberChart (N : NormalBundle T S i) (K : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (z : Fiber N p) (hz : z.val ∈ K.domain) :
    fiberImage N K a p hp ((P202Specs.ThomClass.fiberChart N a p hp z).down) =
      (K.homeomorph ⟨z.val, hz⟩).val := by
  unfold fiberImage
  rw [fiberChart_reconstruct N a p hp z]
  simp only [dif_pos hz]


/-- A coordinate homotopy with the actual tubular endpoint maps transfers
relative fiber values. The coordinate ball lives in Type 0 and the actual
fiber/ambient pairs remain in the original geometry universe. -/
theorem fiber_value_transport_of_coordinate_homotopy
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N) (a p : P)
    (hp : p ∈ (normalBundle N).baseSet a) (ε : ℝ) (hε : 0 < ε)
    (W : Set (Euclidean m × Euclidean (n-m))) (Φ : W → M) (hΦ : Continuous Φ)
    (hΦsub : ∀ w : W, w.val.2 ≠ 0 → Φ w ∉ Set.range i)
    (j g : openPair (puncturedVectorPair (Euclidean (n-m)))
        {v : Euclidean (n-m) | norm v < ε} ⟶
      openPair (secondPuncturedPair (Euclidean m) (Euclidean (n-m))) W)
    (H : P202Specs.PrismHomotopy.PairHomotopy j g)
    (hdom₁ : ∀ v : Euclidean (n-m), norm v < ε →
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K₁.domain)
    (hdom₂ : ∀ v : Euclidean (n-m), norm v < ε →
      (⟨p, (fiberLinearCoordinates N a p hp).symm v⟩ : NormalTotal N) ∈ K₂.domain)
    (hj : ∀ x, Φ (j.map x) = fiberImage N K₁ a p hp x.val)
    (hg : ∀ x, Φ (g.map x) = fiberImage N K₂ a p hp x.val)
    (R : Type v) [CommRing R] (q : ℤ)
    (c : relativeCohomology R R (ambientPair i) q)
    (v₀ : relativeCohomology R R (fiberPair N p) q)
    (hc : (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₁ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₁ p).op v₀) :
    (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₂ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₂ p).op v₀ := by
  have hball₁ : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K₁.domain := by
    intro z hz
    have hd := hdom₁ ((P202Specs.ThomClass.fiberChart N a p hp z).down) hz
    rwa [fiberChart_reconstruct] at hd
  have hball₂ : ∀ z : Fiber N p, norm ((P202Specs.ThomClass.fiberChart N a p hp z).down) < ε →
      z.val ∈ K₂.domain := by
    intro z hz
    have hd := hdom₂ ((P202Specs.ThomClass.fiberChart N a p hp z).down) hz
    rwa [fiberChart_reconstruct] at hd
  let f₁ := fiberBallToSlice N K₁ a p hp ε hball₁ ≫ sliceToAmbient N K₁ p
  let f₂ := fiberBallToSlice N K₂ a p hp ε hball₂ ≫ sliceToAmbient N K₂ p
  let pre := fiberBallCoordinateMap N a p hp ε
  let post : C((openPair (secondPuncturedPair (Euclidean m) (Euclidean (n-m))) W).space,
      (ambientPair i).space) := ⟨Φ, hΦ⟩
  have hpost : Set.MapsTo post
      (openPair (secondPuncturedPair (Euclidean m) (Euclidean (n-m))) W).subspace
      (ambientPair i).subspace := by
    intro w hw
    exact hΦsub w hw
  have hf₁ : ∀ x, f₁.map x = post (j.map (pre x)) := by
    intro x
    change (K₁.homeomorph ⟨x.val.val, hball₁ x.val x.property⟩).val = Φ (j.map (pre x))
    rw [hj]
    exact (fiberImage_fiberChart N K₁ a p hp x.val (hball₁ x.val x.property)).symm
  have hf₂ : ∀ x, f₂.map x = post (g.map (pre x)) := by
    intro x
    change (K₂.homeomorph ⟨x.val.val, hball₂ x.val x.property⟩).val = Φ (g.map (pre x))
    rw [hg]
    exact (fiberImage_fiberChart N K₂ a p hp x.val (hball₂ x.val x.property)).symm
  let Hactual := pairHomotopyOfCoordinates H pre
    (fiberBallCoordinateMap_mapsTo N a p hp ε) post hpost f₁ f₂ hf₁ hf₂
  exact fiber_value_transport_of_ball_homotopy N K₁ K₂ a p hp ε hε hball₁ hball₂ Hactual R q c v₀ hc

end P202.ThomClass



noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite Filter
open scoped Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
namespace P202.ThomClass
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs P202Specs.ThomClass
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
  {i : P → M}
attribute [local instance] normalTopology

/-- The same prescribed relative class is seen on every normalized tubular
normal slice, independently of that tubular choice. -/
theorem normalized_tubular_fiber_value_transport
    (R : Type v) [CommRing R] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (K₁ K₂ : TubularNeighborhood N)
    (hK₁ : NormalCompatible N K₁) (hK₂ : NormalCompatible N K₂)
    (p : P) (q : ℤ) (c : relativeCohomology R R (ambientPair i) q)
    (v₀ : relativeCohomology R R (fiberPair N p) q)
    (hc : (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₁ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₁ p).op v₀) :
    (relativeCohomologyFunctor R R q).map (sliceToAmbient N K₂ p).op c =
      (relativeCohomologyFunctor R R q).map (sliceToFiber N K₂ p).op v₀ := by
  obtain ⟨a, hp, ε, hε, W, Φ, j, g, hW, hΦ, hΦsub, hdom₁, hdom₂, hj, hg, ⟨H⟩⟩ :=
    exists_normalized_tubular_local_homotopy hi N K₁ K₂ hK₁ hK₂ p
  exact fiber_value_transport_of_coordinate_homotopy N K₁ K₂ a p hp ε hε W Φ hΦ hΦsub
    j g H hdom₁ hdom₂ hj hg R q c v₀ hc

/-- Fiber values checked on one normalized tube hold on every normalized
tube, exactly as required by the intrinsic original target. -/
theorem hasFiberValues_of_one_normalized
    (R : Type v) [CommRing R] (hi : IsSmoothEmbedding T S i)
    (N : NormalBundle T S i) (d : ℕ) (o : Orientation R N d)
    (c : relativeCohomology R R (ambientPair i) (d : ℤ))
    (K₀ : TubularNeighborhood N) (hK₀ : NormalCompatible N K₀)
    (hc : ∀ p : P,
      (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToAmbient N K₀ p).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (sliceToFiber N K₀ p).op (o.generator p)) :
    HasFiberValues R o c := by
  intro K hK p
  exact normalized_tubular_fiber_value_transport R hi N K₀ K hK₀ hK p d c (o.generator p) (hc p)

end P202.ThomClass


namespace P202.ThomClass
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs

/-- The full intrinsic Thom conclusion, including normalized tubular
existence and uniqueness independent of every tubular choice. -/
theorem exists_unique :
  ∀ (R : Type v) [CommRing R] (m n d : ℕ)
    (P M : Type u) [TopologicalSpace P] [TopologicalSpace M] [CompactSpace P]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∀ (N : NormalBundle T S i), (∀ _ : P, d = n-m) →
      ∀ o : Orientation R N d,
        (∃ K : TubularNeighborhood N, NormalCompatible N K) ∧
          ∃! c : relativeCohomology R R (ambientPair i) (d : ℤ), HasFiberValues R o c := by
  intro R _ m n d P M _ _ _ T S i hi N hrank o
  cases isEmpty_or_nonempty P with
  | inl hP =>
    letI := hP
    exact exists_unique_of_isEmpty R d hi N o
  | inr hP =>
    cases d with
    | zero => exact exists_unique_of_degree_zero R hi N hrank o
    | succ k =>
      have hd : n-m = k+1 := (hrank (Classical.choice hP)).symm
      obtain ⟨K,hK⟩ := normalized_tubular_exists hi N
      obtain ⟨c,hc,hu⟩ := exists_unique_on_fixed_tube_positive R hi N (k+1) hd (by omega) o K
      refine ⟨⟨K,hK⟩,c,hasFiberValues_of_one_normalized R hi N (k+1) o c K hK hc,?_⟩
      intro b hb
      exact hu b (hb K hK)
end P202.ThomClass
