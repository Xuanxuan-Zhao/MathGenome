import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import Mathlib.Topology.Homeomorph.Lemmas

/-! Local single-member projection formula, paper.tex 2551–2574, 2580–2588.
All pairs below use the original normal bundle, tubular map, and subspace topologies.
No cohomological comparison or projection identity is included as input data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData
universe u v
namespace P202Specs.LocalThomProjection
open P202Specs.ThomClass P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
variable {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
  {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M} {i : P → M}
attribute [local instance] normalTopology

/-- The full normal bundle over U, punctured along its zero section. -/
def normalRegionPair (N : NormalBundle T S i) (U : Set P) : Pair.{u} :=
  ⟨TopCat.of {z : NormalTotal N // z.proj ∈ U}, {z | z.val ≠ normalZero N z.val.proj}⟩

def normalRegionProjection (N : NormalBundle T S i) (a : P) (U : Set P)
    (hU : U ⊆ (normalBundle N).baseSet a) :
    normalRegionPair N U ⟶ modelPair.{u} (n-m) := by
  let e := (normalBundle N).trivialization a
  have he : U ⊆ e.baseSet := by
    change U ⊆ ((normalBundle N).trivialization a).baseSet
    rwa [(normalBundle N).trivialization_baseSet]
  let h := (e.preimageHomeomorph he).trans
    ((Homeomorph.refl U).prodCongr Homeomorph.ulift.symm)
  exact {
    map := TopCat.ofHom ⟨fun z => (h z).2, continuous_snd.comp h.continuous⟩
    mapsTo := by
      intro z hz
      exact (fiberCoordinates N a z.val.proj (hU z.property)).mapsTo
        (show (⟨z.val, rfl⟩ : Fiber N z.val.proj) ≠ fiberOrigin N z.val.proj from
          fun hh => hz (congrArg Subtype.val hh)) }

/-- The exact set W = domain(K) ∩ projection⁻¹(U). -/
def domainRegion (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    Set (NormalTotal N) := K.domain ∩ Bundle.TotalSpace.proj ⁻¹' U

def domainRegionPair (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) : Pair.{u} :=
  ⟨TopCat.of (domainRegion N K U), {z | z.val ≠ normalZero N z.val.proj}⟩

def domainRegionToNormal (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    domainRegionPair N K U ⟶ normalRegionPair N U :=
  ⟨TopCat.ofHom ⟨fun z => ⟨z.val, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩,
    fun _ hz => hz⟩

/-- V is the actual tubular image of W as a subset of the ambient manifold. -/
def imageRegion (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) : Set M :=
  (fun z : K.domain => (K.homeomorph z).val) '' {z | z.val.proj ∈ U}

def regionHomeomorph (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    domainRegion N K U ≃ₜ imageRegion N K U := by
  let h : domainRegion N K U ≃ₜ {z : K.domain // z.val.proj ∈ U} := {
    toFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
    invFun := fun z => ⟨z.val.val, z.val.property, z.property⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact h.trans ((Topology.IsEmbedding.subtypeVal.comp K.homeomorph.isEmbedding).homeomorphImage _)

def ambientRegionPair (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) : Pair.{u} :=
  ⟨TopCat.of (imageRegion N K U), {x | x.val ∉ Set.range i}⟩

def ambientRegionInclusion (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    ambientRegionPair N K U ⟶ ambientPair i :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hx => hx⟩

def regionPairIso (N : NormalBundle T S i) (K : TubularNeighborhood N) (U : Set P) :
    domainRegionPair N K U ≅ ambientRegionPair N K U := by
  let h := regionHomeomorph N K U
  have hh : ∀ z : domainRegion N K U,
      z.val ≠ normalZero N z.val.proj ↔ (h z).val ∉ Set.range i := by
    intro z
    exact not_congr (tubular_mem_range_iff N K z.val.proj ⟨z.val, rfl, z.property.1⟩).symm
  exact {
    hom := ⟨TopCat.ofHom ⟨h, h.continuous⟩, fun z hz => (hh z).mp hz⟩
    inv := ⟨TopCat.ofHom ⟨h.symm, h.symm.continuous⟩, fun x hx =>
      (hh (h.symm x)).mpr (by
        change x.val ∉ Set.range i at hx
        simpa only [h.apply_symm_apply] using hx)⟩
    hom_inv_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext h.symm_apply_apply))
    inv_hom_id := PairMap.ext _ _ (TopCat.hom_ext (ContinuousMap.ext h.apply_symm_apply)) }

/-- Inverse tubular map followed by the fiber coordinate of the original chart. -/
def ambientCoordinates (N : NormalBundle T S i) (K : TubularNeighborhood N)
    (a : P) (U : Set P) (hU : U ⊆ (normalBundle N).baseSet a) :
    ambientRegionPair N K U ⟶ modelPair.{u} (n-m) :=
  (regionPairIso N K U).inv ≫ domainRegionToNormal N K U ≫ normalRegionProjection N a U hU

/-- Full local formula, including arbitrary subsequent pair pullbacks.
The pointwise rank convention permits arbitrary declared degree for empty P.
There are no positive-rank, nonzero-ring, or connectedness assumptions. -/
def localProjection_type : Prop :=
  ∀ (R : Type v) [CommRing R] (m n d : ℕ)
    (P M : Type u) [TopologicalSpace P] [TopologicalSpace M] [CompactSpace P]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M), IsSmoothEmbedding T S i →
    ∀ (N : NormalBundle T S i), (∀ _ : P, d = n-m) →
    ∀ (o : Orientation R N d)
      (c : relativeCohomology R R (ambientPair i) (d : ℤ)), HasFiberValues R o c →
    ∀ (K : TubularNeighborhood N), NormalCompatible N K → ∀ p : P,
    ∃ (a : P) (U : Set P), IsOpen U ∧ p ∈ U ∧
    ∃ hU : U ⊆ (normalBundle N).baseSet a,
    ∃ g : relativeCohomology R R (modelPair.{u} (n-m)) (d : ℤ),
      (∀ (q : P) (hq : q ∈ U),
        (relativeCohomologyFunctor R R (d : ℤ)).map
          (fiberCoordinates N a q (hU hq)).op g = o.generator q) ∧
      Function.Bijective (fun r : R => r • g) ∧
      IsOpen (imageRegion N K U) ∧ i p ∈ imageRegion N K U ∧
      (∀ x : imageRegion N K U,
        ((ambientCoordinates N K a U hU).map x).down = 0 ↔ x.val ∈ Set.range i) ∧
      (relativeCohomologyFunctor R R (d : ℤ)).map (ambientRegionInclusion N K U).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (ambientCoordinates N K a U hU).op g ∧
      (∀ (B : Pair.{u}) (f : B ⟶ ambientRegionPair N K U),
        (relativeCohomologyFunctor R R (d : ℤ)).map (f ≫ ambientRegionInclusion N K U).op c =
        (relativeCohomologyFunctor R R (d : ℤ)).map (f ≫ ambientCoordinates N K a U hU).op g)

end P202Specs.LocalThomProjection
