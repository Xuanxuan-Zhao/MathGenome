import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceRegionsEuler
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SurfaceRegionConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionEuler
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.EulerPoincare
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.OrdinaryHomologyAxioms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Data.Set.UnionLift
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
The complete surface-regions Euler identity, paper.tex 5003–5091. The
upstream construction supplies the actual graph and component closures.
Collars, singular-homology additivity, and Mayer–Vietoris give finite-type
homology and the Euler identity for those same subspaces.
-/
set_option autoImplicit false
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open scoped BigOperators
universe u v w

namespace P202.SurfaceRegionsEuler
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.PlanarRegionTopology P202Specs.EulerPoincare
open P202Specs.SingularChains

section Geometry
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma graphCompact (G : EmbeddedGraph S) : IsCompact G.carrier := by
  exact (Set.finite_range G.vertex).isCompact.union
    (isCompact_iUnion fun i => isCompact_range (G.edge i).continuous)

lemma graphClosed (G : EmbeddedGraph S) : IsClosed G.carrier := by
  haveI := S.topologicalManifold.hausdorff
  exact (graphCompact G).isClosed

/-- The component sets are the actual fibers of the connected-component
quotient, viewed in the original ambient space. -/
lemma mem_componentSet {U : Set M} {a : ConnectedComponents U} {x : M} :
    x ∈ componentSet U a ↔ ∃ hx : x ∈ U, ConnectedComponents.mk ⟨x, hx⟩ = a := by
  constructor
  · rintro ⟨⟨y, hy⟩, ha, rfl⟩
    exact ⟨hy, ha⟩
  · rintro ⟨hx, ha⟩
    exact ⟨⟨x, hx⟩, ha, rfl⟩

lemma componentSet_subset {U : Set M} (a : ConnectedComponents U) :
    componentSet U a ⊆ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

lemma regionInteriors_cover (R : RegionDecomposition S) :
    (⋃ j, regionInterior R j) = R.graph.carrierᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hx⟩ := mem_iUnion.mp hx
    exact componentSet_subset _ hx
  · intro hx
    refine mem_iUnion.mpr ⟨R.component.symm (ConnectedComponents.mk ⟨x, hx⟩), ?_⟩
    exact mem_componentSet.mpr ⟨hx, (R.component.apply_symm_apply _).symm⟩

lemma regionInteriors_disjoint (R : RegionDecomposition S) :
    Pairwise (fun i j => Disjoint (regionInterior R i) (regionInterior R j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  obtain ⟨hi, hei⟩ := mem_componentSet.mp hi
  obtain ⟨hj, hej⟩ := mem_componentSet.mp hj
  exact hij (R.component.injective (hei.symm.trans hej))

/-- A chart restricts to a homeomorphism on any subset of its source,
including a closed region and its boundary. Both model kinds are retained. -/
def coordinatesHomeomorph (e : ModelChart 2 kind M) (U : Set M)
    (hU : U ⊆ e.source) : U ≃ₜ (coordinates e '' U) :=
  (e.homeomorphOfImageSubsetSource hU rfl).trans
    ((toPlane.toHomeomorph.isEmbedding.comp
      (show IsEmbedding (Subtype.val : ModelSpace 2 kind → Euclidean 2) from
        IsEmbedding.subtypeVal)).homeomorphImage (e '' U)) |>.trans
    (Homeomorph.setCongr (by ext x; simp [coordinates, image_image]))

@[simp] lemma coordinatesHomeomorph_apply (e : ModelChart 2 kind M) (U : Set M)
    (hU : U ⊆ e.source) (x : U) :
    ((coordinatesHomeomorph e U hU) x).val = coordinates e x.val := rfl

def regionClosureHomeomorph (R : RegionDecomposition S) (j : Fin R.regionCount) :
    regionClosure R j ≃ₜ (R.region j).carrier :=
  (coordinatesHomeomorph (R.chart j) _ (R.closure_in_chart j)).trans
    (Homeomorph.setCongr (R.closure_coordinates j))

def regionInteriorHomeomorph (R : RegionDecomposition S) (j : Fin R.regionCount) :
    regionInterior R j ≃ₜ (R.region j).domain :=
  (coordinatesHomeomorph (R.chart j) _
    (subset_closure.trans (R.closure_in_chart j))).trans
    (Homeomorph.setCongr (R.domain_coordinates j))

lemma coordinates_injOn (e : ModelChart 2 kind M) : Set.InjOn (coordinates e) e.source := by
  intro x hx y hy h
  apply e.injOn hx hy
  apply Subtype.ext
  exact toPlane.injective h

lemma regionBoundary_eq_diff (R : RegionDecomposition S) (j : Fin R.regionCount) :
    regionClosure R j ∩ R.graph.carrier = regionClosure R j \ regionInterior R j := by
  rw [← R.frontiers_on_graph j, frontier, (R.open_components j).interior_eq]

lemma regionBoundary_coordinates (R : RegionDecomposition S) (j : Fin R.regionCount) :
    coordinates (R.chart j) '' (regionClosure R j ∩ R.graph.carrier) =
      (R.region j).boundary := by
  rw [regionBoundary_eq_diff]
  have hi := coordinates_injOn (R.chart j)
  have he : coordinates (R.chart j) '' (regionClosure R j \ regionInterior R j) =
      (coordinates (R.chart j) '' regionClosure R j) \
        (coordinates (R.chart j) '' regionInterior R j) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hnx⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨y, hy, he⟩
      have hxy := hi (R.closure_in_chart j (subset_closure hy))
        (R.closure_in_chart j hx) he
      exact hnx (hxy ▸ hy)
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      exact ⟨x, ⟨hx, fun hy => hn ⟨x, hy, rfl⟩⟩, rfl⟩
  rw [he, R.closure_coordinates, R.domain_coordinates]
  exact (congrArg (fun A => closure (R.region j).domain \ A)
    (R.region j).open_domain.interior_eq).symm

def regionBoundaryHomeomorph (R : RegionDecomposition S) (j : Fin R.regionCount) :
    (regionClosure R j ∩ R.graph.carrier : Set M) ≃ₜ (R.region j).boundary :=
  (coordinatesHomeomorph (R.chart j) _
    (inter_subset_left.trans (R.closure_in_chart j))).trans
    (Homeomorph.setCongr (regionBoundary_coordinates R j))

def regionUnionMap (R : RegionDecomposition S) :
    (Σ j : Fin R.regionCount, regionInterior R j) → (R.graph.carrierᶜ : Set M) :=
  fun x => ⟨x.2.val, componentSet_subset _ x.2.property⟩

lemma regionUnionMap_bijective (R : RegionDecomposition S) :
    Function.Bijective (regionUnionMap R) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : x.val = y.val := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (regionInteriors_disjoint R hn)
        x.property (hxy ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hxy)
  · intro x
    have hx : x.val ∈ ⋃ j, regionInterior R j := by
      rw [regionInteriors_cover]
      exact x.property
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact ⟨⟨j, ⟨x.val, hj⟩⟩, rfl⟩

/-- The actual complementary open set has the topology of the disjoint union
of its finitely many region interiors. This is stronger than a bijection of
component labels. -/
def regionInteriorsHomeomorph (R : RegionDecomposition S) :
    (Σ j : Fin R.regionCount, regionInterior R j) ≃ₜ (R.graph.carrierᶜ : Set M) :=
  (Equiv.ofBijective (regionUnionMap R) (regionUnionMap_bijective R)).toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ => continuous_subtype_val.subtype_mk _) (by
      apply isOpenMap_sigma.mpr
      intro j
      exact (R.open_components j).isOpenMap_subtype_val.subtype_mk _)

lemma regionClosures_cover (R : RegionDecomposition S) :
    R.graph.carrier ∪ (⋃ j, regionClosure R j) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ R.graph.carrier
  · exact Or.inl hx
  · apply Or.inr
    have hx' : x ∈ ⋃ j, regionInterior R j := by
      rw [regionInteriors_cover]
      exact hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
    exact mem_iUnion.mpr ⟨j, subset_closure hj⟩

lemma coordinates_mem_domain_iff (R : RegionDecomposition S) (j : Fin R.regionCount)
    (x : regionClosure R j) :
    coordinates (R.chart j) x.val ∈ (R.region j).domain ↔ x.val ∈ regionInterior R j := by
  rw [← R.domain_coordinates j]
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy := coordinates_injOn (R.chart j)
      (R.closure_in_chart j (subset_closure hy)) (R.closure_in_chart j x.property) he
    exact hxy ▸ hy
  · intro hx
    exact ⟨x.val, hx, rfl⟩

/-- A closed inner collar of an actual region in the original surface.
The positive-time condition uses the actual complementary component. -/
structure RegionCollar (R : RegionDecomposition S) (j : Fin R.regionCount) where
  map : C((regionClosure R j ∩ R.graph.carrier : Set M) × unitInterval, regionClosure R j)
  embedding : IsEmbedding map
  at_zero : ∀ x, (map (x, 0)).val = x.val
  positive : ∀ x (t : unitInterval), 0 < (t : ℝ) →
    (map (x, t)).val ∈ regionInterior R j
  open_lower_image : IsOpen (map '' {z | (z.2 : ℝ) < 1})

def transportRegionCollar (R : RegionDecomposition S) (j : Fin R.regionCount)
    (C : BoundaryCollar (R.region j).carrier (R.region j).boundary) : RegionCollar R j := by
  let e := regionClosureHomeomorph R j
  let b := regionBoundaryHomeomorph R j
  let d := b.prodCongr (Homeomorph.refl unitInterval)
  let f : C((regionClosure R j ∩ R.graph.carrier : Set M) × unitInterval,
      regionClosure R j) :=
    ⟨fun z => e.symm (C.map (d z)),
      e.symm.continuous.comp (C.map.continuous.comp d.continuous)⟩
  have hf (x : (regionClosure R j ∩ R.graph.carrier : Set M)) (t : unitInterval) :
      coordinates (R.chart j) (f (x, t)).val = (C.map (b x, t)).val := by
    exact congrArg Subtype.val (e.apply_symm_apply (C.map (b x, t)))
  have he_image : f '' {z | (z.2 : ℝ) < 1} =
      e.symm '' (C.map '' {z | (z.2 : ℝ) < 1}) := by
    ext x
    constructor
    · rintro ⟨⟨a, t⟩, ht, rfl⟩
      exact ⟨C.map (b a, t), ⟨(b a, t), ht, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨⟨a, t⟩, ht, rfl⟩, rfl⟩
      refine ⟨(b.symm a, t), ht, ?_⟩
      change e.symm (C.map (b (b.symm a), t)) = e.symm (C.map (a, t))
      rw [b.apply_symm_apply]
  refine ⟨f, e.symm.isEmbedding.comp (C.embedding.comp d.isEmbedding), ?_, ?_, ?_⟩
  · intro x
    apply coordinates_injOn (R.chart j)
      (R.closure_in_chart j (f (x, 0)).property)
      (R.closure_in_chart j x.property.1)
    rw [hf, C.at_zero]
    rfl
  · intro x t ht
    apply (coordinates_mem_domain_iff R j (f (x, t))).mp
    rw [hf]
    rw [← (P202.PlanarRegionTopology.basicProperties (R.region j)).2.2.1]
    exact C.positive_interior (b x) t ht
  · rw [he_image]
    exact e.symm.isOpenMap _ C.open_lower_image

/-- The planar collar is constructed upstream from the original geometric
region hypotheses and is transported to the actual surface closure here. -/
def regionCollar (R : RegionDecomposition S) (j : Fin R.regionCount) : RegionCollar R j :=
  transportRegionCollar R j (Classical.choice
    (P202.PlanarRegionTopology.planarRegionTopology (R.region j)).2.2.2.2.2.2.1)

def componentInclusion (R : RegionDecomposition S) (j : Fin R.regionCount) :
    C(regionInterior R j, regionClosure R j) :=
  ⟨fun x => ⟨x.val, subset_closure x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual inclusion of a region interior into its surface closure is a
homotopy equivalence, with the inverse and homotopies transported from the
constructed planar collar. -/
lemma regionInteriorClosureEquivalence (R : RegionDecomposition S) (j : Fin R.regionCount) :
    ∃ E : ContinuousMap.HomotopyEquiv (regionInterior R j) (regionClosure R j),
      E.toFun = componentInclusion R j := by
  obtain ⟨_, _, hi, _, _, _, _, ⟨e, he⟩, _⟩ :=
    P202.PlanarRegionTopology.planarRegionTopology (R.region j)
  let d : regionInterior R j ≃ₜ interior (R.region j).carrier :=
    (regionInteriorHomeomorph R j).trans (Homeomorph.setCongr hi.symm)
  let k := regionClosureHomeomorph R j
  let E := d.toHomotopyEquiv.trans (e.trans k.symm.toHomotopyEquiv)
  refine ⟨E, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply k.injective
  change k (k.symm (e (d x))) = k ((componentInclusion R j) x)
  rw [k.apply_symm_apply]
  apply Subtype.ext
  rw [he]
  rfl

namespace RegionCollar
variable {R : RegionDecomposition S} {j : Fin R.regionCount}

def lower (C : RegionCollar R j) : Set (regionClosure R j) :=
  C.map '' {z | (z.2 : ℝ) < 1}

/-- The core is taken in the actual compact closure, then included in M. -/
def core (C : RegionCollar R j) : Set M :=
  Subtype.val '' (C.lowerᶜ : Set (regionClosure R j))

lemma core_compact (C : RegionCollar R j) : IsCompact C.core := by
  letI : CompactSpace (regionClosure R j) :=
    isCompact_iff_compactSpace.mp (R.compact_closures j)
  exact (C.open_lower_image.isClosed_compl.isCompact).image continuous_subtype_val

lemma mem_core_iff (C : RegionCollar R j) (x : regionClosure R j) :
    x.val ∈ C.core ↔ x ∉ C.lower := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma boundary_mem_lower (C : RegionCollar R j)
    (x : (regionClosure R j ∩ R.graph.carrier : Set M)) :
    (⟨x.val, x.property.1⟩ : regionClosure R j) ∈ C.lower := by
  refine ⟨(x, 0), by simp, ?_⟩
  exact Subtype.ext (C.at_zero x)

lemma core_subset_regionInterior (C : RegionCollar R j) :
    C.core ⊆ regionInterior R j := by
  rintro _ ⟨x, hx, rfl⟩
  by_contra hn
  have hxb : x.val ∈ regionClosure R j ∩ R.graph.carrier := by
    rw [regionBoundary_eq_diff]
    exact ⟨x.property, hn⟩
  exact hx (C.boundary_mem_lower ⟨x.val, hxb⟩)

lemma core_disjoint_graph (C : RegionCollar R j) : Disjoint C.core R.graph.carrier := by
  apply Set.disjoint_left.mpr
  intro x hc hg
  exact componentSet_subset _ (C.core_subset_regionInterior hc) hg

end RegionCollar

lemma closure_mem_interior_of_not_graph (R : RegionDecomposition S)
    (j : Fin R.regionCount) {x : M} (hx : x ∈ regionClosure R j)
    (hg : x ∉ R.graph.carrier) : x ∈ regionInterior R j := by
  by_contra hn
  have hb : x ∈ regionClosure R j ∩ R.graph.carrier := by
    rw [regionBoundary_eq_diff]
    exact ⟨hx, hn⟩
  exact hg hb.2

/-- The open graph neighborhood obtained by deleting all compact inner cores. -/
def collarNeighborhood (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) : Set M :=
  (⋃ j, (C j).core)ᶜ

lemma collarNeighborhood_open (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    IsOpen (collarNeighborhood R C) := by
  haveI := S.topologicalManifold.hausdorff
  exact (isCompact_iUnion fun j => (C j).core_compact).isClosed.isOpen_compl

lemma graph_subset_collarNeighborhood (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) : R.graph.carrier ⊆ collarNeighborhood R C := by
  intro x hx hn
  obtain ⟨j, hj⟩ := mem_iUnion.mp hn
  exact Set.disjoint_left.mp (C j).core_disjoint_graph hj hx

lemma collarNeighborhood_cover (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    collarNeighborhood R C ∪ R.graph.carrierᶜ = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ R.graph.carrier
  · exact Or.inl (graph_subset_collarNeighborhood R C hx)
  · exact Or.inr hx

/-- On each closed region, W is precisely its half-open inner collar. -/
lemma collarNeighborhood_inter_closure (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) (j : Fin R.regionCount) :
    collarNeighborhood R C ∩ regionClosure R j =
      Subtype.val '' (C j).lower := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hK⟩
    refine ⟨⟨x, hK⟩, ?_, rfl⟩
    by_contra hn
    exact hx (mem_iUnion.mpr ⟨j, (C j).mem_core_iff ⟨x, hK⟩ |>.mpr hn⟩)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, x.property⟩
    intro hn
    obtain ⟨i, hi⟩ := mem_iUnion.mp hn
    by_cases hij : i = j
    · subst i
      exact (C j).mem_core_iff x |>.mp hi |>.elim hx
    · have hCi := (C i).core_subset_regionInterior hi
      have hg : x.val ∉ R.graph.carrier := componentSet_subset _ hCi
      have hCj := closure_mem_interior_of_not_graph R j x.property hg
      exact Set.disjoint_left.mp (regionInteriors_disjoint R hij) hCi hCj

abbrev OpenCollarTime := Ioo (0 : ℝ) 1

def openCollarTimeInclusion (t : OpenCollarTime) : unitInterval :=
  ⟨t.val, t.property.1.le, t.property.2.le⟩

lemma openCollarTimeInclusion_embedding : IsEmbedding openCollarTimeInclusion :=
  IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _)
    continuous_subtype_val IsEmbedding.subtypeVal

def openCollarMap (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) :
    (regionClosure R j ∩ R.graph.carrier : Set M) × OpenCollarTime → M :=
  fun z => ((C j).map (z.1, openCollarTimeInclusion z.2)).val

lemma openCollarMap_embedding (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) (j : Fin R.regionCount) :
    IsEmbedding (openCollarMap R C j) :=
  IsEmbedding.subtypeVal.comp ((C j).embedding.comp
    (IsEmbedding.id.prodMap openCollarTimeInclusion_embedding))

lemma openCollarMap_range (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) (j : Fin R.regionCount) :
    range (openCollarMap R C j) = collarNeighborhood R C ∩ regionInterior R j := by
  ext x
  constructor
  · rintro ⟨⟨a, t⟩, rfl⟩
    have hlow : ((C j).map (a, openCollarTimeInclusion t)).val ∈
        collarNeighborhood R C ∩ regionClosure R j := by
      rw [collarNeighborhood_inter_closure]
      exact ⟨_, ⟨(a, openCollarTimeInclusion t), t.property.2, rfl⟩, rfl⟩
    exact ⟨hlow.1, (C j).positive a _ t.property.1⟩
  · rintro ⟨hW, hU⟩
    have hK : x ∈ regionClosure R j := subset_closure hU
    have hx : x ∈ Subtype.val '' (C j).lower := by
      rw [← collarNeighborhood_inter_closure]
      exact ⟨hW, hK⟩
    obtain ⟨y, ⟨⟨a, t⟩, ht, hty⟩, hy⟩ := hx
    have htx : ((C j).map (a, t)).val = x := congrArg Subtype.val hty |>.trans hy
    have hp : 0 < (t : ℝ) := by
      by_contra hn
      have ht0 : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
      subst t
      have ha : a.val = x := ((C j).at_zero a).symm.trans htx
      exact (componentSet_subset _ hU) (ha ▸ a.property.2)
    exact ⟨(a, ⟨t.val, hp, ht⟩), htx⟩

/-- Every component of the overlap is an actual open boundary cylinder,
with no doubled counting of graph edges. Boundary circles will be counted
once for each incident region, as required by Mayer–Vietoris. -/
def overlapRegionHomeomorph (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) (j : Fin R.regionCount) :
    ((regionClosure R j ∩ R.graph.carrier : Set M) × OpenCollarTime) ≃ₜ
      (collarNeighborhood R C ∩ regionInterior R j : Set M) :=
  (openCollarMap_embedding R C j).toHomeomorph.trans
    (Homeomorph.setCongr (openCollarMap_range R C j))

namespace RegionCollar
variable {R : RegionDecomposition S} {j : Fin R.regionCount}

/-- Coordinates on the actual half-open collar, obtained by inverting its
embedding rather than choosing unrelated boundary points. -/
def lowerCoordinates (C : RegionCollar R j) :
    C(C.lower, (regionClosure R j ∩ R.graph.carrier : Set M) × unitInterval) :=
  (C.embedding.toHomeomorph.symm : C(range C.map,
      (regionClosure R j ∩ R.graph.carrier : Set M) × unitInterval)).comp
    (ContinuousMap.inclusion (image_subset_range _ _))

lemma map_lowerCoordinates (C : RegionCollar R j) (x : C.lower) :
    C.map (C.lowerCoordinates x) = x.val := by
  exact congrArg Subtype.val (C.embedding.toHomeomorph.apply_symm_apply _)

lemma lowerCoordinates_time_lt (C : RegionCollar R j) (x : C.lower) :
    ((C.lowerCoordinates x).2 : ℝ) < 1 := by
  obtain ⟨z, hz, he⟩ := x.property
  have h : C.lowerCoordinates x = z := C.embedding.injective
    ((C.map_lowerCoordinates x).trans he.symm)
  rw [h]
  exact hz

lemma lowerCoordinates_at_graph (C : RegionCollar R j) (x : C.lower)
    (hx : x.val.val ∈ R.graph.carrier) :
    (C.lowerCoordinates x).2 = 0 ∧ (C.lowerCoordinates x).1.val = x.val.val := by
  have he := congrArg Subtype.val (C.map_lowerCoordinates x)
  have ht : (C.lowerCoordinates x).2 = 0 := by
    apply Subtype.ext
    apply le_antisymm _ (C.lowerCoordinates x).2.property.1
    by_contra hn
    have hi := C.positive (C.lowerCoordinates x).1 (C.lowerCoordinates x).2
      (lt_of_not_ge hn)
    rw [he] at hi
    exact componentSet_subset _ hi hx
  refine ⟨ht, ?_⟩
  have hp : ((C.lowerCoordinates x).1, (0 : unitInterval)) = C.lowerCoordinates x := by
    apply Prod.ext
    · rfl
    · exact ht.symm
  exact (C.at_zero (C.lowerCoordinates x).1).symm.trans
    ((congrArg (fun z => (C.map z).val) hp).trans he)

/-- The collar coordinate contracts by (s,t) ↦ (1-s)t and stays in the
half-open collar, including at the final time. -/
def lowerContraction (C : RegionCollar R j) : C(unitInterval × C.lower, C.lower) where
  toFun z := ⟨C.map ((C.lowerCoordinates z.2).1,
    unitInterval.symm z.1 * (C.lowerCoordinates z.2).2),
    ⟨_, (show ((unitInterval.symm z.1 * (C.lowerCoordinates z.2).2 : unitInterval) : ℝ) < 1 from
      lt_of_le_of_lt (show ((unitInterval.symm z.1 * (C.lowerCoordinates z.2).2 : unitInterval) : ℝ) ≤
        ((C.lowerCoordinates z.2).2 : ℝ) from unitInterval.mul_le_right)
        (C.lowerCoordinates_time_lt z.2)), rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact C.map.continuous.comp
      ((C.lowerCoordinates.continuous.comp continuous_snd).fst.prodMk
        ((unitInterval.continuous_symm.comp continuous_fst).mul
          (C.lowerCoordinates.continuous.comp continuous_snd).snd))

lemma lowerContraction_zero (C : RegionCollar R j) (x : C.lower) :
    C.lowerContraction (0, x) = x := by
  apply Subtype.ext
  change C.map (_, unitInterval.symm 0 * _) = x.val
  simpa using C.map_lowerCoordinates x

lemma lowerContraction_one (C : RegionCollar R j) (x : C.lower) :
    (C.lowerContraction (1, x)).val.val = (C.lowerCoordinates x).1.val := by
  change (C.map (_, unitInterval.symm 1 * _)).val = _
  simpa using C.at_zero (C.lowerCoordinates x).1

lemma lowerContraction_fixed (C : RegionCollar R j) (x : C.lower)
    (hx : x.val.val ∈ R.graph.carrier) (s : unitInterval) :
    C.lowerContraction (s, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change (C.map (_, unitInterval.symm s * _)).val = _
  rw [(C.lowerCoordinates_at_graph x hx).1, mul_zero, C.at_zero]
  exact (C.lowerCoordinates_at_graph x hx).2

end RegionCollar

end Geometry

section Retraction
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- An actual point of W in a closed region lies in that region's lower collar. -/
def regionLowerPoint (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) (x : collarNeighborhood R C)
    (hx : x.val ∈ regionClosure R j) : (C j).lower := by
  refine ⟨⟨x.val, hx⟩, ?_⟩
  by_contra hn
  exact x.property (mem_iUnion.mpr ⟨j, ((C j).mem_core_iff ⟨x.val, hx⟩).mpr hn⟩)

lemma lower_mem_neighborhood (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) (x : (C j).lower) : x.val.val ∈ collarNeighborhood R C := by
  have h : x.val.val ∈ collarNeighborhood R C ∩ regionClosure R j := by
    rw [collarNeighborhood_inter_closure R C j]
    exact ⟨x.val, x.property, rfl⟩
  exact h.1

def lowerToNeighborhood (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) : C((C j).lower, collarNeighborhood R C) :=
  ⟨fun x => ⟨x.val.val, lower_mem_neighborhood R C j x⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def collarPiece (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    Option (Fin R.regionCount) → Set (unitInterval × collarNeighborhood R C)
  | none => {z | z.2.val ∈ R.graph.carrier}
  | some j => {z | z.2.val ∈ regionClosure R j}

lemma collarPiece_closed (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (i : Option (Fin R.regionCount)) : IsClosed (collarPiece R C i) := by
  cases i with
  | none => exact (graphClosed R.graph).preimage (continuous_subtype_val.comp continuous_snd)
  | some j => exact isClosed_closure.preimage (continuous_subtype_val.comp continuous_snd)

lemma collarPiece_cover (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    (⋃ i, collarPiece R C i) = univ := by
  apply eq_univ_of_forall
  intro z
  have h : z.2.val ∈ R.graph.carrier ∪ ⋃ j, regionClosure R j := by
    rw [regionClosures_cover]; trivial
  rcases h with h | h
  · exact mem_iUnion.mpr ⟨none, h⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨some j, hj⟩

def collarPieceMap (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    ∀ i : Option (Fin R.regionCount), C(collarPiece R C i, collarNeighborhood R C)
  | none => ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩
  | some j =>
    (lowerToNeighborhood R C j).comp ((C j).lowerContraction.comp
      ⟨fun z => (z.val.1, regionLowerPoint R C j z.val.2 z.property), by
        apply Continuous.prodMk
        · exact continuous_fst.comp continuous_subtype_val
        · apply Continuous.subtype_mk
          apply Continuous.subtype_mk
          exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩)

lemma collarPieceMap_fixed (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (i : Option (Fin R.regionCount)) (z : collarPiece R C i)
    (hz : z.val.2.val ∈ R.graph.carrier) : collarPieceMap R C i z = z.val.2 := by
  cases i with
  | none => rfl
  | some j =>
    apply Subtype.ext
    change ((C j).lowerContraction (_, regionLowerPoint R C j z.val.2 z.property)).val.val = _
    rw [(C j).lowerContraction_fixed _ hz]
    rfl

lemma collarPieceMap_agree (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (i k : Option (Fin R.regionCount)) (z : unitInterval × collarNeighborhood R C)
    (hi : z ∈ collarPiece R C i) (hk : z ∈ collarPiece R C k) :
    collarPieceMap R C i ⟨z, hi⟩ = collarPieceMap R C k ⟨z, hk⟩ := by
  classical
  by_cases hg : z.2.val ∈ R.graph.carrier
  · rw [collarPieceMap_fixed R C i _ hg, collarPieceMap_fixed R C k _ hg]
  · cases i with
    | none => exact (hg hi).elim
    | some j =>
      cases k with
      | none => exact (hg hk).elim
      | some l =>
        have hj : z.2.val ∈ regionInterior R j := closure_mem_interior_of_not_graph R j hi hg
        have hl : z.2.val ∈ regionInterior R l := closure_mem_interior_of_not_graph R l hk hg
        have h : j = l := by
          by_contra hn
          exact Set.disjoint_left.mp (regionInteriors_disjoint R hn) hj hl
        subst l
        rfl

/-- The collar contractions pasted on the finite closed cover of I × W. -/
def collarContraction (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    C(unitInterval × collarNeighborhood R C, collarNeighborhood R C) where
  toFun := Set.liftCover (collarPiece R C) (fun i => collarPieceMap R C i)
    (collarPieceMap_agree R C) (collarPiece_cover R C)
  continuous_toFun := by
    apply LocallyFinite.continuous (locallyFinite_of_finite _) (collarPiece_cover R C)
      (collarPiece_closed R C)
    intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert (collarPieceMap R C i).continuous using 1
    funext z
    exact Set.liftCover_coe z

lemma collarContraction_piece (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (i : Option (Fin R.regionCount)) (z : unitInterval × collarNeighborhood R C)
    (hi : z ∈ collarPiece R C i) :
    collarContraction R C z = collarPieceMap R C i ⟨z, hi⟩ :=
  Set.liftCover_of_mem (f := fun i => collarPieceMap R C i)
    (hf := collarPieceMap_agree R C) (hS := collarPiece_cover R C) hi

lemma collarContraction_zero (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (x : collarNeighborhood R C) : collarContraction R C (0, x) = x := by
  have h : (0, x) ∈ ⋃ i, collarPiece R C i := by rw [collarPiece_cover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp h
  rw [collarContraction_piece R C i _ hi]
  cases i with
  | none => rfl
  | some j =>
    apply Subtype.ext
    change ((C j).lowerContraction (0, regionLowerPoint R C j x hi)).val.val = _
    rw [(C j).lowerContraction_zero]
    rfl

lemma collarContraction_fixed (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (s : unitInterval) (x : collarNeighborhood R C) (hx : x.val ∈ R.graph.carrier) :
    collarContraction R C (s, x) = x := by
  rw [collarContraction_piece R C none _ hx]
  rfl

lemma collarContraction_one_mem (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (x : collarNeighborhood R C) :
    (collarContraction R C (1, x)).val ∈ R.graph.carrier := by
  have h : (1, x) ∈ ⋃ i, collarPiece R C i := by rw [collarPiece_cover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp h
  rw [collarContraction_piece R C i _ hi]
  cases i with
  | none => exact hi
  | some j =>
    change ((C j).lowerContraction (1, regionLowerPoint R C j x hi)).val.val ∈ R.graph.carrier
    rw [(C j).lowerContraction_one]
    exact ((C j).lowerCoordinates _).1.property.2

end Retraction
section RetractionEquivalence
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

def graphToNeighborhood (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    C(R.graph.carrier, collarNeighborhood R C) :=
  ⟨fun x => ⟨x.val, graph_subset_collarNeighborhood R C x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The endpoint of the explicitly pasted collar contraction. -/
def neighborhoodToGraph (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    C(collarNeighborhood R C, R.graph.carrier) :=
  ⟨fun x => ⟨(collarContraction R C (1, x)).val, collarContraction_one_mem R C x⟩,
    (continuous_subtype_val.comp ((collarContraction R C).continuous.comp
      (continuous_const.prodMk continuous_id))).subtype_mk _⟩

/-- W deformation retracts onto the original embedded graph. Its homotopy
is the collar contraction and the backward map is the actual inclusion. -/
def collarNeighborhoodGraphEquiv (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    ContinuousMap.HomotopyEquiv (collarNeighborhood R C) R.graph.carrier where
  toFun := neighborhoodToGraph R C
  invFun := graphToNeighborhood R C
  left_inv := by
    have H : ContinuousMap.Homotopy (ContinuousMap.id (collarNeighborhood R C))
        ((graphToNeighborhood R C).comp (neighborhoodToGraph R C)) := {
      toContinuousMap := collarContraction R C
      map_zero_left := collarContraction_zero R C
      map_one_left := fun _ => rfl }
    exact ⟨H.symm⟩
  right_inv := by
    have h : (neighborhoodToGraph R C).comp (graphToNeighborhood R C) =
        ContinuousMap.id R.graph.carrier := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      change (collarContraction R C (1, graphToNeighborhood R C x)).val = x.val
      exact congrArg Subtype.val (collarContraction_fixed R C 1
        (graphToNeighborhood R C x) x.property)
    rw [h]

end RetractionEquivalence


section Homology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The isomorphism is induced by the actual forward map of the equivalence. -/
def homotopyHomologyIso (e : ContinuousMap.HomotopyEquiv X Y) (n : ℤ) :
    homology ℚ ℚ (TopCat.of X) n ≅ homology ℚ ℚ (TopCat.of Y) n := by
  let H := Classical.choice e.left_inv
  let K := Classical.choice e.right_inv
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have hfg : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := H
  have hgf : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := K
  refine ⟨(homologyFunctor ℚ ℚ n).map f, (homologyFunctor ℚ ℚ n).map g, ?_, ?_⟩
  · calc
      _ = (homologyFunctor ℚ ℚ n).map (f ≫ g) :=
        ((homologyFunctor ℚ ℚ n).map_comp f g).symm
      _ = (homologyFunctor ℚ ℚ n).map (𝟙 (TopCat.of X)) :=
        (P202.PrismHomotopy.homology ℚ ℚ (f := f ≫ g) (g := 𝟙 _) hfg n).1
      _ = _ := (homologyFunctor ℚ ℚ n).map_id _
  · calc
      _ = (homologyFunctor ℚ ℚ n).map (g ≫ f) :=
        ((homologyFunctor ℚ ℚ n).map_comp g f).symm
      _ = (homologyFunctor ℚ ℚ n).map (𝟙 (TopCat.of Y)) :=
        (P202.PrismHomotopy.homology ℚ ℚ (f := g ≫ f) (g := 𝟙 _) hgf n).1
      _ = _ := (homologyFunctor ℚ ℚ n).map_id _

lemma finiteType_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (h : HomologyFiniteType ℚ Y) : HomologyFiniteType ℚ X := by
  constructor
  · intro n
    haveI := h.1 n
    exact (homotopyHomologyIso e n).toLinearEquiv.symm.finiteDimensional
  · obtain ⟨N, hN⟩ := h.2
    exact ⟨N, fun n hn => (homotopyHomologyIso e n).isZero_iff.mpr (hN n hn)⟩

lemma homologicalEuler_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    homologicalEuler ℚ X = homologicalEuler ℚ Y := by
  unfold homologicalEuler
  congr 1
  funext n
  rw [(homotopyHomologyIso e n).toLinearEquiv.finrank_eq]

lemma topologicalEuler_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (hX : HomologyFiniteType ℚ X) (hY : HomologyFiniteType ℚ Y) :
    topologicalEuler X hX = topologicalEuler Y hY :=
  homologicalEuler_homotopyEquiv e

end Homology

/-- The empty-surface case of the original conclusion, with the complete
ordered construction premise retained. This is a partial-case helper, not the
full conditional target. -/
theorem emptySurface_conditional
    (construction : P202Specs.SurfaceRegionConstruction.Expected.construction.{u}) :
    ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M] [IsEmpty M]
      (S : SmoothManifold 2 kind M),
      ∃ R : RegionDecomposition S, EulerConclusion R := by
  intro kind M _ _ _ S
  obtain ⟨R⟩ := construction S
  obtain ⟨hV, hE, hR⟩ := R.empty_case inferInstance
  haveI : IsEmpty (Fin R.regionCount) := by rw [hR]; infer_instance
  obtain ⟨hS, hχ⟩ := P202.Homology.EulerPoincare.emptyFormula M
  refine ⟨R, hS, fun j => isEmptyElim j, ?_⟩
  simp [hχ, hV, hE]

end P202.SurfaceRegionsEuler

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open P202Specs.EulerPoincare P202Specs.SingularChains
namespace P202.SurfaceRegionsEuler

lemma chainTransport_d (R : Type u) [CommRing R]
    {X : TopCat.{v}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (i j : ℕ) (z : Chains R X i) :
    P202.LocalOrientation.chainsHomeomorphEquiv R e j ((complex R R X).d i j z) =
      (complex R R Y).d i j (P202.LocalOrientation.chainsHomeomorphEquiv R e i z) := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · change j + 1 = i at h
    subst i
    exact P202.LocalOrientation.chainsHomeomorphEquiv_boundary R e j z
  · rw [(complex R R X).shape i j h, (complex R R Y).shape i j h]
    change P202.LocalOrientation.chainsHomeomorphEquiv R e j 0 = 0
    exact map_zero _

def homeomorphHomologyEquiv (R : Type u) [CommRing R]
    {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    homology R R (TopCat.of X) (n : ℤ) ≃ₗ[R] homology R R (TopCat.of Y) (n : ℤ) := by
  let ex := ((complex R R (TopCat.of X)).extendHomologyIso (degreeEmbedding 0)
    (show (degreeEmbedding 0).f n = (n : ℤ) by simp [degreeEmbedding])).toLinearEquiv
  let ey := ((complex R R (TopCat.of Y)).extendHomologyIso (degreeEmbedding 0)
    (show (degreeEmbedding 0).f n = (n : ℤ) by simp [degreeEmbedding])).toLinearEquiv
  exact ex.trans ((P202.LocalOrientation.homologyLinearEquiv R (complex R R (TopCat.of X))
    (complex R R (TopCat.of Y))
    (P202.LocalOrientation.chainsHomeomorphEquiv R (X := TopCat.of X) (Y := TopCat.of Y) e)
    (chainTransport_d R (X := TopCat.of X) (Y := TopCat.of Y) e) n).trans ey.symm)

lemma finiteType_homeomorph {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (h : HomologyFiniteType ℚ Y) : HomologyFiniteType ℚ X := by
  constructor
  · intro n
    haveI := h.1 n
    exact (homeomorphHomologyEquiv ℚ e n).symm.finiteDimensional
  · obtain ⟨N, hN⟩ := h.2
    refine ⟨N, fun n hn => ?_⟩
    haveI := ModuleCat.subsingleton_of_isZero (hN n hn)
    haveI : Subsingleton (homology ℚ ℚ (TopCat.of X) (n : ℤ)) :=
      (homeomorphHomologyEquiv ℚ e n).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

lemma euler_homeomorph {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    homologicalEuler ℚ X = homologicalEuler ℚ Y := by
  unfold homologicalEuler
  congr 1
  funext n
  rw [(homeomorphHomologyEquiv ℚ e n).finrank_eq]

end P202.SurfaceRegionsEuler

end

section
open P202.Cellular P202Specs.SurfaceRegionConstruction
namespace P202.SurfaceRegionsEuler
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

abbrev edgeParameters := {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}

def graphEdge (G : EmbeddedGraph S) (i : Fin G.edgeCount) : C(unitInterval, G.carrier) :=
  ⟨fun t => ⟨G.edge i t, Or.inr (mem_iUnion.mpr ⟨i, ⟨t,rfl⟩⟩)⟩,
    (G.edge i).continuous.subtype_mk _⟩

lemma graphEdge_saturated (G : EmbeddedGraph S) (i : Fin G.edgeCount) :
    graphEdge G i ⁻¹' (graphEdge G i '' (Set.univ : Set edgeParameters).image Subtype.val) =
      (Set.univ : Set edgeParameters).image Subtype.val := by
  ext t
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨s, ⟨a, rfl⟩, he⟩
    refine ⟨⟨t, ?_⟩, rfl⟩
    have hnot : G.edge i t ∉ range G.vertex := by
      change (graphEdge G i t).val ∉ range G.vertex
      rw [← congrArg Subtype.val he]
      exact G.avoids_vertices i a.val a.property.1 a.property.2
    constructor
    · by_contra h
      have ht : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
      rw [ht, G.at_zero] at hnot
      exact hnot ⟨_,rfl⟩
    · by_contra h
      have ht : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h))
      rw [ht, G.at_one] at hnot
      exact hnot ⟨_,rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, ⟨a,rfl⟩,rfl⟩

lemma graphEdge_interior_embedding (G : EmbeddedGraph S) (i : Fin G.edgeCount) :
    IsEmbedding (fun t : edgeParameters => graphEdge G i t.val) := by
  haveI := S.topologicalManifold.hausdorff
  let U : Set unitInterval := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  have hsat : graphEdge G i ⁻¹' (graphEdge G i '' U) = U := by
    simpa [U] using graphEdge_saturated G i
  exact P202.Topology.isEmbedding_restrict_of_isClosedMap _ (graphEdge G i).continuous
    (graphEdge G i).continuous.isClosedMap U hsat (fun _ hx _ hy h =>
      G.open_injective i hx hy (congrArg Subtype.val h))

lemma norm_one_coordinate (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

-- Explicit affine parametrization of the one-dimensional Euclidean disk.
def diskOneTime (p : Disk 1) : unitInterval :=
  ⟨(p.val 0 + 1) / 2, by
    have hp : |p.val 0| ≤ 1 := by
      have hp : ‖p.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using p.property
      rwa [norm_one_coordinate] at hp
    constructor <;> linarith [abs_le.mp hp]⟩

lemma continuous_diskOneTime : Continuous diskOneTime := by
  unfold diskOneTime
  fun_prop

lemma diskOneTime_injective : Function.Injective diskOneTime := by
  intro p q h
  apply Subtype.ext
  ext i
  fin_cases i
  have := congrArg Subtype.val h
  dsimp [diskOneTime] at this
  change (p.val 0) = (q.val 0)
  linarith

lemma diskOneTime_surjective : Function.Surjective diskOneTime := by
  intro t
  let v : EuclideanSpace ℝ (Fin 1) := (WithLp.toLp 2 (fun _ => 2 * t.val - 1))
  have hv : v ∈ Metric.closedBall 0 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [norm_one_coordinate]
    change |2*t.val-1| ≤ 1
    rw [abs_le]
    constructor <;> linarith [t.property.1,t.property.2]
  refine ⟨⟨v,hv⟩, ?_⟩
  apply Subtype.ext
  simp [diskOneTime,v]

def diskOneHomeomorph : Disk 1 ≃ₜ unitInterval :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective diskOneTime ⟨diskOneTime_injective,diskOneTime_surjective⟩)
    continuous_diskOneTime

lemma diskOneTime_interior (p : Disk 1) :
    (0 < (diskOneTime p : ℝ) ∧ (diskOneTime p : ℝ) < 1) ↔ ‖p.val‖ < 1 := by
  rw [norm_one_coordinate, abs_lt]
  dsimp [diskOneTime]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith


inductive GraphCell (G : EmbeddedGraph S) : ℕ → Type u where
  | vertex (i : Fin G.vertexCount) : GraphCell G 0
  | edge (i : Fin G.edgeCount) : GraphCell G 1

@[instance_reducible] def graphCells (G : EmbeddedGraph S) : CellStructure G.carrier where
  Cell := GraphCell G
  characteristic := fun n c => match c with
    | .vertex i => ContinuousMap.const _ ⟨G.vertex i, Or.inl ⟨i,rfl⟩⟩
    | .edge i => (graphEdge G i).comp ⟨diskOneHomeomorph, diskOneHomeomorph.continuous⟩

lemma graphCells_openVertex (G : EmbeddedGraph S) (i : Fin G.vertexCount) :
    @openCell G.carrier _ (graphCells G) 0 (.vertex i) =
      {⟨G.vertex i, Or.inl ⟨i,rfl⟩⟩} := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, by simp⟩,rfl⟩

lemma graphCells_openEdge (G : EmbeddedGraph S) (i : Fin G.edgeCount) :
    @openCell G.carrier _ (graphCells G) 1 (.edge i) =
      graphEdge G i '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨diskOneTime (interiorInclusion 1 p),
      (diskOneTime_interior _).mpr (by simpa only [Metric.mem_ball, dist_zero_right, interiorInclusion] using p.property),rfl⟩
  · rintro ⟨t,ht,rfl⟩
    let p := diskOneHomeomorph.symm t
    have hp : ‖p.val‖ < 1 := (diskOneTime_interior p).mp (by
      change 0 < (diskOneHomeomorph p : ℝ) ∧ (diskOneHomeomorph p : ℝ) < 1
      simpa [p] using ht)
    refine ⟨⟨p.val, by simpa using hp⟩, ?_⟩
    change graphEdge G i (diskOneHomeomorph p) = graphEdge G i t
    rw [diskOneHomeomorph.apply_symm_apply]

lemma interiorInclusion_embedding (n : ℕ) : IsEmbedding (interiorInclusion n) :=
  IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal

lemma graphCells_interior_embedding (G : EmbeddedGraph S) :
    ∀ n (c : @Cell G.carrier _ (graphCells G) n),
      IsEmbedding (@interiorMap G.carrier _ (graphCells G) n c) := by
  intro n c
  cases c with
  | vertex i =>
    haveI : Subsingleton (OpenDisk 0) := inferInstance
    exact IsEmbedding.of_subsingleton _
  | edge i =>
    let f : OpenDisk 1 → edgeParameters := fun p =>
      ⟨diskOneTime (interiorInclusion 1 p),
        (diskOneTime_interior _).mpr (by simpa only [Metric.mem_ball, dist_zero_right, interiorInclusion] using p.property)⟩
    have hf : IsEmbedding f := IsEmbedding.of_comp
      ((continuous_diskOneTime.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _)
      continuous_subtype_val (diskOneHomeomorph.isEmbedding.comp (interiorInclusion_embedding 1))
    exact (graphEdge_interior_embedding G i).comp hf


def graphTotalCellEquiv (G : EmbeddedGraph S) :
    (Σ n, GraphCell G n) ≃ Fin G.vertexCount ⊕ Fin G.edgeCount where
  toFun x := match x with
    | ⟨_, .vertex i⟩ => Sum.inl i
    | ⟨_, .edge i⟩ => Sum.inr i
  invFun x := match x with
    | Sum.inl i => ⟨0, .vertex i⟩
    | Sum.inr i => ⟨1, .edge i⟩
  left_inv x := by rcases x with ⟨n,c⟩; cases c <;> rfl
  right_inv x := by cases x <;> rfl

instance graphTotalCellFinite (G : EmbeddedGraph S) : Finite (Σ n, GraphCell G n) :=
  Finite.of_equiv _ (graphTotalCellEquiv G).symm

lemma graphCells_cover (G : EmbeddedGraph S) :
    ⋃ (n : ℕ) (c : @Cell G.carrier _ (graphCells G) n),
      @openCell G.carrier _ (graphCells G) n c = univ := by
  apply eq_univ_of_forall
  intro x
  obtain hx | hx := x.property
  · obtain ⟨i,hi⟩ := hx
    refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨.vertex i,?_⟩⟩
    rw [graphCells_openVertex]
    exact Subtype.ext hi.symm
  · obtain ⟨i,t,ht⟩ := mem_iUnion.mp hx
    by_cases ht0 : t = 0
    · subst t
      refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨.vertex (G.initial i),?_⟩⟩
      rw [graphCells_openVertex]
      apply Subtype.ext
      exact ht.symm.trans (G.at_zero i)
    · by_cases ht1 : t = 1
      · subst t
        refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨.vertex (G.terminal i),?_⟩⟩
        rw [graphCells_openVertex]
        apply Subtype.ext
        exact ht.symm.trans (G.at_one i)
      · refine mem_iUnion.mpr ⟨1,mem_iUnion.mpr ⟨.edge i,?_⟩⟩
        rw [graphCells_openEdge]
        refine ⟨t, ⟨?_, ?_⟩, Subtype.ext ht⟩
        · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
        · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))

lemma graphCells_disjoint (G : EmbeddedGraph S) :
    (univ : Set (Σ n, @Cell G.carrier _ (graphCells G) n)).PairwiseDisjoint
      (fun c => @openCell G.carrier _ (graphCells G) c.1 c.2) := by
  intro a _ b _ hab
  rcases a with ⟨n,c⟩
  rcases b with ⟨m,d⟩
  dsimp only [Function.onFun]
  cases c with
  | vertex i =>
    cases d with
    | vertex j =>
      rw [graphCells_openVertex,graphCells_openVertex]
      apply Set.disjoint_singleton.mpr
      intro he
      apply hab
      have hij := G.vertex_injective (congrArg Subtype.val he)
      subst j
      rfl
    | edge j =>
      rw [graphCells_openVertex,graphCells_openEdge]
      apply Set.disjoint_left.mpr
      rintro x rfl ⟨t,ht,he⟩
      exact G.avoids_vertices j t ht.1 ht.2 ⟨i, (congrArg Subtype.val he).symm⟩
  | edge i =>
    cases d with
    | vertex j =>
      rw [graphCells_openEdge,graphCells_openVertex]
      apply Set.disjoint_left.mpr
      rintro x ⟨t,ht,he⟩ rfl
      exact G.avoids_vertices i t ht.1 ht.2 ⟨j, (congrArg Subtype.val he).symm⟩
    | edge j =>
      rw [graphCells_openEdge,graphCells_openEdge]
      have hij : i ≠ j := fun h => by subst j; exact hab rfl
      apply Set.disjoint_left.mpr
      rintro x ⟨t,ht,he⟩ ⟨s,hs,hf⟩
      exact Set.disjoint_left.mp (G.disjoint_open_edges hij)
        ⟨t,ht,congrArg Subtype.val he⟩ ⟨s,hs,congrArg Subtype.val hf⟩

lemma graphCells_boundary (G : EmbeddedGraph S) :
    ∀ n (c : @Cell G.carrier _ (graphCells G) n),
      MapsTo (@boundaryMap G.carrier _ (graphCells G) n c) univ
        (@skeletonLT G.carrier _ (graphCells G) n) := by
  intro n c
  cases c with
  | vertex i =>
    rintro ⟨v,hv⟩ _
    have hnorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    have hv0 : v = 0 := Subsingleton.elim _ _
    simp [hv0] at hnorm
  | edge i =>
    intro p _
    have hnorm : ‖p.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using p.property
    have ht : diskOneTime (boundaryInclusion 1 p) = 0 ∨
        diskOneTime (boundaryInclusion 1 p) = 1 := by
      rw [norm_one_coordinate,abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hnorm
      rcases hnorm with h | h
      · right; apply Subtype.ext; dsimp [diskOneTime,boundaryInclusion]; linarith
      · left; apply Subtype.ext; dsimp [diskOneTime,boundaryInclusion]; linarith
    rcases ht with ht | ht
    · refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by omega,
        mem_iUnion.mpr ⟨.vertex (G.initial i),?_⟩⟩⟩
      rw [graphCells_openVertex]
      apply Subtype.ext
      change G.edge i (diskOneTime (boundaryInclusion 1 p)) = _
      rw [ht,G.at_zero]
    · refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by omega,
        mem_iUnion.mpr ⟨.vertex (G.terminal i),?_⟩⟩⟩
      rw [graphCells_openVertex]
      apply Subtype.ext
      change G.edge i (diskOneTime (boundaryInclusion 1 p)) = _
      rw [ht,G.at_one]


def graphProjection (G : EmbeddedGraph S) :
    Fin G.vertexCount ⊕ (Σ _ : Fin G.edgeCount, unitInterval) → G.carrier :=
  Sum.elim (fun i => ⟨G.vertex i, Or.inl ⟨i,rfl⟩⟩) (fun p => graphEdge G p.1 p.2)

lemma graphProjection_continuous (G : EmbeddedGraph S) : Continuous (graphProjection G) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · exact continuous_sigma fun i => (graphEdge G i).continuous

lemma graphProjection_surjective (G : EmbeddedGraph S) : Function.Surjective (graphProjection G) := by
  intro x
  obtain hx | hx := x.property
  · obtain ⟨i,hi⟩ := hx
    exact ⟨Sum.inl i,Subtype.ext hi⟩
  · obtain ⟨i,t,ht⟩ := mem_iUnion.mp hx
    exact ⟨Sum.inr ⟨i,t⟩,Subtype.ext ht⟩

lemma graphCells_weak (G : EmbeddedGraph S) :
    ∀ A : Set G.carrier, IsClosed A ↔
      ∀ n (c : @Cell G.carrier _ (graphCells G) n),
        IsClosed (@characteristic G.carrier _ (graphCells G) n c ⁻¹' A) := by
  haveI := S.topologicalManifold.hausdorff
  intro A
  constructor
  · intro h n c
    exact h.preimage (@characteristic G.carrier _ (graphCells G) n c).continuous
  · intro h
    have hq : IsQuotientMap (graphProjection G) :=
      IsQuotientMap.of_surjective_continuous (graphProjection_surjective G)
        (graphProjection_continuous G)
    apply hq.isCoinducing.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    constructor
    · exact isClosed_discrete _
    · apply isClosed_sigma_iff.mpr
      intro i
      have hi := h 1 (.edge i)
      have he : graphEdge G i ⁻¹' A =
          diskOneHomeomorph.symm ⁻¹'
            (@characteristic G.carrier _ (graphCells G) 1 (.edge i) ⁻¹' A) := by
        ext t
        change graphEdge G i t ∈ A ↔ graphEdge G i
          (diskOneHomeomorph (diskOneHomeomorph.symm t)) ∈ A
        rw [diskOneHomeomorph.apply_symm_apply]
      change IsClosed (graphEdge G i ⁻¹' A)
      rw [he]
      exact hi.preimage diskOneHomeomorph.symm.continuous

lemma graphCells_closure_finite (G : EmbeddedGraph S) :
    ∀ n (c : @Cell G.carrier _ (graphCells G) n),
      ∃ F : Finset (Σ m, @Cell G.carrier _ (graphCells G) m),
        @closedCell G.carrier _ (graphCells G) n c ⊆
          ⋃ d ∈ F, @openCell G.carrier _ (graphCells G) d.1 d.2 := by
  classical
  letI : Fintype (Σ m, GraphCell G m) := Fintype.ofFinite _
  intro n c
  refine ⟨Finset.univ, ?_⟩
  intro x _
  have hx : x ∈ ⋃ (n : ℕ) (c : @Cell G.carrier _ (graphCells G) n),
      @openCell G.carrier _ (graphCells G) n c := by rw [graphCells_cover]; trivial
  obtain ⟨m,d,hd⟩ := mem_iUnion.mp hx |>.imp fun _ => mem_iUnion.mp
  exact mem_iUnion.mpr ⟨⟨m,d⟩,mem_iUnion.mpr ⟨Finset.mem_univ _,hd⟩⟩

@[instance_reducible] def graphCWStructure (G : EmbeddedGraph S) : CWStructure G.carrier := by
  haveI := S.topologicalManifold.hausdorff
  letI := graphCells G
  exact P202.Topology.cwStructureOfWeak (graphCells_interior_embedding G)
    (graphCells_disjoint G) (graphCells_cover G) (graphCells_boundary G)
    (graphCells_closure_finite G) (graphCells_weak G)


def graphVertexEquiv (G : EmbeddedGraph S) : GraphCell G 0 ≃ Fin G.vertexCount where
  toFun c := by cases c with | vertex i => exact i
  invFun := .vertex
  left_inv c := by cases c; rfl
  right_inv _ := rfl

def graphEdgeEquiv (G : EmbeddedGraph S) : GraphCell G 1 ≃ Fin G.edgeCount where
  toFun c := by cases c with | edge i => exact i
  invFun := .edge
  left_inv c := by cases c; rfl
  right_inv _ := rfl

lemma graphCells_noHigher (G : EmbeddedGraph S) (n : ℕ) (hn : 2 ≤ n) :
    IsEmpty (GraphCell G n) := by
  constructor
  intro c
  cases c <;> omega

lemma graphCells_vertex_card (G : EmbeddedGraph S) : Nat.card (GraphCell G 0) = G.vertexCount := by
  rw [Nat.card_congr (graphVertexEquiv G)]
  exact Nat.card_fin _

lemma graphCells_edge_card (G : EmbeddedGraph S) : Nat.card (GraphCell G 1) = G.edgeCount := by
  rw [Nat.card_congr (graphEdgeEquiv G)]
  exact Nat.card_fin _


theorem graphEuler
    (G : EmbeddedGraph S) :
    ∃ h : P202Specs.EulerPoincare.HomologyFiniteType ℚ G.carrier,
      P202Specs.EulerPoincare.topologicalEuler G.carrier h =
        (G.vertexCount : ℤ) - (G.edgeCount : ℤ) := by
  letI := graphCWStructure G
  obtain ⟨h,hχ⟩ := P202.Homology.EulerPoincare.graphFormula G.carrier (graphTotalCellFinite G) (graphCells_noHigher G)
  change P202Specs.EulerPoincare.topologicalEuler G.carrier h =
    (Nat.card (GraphCell G 0) : ℤ) - (Nat.card (GraphCell G 1) : ℤ) at hχ
  exact ⟨h, by simpa only [graphCells_vertex_card,graphCells_edge_card] using hχ⟩

end P202.SurfaceRegionsEuler

end

section
open P202Specs.EulerPoincare P202Specs.SingularChains
namespace P202.SurfaceRegionsEuler
variable {F : Type u} [Field F]

lemma exactMiddleFiniteDimensional (S : ShortComplex (ModuleCat.{v} F))
    (hS : S.Exact) [FiniteDimensional F S.X₁] [FiniteDimensional F S.X₃] :
    FiniteDimensional F S.X₂ := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  exact Module.Finite.of_exact h.linearMap_rangeRestrict S.g.hom.surjective_rangeRestrict

lemma exactMiddleZero (S : ShortComplex (ModuleCat.{v} F))
    (hS : S.Exact) (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ := by
  haveI := ModuleCat.subsingleton_of_isZero h₁
  haveI := ModuleCat.subsingleton_of_isZero h₃
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  have hxg : S.g x = 0 := Subsingleton.elim _ _
  have hyg : S.g y = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := (S.moduleCat_exact_iff.mp hS) x hxg
  obtain ⟨b, hb⟩ := (S.moduleCat_exact_iff.mp hS) y hyg
  rw [← ha, ← hb, Subsingleton.elim a b]

lemma exactMiddleDimension (S : ShortComplex (ModuleCat.{v} F))
    (hS : S.Exact) [FiniteDimensional F S.X₂] :
    Module.finrank F S.X₂ = Module.finrank F (LinearMap.range S.f.hom) +
      Module.finrank F (LinearMap.range S.g.hom) := by
  have hd := S.g.hom.finrank_range_add_finrank_ker
  rw [← hS.moduleCat_range_eq_ker] at hd
  omega

end P202.SurfaceRegionsEuler

end

section
open P202Specs.EulerPoincare P202Specs.SingularChains P202Specs.PlanarRegionTopology
namespace P202.SurfaceRegionsEuler

section FiniteDisjointUnion
variable {I : Type u} [Fintype I] (X : I → TopCat.{u})

lemma sigmaHomologyFiniteDimensional (h : ∀ i, HomologyFiniteType ℚ (X i)) (n : ℕ) :
    FiniteDimensional ℚ (homology ℚ ℚ (TopCat.of (Σ i, X i)) (n : ℤ)) := by
  haveI := fun i => (h i).1 n
  let e := (P202.OrdinaryHomologyAxioms.homologyDirectSumIso X ℚ ℚ n).toLinearEquiv
  haveI : FiniteDimensional ℚ (DirectSum I (fun i => homology ℚ ℚ (X i) (n : ℤ))) :=
    (DirectSum.linearEquivFunOnFintype ℚ I _).symm.finiteDimensional
  exact e.finiteDimensional

lemma sigmaHomologyZero (n : ℕ)
    (hz : ∀ i, IsZero (homology ℚ ℚ (X i) (n : ℤ))) :
    IsZero (homology ℚ ℚ (TopCat.of (Σ i, X i)) (n : ℤ)) := by
  haveI := fun i => ModuleCat.subsingleton_of_isZero (hz i)
  apply (P202.OrdinaryHomologyAxioms.homologyDirectSumIso X ℚ ℚ n).isZero_iff.mp
  apply ModuleCat.isZero_iff_subsingleton.mpr
  infer_instance

lemma sigmaHomologyFiniteType (h : ∀ i, HomologyFiniteType ℚ (X i)) :
    HomologyFiniteType ℚ (Σ i, X i) := by
  refine ⟨sigmaHomologyFiniteDimensional X h, ?_⟩
  let N : I → ℕ := fun i => Classical.choose (h i).2
  refine ⟨Finset.univ.sup N, fun n hn => sigmaHomologyZero X n ?_⟩
  intro i
  apply Classical.choose_spec (h i).2
  exact le_trans (Finset.le_sup (f := N) (Finset.mem_univ i)) hn

lemma sigmaHomologyFinrank (h : ∀ i, HomologyFiniteType ℚ (X i)) (n : ℕ) :
    Module.finrank ℚ (homology ℚ ℚ (TopCat.of (Σ i, X i)) (n : ℤ)) =
      ∑ i, Module.finrank ℚ (homology ℚ ℚ (X i) (n : ℤ)) := by
  haveI := fun i => (h i).1 n
  rw [← (P202.OrdinaryHomologyAxioms.homologyDirectSumIso X ℚ ℚ n).toLinearEquiv.finrank_eq]
  exact Module.finrank_directSum (R := ℚ) (fun i : I => homology ℚ ℚ (X i) (n : ℤ))

lemma sigmaHomologicalEuler (h : ∀ i, HomologyFiniteType ℚ (X i)) :
    homologicalEuler ℚ (Σ i, X i) = ∑ i, homologicalEuler ℚ (X i) := by
  let N : I → ℕ := fun i => Classical.choose (h i).2
  let B := Finset.univ.sup N
  have hz (i : I) (n : ℕ) (hn : B ≤ n) : IsZero (homology ℚ ℚ (X i) (n : ℤ)) := by
    apply Classical.choose_spec (h i).2
    exact le_trans (Finset.le_sup (f := N) (Finset.mem_univ i)) hn
  have hzs (n : ℕ) (hn : B ≤ n) :
      IsZero (homology ℚ ℚ (TopCat.of (Σ i, X i)) (n : ℤ)) := sigmaHomologyZero X n (fun i => hz i n hn)
  rw [P202.Homology.EulerPoincare.homologicalSum (Σ i, X i) ℚ B hzs]
  simp_rw [sigmaHomologyFinrank X h, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (P202.Homology.EulerPoincare.homologicalSum (X i) ℚ B (hz i)).symm

end FiniteDisjointUnion
end P202.SurfaceRegionsEuler

end

section
open P202Specs.EulerPoincare P202Specs.SingularChains P202Specs.PlanarRegionTopology
namespace P202.SurfaceRegionsEuler

def boundaryCirclesMap (R : PlanarRegion) : (Σ i : Fin R.boundaryCount, ParameterCircle) → R.boundary :=
  fun z => ⟨(R.curve z.1).parametrization z.2, by
    change (R.curve z.1).parametrization z.2 ∈ frontier R.domain
    rw [R.boundary_eq]
    exact mem_iUnion.mpr ⟨z.1, ⟨z.2, rfl⟩⟩⟩

lemma boundaryCirclesMap_bijective (R : PlanarRegion) :
    Function.Bijective (boundaryCirclesMap R) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : (R.curve i).parametrization x = (R.curve j).parametrization y := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (R.disjoint_curves hn) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
    subst j
    exact congrArg (Sigma.mk i) ((R.curve i).injective hxy)
  · intro x
    have hx : x.val ∈ ⋃ i, (R.curve i).trace := by
      rw [← R.boundary_eq]
      exact x.property
    obtain ⟨i, y, hy⟩ := mem_iUnion.mp hx
    exact ⟨⟨i, y⟩, Subtype.ext hy⟩

def boundaryCirclesHomeomorph (R : PlanarRegion) :
    (Σ i : Fin R.boundaryCount, ParameterCircle) ≃ₜ R.boundary := by
  let e := Equiv.ofBijective (boundaryCirclesMap R) (boundaryCirclesMap_bijective R)
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (continuous_sigma fun i => (R.curve i).parametrization.continuous.subtype_mk _)

end P202.SurfaceRegionsEuler

end

section
open P202Specs.EulerPoincare P202Specs.SingularChains P202Specs.PlanarRegionTopology
namespace P202.SurfaceRegionsEuler

def parameterCircleHomologyIso (n : ℤ) :
    homology ℚ ℚ (TopCat.of ParameterCircle) n ≅
      homology ℚ ℚ (P202Specs.SpheresDisks.sphere 1) n :=
  (homologyFunctor ℚ ℚ n).mapIso (TopCat.isoOfHomeo
    (Classical.choice P202.PlanarRegionTopology.parameterCircleSphere))

def parameterCircleDegreeZero : homology ℚ ℚ (TopCat.of ParameterCircle) 0 ≃ₗ[ℚ] ℚ := by
  haveI := P202.SpheresDisks.sphere_pathConnected 0
  let e := Classical.choice (P202.SingularDegreeZero.degreeZero ℚ ℚ (P202Specs.SpheresDisks.sphere 1))
  exact (parameterCircleHomologyIso 0).toLinearEquiv.trans
    (e.trans (Finsupp.uniqueLinearEquiv ℚ ℚ
      (Classical.choice (inferInstance : Nonempty (ZerothHomotopy (P202Specs.SpheresDisks.sphere 1))))))

def parameterCircleDegreeOne : homology ℚ ℚ (TopCat.of ParameterCircle) 1 ≃ₗ[ℚ] ℚ := by
  let e := Classical.choice ((P202.SpheresDisks.sphereHomology ℚ ℚ 1 1).1 rfl)
  exact (parameterCircleHomologyIso 1).toLinearEquiv.trans
    ((P202.SingularDegreeZero.reducedPositiveIso ℚ ℚ (P202Specs.SpheresDisks.sphere 1) 1
      (by norm_num)).symm.toLinearEquiv.trans e)

lemma parameterCircleHomologyHigh (n : ℕ) (hn : 2 ≤ n) :
    IsZero (homology ℚ ℚ (TopCat.of ParameterCircle) (n : ℤ)) := by
  apply (parameterCircleHomologyIso n).isZero_iff.mpr
  apply (P202.SingularDegreeZero.reducedPositiveIso ℚ ℚ
    (P202Specs.SpheresDisks.sphere 1) n (by omega)).isZero_iff.mp
  exact (P202.SpheresDisks.sphereHomology ℚ ℚ 1 n).2 (by omega)

lemma parameterCircleFiniteType : HomologyFiniteType ℚ ParameterCircle := by
  refine ⟨?_, 2, parameterCircleHomologyHigh⟩
  intro n
  cases n with
  | zero => exact parameterCircleDegreeZero.symm.finiteDimensional
  | succ n =>
    cases n with
    | zero => exact parameterCircleDegreeOne.symm.finiteDimensional
    | succ n =>
      haveI := ModuleCat.subsingleton_of_isZero (parameterCircleHomologyHigh (n+2) (by omega))
      infer_instance

lemma parameterCircleHomologicalEuler : homologicalEuler ℚ ParameterCircle = 0 := by
  have hz : ∀ n : ℕ, 2 ≤ n → IsZero (homology ℚ ℚ (TopCat.of ParameterCircle) (n : ℤ)) :=
    parameterCircleHomologyHigh
  have hs : homologicalEuler ℚ ParameterCircle =
      ∑ n ∈ Finset.range 2, (-1 : ℤ)^n *
        (Module.finrank ℚ (homology ℚ ℚ (TopCat.of ParameterCircle) (n : ℤ)) : ℤ) := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    by_contra hlt
    have hne : n ∉ Function.support (fun n : ℕ => (-1 : ℤ)^n *
      (Module.finrank ℚ (homology ℚ ℚ (TopCat.of ParameterCircle) (n : ℤ)) : ℤ)) := by
      haveI := ModuleCat.subsingleton_of_isZero (hz n (by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hlt))
      simp [Module.finrank_zero_of_subsingleton]
    exact hne hn
  rw [hs]
  have hd0 := parameterCircleDegreeZero.finrank_eq
  have hd1 := parameterCircleDegreeOne.finrank_eq
  simp only [Module.finrank_self] at hd0 hd1
  simp [Finset.sum_range_succ, hd0, hd1]

lemma parameterCircleEuler : topologicalEuler ParameterCircle parameterCircleFiniteType = 0 :=
  parameterCircleHomologicalEuler

end P202.SurfaceRegionsEuler

end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open P202Specs.EulerPoincare P202Specs.SingularChains P202Specs.MayerVietoris
namespace P202.SurfaceRegionsEuler

lemma finiteType_openCover {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hfU : HomologyFiniteType ℚ U) (hfV : HomologyFiniteType ℚ V)
    (hfI : HomologyFiniteType ℚ (U ∩ V : Set X)) : HomologyFiniteType ℚ X := by
  let P : P202Specs.RelativeSingularChains.Pair := ⟨TopCat.of X, ∅⟩
  let C := CoverPair.ofSets.{u,0} P U V hU hV hcover
  let F := theoryFunctor ℚ .ordinary
  obtain ⟨⟨δ, hδ, _, _⟩, _⟩ := P202.MayerVietoris.mayerVietoris.{0,u,0} ℚ .ordinary
  have hmiddle (n : ℕ) : FiniteDimensional ℚ (homologyMiddle F C (n : ℤ)) := by
    haveI := hfU.1 n
    haveI := hfV.1 n
    let A : ModuleCat.{u} ℚ := homology ℚ ℚ (TopCat.of U) (n : ℤ)
    let B : ModuleCat.{u} ℚ := homology ℚ ℚ (TopCat.of V) (n : ℤ)
    change FiniteDimensional ℚ (A ⊞ B : ModuleCat.{u} ℚ)
    exact (ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv.finiteDimensional
  constructor
  · intro n
    cases n with
    | zero =>
      have hs := hδ.1 C (-1)
      let S := hs.sc 1
      haveI : FiniteDimensional ℚ S.X₁ := hmiddle 0
      have hzero : IsZero S.X₃ :=
        P202.SingularChains.ordinary_negative_homology ℚ ℚ (TopCat.of (U ∩ V : Set X)) (-1) (by omega)
      haveI := ModuleCat.subsingleton_of_isZero hzero
      exact exactMiddleFiniteDimensional S (hs.exact 1)
    | succ n =>
      have hs := hδ.1 C (n : ℤ)
      let S := hs.sc 1
      haveI : FiniteDimensional ℚ S.X₁ := hmiddle (n+1)
      haveI : FiniteDimensional ℚ S.X₃ := hfI.1 n
      exact exactMiddleFiniteDimensional S (hs.exact 1)
  · obtain ⟨NU, hNU⟩ := hfU.2
    obtain ⟨NV, hNV⟩ := hfV.2
    obtain ⟨NI, hNI⟩ := hfI.2
    refine ⟨max (max NU NV) (NI+1), ?_⟩
    intro n hn
    have hnI : NI + 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hs := hδ.1 C (m : ℤ)
    let S := hs.sc 1
    have hzU := hNU (m+1) (by omega)
    have hzV := hNV (m+1) (by omega)
    have hzu : IsZero ((F.obj C.leftPair).homology ((m : ℤ)+1)) := hzU
    have hzv : IsZero ((F.obj C.rightPair).homology ((m : ℤ)+1)) := hzV
    haveI := ModuleCat.subsingleton_of_isZero hzu
    haveI := ModuleCat.subsingleton_of_isZero hzv
    have hzB : IsZero S.X₁ := by
      exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (ModuleCat.biprodIsoProd _ _)
    have hzI : IsZero S.X₃ := hNI m (by omega)
    exact exactMiddleZero S (hs.exact 1) hzB hzI

end P202.SurfaceRegionsEuler

end

section
open P202Specs.EulerPoincare P202Specs.SingularChains
namespace P202.SurfaceRegionsEuler
section Regions
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
variable {kind : ModelKind} {M : Type v} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

theorem regionFiniteType (R : RegionDecomposition S) (j : Fin R.regionCount) :
    HomologyFiniteType ℚ (regionClosure R j) :=
  finiteType_homeomorph (regionClosureHomeomorph R j)
    (Classical.choose (P202.PlanarRegionEuler.planarRegionEuler (R.region j)))

lemma regionEuler_model (R : RegionDecomposition S) (j : Fin R.regionCount)
    (hD : HomologyFiniteType ℚ (regionClosure R j))
    (hP : HomologyFiniteType ℚ (R.region j).carrier) :
    topologicalEuler (regionClosure R j) hD = topologicalEuler (R.region j).carrier hP :=
  euler_homeomorph (regionClosureHomeomorph R j)

lemma regionEuler (R : RegionDecomposition S) (j : Fin R.regionCount)
    (hD : HomologyFiniteType ℚ (regionClosure R j)) :
    topologicalEuler (regionClosure R j) hD = 2 - ((R.region j).boundaryCount : ℤ) := by
  obtain ⟨hP, hχ, _⟩ := P202.PlanarRegionEuler.planarRegionEuler (R.region j)
  exact (regionEuler_model R j hD hP).trans hχ

lemma regionInteriorFiniteType (R : RegionDecomposition S) (j : Fin R.regionCount) :
    HomologyFiniteType ℚ (regionInterior R j) := by
  obtain ⟨e, _⟩ := regionInteriorClosureEquivalence R j
  exact finiteType_of_homotopyEquiv e (regionFiniteType R j)

lemma regionInteriorEuler (R : RegionDecomposition S) (j : Fin R.regionCount)
    (hI : HomologyFiniteType ℚ (regionInterior R j)) :
    topologicalEuler (regionInterior R j) hI =
      2 - ((R.region j).boundaryCount : ℤ) := by
  obtain ⟨e, _⟩ := regionInteriorClosureEquivalence R j
  exact (topologicalEuler_homotopyEquiv e hI (regionFiniteType R j)).trans
    (regionEuler R j (regionFiniteType R j))

end Regions
end P202.SurfaceRegionsEuler
end

section
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
namespace P202.SurfaceRegionsEuler
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

def overlapUnionMap (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    (Σ j : Fin R.regionCount, (collarNeighborhood R C ∩ regionInterior R j : Set M)) →
      (collarNeighborhood R C ∩ R.graph.carrierᶜ : Set M) :=
  fun x => ⟨x.2.val, x.2.property.1, componentSet_subset _ x.2.property.2⟩

lemma overlapUnionMap_bijective (R : RegionDecomposition S)
    (C : ∀ j, RegionCollar R j) : Function.Bijective (overlapUnionMap R C) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : x.val = y.val := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (regionInteriors_disjoint R hn)
        x.property.2 (hxy ▸ y.property.2)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hxy)
  · intro x
    have hx : x.val ∈ ⋃ j, regionInterior R j := by
      rw [regionInteriors_cover]
      exact x.property.2
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact ⟨⟨j, ⟨x.val, x.property.1, hj⟩⟩, rfl⟩

def overlapUnionHomeomorph (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    (Σ j : Fin R.regionCount, (collarNeighborhood R C ∩ regionInterior R j : Set M)) ≃ₜ
      (collarNeighborhood R C ∩ R.graph.carrierᶜ : Set M) :=
  (Equiv.ofBijective (overlapUnionMap R C) (overlapUnionMap_bijective R C)).toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ => continuous_subtype_val.subtype_mk _) (by
      apply isOpenMap_sigma.mpr
      intro j
      exact ((collarNeighborhood_open R C).inter (R.open_components j)).isOpenMap_subtype_val.subtype_mk _)

end P202.SurfaceRegionsEuler
end

namespace P202.SurfaceRegionsEuler
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.EulerPoincare P202Specs.PlanarRegionTopology

/-- Lift only the finite indexing type, leaving the actual component spaces unchanged. -/
def sigmaFinLiftHomeomorph {n : ℕ} (X : Fin n → Type u) [∀ i, TopologicalSpace (X i)] :
    (Σ i : ULift.{u} (Fin n), X i.down) ≃ₜ (Σ i : Fin n, X i) where
  toFun x := ⟨x.1.down, x.2⟩
  invFun x := ⟨⟨x.1⟩, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl
  continuous_toFun := continuous_sigma fun _ => continuous_sigmaMk
  continuous_invFun := by
    apply continuous_sigma
    intro i
    exact continuous_sigmaMk (σ := fun j : ULift.{u} (Fin n) => X j.down)
      (i := (⟨i⟩ : ULift.{u} (Fin n)))

lemma sigmaFinFiniteType {n : ℕ} (X : Fin n → Type u) [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, HomologyFiniteType ℚ (X i)) : HomologyFiniteType ℚ (Σ i, X i) := by
  let Y : ULift.{u} (Fin n) → TopCat.{u} := fun i => TopCat.of (X i.down)
  exact finiteType_homeomorph (sigmaFinLiftHomeomorph X).symm
    (sigmaHomologyFiniteType Y (fun i => h i.down))

lemma sigmaFinEuler {n : ℕ} (X : Fin n → Type u) [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, HomologyFiniteType ℚ (X i)) :
    homologicalEuler ℚ (Σ i, X i) = ∑ i, homologicalEuler ℚ (X i) := by
  let Y : ULift.{u} (Fin n) → TopCat.{u} := fun i => TopCat.of (X i.down)
  calc
    _ = homologicalEuler ℚ (Σ i : ULift.{u} (Fin n), X i.down) :=
      euler_homeomorph (sigmaFinLiftHomeomorph X).symm
    _ = ∑ i : ULift.{u} (Fin n), homologicalEuler ℚ (X i.down) :=
      sigmaHomologicalEuler Y (fun i => h i.down)
    _ = _ := Fintype.sum_equiv Equiv.ulift (fun i => homologicalEuler ℚ (X i.down))
      (fun i => homologicalEuler ℚ (X i)) (fun _ => rfl)

lemma planarBoundaryFiniteType (D : PlanarRegion) : HomologyFiniteType ℚ D.boundary :=
  finiteType_homeomorph (boundaryCirclesHomeomorph D).symm
    (sigmaFinFiniteType (fun _ : Fin D.boundaryCount => ParameterCircle)
      (fun _ => parameterCircleFiniteType))

lemma planarBoundaryEuler (D : PlanarRegion) : homologicalEuler ℚ D.boundary = 0 := by
  calc
    _ = homologicalEuler ℚ (Σ _ : Fin D.boundaryCount, ParameterCircle) :=
      euler_homeomorph (boundaryCirclesHomeomorph D).symm
    _ = ∑ _ : Fin D.boundaryCount, homologicalEuler ℚ ParameterCircle :=
      sigmaFinEuler _ (fun _ => parameterCircleFiniteType)
    _ = 0 := by simp [parameterCircleHomologicalEuler]

/-- An open boundary cylinder retracts onto its actual boundary factor. -/
def boundaryCylinderEquiv (B : Type u) [TopologicalSpace B] :
    ContinuousMap.HomotopyEquiv (B × OpenCollarTime) B := by
  letI : ContractibleSpace OpenCollarTime :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨(1/2 : ℝ), by norm_num, by norm_num⟩
  let e := Classical.choice (ContractibleSpace.hequiv_unit OpenCollarTime)
  exact ((ContinuousMap.HomotopyEquiv.refl B).prodCongr e).trans
    (Homeomorph.prodUnique B Unit).toHomotopyEquiv

section Regions
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma actualBoundaryFiniteType (R : RegionDecomposition S) (j : Fin R.regionCount) :
    HomologyFiniteType ℚ (regionClosure R j ∩ R.graph.carrier : Set M) :=
  finiteType_homeomorph (regionBoundaryHomeomorph R j) (planarBoundaryFiniteType _)

lemma actualBoundaryEuler (R : RegionDecomposition S) (j : Fin R.regionCount) :
    homologicalEuler ℚ (regionClosure R j ∩ R.graph.carrier : Set M) = 0 :=
  (euler_homeomorph (regionBoundaryHomeomorph R j)).trans (planarBoundaryEuler _)

lemma overlapRegionFiniteType (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) :
    HomologyFiniteType ℚ (collarNeighborhood R C ∩ regionInterior R j : Set M) := by
  let e := (overlapRegionHomeomorph R C j).symm.toHomotopyEquiv.trans
    (boundaryCylinderEquiv (regionClosure R j ∩ R.graph.carrier : Set M))
  exact finiteType_of_homotopyEquiv e (actualBoundaryFiniteType R j)

lemma overlapRegionEuler (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j)
    (j : Fin R.regionCount) :
    homologicalEuler ℚ (collarNeighborhood R C ∩ regionInterior R j : Set M) = 0 := by
  let e := (overlapRegionHomeomorph R C j).symm.toHomotopyEquiv.trans
    (boundaryCylinderEquiv (regionClosure R j ∩ R.graph.carrier : Set M))
  exact (homologicalEuler_homotopyEquiv e).trans (actualBoundaryEuler R j)
end Regions
end P202.SurfaceRegionsEuler


namespace P202.SurfaceRegionsEuler
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.EulerPoincare
section Assembly
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

lemma collarNeighborhoodFiniteType (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    HomologyFiniteType ℚ (collarNeighborhood R C) :=
  finiteType_of_homotopyEquiv (collarNeighborhoodGraphEquiv R C) (Classical.choose (graphEuler R.graph))

lemma collarNeighborhoodEuler (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    homologicalEuler ℚ (collarNeighborhood R C) =
      (R.graph.vertexCount : ℤ) - (R.graph.edgeCount : ℤ) := by
  obtain ⟨hG, hχ⟩ := graphEuler R.graph
  exact (homologicalEuler_homotopyEquiv (collarNeighborhoodGraphEquiv R C)).trans hχ

lemma graphComplementFiniteType (R : RegionDecomposition S) :
    HomologyFiniteType ℚ (R.graph.carrierᶜ : Set M) :=
  finiteType_homeomorph (regionInteriorsHomeomorph R).symm
    (sigmaFinFiniteType (fun j => regionInterior R j) (regionInteriorFiniteType R))

lemma graphComplementEuler (R : RegionDecomposition S) :
    homologicalEuler ℚ (R.graph.carrierᶜ : Set M) =
      ∑ j : Fin R.regionCount, homologicalEuler ℚ (regionClosure R j) := by
  calc
    _ = homologicalEuler ℚ (Σ j : Fin R.regionCount, regionInterior R j) :=
      euler_homeomorph (regionInteriorsHomeomorph R).symm
    _ = ∑ j : Fin R.regionCount, homologicalEuler ℚ (regionInterior R j) :=
      sigmaFinEuler _ (regionInteriorFiniteType R)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      obtain ⟨e, _⟩ := regionInteriorClosureEquivalence R j
      exact homologicalEuler_homotopyEquiv e

lemma overlapFiniteType (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    HomologyFiniteType ℚ (collarNeighborhood R C ∩ R.graph.carrierᶜ : Set M) :=
  finiteType_homeomorph (overlapUnionHomeomorph R C).symm
    (sigmaFinFiniteType (fun j => (collarNeighborhood R C ∩ regionInterior R j : Set M))
      (overlapRegionFiniteType R C))

lemma overlapEuler (R : RegionDecomposition S) (C : ∀ j, RegionCollar R j) :
    homologicalEuler ℚ (collarNeighborhood R C ∩ R.graph.carrierᶜ : Set M) = 0 := by
  calc
    _ = homologicalEuler ℚ (Σ j : Fin R.regionCount,
        (collarNeighborhood R C ∩ regionInterior R j : Set M)) :=
      euler_homeomorph (overlapUnionHomeomorph R C).symm
    _ = ∑ j : Fin R.regionCount,
        homologicalEuler ℚ (collarNeighborhood R C ∩ regionInterior R j : Set M) :=
      sigmaFinEuler _ (overlapRegionFiniteType R C)
    _ = 0 := by simp [overlapRegionEuler]

/-- The constructed geometric decomposition suffices to establish actual
finite-type rational singular homology of the whole surface. -/
lemma surfaceFiniteTypeFromRegions (R : RegionDecomposition S) : HomologyFiniteType ℚ M := by
  let C := regionCollar R
  exact finiteType_openCover (collarNeighborhood R C) R.graph.carrierᶜ
    (collarNeighborhood_open R C) (graphClosed R.graph).isOpen_compl (collarNeighborhood_cover R C)
    (collarNeighborhoodFiniteType R C) (graphComplementFiniteType R) (overlapFiniteType R C)

end Assembly
end P202.SurfaceRegionsEuler


section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open P202Specs.SingularChains P202Specs.EulerPoincare P202Specs.MayerVietoris
namespace P202.SurfaceRegionsEuler
abbrev mvTheory := theoryFunctor ℚ .ordinary

def mvBoundaryRank (δ : Connecting mvTheory) (C : CoverPair.{u,0}) (n : ℕ) : ℕ :=
  Module.finrank ℚ (LinearMap.range (δ C ((n : ℤ)-1)).hom)

lemma mvDimension (δ : Connecting mvTheory) (he : Exact mvTheory δ)
    (C : CoverPair.{u,0}) (hX : HomologyFiniteType ℚ C.pair.space)
    (hL : HomologyFiniteType ℚ C.left) (hR : HomologyFiniteType ℚ C.right)
    (hI : HomologyFiniteType ℚ (C.left ∩ C.right : Set C.pair.space)) (n : ℕ) :
    (Module.finrank ℚ (homology ℚ ℚ C.pair.space n) : ℤ) +
      (Module.finrank ℚ (homology ℚ ℚ (TopCat.of (C.left ∩ C.right : Set C.pair.space)) n) : ℤ) =
    (Module.finrank ℚ (homologyMiddle mvTheory C n) : ℤ) +
      (mvBoundaryRank δ C (n+1) : ℤ) + (mvBoundaryRank δ C n : ℤ) := by
  have hn : ((n : ℤ)-1)+1 = (n : ℤ) := by omega
  haveI := hX.1 n
  haveI := hI.1 n
  haveI := hL.1 n
  haveI := hR.1 n
  haveI : FiniteDimensional ℚ (homologyMiddle mvTheory C n) :=
    (ModuleCat.biprodIsoProd (homology ℚ ℚ (TopCat.of C.left) n)
      (homology ℚ ℚ (TopCat.of C.right) n)).symm.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional ℚ (homology ℚ ℚ C.pair.space (((n : ℤ)-1)+1)) := by
    rwa [hn]
  let TI := (he.1 C (n : ℤ)).sc 2
  let TB := (he.2 C (n : ℤ)).sc 0
  let TX := (he.1 C ((n : ℤ)-1)).sc 1
  haveI : FiniteDimensional ℚ TI.X₂ := by
    change FiniteDimensional ℚ (homology ℚ ℚ (TopCat.of (C.left ∩ C.right : Set C.pair.space)) n)
    exact hI.1 n
  haveI : FiniteDimensional ℚ TB.X₂ := by
    change FiniteDimensional ℚ (homologyMiddle mvTheory C n)
    infer_instance
  haveI : FiniteDimensional ℚ TX.X₂ := by
    change FiniteDimensional ℚ (homology ℚ ℚ C.pair.space (((n : ℤ)-1)+1))
    infer_instance
  have dI := exactMiddleDimension TI ((he.1 C (n : ℤ)).exact 2)
  have dB := exactMiddleDimension TB ((he.2 C (n : ℤ)).exact 0)
  have dX := exactMiddleDimension TX ((he.1 C ((n : ℤ)-1)).exact 1)
  change Module.finrank ℚ (homology ℚ ℚ (TopCat.of (C.left ∩ C.right : Set C.pair.space)) n) =
      Module.finrank ℚ (LinearMap.range (δ C n).hom) +
      Module.finrank ℚ (LinearMap.range (first mvTheory C n).hom) at dI
  change Module.finrank ℚ (homologyMiddle mvTheory C n) =
      Module.finrank ℚ (LinearMap.range (first mvTheory C n).hom) +
      Module.finrank ℚ (LinearMap.range (sum mvTheory C n).hom) at dB
  change Module.finrank ℚ (homology ℚ ℚ C.pair.space (((n : ℤ)-1)+1)) =
      Module.finrank ℚ (LinearMap.range (sum mvTheory C (((n : ℤ)-1)+1)).hom) +
      Module.finrank ℚ (LinearMap.range (δ C ((n : ℤ)-1)).hom) at dX
  have hxnorm := congrArg
    (fun k : ℤ => Module.finrank ℚ (homology ℚ ℚ C.pair.space k)) hn
  have hsnorm := congrArg
    (fun k : ℤ => Module.finrank ℚ (LinearMap.range (sum mvTheory C k).hom)) hn
  have hsucc : ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) := by omega
  have hrnorm := congrArg
    (fun k : ℤ => Module.finrank ℚ (LinearMap.range (δ C k).hom)) hsucc
  simp only [mvBoundaryRank]
  omega

lemma mvBoundaryRank_zero (δ : Connecting mvTheory) (C : CoverPair.{u,0}) :
    mvBoundaryRank δ C 0 = 0 := by
  haveI : Subsingleton ((mvTheory.obj C.intersectionPair).homology ((0 : ℤ)-1)) := by
    change Subsingleton (homology ℚ ℚ (TopCat.of (C.left ∩ C.right : Set C.pair.space)) (-1))
    exact ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_homology ℚ ℚ
        (TopCat.of (C.left ∩ C.right : Set C.pair.space)) (-1) (by norm_num))
  unfold mvBoundaryRank
  exact Module.finrank_zero_of_subsingleton

lemma mvBoundaryRank_vanish (δ : Connecting mvTheory) (C : CoverPair.{u,0})
    (N : ℕ) (hz : IsZero (homology ℚ ℚ C.pair.space N)) : mvBoundaryRank δ C N = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero hz
  have hN : ((N : ℤ)-1)+1 = (N : ℤ) := by omega
  unfold mvBoundaryRank
  haveI : Subsingleton ((mvTheory.obj C.pair).homology (((N : ℤ)-1)+1)) := by
    change Subsingleton (homology ℚ ℚ C.pair.space (((N : ℤ)-1)+1))
    rwa [hN]
  have hzero : Module.finrank ℚ ((mvTheory.obj C.pair).homology (((N : ℤ)-1)+1)) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hle := (δ C ((N : ℤ)-1)).hom.finrank_range_le
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

lemma mvMiddleFinrank (C : CoverPair.{u,0})
    (hL : HomologyFiniteType ℚ C.left) (hR : HomologyFiniteType ℚ C.right) (n : ℕ) :
    Module.finrank ℚ (homologyMiddle mvTheory C n) =
      Module.finrank ℚ (homology ℚ ℚ (TopCat.of C.left) n) +
      Module.finrank ℚ (homology ℚ ℚ (TopCat.of C.right) n) := by
  haveI := hL.1 n
  haveI := hR.1 n
  calc
    _ = Module.finrank ℚ (homology ℚ ℚ (TopCat.of C.left) n ×
        homology ℚ ℚ (TopCat.of C.right) n) :=
      (ModuleCat.biprodIsoProd (homology ℚ ℚ (TopCat.of C.left) n)
        (homology ℚ ℚ (TopCat.of C.right) n)).toLinearEquiv.finrank_eq
    _ = _ := Module.finrank_prod

lemma mvHomologicalEuler (C : CoverPair.{u,0})
    (hX : HomologyFiniteType ℚ C.pair.space)
    (hL : HomologyFiniteType ℚ C.left) (hR : HomologyFiniteType ℚ C.right)
    (hI : HomologyFiniteType ℚ (C.left ∩ C.right : Set C.pair.space)) :
    homologicalEuler ℚ C.pair.space = homologicalEuler ℚ C.left +
      homologicalEuler ℚ C.right - homologicalEuler ℚ (C.left ∩ C.right : Set C.pair.space) := by
  obtain ⟨⟨δ, he, _, _⟩, _, _, _⟩ := P202.MayerVietoris.mayerVietoris ℚ .ordinary
  obtain ⟨NX, hzX⟩ := hX.2
  obtain ⟨NL, hzL⟩ := hL.2
  obtain ⟨NR, hzR⟩ := hR.2
  obtain ⟨NI, hzI⟩ := hI.2
  let N := max (max NX NL) (max NR NI)
  have hzX' (n : ℕ) (hn : N ≤ n) := hzX n (by omega)
  have hzL' (n : ℕ) (hn : N ≤ n) := hzL n (by omega)
  have hzR' (n : ℕ) (hn : N ≤ n) := hzR n (by omega)
  have hzI' (n : ℕ) (hn : N ≤ n) := hzI n (by omega)
  rw [P202.Homology.EulerPoincare.homologicalSum _ ℚ N hzX',
    P202.Homology.EulerPoincare.homologicalSum _ ℚ N hzL',
    P202.Homology.EulerPoincare.homologicalSum _ ℚ N hzR',
    P202.Homology.EulerPoincare.homologicalSum _ ℚ N hzI']
  have ht := P202.Homology.EulerPoincare.alternatingTelescope
    (fun n => (Module.finrank ℚ (homology ℚ ℚ C.pair.space n) : ℤ) +
      (Module.finrank ℚ (homology ℚ ℚ (TopCat.of (C.left ∩ C.right : Set C.pair.space)) n) : ℤ))
    (fun n => (Module.finrank ℚ (homologyMiddle mvTheory C n) : ℤ))
    (fun n => (mvBoundaryRank δ C n : ℤ)) (mvDimension δ he C hX hL hR hI) N
  rw [mvBoundaryRank_zero, mvBoundaryRank_vanish δ C N (hzX' N le_rfl)] at ht
  simp only [Nat.cast_zero, mul_zero, add_zero] at ht
  simp_rw [mul_add, Finset.sum_add_distrib, mvMiddleFinrank C hL hR,
    Nat.cast_add] at ht
  simp_rw [mul_add, Finset.sum_add_distrib] at ht
  exact eq_sub_of_add_eq ht

lemma homologicalEuler_openCover {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hfX : HomologyFiniteType ℚ X) (hfU : HomologyFiniteType ℚ U)
    (hfV : HomologyFiniteType ℚ V) (hfI : HomologyFiniteType ℚ (U ∩ V : Set X)) :
    homologicalEuler ℚ X = homologicalEuler ℚ U + homologicalEuler ℚ V -
      homologicalEuler ℚ (U ∩ V : Set X) := by
  let P : P202Specs.RelativeSingularChains.Pair := ⟨TopCat.of X, ∅⟩
  let C := CoverPair.ofSets.{u,0} P U V hU hV hcover
  exact mvHomologicalEuler C hfX hfU hfV hfI

end P202.SurfaceRegionsEuler

end

namespace P202.SurfaceRegionsEuler
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.EulerPoincare

/-- The full Euler identity for the actual graph and actual region closures. -/
lemma eulerConclusionFromRegions {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (R : RegionDecomposition S) : EulerConclusion R := by
  let C := regionCollar R
  let hS := surfaceFiniteTypeFromRegions R
  refine ⟨hS, regionFiniteType R, ?_⟩
  have h := homologicalEuler_openCover (collarNeighborhood R C) R.graph.carrierᶜ
    (collarNeighborhood_open R C) (graphClosed R.graph).isOpen_compl (collarNeighborhood_cover R C)
    hS (collarNeighborhoodFiniteType R C) (graphComplementFiniteType R) (overlapFiniteType R C)
  rw [collarNeighborhoodEuler, graphComplementEuler, overlapEuler, sub_zero] at h
  exact h

/-- Assembly from any proof of the complete surface-region construction. -/
theorem surfaceRegionsEuler_conditional
    (construction : P202Specs.SurfaceRegionConstruction.Expected.construction.{u}) :
    P202Specs.SurfaceRegionsEuler.Expected.surfaceRegionsEuler.{u} := by
  intro kind M _ _ S
  obtain ⟨R⟩ := construction S
  exact ⟨R, eulerConclusionFromRegions R⟩

/-- Every compact smooth surface has the stated graph and chart regions,
finite-type rational homology, and the topological Euler identity. -/
theorem surfaceRegionsEuler :
    P202Specs.SurfaceRegionsEuler.Expected.surfaceRegionsEuler.{u} :=
  surfaceRegionsEuler_conditional P202.SurfaceRegionConstruction.construction

end P202.SurfaceRegionsEuler
