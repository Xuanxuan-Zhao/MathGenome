import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fintype.EquivFin

universe u
noncomputable section

namespace FiniteCombinatorics.Graph.Plane

abbrev Realization := @Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.Realization
abbrev realizationVertex := @Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.realizationVertex
abbrev PlaneRealization := @Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry.PlaneRealization

open Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry

theorem arc_compact : arc_compactType := by
  rintro a b s ⟨_, p, _, rfl⟩
  exact isCompact_range p.continuous

theorem arc_interval : arc_intervalType := by
  rintro a b s ⟨_, p, hp, hps⟩
  let h := (p.continuous.isClosedEmbedding hp).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hps)
  exact ⟨h, p.source, p.target⟩

theorem edge_compact : edge_compactType := by
  intro V _ G D e
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have h : G.Adj a b := by simpa [← hab] using e.property
  have he : e = ⟨s(a, b), h⟩ := Subtype.ext hab.symm
  rw [he]
  exact arc_compact (D.edge_arc a b h)

theorem plane_image_compact : plane_image_compactType := by
  intro V _ G D
  exact (Set.finite_range D.point).isCompact.union (isCompact_iUnion (edge_compact D))

theorem sphere_image_compact : sphere_image_compactType := by
  intro V _ G D
  exact (plane_image_compact D).image OnePoint.continuous_coe

theorem realization_compact : realization_compactType := by
  intro V _ G D
  exact isCompact_iff_compactSpace.mp (sphere_image_compact D)

def realization_homeomorph : realization_homeomorphType := fun D =>
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (planeImage D)

theorem realization_proper : realization_properType := by
  intro V _ G D heq
  exact infinity_not_in_image D (heq ▸ Set.mem_univ _)

theorem realization_inclusion_proper : realization_inclusion_properType := by
  intro V _ G D
  exact (sphere_image_compact D).isClosed.isProperMap_subtypeVal

theorem realization_nonempty_iff : realization_nonempty_iffType := by
  intro V _ G D
  constructor
  · rintro ⟨⟨x, y, hy, rfl⟩⟩
    rcases hy with ⟨v, _⟩ | hy
    · exact ⟨v⟩
    · obtain ⟨e, _⟩ := Set.mem_iUnion.mp hy
      obtain ⟨⟨a, b⟩, _⟩ := Sym2.mk_surjective e.val
      exact ⟨a⟩
  · rintro ⟨v⟩
    exact ⟨⟨OnePoint.some (D.point v), D.point v,
      Or.inl (Set.mem_range_self v), rfl⟩⟩

theorem plane_complement_open : plane_complement_openType := by
  intro V _ G D
  exact (plane_image_compact D).isClosed.isOpen_compl

theorem sphere_complement_open : sphere_complement_openType := by
  intro V _ G D
  exact (sphere_image_compact D).isClosed.isOpen_compl

theorem plane_complement_locally_path_connected : plane_complement_locally_path_connectedType := by
  intro V _ G D
  exact (plane_complement_open D).locallyPathConnectedSpace

theorem sphere_locally_path_connected : LocallyPathConnectedSpace Sphere := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  exact sphereHomeomorph.symm.locallyPathConnectedSpace

theorem sphere_complement_locally_path_connected : sphere_complement_locally_path_connectedType := by
  intro V _ G D
  have := sphere_locally_path_connected
  exact (sphere_complement_open D).locallyPathConnectedSpace

theorem complement_path_component : complement_path_componentType := by
  intro V _ G D x
  have := sphere_complement_locally_path_connected D
  exact pathComponent_eq_connectedComponent x


section Components
variable {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)

/-- The part of the drawing belonging to a graph connected component. -/
def planeComponentRegion (C : G.ConnectedComponent) : Set Point :=
  D.point '' C.supp ∪ ⋃ (e : {e : G.edgeSet // ∃ v ∈ C.supp, v ∈ e.val}), D.edge e.val

lemma mem_planeComponentRegion {C : G.ConnectedComponent} {x : Point} :
    x ∈ planeComponentRegion D C ↔
      (∃ v ∈ C.supp, D.point v = x) ∨
      ∃ e : G.edgeSet, (∃ v ∈ C.supp, v ∈ e.val) ∧ x ∈ D.edge e := by
  simp [planeComponentRegion]

omit [Finite V] in
lemma component_eq_of_mem_edge (e : G.edgeSet) {a b : V}
    (ha : a ∈ e.val) (hb : b ∈ e.val) :
    G.connectedComponentMk a = G.connectedComponentMk b := by
  by_cases h : a = b
  · rw [h]
  · exact SimpleGraph.ConnectedComponent.sound
      (G.adj_iff_exists_edge.mpr ⟨h, e.val, e.property, ha, hb⟩).reachable

omit [Finite V] in
lemma mem_component_of_mem_edge {C : G.ConnectedComponent} {e : G.edgeSet}
    (he : ∃ v ∈ C.supp, v ∈ e.val) {v : V} (hv : v ∈ e.val) : v ∈ C.supp := by
  obtain ⟨w, hw, hwe⟩ := he
  exact (component_eq_of_mem_edge e hv hwe).trans hw

lemma point_mem_planeComponentRegion (C : G.ConnectedComponent) (v : V) :
    D.point v ∈ planeComponentRegion D C ↔ v ∈ C.supp := by
  rw [mem_planeComponentRegion]
  constructor
  · rintro (⟨w, hw, heq⟩ | ⟨e, he, hv⟩)
    · exact D.point_injective heq ▸ hw
    · exact mem_component_of_mem_edge he ((D.vertex_edge e v).mp hv)
  · intro hv
    exact Or.inl ⟨v, hv, rfl⟩

lemma planeComponentRegion_subset (C : G.ConnectedComponent) :
    planeComponentRegion D C ⊆ planeImage D := by
  intro x hx
  rcases (mem_planeComponentRegion D).mp hx with ⟨v, _, rfl⟩ | ⟨e, _, hx⟩
  · exact Or.inl (Set.mem_range_self v)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨e, hx⟩)

lemma planeComponentRegion_cover {x : Point} (hx : x ∈ planeImage D) :
    ∃ C, x ∈ planeComponentRegion D C := by
  rcases hx with ⟨v, rfl⟩ | hx
  · exact ⟨G.connectedComponentMk v, (point_mem_planeComponentRegion D _ v).mpr rfl⟩
  · obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨⟨a, b⟩, he⟩ := Sym2.mk_surjective e.val
    refine ⟨G.connectedComponentMk a, (mem_planeComponentRegion D).mpr (Or.inr ⟨e, ?_, hx⟩)⟩
    exact ⟨a, rfl, he ▸ Sym2.mem_mk_left a b⟩

lemma planeComponentRegion_compact (C : G.ConnectedComponent) :
    IsCompact (planeComponentRegion D C) := by
  exact ((Set.toFinite C.supp).image D.point).isCompact.union
    (isCompact_iUnion fun e => edge_compact D e.val)

lemma planeComponentRegion_disjoint :
    Pairwise (fun C C' : G.ConnectedComponent =>
      Disjoint (planeComponentRegion D C) (planeComponentRegion D C')) := by
  intro C C' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  apply hne
  rcases (mem_planeComponentRegion D).mp hx with ⟨v, hv, rfl⟩ | ⟨e, he, hx⟩
  · exact hv.symm.trans ((point_mem_planeComponentRegion D C' v).mp hx')
  rcases (mem_planeComponentRegion D).mp hx' with ⟨v, hv, rfl⟩ | ⟨f, hf, hx'⟩
  · exact (mem_component_of_mem_edge he ((D.vertex_edge e v).mp hx)).symm.trans hv
  by_cases hef : e = f
  · obtain ⟨v, hv, hve⟩ := he
    exact hv.symm.trans (mem_component_of_mem_edge hf (hef ▸ hve))
  · have hi : x ∈ D.point '' {v | v ∈ e.val ∧ v ∈ f.val} := by
      rw [← D.edge_intersection e f hef]
      exact ⟨hx, hx'⟩
    obtain ⟨v, ⟨hve, hvf⟩, _⟩ := hi
    exact (mem_component_of_mem_edge he hve).symm.trans (mem_component_of_mem_edge hf hvf)

lemma arc_path_connected {a b : Point} {s : Set Point} (h : IsSimplePolygonalArc a b s) :
    IsPathConnected s := by
  obtain ⟨_, p, _, rfl⟩ := h
  have : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  exact isPathConnected_range p.continuous

lemma joinedIn_component_of_adj (C : G.ConnectedComponent) {a b : V}
    (ha : a ∈ C.supp) (hab : G.Adj a b) :
    JoinedIn (planeComponentRegion D C) (D.point a) (D.point b) := by
  obtain ⟨_, p, _, hp⟩ := D.edge_arc a b hab
  refine ⟨p, fun t => (mem_planeComponentRegion D).mpr (Or.inr ⟨⟨s(a,b), hab⟩, ?_, ?_⟩)⟩
  · exact ⟨a, ha, Sym2.mem_mk_left a b⟩
  · rw [← hp]
    exact Set.mem_range_self t

lemma joinedIn_component_of_walk (C : G.ConnectedComponent) {a b : V}
    (p : G.Walk a b) (ha : a ∈ C.supp) :
    JoinedIn (planeComponentRegion D C) (D.point a) (D.point b) := by
  induction p with
  | nil => exact JoinedIn.refl ((point_mem_planeComponentRegion D C _).mpr ha)
  | @cons a b c hab p ih =>
    exact (joinedIn_component_of_adj D C ha hab).trans
      (ih (C.mem_supp_of_adj_mem_supp ha hab))

lemma planeComponentRegion_path_connected (C : G.ConnectedComponent) :
    IsPathConnected (planeComponentRegion D C) := by
  obtain ⟨a, ha⟩ := C.nonempty_supp
  refine ⟨D.point a, (point_mem_planeComponentRegion D C a).mpr ha, ?_⟩
  intro x hx
  rcases (mem_planeComponentRegion D).mp hx with ⟨b, hb, rfl⟩ | ⟨e, he, hx⟩
  · exact (C.reachable_of_mem_supp ha hb).elim
      fun p => joinedIn_component_of_walk D C p ha
  · obtain ⟨b, hb, hbe⟩ := he
    have hj := (C.reachable_of_mem_supp ha hb).elim
      fun p => joinedIn_component_of_walk D C p ha
    have hac : IsPathConnected (D.edge e) := by
      obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
      have hadj : G.Adj u v := by simpa [← huv] using e.property
      have heq : e = ⟨s(u,v), hadj⟩ := Subtype.ext huv.symm
      rw [heq]
      exact arc_path_connected (D.edge_arc u v hadj)
    exact hj.trans ((hac.joinedIn (D.point b) ((D.vertex_edge e b).mpr hbe) x hx).mono
      fun y hy => (mem_planeComponentRegion D).mpr (Or.inr ⟨e, ⟨b, hb, hbe⟩, hy⟩))

/-- The regions considered as subsets of the actual plane realization. -/
def realizationComponentRegion (C : G.ConnectedComponent) : Set (PlaneRealization D) :=
  Subtype.val ⁻¹' planeComponentRegion D C

lemma realizationComponentRegion_clopen (C : G.ConnectedComponent) :
    IsClopen (realizationComponentRegion D C) := by
  have hc (C : G.ConnectedComponent) : IsClosed (realizationComponentRegion D C) :=
    (planeComponentRegion_compact D C).isClosed.preimage continuous_subtype_val
  refine ⟨hc C, ?_⟩
  rw [← isClosed_compl_iff]
  have heq : (realizationComponentRegion D C)ᶜ =
      ⋃ (C' : {C' : G.ConnectedComponent // C' ≠ C}), realizationComponentRegion D C' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Subtype.exists, realizationComponentRegion,
      Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨C', hx'⟩ := planeComponentRegion_cover D x.property
      exact ⟨C', fun h => hx (h ▸ hx'), hx'⟩
    · rintro ⟨C', hne, hx'⟩ hx
      exact Set.disjoint_left.mp (planeComponentRegion_disjoint D hne) hx' hx
  rw [heq]
  exact isClosed_iUnion_of_finite fun C' => hc C'

lemma realizationComponentRegion_connected (C : G.ConnectedComponent) :
    IsConnected (realizationComponentRegion D C) := by
  exact ((planeComponentRegion_path_connected D C).preimage_coe
    (planeComponentRegion_subset D C)).isConnected

lemma realizationComponentRegion_cover :
    ⋃ C, realizationComponentRegion D C = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨C, hx⟩ := planeComponentRegion_cover D x.property
  exact Set.mem_iUnion.mpr ⟨C, hx⟩

lemma realizationComponentRegion_disjoint :
    Pairwise (fun C C' : G.ConnectedComponent =>
      Disjoint (realizationComponentRegion D C) (realizationComponentRegion D C')) := by
  intro C C' hne
  exact (planeComponentRegion_disjoint D hne).preimage Subtype.val

/-- Graph components are precisely the connected pieces of the actual plane image. -/
def planeRealizationComponentsEquiv : ConnectedComponents (PlaneRealization D) ≃
    G.ConnectedComponent :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (realizationComponentRegion_clopen D) (realizationComponentRegion_disjoint D)
    (realizationComponentRegion_cover D) (realizationComponentRegion_connected D)

end Components

/-- Functoriality of connected components under a homeomorphism. -/
def homeomorphComponentsEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := h.continuous.connectedComponentsMap
  invFun := h.symm.continuous.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp
  right_inv c := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    simp

theorem realization_components : realization_componentsType := by
  intro V _ G D
  let E := (homeomorphComponentsEquiv (realization_homeomorph D).symm).trans
    (planeRealizationComponentsEquiv D)
  refine ⟨E, fun v => ?_⟩
  have he : (realization_homeomorph D).symm (realizationVertex D v) =
      ⟨D.point v, Or.inl (Set.mem_range_self v)⟩ := by
    apply (realization_homeomorph D).injective
    simp only [Homeomorph.apply_symm_apply]
    rfl
  change planeRealizationComponentsEquiv D
    (ConnectedComponents.mk ((realization_homeomorph D).symm (realizationVertex D v))) = _
  rw [he]
  exact ConnectedComponents.equivOfIsClopenOfIsConnected_mk
    (realizationComponentRegion_clopen D) (realizationComponentRegion_disjoint D)
    (realizationComponentRegion_cover D) (realizationComponentRegion_connected D)
    _ ((point_mem_planeComponentRegion D _ v).mpr rfl)

theorem realization_vertex_components : realization_vertex_componentsType := by
  intro V _ G D a b
  obtain ⟨E, hE⟩ := realization_components D
  rw [← E.injective.eq_iff, hE, hE]
  exact SimpleGraph.ConnectedComponent.eq


section EdgeInterior
variable {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)

/-- Interior of an edge in the actual realization; all vertex images are removed. -/
def planeEdgeInterior (e : G.edgeSet) : Set (PlaneRealization D) :=
  {x | x.val ∈ D.edge e ∧ x.val ∉ Set.range D.point}

lemma edge_eq_of_common_nonvertex {e f : G.edgeSet} {x : Point}
    (he : x ∈ D.edge e) (hf : x ∈ D.edge f) (hn : x ∉ Set.range D.point) : e = f := by
  by_contra hef
  have hx : x ∈ D.point '' {v | v ∈ e.val ∧ v ∈ f.val} := by
    rw [← D.edge_intersection e f hef]
    exact ⟨he, hf⟩
  obtain ⟨v, _, rfl⟩ := hx
  exact hn (Set.mem_range_self v)

lemma planeEdgeInterior_open (e : G.edgeSet) : IsOpen (planeEdgeInterior D e) := by
  let K := Set.range D.point ∪ ⋃ (f : {f : G.edgeSet // f ≠ e}), D.edge f.val
  have hK : IsClosed K :=
    ((Set.finite_range D.point).isCompact.union
      (isCompact_iUnion fun f : {f : G.edgeSet // f ≠ e} => edge_compact D f.val)).isClosed
  have heq : planeEdgeInterior D e = (Subtype.val : PlaneRealization D → Point) ⁻¹' Kᶜ := by
    ext x
    constructor
    · rintro ⟨he, hn⟩ (hv | hf)
      · exact hn hv
      · obtain ⟨⟨f, hfe⟩, hf⟩ := Set.mem_iUnion.mp hf
        exact hfe (edge_eq_of_common_nonvertex D hf he hn)
    · intro hx
      have hn : x.val ∉ Set.range D.point := fun hv => hx (Or.inl hv)
      refine ⟨?_, hn⟩
      rcases x.property with hv | hf
      · exact False.elim (hn hv)
      · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hf
        by_cases hfe : f = e
        · exact hfe ▸ hf
        · exact False.elim (hx (Or.inr (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, hf⟩)))
  rw [heq]
  exact hK.isOpen_compl.preimage continuous_subtype_val

lemma planeEdgeInterior_interval (e : G.edgeSet) :
    Nonempty ((planeEdgeInterior D e) ≃ₜ ↥(Set.Ioo (0 : ℝ) 1)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have hadj : G.Adj a b := by simpa [← hab] using e.property
  have he : e = ⟨s(a,b), hadj⟩ := Subtype.ext hab.symm
  obtain ⟨h, h0, h1⟩ := arc_interval (D.edge_arc a b hadj)
  let j : ↥(Set.Ioo (0 : ℝ) 1) → unitInterval := fun t => ⟨t.val, t.property.1.le, t.property.2.le⟩
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      (show Topology.IsEmbedding (fun t : ↥(Set.Ioo (0 : ℝ) 1) => t.val) from
        Topology.IsEmbedding.subtypeVal)
  let f : ↥(Set.Ioo (0 : ℝ) 1) → PlaneRealization D := fun t =>
    ⟨(h (j t)).val, Or.inr (Set.mem_iUnion.mpr
      ⟨⟨s(a,b), hadj⟩, (h (j t)).property⟩)⟩
  have hcomp := (show Topology.IsEmbedding
      (Subtype.val : D.edge ⟨s(a,b), hadj⟩ → Point) from
        Topology.IsEmbedding.subtypeVal).comp (h.isEmbedding.comp hj)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hcomp
  have hf_range : Set.range f = planeEdgeInterior D e := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨he.symm ▸ (h (j t)).property, ?_⟩
      rintro ⟨v, hv⟩
      have hve : v ∈ s(a,b) := (D.vertex_edge ⟨s(a,b), hadj⟩ v).mp
        (hv.symm ▸ (h (j t)).property)
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · have ht : j t = 0 := h.injective (Subtype.ext (hv.symm.trans h0.symm))
        have htz := congrArg Subtype.val ht
        exact (ne_of_gt t.property.1) htz
      · have ht : j t = 1 := h.injective (Subtype.ext (hv.symm.trans h1.symm))
        have hto := congrArg Subtype.val ht
        exact (ne_of_lt t.property.2) hto
    · rintro ⟨hx, hn⟩
      let y : D.edge ⟨s(a,b), hadj⟩ := ⟨x.val, he ▸ hx⟩
      let t := h.symm y
      have ht0 : (0 : ℝ) < t.val := by
        apply lt_of_le_of_ne t.property.1
        intro heq
        have ht : t = 0 := Subtype.ext heq.symm
        have hx0 : x.val = D.point a := by
          have hh := congrArg Subtype.val (h.apply_symm_apply y)
          change (h t).val = x.val at hh
          rw [ht, h0] at hh
          exact hh.symm
        exact hn ⟨a, hx0.symm⟩
      have ht1 : t.val < (1 : ℝ) := by
        apply lt_of_le_of_ne t.property.2
        intro heq
        have ht : t = 1 := Subtype.ext heq
        have hx1 : x.val = D.point b := by
          have hh := congrArg Subtype.val (h.apply_symm_apply y)
          change (h t).val = x.val at hh
          rw [ht, h1] at hh
          exact hh.symm
        exact hn ⟨b, hx1.symm⟩
      refine ⟨⟨t.val, ht0, ht1⟩, ?_⟩
      apply Subtype.ext
      change (h (j ⟨t.val, ht0, ht1⟩)).val = x.val
      exact congrArg Subtype.val (h.apply_symm_apply y)
  exact ⟨(hf.toHomeomorph.trans (Homeomorph.setCongr hf_range)).symm⟩

end EdgeInterior

theorem edge_interior_local_model : edge_interior_local_modelType := by
  intro V _ G D e
  let h := realization_homeomorph D
  let U := h '' planeEdgeInterior D e
  refine ⟨U, h.isOpenMap _ (planeEdgeInterior_open D e), ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.val, hy.1, hy.2, rfl⟩
    · rintro ⟨y, hy, hn, heq⟩
      refine ⟨⟨y, Or.inr (Set.mem_iUnion.mpr ⟨e, hy⟩)⟩, ⟨hy, hn⟩, ?_⟩
      exact Subtype.ext heq.symm
  · obtain ⟨he⟩ := planeEdgeInterior_interval D e
    exact ⟨(h.image (planeEdgeInterior D e)).symm.trans he⟩

theorem isolated_vertex_local_model : isolated_vertex_local_modelType := by
  intro V _ G D v hv
  let z : PlaneRealization D := ⟨D.point v, Or.inl (Set.mem_range_self v)⟩
  let K := Set.range (fun w : {w : V // w ≠ v} => D.point w.val) ∪ ⋃ e, D.edge e
  have hK : IsClosed K :=
    ((Set.finite_range (fun w : {w : V // w ≠ v} => D.point w.val)).isCompact.union
      (isCompact_iUnion (edge_compact D))).isClosed
  have hvK : D.point v ∉ K := by
    rintro (⟨⟨w, hw⟩, heq⟩ | hx)
    · exact hw (D.point_injective heq)
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      exact (G.isIsolated_iff_forall_edgeSet_notMem.mp hv e.val e.property)
        ((D.vertex_edge e v).mp he)
  have heq : ({z} : Set (PlaneRealization D)) =
      (Subtype.val : PlaneRealization D → Point) ⁻¹' Kᶜ := by
    ext x
    constructor
    · rintro rfl
      exact hvK
    · intro hx
      apply Subtype.ext
      rcases x.property with ⟨w, hw⟩ | hxe
      · by_cases hwv : w = v
        · subst w
          exact hw.symm
        · exact False.elim (hx (Or.inl ⟨⟨w, hwv⟩, hw⟩))
      · exact False.elim (hx (Or.inr hxe))
  have hz : IsOpen ({z} : Set (PlaneRealization D)) := by
    rw [heq]
    exact hK.isOpen_compl.preimage continuous_subtype_val
  have hi := (realization_homeomorph D).isOpenMap {z} hz
  rw [Set.image_singleton] at hi
  have he : (realization_homeomorph D) z = realizationVertex D v := Subtype.ext rfl
  rw [he] at hi
  exact hi


theorem finite_star_contractible : finite_star_contractibleType := by
  intro n
  apply StarConvex.contractibleSpace (x := (0 : Fin n → ℝ))
  · exact (starConvex_singleton (0 : Fin n → ℝ)).union
      (starConvex_iUnion fun i => (convex_segment (0 : Fin n → ℝ) (Pi.single i 1)).starConvex
        (left_mem_segment ℝ _ _))
  · exact ⟨0, Or.inl rfl⟩

/-- A finite union of closed convex sets has arbitrarily small star-shaped
neighborhoods: discard the finitely many members which miss the center. -/
theorem finite_closed_convex_union_stronglyLocallyContractible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Finite ι] (K : ι → Set E)
    (hclosed : ∀ i, IsClosed (K i)) (hconvex : ∀ i, Convex ℝ (K i)) :
    StronglyLocallyContractibleSpace (⋃ i, K i) := by
  classical
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  let B : Set E := ⋃ i : {i // x.val ∉ K i}, K i.val
  have hB : IsClosed B := isClosed_iUnion_of_finite fun i => hclosed i.val
  have hxB : x.val ∉ B := by
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact i.property hi
  have hW : U ∩ (Subtype.val ⁻¹' Bᶜ) ∈ nhds x :=
    Filter.inter_mem hU
      ((hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds hxB)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
  let N : Set ↥(⋃ i, K i) := Metric.ball x r
  let T : Set E := (⋃ i, K i) ∩ Metric.ball x.val r
  have hT : T = (⋃ i : {i // x.val ∈ K i}, K i.val) ∩ Metric.ball x.val r := by
    ext y
    constructor
    · rintro ⟨hy, hyr⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      have hxi : x.val ∈ K i := by
        by_contra hn
        exact (hball (show (⟨y, Set.mem_iUnion.mpr ⟨i, hi⟩⟩ : ↥(⋃ i, K i)) ∈
          Metric.ball x r from hyr)).2 (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, hi⟩)
      exact ⟨Set.mem_iUnion.mpr ⟨⟨i, hxi⟩, hi⟩, hyr⟩
    · rintro ⟨hy, hyr⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact ⟨Set.mem_iUnion.mpr ⟨i.val, hi⟩, hyr⟩
  have hstar : StarConvex ℝ x.val T := by
    rw [hT]
    exact (starConvex_iUnion fun i : {i // x.val ∈ K i} =>
      (hconvex i.val).starConvex i.property).inter
      ((convex_ball x.val r).starConvex (Metric.mem_ball_self hr))
  have hcT : ContractibleSpace T := hstar.contractibleSpace
    ⟨x.val, x.property, Metric.mem_ball_self hr⟩
  have himage : (Subtype.val : ↥(⋃ i, K i) → E) '' N = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hyr⟩
      exact ⟨⟨y, hy⟩, hyr, rfl⟩
  let h : N ≃ₜ T := Topology.IsEmbedding.subtypeVal.homeomorphImage N |>.trans
    (Homeomorph.setCongr himage)
  exact ⟨N, Metric.ball_mem_nhds x hr, h.contractibleSpace_iff.mpr hcT,
    fun y hy => (hball hy).1⟩

theorem edge_polygonal {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : PlaneEmbedding G) (e : G.edgeSet) : IsPolygonal (D.edge e) := by
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have h : G.Adj a b := by simpa [← hab] using e.property
  have he : e = ⟨s(a, b), h⟩ := Subtype.ext hab.symm
  rw [he]
  exact (D.edge_arc a b h).1

/-- Polygonality gives a finite closed convex cover, also retaining isolated vertices. -/
theorem plane_realization_stronglyLocallyContractible {V : Type u} [Finite V]
    {G : SimpleGraph V} (D : PlaneEmbedding G) :
    StronglyLocallyContractibleSpace (PlaneRealization D) := by
  classical
  choose n a b hseg using edge_polygonal D
  let K : (V ⊕ (Σ e : G.edgeSet, Fin (n e))) → Set Point :=
    Sum.elim (fun v => {D.point v}) (fun i => segment ℝ (a i.1 i.2) (b i.1 i.2))
  have heq : planeImage D = ⋃ i, K i := by
    ext x
    change x ∈ Set.range D.point ∪ (⋃ e, D.edge e) ↔ x ∈ ⋃ i, K i
    simp only [Set.mem_union, Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro (⟨v, rfl⟩ | ⟨e, hx⟩)
      · exact ⟨Sum.inl v, rfl⟩
      · rw [hseg e] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨e, i⟩, hi⟩
    · rintro ⟨v | ⟨e, i⟩, hx⟩
      · exact Or.inl ⟨v, hx.symm⟩
      · exact Or.inr ⟨e, (hseg e) ▸ Set.mem_iUnion.mpr ⟨i, hx⟩⟩
  change StronglyLocallyContractibleSpace ↥(planeImage D)
  rw [heq]
  apply finite_closed_convex_union_stronglyLocallyContractible
  · rintro (v | ⟨e, i⟩)
    · exact isClosed_singleton
    · change IsClosed (segment ℝ (a e i) (b e i))
      rw [segment_eq_image]
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  · rintro (v | ⟨e, i⟩)
    · exact convex_singleton _
    · exact convex_segment _ _

theorem realization_locally_contractible : realization_locally_contractibleType := by
  intro V _ G D
  have := plane_realization_stronglyLocallyContractible D
  have := (realization_homeomorph D).symm.isOpenEmbedding.stronglyLocallyContractibleSpace
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- The exterior of a disk in the real normed plane is path connected. This
also applies to the product norm used by `Point`. -/
theorem plane_exterior_path_connected {r : ℝ} (hr : 0 < r) :
    IsPathConnected {x : Point | r < ‖x‖} := by
  have hs : IsPathConnected (Metric.sphere (0 : Point) 1) :=
    isPathConnected_sphere (by
      simp only [Point, rank_prod', Module.rank_self]
      norm_num) 0 (by norm_num)
  have ht : IsPathConnected (Set.Ioi r) :=
    (convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩
  have hc : Continuous (fun p : Point × ℝ => p.2 • p.1) := by fun_prop
  have heq : (fun p : Point × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : Point) 1 ×ˢ Set.Ioi r) = {x : Point | r < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      have hyn : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
      simpa [norm_smul, hyn, abs_of_pos (hr.trans ht)] using ht
    · intro hx
      have hxpos : 0 < ‖x‖ := hr.trans hx
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hx⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ hxpos.ne']
      · simp [smul_smul, mul_inv_cancel₀ hxpos.ne']
  rw [← heq]
  exact (hs.prod ht).image' hc.continuousOn

section Faces
variable {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G)

lemma planeFaceRegion_mem (F : PlaneFace D) (x : PlaneComplement D) :
    x.val ∈ planeFaceRegion D F ↔ ConnectedComponents.mk x = F := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (Subtype.ext heq : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma plane_face_region_connected (F : PlaneFace D) :
    IsConnected (planeFaceRegion D F) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe F
  have heq : planeFaceRegion D (ConnectedComponents.mk x) =
      Subtype.val '' connectedComponent x := by
    change Subtype.val '' {y : PlaneComplement D | ConnectedComponents.mk y =
      ConnectedComponents.mk x} = _
    congr 1
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [heq]
  exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

lemma plane_face_region_open (F : PlaneFace D) : IsOpen (planeFaceRegion D F) := by
  have := plane_complement_locally_path_connected D
  exact (plane_complement_open D).isOpenMap_subtype_val _
    (ConnectedComponents.continuous_coe.isOpen_preimage {F} (isOpen_discrete _))

lemma plane_exterior_same_face {r : ℝ} (hr : 0 < r)
    (hcover : planeImage D ⊆ Metric.ball 0 r) (x y : PlaneComplement D)
    (hx : r < ‖x.val‖) (hy : r < ‖y.val‖) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  have hsub : {z : Point | r < ‖z‖} ⊆ (planeImage D)ᶜ := by
    intro z hz hzG
    have hzr : ‖z‖ < r := by simpa using hcover hzG
    exact (hz.trans hzr).false
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact ((plane_exterior_path_connected hr).preimage_coe hsub).isConnected.subset_connectedComponent
    (show y ∈ Subtype.val ⁻¹' {z : Point | r < ‖z‖} from hy) hx

/-- Exactly one plane component is unbounded, without any connectedness
assumption on the graph (and including the empty drawing). -/
theorem unique_unbounded_plane_face :
    ∃ C : PlaneFace D, ∀ F : PlaneFace D,
      F = C ↔ ¬Bornology.IsBounded (planeFaceRegion D F) := by
  obtain ⟨r, hr, hcover⟩ := (plane_image_compact D).isBounded.subset_ball_lt 0 0
  have hnot (x : Point) (hx : r < ‖x‖) : x ∉ planeImage D := by
    intro h
    have : ‖x‖ < r := by simpa using hcover h
    exact (hx.trans this).false
  obtain ⟨z, hz⟩ := NormedSpace.exists_lt_norm ℝ Point r
  let z' : PlaneComplement D := ⟨z, hnot z hz⟩
  let C : PlaneFace D := ConnectedComponents.mk z'
  have hout (x : Point) (hx : r < ‖x‖) : x ∈ planeFaceRegion D C :=
    (planeFaceRegion_mem D C ⟨x, hnot x hx⟩).mpr
      (plane_exterior_same_face D hr hcover _ z' hx hz)
  have hC : ¬Bornology.IsBounded (planeFaceRegion D C) := by
    intro h
    obtain ⟨M, hM⟩ := h.exists_norm_le
    obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ Point (max r M)
    exact (not_lt_of_ge (hM x (hout x ((le_max_left r M).trans_lt hx))))
      ((le_max_right r M).trans_lt hx)
  refine ⟨C, fun F => ⟨fun h => h ▸ hC, ?_⟩⟩
  intro hF
  by_contra hne
  apply hF
  apply (Metric.isBounded_closedBall (x := (0 : Point)) (r := r)).subset
  intro x hx
  have hxnot : x ∉ planeImage D := by
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  have hle : ‖x‖ ≤ r := by
    by_contra h
    have hxc := hout x (lt_of_not_ge h)
    have hF' := (planeFaceRegion_mem D F ⟨x, hxnot⟩).mp hx
    have hC' := (planeFaceRegion_mem D C ⟨x, hxnot⟩).mp hxc
    exact hne (hF'.symm.trans hC')
  simpa using hle

/-- In the proper metric plane, precisely the unbounded sets accumulate at infinity. -/
lemma infty_mem_closure_image_iff (s : Set Point) :
    OnePoint.infty ∈ closure (OnePoint.some '' s) ↔ ¬Bornology.IsBounded s := by
  classical
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  constructor
  · intro h hs
    obtain ⟨r, hr⟩ := hs.subset_closedBall (0 : Point)
    obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := h (Metric.closedBall 0 r)
      ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
    rcases hz with ⟨y, hy, heq⟩ | hz
    · exact hy (OnePoint.coe_injective heq ▸ hr hx)
    · exact OnePoint.coe_ne_infty x hz
  · intro hs K hK
    have hnot : ¬s ⊆ K := fun h => hs (hK.2.isBounded.subset h)
    obtain ⟨x, hx, hxK⟩ := Set.not_subset.mp hnot
    exact ⟨OnePoint.some x, ⟨x, hx, rfl⟩, Or.inl ⟨x, hxK, rfl⟩⟩

lemma unbounded_plane_face_contains_exterior (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) :
    ∃ r : ℝ, 0 < r ∧ {x : Point | r < ‖x‖} ⊆ planeFaceRegion D C := by
  obtain ⟨r, hr, hcover⟩ := (plane_image_compact D).isBounded.subset_ball_lt 0 0
  have hnot : ¬planeFaceRegion D C ⊆ Metric.closedBall (0 : Point) r :=
    fun h => hC (Metric.isBounded_closedBall.subset h)
  obtain ⟨z, hz, hzr⟩ := Set.not_subset.mp hnot
  have hznot : z ∉ planeImage D := by
    obtain ⟨w, _, rfl⟩ := hz
    exact w.property
  have hzlarge : r < ‖z‖ := by simpa using hzr
  refine ⟨r, hr, fun x hx => ?_⟩
  have hxnot : x ∉ planeImage D := by
    intro h
    have : ‖x‖ < r := by simpa using hcover h
    exact (hx.trans this).false
  exact (planeFaceRegion_mem D C ⟨x, hxnot⟩).mpr
    ((plane_exterior_same_face D hr hcover ⟨x, hxnot⟩ ⟨z, hznot⟩ hx hzlarge).trans
      ((planeFaceRegion_mem D C ⟨z, hznot⟩).mp hz))

def liftedPlaneFaceRegion (C F : PlaneFace D) : Set Sphere :=
  OnePoint.some '' planeFaceRegion D F ∪ {x | x = OnePoint.infty ∧ F = C}

lemma liftedPlaneFaceRegion_subset (C F : PlaneFace D) :
    liftedPlaneFaceRegion D C F ⊆ (sphereImage D)ᶜ := by
  rintro x (⟨y, ⟨z, hz, rfl⟩, rfl⟩ | ⟨rfl, _⟩)
  · intro hx
    exact z.property ((sphere_image_membership D z.val).mp hx)
  · exact infinity_not_in_image D

lemma liftedPlaneFaceRegion_connected (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) (F : PlaneFace D) :
    IsConnected (liftedPlaneFaceRegion D C F) := by
  have h := (plane_face_region_connected D F).image _ OnePoint.continuous_coe.continuousOn
  apply h.subset_closure Set.subset_union_left
  rintro x (hx | ⟨rfl, rfl⟩)
  · exact subset_closure hx
  · exact (infty_mem_closure_image_iff _).mpr hC

lemma liftedPlaneFaceRegion_open (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) (F : PlaneFace D) :
    IsOpen (liftedPlaneFaceRegion D C F) := by
  classical
  have hfin := OnePoint.isOpen_image_coe.mpr (plane_face_region_open D F)
  by_cases hFC : F = C
  · subst F
    obtain ⟨r, hr, hout⟩ := unbounded_plane_face_contains_exterior D C hC
    have heq : liftedPlaneFaceRegion D C C =
        OnePoint.some '' planeFaceRegion D C ∪
          (OnePoint.some '' Metric.closedBall (0 : Point) r)ᶜ := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp [liftedPlaneFaceRegion]
      | coe y =>
        simp only [liftedPlaneFaceRegion, Set.mem_union, Set.mem_image,
          OnePoint.some_eq_iff, exists_eq_right, Set.mem_ofPred_eq, OnePoint.coe_ne_infty,
          false_and, or_false, Set.mem_compl_iff]
        exact ⟨Or.inl, fun h => h.elim id (fun hy => hout (by simpa using hy))⟩
    rw [heq]
    exact hfin.union (OnePoint.isOpen_compl_image_coe.mpr
      ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩)
  · have heq : liftedPlaneFaceRegion D C F = OnePoint.some '' planeFaceRegion D F := by
      ext x
      simp [liftedPlaneFaceRegion, hFC]
    rw [heq]
    exact hfin

@[simp] lemma some_mem_liftedPlaneFaceRegion (C F : PlaneFace D) (x : Point) :
    OnePoint.some x ∈ liftedPlaneFaceRegion D C F ↔ x ∈ planeFaceRegion D F := by
  simp [liftedPlaneFaceRegion]

@[simp] lemma infty_mem_liftedPlaneFaceRegion (C F : PlaneFace D) :
    OnePoint.infty ∈ liftedPlaneFaceRegion D C F ↔ F = C := by
  simp [liftedPlaneFaceRegion]

lemma liftedPlaneFaceRegion_disjoint (C : PlaneFace D) :
    Pairwise (fun F F' => Disjoint (liftedPlaneFaceRegion D C F)
      (liftedPlaneFaceRegion D C F')) := by
  intro F F' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  induction x using OnePoint.rec with
  | infty => exact hne ((infty_mem_liftedPlaneFaceRegion D C F).mp hx |>.trans
      ((infty_mem_liftedPlaneFaceRegion D C F').mp hx').symm)
  | coe y =>
    obtain ⟨z, hz, rfl⟩ := (some_mem_liftedPlaneFaceRegion D C F y).mp hx
    have hy' := (some_mem_liftedPlaneFaceRegion D C F' z.val).mp hx'
    exact hne (hz.symm.trans ((planeFaceRegion_mem D F' z).mp hy'))

def sphereFacePiece (C F : PlaneFace D) : Set (SphereComplement D) :=
  Subtype.val ⁻¹' liftedPlaneFaceRegion D C F

lemma sphereFacePiece_cover (C : PlaneFace D) :
    ⋃ F, sphereFacePiece D C F = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨x, hx⟩
  induction x using OnePoint.rec with
  | infty => exact Set.mem_iUnion.mpr ⟨C, Or.inr ⟨rfl, rfl⟩⟩
  | coe y =>
    have hy : y ∉ planeImage D := fun hy => hx ⟨y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk (⟨y, hy⟩ : PlaneComplement D),
      Or.inl ⟨y, ⟨⟨y, hy⟩, rfl, rfl⟩, rfl⟩⟩

lemma sphereFacePiece_disjoint (C : PlaneFace D) :
    Pairwise (fun F F' => Disjoint (sphereFacePiece D C F) (sphereFacePiece D C F')) :=
  fun _ _ hne => (liftedPlaneFaceRegion_disjoint D C hne).preimage Subtype.val

lemma sphereFacePiece_clopen (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) (F : PlaneFace D) :
    IsClopen (sphereFacePiece D C F) := by
  have ho (F) : IsOpen (sphereFacePiece D C F) :=
    (liftedPlaneFaceRegion_open D C hC F).preimage continuous_subtype_val
  refine ⟨?_, ho F⟩
  rw [← isOpen_compl_iff]
  have heq : (sphereFacePiece D C F)ᶜ =
      ⋃ F' : {F' : PlaneFace D // F' ≠ F}, sphereFacePiece D C F' := by
    ext x
    constructor
    · intro hx
      obtain ⟨F', hx'⟩ := Set.mem_iUnion.mp ((sphereFacePiece_cover D C) ▸ Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨F', fun h => hx (h ▸ hx')⟩, hx'⟩
    · intro hx hxF
      obtain ⟨F', hx'⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (sphereFacePiece_disjoint D C F'.property) hx' hxF
  rw [heq]
  exact isOpen_iUnion fun F' => ho F'

lemma sphereFacePiece_connected (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) (F : PlaneFace D) :
    IsConnected (sphereFacePiece D C F) := by
  apply (liftedPlaneFaceRegion_connected D C hC F).preimage_of_isOpenMap
    Subtype.val_injective (sphere_complement_open D).isOpenMap_subtype_val
  intro x hx
  exact ⟨⟨x, liftedPlaneFaceRegion_subset D C F hx⟩, rfl⟩

def sphereFacePiecesEquiv (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C)) : Face D ≃ PlaneFace D :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (sphereFacePiece_clopen D C hC) (sphereFacePiece_disjoint D C)
    (sphereFacePiece_cover D C) (sphereFacePiece_connected D C hC)

lemma sphereFacePiecesEquiv_mk (C : PlaneFace D)
    (hC : ¬Bornology.IsBounded (planeFaceRegion D C))
    (x : SphereComplement D) (F : PlaneFace D) :
    sphereFacePiecesEquiv D C hC (ConnectedComponents.mk x) = F ↔
      x.val ∈ liftedPlaneFaceRegion D C F := by
  have hm (J) (hx : x ∈ sphereFacePiece D C J) :
      sphereFacePiecesEquiv D C hC (ConnectedComponents.mk x) = J :=
    ConnectedComponents.equivOfIsClopenOfIsConnected_mk
      (sphereFacePiece_clopen D C hC) (sphereFacePiece_disjoint D C)
      (sphereFacePiece_cover D C) (sphereFacePiece_connected D C hC) x hx
  constructor
  · intro hx
    obtain ⟨J, hxJ⟩ := Set.mem_iUnion.mp ((sphereFacePiece_cover D C) ▸ Set.mem_univ x)
    exact (hx.symm.trans (hm J hxJ)) ▸ hxJ
  · exact hm F

theorem plane_sphere_faces : plane_sphere_facesType := by
  intro V _ G D
  obtain ⟨C, hC⟩ := unique_unbounded_plane_face D
  have hCu := (hC C).mp rfl
  let Q := sphereFacePiecesEquiv D C hCu
  let E := Q.symm
  have hfinite (x : PlaneComplement D) :
      Q (ConnectedComponents.mk (complementInclusion D x)) = ConnectedComponents.mk x :=
    (sphereFacePiecesEquiv_mk D C hCu _ _).mpr
      ((some_mem_liftedPlaneFaceRegion D C _ x.val).mpr
        ((planeFaceRegion_mem D _ x).mpr rfl))
  have hinfty : Q (unboundedFace D) = C :=
    (sphereFacePiecesEquiv_mk D C hCu _ C).mpr (Or.inr ⟨rfl, rfl⟩)
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x
    exact (Q.symm_apply_eq).mpr (hfinite x).symm
  · intro F
    ext z
    induction z using OnePoint.rec with
    | infty => simp
    | coe y =>
      constructor
      · rintro ⟨y', hy', heq⟩
        have heqy : y' = y := OnePoint.coe_injective heq
        subst y'
        obtain ⟨x, hx, rfl⟩ := hy'
        refine ⟨⟨complementInclusion D x, ?_, rfl⟩, OnePoint.coe_ne_infty x.val⟩
        change ConnectedComponents.mk (complementInclusion D x) = E F
        apply Q.injective
        change Q (ConnectedComponents.mk (complementInclusion D x)) = Q (Q.symm F)
        rw [Q.apply_symm_apply]
        exact (hfinite x).trans hx
      · rintro ⟨⟨x, hx, hxval⟩, _⟩
        have hy : y ∉ planeImage D := fun hy => x.property
          (hxval.symm ▸ (show OnePoint.some y ∈ sphereImage D from ⟨y, hy, rfl⟩))
        let y' : PlaneComplement D := ⟨y, hy⟩
        have hxy : x = complementInclusion D y' := Subtype.ext hxval
        have hm : ConnectedComponents.mk y' = F := by
          have hh := congrArg Q hx
          rw [hxy, hfinite] at hh
          exact hh.trans (Q.apply_symm_apply F)
        exact ⟨y, (planeFaceRegion_mem D F y').mpr hm, rfl⟩
  · intro F
    rw [← hC F]
    constructor
    · intro h
      have hh := congrArg Q h
      exact (Q.apply_symm_apply F).symm.trans (hh.trans hinfty)
    · intro h
      apply Q.injective
      exact (Q.apply_symm_apply F).trans (h.trans hinfty.symm)

end Faces

lemma finite_arcs_initial_subset {ι E : Type*} [Finite ι] [TopologicalSpace E]
    (p : ι → unitInterval → E) (hp : ∀ i, Continuous (p i))
    (c : E) (h0 : ∀ i, p i 0 = c) {U : Set E} (hU : U ∈ nhds c) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ i (s : unitInterval), (s : ℝ) ≤ t → p i s ∈ U := by
  have hi : (⋂ i, p i ⁻¹' U) ∈ nhds (0 : unitInterval) := by
    apply Filter.iInter_mem.mpr
    intro i
    exact (hp i).continuousAt.preimage_mem_nhds ((h0 i).symm ▸ hU)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hi
  refine ⟨min (r / 2) (1 / 2), lt_min (by positivity) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro i s hs
  have hsr : dist s (0 : unitInterval) < r := by
    change dist (s : ℝ) 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg s.property.1]
    exact hs.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  exact Set.mem_iInter.mp (hsub hsr) i

namespace StarGluing
open Set

lemma finiteStar_mem_iff {n : ℕ} (x : Fin n → ℝ) :
    x ∈ finiteStar n ↔ x = 0 ∨ ∃ (i : Fin n) (t : unitInterval), x = Pi.single i (t : ℝ) := by
  simp only [finiteStar, mem_union, mem_singleton_iff, mem_iUnion]
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  rw [segment_eq_image]
  simp only [smul_zero, zero_add, mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, by ext j; by_cases h : j = i <;> simp [h]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, t.property, by ext j; by_cases h : j = i <;> simp [h]⟩

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Ambient extension of an arbitrary finite family of arms with common center. -/
def armMap {n : ℕ} (c : E) (p : Fin n → unitInterval → E) (x : Fin n → ℝ) : E :=
  c + ∑ i, (p i (Set.projIcc 0 1 (by norm_num) (x i)) - c)

lemma continuous_armMap {n : ℕ} (c : E) (p : Fin n → unitInterval → E)
    (hp : ∀ i, Continuous (p i)) : Continuous (armMap c p) := by
  apply continuous_const.add
  exact continuous_finsetSum _ (fun i _ =>
    ((hp i).comp (continuous_projIcc.comp (continuous_apply i))).sub continuous_const)

lemma armMap_zero {n : ℕ} (c : E) (p : Fin n → unitInterval → E)
    (hp0 : ∀ i, p i 0 = c) : armMap c p 0 = c := by
  simp [armMap, hp0]

lemma armMap_single {n : ℕ} (c : E) (p : Fin n → unitInterval → E)
    (hp0 : ∀ i, p i 0 = c) (i : Fin n) (t : unitInterval) :
    armMap c p (Pi.single i (t : ℝ)) = p i t := by
  unfold armMap
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, Set.projIcc_of_mem _ t.property]
    exact add_sub_cancel _ _
  · intro j _ hji
    simp [hji, hp0]
  · simp

lemma armMap_injective {n : ℕ} (c : E) (p : Fin n → unitInterval → E)
    (hp0 : ∀ i, p i 0 = c)
    (hsep : ∀ i j s t, p i s = p j t → (i = j ∧ s = t) ∨ (s = 0 ∧ t = 0)) :
    Function.Injective (fun x : finiteStar n => armMap c p x.val) := by
  intro x y hxy
  change armMap c p x.val = armMap c p y.val at hxy
  apply Subtype.ext
  rcases (finiteStar_mem_iff x.val).mp x.property with hx | ⟨i, s, hx⟩ <;>
    rcases (finiteStar_mem_iff y.val).mp y.property with hy | ⟨j, t, hy⟩
  · exact hx.trans hy.symm
  · rw [hx, hy, armMap_zero c p hp0, armMap_single c p hp0] at hxy
    have ht : t = 0 := by
      rcases hsep j j 0 t ((hp0 j).trans hxy) with h | h
      · exact h.2.symm
      · exact h.2
    simp [ht, hx, hy]
  · rw [hx, hy, armMap_single c p hp0, armMap_zero c p hp0] at hxy
    have hs : s = 0 := by
      rcases hsep i i s 0 (hxy.trans (hp0 i).symm) with h | h
      · exact h.2
      · exact h.1
    simp [hs, hx, hy]
  · rw [hx, hy, armMap_single c p hp0, armMap_single c p hp0] at hxy
    rcases hsep i j s t hxy with ⟨hij, hst⟩ | ⟨hs, ht⟩
    · simp [hx, hy, hij, hst]
    · simp [hx, hy, hs, ht]

lemma armMap_range {n : ℕ} (c : E) (p : Fin n → unitInterval → E)
    (hp0 : ∀ i, p i 0 = c) :
    Set.range (fun x : finiteStar n => armMap c p x.val) = {c} ∪ ⋃ i, Set.range (p i) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases (finiteStar_mem_iff x.val).mp x.property with hx | ⟨i, t, hx⟩
    · left
      simp [hx, armMap_zero c p hp0]
    · right
      change armMap c p x.val ∈ _
      rw [hx, armMap_single c p hp0]
      exact mem_iUnion.mpr ⟨i, mem_range_self _⟩
  · intro hz
    rcases hz with hz | hz
    · have hzc : z = c := hz
      subst z
      exact ⟨⟨0, (finiteStar_mem_iff _).mpr (Or.inl rfl)⟩, armMap_zero c p hp0⟩
    · rcases mem_iUnion.mp hz with ⟨i, t, rfl⟩
      exact ⟨⟨Pi.single i (t : ℝ), (finiteStar_mem_iff _).mpr (Or.inr ⟨i, t, rfl⟩)⟩,
        armMap_single c p hp0 i t⟩

lemma isCompact_finiteStar (n : ℕ) : IsCompact (finiteStar n) := by
  apply isCompact_singleton.union
  apply isCompact_iUnion
  intro i
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem finiteStar_homeomorph_arms [T2Space E] {n : ℕ}
    (c : E) (p : Fin n → unitInterval → E)
    (hp : ∀ i, Continuous (p i)) (hp0 : ∀ i, p i 0 = c)
    (hsep : ∀ i j s t, p i s = p j t → (i = j ∧ s = t) ∨ (s = 0 ∧ t = 0)) :
    ∃ h : finiteStar n ≃ₜ ↥({c} ∪ ⋃ i, Set.range (p i)),
      (h ⟨0, (finiteStar_mem_iff _).mpr (Or.inl rfl)⟩).val = c := by
  haveI : CompactSpace (finiteStar n) := isCompact_iff_compactSpace.mp (isCompact_finiteStar n)
  let F : finiteStar n → E := fun x => armMap c p x.val
  have hF : Continuous F := (continuous_armMap c p hp).comp continuous_subtype_val
  have hFi : Function.Injective F := armMap_injective c p hp0 hsep
  let h : finiteStar n ≃ₜ ↥({c} ∪ ⋃ i, Set.range (p i)) :=
    hF.isClosedEmbedding hFi |>.isEmbedding.toHomeomorph |>.trans
      (Homeomorph.setCongr (armMap_range c p hp0))
  exact ⟨h, armMap_zero c p hp0⟩

theorem arms_homeomorph_finiteStar [T2Space E] {n : ℕ}
    (c : E) (p : Fin n → unitInterval → E)
    (hp : ∀ i, Continuous (p i)) (hp0 : ∀ i, p i 0 = c)
    (hsep : ∀ i j s t, p i s = p j t → (i = j ∧ s = t) ∨ (s = 0 ∧ t = 0)) :
    ∃ h : ↥({c} ∪ ⋃ i, Set.range (p i)) ≃ₜ finiteStar n,
      (h ⟨c, Or.inl rfl⟩).val = 0 := by
  obtain ⟨h, hc⟩ := finiteStar_homeomorph_arms c p hp hp0 hsep
  have heq : h ⟨0, (finiteStar_mem_iff _).mpr (Or.inl rfl)⟩ = ⟨c, Or.inl rfl⟩ :=
    Subtype.ext hc
  refine ⟨h.symm, ?_⟩
  rw [← heq, h.symm_apply_apply]

end StarGluing

section VertexStar
variable {V : Type u} [Finite V] {G : SimpleGraph V} (D : PlaneEmbedding G) (v : V)

def incidentEdge (w : G.neighborSet v) : G.edgeSet := ⟨s(v, w.val), w.property⟩

lemma incidentEdge_injective : Function.Injective (incidentEdge (G := G) v) := by
  intro a b hab
  apply Subtype.ext
  have h : a.val ∈ (incidentEdge (G := G) v b).val := by
    rw [← hab]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  rcases Sym2.mem_iff.mp h with hav | hab
  · exact False.elim (a.property.ne hav.symm)
  · exact hab

lemma edge_eq_incidentEdge (e : G.edgeSet) (hv : v ∈ e.val) :
    ∃ w : G.neighborSet v, e = incidentEdge v w := by
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.val
  have hadj : G.Adj a b := by simpa [← hab] using e.property
  have hv' : v = a ∨ v = b := Sym2.mem_iff.mp (by simpa [← hab] using hv)
  rcases hv' with rfl | rfl
  · exact ⟨⟨b, hadj⟩, Subtype.ext hab.symm⟩
  · exact ⟨⟨a, hadj.symm⟩, Subtype.ext (hab.symm.trans (Sym2.eq_swap))⟩

def incidentPath (w : G.neighborSet v) : _root_.Path (D.point v) (D.point w.val) :=
  Classical.choose (D.edge_arc v w.val w.property).2

lemma incidentPath_injective (w : G.neighborSet v) : Function.Injective (incidentPath D v w) :=
  (Classical.choose_spec (D.edge_arc v w.val w.property).2).1

lemma incidentPath_range (w : G.neighborSet v) :
    Set.range (incidentPath D v w) = D.edge (incidentEdge v w) :=
  (Classical.choose_spec (D.edge_arc v w.val w.property).2).2

lemma incidentPath_mem (w : G.neighborSet v) (s : unitInterval) :
    incidentPath D v w s ∈ D.edge (incidentEdge v w) := by
  rw [← incidentPath_range]
  exact Set.mem_range_self s

lemma incidentPath_eq_vertex (w : G.neighborSet v) (s : unitInterval) (z : V)
    (heq : incidentPath D v w s = D.point z) : s = 0 ∨ s = 1 := by
  have hz : z ∈ (incidentEdge v w).val :=
    (D.vertex_edge (incidentEdge v w) z).mp (heq ▸ incidentPath_mem D v w s)
  rcases Sym2.mem_iff.mp hz with hz | hz
  · left
    apply incidentPath_injective D v w
    simpa [hz] using heq
  · right
    apply incidentPath_injective D v w
    simpa [hz] using heq


def scaleUnit (t : ℝ) (ht : t ∈ unitInterval) (s : unitInterval) : unitInterval :=
  ⟨t * s.val, unitInterval.mul_mem ht s.property⟩

lemma scaleUnit_continuous (t : ℝ) (ht : t ∈ unitInterval) : Continuous (scaleUnit t ht) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

lemma scaleUnit_zero (t : ℝ) (ht : t ∈ unitInterval) : scaleUnit t ht 0 = 0 := by
  apply Subtype.ext
  simp [scaleUnit]

lemma scaleUnit_injective (t : ℝ) (ht : t ∈ unitInterval) (htpos : 0 < t) :
    Function.Injective (scaleUnit t ht) := by
  intro a b h
  apply Subtype.ext
  exact mul_left_cancel₀ (ne_of_gt htpos) (congrArg Subtype.val h)


def truncatedIncidentPath (t : ℝ) (ht : t ∈ unitInterval) (w : G.neighborSet v) :
    unitInterval → Point := fun s => incidentPath D v w (scaleUnit t ht s)

lemma truncatedIncidentPath_continuous (t : ℝ) (ht : t ∈ unitInterval)
    (w : G.neighborSet v) : Continuous (truncatedIncidentPath D v t ht w) :=
  (incidentPath D v w).continuous.comp (scaleUnit_continuous t ht)

lemma truncatedIncidentPath_zero (t : ℝ) (ht : t ∈ unitInterval)
    (w : G.neighborSet v) : truncatedIncidentPath D v t ht w 0 = D.point v := by
  simp [truncatedIncidentPath, scaleUnit_zero]

lemma truncatedIncidentPath_eq_vertex (t : ℝ) (ht : t ∈ unitInterval)
    (htpos : 0 < t) (htone : t < 1) (w : G.neighborSet v)
    (s : unitInterval) (z : V)
    (heq : truncatedIncidentPath D v t ht w s = D.point z) : s = 0 := by
  have hs := incidentPath_eq_vertex D v w (scaleUnit t ht s) z heq
  have hlt : (scaleUnit t ht s).val < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ht.1 s.property.2) htone
  have hzero : scaleUnit t ht s = 0 := hs.resolve_right (by
    intro hs1
    have := congrArg Subtype.val hs1
    exact ne_of_lt hlt this)
  exact scaleUnit_injective t ht htpos (hzero.trans (scaleUnit_zero t ht).symm)

lemma truncatedIncidentPath_collisions (t : ℝ) (ht : t ∈ unitInterval)
    (htpos : 0 < t) (htone : t < 1) (a b : G.neighborSet v)
    (s r : unitInterval)
    (heq : truncatedIncidentPath D v t ht a s = truncatedIncidentPath D v t ht b r) :
    (a = b ∧ s = r) ∨ (s = 0 ∧ r = 0) := by
  by_cases hab : a = b
  · subst b
    left
    exact ⟨rfl, scaleUnit_injective t ht htpos (incidentPath_injective D v a heq)⟩
  · have hef : incidentEdge v a ≠ incidentEdge v b :=
      fun h => hab (incidentEdge_injective v h)
    have hx : truncatedIncidentPath D v t ht a s ∈
        D.edge (incidentEdge v a) ∩ D.edge (incidentEdge v b) :=
      ⟨incidentPath_mem D v a _, heq ▸ incidentPath_mem D v b _⟩
    rw [D.edge_intersection _ _ hef] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    right
    exact ⟨truncatedIncidentPath_eq_vertex D v t ht htpos htone a s z hzx.symm,
      truncatedIncidentPath_eq_vertex D v t ht htpos htone b r z (hzx.trans heq).symm⟩



lemma truncatedIncident_union_subset (t : ℝ) (ht : t ∈ unitInterval) :
    ({D.point v} ∪ ⋃ w : G.neighborSet v,
      Set.range (truncatedIncidentPath D v t ht w)) ⊆ planeImage D := by
  rintro x (hx | hx)
  · exact Or.inl (hx ▸ Set.mem_range_self v)
  · obtain ⟨w, s, rfl⟩ := Set.mem_iUnion.mp hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨incidentEdge v w, incidentPath_mem D v w _⟩)

lemma truncatedIncident_union_nhds (t : ℝ) (ht : t ∈ unitInterval)
    (htpos : 0 < t) :
    (Subtype.val : PlaneRealization D → Point) ⁻¹'
      ({D.point v} ∪ ⋃ w : G.neighborSet v,
        Set.range (truncatedIncidentPath D v t ht w)) ∈
      nhds (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) := by
  let T (w : G.neighborSet v) : Set Point :=
    incidentPath D v w '' {s : unitInterval | t ≤ s.val}
  let K : Set Point :=
    (Set.range (fun w : {w : V // w ≠ v} => D.point w.val) ∪
      ⋃ e : {e : G.edgeSet // v ∉ e.val}, D.edge e.val) ∪ ⋃ w, T w
  have hT : ∀ w, IsCompact (T w) := by
    intro w
    exact (isClosed_le continuous_const continuous_subtype_val).isCompact.image
      (incidentPath D v w).continuous
  have hK : IsClosed K :=
    (((Set.finite_range (fun w : {w : V // w ≠ v} => D.point w.val)).isCompact.union
      (isCompact_iUnion fun e : {e : G.edgeSet // v ∉ e.val} => edge_compact D e.val)).union
      (isCompact_iUnion hT)).isClosed
  have hvK : D.point v ∉ K := by
    rintro ((hv | he) | hs)
    · obtain ⟨⟨w, hw⟩, heq⟩ := hv
      exact hw (D.point_injective heq)
    · obtain ⟨⟨e, he⟩, hmem⟩ := Set.mem_iUnion.mp he
      exact he ((D.vertex_edge e v).mp hmem)
    · obtain ⟨w, s, hs, heq⟩ := Set.mem_iUnion.mp hs
      have hz : s = 0 := incidentPath_injective D v w (heq.trans (incidentPath D v w).source.symm)
      have : t ≤ 0 := by simpa [hz] using hs
      exact (not_le_of_gt htpos) this
  have hsub : (Subtype.val : PlaneRealization D → Point) ⁻¹' Kᶜ ⊆
      (Subtype.val : PlaneRealization D → Point) ⁻¹'
        ({D.point v} ∪ ⋃ w : G.neighborSet v,
          Set.range (truncatedIncidentPath D v t ht w)) := by
    intro x hx
    rcases x.property with ⟨w, hw⟩ | he
    · by_cases hwv : w = v
      · exact Or.inl (by simpa [hwv] using hw.symm)
      · exact False.elim (hx (Or.inl (Or.inl ⟨⟨w, hwv⟩, hw⟩)))
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp he
      have hv : v ∈ e.val := by
        by_contra hv
        exact hx (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨e, hv⟩, he⟩)))
      obtain ⟨w, rfl⟩ := edge_eq_incidentEdge v e hv
      rw [← incidentPath_range D v w] at he
      obtain ⟨s, hs⟩ := he
      have hst : s.val < t := by
        by_contra hn
        exact hx (Or.inr (Set.mem_iUnion.mpr ⟨w, s, le_of_not_gt hn, hs⟩))
      let r : unitInterval := ⟨s.val / t, div_nonneg s.property.1 htpos.le,
        (div_le_one htpos).mpr hst.le⟩
      have hrs : scaleUnit t ht r = s := by
        apply Subtype.ext
        change t * (s.val / t) = s.val
        exact mul_div_cancel₀ _ (ne_of_gt htpos)
      refine Or.inr (Set.mem_iUnion.mpr ⟨w, r, ?_⟩)
      change incidentPath D v w (scaleUnit t ht r) = x.val
      exact hrs ▸ hs
  exact Filter.mem_of_superset
    ((hK.isOpen_compl.preimage continuous_subtype_val).mem_nhds hvK) hsub



theorem plane_vertex_star_local_model
    (U : Set (PlaneRealization D))
    (hU : U ∈ nhds (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D)) :
    ∃ N : Set (PlaneRealization D),
      N ∈ nhds (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) ∧
      N ⊆ U ∧
      ∃ (hv : (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) ∈ N)
        (h : N ≃ₜ ↥(finiteStar (Nat.card (G.neighborSet v)))),
        (h ⟨⟨D.point v, Or.inl (Set.mem_range_self v)⟩, hv⟩).val = 0 := by
  classical
  have hnhds : nhds (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) =
      Filter.comap (Subtype.val : PlaneRealization D → Point) (nhds (D.point v)) :=
    nhds_subtype_eq_comap
  rw [hnhds] at hU
  obtain ⟨O, hO, hOU⟩ := Filter.mem_comap.mp hU
  obtain ⟨t, htpos, htone, htsub⟩ := finite_arcs_initial_subset
    (fun w : G.neighborSet v => (incidentPath D v w : unitInterval → Point))
    (fun w => (incidentPath D v w).continuous) (D.point v)
    (fun w => (incidentPath D v w).source) hO
  let ht : t ∈ unitInterval := ⟨htpos.le, htone.le⟩
  let W : Set Point := {D.point v} ∪ ⋃ w : G.neighborSet v,
    Set.range (truncatedIncidentPath D v t ht w)
  let N : Set (PlaneRealization D) := Subtype.val ⁻¹' W
  have hN : N ∈ nhds (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) :=
    truncatedIncident_union_nhds D v t ht htpos
  have hNW : (Subtype.val : PlaneRealization D → Point) '' N = W := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x, truncatedIncident_union_subset D v t ht hx⟩, rfl⟩
  let hNW' : N ≃ₜ W := Topology.IsEmbedding.subtypeVal.homeomorphImage N |>.trans
    (Homeomorph.setCongr hNW)
  have hNU : N ⊆ U := by
    intro x hx
    apply hOU
    change x.val ∈ O
    rcases hx with hx | hx
    · have hxv : x.val = D.point v := hx
      exact hxv ▸ mem_of_mem_nhds hO
    · obtain ⟨w, s, hs⟩ := Set.mem_iUnion.mp hx
      exact hs ▸ htsub w (scaleUnit t ht s)
        (mul_le_of_le_one_right ht.1 s.property.2)
  let e : Fin (Nat.card (G.neighborSet v)) ≃ G.neighborSet v :=
    (Finite.equivFin (G.neighborSet v)).symm
  let q : Fin (Nat.card (G.neighborSet v)) → unitInterval → Point :=
    fun i => truncatedIncidentPath D v t ht (e i)
  have hW : ({D.point v} ∪ ⋃ i, Set.range (q i)) = W := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨e i, hi⟩)
    · rintro (hx | hx)
      · exact Or.inl hx
      · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨e.symm w, by
          change x ∈ Set.range (truncatedIncidentPath D v t ht (e (e.symm w)))
          rw [e.apply_symm_apply]
          exact hw⟩)
  obtain ⟨h, hc⟩ := StarGluing.arms_homeomorph_finiteStar (D.point v) q
    (fun i => truncatedIncidentPath_continuous D v t ht (e i))
    (fun i => truncatedIncidentPath_zero D v t ht (e i))
    (by
      intro i j s r hij
      rcases truncatedIncidentPath_collisions D v t ht htpos htone (e i) (e j) s r hij with
        ⟨he, hsr⟩ | hzero
      · exact Or.inl ⟨e.injective he, hsr⟩
      · exact Or.inr hzero)
  let H : N ≃ₜ finiteStar (Nat.card (G.neighborSet v)) :=
    hNW'.trans ((Homeomorph.setCongr hW.symm).trans h)
  have hv : (⟨D.point v, Or.inl (Set.mem_range_self v)⟩ : PlaneRealization D) ∈ N :=
    Or.inl rfl
  refine ⟨N, hN, hNU, hv, H, ?_⟩
  exact hc
end VertexStar

theorem vertex_star_local_model : vertex_star_local_modelType := by
  intro V _ G D v U hU
  let z : PlaneRealization D := ⟨D.point v, Or.inl (Set.mem_range_self v)⟩
  let H := realization_homeomorph D
  have Hz : H z = realizationVertex D v := Subtype.ext rfl
  have hU' : H ⁻¹' U ∈ nhds z :=
    H.continuous.continuousAt.preimage_mem_nhds (Hz.symm ▸ hU)
  obtain ⟨N, hN, hNU, hzN, h, hc⟩ := plane_vertex_star_local_model D v (H ⁻¹' U) hU'
  refine ⟨H '' N, ?_, ?_, ?_⟩
  · have hn : H '' N ∈ nhds (H z) := H.isOpenMap.image_mem_nhds hN
    rwa [Hz] at hn
  · rintro _ ⟨x, hx, rfl⟩
    exact hNU hx
  · have hzN' : realizationVertex D v ∈ H '' N := ⟨z, hzN, Hz⟩
    refine ⟨hzN', (H.image N).symm.trans h, ?_⟩
    have heq : (H.image N).symm ⟨realizationVertex D v, hzN'⟩ = ⟨z, hzN⟩ := by
      apply (H.image N).injective
      simp only [Homeomorph.apply_symm_apply]
      exact Subtype.ext Hz.symm
    change (h ((H.image N).symm ⟨realizationVertex D v, hzN'⟩)).val = 0
    rw [heq]
    exact hc


end FiniteCombinatorics.Graph.Plane
