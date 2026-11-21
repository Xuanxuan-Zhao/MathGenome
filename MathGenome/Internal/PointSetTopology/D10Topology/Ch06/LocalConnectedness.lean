import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.LocalConnectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.ComponentsAndPaths
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods

/-! Local connectedness using the paper's possibly nonopen neighborhoods.
All comparisons below use the already proved source predicates. In particular,
the library's nonempty path-connected sets are used only for neighborhoods
(which contain their base point). -/

open Set Topology
universe u v

namespace D10Topology.Ch06

variable {X : Type u} [t : TopologicalSpace X]

def LocallyConnectedAt (x : X) : Prop := LocalConnectednessData.LocallyConnectedAt x
def LocallyPathConnectedAt (x : X) : Prop := LocalConnectednessData.LocallyPathConnectedAt x

def LocallyConnected (X : Type u) [TopologicalSpace X] : Prop :=
  LocalConnectednessData.LocallyConnected X

def LocallyPathConnected (X : Type u) [TopologicalSpace X] : Prop :=
  LocalConnectednessData.LocallyPathConnected X

theorem locallyConnectedAt_iff_nhds (x : X) :
    LocallyConnectedAt x ↔
      ∀ N ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ N := by
  change (∀ N : Set X, Ch01.Neighborhood t x N →
    ∃ V : Set X, Ch01.Neighborhood t x V ∧ ConnectedSubset V ∧ V ⊆ N) ↔ _
  simp_rw [Ch01.neighborhood_iff_mem_nhds, connectedSubset_iff_isPreconnected]

theorem locallyPathConnectedAt_iff_nhds (x : X) :
    LocallyPathConnectedAt x ↔
      ∀ N ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPathConnected V ∧ V ⊆ N := by
  change (∀ N : Set X, Ch01.Neighborhood t x N →
    ∃ V : Set X, Ch01.Neighborhood t x V ∧ PathConnectedSubset V ∧ V ⊆ N) ↔ _
  simp_rw [Ch01.neighborhood_iff_mem_nhds]
  constructor
  · intro h N hN
    obtain ⟨V, hV, hVc, hVN⟩ := h N hN
    have hx : x ∈ V := mem_of_mem_nhds hV
    exact ⟨V, hV, ⟨x, hx, fun y hy => hVc x hx y hy⟩, hVN⟩
  · intro h N hN
    obtain ⟨V, hV, hVc, hVN⟩ := h N hN
    exact ⟨V, hV, hVc.joinedIn, hVN⟩

theorem locallyConnected_iff_mathlib (X : Type u) [TopologicalSpace X] :
    LocallyConnected X ↔ LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' (fun x => locallyConnectedAt_iff_nhds x)

theorem locallyPathConnected_iff_mathlib (X : Type u) [TopologicalSpace X] :
    LocallyPathConnected X ↔ LocallyPathConnectedSpace X := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    rw [Filter.hasBasis_self]
    exact (locallyPathConnectedAt_iff_nhds x).mp (h x)
  · intro h x
    apply (locallyPathConnectedAt_iff_nhds x).mpr
    exact (Filter.hasBasis_self.mp (h.path_connected_basis x))

/-- Components of subspaces are included in the ambient space by Subtype.val. -/
private theorem component_subspace_image (U : Set X) (x : U) :
    (Subtype.val : U → X) '' Component x = connectedComponentIn U x.val := by
  rw [component_eq_mathlib, connectedComponentIn_eq_image x.property]

private theorem pathComponent_subspace_image (U : Set X) (x : U) :
    (Subtype.val : U → X) '' PathComponent x = pathComponentIn U x.val := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (joinedIn_iff_joined x.property z.property).mpr hz
  · intro hy
    have hyU : y ∈ U := pathComponentIn_subset hy
    exact ⟨⟨y, hyU⟩, (joinedIn_iff_joined x.property hyU).mp hy, rfl⟩

theorem locallyConnected_iff_open_components (X : Type u) [TopologicalSpace X] :
    LocallyConnected X ↔
      ∀ U : Set X, IsOpen U → ∀ x : U,
        IsOpen ((Subtype.val : U → X) '' Component x) := by
  rw [locallyConnected_iff_mathlib, locallyConnectedSpace_iff_connectedComponentIn_open]
  constructor
  · intro h U hU x
    rw [component_subspace_image]
    exact h U hU x.val x.property
  · intro h U hU x hx
    simpa only [component_subspace_image] using h U hU ⟨x, hx⟩

theorem locallyPathConnected_iff_open_pathComponents (X : Type u) [TopologicalSpace X] :
    LocallyPathConnected X ↔
      ∀ U : Set X, IsOpen U → ∀ x : U,
        IsOpen ((Subtype.val : U → X) '' PathComponent x) := by
  rw [locallyPathConnected_iff_mathlib]
  constructor
  · intro h U hU x
    rw [pathComponent_subspace_image]
    exact hU.pathComponentIn _
  · intro h
    apply locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
    intro x U hU hx
    have hopen : IsOpen (pathComponentIn U x) := by
      simpa only [pathComponent_subspace_image] using h U hU ⟨x, hx⟩
    exact hopen.mem_nhds (mem_pathComponentIn_self hx)

theorem locallyConnected_iff_connected_open_basis (X : Type u) [t : TopologicalSpace X] :
    LocallyConnected X ↔ Ch01.BasisFor t {U : Set X | IsOpen U ∧ ConnectedSubset U} := by
  rw [locallyConnected_iff_mathlib, Ch01.basis_iff_mathlib]
  simp_rw [connectedSubset_iff_isPreconnected]
  exact locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected

theorem locallyPathConnected_iff_pathConnected_open_basis
    (X : Type u) [t : TopologicalSpace X] :
    LocallyPathConnected X ↔
      Ch01.BasisFor t {U : Set X | IsOpen U ∧ PathConnectedSubset U} := by
  rw [locallyPathConnected_iff_mathlib, Ch01.basis_iff_mathlib]
  constructor
  · intro h
    apply TopologicalSpace.IsTopologicalBasis.of_hasBasis_nhds
    intro x
    exact (isOpen_isPathConnected_basis x).congr
      (fun U => by
        constructor
        · rintro ⟨hU, hx, hc⟩
          exact ⟨⟨hU, hc.joinedIn⟩, hx⟩
        · rintro ⟨⟨hU, hc⟩, hx⟩
          exact ⟨hU, hx, ⟨x, hx, fun y hy => hc x hx y hy⟩⟩)
      (fun _ _ => rfl)
  · intro h
    refine ⟨fun x => ?_⟩
    rw [Filter.hasBasis_self]
    intro N hN
    obtain ⟨U, ⟨⟨hU, hc⟩, hx⟩, hUN⟩ := h.nhds_hasBasis.mem_iff.mp hN
    exact ⟨U, hU.mem_nhds hx, ⟨x, hx, fun y hy => hc x hx y hy⟩, hUN⟩

theorem component_eq_pathComponent_of_locallyPathConnected
    (h : LocallyPathConnected X) (x : X) : Component x = PathComponent x := by
  letI := (locallyPathConnected_iff_mathlib X).mp h
  rw [component_eq_mathlib, pathComponent_eq_mathlib]
  exact (pathComponent_eq_connectedComponent x).symm

theorem locallyPathConnected_implies_locallyConnected
    (X : Type u) [TopologicalSpace X] (h : LocallyPathConnected X) : LocallyConnected X := by
  letI := (locallyPathConnected_iff_mathlib X).mp h
  exact (locallyConnected_iff_mathlib X).mpr inferInstance

theorem locallyConnected_open_subspace (h : LocallyConnected X)
    (U : Set X) (hU : IsOpen U) : LocallyConnected U := by
  letI := (locallyConnected_iff_mathlib X).mp h
  exact (locallyConnected_iff_mathlib U).mpr hU.locallyConnectedSpace

theorem locallyPathConnected_open_subspace (h : LocallyPathConnected X)
    (U : Set X) (hU : IsOpen U) : LocallyPathConnected U := by
  letI := (locallyPathConnected_iff_mathlib X).mp h
  exact (locallyPathConnected_iff_mathlib U).mpr hU.locallyPathConnectedSpace

theorem locallyConnected_quotient_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (q : X → Y)
    (hq : Ch03.QuotientMap q) (hX : LocallyConnected X) : LocallyConnected Y := by
  letI := (locallyConnected_iff_mathlib X).mp hX
  exact (locallyConnected_iff_mathlib Y).mpr
    ((Ch03.quotientMap_iff_mathlib q).mp hq).isCoinducing.locallyConnectedSpace

end D10Topology.Ch06
