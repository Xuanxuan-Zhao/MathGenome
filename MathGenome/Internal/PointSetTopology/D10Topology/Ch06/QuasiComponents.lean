import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.QuasiComponents
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.ComponentsAndPaths
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Separation.Regular

/-! Quasi-components and zero-dimensionality with the source's separation
conventions. Mathlib's compact Hausdorff component theorem applies to the
actual intersection of clopen neighborhoods. The refinement theorem below
uses compactness of a directed family of closed sets. -/

open Set Topology
universe u

namespace D10Topology.Ch06

def QuasiComponent {X : Type u} [TopologicalSpace X] (x : X) : Set X :=
  QuasiComponentsData.QuasiComponent x

def TotallyDisconnected (X : Type u) [TopologicalSpace X] : Prop :=
  QuasiComponentsData.TotallyDisconnected X

def ZeroDimensional (X : Type u) [TopologicalSpace X] : Prop :=
  QuasiComponentsData.ZeroDimensional X

variable {X : Type u} [TopologicalSpace X]

theorem mem_quasiComponent (x y : X) :
    y ∈ QuasiComponent x ↔ ∀ H : Set X, IsClopen H → x ∈ H → y ∈ H := by
  simp only [QuasiComponent, QuasiComponentsData.QuasiComponent, mem_sInter,
    mem_ofPred_eq, and_imp]

theorem component_subset_quasiComponent (x : X) : Component x ⊆ QuasiComponent x := by
  intro y hy
  exact (mem_quasiComponent x y).mpr fun H hH hx =>
    hH.connectedComponent_subset hx ((component_eq_mathlib x) ▸ hy)

theorem quasiComponent_eq_component [CompactSpace X] [T2Space X] (x : X) :
    QuasiComponent x = Component x := by
  rw [component_eq_mathlib, connectedComponent_eq_iInter_isClopen]
  ext y
  simp [QuasiComponent, QuasiComponentsData.QuasiComponent]

theorem clopen_component_refinement [CompactSpace X] [T2Space X]
    (x : X) (O : Set X) (hO : IsOpen O) (hCO : Component x ⊆ O) :
    ∃ H : Set X, IsClopen H ∧ Component x ⊆ H ∧ H ⊆ O := by
  let N := {H : Set X // IsClopen H ∧ x ∈ H}
  have : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
  have hdir : Directed (· ⊇ ·) (fun H : N => H.val) := by
    intro H K
    exact ⟨⟨H.val ∩ K.val, H.property.1.inter K.property.1,
      ⟨H.property.2, K.property.2⟩⟩, inter_subset_left, inter_subset_right⟩
  have hclosed : ∀ H : N, IsClosed H.val := fun H => H.property.1.isClosed
  have hsub : (⋂ H : N, H.val) ⊆ O := by
    rw [← connectedComponent_eq_iInter_isClopen, ← component_eq_mathlib]
    exact hCO
  obtain ⟨H, hHO⟩ := exists_subset_nhds_of_compactSpace hdir hclosed
    (hO.mem_nhdsSet.mpr hsub)
  exact ⟨H.val, H.property.1, fun y hy =>
    (mem_quasiComponent x y).mp (component_subset_quasiComponent x hy)
      H.val H.property.1 H.property.2, hHO⟩

theorem totallyDisconnected_iff_mathlib (X : Type u) [TopologicalSpace X] :
    TotallyDisconnected X ↔ TotallyDisconnectedSpace X := by
  change (∀ x : X, Component x = {x}) ↔ _
  simp only [component_eq_mathlib]
  exact totallyDisconnectedSpace_iff_connectedComponent_singleton.symm

theorem zeroDimensional_iff_clopen_basis (X : Type u) [t : TopologicalSpace X] :
    ZeroDimensional X ↔ Ch01.BasisFor t {H : Set X | IsClopen H} := by
  constructor
  · rintro ⟨B, hB, hclopen⟩
    apply (Ch01.basis_iff_mathlib _ _).mpr
    exact ((Ch01.basis_iff_mathlib _ _).mp hB).of_isOpen_of_subset
      (fun _ hH => hH.isOpen) hclopen
  · intro h
    exact ⟨{H : Set X | IsClopen H}, h, fun _ hH => hH⟩

theorem zeroDimensional_iff_mathlib (X : Type u) [TopologicalSpace X] :
    ZeroDimensional X ↔ ZeroDimensionalSpace X := by
  rw [zeroDimensional_iff_clopen_basis, Ch01.basis_iff_mathlib,
    zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]

theorem zeroDimensional_t1_hausdorff (X : Type u) [TopologicalSpace X] [T1Space X]
    (h : ZeroDimensional X) : T2Space X := by
  have hb := (Ch01.basis_iff_mathlib _ _).mp
    ((zeroDimensional_iff_clopen_basis X).mp h)
  refine ⟨fun x y hxy => ?_⟩
  have hx : x ∈ ({y} : Set X)ᶜ := hxy
  obtain ⟨H, hH, hxH, hHsub⟩ := hb.mem_nhds_iff.mp
    ((isClosed_singleton : IsClosed ({y} : Set X)).isOpen_compl.mem_nhds hx)
  exact ⟨H, Hᶜ, hH.isOpen, hH.compl.isOpen, hxH,
    fun hyH => hHsub hyH (mem_singleton y), disjoint_compl_right⟩

theorem zeroDimensional_t1_totallyDisconnected (X : Type u)
    [TopologicalSpace X] [T1Space X] (h : ZeroDimensional X) : TotallyDisconnected X := by
  let : ZeroDimensionalSpace X := (zeroDimensional_iff_mathlib X).mp h
  exact (totallyDisconnected_iff_mathlib X).mpr inferInstance

theorem compact_t2_totallyDisconnected_iff_zeroDimensional
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    TotallyDisconnected X ↔ ZeroDimensional X := by
  constructor
  · intro h
    apply (zeroDimensional_iff_clopen_basis X).mpr
    apply (Ch01.basis_iff_mathlib _ _).mpr
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      (fun _ hH => hH.isOpen)
    intro x O hx hO
    have hCO : Component x ⊆ O := by
      have hcx : Component x = {x} := h x
      rw [hcx]
      exact singleton_subset_iff.mpr hx
    obtain ⟨H, hH, hCH, hHO⟩ := clopen_component_refinement x O hO hCO
    exact ⟨H, hH, hCH (component_self x), hHO⟩
  · exact zeroDimensional_t1_totallyDisconnected X

theorem indiscrete_twoPoint_clopen_basis :
    letI : TopologicalSpace Bool := ⊤
    Ch01.BasisFor (⊤ : TopologicalSpace Bool) {(univ : Set Bool)} ∧
      ∀ H ∈ ({(univ : Set Bool)} : Set (Set Bool)), IsClopen H := by
  letI : TopologicalSpace Bool := ⊤
  constructor
  · constructor
    · intro H hH
      obtain rfl := mem_singleton_iff.mp hH
      exact isOpen_univ
    · intro O hO
      rcases (TopologicalSpace.isOpen_top_iff O).mp hO with rfl | rfl
      · exact ⟨∅, empty_subset _, by simp⟩
      · exact ⟨{univ}, Subset.rfl, by simp⟩
  · intro H hH
    obtain rfl := mem_singleton_iff.mp hH
    exact isClopen_univ

theorem indiscrete_twoPoint_connected : @Connected Bool ⊤ := by
  letI : TopologicalSpace Bool := ⊤
  apply (connected_iff_clopen Bool).mpr
  intro H hH
  exact (TopologicalSpace.isOpen_top_iff H).mp hH.isOpen

theorem indiscrete_twoPoint_not_totallyDisconnected : ¬ @TotallyDisconnected Bool ⊤ := by
  letI : TopologicalSpace Bool := ⊤
  intro h
  have : PreconnectedSpace Bool :=
    (connected_iff_preconnectedSpace Bool).mp indiscrete_twoPoint_connected
  have heq : (univ : Set Bool) = {false} := by
    rw [← PreconnectedSpace.connectedComponent_eq_univ false, ← component_eq_mathlib]
    exact h false
  have : true ∈ ({false} : Set Bool) := heq ▸ mem_univ true
  simp at this

end D10Topology.Ch06
