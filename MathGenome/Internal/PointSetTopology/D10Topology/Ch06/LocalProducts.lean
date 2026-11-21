import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.LocalProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.LocalConnectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.ConnectedProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness

/-! Product criteria and finiteness of components, paper.tex
`d10:06:local-products`. The library product criteria use the usual Pi
topology, identified here with the source product topology. Nonemptiness
of the product supplies exactly the nonempty factors needed for the library
path-connected-space convention. -/

open Set
universe u v

namespace D10Topology.Ch06

/-- The library requires a nonempty path-connected space; the source predicate
only requires paths between every pair, and hence also holds on empty spaces. -/
theorem pathConnected_iff_mathlib_of_nonempty (X : Type u) [TopologicalSpace X]
    (hn : Nonempty X) : PathConnected X ↔ PathConnectedSpace X :=
  ⟨fun h => ⟨hn, h⟩, fun h => h.joined⟩

theorem locallyConnected_product_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hn : Nonempty (∀ i, X i)) :
    @LocallyConnected (∀ i, X i) (Ch03.productTopology tX) ↔
      (∀ i, @LocallyConnected (X i) (tX i)) ∧
        {i | ¬ @Connected (X i) (tX i)}.Finite := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  have hne : ¬ IsEmpty (∀ i, X i) := fun h => hn.elim h.false
  simpa only [hne, false_or, ← locallyConnected_iff_mathlib,
    ← connected_iff_preconnectedSpace] using
    (Pi.locallyConnectedSpace_iff (X := X))

theorem locallyPathConnected_product_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hn : Nonempty (∀ i, X i)) :
    @LocallyPathConnected (∀ i, X i) (Ch03.productTopology tX) ↔
      (∀ i, @LocallyPathConnected (X i) (tX i)) ∧
        {i | ¬ @PathConnected (X i) (tX i)}.Finite := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  have hne : ¬ IsEmpty (∀ i, X i) := fun h => hn.elim h.false
  have hpath (i : I) : PathConnectedSpace (X i) ↔ PathConnected (X i) :=
    (pathConnected_iff_mathlib_of_nonempty (X i) (hn.map (fun x => x i))).symm
  simpa only [hne, false_or, ← locallyPathConnected_iff_mathlib, hpath] using
    (Pi.locallyPathConnectedSpace_iff (Z := X))

/-- The open components form a cover. Compactness gives finitely many of
them, and the component partition shows these exhaust the entire range. -/
theorem finite_components_of_compact_locallyConnected (X : Type u)
    [TopologicalSpace X] (hc : Ch05.CoverCompact X) (hl : LocallyConnected X) :
    (range (Component : X → Set X)).Finite := by
  let := (Ch05.coverCompact_iff_compactSpace X).mp hc
  let := (locallyConnected_iff_mathlib X).mp hl
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (Component : X → Set X)
    (fun x => by rw [component_eq_mathlib]; exact isOpen_connectedComponent)
    (fun x _ => mem_iUnion.mpr ⟨x, component_self x⟩)
  apply (s.finite_toSet.image Component).subset
  rintro C ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine ⟨y, hy, ?_⟩
  simp only [component_eq_mathlib] at hxy ⊢
  exact connectedComponent_eq hxy

theorem components_of_empty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    range (Component : X → Set X) = ∅ := by
  exact Set.range_eq_empty (f := Component)

end D10Topology.Ch06
