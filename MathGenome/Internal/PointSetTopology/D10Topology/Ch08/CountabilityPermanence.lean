import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityPermanence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests

/-!
Subspace and map permanence in paper.tex, d10:08:permanence. The canonical
subtype topology is the paper's subspace topology, as established in chapter 3.
The first-countability bridge preserves arbitrary neighborhood bases, while
the other three conditions have their exact basis/density/cover bridges in
CountabilityConventions. Empty spaces are permitted throughout.
-/

open Set TopologicalSpace Filter
open scoped Topology
universe u v

namespace D10Topology.Ch08

theorem firstCountable_subspace {X : Type u} [t : TopologicalSpace X]
    (h : FirstCountable t) (A : Set X) :
    FirstCountable (inferInstance : TopologicalSpace A) := by
  let : FirstCountableTopology X := firstCountable_iff_mathlib.mp h
  exact firstCountable_iff_mathlib.mpr inferInstance

theorem lindelof_closed_subspace {X : Type u} [TopologicalSpace X]
    (h : LindelofSpace X) (A : Set X) (hA : IsClosed A) : LindelofSpace A := by
  let := h
  exact isLindelof_iff_lindelofSpace.mp hA.isLindelof

theorem separable_open_subspace {X : Type u} [TopologicalSpace X]
    (h : SeparableSpace X) (A : Set X) (hA : IsOpen A) : SeparableSpace A := by
  let := h
  exact hA.isOpenEmbedding_subtypeVal.separableSpace

theorem separable_continuous_surjection {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (h : SeparableSpace X) (f : X → Y)
    (hc : Continuous f) (hs : Function.Surjective f) : SeparableSpace Y := by
  let := h
  exact hs.denseRange.separableSpace hc

theorem lindelof_continuous_surjection {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] (h : LindelofSpace X) (f : X → Y)
    (hc : Continuous f) (hs : Function.Surjective f) : LindelofSpace Y := by
  let := h
  exact LindelofSpace.of_continuous_surjective hc hs

/-- An open continuous map sends a neighborhood filter to the neighborhood
filter of its image point. Its countable generation therefore passes to the
image; surjectivity supplies a preimage for every target point. -/
theorem firstCountable_open_continuous_surjection
    {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y]
    (h : FirstCountable tX) (f : X → Y) (hc : Continuous f)
    (ho : IsOpenMap f) (hs : Function.Surjective f) : FirstCountable tY := by
  let : FirstCountableTopology X := firstCountable_iff_mathlib.mp h
  apply firstCountable_iff_mathlib.mpr
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hs y
  rw [← ho.map_nhds_eq hc.continuousAt]
  infer_instance

theorem secondCountable_open_continuous_surjection
    {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
    (h : SecondCountableTopology X) (f : X → Y) (hc : Continuous f)
    (ho : IsOpenMap f) (hs : Function.Surjective f) : SecondCountableTopology Y := by
  let := h
  exact Topology.IsOpenQuotientMap.secondCountableTopology
    (show _root_.IsOpenQuotientMap f from ⟨hs, hc, ho⟩)

end D10Topology.Ch08
