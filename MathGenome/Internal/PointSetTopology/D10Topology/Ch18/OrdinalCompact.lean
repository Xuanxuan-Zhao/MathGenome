import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.OrdinalCompact
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.OrderTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import Mathlib.Topology.Order.IsLUB

/-!
Closed ordinal intervals are compact Hausdorff (`d10:18:ordinal-compact`).
Ordinals are conditionally complete linear orders by their standard
well-ordering. The general compact-interval theorem therefore applies to
`[0, β]` for every ordinal β, including zero, successors and arbitrary limits.
The convex-subspace bridge identifies its induced topology with its own
order topology, and Chapter 5 converts compactness to finite open subcovers.
-/

open Set
universe u

namespace D10Topology.Ch18

theorem ordinalInterval_orderTopology_eq_subspace (β : Ordinal.{u}) :
    Ch01.orderTopology (Icc (0 : Ordinal.{u}) β) =
      TopologicalSpace.induced (Subtype.val : Icc (0 : Ordinal.{u}) β → Ordinal.{u})
        (Ch01.orderTopology Ordinal.{u}) := by
  apply Ch01.orderTopology_convex_subspace
  intro x hx y hy z hxz hzy
  exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩

theorem ordinalInterval_compact_hausdorff (β : Ordinal.{u}) :
    @Ch05.CoverCompact (Icc (0 : Ordinal.{u}) β)
      (Ch01.orderTopology (Icc (0 : Ordinal.{u}) β)) ∧
    @T2Space (Icc (0 : Ordinal.{u}) β)
      (Ch01.orderTopology (Icc (0 : Ordinal.{u}) β)) := by
  constructor
  · rw [ordinalInterval_orderTopology_eq_subspace]
    let : TopologicalSpace Ordinal.{u} := Ch01.orderTopology Ordinal.{u}
    let : OrderTopology Ordinal.{u} := ⟨rfl⟩
    apply (Ch05.coverCompact_iff_compactSpace _).mpr
    exact isCompact_iff_compactSpace.mp
      (ConditionallyCompleteLinearOrder.isCompact_Icc (0 : Ordinal.{u}) β)
  · exact Ch01.orderTopology_hausdorff _

end D10Topology.Ch18
