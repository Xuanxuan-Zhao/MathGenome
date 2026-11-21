import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionComponents

/-! Topology of the planar region in paper.tex 4762–4813, assembled using the
canonical region, the corner-compatible collar, and the actual complementary
components. The foundation constructs the inward push of the actual inclusion. -/

noncomputable section
open Set Topology

namespace P202.PlanarRegionTopology
open P202Specs.PlanarRegionTopology

/-- The genuine boundary collar supplies the homotopy equivalence of the
interior inclusion; the two geometric results supply every remaining factor. -/
theorem assembly : Expected.assembly := by
  intro hlocal hglobal R
  obtain ⟨hc, hconn, hi, hb⟩ := basicProperties R
  obtain ⟨hsurf, hlc, hcollar, horient⟩ := hlocal R
  obtain ⟨S, hS⟩ := hglobal R
  exact ⟨hc, hconn, hi, hb, hsurf, hlc, hcollar,
    regionInteriorEquivalenceOfCollar R hcollar, S, horient, hS⟩


/-- The full topology, collar, inclusion equivalence, component count and
boundary orientation result under the original planar-region hypotheses. -/
theorem planarRegionTopology : Expected.planarRegionTopology :=
  assembly localGeometry P202.PlanarRegionComponents.complementComponents

end P202.PlanarRegionTopology
