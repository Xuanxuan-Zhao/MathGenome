import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.GenusTwoOrientation
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoSurface

/-! The specific reflected connected sum of two standard oriented tori from
paper.tex 2385–2396. The upstream construction supplies the literal quotient
and its generating bulk and signed radial charts. Here we assemble its full
smooth and oriented construction on that same quotient topology. The shared
`SmoothManifolds.GenusTwoSurface` is the upstream alias of this quotient. -/
namespace SmoothManifolds.GenusTwo

/-- The same canonical quotient, retained under this construction's namespace.
The shared `SmoothManifolds.GenusTwoSurface` remains the upstream alias. -/
abbrev Surface := GenusTwoData.Surface

/-- The removed coordinate disk has precisely the prescribed frontier circle,
and the angular reflection preserves both disk and circle. -/
theorem diskGeometry : Specs.SmoothManifolds.Examples.GenusTwoSurface.diskGeometryType :=
  GenusTwoAtlas.diskGeometry

/-- Only the reflected boundary pairs are identified. -/
theorem exactFibers : Specs.SmoothManifolds.Examples.GenusTwoSurface.exactFibersType :=
  GenusTwoAtlas.exactFibers

/-- The literal connected sum is nonempty, compact, Hausdorff and second countable. -/
theorem quotientTopology : Specs.SmoothManifolds.Examples.GenusTwoSurface.quotientTopologyType :=
  GenusTwoAtlas.quotientTopology

theorem connected : Specs.SmoothManifolds.Examples.GenusTwoSurface.connectedType :=
  GenusTwoAtlas.connected

/-- The two bulks and the seam provide a countable chart cover. -/
theorem countableChartCover :
    Specs.SmoothManifolds.Examples.GenusTwoSurface.countableChartCoverType :=
  GenusTwoAtlas.countableChartCover

/-- Every specified chart is realized, its maximal atlas is smooth and
boundaryless, and the standard orientations of both bulks extend across the
reflected seam. The witness is the fixed upstream smooth structure. -/
theorem smoothConstruction :
    Specs.SmoothManifolds.Examples.GenusTwoSurface.smoothConstructionType := by
  refine ⟨GenusTwoAtlas.interiorCharts, GenusTwoAtlas.seamCharts,
    GenusTwoAtlas.constructionAtlas_isContDiffAtlas, GenusTwoAtlas.smoothManifold,
    GenusTwoAtlas.smoothManifold_generatingAtlas, GenusTwoAtlas.smoothManifold_maximalAtlas,
    GenusTwoAtlas.smoothManifold_boundary, GenusTwoOrientation.orientation, ?_⟩
  exact GenusTwoOrientation.orientation_signs

/-- Complete construction of the manuscript's genus-two surface, independently
of the later cohomology computation. -/
theorem fullConstruction :
    Specs.SmoothManifolds.Examples.GenusTwoSurface.fullConstructionType :=
  ⟨diskGeometry, exactFibers, quotientTopology, connected, smoothConstruction⟩

end SmoothManifolds.GenusTwo
