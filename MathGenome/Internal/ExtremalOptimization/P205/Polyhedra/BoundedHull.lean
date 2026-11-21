import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.BoundedHull
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.ExtremeRepresentation

namespace P205.Polyhedra

/-- Bounded polyhedra are convex hulls of their vertices, including in zero
ambient dimension and when their affine span is proper. -/
theorem bounded_polyhedron_hull : Specs.bounded_polyhedron_hull := by
  intro m n A b P hne hb
  have hclosed : IsClosed P := by
    exact isClosed_Iic.preimage (A.mulVecLin.continuous_of_finiteDimensional)
  have hconvex : Convex ℝ P :=
    (convex_Iic b).linear_preimage A.mulVecLin
  have hcompact : IsCompact P :=
    Metric.isCompact_of_isClosed_isBounded hclosed hb
  exact VariationalNotes.ConvexGeometry.extremePoint_representation P hne hcompact hconvex

end P205.Polyhedra
