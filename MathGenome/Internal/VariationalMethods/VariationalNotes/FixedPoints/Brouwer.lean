import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.Brouwer
import MathGenome.PointSetTopology.Topics.D10Topology.Ch17

namespace VariationalNotes.FixedPoints

universe u

/-- Brouwer's fixed point theorem, in the compact convex form of
paper.tex, Theorem 10.3, for the given norm on any finite-dimensional
real normed space, including dimension zero. -/
theorem brouwer_compact_convex :
    Specs.VariationalNotes.FixedPoints.brouwer_compact_convex.{u} := by
  intro E _ _ _ K hne hcompact hconvex F hF
  exact D10Topology.Ch17.brouwer_finiteDimensional E K hne hcompact hconvex F hF

end VariationalNotes.FixedPoints
