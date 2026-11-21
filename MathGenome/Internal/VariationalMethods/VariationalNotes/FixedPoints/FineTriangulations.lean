import MathGenome.Internal.VariationalMethods.VariationalNotes.FixedPoints.SimplexGeometry
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.FineTriangulations
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.BarycentricSubdivision

/-! Fine triangulations of the standard Euclidean simplex. The library's
iterated barycentric subdivisions specialize directly to the shared simplex.
Face coverage and purity are proved by the library, not assumed as input. -/
noncomputable section
open scoped Topology

namespace VariationalNotes.FixedPoints.FineTriangulations
open VariationalNotes.FixedPoints.SimplexGeometry

/-- Lemma `lem:fine-simplex-triangulations`, valid also in dimension zero.
Each restriction is the induced geometric complex, covers the corresponding
face, and has maximal cells with exactly that face's number of vertices. -/
theorem fine_triangulations (d : ℕ) :
    ∃ T : ℕ → Triangulation d,
      (∀ r (I : Finset (Fin (d + 1))),
        D10Topology.Ch17.complexSupport (inducedComplex (T r) I) = face d I ∧
        ∀ s ∈ D10Topology.Ch17.maximalCells (inducedComplex (T r) I),
          s.card = I.card) ∧
      Filter.Tendsto (fun r => mesh (T r)) Filter.atTop (𝓝 0) :=
  D10Topology.Ch17.Subdivision.fine_triangulations (standardAffineSimplex d)

end VariationalNotes.FixedPoints.FineTriangulations
