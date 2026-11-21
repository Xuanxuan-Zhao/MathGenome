import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.SimplexGeometry

/-! Independent statement of paper.tex, Lemma `lem:fine-simplex-triangulations`.
The shared triangulation type already requires finite geometric cells, affine
independence, closure under faces, exact intersections, coverage, and purity.
Face restrictions retain exactly the cells contained in the original face.
Their coverage and purity are conclusions here, including for the empty face.
Mesh is measured in the inherited Euclidean L2 metric. -/
noncomputable section
open scoped Topology

namespace Specs.VariationalNotes.FixedPoints.FineTriangulations
open Specs.VariationalNotes.FixedPoints.SimplexGeometry

/-- Every standard simplex, including dimension zero, has a sequence of
geometric triangulations with compatible face restrictions and vanishing mesh. -/
def fine_triangulations : Prop :=
  ∀ d : ℕ, ∃ T : ℕ → Triangulation d,
    (∀ r (I : Finset (Fin (d + 1))),
      D10Topology.Ch17.complexSupport (inducedComplex (T r) I) = face d I ∧
      ∀ s ∈ D10Topology.Ch17.maximalCells (inducedComplex (T r) I),
        s.card = I.card) ∧
    Filter.Tendsto (fun r => mesh (T r)) Filter.atTop (𝓝 0)

end Specs.VariationalNotes.FixedPoints.FineTriangulations
