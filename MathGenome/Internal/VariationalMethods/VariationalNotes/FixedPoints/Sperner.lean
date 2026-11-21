import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.Sperner
import MathGenome.Internal.VariationalMethods.VariationalNotes.FixedPoints.SimplexGeometry
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.Sperner

/-! Sperner parity for the standard simplex, including dimension zero.
The geometric triangulation and the finite set of fully labeled cells are
the shared canonical objects. The only labeling bridge needed is the proved
equivalence of coordinate positivity and respect for the original faces. -/
namespace VariationalNotes.FixedPoints.Sperner

open VariationalNotes.FixedPoints.SimplexGeometry

theorem sperner_odd {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T)
    (hℓ : SpernerLabeling T ℓ) : Odd (fullyLabeledCells T ℓ).card :=
  D10Topology.Ch17.sperner_odd T ℓ
    ((spernerLabeling_iff_faceRespecting T ℓ).mp hℓ)

theorem sperner_exists {d : ℕ} (T : Triangulation d) (ℓ : VertexLabeling T)
    (hℓ : SpernerLabeling T ℓ) : ∃ s ∈ topCells T, FullyLabeled T ℓ s :=
  D10Topology.Ch17.sperner_exists T ℓ
    ((spernerLabeling_iff_faceRespecting T ℓ).mp hℓ)

end VariationalNotes.FixedPoints.Sperner
