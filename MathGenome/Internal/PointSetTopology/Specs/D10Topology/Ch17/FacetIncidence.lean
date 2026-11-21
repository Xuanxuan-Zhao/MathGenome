import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.SimplexTriangulation

/-! Independent statement of paper.tex, d10:17:incidence.
Incidence counts actual cofaces of the shared geometric triangulation.
The affine formulation includes the standard simplex, with no extra condition.
The induced triangulation is required to have exactly the shared induced complex. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace Specs.D10Topology.Ch17.FacetIncidence
open Specs.D10Topology.Ch17.SimplexTriangulation

abbrev incidentTopCellsType := {m n : ℕ} → {S : AffineSimplex m n} →
  TriangulationData S → Finset (Euclidean m) → Finset (Finset (Euclidean m))
def incidentTopCellsValue : incidentTopCellsType := fun T F =>
  (topCellsValue T).filter (IncidentValue F)

def internal_facet_incidence : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S),
  0 < n → ∀ F ∈ internalFacetsValue T, (incidentTopCellsValue T F).card = 2

def boundary_facet_incidence : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S),
  0 < n → ∀ F ∈ boundaryFacetsValue T, (incidentTopCellsValue T F).card = 1

def original_facet_triangulation : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m (n + 1)} (T : TriangulationData S)
    (i : Fin (n + 2)),
    ∃ U : TriangulationData (S.face (m := n) (fs := Finset.univ.erase i) (by simp)),
      U.complex = inducedComplexValue T (Finset.univ.erase i)

end Specs.D10Topology.Ch17.FacetIncidence
