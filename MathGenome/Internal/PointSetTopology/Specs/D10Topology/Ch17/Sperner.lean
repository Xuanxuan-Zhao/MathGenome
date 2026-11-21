import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.SimplexTriangulation
import Mathlib.Algebra.Ring.Parity

/-! Independent statements of the geometric Sperner lemma, paper.tex d10:17:sperner.
The affine formulation includes the standard simplex in every dimension, including zero.
The count uses the canonical geometric triangulation and vertex-labeling definitions. -/
namespace Specs.D10Topology.Ch17.Sperner
open Specs.D10Topology.Ch17.SimplexTriangulation

def sperner_odd : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S)
    (ℓ : VertexLabelingValue T), FaceRespectingValue T ℓ →
      Odd (fullyLabeledCellsValue T ℓ).card

def sperner_exists : Prop :=
  ∀ {m n : ℕ} {S : AffineSimplex m n} (T : TriangulationData S)
    (ℓ : VertexLabelingValue T), FaceRespectingValue T ℓ →
      ∃ C ∈ topCellsValue T, FullyLabeled T ℓ C

end Specs.D10Topology.Ch17.Sperner
