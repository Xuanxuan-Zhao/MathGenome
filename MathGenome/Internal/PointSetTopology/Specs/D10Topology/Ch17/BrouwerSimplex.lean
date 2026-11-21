import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.SimplexTriangulation

/-! The simplex has its subspace topology in Euclidean L2 space. The dimension
is an arbitrary natural number, so the one-point zero-dimensional case is
included. No further hypothesis is imposed on the continuous self-map. -/
namespace Specs.D10Topology.Ch17.BrouwerSimplex
open Specs.D10Topology.Ch17.SimplexTriangulation

def brouwer_simplex : Prop :=
  ∀ (n : ℕ) (f : standardSimplexValue n → standardSimplexValue n),
    Continuous f → ∃ x, f x = x

end Specs.D10Topology.Ch17.BrouwerSimplex
