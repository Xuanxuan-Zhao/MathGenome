import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Independent statement of the planar ellipse bridge in `fa2:p2:ellipsoid`. -/
namespace ExpandedFA.HilbertCharacterization

abbrev Plane := Fin 2 → ℝ

/-- Symmetry about the origin, the center of the central section in the source. -/
def OriginSymmetric (D : Set Plane) : Prop := ∀ x ∈ D, -x ∈ D

/-- The full linear automorphism group of the body acts transitively on its boundary. -/
def BoundaryTransitive (D : Set Plane) : Prop :=
  ∀ x ∈ frontier D, ∀ y ∈ frontier D,
    ∃ A : Plane ≃ₗ[ℝ] Plane, A '' D = D ∧ A x = y

/-- A filled, nondegenerate centered ellipse, expressed by a positive definite quadratic form.
The positive level is allowed to vary; dividing the form by that level gives level one. -/
def IsEllipse (D : Set Plane) : Prop :=
  ∃ Q : QuadraticForm ℝ Plane, Q.PosDef ∧ ∃ c : ℝ, 0 < c ∧ D = {x | Q x ≤ c}

namespace HomogeneousPlanarEllipseSpec

def statement : Prop :=
  ∀ D : Set Plane, IsCompact D → Convex ℝ D → OriginSymmetric D →
    (interior D).Nonempty → BoundaryTransitive D → IsEllipse D

end HomogeneousPlanarEllipseSpec
end ExpandedFA.HilbertCharacterization
