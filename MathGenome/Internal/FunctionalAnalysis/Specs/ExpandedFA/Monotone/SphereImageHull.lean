import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Convex.Hull

/-! The last assertion of `fa2:p2:schur-cauchy-sphere`, paper.tex:8907–8940.
The domain is exactly the closed unit ball of an arbitrary real normed space.
The values are continuous real linear functionals. Only the hull's topology
is weak-star; the map itself has no regularity assumption. -/

noncomputable section
open scoped Topology

namespace ExpandedFA.Monotone.SphereImageHull

universe u

/-- The closed unit ball, including its boundary. -/
abbrev UnitBall (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ ≤ 1}

/-- Monotonicity of a possibly nonlinear map on the closed unit ball. -/
def IsMonotone {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : UnitBall X → StrongDual ℝ X) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) ((x : X) - (y : X))

/-- Boundary values of the map, regarded in the weak-star dual. -/
def sphereImage {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : UnitBall X → StrongDual ℝ X) : Set (WeakDual ℝ X) :=
  (fun x => (A x).toWeakDual) '' {x : UnitBall X | ‖(x : X)‖ = 1}

namespace Spec

/-- The full sphere-image hull assertion, retaining the nonempty-sphere hypothesis. -/
def ImageInWeakStarHull : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X],
    (Metric.sphere (0 : X) 1).Nonempty →
    ∀ A : UnitBall X → StrongDual ℝ X, IsMonotone A →
      Set.range (fun x => (A x).toWeakDual) ⊆ closure (convexHull ℝ (sphereImage A))

end Spec
end ExpandedFA.Monotone.SphereImageHull
