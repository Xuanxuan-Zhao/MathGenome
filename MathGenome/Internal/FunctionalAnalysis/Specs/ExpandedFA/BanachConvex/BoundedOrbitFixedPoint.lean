import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.AsymptoticCenters
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Corollary `fa2:p2:bounded-orbit-fixed-point` (paper.tex:8408–8425).
The chapter uses real Banach spaces. The map acts on the subtype C; its
nonexpansiveness is expressed with the induced norm metric. Only the chosen
orbit is bounded. The fixed set below is a subset of the ambient space X,
so closedness means ambient norm closedness, and convexity is real convexity. -/
namespace ExpandedFA.BanachConvex.BoundedOrbitFixedPoint
open Set
universe u
noncomputable section

/-- The orbit, viewed in the ambient normed space, including its initial point. -/
def orbit {X : Type u} {C : Set X} (T : C → C) (a : C) (n : ℕ) : X :=
  (T^[n] a : C)

/-- All fixed points of the map, as an ambient subset. -/
def fixedSet {X : Type u} {C : Set X} (T : C → C) : Set X :=
  Subtype.val '' Function.fixedPoints T

namespace Spec

/-- The actual limsup-radius center exists uniquely, and every such center is fixed. -/
def OrbitCenterFixed : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (T : C → C), LipschitzWith 1 T → ∀ a : C,
    Bornology.IsBounded (range (orbit T a)) →
    (∃! c : X, AsymptoticCenters.IsCenter C (orbit T a) c) ∧
    ∀ c : C, AsymptoticCenters.IsCenter C (orbit T a) (c : X) → T c = c

/-- Closedness and convexity of the entire fixed set, without any boundedness of C. -/
def FixedSetClosedConvex : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [UniformConvexSpace X]
    (C : Set X), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (T : C → C), LipschitzWith 1 T →
    IsClosed (fixedSet T) ∧ Convex ℝ (fixedSet T)

end Spec
end
end ExpandedFA.BanachConvex.BoundedOrbitFixedPoint
