import Mathlib.Topology.MetricSpace.Basic

/-!
Independent specifications for Proposition p206:W68 in paper.tex.
The space may itself be a domain equipped with its restricted metric.
Both fixed points are premises; no completeness or contraction of S is required.
-/

namespace Specs.NumAnalysis206.Iterations

/-- The perturbation bound at the fixed point of S suffices. -/
def FixedPointSensitivityAtPoint : Prop :=
  ∀ {X : Type*} [MetricSpace X] (T S : X → X) (p ptilde : X) (q δ : ℝ),
    0 ≤ q → q < 1 →
    (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
    T p = p → S ptilde = ptilde →
    dist (T ptilde) (S ptilde) ≤ δ →
    dist p ptilde ≤ δ / (1 - q)

/-- The uniform perturbation estimate in Proposition p206:W68. -/
def FixedPointSensitivityUniform : Prop :=
  ∀ {X : Type*} [MetricSpace X] (T S : X → X) (p ptilde : X) (q δ : ℝ),
    0 ≤ q → q < 1 →
    (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
    T p = p → S ptilde = ptilde →
    (∀ x : X, dist (T x) (S x) ≤ δ) →
    dist p ptilde ≤ δ / (1 - q)

end Specs.NumAnalysis206.Iterations
