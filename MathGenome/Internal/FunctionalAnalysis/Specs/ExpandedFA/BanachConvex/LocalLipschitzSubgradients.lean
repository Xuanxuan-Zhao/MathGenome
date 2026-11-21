import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! Independent statements for the local stage of paper.tex:8080–8086.
The real representative is used only where the finite upper bound guarantees
that the original extended-valued function is finite. No completeness or lower
semicontinuity is assumed. -/
namespace ExpandedFA.BanachConvex.LocalSpec

open P1.ExtendedConvexFunctions
open Filter Set
open scoped Topology
universe u

/-- A canonical real representative; its values outside the finite domain
are immaterial to each local conclusion. -/
def realValue {X : Type u} (φ : ExtendedFunction X) (y : X) : ℝ :=
  (φ y).untopD 0

def LocalLipschitz : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (R M : ℝ),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    0 < R → (∀ y ∈ Metric.closedBall x R, φ y ≤ (M : WithTop ℝ)) →
    (∀ y ∈ Metric.closedBall x R, φ y = (realValue φ y : WithTop ℝ)) ∧
    LocallyLipschitzOn (Metric.ball x R) (realValue φ)

def SubgradientsNonempty : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (R M : ℝ),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    0 < R → (∀ y ∈ Metric.closedBall x R, φ y ≤ (M : WithTop ℝ)) →
    ∀ y ∈ Metric.ball x R, (Spec.SubdifferentialValue X φ y).Nonempty

def SubgradientNormBound : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (R M : ℝ),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    0 < R → (∀ y ∈ Metric.closedBall x R, φ y ≤ (M : WithTop ℝ)) →
    ∀ f ∈ Spec.SubdifferentialValue X φ x,
      ‖f‖ ≤ (M - realValue φ x) / R

/-- A finite right directional limit, with its supremum over the continuous
subgradients attained, including the zero direction and the zero space. -/
def DirectionalMaximum : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (R M : ℝ),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    0 < R → (∀ y ∈ Metric.closedBall x R, φ y ≤ (M : WithTop ℝ)) →
    ∀ v : X, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (realValue φ (x + t • v) - realValue φ x) / t)
        (𝓝[>] 0) (𝓝 d) ∧
      (∃ f ∈ Spec.SubdifferentialValue X φ x, f v = d) ∧
      (∀ f ∈ Spec.SubdifferentialValue X φ x, f v ≤ d)

end ExpandedFA.BanachConvex.LocalSpec
