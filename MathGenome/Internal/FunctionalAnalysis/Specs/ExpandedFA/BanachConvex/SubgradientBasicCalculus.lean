import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.NormSquareConjugate
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent statements for the elementary clauses of
`fa2:p2:subgradient-calculus`, paper.tex:8056–8109. No completeness,
lower semicontinuity, or norm attainment is imposed. -/
namespace ExpandedFA.BanachConvex.BasicCalculusSpec

open P1.ExtendedConvexFunctions
open P1.C06Conjugates
open Filter
open scoped Topology

universe u

def ClosedConvex : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X),
    IsClosed (Spec.SubdifferentialValue X φ x) ∧
      Convex ℝ (Spec.SubdifferentialValue X φ x)

def MonotoneGraph : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x y : X) (f g : X →L[ℝ] ℝ),
    f ∈ Spec.SubdifferentialValue X φ x → g ∈ Spec.SubdifferentialValue X φ y →
      0 ≤ (f - g) (x - y)

/-- The finite-domain guard is essential for extended-valued primal functions. -/
def FenchelEquality : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (f : X →L[ℝ] ℝ),
    f ∈ Spec.SubdifferentialValue X φ x ↔
      φ x ≠ ⊤ ∧
      P1.C06Conjugates.Spec.ExtendedRealValueValue (φ x) +
        P1.C06Conjugates.Spec.ConvexConjugateValue X φ f = (f x : EReal)

def HalfNormSquare : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X),
    Spec.SubdifferentialValue X (Asplund.NormSquareConjugate.halfNormSquare (norm : X → ℝ)) x =
      Spec.DualityMapValue X x

def NormAtZero : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    Spec.SubdifferentialValue X (fun y : X => (‖y‖ : WithTop ℝ)) 0 =
      Metric.closedBall (0 : X →L[ℝ] ℝ) 1

def NormAtNonzero : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X), x ≠ 0 →
    Spec.SubdifferentialValue X (fun y : X => (‖y‖ : WithTop ℝ)) x =
      {f : X →L[ℝ] ℝ | ‖f‖ = 1 ∧ f x = ‖x‖}

open Classical in
/-- Includes points outside C, and empty or nonclosed C. For convex C this
is exactly the convex indicator/normal-cone identity in the source. -/
def Indicator : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] (C : Set X),
    ∀ x, Spec.SubdifferentialValue X (fun y => if y ∈ C then (0 : WithTop ℝ) else ⊤) x =
      Spec.NormalConeValue X C x

/-- Even Gâteaux differentiability with a continuous linear derivative suffices. -/
def DifferentiableAlongLines : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (u : X → ℝ) (x : X) (d : X →L[ℝ] ℝ),
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    (∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ)) →
    (∀ v : X, HasDerivAt (fun t : ℝ => u (x + t • v)) (d v) 0) →
      Spec.SubdifferentialValue X φ x = {d}

/-- Differentiability of an extended function means it agrees near x with a
real-valued differentiable function. Its domain need not be all of X. -/
def Differentiable : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (u : X → ℝ) (x : X) (d : X →L[ℝ] ℝ),
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    (∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ)) → HasFDerivAt u d x →
      Spec.SubdifferentialValue X φ x = {d}

end ExpandedFA.BanachConvex.BasicCalculusSpec
