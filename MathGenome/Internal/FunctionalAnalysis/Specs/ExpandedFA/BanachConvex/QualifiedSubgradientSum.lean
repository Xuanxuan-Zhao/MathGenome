import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.WithTop

/-! The sum-rule clauses of paper.tex:8089–8095 and the strict example at
8153–8158. The other clauses of the theorem have separate upstream goals.
The value space has +∞ but no −∞. No completeness or lower semicontinuity
is imposed on this calculus. -/
namespace ExpandedFA.BanachConvex.SumSpec

open P1.ExtendedConvexFunctions
open scoped Pointwise
universe u

def SumInclusion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ ψ : ExtendedFunction X) (x : X),
    Spec.SubdifferentialValue X φ x + Spec.SubdifferentialValue X ψ x ⊆
      Spec.SubdifferentialValue X (φ + ψ) x

/-- Continuity is at one common finite-domain point, and the conclusion
holds at every point, including points outside the common finite domain. -/
def QualifiedSum : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ ψ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ProperValue X ψ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X ψ →
    ∀ x₀ : X, φ x₀ ≠ ⊤ → ψ x₀ ≠ ⊤ → ContinuousAt φ x₀ →
    ∀ x : X, Spec.SubdifferentialValue X (φ + ψ) x =
      Spec.SubdifferentialValue X φ x + Spec.SubdifferentialValue X ψ x

abbrev SqrtExampleType := ExtendedFunction ℝ
noncomputable def SqrtExampleValue : SqrtExampleType :=
  fun t => if 0 ≤ t then ((-Real.sqrt t : ℝ) : WithTop ℝ) else ⊤

abbrev PointIndicatorType := ExtendedFunction ℝ
noncomputable def PointIndicatorValue : PointIndicatorType :=
  fun t => if t = 0 then 0 else ⊤

/-- Both functions are proper convex, their sum is precisely I_{0}, and
the inclusion is strict at zero: the left set is empty, the right is all
continuous scalar-linear functionals. -/
def StrictExample : Prop :=
  let φ := SqrtExampleValue
  let ψ := PointIndicatorValue
  P1.ExtendedConvexFunctions.Spec.ProperValue ℝ φ ∧
  P1.ExtendedConvexFunctions.Spec.ProperValue ℝ ψ ∧
  P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ φ ∧
  P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ ψ ∧
  φ + ψ = ψ ∧
  Spec.SubdifferentialValue ℝ φ 0 = ∅ ∧
  Spec.SubdifferentialValue ℝ (φ + ψ) 0 = Set.univ ∧
  Spec.SubdifferentialValue ℝ φ 0 + Spec.SubdifferentialValue ℝ ψ 0 ⊂
    Spec.SubdifferentialValue ℝ (φ + ψ) 0

end ExpandedFA.BanachConvex.SumSpec
