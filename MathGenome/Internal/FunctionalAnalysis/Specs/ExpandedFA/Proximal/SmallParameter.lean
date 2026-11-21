import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Definitions
import Mathlib.Topology.Order.Filter

/-! Independent specification of paper.tex:8573–8582. The parameter approaches
zero through all positive real numbers. The finite domain is not assumed closed,
and the datum is arbitrary. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ExpandedFA.Proximal.SmallParameterSpec
open P1.ExtendedConvexFunctions
universe u

/-- The same nearest-point choice as the shared convex projector, applied to
the norm closure of the finite domain. Well-posedness follows from the source
hypotheses, rather than being an argument to the proximal map. -/
def DomainProjectionType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → H → H

def DomainProjectionValue : DomainProjectionType.{u} :=
  fun H _ _ φ f => Classical.epsilon fun p =>
    p ∈ closure (P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ) ∧
      ∀ v ∈ closure (P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ),
        ‖f - p‖ ≤ ‖f - v‖

def SmallParameterLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ f : H, Tendsto (fun μ : ℝ => Spec.ProximalMapValue H φ μ f)
      (𝓝[>] (0 : ℝ)) (𝓝 (DomainProjectionValue H φ f))

end ExpandedFA.Proximal.SmallParameterSpec
