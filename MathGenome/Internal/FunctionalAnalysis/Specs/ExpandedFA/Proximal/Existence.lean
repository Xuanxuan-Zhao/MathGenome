import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Definitions

/-! Existence stage of paper.tex:8460–8495. The space is a real Hilbert
space, and the function may take +∞ and need not be bounded below. -/
namespace ExpandedFA.Proximal.ExistenceSpec
open P1.ExtendedConvexFunctions
universe u

def UniqueMinimizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃! u, Spec.IsProximalMinimizerValue H φ μ f u

def FiniteEnvelope : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃ r : ℝ, Spec.MoreauEnvelopeValue H φ μ f = (r : EReal)

def ProximalMapMinimizes : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      Spec.IsProximalMinimizerValue H φ μ f (Spec.ProximalMapValue H φ μ f)

end ExpandedFA.Proximal.ExistenceSpec
