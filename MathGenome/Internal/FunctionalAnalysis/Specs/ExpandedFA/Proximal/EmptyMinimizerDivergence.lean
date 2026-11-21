import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.LargeParameterMinimizers

/-! Independent statements for `fa2:p2:prox-large-parameter`, paper.tex:8619–8629.
The function takes values in ℝ ∪ {+∞}, and may have infimum −∞.
No lower bound, coercivity, or nonempty minimizing set is assumed for divergence.
The parameter is real and tends to +∞, so positivity is eventual. -/
noncomputable section
open Filter
namespace ExpandedFA.Proximal.EmptyMinimizerSpec
open P1.ExtendedConvexFunctions
universe u

def EmptyMinimizerDivergence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    LargeParameterSpec.ArgminValue H φ = ∅ →
    ∀ f : H, Tendsto (fun μ : ℝ => ‖Spec.ProximalMapValue H φ μ f‖) atTop atTop

/-- Both clauses of the manuscript theorem, retaining the accepted projection
limit and its closedness and convexity conclusions. -/
def LargeParameterTheorem : Prop :=
  LargeParameterSpec.LargeParameterLimit.{u} ∧ EmptyMinimizerDivergence.{u}

end ExpandedFA.Proximal.EmptyMinimizerSpec
