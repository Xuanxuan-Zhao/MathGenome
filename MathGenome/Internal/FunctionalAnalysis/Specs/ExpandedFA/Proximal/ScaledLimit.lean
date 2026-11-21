import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.SmallParameter
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.MoreauDecomposition

/-! Independent statement of `fa2:p2:prox-scaled-limit`, paper.tex:8673–8681.
The conjugate is the shared genuine Hilbert conjugate, expressed in WithTop ℝ.
The projection is onto the norm closure of its finite domain. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.Proximal.ScaledLimitSpec
open P1.ExtendedConvexFunctions
universe u

/-- All positive parameters tending to infinity, arbitrary data, and no
assumption that the original function attains its infimum. -/
def ScaledLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ f : H, Tendsto (fun μ : ℝ => μ⁻¹ • Spec.ProximalMapValue H φ μ f)
      atTop (𝓝 (-SmallParameterSpec.DomainProjectionValue H
        (MoreauSpec.ConjugateFunctionValue H φ) 0))

end ExpandedFA.Proximal.ScaledLimitSpec
