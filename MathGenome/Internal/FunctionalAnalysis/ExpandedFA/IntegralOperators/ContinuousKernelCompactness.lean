import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel

/-!
The continuous-kernel stage of `fa2:p2:kernel-compactness` is the square-domain
specialization of the accepted general continuous-kernel theorem. We use its
canonical operator directly, so later integral-operator results refer to the
same construction. In particular no regularity, nonemptiness, positive-mass,
or metrizability assumptions enter this specialization.
-/

universe u v
namespace ExpandedFA.IntegralOperators.ContinuousKernelCompactness

theorem canonical_properties : Spec.CanonicalProperties.{u, v} := by
  intro 𝕜 Q _ _ _ _ _ _ μ _ k
  exact ExpandedFA.PartV.ContinuousKernel.canonical_operator_properties 𝕜 Q Q μ k

theorem continuous_kernel_theorem : Spec.ContinuousKernelTheorem.{u, v} := by
  intro 𝕜 Q _ _ _ _ _ _ μ _ k
  exact ExpandedFA.PartV.ContinuousKernel.continuous_kernel_theorem 𝕜 Q Q μ k

theorem zero_cases : Spec.ZeroCases.{u, v} := by
  intro 𝕜 Q _ _ _ _ _ _ μ _ k hz
  apply ExpandedFA.PartV.ContinuousKernel.continuous_kernel_zero_cases 𝕜 Q Q μ k
    (ExpandedFA.PartV.ContinuousKernel.kernelOperator μ k)
    (ExpandedFA.PartV.ContinuousKernel.kernelOperator_apply μ k)
  rcases hz with hμ | hQ
  · exact Or.inl hμ
  · exact Or.inr (Or.inl hQ)

end ExpandedFA.IntegralOperators.ContinuousKernelCompactness
